#!/usr/bin/env python
#
# ESP8266 & ESP32 family ROM Bootloader Utility
# Copyright (C) 2014-2021 Fredrik Ahlberg, Angus Gratton, Espressif Systems (Shanghai) CO LTD, other contributors as noted.
# https://github.com/espressif/esptool
#
# This program is free software; you can redistribute it and/or modify it under
# the terms of the GNU General Public License as published by the Free Software
# Foundation; either version 2 of the License, or (at your option) any later version.
#
# This program is distributed in the hope that it will be useful, but WITHOUT
# ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS
# FOR A PARTICULAR PURPOSE. See the GNU General Public License for more details.
#
# You should have received a copy of the GNU General Public License along with
# this program; if not, write to the Free Software Foundation, Inc., 51 Franklin
# Street, Fifth Floor, Boston, MA 02110-1301 USA.

from __future__ import division, print_function

import argparse
import base64
import binascii
import copy
import hashlib
import inspect
import io
import itertools
import os
import shlex
import string
import struct
import sys
import time
import zlib

try:
    import serial
except ImportError:
    print("Pyserial is not installed for %s. Check the README for installation instructions." % (sys.executable))
    raise

# check 'serial' is 'pyserial' and not 'serial' https://github.com/espressif/esptool/issues/269
try:
    if "serialization" in serial.__doc__ and "deserialization" in serial.__doc__:
        raise ImportError("""
esptool.py depends on pyserial, but there is a conflict with a currently installed package named 'serial'.

You may be able to work around this by 'pip uninstall serial; pip install pyserial' \
but this may break other installed Python software that depends on 'serial'.

There is no good fix for this right now, apart from configuring virtualenvs. \
See https://github.com/espressif/esptool/issues/269#issuecomment-385298196 for discussion of the underlying issue(s).""")
except TypeError:
    pass  # __doc__ returns None for pyserial

try:
    import serial.tools.list_ports as list_ports
except ImportError:
    print("The installed version (%s) of pyserial appears to be too old for esptool.py (Python interpreter %s). "
          "Check the README for installation instructions." % (sys.VERSION, sys.executable))
    raise
except Exception:
    if sys.platform == "darwin":
        # swallow the exception, this is a known issue in pyserial+macOS Big Sur preview ref https://github.com/espressif/esptool/issues/540
        list_ports = None
    else:
        raise


__version__ = "3.1-dev"

MAX_UINT32 = 0xffffffff
MAX_UINT24 = 0xffffff

DEFAULT_TIMEOUT = 3                   # timeout for most flash operations
START_FLASH_TIMEOUT = 20              # timeout for starting flash (may perform erase)
CHIP_ERASE_TIMEOUT = 120              # timeout for full chip erase
MAX_TIMEOUT = CHIP_ERASE_TIMEOUT * 2  # longest any command can run
SYNC_TIMEOUT = 0.1                    # timeout for syncing with bootloader
MD5_TIMEOUT_PER_MB = 8                # timeout (per megabyte) for calculating md5sum
ERASE_REGION_TIMEOUT_PER_MB = 30      # timeout (per megabyte) for erasing a region
ERASE_WRITE_TIMEOUT_PER_MB = 40       # timeout (per megabyte) for erasing and writing data
MEM_END_ROM_TIMEOUT = 0.05            # special short timeout for ESP_MEM_END, as it may never respond
DEFAULT_SERIAL_WRITE_TIMEOUT = 10     # timeout for serial port write
DEFAULT_CONNECT_ATTEMPTS = 7          # default number of times to try connection


def timeout_per_mb(seconds_per_mb, size_bytes):
    """ Scales timeouts which are size-specific """
    result = seconds_per_mb * (size_bytes / 1e6)
    if result < DEFAULT_TIMEOUT:
        return DEFAULT_TIMEOUT
    return result


def _chip_to_rom_loader(chip):
    return {
        'esp8266': ESP8266ROM,
        'esp32': ESP32ROM,
        'esp32s2': ESP32S2ROM,
        'esp32s3beta2': ESP32S3BETA2ROM,
        'esp32c3': ESP32C3ROM,
    }[chip]


def get_default_connected_device(serial_list, port, connect_attempts, initial_baud, chip='auto', trace=False,
                                 before='default_reset'):
    _esp = None
    for each_port in reversed(serial_list):
        print("Serial port %s" % each_port)
        try:
            if chip == 'auto':
                _esp = ESPLoader.detect_chip(each_port, initial_baud, before, trace,
                                             connect_attempts)
            else:
                chip_class = _chip_to_rom_loader(chip)
                _esp = chip_class(each_port, initial_baud, trace)
                _esp.connect(before, connect_attempts)
            break
        except (FatalError, OSError) as err:
            if port is not None:
                raise
            print("%s failed to connect: %s" % (each_port, err))
            _esp = None
    return _esp


DETECTED_FLASH_SIZES = {0x12: '256KB', 0x13: '512KB', 0x14: '1MB',
                        0x15: '2MB', 0x16: '4MB', 0x17: '8MB', 0x18: '16MB'}


def check_supported_function(func, check_func):
    """
    Decorator implementation that wraps a check around an ESPLoader
    bootloader function to check if it's supported.

    This is used to capture the multidimensional differences in
    functionality between the ESP8266 & ESP32/32S2/32S3/32C3 ROM loaders, and the
    software stub that runs on both. Not possible to do this cleanly
    via inheritance alone.
    """
    def inner(*args, **kwargs):
        obj = args[0]
        if check_func(obj):
            return func(*args, **kwargs)
        else:
            raise NotImplementedInROMError(obj, func)
    return inner


def stub_function_only(func):
    """ Attribute for a function only supported in the software stub loader """
    return check_supported_function(func, lambda o: o.IS_STUB)


def stub_and_esp32_function_only(func):
    """ Attribute for a function only supported by software stubs or ESP32/32S2/32S3/32C3 ROM """
    return check_supported_function(func, lambda o: o.IS_STUB or isinstance(o, ESP32ROM))


PYTHON2 = sys.version_info[0] < 3  # True if on pre-Python 3

# Function to return nth byte of a bitstring
# Different behaviour on Python 2 vs 3
if PYTHON2:
    def byte(bitstr, index):
        return ord(bitstr[index])
else:
    def byte(bitstr, index):
        return bitstr[index]

# Provide a 'basestring' class on Python 3
try:
    basestring
except NameError:
    basestring = str


def print_overwrite(message, last_line=False):
    """ Print a message, overwriting the currently printed line.

    If last_line is False, don't append a newline at the end (expecting another subsequent call will overwrite this one.)

    After a sequence of calls with last_line=False, call once with last_line=True.

    If output is not a TTY (for example redirected a pipe), no overwriting happens and this function is the same as print().
    """
    if sys.stdout.isatty():
        print("\r%s" % message, end='\n' if last_line else '')
    else:
        print(message)


def _mask_to_shift(mask):
    """ Return the index of the least significant bit in the mask """
    shift = 0
    while mask & 0x1 == 0:
        shift += 1
        mask >>= 1
    return shift


def esp8266_function_only(func):
    """ Attribute for a function only supported on ESP8266 """
    return check_supported_function(func, lambda o: o.CHIP_NAME == "ESP8266")


class ESPLoader(object):
    """ Base class providing access to ESP ROM & software stub bootloaders.
    Subclasses provide ESP8266 & ESP32 specific functionality.

    Don't instantiate this base class directly, either instantiate a subclass or
    call ESPLoader.detect_chip() which will interrogate the chip and return the
    appropriate subclass instance.

    """
    CHIP_NAME = "Espressif device"
    IS_STUB = False

    DEFAULT_PORT = "/dev/ttyUSB0"

    # Commands supported by ESP8266 ROM bootloader
    ESP_FLASH_BEGIN = 0x02
    ESP_FLASH_DATA  = 0x03
    ESP_FLASH_END   = 0x04
    ESP_MEM_BEGIN   = 0x05
    ESP_MEM_END     = 0x06
    ESP_MEM_DATA    = 0x07
    ESP_SYNC        = 0x08
    ESP_WRITE_REG   = 0x09
    ESP_READ_REG    = 0x0a

    # Some comands supported by ESP32 ROM bootloader (or -8266 w/ stub)
    ESP_SPI_SET_PARAMS = 0x0B
    ESP_SPI_ATTACH     = 0x0D
    ESP_READ_FLASH_SLOW  = 0x0e  # ROM only, much slower than the stub flash read
    ESP_CHANGE_BAUDRATE = 0x0F
    ESP_FLASH_DEFL_BEGIN = 0x10
    ESP_FLASH_DEFL_DATA  = 0x11
    ESP_FLASH_DEFL_END   = 0x12
    ESP_SPI_FLASH_MD5    = 0x13

    # Commands supported by ESP32-S2/S3/C3 ROM bootloader only
    ESP_GET_SECURITY_INFO = 0x14

    # Some commands supported by stub only
    ESP_ERASE_FLASH = 0xD0
    ESP_ERASE_REGION = 0xD1
    ESP_READ_FLASH = 0xD2
    ESP_RUN_USER_CODE = 0xD3

    # Flash encryption encrypted data command
    ESP_FLASH_ENCRYPT_DATA = 0xD4

    # Response code(s) sent by ROM
    ROM_INVALID_RECV_MSG = 0x05   # response if an invalid message is received

    # Maximum block sized for RAM and Flash writes, respectively.
    ESP_RAM_BLOCK   = 0x1800

    FLASH_WRITE_SIZE = 0x400

    # Default baudrate. The ROM auto-bauds, so we can use more or less whatever we want.
    ESP_ROM_BAUD    = 115200

    # First byte of the application image
    ESP_IMAGE_MAGIC = 0xe9

    # Initial state for the checksum routine
    ESP_CHECKSUM_MAGIC = 0xef

    # Flash sector size, minimum unit of erase.
    FLASH_SECTOR_SIZE = 0x1000

    UART_DATE_REG_ADDR = 0x60000078

    CHIP_DETECT_MAGIC_REG_ADDR = 0x40001000  # This ROM address has a different value on each chip model

    UART_CLKDIV_MASK = 0xFFFFF

    # Memory addresses
    IROM_MAP_START = 0x40200000
    IROM_MAP_END = 0x40300000

    # The number of bytes in the UART response that signify command status
    STATUS_BYTES_LENGTH = 2

    # Response to ESP_SYNC might indicate that flasher stub is running instead of the ROM bootloader
    sync_stub_detected = False

    def __init__(self, port=DEFAULT_PORT, baud=ESP_ROM_BAUD, trace_enabled=False):
        """Base constructor for ESPLoader bootloader interaction

        Don't call this constructor, either instantiate ESP8266ROM
        or ESP32ROM, or use ESPLoader.detect_chip().

        This base class has all of the instance methods for bootloader
        functionality supported across various chips & stub
        loaders. Subclasses replace the functions they don't support
        with ones which throw NotImplementedInROMError().

        """
        self.secure_download_mode = False  # flag is set to True if esptool detects the ROM is in Secure Download Mode

        if isinstance(port, basestring):
            self._port = serial.serial_for_url(port)
        else:
            self._port = port
        self._slip_reader = slip_reader(self._port, self.trace)
        # setting baud rate in a separate step is a workaround for
        # CH341 driver on some Linux versions (this opens at 9600 then
        # sets), shouldn't matter for other platforms/drivers. See
        # https://github.com/espressif/esptool/issues/44#issuecomment-107094446
        self._set_port_baudrate(baud)
        self._trace_enabled = trace_enabled
        # set write timeout, to prevent esptool blocked at write forever.
        try:
            self._port.write_timeout = DEFAULT_SERIAL_WRITE_TIMEOUT
        except NotImplementedError:
            # no write timeout for RFC2217 ports
            # need to set the property back to None or it will continue to fail
            self._port.write_timeout = None

    @property
    def serial_port(self):
        return self._port.port

    def _set_port_baudrate(self, baud):
        try:
            self._port.baudrate = baud
        except IOError:
            raise FatalError("Failed to set baud rate %d. The driver may not support this rate." % baud)

    @staticmethod
    def detect_chip(port=DEFAULT_PORT, baud=ESP_ROM_BAUD, connect_mode='default_reset', trace_enabled=False,
                    connect_attempts=DEFAULT_CONNECT_ATTEMPTS):
        """ Use serial access to detect the chip type.

        We use the UART's datecode register for this, it's mapped at
        the same address on ESP8266 & ESP32 so we can use one
        memory read and compare to the datecode register for each chip
        type.

        This routine automatically performs ESPLoader.connect() (passing
        connect_mode parameter) as part of querying the chip.
        """
        detect_port = ESPLoader(port, baud, trace_enabled=trace_enabled)
        detect_port.connect(connect_mode, connect_attempts, detecting=True)
        try:
            print('Detecting chip type...', end='')
            sys.stdout.flush()
            chip_magic_value = detect_port.read_reg(ESPLoader.CHIP_DETECT_MAGIC_REG_ADDR)

            for cls in [ESP8266ROM, ESP32ROM, ESP32S2ROM, ESP32S3BETA2ROM, ESP32C3ROM]:
                if chip_magic_value == cls.CHIP_DETECT_MAGIC_VALUE:
                    # don't connect a second time
                    inst = cls(detect_port._port, baud, trace_enabled=trace_enabled)
                    inst._post_connect()
                    print(' %s' % inst.CHIP_NAME, end='')
                    if detect_port.sync_stub_detected:
                        inst = inst.STUB_CLASS(inst)
                        inst.sync_stub_detected = True
                    return inst
        except UnsupportedCommandError:
            raise FatalError("Unsupported Command Error received. Probably this means Secure Download Mode is enabled, "
                             "autodetection will not work. Need to manually specify the chip.")
        finally:
            print('')  # end line
        raise FatalError("Unexpected CHIP magic value 0x%08x. Failed to autodetect chip type." % (chip_magic_value))

    """ Read a SLIP packet from the serial port """
    def read(self):
        return next(self._slip_reader)

    """ Write bytes to the serial port while performing SLIP escaping """
    def write(self, packet):
        buf = b'\xc0' \
              + (packet.replace(b'\xdb', b'\xdb\xdd').replace(b'\xc0', b'\xdb\xdc')) \
              + b'\xc0'
        self.trace("Write %d bytes: %s", len(buf), HexFormatter(buf))
        self._port.write(buf)

    def trace(self, message, *format_args):
        if self._trace_enabled:
            now = time.time()
            try:

                delta = now - self._last_trace
            except AttributeError:
                delta = 0.0
            self._last_trace = now
            prefix = "TRACE +%.3f " % delta
            print(prefix + (message % format_args))

    """ Calculate checksum of a blob, as it is defined by the ROM """
    @staticmethod
    def checksum(data, state=ESP_CHECKSUM_MAGIC):
        for b in data:
            if type(b) is int:  # python 2/3 compat
                state ^= b
            else:
                state ^= ord(b)

        return state

    """ Send a request and read the response """
    def command(self, op=None, data=b"", chk=0, wait_response=True, timeout=DEFAULT_TIMEOUT):
        saved_timeout = self._port.timeout
        new_timeout = min(timeout, MAX_TIMEOUT)
        if new_timeout != saved_timeout:
            self._port.timeout = new_timeout

        try:
            if op is not None:
                self.trace("command op=0x%02x data len=%s wait_response=%d timeout=%.3f data=%s",
                           op, len(data), 1 if wait_response else 0, timeout, HexFormatter(data))
                pkt = struct.pack(b'<BBHI', 0x00, op, len(data), chk) + data
                self.write(pkt)

            if not wait_response:
                return

            self._port.flush()

            # tries to get a response until that response has the
            # same operation as the request or a retries limit has
            # exceeded. This is needed for some esp8266s that
            # reply with more sync responses than expected.
            for retry in range(100):
                p = self.read()
                if len(p) < 8:
                    continue
                (resp, op_ret, len_ret, val) = struct.unpack('<BBHI', p[:8])
                if resp != 1:
                    continue
                data = p[8:]

                if op is None or op_ret == op:
                    return val, data
                if byte(data, 0) != 0 and byte(data, 1) == self.ROM_INVALID_RECV_MSG:
                    self.flush_input()  # Unsupported read_reg can result in more than one error response for some reason
                    raise UnsupportedCommandError(self, op)

        finally:
            if new_timeout != saved_timeout:
                self._port.timeout = saved_timeout

        raise FatalError("Response doesn't match request")

    def check_command(self, op_description, op=None, data=b'', chk=0, timeout=DEFAULT_TIMEOUT):
        """
        Execute a command with 'command', check the result code and throw an appropriate
        FatalError if it fails.

        Returns the "result" of a successful command.
        """
        val, data = self.command(op, data, chk, timeout=timeout)

        # things are a bit weird here, bear with us

        # the status bytes are the last 2/4 bytes in the data (depending on chip)
        if len(data) < self.STATUS_BYTES_LENGTH:
            raise FatalError("Failed to %s. Only got %d byte status response." % (op_description, len(data)))
        status_bytes = data[-self.STATUS_BYTES_LENGTH:]
        # we only care if the first one is non-zero. If it is, the second byte is a reason.
        if byte(status_bytes, 0) != 0:
            raise FatalError.WithResult('Failed to %s' % op_description, status_bytes)

        # if we had more data than just the status bytes, return it as the result
        # (this is used by the md5sum command, maybe other commands?)
        if len(data) > self.STATUS_BYTES_LENGTH:
            return data[:-self.STATUS_BYTES_LENGTH]
        else:  # otherwise, just return the 'val' field which comes from the reply header (this is used by read_reg)
            return val

    def flush_input(self):
        self._port.flushInput()
        self._slip_reader = slip_reader(self._port, self.trace)

    def sync(self):
        val, _ = self.command(self.ESP_SYNC, b'\x07\x07\x12\x20' + 32 * b'\x55',
                              timeout=SYNC_TIMEOUT)

        # ROM bootloaders send some non-zero "val" response. The flasher stub sends 0. If we receive 0 then it
        # probably indicates that the chip wasn't or couldn't be reseted properly and esptool is talking to the
        # flasher stub.
        self.sync_stub_detected = val == 0

        for _ in range(7):
            val, _ = self.command()
            self.sync_stub_detected &= val == 0

    def _setDTR(self, state):
        self._port.setDTR(state)

    def _setRTS(self, state):
        self._port.setRTS(state)
        # Work-around for adapters on Windows using the usbser.sys driver:
        # generate a dummy change to DTR so that the set-control-line-state
        # request is sent with the updated RTS state and the same DTR state
        self._port.setDTR(self._port.dtr)

    def _connect_attempt(self, mode='default_reset', esp32r0_delay=False):
        """ A single connection attempt, with esp32r0 workaround options """
        # esp32r0_delay is a workaround for bugs with the most common auto reset
        # circuit and Windows, if the EN pin on the dev board does not have
        # enough capacitance.
        #
        # Newer dev boards shouldn't have this problem (higher value capacitor
        # on the EN pin), and ESP32 revision 1 can't use this workaround as it
        # relies on a silicon bug.
        #
        # Details: https://github.com/espressif/esptool/issues/136
        last_error = None

        # If we're doing no_sync, we're likely communicating as a pass through
        # with an intermediate device to the ESP32
        if mode == "no_reset_no_sync":
            return last_error

        # issue reset-to-bootloader:
        # RTS = either CH_PD/EN or nRESET (both active low = chip in reset
        # DTR = GPIO0 (active low = boot to flasher)
        #
        # DTR & RTS are active low signals,
        # ie True = pin @ 0V, False = pin @ VCC.
        if mode != 'no_reset':
            self._setDTR(False)  # IO0=HIGH
            self._setRTS(True)   # EN=LOW, chip in reset
            time.sleep(0.1)
            if esp32r0_delay:
                # Some chips are more likely to trigger the esp32r0
                # watchdog reset silicon bug if they're held with EN=LOW
                # for a longer period
                time.sleep(1.2)
            self._setDTR(True)   # IO0=LOW
            self._setRTS(False)  # EN=HIGH, chip out of reset
            if esp32r0_delay:
                # Sleep longer after reset.
                # This workaround only works on revision 0 ESP32 chips,
                # it exploits a silicon bug spurious watchdog reset.
                time.sleep(0.4)  # allow watchdog reset to occur
            time.sleep(0.05)
            self._setDTR(False)  # IO0=HIGH, done

        for _ in range(5):
            try:
                self.flush_input()
                self._port.flushOutput()
                self.sync()
                return None
            except FatalError as e:
                if esp32r0_delay:
                    print('_', end='')
                else:
                    print('.', end='')
                sys.stdout.flush()
                time.sleep(0.05)
                last_error = e
        return last_error

    def get_memory_region(self, name):
        """ Returns a tuple of (start, end) for the memory map entry with the given name, or None if it doesn't exist
        """
        try:
            return [(start, end) for (start, end, n) in self.MEMORY_MAP if n == name][0]
        except IndexError:
            return None

    def connect(self, mode='default_reset', attempts=DEFAULT_CONNECT_ATTEMPTS, detecting=False):
        """ Try connecting repeatedly until successful, or giving up """
        print('Connecting...', end='')
        sys.stdout.flush()
        last_error = None

        try:
            for _ in range(attempts) if attempts > 0 else itertools.count():
                last_error = self._connect_attempt(mode=mode, esp32r0_delay=False)
                if last_error is None:
                    break
                last_error = self._connect_attempt(mode=mode, esp32r0_delay=True)
                if last_error is None:
                    break
        finally:
            print('')  # end 'Connecting...' line

        if last_error is not None:
            raise FatalError('Failed to connect to %s: %s' % (self.CHIP_NAME, last_error))

        if not detecting:
            try:
                # check the date code registers match what we expect to see
                chip_magic_value = self.read_reg(ESPLoader.CHIP_DETECT_MAGIC_REG_ADDR)
                if chip_magic_value != self.CHIP_DETECT_MAGIC_VALUE:
                    actually = None
                    for cls in [ESP8266ROM, ESP32ROM, ESP32S2ROM, ESP32S3BETA2ROM, ESP32C3ROM]:
                        if chip_magic_value == cls.CHIP_DETECT_MAGIC_VALUE:
                            actually = cls
                            break
                    if actually is None:
                        print(("WARNING: This chip doesn't appear to be a %s (chip magic value 0x%08x). "
                               "Probably it is unsupported by this version of esptool.") % (self.CHIP_NAME, chip_magic_value))
                    else:
                        raise FatalError("This chip is %s not %s. Wrong --chip argument?" % (actually.CHIP_NAME, self.CHIP_NAME))
            except UnsupportedCommandError:
                self.secure_download_mode = True
            self._post_connect()

    def _post_connect(self):
        """
        Additional initialization hook, may be overridden by the chip-specific class.
        Gets called after connect, and after auto-detection.
        """
        pass

    def read_reg(self, addr, timeout=DEFAULT_TIMEOUT):
        """ Read memory address in target """
        # we don't call check_command here because read_reg() function is called
        # when detecting chip type, and the way we check for success (STATUS_BYTES_LENGTH) is different
        # for different chip types (!)
        val, data = self.command(self.ESP_READ_REG, struct.pack('<I', addr), timeout=timeout)
        if byte(data, 0) != 0:
            raise FatalError.WithResult("Failed to read register address %08x" % addr, data)
        return val

    """ Write to memory address in target """
    def write_reg(self, addr, value, mask=0xFFFFFFFF, delay_us=0, delay_after_us=0):
        command = struct.pack('<IIII', addr, value, mask, delay_us)
        if delay_after_us > 0:
            # add a dummy write to a date register as an excuse to have a delay
            command += struct.pack('<IIII', self.UART_DATE_REG_ADDR, 0, 0, delay_after_us)

        return self.check_command("write target memory", self.ESP_WRITE_REG, command)

    def update_reg(self, addr, mask, new_val):
        """ Update register at 'addr', replace the bits masked out by 'mask'
        with new_val. new_val is shifted left to match the LSB of 'mask'

        Returns just-written value of register.
        """
        shift = _mask_to_shift(mask)
        val = self.read_reg(addr)
        val &= ~mask
        val |= (new_val << shift) & mask
        self.write_reg(addr, val)

        return val

    """ Start downloading an application image to RAM """
    def mem_begin(self, size, blocks, blocksize, offset):
        if self.IS_STUB:  # check we're not going to overwrite a running stub with this data
            stub = self.STUB_CODE
            load_start = offset
            load_end = offset + size
            for (start, end) in [(stub["data_start"], stub["data_start"] + len(stub["data"])),
                                 (stub["text_start"], stub["text_start"] + len(stub["text"]))]:
                if load_start < end and load_end > start:
                    raise FatalError(("Software loader is resident at 0x%08x-0x%08x. "
                                      "Can't load binary at overlapping address range 0x%08x-0x%08x. "
                                      "Either change binary loading address, or use the --no-stub "
                                      "option to disable the software loader.") % (start, end, load_start, load_end))

        return self.check_command("enter RAM download mode", self.ESP_MEM_BEGIN,
                                  struct.pack('<IIII', size, blocks, blocksize, offset))

    """ Send a block of an image to RAM """
    def mem_block(self, data, seq):
        return self.check_command("write to target RAM", self.ESP_MEM_DATA,
                                  struct.pack('<IIII', len(data), seq, 0, 0) + data,
                                  self.checksum(data))

    """ Leave download mode and run the application """
    def mem_finish(self, entrypoint=0):
        # Sending ESP_MEM_END usually sends a correct response back, however sometimes
        # (with ROM loader) the executed code may reset the UART or change the baud rate
        # before the transmit FIFO is empty. So in these cases we set a short timeout and
        # ignore errors.
        timeout = DEFAULT_TIMEOUT if self.IS_STUB else MEM_END_ROM_TIMEOUT
        data = struct.pack('<II', int(entrypoint == 0), entrypoint)
        try:
            return self.check_command("leave RAM download mode", self.ESP_MEM_END,
                                      data=data, timeout=timeout)
        except FatalError:
            if self.IS_STUB:
                raise
            pass

    """ Start downloading to Flash (performs an erase)

    Returns number of blocks (of size self.FLASH_WRITE_SIZE) to write.
    """
    def flash_begin(self, size, offset, begin_rom_encrypted=False):
        num_blocks = (size + self.FLASH_WRITE_SIZE - 1) // self.FLASH_WRITE_SIZE
        erase_size = self.get_erase_size(offset, size)

        t = time.time()
        if self.IS_STUB:
            timeout = DEFAULT_TIMEOUT
        else:
            timeout = timeout_per_mb(ERASE_REGION_TIMEOUT_PER_MB, size)  # ROM performs the erase up front

        params = struct.pack('<IIII', erase_size, num_blocks, self.FLASH_WRITE_SIZE, offset)
        if isinstance(self, (ESP32S2ROM, ESP32S3BETA2ROM, ESP32C3ROM)) and not self.IS_STUB:
            params += struct.pack('<I', 1 if begin_rom_encrypted else 0)
        self.check_command("enter Flash download mode", self.ESP_FLASH_BEGIN,
                           params, timeout=timeout)
        if size != 0 and not self.IS_STUB:
            print("Took %.2fs to erase flash block" % (time.time() - t))
        return num_blocks

    """ Write block to flash """
    def flash_block(self, data, seq, timeout=DEFAULT_TIMEOUT):
        self.check_command("write to target Flash after seq %d" % seq,
                           self.ESP_FLASH_DATA,
                           struct.pack('<IIII', len(data), seq, 0, 0) + data,
                           self.checksum(data),
                           timeout=timeout)

    """ Encrypt before writing to flash """
    def flash_encrypt_block(self, data, seq, timeout=DEFAULT_TIMEOUT):
        if isinstance(self, (ESP32S2ROM, ESP32C3ROM)) and not self.IS_STUB:
            # ROM support performs the encrypted writes via the normal write command,
            # triggered by flash_begin(begin_rom_encrypted=True)
            return self.flash_block(data, seq, timeout)

        self.check_command("Write encrypted to target Flash after seq %d" % seq,
                           self.ESP_FLASH_ENCRYPT_DATA,
                           struct.pack('<IIII', len(data), seq, 0, 0) + data,
                           self.checksum(data),
                           timeout=timeout)

    """ Leave flash mode and run/reboot """
    def flash_finish(self, reboot=False):
        pkt = struct.pack('<I', int(not reboot))
        # stub sends a reply to this command
        self.check_command("leave Flash mode", self.ESP_FLASH_END, pkt)

    """ Run application code in flash """
    def run(self, reboot=False):
        # Fake flash begin immediately followed by flash end
        self.flash_begin(0, 0)
        self.flash_finish(reboot)

    """ Read SPI flash manufacturer and device id """
    def flash_id(self):
        SPIFLASH_RDID = 0x9F
        return self.run_spiflash_command(SPIFLASH_RDID, b"", 24)

    def get_security_info(self):
        # TODO: this only works on the ESP32S2 ROM code loader and needs to work in stub loader also
        res = self.check_command('get security info', self.ESP_GET_SECURITY_INFO, b'')
        res = struct.unpack("<IBBBBBBBB", res)
        flags, flash_crypt_cnt, key_purposes = res[0], res[1], res[2:]
        # TODO: pack this as some kind of better data type
        return (flags, flash_crypt_cnt, key_purposes)

    @classmethod
    def parse_flash_size_arg(cls, arg):
        try:
            return cls.FLASH_SIZES[arg]
        except KeyError:
            raise FatalError("Flash size '%s' is not supported by this chip type. Supported sizes: %s"
                             % (arg, ", ".join(cls.FLASH_SIZES.keys())))

    def run_stub(self, stub=None):
        if stub is None:
            stub = self.STUB_CODE

        if self.sync_stub_detected:
            print("Stub is already running. No upload is necessary.")
            return self.STUB_CLASS(self)

        # Upload
        print("Uploading stub...")
        for field in ['text', 'data']:
            if field in stub:
                offs = stub[field + "_start"]
                length = len(stub[field])
                blocks = (length + self.ESP_RAM_BLOCK - 1) // self.ESP_RAM_BLOCK
                self.mem_begin(length, blocks, self.ESP_RAM_BLOCK, offs)
                for seq in range(blocks):
                    from_offs = seq * self.ESP_RAM_BLOCK
                    to_offs = from_offs + self.ESP_RAM_BLOCK
                    self.mem_block(stub[field][from_offs:to_offs], seq)
        print("Running stub...")
        self.mem_finish(stub['entry'])

        p = self.read()
        if p != b'OHAI':
            raise FatalError("Failed to start stub. Unexpected response: %s" % p)
        print("Stub running...")
        return self.STUB_CLASS(self)

    @stub_and_esp32_function_only
    def flash_defl_begin(self, size, compsize, offset):
        """ Start downloading compressed data to Flash (performs an erase)

        Returns number of blocks (size self.FLASH_WRITE_SIZE) to write.
        """
        num_blocks = (compsize + self.FLASH_WRITE_SIZE - 1) // self.FLASH_WRITE_SIZE
        erase_blocks = (size + self.FLASH_WRITE_SIZE - 1) // self.FLASH_WRITE_SIZE

        t = time.time()
        if self.IS_STUB:
            write_size = size  # stub expects number of bytes here, manages erasing internally
            timeout = DEFAULT_TIMEOUT
        else:
            write_size = erase_blocks * self.FLASH_WRITE_SIZE  # ROM expects rounded up to erase block size
            timeout = timeout_per_mb(ERASE_REGION_TIMEOUT_PER_MB, write_size)  # ROM performs the erase up front
        print("Compressed %d bytes to %d..." % (size, compsize))
        params = struct.pack('<IIII', write_size, num_blocks, self.FLASH_WRITE_SIZE, offset)
        if isinstance(self, (ESP32S2ROM, ESP32S3BETA2ROM, ESP32C3ROM)) and not self.IS_STUB:
            params += struct.pack('<I', 0)  # extra param is to enter encrypted flash mode via ROM (not supported currently)
        self.check_command("enter compressed flash mode", self.ESP_FLASH_DEFL_BEGIN, params, timeout=timeout)
        if size != 0 and not self.IS_STUB:
            # (stub erases as it writes, but ROM loaders erase on begin)
            print("Took %.2fs to erase flash block" % (time.time() - t))
        return num_blocks

    """ Write block to flash, send compressed """
    @stub_and_esp32_function_only
    def flash_defl_block(self, data, seq, timeout=DEFAULT_TIMEOUT):
        self.check_command("write compressed data to flash after seq %d" % seq,
                           self.ESP_FLASH_DEFL_DATA, struct.pack('<IIII', len(data), seq, 0, 0) + data, self.checksum(data), timeout=timeout)

    """ Leave compressed flash mode and run/reboot """
    @stub_and_esp32_function_only
    def flash_defl_finish(self, reboot=False):
        if not reboot and not self.IS_STUB:
            # skip sending flash_finish to ROM loader, as this
            # exits the bootloader. Stub doesn't do this.
            return
        pkt = struct.pack('<I', int(not reboot))
        self.check_command("leave compressed flash mode", self.ESP_FLASH_DEFL_END, pkt)
        self.in_bootloader = False

    @stub_and_esp32_function_only
    def flash_md5sum(self, addr, size):
        # the MD5 command returns additional bytes in the standard
        # command reply slot
        timeout = timeout_per_mb(MD5_TIMEOUT_PER_MB, size)
        res = self.check_command('calculate md5sum', self.ESP_SPI_FLASH_MD5, struct.pack('<IIII', addr, size, 0, 0),
                                 timeout=timeout)

        if len(res) == 32:
            return res.decode("utf-8")  # already hex formatted
        elif len(res) == 16:
            return hexify(res).lower()
        else:
            raise FatalError("MD5Sum command returned unexpected result: %r" % res)

    @stub_and_esp32_function_only
    def change_baud(self, baud):
        print("Changing baud rate to %d" % baud)
        # stub takes the new baud rate and the old one
        second_arg = self._port.baudrate if self.IS_STUB else 0
        self.command(self.ESP_CHANGE_BAUDRATE, struct.pack('<II', baud, second_arg))
        print("Changed.")
        self._set_port_baudrate(baud)
        time.sleep(0.05)  # get rid of crap sent during baud rate change
        self.flush_input()

    @stub_function_only
    def erase_flash(self):
        # depending on flash chip model the erase may take this long (maybe longer!)
        self.check_command("erase flash", self.ESP_ERASE_FLASH,
                           timeout=CHIP_ERASE_TIMEOUT)

    @stub_function_only
    def erase_region(self, offset, size):
        if offset % self.FLASH_SECTOR_SIZE != 0:
            raise FatalError("Offset to erase from must be a multiple of 4096")
        if size % self.FLASH_SECTOR_SIZE != 0:
            raise FatalError("Size of data to erase must be a multiple of 4096")
        timeout = timeout_per_mb(ERASE_REGION_TIMEOUT_PER_MB, size)
        self.check_command("erase region", self.ESP_ERASE_REGION, struct.pack('<II', offset, size), timeout=timeout)

    def read_flash_slow(self, offset, length, progress_fn):
        raise NotImplementedInROMError(self, self.read_flash_slow)

    def read_flash(self, offset, length, progress_fn=None):
        if not self.IS_STUB:
            return self.read_flash_slow(offset, length, progress_fn)  # ROM-only routine

        # issue a standard bootloader command to trigger the read
        self.check_command("read flash", self.ESP_READ_FLASH,
                           struct.pack('<IIII',
                                       offset,
                                       length,
                                       self.FLASH_SECTOR_SIZE,
                                       64))
        # now we expect (length // block_size) SLIP frames with the data
        data = b''
        while len(data) < length:
            p = self.read()
            data += p
            if len(data) < length and len(p) < self.FLASH_SECTOR_SIZE:
                raise FatalError('Corrupt data, expected 0x%x bytes but received 0x%x bytes' % (self.FLASH_SECTOR_SIZE, len(p)))
            self.write(struct.pack('<I', len(data)))
            if progress_fn and (len(data) % 1024 == 0 or len(data) == length):
                progress_fn(len(data), length)
        if progress_fn:
            progress_fn(len(data), length)
        if len(data) > length:
            raise FatalError('Read more than expected')

        digest_frame = self.read()
        if len(digest_frame) != 16:
            raise FatalError('Expected digest, got: %s' % hexify(digest_frame))
        expected_digest = hexify(digest_frame).upper()
        digest = hashlib.md5(data).hexdigest().upper()
        if digest != expected_digest:
            raise FatalError('Digest mismatch: expected %s, got %s' % (expected_digest, digest))
        return data

    def flash_spi_attach(self, hspi_arg):
        """Send SPI attach command to enable the SPI flash pins

        ESP8266 ROM does this when you send flash_begin, ESP32 ROM
        has it as a SPI command.
        """
        # last 3 bytes in ESP_SPI_ATTACH argument are reserved values
        arg = struct.pack('<I', hspi_arg)
        if not self.IS_STUB:
            # ESP32 ROM loader takes additional 'is legacy' arg, which is not
            # currently supported in the stub loader or esptool.py (as it's not usually needed.)
            is_legacy = 0
            arg += struct.pack('BBBB', is_legacy, 0, 0, 0)
        self.check_command("configure SPI flash pins", ESP32ROM.ESP_SPI_ATTACH, arg)

    def flash_set_parameters(self, size):
        """Tell the ESP bootloader the parameters of the chip

        Corresponds to the "flashchip" data structure that the ROM
        has in RAM.

        'size' is in bytes.

        All other flash parameters are currently hardcoded (on ESP8266
        these are mostly ignored by ROM code, on ESP32 I'm not sure.)
        """
        fl_id = 0
        total_size = size
        block_size = 64 * 1024
        sector_size = 4 * 1024
        page_size = 256
        status_mask = 0xffff
        self.check_command("set SPI params", ESP32ROM.ESP_SPI_SET_PARAMS,
                           struct.pack('<IIIIII', fl_id, total_size, block_size, sector_size, page_size, status_mask))

    def run_spiflash_command(self, spiflash_command, data=b"", read_bits=0):
        """Run an arbitrary SPI flash command.

        This function uses the "USR_COMMAND" functionality in the ESP
        SPI hardware, rather than the precanned commands supported by
        hardware. So the value of spiflash_command is an actual command
        byte, sent over the wire.

        After writing command byte, writes 'data' to MOSI and then
        reads back 'read_bits' of reply on MISO. Result is a number.
        """

        # SPI_USR register flags
        SPI_USR_COMMAND = (1 << 31)
        SPI_USR_MISO    = (1 << 28)
        SPI_USR_MOSI    = (1 << 27)

        # SPI registers, base address differs ESP32* vs 8266
        base = self.SPI_REG_BASE
        SPI_CMD_REG       = base + 0x00
        SPI_USR_REG       = base + self.SPI_USR_OFFS
        SPI_USR1_REG      = base + self.SPI_USR1_OFFS
        SPI_USR2_REG      = base + self.SPI_USR2_OFFS
        SPI_W0_REG        = base + self.SPI_W0_OFFS

        # following two registers are ESP32 & 32S2/32C3 only
        if self.SPI_MOSI_DLEN_OFFS is not None:
            # ESP32/32S2/32C3 has a more sophisticated way to set up "user" commands
            def set_data_lengths(mosi_bits, miso_bits):
                SPI_MOSI_DLEN_REG = base + self.SPI_MOSI_DLEN_OFFS
                SPI_MISO_DLEN_REG = base + self.SPI_MISO_DLEN_OFFS
                if mosi_bits > 0:
                    self.write_reg(SPI_MOSI_DLEN_REG, mosi_bits - 1)
                if miso_bits > 0:
                    self.write_reg(SPI_MISO_DLEN_REG, miso_bits - 1)
        else:

            def set_data_lengths(mosi_bits, miso_bits):
                SPI_DATA_LEN_REG = SPI_USR1_REG
                SPI_MOSI_BITLEN_S = 17
                SPI_MISO_BITLEN_S = 8
                mosi_mask = 0 if (mosi_bits == 0) else (mosi_bits - 1)
                miso_mask = 0 if (miso_bits == 0) else (miso_bits - 1)
                self.write_reg(SPI_DATA_LEN_REG,
                               (miso_mask << SPI_MISO_BITLEN_S) | (
                                   mosi_mask << SPI_MOSI_BITLEN_S))

        # SPI peripheral "command" bitmasks for SPI_CMD_REG
        SPI_CMD_USR  = (1 << 18)

        # shift values
        SPI_USR2_COMMAND_LEN_SHIFT = 28

        if read_bits > 32:
            raise FatalError("Reading more than 32 bits back from a SPI flash operation is unsupported")
        if len(data) > 64:
            raise FatalError("Writing more than 64 bytes of data with one SPI command is unsupported")

        data_bits = len(data) * 8
        old_spi_usr = self.read_reg(SPI_USR_REG)
        old_spi_usr2 = self.read_reg(SPI_USR2_REG)
        flags = SPI_USR_COMMAND
        if read_bits > 0:
            flags |= SPI_USR_MISO
        if data_bits > 0:
            flags |= SPI_USR_MOSI
        set_data_lengths(data_bits, read_bits)
        self.write_reg(SPI_USR_REG, flags)
        self.write_reg(SPI_USR2_REG,
                       (7 << SPI_USR2_COMMAND_LEN_SHIFT) | spiflash_command)
        if data_bits == 0:
            self.write_reg(SPI_W0_REG, 0)  # clear data register before we read it
        else:
            data = pad_to(data, 4, b'\00')  # pad to 32-bit multiple
            words = struct.unpack("I" * (len(data) // 4), data)
            next_reg = SPI_W0_REG
            for word in words:
                self.write_reg(next_reg, word)
                next_reg += 4
        self.write_reg(SPI_CMD_REG, SPI_CMD_USR)

        def wait_done():
            for _ in range(10):
                if (self.read_reg(SPI_CMD_REG) & SPI_CMD_USR) == 0:
                    return
            raise FatalError("SPI command did not complete in time")
        wait_done()

        status = self.read_reg(SPI_W0_REG)
        # restore some SPI controller registers
        self.write_reg(SPI_USR_REG, old_spi_usr)
        self.write_reg(SPI_USR2_REG, old_spi_usr2)
        return status

    def read_status(self, num_bytes=2):
        """Read up to 24 bits (num_bytes) of SPI flash status register contents
        via RDSR, RDSR2, RDSR3 commands

        Not all SPI flash supports all three commands. The upper 1 or 2
        bytes may be 0xFF.
        """
        SPIFLASH_RDSR  = 0x05
        SPIFLASH_RDSR2 = 0x35
        SPIFLASH_RDSR3 = 0x15

        status = 0
        shift = 0
        for cmd in [SPIFLASH_RDSR, SPIFLASH_RDSR2, SPIFLASH_RDSR3][0:num_bytes]:
            status += self.run_spiflash_command(cmd, read_bits=8) << shift
            shift += 8
        return status

    def write_status(self, new_status, num_bytes=2, set_non_volatile=False):
        """Write up to 24 bits (num_bytes) of new status register

        num_bytes can be 1, 2 or 3.

        Not all flash supports the additional commands to write the
        second and third byte of the status register. When writing 2
        bytes, esptool also sends a 16-byte WRSR command (as some
        flash types use this instead of WRSR2.)

        If the set_non_volatile flag is set, non-volatile bits will
        be set as well as volatile ones (WREN used instead of WEVSR).

        """
        SPIFLASH_WRSR = 0x01
        SPIFLASH_WRSR2 = 0x31
        SPIFLASH_WRSR3 = 0x11
        SPIFLASH_WEVSR = 0x50
        SPIFLASH_WREN = 0x06
        SPIFLASH_WRDI = 0x04

        enable_cmd = SPIFLASH_WREN if set_non_volatile else SPIFLASH_WEVSR

        # try using a 16-bit WRSR (not supported by all chips)
        # this may be redundant, but shouldn't hurt
        if num_bytes == 2:
            self.run_spiflash_command(enable_cmd)
            self.run_spiflash_command(SPIFLASH_WRSR, struct.pack("<H", new_status))

        # also try using individual commands (also not supported by all chips for num_bytes 2 & 3)
        for cmd in [SPIFLASH_WRSR, SPIFLASH_WRSR2, SPIFLASH_WRSR3][0:num_bytes]:
            self.run_spiflash_command(enable_cmd)
            self.run_spiflash_command(cmd, struct.pack("B", new_status & 0xFF))
            new_status >>= 8

        self.run_spiflash_command(SPIFLASH_WRDI)

    def get_crystal_freq(self):
        # Figure out the crystal frequency from the UART clock divider
        # Returns a normalized value in integer MHz (40 or 26 are the only supported values)
        #
        # The logic here is:
        # - We know that our baud rate and the ESP UART baud rate are roughly the same, or we couldn't communicate
        # - We can read the UART clock divider register to know how the ESP derives this from the APB bus frequency
        # - Multiplying these two together gives us the bus frequency which is either the crystal frequency (ESP32)
        #   or double the crystal frequency (ESP8266). See the self.XTAL_CLK_DIVIDER parameter for this factor.
        uart_div = self.read_reg(self.UART_CLKDIV_REG) & self.UART_CLKDIV_MASK
        est_xtal = (self._port.baudrate * uart_div) / 1e6 / self.XTAL_CLK_DIVIDER
        norm_xtal = 40 if est_xtal > 33 else 26
        if abs(norm_xtal - est_xtal) > 1:
            print("WARNING: Detected crystal freq %.2fMHz is quite different to normalized freq %dMHz. Unsupported crystal in use?" % (est_xtal, norm_xtal))
        return norm_xtal

    def hard_reset(self):
        self._setRTS(True)  # EN->LOW
        time.sleep(0.1)
        self._setRTS(False)

    def soft_reset(self, stay_in_bootloader):
        if not self.IS_STUB:
            if stay_in_bootloader:
                return  # ROM bootloader is already in bootloader!
            else:
                # 'run user code' is as close to a soft reset as we can do
                self.flash_begin(0, 0)
                self.flash_finish(False)
        else:
            if stay_in_bootloader:
                # soft resetting from the stub loader
                # will re-load the ROM bootloader
                self.flash_begin(0, 0)
                self.flash_finish(True)
            elif self.CHIP_NAME != "ESP8266":
                raise FatalError("Soft resetting is currently only supported on ESP8266")
            else:
                # running user code from stub loader requires some hacks
                # in the stub loader
                self.command(self.ESP_RUN_USER_CODE, wait_response=False)


class ESP8266ROM(ESPLoader):
    """ Access class for ESP8266 ROM bootloader
    """
    CHIP_NAME = "ESP8266"
    IS_STUB = False

    CHIP_DETECT_MAGIC_VALUE = 0xfff0c101

    # OTP ROM addresses
    ESP_OTP_MAC0    = 0x3ff00050
    ESP_OTP_MAC1    = 0x3ff00054
    ESP_OTP_MAC3    = 0x3ff0005c

    SPI_REG_BASE    = 0x60000200
    SPI_USR_OFFS    = 0x1c
    SPI_USR1_OFFS   = 0x20
    SPI_USR2_OFFS   = 0x24
    SPI_MOSI_DLEN_OFFS = None
    SPI_MISO_DLEN_OFFS = None
    SPI_W0_OFFS     = 0x40

    UART_CLKDIV_REG = 0x60000014

    XTAL_CLK_DIVIDER = 2

    FLASH_SIZES = {
        '512KB': 0x00,
        '256KB': 0x10,
        '1MB': 0x20,
        '2MB': 0x30,
        '4MB': 0x40,
        '2MB-c1': 0x50,
        '4MB-c1': 0x60,
        '8MB': 0x80,
        '16MB': 0x90,
    }

    BOOTLOADER_FLASH_OFFSET = 0

    MEMORY_MAP = [[0x3FF00000, 0x3FF00010, "DPORT"],
                  [0x3FFE8000, 0x40000000, "DRAM"],
                  [0x40100000, 0x40108000, "IRAM"],
                  [0x40201010, 0x402E1010, "IROM"]]

    def get_efuses(self):
        # Return the 128 bits of ESP8266 efuse as a single Python integer
        result = self.read_reg(0x3ff0005c) << 96
        result |= self.read_reg(0x3ff00058) << 64
        result |= self.read_reg(0x3ff00054) << 32
        result |= self.read_reg(0x3ff00050)
        return result

    def _get_flash_size(self, efuses):
        # rX_Y = EFUSE_DATA_OUTX[Y]
        r0_4 = (efuses & (1 << 4)) != 0
        r3_25 = (efuses & (1 << 121)) != 0
        r3_26 = (efuses & (1 << 122)) != 0
        r3_27 = (efuses & (1 << 123)) != 0

        if r0_4 and not r3_25:
            if not r3_27 and not r3_26:
                return 1
            elif not r3_27 and r3_26:
                return 2
        if not r0_4 and r3_25:
            if not r3_27 and not r3_26:
                return 2
            elif not r3_27 and r3_26:
                return 4
        return -1

    def get_chip_description(self):
        efuses = self.get_efuses()
        is_8285 = (efuses & ((1 << 4) | 1 << 80)) != 0  # One or the other efuse bit is set for ESP8285
        if is_8285:
            flash_size = self._get_flash_size(efuses)
            max_temp = (efuses & (1 << 5)) != 0  # This efuse bit identifies the max flash temperature
            chip_name = {
                1: "ESP8285H08" if max_temp else "ESP8285N08",
                2: "ESP8285H16" if max_temp else "ESP8285N16"
            }.get(flash_size, "ESP8285")
            return chip_name
        return "ESP8266EX"

    def get_chip_features(self):
        features = ["WiFi"]
        if "ESP8285" in self.get_chip_description():
            features += ["Embedded Flash"]
        return features

    def flash_spi_attach(self, hspi_arg):
        if self.IS_STUB:
            super(ESP8266ROM, self).flash_spi_attach(hspi_arg)
        else:
            # ESP8266 ROM has no flash_spi_attach command in serial protocol,
            # but flash_begin will do it
            self.flash_begin(0, 0)

    def flash_set_parameters(self, size):
        # not implemented in ROM, but OK to silently skip for ROM
        if self.IS_STUB:
            super(ESP8266ROM, self).flash_set_parameters(size)

    def chip_id(self):
        """ Read Chip ID from efuse - the equivalent of the SDK system_get_chip_id() function """
        id0 = self.read_reg(self.ESP_OTP_MAC0)
        id1 = self.read_reg(self.ESP_OTP_MAC1)
        return (id0 >> 24) | ((id1 & MAX_UINT24) << 8)

    def read_mac(self):
        """ Read MAC from OTP ROM """
        mac0 = self.read_reg(self.ESP_OTP_MAC0)
        mac1 = self.read_reg(self.ESP_OTP_MAC1)
        mac3 = self.read_reg(self.ESP_OTP_MAC3)
        if (mac3 != 0):
            oui = ((mac3 >> 16) & 0xff, (mac3 >> 8) & 0xff, mac3 & 0xff)
        elif ((mac1 >> 16) & 0xff) == 0:
            oui = (0x18, 0xfe, 0x34)
        elif ((mac1 >> 16) & 0xff) == 1:
            oui = (0xac, 0xd0, 0x74)
        else:
            raise FatalError("Unknown OUI")
        return oui + ((mac1 >> 8) & 0xff, mac1 & 0xff, (mac0 >> 24) & 0xff)

    def get_erase_size(self, offset, size):
        """ Calculate an erase size given a specific size in bytes.

        Provides a workaround for the bootloader erase bug."""

        sectors_per_block = 16
        sector_size = self.FLASH_SECTOR_SIZE
        num_sectors = (size + sector_size - 1) // sector_size
        start_sector = offset // sector_size

        head_sectors = sectors_per_block - (start_sector % sectors_per_block)
        if num_sectors < head_sectors:
            head_sectors = num_sectors

        if num_sectors < 2 * head_sectors:
            return (num_sectors + 1) // 2 * sector_size
        else:
            return (num_sectors - head_sectors) * sector_size

    def override_vddsdio(self, new_voltage):
        raise NotImplementedInROMError("Overriding VDDSDIO setting only applies to ESP32")


class ESP8266StubLoader(ESP8266ROM):
    """ Access class for ESP8266 stub loader, runs on top of ROM.
    """
    FLASH_WRITE_SIZE = 0x4000  # matches MAX_WRITE_BLOCK in stub_loader.c
    IS_STUB = True

    def __init__(self, rom_loader):
        self.secure_download_mode = rom_loader.secure_download_mode
        self._port = rom_loader._port
        self._trace_enabled = rom_loader._trace_enabled
        self.flush_input()  # resets _slip_reader

    def get_erase_size(self, offset, size):
        return size  # stub doesn't have same size bug as ROM loader


ESP8266ROM.STUB_CLASS = ESP8266StubLoader


class ESP32ROM(ESPLoader):
    """Access class for ESP32 ROM bootloader

    """
    CHIP_NAME = "ESP32"
    IMAGE_CHIP_ID = 0
    IS_STUB = False

    CHIP_DETECT_MAGIC_VALUE = 0x00f01d83

    IROM_MAP_START = 0x400d0000
    IROM_MAP_END   = 0x40400000

    DROM_MAP_START = 0x3F400000
    DROM_MAP_END   = 0x3F800000

    # ESP32 uses a 4 byte status reply
    STATUS_BYTES_LENGTH = 4

    SPI_REG_BASE   = 0x3ff42000
    SPI_USR_OFFS    = 0x1c
    SPI_USR1_OFFS   = 0x20
    SPI_USR2_OFFS   = 0x24
    SPI_MOSI_DLEN_OFFS = 0x28
    SPI_MISO_DLEN_OFFS = 0x2c
    EFUSE_RD_REG_BASE = 0x3ff5a000

    EFUSE_DIS_DOWNLOAD_MANUAL_ENCRYPT_REG = EFUSE_RD_REG_BASE + 0x18
    EFUSE_DIS_DOWNLOAD_MANUAL_ENCRYPT = (1 << 7)  # EFUSE_RD_DISABLE_DL_ENCRYPT

    DR_REG_SYSCON_BASE = 0x3ff66000

    SPI_W0_OFFS = 0x80

    UART_CLKDIV_REG = 0x3ff40014

    XTAL_CLK_DIVIDER = 1

    FLASH_SIZES = {
        '1MB': 0x00,
        '2MB': 0x10,
        '4MB': 0x20,
        '8MB': 0x30,
        '16MB': 0x40
    }

    BOOTLOADER_FLASH_OFFSET = 0x1000

    OVERRIDE_VDDSDIO_CHOICES = ["1.8V", "1.9V", "OFF"]

    MEMORY_MAP = [[0x00000000, 0x00010000, "PADDING"],
                  [0x3F400000, 0x3F800000, "DROM"],
                  [0x3F800000, 0x3FC00000, "EXTRAM_DATA"],
                  [0x3FF80000, 0x3FF82000, "RTC_DRAM"],
                  [0x3FF90000, 0x40000000, "BYTE_ACCESSIBLE"],
                  [0x3FFAE000, 0x40000000, "DRAM"],
                  [0x3FFE0000, 0x3FFFFFFC, "DIRAM_DRAM"],
                  [0x40000000, 0x40070000, "IROM"],
                  [0x40070000, 0x40078000, "CACHE_PRO"],
                  [0x40078000, 0x40080000, "CACHE_APP"],
                  [0x40080000, 0x400A0000, "IRAM"],
                  [0x400A0000, 0x400BFFFC, "DIRAM_IRAM"],
                  [0x400C0000, 0x400C2000, "RTC_IRAM"],
                  [0x400D0000, 0x40400000, "IROM"],
                  [0x50000000, 0x50002000, "RTC_DATA"]]

    FLASH_ENCRYPTED_WRITE_ALIGN = 32

    """ Try to read the BLOCK1 (encryption key) and check if it is valid """

    def is_flash_encryption_key_valid(self):

        """ Bit 0 of efuse_rd_disable[3:0] is mapped to BLOCK1
        this bit is at position 16 in EFUSE_BLK0_RDATA0_REG """
        word0 = self.read_efuse(0)
        rd_disable = (word0 >> 16) & 0x1

        # reading of BLOCK1 is NOT ALLOWED so we assume valid key is programmed
        if rd_disable:
            return True
        else:
            # reading of BLOCK1 is ALLOWED so we will read and verify for non-zero.
            # When ESP32 has not generated AES/encryption key in BLOCK1, the contents will be readable and 0.
            # If the flash encryption is enabled it is expected to have a valid non-zero key. We break out on
            # first occurance of non-zero value
            key_word = [0] * 7
            for i in range(len(key_word)):
                key_word[i] = self.read_efuse(14 + i)
                # key is non-zero so break & return
                if key_word[i] != 0:
                    return True
            return False

    def get_flash_crypt_config(self):
        """ For flash encryption related commands we need to make sure
        user has programmed all the relevant efuse correctly so before
        writing encrypted write_flash_encrypt esptool will verify the values
        of flash_crypt_config to be non zero if they are not read
        protected. If the values are zero a warning will be printed

        bit 3 in efuse_rd_disable[3:0] is mapped to flash_crypt_config
        this bit is at position 19 in EFUSE_BLK0_RDATA0_REG """
        word0 = self.read_efuse(0)
        rd_disable = (word0 >> 19) & 0x1

        if rd_disable == 0:
            """ we can read the flash_crypt_config efuse value
            so go & read it (EFUSE_BLK0_RDATA5_REG[31:28]) """
            word5 = self.read_efuse(5)
            word5 = (word5 >> 28) & 0xF
            return word5
        else:
            # if read of the efuse is disabled we assume it is set correctly
            return 0xF

    def get_encrypted_download_disabled(self):
        if self.read_reg(self.EFUSE_DIS_DOWNLOAD_MANUAL_ENCRYPT_REG) & self.EFUSE_DIS_DOWNLOAD_MANUAL_ENCRYPT:
            return True
        else:
            return False

    def get_pkg_version(self):
        word3 = self.read_efuse(3)
        pkg_version = (word3 >> 9) & 0x07
        pkg_version += ((word3 >> 2) & 0x1) << 3
        return pkg_version

    def get_chip_revision(self):
        word3 = self.read_efuse(3)
        word5 = self.read_efuse(5)
        apb_ctl_date = self.read_reg(self.DR_REG_SYSCON_BASE + 0x7C)

        rev_bit0 = (word3 >> 15) & 0x1
        rev_bit1 = (word5 >> 20) & 0x1
        rev_bit2 = (apb_ctl_date >> 31) & 0x1
        if rev_bit0:
            if rev_bit1:
                if rev_bit2:
                    return 3
                else:
                    return 2
            else:
                return 1
        return 0

    def get_chip_description(self):
        pkg_version = self.get_pkg_version()
        chip_revision = self.get_chip_revision()
        rev3 = (chip_revision == 3)
        single_core = self.read_efuse(3) & (1 << 0)  # CHIP_VER DIS_APP_CPU

        chip_name = {
            0: "ESP32-S0WDQ6" if single_core else "ESP32-D0WDQ6",
            1: "ESP32-S0WD" if single_core else "ESP32-D0WD",
            2: "ESP32-D2WD",
            4: "ESP32-U4WDH",
            5: "ESP32-PICO-V3" if rev3 else "ESP32-PICO-D4",
            6: "ESP32-PICO-V3-02",
        }.get(pkg_version, "unknown ESP32")

        # ESP32-D0WD-V3, ESP32-D0WDQ6-V3
        if chip_name.startswith("ESP32-D0WD") and rev3:
            chip_name += "-V3"

        return "%s (revision %d)" % (chip_name, chip_revision)

    def get_chip_features(self):
        features = ["WiFi"]
        word3 = self.read_efuse(3)

        # names of variables in this section are lowercase
        #  versions of EFUSE names as documented in TRM and
        # ESP-IDF efuse_reg.h

        chip_ver_dis_bt = word3 & (1 << 1)
        if chip_ver_dis_bt == 0:
            features += ["BT"]

        chip_ver_dis_app_cpu = word3 & (1 << 0)
        if chip_ver_dis_app_cpu:
            features += ["Single Core"]
        else:
            features += ["Dual Core"]

        chip_cpu_freq_rated = word3 & (1 << 13)
        if chip_cpu_freq_rated:
            chip_cpu_freq_low = word3 & (1 << 12)
            if chip_cpu_freq_low:
                features += ["160MHz"]
            else:
                features += ["240MHz"]

        pkg_version = self.get_pkg_version()
        if pkg_version in [2, 4, 5, 6]:
            features += ["Embedded Flash"]

        if pkg_version == 6:
            features += ["Embedded PSRAM"]

        word4 = self.read_efuse(4)
        adc_vref = (word4 >> 8) & 0x1F
        if adc_vref:
            features += ["VRef calibration in efuse"]

        blk3_part_res = word3 >> 14 & 0x1
        if blk3_part_res:
            features += ["BLK3 partially reserved"]

        word6 = self.read_efuse(6)
        coding_scheme = word6 & 0x3
        features += ["Coding Scheme %s" % {
            0: "None",
            1: "3/4",
            2: "Repeat (UNSUPPORTED)",
            3: "Invalid"}[coding_scheme]]

        return features

    def read_efuse(self, n):
        """ Read the nth word of the ESP3x EFUSE region. """
        return self.read_reg(self.EFUSE_RD_REG_BASE + (4 * n))

    def chip_id(self):
        raise NotSupportedError(self, "chip_id")

    def read_mac(self):
        """ Read MAC from EFUSE region """
        words = [self.read_efuse(2), self.read_efuse(1)]
        bitstring = struct.pack(">II", *words)
        bitstring = bitstring[2:8]  # trim the 2 byte CRC
        try:
            return tuple(ord(b) for b in bitstring)
        except TypeError:  # Python 3, bitstring elements are already bytes
            return tuple(bitstring)

    def get_erase_size(self, offset, size):
        return size

    def override_vddsdio(self, new_voltage):
        new_voltage = new_voltage.upper()
        if new_voltage not in self.OVERRIDE_VDDSDIO_CHOICES:
            raise FatalError("The only accepted VDDSDIO overrides are '1.8V', '1.9V' and 'OFF'")
        RTC_CNTL_SDIO_CONF_REG = 0x3ff48074
        RTC_CNTL_XPD_SDIO_REG = (1 << 31)
        RTC_CNTL_DREFH_SDIO_M = (3 << 29)
        RTC_CNTL_DREFM_SDIO_M = (3 << 27)
        RTC_CNTL_DREFL_SDIO_M = (3 << 25)
        # RTC_CNTL_SDIO_TIEH = (1 << 23)  # not used here, setting TIEH=1 would set 3.3V output, not safe for esptool.py to do
        RTC_CNTL_SDIO_FORCE = (1 << 22)
        RTC_CNTL_SDIO_PD_EN = (1 << 21)

        reg_val = RTC_CNTL_SDIO_FORCE  # override efuse setting
        reg_val |= RTC_CNTL_SDIO_PD_EN
        if new_voltage != "OFF":
            reg_val |= RTC_CNTL_XPD_SDIO_REG  # enable internal LDO
        if new_voltage == "1.9V":
            reg_val |= (RTC_CNTL_DREFH_SDIO_M | RTC_CNTL_DREFM_SDIO_M | RTC_CNTL_DREFL_SDIO_M)  # boost voltage
        self.write_reg(RTC_CNTL_SDIO_CONF_REG, reg_val)
        print("VDDSDIO regulator set to %s" % new_voltage)

    def read_flash_slow(self, offset, length, progress_fn):
        BLOCK_LEN = 64  # ROM read limit per command (this limit is why it's so slow)

        data = b''
        while len(data) < length:
            block_len = min(BLOCK_LEN, length - len(data))
            r = self.check_command("read flash block", self.ESP_READ_FLASH_SLOW,
                                   struct.pack('<II', offset + len(data), block_len))
            if len(r) < block_len:
                raise FatalError("Expected %d byte block, got %d bytes. Serial errors?" % (block_len, len(r)))
            data += r[:block_len]  # command always returns 64 byte buffer, regardless of how many bytes were actually read from flash
            if progress_fn and (len(data) % 1024 == 0 or len(data) == length):
                progress_fn(len(data), length)
        return data


class ESP32S2ROM(ESP32ROM):
    CHIP_NAME = "ESP32-S2"
    IMAGE_CHIP_ID = 2

    IROM_MAP_START = 0x40080000
    IROM_MAP_END   = 0x40b80000
    DROM_MAP_START = 0x3F000000
    DROM_MAP_END   = 0x3F3F0000

    CHIP_DETECT_MAGIC_VALUE = 0x000007c6

    SPI_REG_BASE = 0x3f402000
    SPI_USR_OFFS    = 0x18
    SPI_USR1_OFFS   = 0x1c
    SPI_USR2_OFFS   = 0x20
    SPI_MOSI_DLEN_OFFS = 0x24
    SPI_MISO_DLEN_OFFS = 0x28
    SPI_W0_OFFS = 0x58

    MAC_EFUSE_REG = 0x3f41A044  # ESP32-S2 has special block for MAC efuses

    UART_CLKDIV_REG = 0x3f400014

    FLASH_ENCRYPTED_WRITE_ALIGN = 16

    # todo: use espefuse APIs to get this info
    EFUSE_BASE = 0x3f41A000
    EFUSE_RD_REG_BASE = EFUSE_BASE + 0x030  # BLOCK0 read base address

    EFUSE_PURPOSE_KEY0_REG = EFUSE_BASE + 0x34
    EFUSE_PURPOSE_KEY0_SHIFT = 24
    EFUSE_PURPOSE_KEY1_REG = EFUSE_BASE + 0x34
    EFUSE_PURPOSE_KEY1_SHIFT = 28
    EFUSE_PURPOSE_KEY2_REG = EFUSE_BASE + 0x38
    EFUSE_PURPOSE_KEY2_SHIFT = 0
    EFUSE_PURPOSE_KEY3_REG = EFUSE_BASE + 0x38
    EFUSE_PURPOSE_KEY3_SHIFT = 4
    EFUSE_PURPOSE_KEY4_REG = EFUSE_BASE + 0x38
    EFUSE_PURPOSE_KEY4_SHIFT = 8
    EFUSE_PURPOSE_KEY5_REG = EFUSE_BASE + 0x38
    EFUSE_PURPOSE_KEY5_SHIFT = 12

    EFUSE_DIS_DOWNLOAD_MANUAL_ENCRYPT_REG = EFUSE_RD_REG_BASE
    EFUSE_DIS_DOWNLOAD_MANUAL_ENCRYPT = 1 << 19

    PURPOSE_VAL_XTS_AES256_KEY_1 = 2
    PURPOSE_VAL_XTS_AES256_KEY_2 = 3
    PURPOSE_VAL_XTS_AES128_KEY = 4

    UARTDEV_BUF_NO = 0x3ffffd14  # Variable in ROM .bss which indicates the port in use
    UARTDEV_BUF_NO_USB = 2  # Value of the above variable indicating that USB is in use

    USB_RAM_BLOCK = 0x800  # Max block size USB CDC is used

    GPIO_STRAP_REG = 0x3f404038
    GPIO_STRAP_SPI_BOOT_MASK = 0x8   # Not download mode
    RTC_CNTL_OPTION1_REG = 0x3f408128
    RTC_CNTL_FORCE_DOWNLOAD_BOOT_MASK = 0x1  # Is download mode forced over USB?

    MEMORY_MAP = [[0x00000000, 0x00010000, "PADDING"],
                  [0x3F000000, 0x3FF80000, "DROM"],
                  [0x3F500000, 0x3FF80000, "EXTRAM_DATA"],
                  [0x3FF9E000, 0x3FFA0000, "RTC_DRAM"],
                  [0x3FF9E000, 0x40000000, "BYTE_ACCESSIBLE"],
                  [0x3FF9E000, 0x40072000, "MEM_INTERNAL"],
                  [0x3FFB0000, 0x40000000, "DRAM"],
                  [0x40000000, 0x4001A100, "IROM_MASK"],
                  [0x40020000, 0x40070000, "IRAM"],
                  [0x40070000, 0x40072000, "RTC_IRAM"],
                  [0x40080000, 0x40800000, "IROM"],
                  [0x50000000, 0x50002000, "RTC_DATA"]]

    def get_pkg_version(self):
        num_word = 3
        block1_addr = self.EFUSE_BASE + 0x044
        word3 = self.read_reg(block1_addr + (4 * num_word))
        pkg_version = (word3 >> 21) & 0x0F
        return pkg_version

    def get_chip_description(self):
        chip_name = {
            0: "ESP32-S2",
            1: "ESP32-S2FH16",
            2: "ESP32-S2FH32",
        }.get(self.get_pkg_version(), "unknown ESP32-S2")

        return "%s" % (chip_name)

    def get_chip_features(self):
        features = ["WiFi"]

        if self.secure_download_mode:
            features += ["Secure Download Mode Enabled"]

        pkg_version = self.get_pkg_version()

        if pkg_version in [1, 2]:
            if pkg_version == 1:
                features += ["Embedded 2MB Flash"]
            elif pkg_version == 2:
                features += ["Embedded 4MB Flash"]
            features += ["105C temp rating"]

        num_word = 4
        block2_addr = self.EFUSE_BASE + 0x05C
        word4 = self.read_reg(block2_addr + (4 * num_word))
        block2_version = (word4 >> 4) & 0x07

        if block2_version == 1:
            features += ["ADC and temperature sensor calibration in BLK2 of efuse"]
        return features

    def get_crystal_freq(self):
        # ESP32-S2 XTAL is fixed to 40MHz
        return 40

    def override_vddsdio(self, new_voltage):
        raise NotImplementedInROMError("VDD_SDIO overrides are not supported for ESP32-S2")

    def read_mac(self):
        mac0 = self.read_reg(self.MAC_EFUSE_REG)
        mac1 = self.read_reg(self.MAC_EFUSE_REG + 4)  # only bottom 16 bits are MAC
        bitstring = struct.pack(">II", mac1, mac0)[2:]
        try:
            return tuple(ord(b) for b in bitstring)
        except TypeError:  # Python 3, bitstring elements are already bytes
            return tuple(bitstring)

    def get_flash_crypt_config(self):
        return None  # doesn't exist on ESP32-S2

    def get_key_block_purpose(self, key_block):
        if key_block < 0 or key_block > 5:
            raise FatalError("Valid key block numbers must be in range 0-5")

        reg, shift = [(self.EFUSE_PURPOSE_KEY0_REG, self.EFUSE_PURPOSE_KEY0_SHIFT),
                      (self.EFUSE_PURPOSE_KEY1_REG, self.EFUSE_PURPOSE_KEY1_SHIFT),
                      (self.EFUSE_PURPOSE_KEY2_REG, self.EFUSE_PURPOSE_KEY2_SHIFT),
                      (self.EFUSE_PURPOSE_KEY3_REG, self.EFUSE_PURPOSE_KEY3_SHIFT),
                      (self.EFUSE_PURPOSE_KEY4_REG, self.EFUSE_PURPOSE_KEY4_SHIFT),
                      (self.EFUSE_PURPOSE_KEY5_REG, self.EFUSE_PURPOSE_KEY5_SHIFT)][key_block]
        return (self.read_reg(reg) >> shift) & 0xF

    def is_flash_encryption_key_valid(self):
        # Need to see either an AES-128 key or two AES-256 keys
        purposes = [self.get_key_block_purpose(b) for b in range(6)]

        if any(p == self.PURPOSE_VAL_XTS_AES128_KEY for p in purposes):
            return True

        return any(p == self.PURPOSE_VAL_XTS_AES256_KEY_1 for p in purposes) \
            and any(p == self.PURPOSE_VAL_XTS_AES256_KEY_2 for p in purposes)

    def uses_usb(self, _cache=[]):
        if self.secure_download_mode:
            return False  # can't detect native USB in secure download mode
        if not _cache:
            buf_no = self.read_reg(self.UARTDEV_BUF_NO) & 0xff
            _cache.append(buf_no == self.UARTDEV_BUF_NO_USB)
        return _cache[0]

    def _post_connect(self):
        if self.uses_usb():
            self.ESP_RAM_BLOCK = self.USB_RAM_BLOCK

    def _check_if_can_reset(self):
        """
        Check the strapping register to see if we can reset out of download mode.
        """
        if os.getenv("ESPTOOL_TESTING") is not None:
            print("ESPTOOL_TESTING is set, ignoring strapping mode check")
            # Esptool tests over USB CDC run with GPIO0 strapped low, don't complain in this case.
            return
        strap_reg = self.read_reg(self.GPIO_STRAP_REG)
        force_dl_reg = self.read_reg(self.RTC_CNTL_OPTION1_REG)
        if strap_reg & self.GPIO_STRAP_SPI_BOOT_MASK == 0 and force_dl_reg & self.RTC_CNTL_FORCE_DOWNLOAD_BOOT_MASK == 0:
            print("ERROR: {} chip was placed into download mode using GPIO0.\n"
                  "esptool.py can not exit the download mode over USB. "
                  "To run the app, reset the chip manually.\n"
                  "To suppress this error, set --after option to 'no_reset'.".format(self.get_chip_description()))
            raise SystemExit(1)

    def hard_reset(self):
        if self.uses_usb():
            self._check_if_can_reset()

        self._setRTS(True)  # EN->LOW
        if self.uses_usb():
            # Give the chip some time to come out of reset, to be able to handle further DTR/RTS transitions
            time.sleep(0.2)
            self._setRTS(False)
            time.sleep(0.2)
        else:
            self._setRTS(False)


class ESP32S3BETA2ROM(ESP32ROM):
    CHIP_NAME = "ESP32-S3(beta2)"
    IMAGE_CHIP_ID = 4

    IROM_MAP_START = 0x42000000
    IROM_MAP_END   = 0x44000000
    DROM_MAP_START = 0x3c000000
    DROM_MAP_END   = 0x3e000000

    UART_DATE_REG_ADDR = 0x60000080

    CHIP_DETECT_MAGIC_VALUE = 0xeb004136

    SPI_REG_BASE = 0x60002000
    SPI_USR_OFFS    = 0x18
    SPI_USR1_OFFS   = 0x1c
    SPI_USR2_OFFS   = 0x20
    SPI_MOSI_DLEN_OFFS = 0x24
    SPI_MISO_DLEN_OFFS = 0x28
    SPI_W0_OFFS = 0x58

    EFUSE_REG_BASE = 0x6001A030  # BLOCK0 read base address

    MAC_EFUSE_REG = 0x6001A000  # ESP32S3 has special block for MAC efuses

    UART_CLKDIV_REG = 0x60000014

    GPIO_STRAP_REG = 0x60004038

    MEMORY_MAP = [[0x00000000, 0x00010000, "PADDING"],
                  [0x3C000000, 0x3D000000, "DROM"],
                  [0x3D000000, 0x3E000000, "EXTRAM_DATA"],
                  [0x600FE000, 0x60100000, "RTC_DRAM"],
                  [0x3FC88000, 0x3FD00000, "BYTE_ACCESSIBLE"],
                  [0x3FC88000, 0x403E2000, "MEM_INTERNAL"],
                  [0x3FC88000, 0x3FD00000, "DRAM"],
                  [0x40000000, 0x4001A100, "IROM_MASK"],
                  [0x40370000, 0x403E0000, "IRAM"],
                  [0x600FE000, 0x60100000, "RTC_IRAM"],
                  [0x42000000, 0x42800000, "IROM"],
                  [0x50000000, 0x50002000, "RTC_DATA"]]

    def get_chip_description(self):
        return "ESP32-S3(beta2)"

    def get_chip_features(self):
        return ["WiFi", "BLE"]

    def get_crystal_freq(self):
        # ESP32S3 XTAL is fixed to 40MHz
        return 40

    def override_vddsdio(self, new_voltage):
        raise NotImplementedInROMError("VDD_SDIO overrides are not supported for ESP32-S3")

    def read_mac(self):
        mac0 = self.read_reg(self.MAC_EFUSE_REG)
        mac1 = self.read_reg(self.MAC_EFUSE_REG + 4)  # only bottom 16 bits are MAC
        bitstring = struct.pack(">II", mac1, mac0)[2:]
        try:
            return tuple(ord(b) for b in bitstring)
        except TypeError:  # Python 3, bitstring elements are already bytes
            return tuple(bitstring)


class ESP32C3ROM(ESP32ROM):
    CHIP_NAME = "ESP32-C3"
    IMAGE_CHIP_ID = 5

    IROM_MAP_START = 0x42000000
    IROM_MAP_END   = 0x42800000
    DROM_MAP_START = 0x3c000000
    DROM_MAP_END   = 0x3c800000

    SPI_REG_BASE = 0x60002000
    SPI_USR_OFFS    = 0x18
    SPI_USR1_OFFS   = 0x1C
    SPI_USR2_OFFS   = 0x20
    SPI_MOSI_DLEN_OFFS = 0x24
    SPI_MISO_DLEN_OFFS = 0x28
    SPI_W0_OFFS = 0x58

    BOOTLOADER_FLASH_OFFSET = 0x0

    CHIP_DETECT_MAGIC_VALUE = 0x6921506f

    UART_DATE_REG_ADDR = 0x60000000 + 0x7c

    EFUSE_BASE = 0x60008800
    MAC_EFUSE_REG  = EFUSE_BASE + 0x044

    EFUSE_RD_REG_BASE = EFUSE_BASE + 0x030  # BLOCK0 read base address

    EFUSE_PURPOSE_KEY0_REG = EFUSE_BASE + 0x34
    EFUSE_PURPOSE_KEY0_SHIFT = 24
    EFUSE_PURPOSE_KEY1_REG = EFUSE_BASE + 0x34
    EFUSE_PURPOSE_KEY1_SHIFT = 28
    EFUSE_PURPOSE_KEY2_REG = EFUSE_BASE + 0x38
    EFUSE_PURPOSE_KEY2_SHIFT = 0
    EFUSE_PURPOSE_KEY3_REG = EFUSE_BASE + 0x38
    EFUSE_PURPOSE_KEY3_SHIFT = 4
    EFUSE_PURPOSE_KEY4_REG = EFUSE_BASE + 0x38
    EFUSE_PURPOSE_KEY4_SHIFT = 8
    EFUSE_PURPOSE_KEY5_REG = EFUSE_BASE + 0x38
    EFUSE_PURPOSE_KEY5_SHIFT = 12

    EFUSE_DIS_DOWNLOAD_MANUAL_ENCRYPT_REG = EFUSE_RD_REG_BASE
    EFUSE_DIS_DOWNLOAD_MANUAL_ENCRYPT = 1 << 20

    PURPOSE_VAL_XTS_AES128_KEY = 4

    GPIO_STRAP_REG = 0x3f404038

    FLASH_ENCRYPTED_WRITE_ALIGN = 16

    MEMORY_MAP = [[0x00000000, 0x00010000, "PADDING"],
                  [0x3C000000, 0x3C800000, "DROM"],
                  [0x3FC80000, 0x3FCE0000, "DRAM"],
                  [0x3FC88000, 0x3FD00000, "BYTE_ACCESSIBLE"],
                  [0x3FF00000, 0x3FF20000, "DROM_MASK"],
                  [0x40000000, 0x40060000, "IROM_MASK"],
                  [0x42000000, 0x42800000, "IROM"],
                  [0x4037C000, 0x403E0000, "IRAM"],
                  [0x50000000, 0x50002000, "RTC_IRAM"],
                  [0x50000000, 0x50002000, "RTC_DRAM"],
                  [0x600FE000, 0x60100000, "MEM_INTERNAL2"]]

    def get_pkg_version(self):
        num_word = 3
        block1_addr = self.EFUSE_BASE + 0x044
        word3 = self.read_reg(block1_addr + (4 * num_word))
        pkg_version = (word3 >> 21) & 0x0F
        return pkg_version

    def get_chip_revision(self):
        # reads WAFER_VERSION field from EFUSE_RD_MAC_SPI_SYS_3_REG
        block1_addr = self.EFUSE_BASE + 0x044
        num_word = 3
        pos = 18
        return (self.read_reg(block1_addr + (4 * num_word)) & (0x7 << pos)) >> pos

    def get_chip_description(self):
        chip_name = {
            0: "ESP32-C3",
        }.get(self.get_pkg_version(), "unknown ESP32-C3")
        chip_revision = self.get_chip_revision()

        return "%s (revision %d)" % (chip_name, chip_revision)

    def get_chip_features(self):
        return ["Wi-Fi"]

    def get_crystal_freq(self):
        # ESP32C3 XTAL is fixed to 40MHz
        return 40

    def override_vddsdio(self, new_voltage):
        raise NotImplementedInROMError("VDD_SDIO overrides are not supported for ESP32-C3")

    def read_mac(self):
        mac0 = self.read_reg(self.MAC_EFUSE_REG)
        mac1 = self.read_reg(self.MAC_EFUSE_REG + 4)  # only bottom 16 bits are MAC
        bitstring = struct.pack(">II", mac1, mac0)[2:]
        try:
            return tuple(ord(b) for b in bitstring)
        except TypeError:  # Python 3, bitstring elements are already bytes
            return tuple(bitstring)

    def get_flash_crypt_config(self):
        return None  # doesn't exist on ESP32-C3

    def get_key_block_purpose(self, key_block):
        if key_block < 0 or key_block > 5:
            raise FatalError("Valid key block numbers must be in range 0-5")

        reg, shift = [(self.EFUSE_PURPOSE_KEY0_REG, self.EFUSE_PURPOSE_KEY0_SHIFT),
                      (self.EFUSE_PURPOSE_KEY1_REG, self.EFUSE_PURPOSE_KEY1_SHIFT),
                      (self.EFUSE_PURPOSE_KEY2_REG, self.EFUSE_PURPOSE_KEY2_SHIFT),
                      (self.EFUSE_PURPOSE_KEY3_REG, self.EFUSE_PURPOSE_KEY3_SHIFT),
                      (self.EFUSE_PURPOSE_KEY4_REG, self.EFUSE_PURPOSE_KEY4_SHIFT),
                      (self.EFUSE_PURPOSE_KEY5_REG, self.EFUSE_PURPOSE_KEY5_SHIFT)][key_block]
        return (self.read_reg(reg) >> shift) & 0xF

    def is_flash_encryption_key_valid(self):
        # Need to see an AES-128 key
        purposes = [self.get_key_block_purpose(b) for b in range(6)]

        return any(p == self.PURPOSE_VAL_XTS_AES128_KEY for p in purposes)


class ESP32StubLoader(ESP32ROM):
    """ Access class for ESP32 stub loader, runs on top of ROM.
    """
    FLASH_WRITE_SIZE = 0x4000  # matches MAX_WRITE_BLOCK in stub_loader.c
    STATUS_BYTES_LENGTH = 2  # same as ESP8266, different to ESP32 ROM
    IS_STUB = True

    def __init__(self, rom_loader):
        self.secure_download_mode = rom_loader.secure_download_mode
        self._port = rom_loader._port
        self._trace_enabled = rom_loader._trace_enabled
        self.flush_input()  # resets _slip_reader


ESP32ROM.STUB_CLASS = ESP32StubLoader


class ESP32S2StubLoader(ESP32S2ROM):
    """ Access class for ESP32-S2 stub loader, runs on top of ROM.

    (Basically the same as ESP32StubLoader, but different base class.
    Can possibly be made into a mixin.)
    """
    FLASH_WRITE_SIZE = 0x4000  # matches MAX_WRITE_BLOCK in stub_loader.c
    STATUS_BYTES_LENGTH = 2  # same as ESP8266, different to ESP32 ROM
    IS_STUB = True

    def __init__(self, rom_loader):
        self.secure_download_mode = rom_loader.secure_download_mode
        self._port = rom_loader._port
        self._trace_enabled = rom_loader._trace_enabled
        self.flush_input()  # resets _slip_reader

        if rom_loader.uses_usb():
            self.ESP_RAM_BLOCK = self.USB_RAM_BLOCK
            self.FLASH_WRITE_SIZE = self.USB_RAM_BLOCK


ESP32S2ROM.STUB_CLASS = ESP32S2StubLoader


class ESP32S3BETA2StubLoader(ESP32S3BETA2ROM):
    """ Access class for ESP32S3 stub loader, runs on top of ROM.

    (Basically the same as ESP32StubLoader, but different base class.
    Can possibly be made into a mixin.)
    """
    FLASH_WRITE_SIZE = 0x4000  # matches MAX_WRITE_BLOCK in stub_loader.c
    STATUS_BYTES_LENGTH = 2  # same as ESP8266, different to ESP32 ROM
    IS_STUB = True

    def __init__(self, rom_loader):
        self.secure_download_mode = rom_loader.secure_download_mode
        self._port = rom_loader._port
        self._trace_enabled = rom_loader._trace_enabled
        self.flush_input()  # resets _slip_reader


ESP32S3BETA2ROM.STUB_CLASS = ESP32S3BETA2StubLoader


class ESP32C3StubLoader(ESP32C3ROM):
    """ Access class for ESP32C3 stub loader, runs on top of ROM.

    (Basically the same as ESP32StubLoader, but different base class.
    Can possibly be made into a mixin.)
    """
    FLASH_WRITE_SIZE = 0x4000  # matches MAX_WRITE_BLOCK in stub_loader.c
    STATUS_BYTES_LENGTH = 2  # same as ESP8266, different to ESP32 ROM
    IS_STUB = True

    def __init__(self, rom_loader):
        self.secure_download_mode = rom_loader.secure_download_mode
        self._port = rom_loader._port
        self._trace_enabled = rom_loader._trace_enabled
        self.flush_input()  # resets _slip_reader


ESP32C3ROM.STUB_CLASS = ESP32C3StubLoader


class ESPBOOTLOADER(object):
    """ These are constants related to software ESP8266 bootloader, working with 'v2' image files """

    # First byte of the "v2" application image
    IMAGE_V2_MAGIC = 0xea

    # First 'segment' value in a "v2" application image, appears to be a constant version value?
    IMAGE_V2_SEGMENT = 4


def LoadFirmwareImage(chip, filename):
    """ Load a firmware image. Can be for any supported SoC.

        ESP8266 images will be examined to determine if they are original ROM firmware images (ESP8266ROMFirmwareImage)
        or "v2" OTA bootloader images.

        Returns a BaseFirmwareImage subclass, either ESP8266ROMFirmwareImage (v1) or ESP8266V2FirmwareImage (v2).
    """
    chip = chip.lower().replace("-", "")
    with open(filename, 'rb') as f:
        if chip == 'esp32':
            return ESP32FirmwareImage(f)
        elif chip == "esp32s2":
            return ESP32S2FirmwareImage(f)
        elif chip == "esp32s3beta2":
            return ESP32S3BETA2FirmwareImage(f)
        elif chip == 'esp32c3':
            return ESP32C3FirmwareImage(f)
        else:  # Otherwise, ESP8266 so look at magic to determine the image type
            magic = ord(f.read(1))
            f.seek(0)
            if magic == ESPLoader.ESP_IMAGE_MAGIC:
                return ESP8266ROMFirmwareImage(f)
            elif magic == ESPBOOTLOADER.IMAGE_V2_MAGIC:
                return ESP8266V2FirmwareImage(f)
            else:
                raise FatalError("Invalid image magic number: %d" % magic)


class ImageSegment(object):
    """ Wrapper class for a segment in an ESP image
    (very similar to a section in an ELFImage also) """
    def __init__(self, addr, data, file_offs=None):
        self.addr = addr
        self.data = data
        self.file_offs = file_offs
        self.include_in_checksum = True
        if self.addr != 0:
            self.pad_to_alignment(4)  # pad all "real" ImageSegments 4 byte aligned length

    def copy_with_new_addr(self, new_addr):
        """ Return a new ImageSegment with same data, but mapped at
        a new address. """
        return ImageSegment(new_addr, self.data, 0)

    def split_image(self, split_len):
        """ Return a new ImageSegment which splits "split_len" bytes
        from the beginning of the data. Remaining bytes are kept in
        this segment object (and the start address is adjusted to match.) """
        result = copy.copy(self)
        result.data = self.data[:split_len]
        self.data = self.data[split_len:]
        self.addr += split_len
        self.file_offs = None
        result.file_offs = None
        return result

    def __repr__(self):
        r = "len 0x%05x load 0x%08x" % (len(self.data), self.addr)
        if self.file_offs is not None:
            r += " file_offs 0x%08x" % (self.file_offs)
        return r

    def get_memory_type(self, image):
        """
        Return a list describing the memory type(s) that is covered by this
        segment's start address.
        """
        return [map_range[2] for map_range in image.ROM_LOADER.MEMORY_MAP if map_range[0] <= self.addr < map_range[1]]

    def pad_to_alignment(self, alignment):
        self.data = pad_to(self.data, alignment, b'\x00')


class ELFSection(ImageSegment):
    """ Wrapper class for a section in an ELF image, has a section
    name as well as the common properties of an ImageSegment. """
    def __init__(self, name, addr, data):
        super(ELFSection, self).__init__(addr, data)
        self.name = name.decode("utf-8")

    def __repr__(self):
        return "%s %s" % (self.name, super(ELFSection, self).__repr__())


class BaseFirmwareImage(object):
    SEG_HEADER_LEN = 8
    SHA256_DIGEST_LEN = 32

    """ Base class with common firmware image functions """
    def __init__(self):
        self.segments = []
        self.entrypoint = 0
        self.elf_sha256 = None
        self.elf_sha256_offset = 0

    def load_common_header(self, load_file, expected_magic):
        (magic, segments, self.flash_mode, self.flash_size_freq, self.entrypoint) = struct.unpack('<BBBBI', load_file.read(8))

        if magic != expected_magic:
            raise FatalError('Invalid firmware image magic=0x%x' % (magic))
        return segments

    def verify(self):
        if len(self.segments) > 16:
            raise FatalError('Invalid segment count %d (max 16). Usually this indicates a linker script problem.' % len(self.segments))

    def load_segment(self, f, is_irom_segment=False):
        """ Load the next segment from the image file """
        file_offs = f.tell()
        (offset, size) = struct.unpack('<II', f.read(8))
        self.warn_if_unusual_segment(offset, size, is_irom_segment)
        segment_data = f.read(size)
        if len(segment_data) < size:
            raise FatalError('End of file reading segment 0x%x, length %d (actual length %d)' % (offset, size, len(segment_data)))
        segment = ImageSegment(offset, segment_data, file_offs)
        self.segments.append(segment)
        return segment

    def warn_if_unusual_segment(self, offset, size, is_irom_segment):
        if not is_irom_segment:
            if offset > 0x40200000 or offset < 0x3ffe0000 or size > 65536:
                print('WARNING: Suspicious segment 0x%x, length %d' % (offset, size))

    def maybe_patch_segment_data(self, f, segment_data):
        """If SHA256 digest of the ELF file needs to be inserted into this segment, do so. Returns segment data."""
        segment_len = len(segment_data)
        file_pos = f.tell()  # file_pos is position in the .bin file
        if self.elf_sha256_offset >= file_pos and self.elf_sha256_offset < file_pos + segment_len:
            # SHA256 digest needs to be patched into this binary segment,
            # calculate offset of the digest inside the binary segment.
            patch_offset = self.elf_sha256_offset - file_pos
            # Sanity checks
            if patch_offset < self.SEG_HEADER_LEN or patch_offset + self.SHA256_DIGEST_LEN > segment_len:
                raise FatalError('Cannot place SHA256 digest on segment boundary'
                                 '(elf_sha256_offset=%d, file_pos=%d, segment_size=%d)' %
                                 (self.elf_sha256_offset, file_pos, segment_len))
            # offset relative to the data part
            patch_offset -= self.SEG_HEADER_LEN
            if segment_data[patch_offset:patch_offset + self.SHA256_DIGEST_LEN] != b'\x00' * self.SHA256_DIGEST_LEN:
                raise FatalError('Contents of segment at SHA256 digest offset 0x%x are not all zero. Refusing to overwrite.' %
                                 self.elf_sha256_offset)
            assert(len(self.elf_sha256) == self.SHA256_DIGEST_LEN)
            segment_data = segment_data[0:patch_offset] + self.elf_sha256 + \
                segment_data[patch_offset + self.SHA256_DIGEST_LEN:]
        return segment_data

    def save_segment(self, f, segment, checksum=None):
        """ Save the next segment to the image file, return next checksum value if provided """
        segment_data = self.maybe_patch_segment_data(f, segment.data)
        f.write(struct.pack('<II', segment.addr, len(segment_data)))
        f.write(segment_data)
        if checksum is not None:
            return ESPLoader.checksum(segment_data, checksum)

    def read_checksum(self, f):
        """ Return ESPLoader checksum from end of just-read image """
        # Skip the padding. The checksum is stored in the last byte so that the
        # file is a multiple of 16 bytes.
        align_file_position(f, 16)
        return ord(f.read(1))

    def calculate_checksum(self):
        """ Calculate checksum of loaded image, based on segments in
        segment array.
        """
        checksum = ESPLoader.ESP_CHECKSUM_MAGIC
        for seg in self.segments:
            if seg.include_in_checksum:
                checksum = ESPLoader.checksum(seg.data, checksum)
        return checksum

    def append_checksum(self, f, checksum):
        """ Append ESPLoader checksum to the just-written image """
        align_file_position(f, 16)
        f.write(struct.pack(b'B', checksum))

    def write_common_header(self, f, segments):
        f.write(struct.pack('<BBBBI', ESPLoader.ESP_IMAGE_MAGIC, len(segments),
                            self.flash_mode, self.flash_size_freq, self.entrypoint))

    def is_irom_addr(self, addr):
        """ Returns True if an address starts in the irom region.
        Valid for ESP8266 only.
        """
        return ESP8266ROM.IROM_MAP_START <= addr < ESP8266ROM.IROM_MAP_END

    def get_irom_segment(self):
        irom_segments = [s for s in self.segments if self.is_irom_addr(s.addr)]
        if len(irom_segments) > 0:
            if len(irom_segments) != 1:
                raise FatalError('Found %d segments that could be irom0. Bad ELF file?' % len(irom_segments))
            return irom_segments[0]
        return None

    def get_non_irom_segments(self):
        irom_segment = self.get_irom_segment()
        return [s for s in self.segments if s != irom_segment]

    def merge_adjacent_segments(self):
        if not self.segments:
            return  # nothing to merge

        segments = []
        # The easiest way to merge the sections is the browse them backward.
        for i in range(len(self.segments) - 1, 0, -1):
            # elem is the previous section, the one `next_elem` may need to be
            # merged in
            elem = self.segments[i - 1]
            next_elem = self.segments[i]
            if all((elem.get_memory_type(self) == next_elem.get_memory_type(self),
                    elem.include_in_checksum == next_elem.include_in_checksum,
                    next_elem.addr == elem.addr + len(elem.data))):
                # Merge any segment that ends where the next one starts, without spanning memory types
                #
                # (don't 'pad' any gaps here as they may be excluded from the image due to 'noinit'
                # or other reasons.)
                elem.data += next_elem.data
            else:
                # The section next_elem cannot be merged into the previous one,
                # which means it needs to be part of the final segments.
                # As we are browsing the list backward, the elements need to be
                # inserted at the beginning of the final list.
                segments.insert(0, next_elem)

        # The first segment will always be here as it cannot be merged into any
        # "previous" section.
        segments.insert(0, self.segments[0])

        # note: we could sort segments here as well, but the ordering of segments is sometimes
        # important for other reasons (like embedded ELF SHA-256), so we assume that the linker
        # script will have produced any adjacent sections in linear order in the ELF, anyhow.
        self.segments = segments


class ESP8266ROMFirmwareImage(BaseFirmwareImage):
    """ 'Version 1' firmware image, segments loaded directly by the ROM bootloader. """

    ROM_LOADER = ESP8266ROM

    def __init__(self, load_file=None):
        super(ESP8266ROMFirmwareImage, self).__init__()
        self.flash_mode = 0
        self.flash_size_freq = 0
        self.version = 1

        if load_file is not None:
            segments = self.load_common_header(load_file, ESPLoader.ESP_IMAGE_MAGIC)

            for _ in range(segments):
                self.load_segment(load_file)
            self.checksum = self.read_checksum(load_file)

            self.verify()

    def default_output_name(self, input_file):
        """ Derive a default output name from the ELF name. """
        return input_file + '-'

    def save(self, basename):
        """ Save a set of V1 images for flashing. Parameter is a base filename. """
        # IROM data goes in its own plain binary file
        irom_segment = self.get_irom_segment()
        if irom_segment is not None:
            with open("%s0x%05x.bin" % (basename, irom_segment.addr - ESP8266ROM.IROM_MAP_START), "wb") as f:
                f.write(irom_segment.data)

        # everything but IROM goes at 0x00000 in an image file
        normal_segments = self.get_non_irom_segments()
        with open("%s0x00000.bin" % basename, 'wb') as f:
            self.write_common_header(f, normal_segments)
            checksum = ESPLoader.ESP_CHECKSUM_MAGIC
            for segment in normal_segments:
                checksum = self.save_segment(f, segment, checksum)
            self.append_checksum(f, checksum)


ESP8266ROM.BOOTLOADER_IMAGE = ESP8266ROMFirmwareImage


class ESP8266V2FirmwareImage(BaseFirmwareImage):
    """ 'Version 2' firmware image, segments loaded by software bootloader stub
        (ie Espressif bootloader or rboot)
    """

    ROM_LOADER = ESP8266ROM

    def __init__(self, load_file=None):
        super(ESP8266V2FirmwareImage, self).__init__()
        self.version = 2
        if load_file is not None:
            segments = self.load_common_header(load_file, ESPBOOTLOADER.IMAGE_V2_MAGIC)
            if segments != ESPBOOTLOADER.IMAGE_V2_SEGMENT:
                # segment count is not really segment count here, but we expect to see '4'
                print('Warning: V2 header has unexpected "segment" count %d (usually 4)' % segments)

            # irom segment comes before the second header
            #
            # the file is saved in the image with a zero load address
            # in the header, so we need to calculate a load address
            irom_segment = self.load_segment(load_file, True)
            irom_segment.addr = 0  # for actual mapped addr, add ESP8266ROM.IROM_MAP_START + flashing_addr + 8
            irom_segment.include_in_checksum = False

            first_flash_mode = self.flash_mode
            first_flash_size_freq = self.flash_size_freq
            first_entrypoint = self.entrypoint
            # load the second header

            segments = self.load_common_header(load_file, ESPLoader.ESP_IMAGE_MAGIC)

            if first_flash_mode != self.flash_mode:
                print('WARNING: Flash mode value in first header (0x%02x) disagrees with second (0x%02x). Using second value.'
                      % (first_flash_mode, self.flash_mode))
            if first_flash_size_freq != self.flash_size_freq:
                print('WARNING: Flash size/freq value in first header (0x%02x) disagrees with second (0x%02x). Using second value.'
                      % (first_flash_size_freq, self.flash_size_freq))
            if first_entrypoint != self.entrypoint:
                print('WARNING: Entrypoint address in first header (0x%08x) disagrees with second header (0x%08x). Using second value.'
                      % (first_entrypoint, self.entrypoint))

            # load all the usual segments
            for _ in range(segments):
                self.load_segment(load_file)
            self.checksum = self.read_checksum(load_file)

            self.verify()

    def default_output_name(self, input_file):
        """ Derive a default output name from the ELF name. """
        irom_segment = self.get_irom_segment()
        if irom_segment is not None:
            irom_offs = irom_segment.addr - ESP8266ROM.IROM_MAP_START
        else:
            irom_offs = 0
        return "%s-0x%05x.bin" % (os.path.splitext(input_file)[0],
                                  irom_offs & ~(ESPLoader.FLASH_SECTOR_SIZE - 1))

    def save(self, filename):
        with open(filename, 'wb') as f:
            # Save first header for irom0 segment
            f.write(struct.pack(b'<BBBBI', ESPBOOTLOADER.IMAGE_V2_MAGIC, ESPBOOTLOADER.IMAGE_V2_SEGMENT,
                                self.flash_mode, self.flash_size_freq, self.entrypoint))

            irom_segment = self.get_irom_segment()
            if irom_segment is not None:
                # save irom0 segment, make sure it has load addr 0 in the file
                irom_segment = irom_segment.copy_with_new_addr(0)
                irom_segment.pad_to_alignment(16)  # irom_segment must end on a 16 byte boundary
                self.save_segment(f, irom_segment)

            # second header, matches V1 header and contains loadable segments
            normal_segments = self.get_non_irom_segments()
            self.write_common_header(f, normal_segments)
            checksum = ESPLoader.ESP_CHECKSUM_MAGIC
            for segment in normal_segments:
                checksum = self.save_segment(f, segment, checksum)
            self.append_checksum(f, checksum)

        # calculate a crc32 of entire file and append
        # (algorithm used by recent 8266 SDK bootloaders)
        with open(filename, 'rb') as f:
            crc = esp8266_crc32(f.read())
        with open(filename, 'ab') as f:
            f.write(struct.pack(b'<I', crc))


# Backwards compatibility for previous API, remove in esptool.py V3
ESPFirmwareImage = ESP8266ROMFirmwareImage
OTAFirmwareImage = ESP8266V2FirmwareImage


def esp8266_crc32(data):
    """
    CRC32 algorithm used by 8266 SDK bootloader (and gen_appbin.py).
    """
    crc = binascii.crc32(data, 0) & 0xFFFFFFFF
    if crc & 0x80000000:
        return crc ^ 0xFFFFFFFF
    else:
        return crc + 1


class ESP32FirmwareImage(BaseFirmwareImage):
    """ ESP32 firmware image is very similar to V1 ESP8266 image,
    except with an additional 16 byte reserved header at top of image,
    and because of new flash mapping capabilities the flash-mapped regions
    can be placed in the normal image (just @ 64kB padded offsets).
    """

    ROM_LOADER = ESP32ROM

    # ROM bootloader will read the wp_pin field if SPI flash
    # pins are remapped via flash. IDF actually enables QIO only
    # from software bootloader, so this can be ignored. But needs
    # to be set to this value so ROM bootloader will skip it.
    WP_PIN_DISABLED = 0xEE

    EXTENDED_HEADER_STRUCT_FMT = "<BBBBHB" + ("B" * 8) + "B"

    IROM_ALIGN = 65536

    def __init__(self, load_file=None):
        super(ESP32FirmwareImage, self).__init__()
        self.secure_pad = None
        self.flash_mode = 0
        self.flash_size_freq = 0
        self.version = 1
        self.wp_pin = self.WP_PIN_DISABLED
        # SPI pin drive levels
        self.clk_drv = 0
        self.q_drv = 0
        self.d_drv = 0
        self.cs_drv = 0
        self.hd_drv = 0
        self.wp_drv = 0
        self.min_rev = 0

        self.append_digest = True

        if load_file is not None:
            start = load_file.tell()

            segments = self.load_common_header(load_file, ESPLoader.ESP_IMAGE_MAGIC)
            self.load_extended_header(load_file)

            for _ in range(segments):
                self.load_segment(load_file)
            self.checksum = self.read_checksum(load_file)

            if self.append_digest:
                end = load_file.tell()
                self.stored_digest = load_file.read(32)
                load_file.seek(start)
                calc_digest = hashlib.sha256()
                calc_digest.update(load_file.read(end - start))
                self.calc_digest = calc_digest.digest()  # TODO: decide what to do here?

            self.verify()

    def is_flash_addr(self, addr):
        return (self.ROM_LOADER.IROM_MAP_START <= addr < self.ROM_LOADER.IROM_MAP_END) \
            or (self.ROM_LOADER.DROM_MAP_START <= addr < self.ROM_LOADER.DROM_MAP_END)

    def default_output_name(self, input_file):
        """ Derive a default output name from the ELF name. """
        return "%s.bin" % (os.path.splitext(input_file)[0])

    def warn_if_unusual_segment(self, offset, size, is_irom_segment):
        pass  # TODO: add warnings for ESP32 segment offset/size combinations that are wrong

    def save(self, filename):
        total_segments = 0
        with io.BytesIO() as f:  # write file to memory first
            self.write_common_header(f, self.segments)

            # first 4 bytes of header are read by ROM bootloader for SPI
            # config, but currently unused
            self.save_extended_header(f)

            checksum = ESPLoader.ESP_CHECKSUM_MAGIC

            # split segments into flash-mapped vs ram-loaded, and take copies so we can mutate them
            flash_segments = [copy.deepcopy(s) for s in sorted(self.segments, key=lambda s:s.addr) if self.is_flash_addr(s.addr)]
            ram_segments = [copy.deepcopy(s) for s in sorted(self.segments, key=lambda s:s.addr) if not self.is_flash_addr(s.addr)]

            # check for multiple ELF sections that are mapped in the same flash mapping region.
            # this is usually a sign of a broken linker script, but if you have a legitimate
            # use case then let us know
            if len(flash_segments) > 0:
                last_addr = flash_segments[0].addr
                for segment in flash_segments[1:]:
                    if segment.addr // self.IROM_ALIGN == last_addr // self.IROM_ALIGN:
                        raise FatalError(("Segment loaded at 0x%08x lands in same 64KB flash mapping as segment loaded at 0x%08x. "
                                          "Can't generate binary. Suggest changing linker script or ELF to merge sections.") %
                                         (segment.addr, last_addr))
                    last_addr = segment.addr

            def get_alignment_data_needed(segment):
                # Actual alignment (in data bytes) required for a segment header: positioned so that
                # after we write the next 8 byte header, file_offs % IROM_ALIGN == segment.addr % IROM_ALIGN
                #
                # (this is because the segment's vaddr may not be IROM_ALIGNed, more likely is aligned
                # IROM_ALIGN+0x18 to account for the binary file header
                align_past = (segment.addr % self.IROM_ALIGN) - self.SEG_HEADER_LEN
                pad_len = (self.IROM_ALIGN - (f.tell() % self.IROM_ALIGN)) + align_past
                if pad_len == 0 or pad_len == self.IROM_ALIGN:
                    return 0  # already aligned

                # subtract SEG_HEADER_LEN a second time, as the padding block has a header as well
                pad_len -= self.SEG_HEADER_LEN
                if pad_len < 0:
                    pad_len += self.IROM_ALIGN
                return pad_len

            # try to fit each flash segment on a 64kB aligned boundary
            # by padding with parts of the non-flash segments...
            while len(flash_segments) > 0:
                segment = flash_segments[0]
                pad_len = get_alignment_data_needed(segment)
                if pad_len > 0:  # need to pad
                    if len(ram_segments) > 0 and pad_len > self.SEG_HEADER_LEN:
                        pad_segment = ram_segments[0].split_image(pad_len)
                        if len(ram_segments[0].data) == 0:
                            ram_segments.pop(0)
                    else:
                        pad_segment = ImageSegment(0, b'\x00' * pad_len, f.tell())
                    checksum = self.save_segment(f, pad_segment, checksum)
                    total_segments += 1
                else:
                    # write the flash segment
                    assert (f.tell() + 8) % self.IROM_ALIGN == segment.addr % self.IROM_ALIGN
                    checksum = self.save_flash_segment(f, segment, checksum)
                    flash_segments.pop(0)
                    total_segments += 1

            # flash segments all written, so write any remaining RAM segments
            for segment in ram_segments:
                checksum = self.save_segment(f, segment, checksum)
                total_segments += 1

            if self.secure_pad:
                # pad the image so that after signing it will end on a a 64KB boundary.
                # This ensures all mapped flash content will be verified.
                if not self.append_digest:
                    raise FatalError("secure_pad only applies if a SHA-256 digest is also appended to the image")
                align_past = (f.tell() + self.SEG_HEADER_LEN) % self.IROM_ALIGN
                # 16 byte aligned checksum (force the alignment to simplify calculations)
                checksum_space = 16
                if self.secure_pad == '1':
                    # after checksum: SHA-256 digest + (to be added by signing process) version, signature + 12 trailing bytes due to alignment
                    space_after_checksum = 32 + 4 + 64 + 12
                elif self.secure_pad == '2':  # Secure Boot V2
                    # after checksum: SHA-256 digest + signature sector, but we place signature sector after the 64KB boundary
                    space_after_checksum = 32
                pad_len = (self.IROM_ALIGN - align_past - checksum_space - space_after_checksum) % self.IROM_ALIGN
                pad_segment = ImageSegment(0, b'\x00' * pad_len, f.tell())

                checksum = self.save_segment(f, pad_segment, checksum)
                total_segments += 1

            # done writing segments
            self.append_checksum(f, checksum)
            image_length = f.tell()

            if self.secure_pad:
                assert ((image_length + space_after_checksum) % self.IROM_ALIGN) == 0

            # kinda hacky: go back to the initial header and write the new segment count
            # that includes padding segments. This header is not checksummed
            f.seek(1)
            try:
                f.write(chr(total_segments))
            except TypeError:  # Python 3
                f.write(bytes([total_segments]))

            if self.append_digest:
                # calculate the SHA256 of the whole file and append it
                f.seek(0)
                digest = hashlib.sha256()
                digest.update(f.read(image_length))
                f.write(digest.digest())

            with open(filename, 'wb') as real_file:
                real_file.write(f.getvalue())

    def save_flash_segment(self, f, segment, checksum=None):
        """ Save the next segment to the image file, return next checksum value if provided """
        segment_end_pos = f.tell() + len(segment.data) + self.SEG_HEADER_LEN
        segment_len_remainder = segment_end_pos % self.IROM_ALIGN
        if segment_len_remainder < 0x24:
            # Work around a bug in ESP-IDF 2nd stage bootloader, that it didn't map the
            # last MMU page, if an IROM/DROM segment was < 0x24 bytes over the page boundary.
            segment.data += b'\x00' * (0x24 - segment_len_remainder)
        return self.save_segment(f, segment, checksum)

    def load_extended_header(self, load_file):
        def split_byte(n):
            return (n & 0x0F, (n >> 4) & 0x0F)

        fields = list(struct.unpack(self.EXTENDED_HEADER_STRUCT_FMT, load_file.read(16)))

        self.wp_pin = fields[0]

        # SPI pin drive stengths are two per byte
        self.clk_drv, self.q_drv = split_byte(fields[1])
        self.d_drv, self.cs_drv = split_byte(fields[2])
        self.hd_drv, self.wp_drv = split_byte(fields[3])

        chip_id = fields[4]
        if chip_id != self.ROM_LOADER.IMAGE_CHIP_ID:
            print(("Unexpected chip id in image. Expected %d but value was %d. "
                   "Is this image for a different chip model?") % (self.ROM_LOADER.IMAGE_CHIP_ID, chip_id))

        # reserved fields in the middle should all be zero
        if any(f for f in fields[6:-1] if f != 0):
            print("Warning: some reserved header fields have non-zero values. This image may be from a newer esptool.py?")

        append_digest = fields[-1]  # last byte is append_digest
        if append_digest in [0, 1]:
            self.append_digest = (append_digest == 1)
        else:
            raise RuntimeError("Invalid value for append_digest field (0x%02x). Should be 0 or 1.", append_digest)

    def save_extended_header(self, save_file):
        def join_byte(ln, hn):
            return (ln & 0x0F) + ((hn & 0x0F) << 4)

        append_digest = 1 if self.append_digest else 0

        fields = [self.wp_pin,
                  join_byte(self.clk_drv, self.q_drv),
                  join_byte(self.d_drv, self.cs_drv),
                  join_byte(self.hd_drv, self.wp_drv),
                  self.ROM_LOADER.IMAGE_CHIP_ID,
                  self.min_rev]
        fields += [0] * 8  # padding
        fields += [append_digest]

        packed = struct.pack(self.EXTENDED_HEADER_STRUCT_FMT, *fields)
        save_file.write(packed)


ESP32ROM.BOOTLOADER_IMAGE = ESP32FirmwareImage


class ESP32S2FirmwareImage(ESP32FirmwareImage):
    """ ESP32S2 Firmware Image almost exactly the same as ESP32FirmwareImage """
    ROM_LOADER = ESP32S2ROM


ESP32S2ROM.BOOTLOADER_IMAGE = ESP32S2FirmwareImage


class ESP32S3BETA2FirmwareImage(ESP32FirmwareImage):
    """ ESP32S3 Firmware Image almost exactly the same as ESP32FirmwareImage """
    ROM_LOADER = ESP32S3BETA2ROM


ESP32S3BETA2ROM.BOOTLOADER_IMAGE = ESP32S3BETA2FirmwareImage


class ESP32C3FirmwareImage(ESP32FirmwareImage):
    """ ESP32C3 Firmware Image almost exactly the same as ESP32FirmwareImage """
    ROM_LOADER = ESP32C3ROM


ESP32C3ROM.BOOTLOADER_IMAGE = ESP32C3FirmwareImage


class ELFFile(object):
    SEC_TYPE_PROGBITS = 0x01
    SEC_TYPE_STRTAB = 0x03

    LEN_SEC_HEADER = 0x28

    SEG_TYPE_LOAD = 0x01
    LEN_SEG_HEADER = 0x20

    def __init__(self, name):
        # Load sections from the ELF file
        self.name = name
        with open(self.name, 'rb') as f:
            self._read_elf_file(f)

    def get_section(self, section_name):
        for s in self.sections:
            if s.name == section_name:
                return s
        raise ValueError("No section %s in ELF file" % section_name)

    def _read_elf_file(self, f):
        # read the ELF file header
        LEN_FILE_HEADER = 0x34
        try:
            (ident, _type, machine, _version,
             self.entrypoint, _phoff, shoff, _flags,
             _ehsize, _phentsize, _phnum, shentsize,
             shnum, shstrndx) = struct.unpack("<16sHHLLLLLHHHHHH", f.read(LEN_FILE_HEADER))
        except struct.error as e:
            raise FatalError("Failed to read a valid ELF header from %s: %s" % (self.name, e))

        if byte(ident, 0) != 0x7f or ident[1:4] != b'ELF':
            raise FatalError("%s has invalid ELF magic header" % self.name)
        if machine not in [0x5e, 0xf3]:
            raise FatalError("%s does not appear to be an Xtensa or an RISCV ELF file. e_machine=%04x" % (self.name, machine))
        if shentsize != self.LEN_SEC_HEADER:
            raise FatalError("%s has unexpected section header entry size 0x%x (not 0x%x)" % (self.name, shentsize, self.LEN_SEC_HEADER))
        if shnum == 0:
            raise FatalError("%s has 0 section headers" % (self.name))
        self._read_sections(f, shoff, shnum, shstrndx)
        self._read_segments(f, _phoff, _phnum, shstrndx)

    def _read_sections(self, f, section_header_offs, section_header_count, shstrndx):
        f.seek(section_header_offs)
        len_bytes = section_header_count * self.LEN_SEC_HEADER
        section_header = f.read(len_bytes)
        if len(section_header) == 0:
            raise FatalError("No section header found at offset %04x in ELF file." % section_header_offs)
        if len(section_header) != (len_bytes):
            raise FatalError("Only read 0x%x bytes from section header (expected 0x%x.) Truncated ELF file?" % (len(section_header), len_bytes))

        # walk through the section header and extract all sections
        section_header_offsets = range(0, len(section_header), self.LEN_SEC_HEADER)

        def read_section_header(offs):
            name_offs, sec_type, _flags, lma, sec_offs, size = struct.unpack_from("<LLLLLL", section_header[offs:])
            return (name_offs, sec_type, lma, size, sec_offs)
        all_sections = [read_section_header(offs) for offs in section_header_offsets]
        prog_sections = [s for s in all_sections if s[1] == ELFFile.SEC_TYPE_PROGBITS]

        # search for the string table section
        if not (shstrndx * self.LEN_SEC_HEADER) in section_header_offsets:
            raise FatalError("ELF file has no STRTAB section at shstrndx %d" % shstrndx)
        _, sec_type, _, sec_size, sec_offs = read_section_header(shstrndx * self.LEN_SEC_HEADER)
        if sec_type != ELFFile.SEC_TYPE_STRTAB:
            print('WARNING: ELF file has incorrect STRTAB section type 0x%02x' % sec_type)
        f.seek(sec_offs)
        string_table = f.read(sec_size)

        # build the real list of ELFSections by reading the actual section names from the
        # string table section, and actual data for each section from the ELF file itself
        def lookup_string(offs):
            raw = string_table[offs:]
            return raw[:raw.index(b'\x00')]

        def read_data(offs, size):
            f.seek(offs)
            return f.read(size)

        prog_sections = [ELFSection(lookup_string(n_offs), lma, read_data(offs, size)) for (n_offs, _type, lma, size, offs) in prog_sections
                         if lma != 0 and size > 0]
        self.sections = prog_sections

    def _read_segments(self, f, segment_header_offs, segment_header_count, shstrndx):
        f.seek(segment_header_offs)
        len_bytes = segment_header_count * self.LEN_SEG_HEADER
        segment_header = f.read(len_bytes)
        if len(segment_header) == 0:
            raise FatalError("No segment header found at offset %04x in ELF file." % segment_header_offs)
        if len(segment_header) != (len_bytes):
            raise FatalError("Only read 0x%x bytes from segment header (expected 0x%x.) Truncated ELF file?" % (len(segment_header), len_bytes))

        # walk through the segment header and extract all segments
        segment_header_offsets = range(0, len(segment_header), self.LEN_SEG_HEADER)

        def read_segment_header(offs):
            seg_type, seg_offs, _vaddr, lma, size, _memsize, _flags, _align = struct.unpack_from("<LLLLLLLL", segment_header[offs:])
            return (seg_type, lma, size, seg_offs)
        all_segments = [read_segment_header(offs) for offs in segment_header_offsets]
        prog_segments = [s for s in all_segments if s[0] == ELFFile.SEG_TYPE_LOAD]

        def read_data(offs, size):
            f.seek(offs)
            return f.read(size)

        prog_segments = [ELFSection(b'PHDR', lma, read_data(offs, size)) for (_type, lma, size, offs) in prog_segments
                         if lma != 0 and size > 0]
        self.segments = prog_segments

    def sha256(self):
        # return SHA256 hash of the input ELF file
        sha256 = hashlib.sha256()
        with open(self.name, 'rb') as f:
            sha256.update(f.read())
        return sha256.digest()


def slip_reader(port, trace_function):
    """Generator to read SLIP packets from a serial port.
    Yields one full SLIP packet at a time, raises exception on timeout or invalid data.

    Designed to avoid too many calls to serial.read(1), which can bog
    down on slow systems.
    """
    partial_packet = None
    in_escape = False
    while True:
        waiting = port.inWaiting()
        read_bytes = port.read(1 if waiting == 0 else waiting)
        if read_bytes == b'':
            waiting_for = "header" if partial_packet is None else "content"
            trace_function("Timed out waiting for packet %s", waiting_for)
            raise FatalError("Timed out waiting for packet %s" % waiting_for)
        trace_function("Read %d bytes: %s", len(read_bytes), HexFormatter(read_bytes))
        for b in read_bytes:
            if type(b) is int:
                b = bytes([b])  # python 2/3 compat

            if partial_packet is None:  # waiting for packet header
                if b == b'\xc0':
                    partial_packet = b""
                else:
                    trace_function("Read invalid data: %s", HexFormatter(read_bytes))
                    trace_function("Remaining data in serial buffer: %s", HexFormatter(port.read(port.inWaiting())))
                    raise FatalError('Invalid head of packet (0x%s)' % hexify(b))
            elif in_escape:  # part-way through escape sequence
                in_escape = False
                if b == b'\xdc':
                    partial_packet += b'\xc0'
                elif b == b'\xdd':
                    partial_packet += b'\xdb'
                else:
                    trace_function("Read invalid data: %s", HexFormatter(read_bytes))
                    trace_function("Remaining data in serial buffer: %s", HexFormatter(port.read(port.inWaiting())))
                    raise FatalError('Invalid SLIP escape (0xdb, 0x%s)' % (hexify(b)))
            elif b == b'\xdb':  # start of escape sequence
                in_escape = True
            elif b == b'\xc0':  # end of packet
                trace_function("Received full packet: %s", HexFormatter(partial_packet))
                yield partial_packet
                partial_packet = None
            else:  # normal byte in packet
                partial_packet += b


def arg_auto_int(x):
    return int(x, 0)


def div_roundup(a, b):
    """ Return a/b rounded up to nearest integer,
    equivalent result to int(math.ceil(float(int(a)) / float(int(b))), only
    without possible floating point accuracy errors.
    """
    return (int(a) + int(b) - 1) // int(b)


def align_file_position(f, size):
    """ Align the position in the file to the next block of specified size """
    align = (size - 1) - (f.tell() % size)
    f.seek(align, 1)


def flash_size_bytes(size):
    """ Given a flash size of the type passed in args.flash_size
    (ie 512KB or 1MB) then return the size in bytes.
    """
    if "MB" in size:
        return int(size[:size.index("MB")]) * 1024 * 1024
    elif "KB" in size:
        return int(size[:size.index("KB")]) * 1024
    else:
        raise FatalError("Unknown size %s" % size)


def hexify(s, uppercase=True):
    format_str = '%02X' if uppercase else '%02x'
    if not PYTHON2:
        return ''.join(format_str % c for c in s)
    else:
        return ''.join(format_str % ord(c) for c in s)


class HexFormatter(object):
    """
    Wrapper class which takes binary data in its constructor
    and returns a hex string as it's __str__ method.

    This is intended for "lazy formatting" of trace() output
    in hex format. Avoids overhead (significant on slow computers)
    of generating long hex strings even if tracing is disabled.

    Note that this doesn't save any overhead if passed as an
    argument to "%", only when passed to trace()

    If auto_split is set (default), any long line (> 16 bytes) will be
    printed as separately indented lines, with ASCII decoding at the end
    of each line.
    """
    def __init__(self, binary_string, auto_split=True):
        self._s = binary_string
        self._auto_split = auto_split

    def __str__(self):
        if self._auto_split and len(self._s) > 16:
            result = ""
            s = self._s
            while len(s) > 0:
                line = s[:16]
                ascii_line = "".join(c if (c == ' ' or (c in string.printable and c not in string.whitespace))
                                     else '.' for c in line.decode('ascii', 'replace'))
                s = s[16:]
                result += "\n    %-16s %-16s | %s" % (hexify(line[:8], False), hexify(line[8:], False), ascii_line)
            return result
        else:
            return hexify(self._s, False)


def pad_to(data, alignment, pad_character=b'\xFF'):
    """ Pad to the next alignment boundary """
    pad_mod = len(data) % alignment
    if pad_mod != 0:
        data += pad_character * (alignment - pad_mod)
    return data


class FatalError(RuntimeError):
    """
    Wrapper class for runtime errors that aren't caused by internal bugs, but by
    ESP8266 responses or input content.
    """
    def __init__(self, message):
        RuntimeError.__init__(self, message)

    @staticmethod
    def WithResult(message, result):
        """
        Return a fatal error object that appends the hex values of
        'result' as a string formatted argument.
        """
        message += " (result was %s)" % hexify(result)
        return FatalError(message)


class NotImplementedInROMError(FatalError):
    """
    Wrapper class for the error thrown when a particular ESP bootloader function
    is not implemented in the ROM bootloader.
    """
    def __init__(self, bootloader, func):
        FatalError.__init__(self, "%s ROM does not support function %s." % (bootloader.CHIP_NAME, func.__name__))


class NotSupportedError(FatalError):
    def __init__(self, esp, function_name):
        FatalError.__init__(self, "Function %s is not supported for %s." % (function_name, esp.CHIP_NAME))

# "Operation" commands, executable at command line. One function each
#
# Each function takes either two args (<ESPLoader instance>, <args>) or a single <args>
# argument.


class UnsupportedCommandError(RuntimeError):
    """
    Wrapper class for when ROM loader returns an invalid command response.

    Usually this indicates the loader is running in Secure Download Mode.
    """
    def __init__(self, esp, op):
        if esp.secure_download_mode:
            msg = "This command (0x%x) is not supported in Secure Download Mode" % op
        else:
            msg = "Invalid (unsupported) command 0x%x" % op
        RuntimeError.__init__(self, msg)


def load_ram(esp, args):
    image = LoadFirmwareImage(esp.CHIP_NAME, args.filename)

    print('RAM boot...')
    for seg in image.segments:
        size = len(seg.data)
        print('Downloading %d bytes at %08x...' % (size, seg.addr), end=' ')
        sys.stdout.flush()
        esp.mem_begin(size, div_roundup(size, esp.ESP_RAM_BLOCK), esp.ESP_RAM_BLOCK, seg.addr)

        seq = 0
        while len(seg.data) > 0:
            esp.mem_block(seg.data[0:esp.ESP_RAM_BLOCK], seq)
            seg.data = seg.data[esp.ESP_RAM_BLOCK:]
            seq += 1
        print('done!')

    print('All segments done, executing at %08x' % image.entrypoint)
    esp.mem_finish(image.entrypoint)


def read_mem(esp, args):
    print('0x%08x = 0x%08x' % (args.address, esp.read_reg(args.address)))


def write_mem(esp, args):
    esp.write_reg(args.address, args.value, args.mask, 0)
    print('Wrote %08x, mask %08x to %08x' % (args.value, args.mask, args.address))


def dump_mem(esp, args):
    with open(args.filename, 'wb') as f:
        for i in range(args.size // 4):
            d = esp.read_reg(args.address + (i * 4))
            f.write(struct.pack(b'<I', d))
            if f.tell() % 1024 == 0:
                print_overwrite('%d bytes read... (%d %%)' % (f.tell(),
                                                              f.tell() * 100 // args.size))
            sys.stdout.flush()
        print_overwrite("Read %d bytes" % f.tell(), last_line=True)
    print('Done!')


def detect_flash_size(esp, args):
    if args.flash_size == 'detect':
        if esp.secure_download_mode:
            raise FatalError("Detecting flash size is not supported in secure download mode. Need to manually specify flash size.")
        flash_id = esp.flash_id()
        size_id = flash_id >> 16
        args.flash_size = DETECTED_FLASH_SIZES.get(size_id)
        if args.flash_size is None:
            print('Warning: Could not auto-detect Flash size (FlashID=0x%x, SizeID=0x%x), defaulting to 4MB' % (flash_id, size_id))
            args.flash_size = '4MB'
        else:
            print('Auto-detected Flash size:', args.flash_size)


def _update_image_flash_params(esp, address, args, image):
    """ Modify the flash mode & size bytes if this looks like an executable bootloader image  """
    if len(image) < 8:
        return image  # not long enough to be a bootloader image

    # unpack the (potential) image header
    magic, _, flash_mode, flash_size_freq = struct.unpack("BBBB", image[:4])
    if address != esp.BOOTLOADER_FLASH_OFFSET:
        return image  # not flashing bootloader offset, so don't modify this

    if (args.flash_mode, args.flash_freq, args.flash_size) == ('keep',) * 3:
        return image  # all settings are 'keep', not modifying anything

    # easy check if this is an image: does it start with a magic byte?
    if magic != esp.ESP_IMAGE_MAGIC:
        print("Warning: Image file at 0x%x doesn't look like an image file, so not changing any flash settings." % address)
        return image

    # make sure this really is an image, and not just data that
    # starts with esp.ESP_IMAGE_MAGIC (mostly a problem for encrypted
    # images that happen to start with a magic byte
    try:
        test_image = esp.BOOTLOADER_IMAGE(io.BytesIO(image))
        test_image.verify()
    except Exception:
        print("Warning: Image file at 0x%x is not a valid %s image, so not changing any flash settings." % (address, esp.CHIP_NAME))
        return image

    if args.flash_mode != 'keep':
        flash_mode = {'qio': 0, 'qout': 1, 'dio': 2, 'dout': 3}[args.flash_mode]

    flash_freq = flash_size_freq & 0x0F
    if args.flash_freq != 'keep':
        flash_freq = {'40m': 0, '26m': 1, '20m': 2, '80m': 0xf}[args.flash_freq]

    flash_size = flash_size_freq & 0xF0
    if args.flash_size != 'keep':
        flash_size = esp.parse_flash_size_arg(args.flash_size)

    flash_params = struct.pack(b'BB', flash_mode, flash_size + flash_freq)
    if flash_params != image[2:4]:
        print('Flash params set to 0x%04x' % struct.unpack(">H", flash_params))
        image = image[0:2] + flash_params + image[4:]
    return image


def write_flash(esp, args):
    # set args.compress based on default behaviour:
    # -> if either --compress or --no-compress is set, honour that
    # -> otherwise, set --compress unless --no-stub is set
    if args.compress is None and not args.no_compress:
        args.compress = not args.no_stub

    # In case we have encrypted files to write, we first do few sanity checks before actual flash
    if args.encrypt or args.encrypt_files is not None:
        do_write = True

        if not esp.secure_download_mode:
            if esp.get_encrypted_download_disabled():
                raise FatalError("This chip has encrypt functionality in UART download mode disabled. "
                                 "This is the Flash Encryption configuration for Production mode instead of Development mode.")

            crypt_cfg_efuse = esp.get_flash_crypt_config()

            if crypt_cfg_efuse is not None and crypt_cfg_efuse != 0xF:
                print('Unexpected FLASH_CRYPT_CONFIG value: 0x%x' % (crypt_cfg_efuse))
                do_write = False

            enc_key_valid = esp.is_flash_encryption_key_valid()

            if not enc_key_valid:
                print('Flash encryption key is not programmed')
                do_write = False

        # Determine which files list contain the ones to encrypt
        files_to_encrypt = args.addr_filename if args.encrypt else args.encrypt_files

        for address, argfile in files_to_encrypt:
            if address % esp.FLASH_ENCRYPTED_WRITE_ALIGN:
                print("File %s address 0x%x is not %d byte aligned, can't flash encrypted" %
                      (argfile.name, address, esp.FLASH_ENCRYPTED_WRITE_ALIGN))
                do_write = False

        if not do_write and not args.ignore_flash_encryption_efuse_setting:
            raise FatalError("Can't perform encrypted flash write, consult Flash Encryption documentation for more information")

    # verify file sizes fit in flash
    if args.flash_size != 'keep':  # TODO: check this even with 'keep'
        flash_end = flash_size_bytes(args.flash_size)
        for address, argfile in args.addr_filename:
            argfile.seek(0, 2)  # seek to end
            if address + argfile.tell() > flash_end:
                raise FatalError(("File %s (length %d) at offset %d will not fit in %d bytes of flash. "
                                  "Use --flash-size argument, or change flashing address.")
                                 % (argfile.name, argfile.tell(), address, flash_end))
            argfile.seek(0)

    if args.erase_all:
        erase_flash(esp, args)

    """ Create a list describing all the files we have to flash. Each entry holds an "encrypt" flag
    marking whether the file needs encryption or not. This list needs to be sorted.

    First, append to each entry of our addr_filename list the flag args.encrypt
    For example, if addr_filename is [(0x1000, "partition.bin"), (0x8000, "bootloader")],
    all_files will be [(0x1000, "partition.bin", args.encrypt), (0x8000, "bootloader", args.encrypt)],
    where, of course, args.encrypt is either True or False
    """
    all_files = [(offs, filename, args.encrypt) for (offs, filename) in args.addr_filename]

    """Now do the same with encrypt_files list, if defined.
    In this case, the flag is True
    """
    if args.encrypt_files is not None:
        encrypted_files_flag = [(offs, filename, True) for (offs, filename) in args.encrypt_files]

        # Concatenate both lists and sort them.
        # As both list are already sorted, we could simply do a merge instead,
        # but for the sake of simplicity and because the lists are very small,
        # let's use sorted.
        all_files = sorted(all_files + encrypted_files_flag, key=lambda x: x[0])

    for address, argfile, encrypted in all_files:
        compress = args.compress

        # Check whether we can compress the current file before flashing
        if compress and encrypted:
            print('\nWARNING: - compress and encrypt options are mutually exclusive ')
            print('Will flash %s uncompressed' % argfile.name)
            compress = False

        if args.no_stub:
            print('Erasing flash...')
        image = pad_to(argfile.read(), esp.FLASH_ENCRYPTED_WRITE_ALIGN if encrypted else 4)
        if len(image) == 0:
            print('WARNING: File %s is empty' % argfile.name)
            continue
        image = _update_image_flash_params(esp, address, args, image)
        calcmd5 = hashlib.md5(image).hexdigest()
        uncsize = len(image)
        if compress:
            uncimage = image
            image = zlib.compress(uncimage, 9)
            # Decompress the compressed binary a block at a time, to dynamically calculate the
            # timeout based on the real write size
            decompress = zlib.decompressobj()
            blocks = esp.flash_defl_begin(uncsize, len(image), address)
        else:
            blocks = esp.flash_begin(uncsize, address, begin_rom_encrypted=encrypted)
        argfile.seek(0)  # in case we need it again
        seq = 0
        bytes_sent = 0  # bytes sent on wire
        bytes_written = 0  # bytes written to flash
        t = time.time()

        timeout = DEFAULT_TIMEOUT

        while len(image) > 0:
            print_overwrite('Writing at 0x%08x... (%d %%)' % (address + bytes_written, 100 * (seq + 1) // blocks))
            sys.stdout.flush()
            block = image[0:esp.FLASH_WRITE_SIZE]
            if compress:
                # feeding each compressed block into the decompressor lets us see block-by-block how much will be written
                block_uncompressed = len(decompress.decompress(block))
                bytes_written += block_uncompressed
                block_timeout = max(DEFAULT_TIMEOUT, timeout_per_mb(ERASE_WRITE_TIMEOUT_PER_MB, block_uncompressed))
                if not esp.IS_STUB:
                    timeout = block_timeout  # ROM code writes block to flash before ACKing
                esp.flash_defl_block(block, seq, timeout=timeout)
                if esp.IS_STUB:
                    timeout = block_timeout  # Stub ACKs when block is received, then writes to flash while receiving the block after it
            else:
                # Pad the last block
                block = block + b'\xff' * (esp.FLASH_WRITE_SIZE - len(block))
                if encrypted:
                    esp.flash_encrypt_block(block, seq)
                else:
                    esp.flash_block(block, seq)
                bytes_written += len(block)
            bytes_sent += len(block)
            image = image[esp.FLASH_WRITE_SIZE:]
            seq += 1

        if esp.IS_STUB:
            # Stub only writes each block to flash after 'ack'ing the receive, so do a final dummy operation which will
            # not be 'ack'ed until the last block has actually been written out to flash
            esp.read_reg(ESPLoader.CHIP_DETECT_MAGIC_REG_ADDR, timeout=timeout)

        t = time.time() - t
        speed_msg = ""
        if compress:
            if t > 0.0:
                speed_msg = " (effective %.1f kbit/s)" % (uncsize / t * 8 / 1000)
            print_overwrite('Wrote %d bytes (%d compressed) at 0x%08x in %.1f seconds%s...' % (uncsize,
                                                                                               bytes_sent,
                                                                                               address, t, speed_msg), last_line=True)
        else:
            if t > 0.0:
                speed_msg = " (%.1f kbit/s)" % (bytes_written / t * 8 / 1000)
            print_overwrite('Wrote %d bytes at 0x%08x in %.1f seconds%s...' % (bytes_written, address, t, speed_msg), last_line=True)

        if not encrypted and not esp.secure_download_mode:
            try:
                res = esp.flash_md5sum(address, uncsize)
                if res != calcmd5:
                    print('File  md5: %s' % calcmd5)
                    print('Flash md5: %s' % res)
                    print('MD5 of 0xFF is %s' % (hashlib.md5(b'\xFF' * uncsize).hexdigest()))
                    raise FatalError("MD5 of file does not match data in flash!")
                else:
                    print('Hash of data verified.')
            except NotImplementedInROMError:
                pass

    print('\nLeaving...')

    if esp.IS_STUB:
        # skip sending flash_finish to ROM loader here,
        # as it causes the loader to exit and run user code
        esp.flash_begin(0, 0)

        # Get the "encrypted" flag for the last file flashed
        # Note: all_files list contains triplets like:
        # (address: Integer, filename: String, encrypted: Boolean)
        last_file_encrypted = all_files[-1][2]

        # Check whether the last file flashed was compressed or not
        if args.compress and not last_file_encrypted:
            esp.flash_defl_finish(False)
        else:
            esp.flash_finish(False)

    if args.verify:
        print('Verifying just-written flash...')
        print('(This option is deprecated, flash contents are now always read back after flashing.)')
        # If some encrypted files have been flashed print a warning saying that we won't check them
        if args.encrypt or args.encrypt_files is not None:
            print('WARNING: - cannot verify encrypted files, they will be ignored')
        # Call verify_flash function only if there at least one non-encrypted file flashed
        if not args.encrypt:
            verify_flash(esp, args)


def image_info(args):
    image = LoadFirmwareImage(args.chip, args.filename)
    print('Image version: %d' % image.version)
    print('Entry point: %08x' % image.entrypoint if image.entrypoint != 0 else 'Entry point not set')
    print('%d segments' % len(image.segments))
    print()
    idx = 0
    for seg in image.segments:
        idx += 1
        segs = seg.get_memory_type(image)
        seg_name = ",".join(segs)
        print('Segment %d: %r [%s]' % (idx, seg, seg_name))
    calc_checksum = image.calculate_checksum()
    print('Checksum: %02x (%s)' % (image.checksum,
                                   'valid' if image.checksum == calc_checksum else 'invalid - calculated %02x' % calc_checksum))
    try:
        digest_msg = 'Not appended'
        if image.append_digest:
            is_valid = image.stored_digest == image.calc_digest
            digest_msg = "%s (%s)" % (hexify(image.calc_digest).lower(),
                                      "valid" if is_valid else "invalid")
            print('Validation Hash: %s' % digest_msg)
    except AttributeError:
        pass  # ESP8266 image has no append_digest field


def make_image(args):
    image = ESP8266ROMFirmwareImage()
    if len(args.segfile) == 0:
        raise FatalError('No segments specified')
    if len(args.segfile) != len(args.segaddr):
        raise FatalError('Number of specified files does not match number of specified addresses')
    for (seg, addr) in zip(args.segfile, args.segaddr):
        with open(seg, 'rb') as f:
            data = f.read()
            image.segments.append(ImageSegment(addr, data))
    image.entrypoint = args.entrypoint
    image.save(args.output)


def elf2image(args):
    e = ELFFile(args.input)
    if args.chip == 'auto':  # Default to ESP8266 for backwards compatibility
        print("Creating image for ESP8266...")
        args.chip = 'esp8266'

    if args.chip == 'esp32':
        image = ESP32FirmwareImage()
        if args.secure_pad:
            image.secure_pad = '1'
        elif args.secure_pad_v2:
            image.secure_pad = '2'
        image.min_rev = int(args.min_rev)
    elif args.chip == 'esp32s2':
        image = ESP32S2FirmwareImage()
        if args.secure_pad_v2:
            image.secure_pad = '2'
        image.min_rev = 0
    elif args.chip == 'esp32s3beta2':
        image = ESP32S3BETA2FirmwareImage()
        if args.secure_pad_v2:
            image.secure_pad = '2'
        image.min_rev = 0
    elif args.chip == 'esp32c3':
        image = ESP32C3FirmwareImage()
        if args.secure_pad_v2:
            image.secure_pad = '2'
        image.min_rev = 0
    elif args.version == '1':  # ESP8266
        image = ESP8266ROMFirmwareImage()
    else:
        image = ESP8266V2FirmwareImage()
    image.entrypoint = e.entrypoint
    image.flash_mode = {'qio': 0, 'qout': 1, 'dio': 2, 'dout': 3}[args.flash_mode]

    # ELFSection is a subclass of ImageSegment, so can use interchangeably
    image.segments = e.segments if args.use_segments else e.sections

    image.flash_size_freq = image.ROM_LOADER.FLASH_SIZES[args.flash_size]
    image.flash_size_freq += {'40m': 0, '26m': 1, '20m': 2, '80m': 0xf}[args.flash_freq]

    if args.elf_sha256_offset:
        image.elf_sha256 = e.sha256()
        image.elf_sha256_offset = args.elf_sha256_offset

    before = len(image.segments)
    image.merge_adjacent_segments()
    if len(image.segments) != before:
        delta = before - len(image.segments)
        print("Merged %d ELF section%s" % (delta, "s" if delta > 1 else ""))

    image.verify()

    if args.output is None:
        args.output = image.default_output_name(args.input)
    image.save(args.output)


def read_mac(esp, args):
    mac = esp.read_mac()

    def print_mac(label, mac):
        print('%s: %s' % (label, ':'.join(map(lambda x: '%02x' % x, mac))))
    print_mac("MAC", mac)


def chip_id(esp, args):
    try:
        chipid = esp.chip_id()
        print('Chip ID: 0x%08x' % chipid)
    except NotSupportedError:
        print('Warning: %s has no Chip ID. Reading MAC instead.' % esp.CHIP_NAME)
        read_mac(esp, args)


def erase_flash(esp, args):
    print('Erasing flash (this may take a while)...')
    t = time.time()
    esp.erase_flash()
    print('Chip erase completed successfully in %.1fs' % (time.time() - t))


def erase_region(esp, args):
    print('Erasing region (may be slow depending on size)...')
    t = time.time()
    esp.erase_region(args.address, args.size)
    print('Erase completed successfully in %.1f seconds.' % (time.time() - t))


def run(esp, args):
    esp.run()


def flash_id(esp, args):
    flash_id = esp.flash_id()
    print('Manufacturer: %02x' % (flash_id & 0xff))
    flid_lowbyte = (flash_id >> 16) & 0xFF
    print('Device: %02x%02x' % ((flash_id >> 8) & 0xff, flid_lowbyte))
    print('Detected flash size: %s' % (DETECTED_FLASH_SIZES.get(flid_lowbyte, "Unknown")))


def read_flash(esp, args):
    if args.no_progress:
        flash_progress = None
    else:
        def flash_progress(progress, length):
            msg = '%d (%d %%)' % (progress, progress * 100.0 / length)
            padding = '\b' * len(msg)
            if progress == length:
                padding = '\n'
            sys.stdout.write(msg + padding)
            sys.stdout.flush()
    t = time.time()
    data = esp.read_flash(args.address, args.size, flash_progress)
    t = time.time() - t
    print_overwrite('Read %d bytes at 0x%x in %.1f seconds (%.1f kbit/s)...'
                    % (len(data), args.address, t, len(data) / t * 8 / 1000), last_line=True)
    with open(args.filename, 'wb') as f:
        f.write(data)


def verify_flash(esp, args):
    differences = False

    for address, argfile in args.addr_filename:
        image = pad_to(argfile.read(), 4)
        argfile.seek(0)  # rewind in case we need it again

        image = _update_image_flash_params(esp, address, args, image)

        image_size = len(image)
        print('Verifying 0x%x (%d) bytes @ 0x%08x in flash against %s...' % (image_size, image_size, address, argfile.name))
        # Try digest first, only read if there are differences.
        digest = esp.flash_md5sum(address, image_size)
        expected_digest = hashlib.md5(image).hexdigest()
        if digest == expected_digest:
            print('-- verify OK (digest matched)')
            continue
        else:
            differences = True
            if getattr(args, 'diff', 'no') != 'yes':
                print('-- verify FAILED (digest mismatch)')
                continue

        flash = esp.read_flash(address, image_size)
        assert flash != image
        diff = [i for i in range(image_size) if flash[i] != image[i]]
        print('-- verify FAILED: %d differences, first @ 0x%08x' % (len(diff), address + diff[0]))
        for d in diff:
            flash_byte = flash[d]
            image_byte = image[d]
            if PYTHON2:
                flash_byte = ord(flash_byte)
                image_byte = ord(image_byte)
            print('   %08x %02x %02x' % (address + d, flash_byte, image_byte))
    if differences:
        raise FatalError("Verify failed.")


def read_flash_status(esp, args):
    print('Status value: 0x%04x' % esp.read_status(args.bytes))


def write_flash_status(esp, args):
    fmt = "0x%%0%dx" % (args.bytes * 2)
    args.value = args.value & ((1 << (args.bytes * 8)) - 1)
    print(('Initial flash status: ' + fmt) % esp.read_status(args.bytes))
    print(('Setting flash status: ' + fmt) % args.value)
    esp.write_status(args.value, args.bytes, args.non_volatile)
    print(('After flash status:   ' + fmt) % esp.read_status(args.bytes))


def get_security_info(esp, args):
    (flags, flash_crypt_cnt, key_purposes) = esp.get_security_info()
    # TODO: better display
    print('Flags: 0x%08x (%s)' % (flags, bin(flags)))
    print('Flash_Crypt_Cnt: 0x%x' % flash_crypt_cnt)
    print('Key_Purposes: %s' % (key_purposes,))


def merge_bin(args):
    chip_class = _chip_to_rom_loader(args.chip)

    # sort the files by offset. The AddrFilenamePairAction has already checked for overlap
    input_files = sorted(args.addr_filename, key=lambda x: x[0])
    if not input_files:
        raise FatalError("No input files specified")
    first_addr = input_files[0][0]
    if first_addr < args.target_offset:
        raise FatalError("Output file target offset is 0x%x. Input file offset 0x%x is before this." % (args.target_offset, first_addr))

    if args.format != 'raw':
        raise FatalError("This version of esptool only supports the 'raw' output format")

    with open(args.output, 'wb') as of:
        def pad_to(flash_offs):
            # account for output file offset if there is any
            of.write(b'\xFF' * (flash_offs - args.target_offset - of.tell()))
        for addr, argfile in input_files:
            pad_to(addr)
            image = argfile.read()
            image = _update_image_flash_params(chip_class, addr, args, image)
            of.write(image)
        if args.fill_flash_size:
            pad_to(flash_size_bytes(args.fill_flash_size))
        print("Wrote 0x%x bytes to file %s, ready to flash to offset 0x%x" % (of.tell(), args.output, args.target_offset))


def version(args):
    print(__version__)

#
# End of operations functions
#


def main(argv=None, esp=None):
    """
    Main function for esptool

    argv - Optional override for default arguments parsing (that uses sys.argv), can be a list of custom arguments
    as strings. Arguments and their values need to be added as individual items to the list e.g. "-b 115200" thus
    becomes ['-b', '115200'].

    esp - Optional override of the connected device previously returned by get_default_connected_device()
    """

    external_esp = esp is not None

    parser = argparse.ArgumentParser(description='esptool.py v%s - ESP8266 ROM Bootloader Utility' % __version__, prog='esptool')

    parser.add_argument('--chip', '-c',
                        help='Target chip type',
                        type=lambda c: c.lower().replace('-', ''),  # support ESP32-S2, etc.
                        choices=['auto', 'esp8266', 'esp32', 'esp32s2', 'esp32s3beta2', 'esp32c3'],
                        default=os.environ.get('ESPTOOL_CHIP', 'auto'))

    parser.add_argument(
        '--port', '-p',
        help='Serial port device',
        default=os.environ.get('ESPTOOL_PORT', None))

    parser.add_argument(
        '--baud', '-b',
        help='Serial port baud rate used when flashing/reading',
        type=arg_auto_int,
        default=os.environ.get('ESPTOOL_BAUD', ESPLoader.ESP_ROM_BAUD))

    parser.add_argument(
        '--before',
        help='What to do before connecting to the chip',
        choices=['default_reset', 'no_reset', 'no_reset_no_sync'],
        default=os.environ.get('ESPTOOL_BEFORE', 'default_reset'))

    parser.add_argument(
        '--after', '-a',
        help='What to do after esptool.py is finished',
        choices=['hard_reset', 'soft_reset', 'no_reset', 'no_reset_stub'],
        default=os.environ.get('ESPTOOL_AFTER', 'hard_reset'))

    parser.add_argument(
        '--no-stub',
        help="Disable launching the flasher stub, only talk to ROM bootloader. Some features will not be available.",
        action='store_true')

    parser.add_argument(
        '--trace', '-t',
        help="Enable trace-level output of esptool.py interactions.",
        action='store_true')

    parser.add_argument(
        '--override-vddsdio',
        help="Override ESP32 VDDSDIO internal voltage regulator (use with care)",
        choices=ESP32ROM.OVERRIDE_VDDSDIO_CHOICES,
        nargs='?')

    parser.add_argument(
        '--connect-attempts',
        help=('Number of attempts to connect, negative or 0 for infinite. '
              'Default: %d.' % DEFAULT_CONNECT_ATTEMPTS),
        type=int,
        default=os.environ.get('ESPTOOL_CONNECT_ATTEMPTS', DEFAULT_CONNECT_ATTEMPTS))

    subparsers = parser.add_subparsers(
        dest='operation',
        help='Run esptool {command} -h for additional help')

    def add_spi_connection_arg(parent):
        parent.add_argument('--spi-connection', '-sc', help='ESP32-only argument. Override default SPI Flash connection. '
                            'Value can be SPI, HSPI or a comma-separated list of 5 I/O numbers to use for SPI flash (CLK,Q,D,HD,CS).',
                            action=SpiConnectionAction)

    parser_load_ram = subparsers.add_parser(
        'load_ram',
        help='Download an image to RAM and execute')
    parser_load_ram.add_argument('filename', help='Firmware image')

    parser_dump_mem = subparsers.add_parser(
        'dump_mem',
        help='Dump arbitrary memory to disk')
    parser_dump_mem.add_argument('address', help='Base address', type=arg_auto_int)
    parser_dump_mem.add_argument('size', help='Size of region to dump', type=arg_auto_int)
    parser_dump_mem.add_argument('filename', help='Name of binary dump')

    parser_read_mem = subparsers.add_parser(
        'read_mem',
        help='Read arbitrary memory location')
    parser_read_mem.add_argument('address', help='Address to read', type=arg_auto_int)

    parser_write_mem = subparsers.add_parser(
        'write_mem',
        help='Read-modify-write to arbitrary memory location')
    parser_write_mem.add_argument('address', help='Address to write', type=arg_auto_int)
    parser_write_mem.add_argument('value', help='Value', type=arg_auto_int)
    parser_write_mem.add_argument('mask', help='Mask of bits to write', type=arg_auto_int, nargs='?', default='0xFFFFFFFF')

    def add_spi_flash_subparsers(parent, allow_keep, auto_detect):
        """ Add common parser arguments for SPI flash properties """
        extra_keep_args = ['keep'] if allow_keep else []

        if auto_detect and allow_keep:
            extra_fs_message = ", detect, or keep"
        elif auto_detect:
            extra_fs_message = ", or detect"
        elif allow_keep:
            extra_fs_message = ", or keep"
        else:
            extra_fs_message = ""

        parent.add_argument('--flash_freq', '-ff', help='SPI Flash frequency',
                            choices=extra_keep_args + ['40m', '26m', '20m', '80m'],
                            default=os.environ.get('ESPTOOL_FF', 'keep' if allow_keep else '40m'))
        parent.add_argument('--flash_mode', '-fm', help='SPI Flash mode',
                            choices=extra_keep_args + ['qio', 'qout', 'dio', 'dout'],
                            default=os.environ.get('ESPTOOL_FM', 'keep' if allow_keep else 'qio'))
        parent.add_argument('--flash_size', '-fs', help='SPI Flash size in MegaBytes (1MB, 2MB, 4MB, 8MB, 16M)'
                            ' plus ESP8266-only (256KB, 512KB, 2MB-c1, 4MB-c1)' + extra_fs_message,
                            action=FlashSizeAction, auto_detect=auto_detect,
                            default=os.environ.get('ESPTOOL_FS', 'keep' if allow_keep else '1MB'))
        add_spi_connection_arg(parent)

    parser_write_flash = subparsers.add_parser(
        'write_flash',
        help='Write a binary blob to flash')

    parser_write_flash.add_argument('addr_filename', metavar='<address> <filename>', help='Address followed by binary filename, separated by space',
                                    action=AddrFilenamePairAction)
    parser_write_flash.add_argument('--erase-all', '-e',
                                    help='Erase all regions of flash (not just write areas) before programming',
                                    action="store_true")

    add_spi_flash_subparsers(parser_write_flash, allow_keep=True, auto_detect=True)
    parser_write_flash.add_argument('--no-progress', '-p', help='Suppress progress output', action="store_true")
    parser_write_flash.add_argument('--verify', help='Verify just-written data on flash '
                                    '(mostly superfluous, data is read back during flashing)', action='store_true')
    parser_write_flash.add_argument('--encrypt', help='Apply flash encryption when writing data (required correct efuse settings)',
                                    action='store_true')
    # In order to not break backward compatibility, our list of encrypted files to flash is a new parameter
    parser_write_flash.add_argument('--encrypt-files', metavar='<address> <filename>',
                                    help='Files to be encrypted on the flash. Address followed by binary filename, separated by space.',
                                    action=AddrFilenamePairAction)
    parser_write_flash.add_argument('--ignore-flash-encryption-efuse-setting', help='Ignore flash encryption efuse settings ',
                                    action='store_true')

    compress_args = parser_write_flash.add_mutually_exclusive_group(required=False)
    compress_args.add_argument('--compress', '-z', help='Compress data in transfer (default unless --no-stub is specified)',
                               action="store_true", default=None)
    compress_args.add_argument('--no-compress', '-u', help='Disable data compression during transfer (default if --no-stub is specified)',
                               action="store_true")

    subparsers.add_parser(
        'run',
        help='Run application code in flash')

    parser_image_info = subparsers.add_parser(
        'image_info',
        help='Dump headers from an application image')
    parser_image_info.add_argument('filename', help='Image file to parse')

    parser_make_image = subparsers.add_parser(
        'make_image',
        help='Create an application image from binary files')
    parser_make_image.add_argument('output', help='Output image file')
    parser_make_image.add_argument('--segfile', '-f', action='append', help='Segment input file')
    parser_make_image.add_argument('--segaddr', '-a', action='append', help='Segment base address', type=arg_auto_int)
    parser_make_image.add_argument('--entrypoint', '-e', help='Address of entry point', type=arg_auto_int, default=0)

    parser_elf2image = subparsers.add_parser(
        'elf2image',
        help='Create an application image from ELF file')
    parser_elf2image.add_argument('input', help='Input ELF file')
    parser_elf2image.add_argument('--output', '-o', help='Output filename prefix (for version 1 image), or filename (for version 2 single image)', type=str)
    parser_elf2image.add_argument('--version', '-e', help='Output image version', choices=['1', '2'], default='1')
    parser_elf2image.add_argument('--min-rev', '-r', help='Minimum chip revision', choices=['0', '1', '2', '3'], default='0')
    parser_elf2image.add_argument('--secure-pad', action='store_true',
                                  help='Pad image so once signed it will end on a 64KB boundary. For Secure Boot v1 images only.')
    parser_elf2image.add_argument('--secure-pad-v2', action='store_true',
                                  help='Pad image to 64KB, so once signed its signature sector will start at the next 64K block. '
                                  'For Secure Boot v2 images only.')
    parser_elf2image.add_argument('--elf-sha256-offset', help='If set, insert SHA256 hash (32 bytes) of the input ELF file at specified offset in the binary.',
                                  type=arg_auto_int, default=None)
    parser_elf2image.add_argument('--use_segments', help='If set, ELF segments will be used instead of ELF sections to genereate the image.',
                                  action='store_true')

    add_spi_flash_subparsers(parser_elf2image, allow_keep=False, auto_detect=False)

    subparsers.add_parser(
        'read_mac',
        help='Read MAC address from OTP ROM')

    subparsers.add_parser(
        'chip_id',
        help='Read Chip ID from OTP ROM')

    parser_flash_id = subparsers.add_parser(
        'flash_id',
        help='Read SPI flash manufacturer and device ID')
    add_spi_connection_arg(parser_flash_id)

    parser_read_status = subparsers.add_parser(
        'read_flash_status',
        help='Read SPI flash status register')

    add_spi_connection_arg(parser_read_status)
    parser_read_status.add_argument('--bytes', help='Number of bytes to read (1-3)', type=int, choices=[1, 2, 3], default=2)

    parser_write_status = subparsers.add_parser(
        'write_flash_status',
        help='Write SPI flash status register')

    add_spi_connection_arg(parser_write_status)
    parser_write_status.add_argument('--non-volatile', help='Write non-volatile bits (use with caution)', action='store_true')
    parser_write_status.add_argument('--bytes', help='Number of status bytes to write (1-3)', type=int, choices=[1, 2, 3], default=2)
    parser_write_status.add_argument('value', help='New value', type=arg_auto_int)

    parser_read_flash = subparsers.add_parser(
        'read_flash',
        help='Read SPI flash content')
    add_spi_connection_arg(parser_read_flash)
    parser_read_flash.add_argument('address', help='Start address', type=arg_auto_int)
    parser_read_flash.add_argument('size', help='Size of region to dump', type=arg_auto_int)
    parser_read_flash.add_argument('filename', help='Name of binary dump')
    parser_read_flash.add_argument('--no-progress', '-p', help='Suppress progress output', action="store_true")

    parser_verify_flash = subparsers.add_parser(
        'verify_flash',
        help='Verify a binary blob against flash')
    parser_verify_flash.add_argument('addr_filename', help='Address and binary file to verify there, separated by space',
                                     action=AddrFilenamePairAction)
    parser_verify_flash.add_argument('--diff', '-d', help='Show differences',
                                     choices=['no', 'yes'], default='no')
    add_spi_flash_subparsers(parser_verify_flash, allow_keep=True, auto_detect=True)

    parser_erase_flash = subparsers.add_parser(
        'erase_flash',
        help='Perform Chip Erase on SPI flash')
    add_spi_connection_arg(parser_erase_flash)

    parser_erase_region = subparsers.add_parser(
        'erase_region',
        help='Erase a region of the flash')
    add_spi_connection_arg(parser_erase_region)
    parser_erase_region.add_argument('address', help='Start address (must be multiple of 4096)', type=arg_auto_int)
    parser_erase_region.add_argument('size', help='Size of region to erase (must be multiple of 4096)', type=arg_auto_int)

    parser_merge_bin = subparsers.add_parser(
        'merge_bin',
        help='Merge multiple raw binary files into a single file for later flashing')

    parser_merge_bin.add_argument('--output', '-o', help='Output filename', type=str, required=True)
    parser_merge_bin.add_argument('--format', '-f', help='Format of the output file', choices='raw', default='raw')  # for future expansion
    add_spi_flash_subparsers(parser_merge_bin, allow_keep=True, auto_detect=False)

    parser_merge_bin.add_argument('--target-offset', '-t', help='Target offset where the output file will be flashed',
                                  type=arg_auto_int, default=0)
    parser_merge_bin.add_argument('--fill-flash-size', help='If set, the final binary file will be padded with FF '
                                  'bytes up to this flash size.', action=FlashSizeAction)
    parser_merge_bin.add_argument('addr_filename', metavar='<address> <filename>',
                                  help='Address followed by binary filename, separated by space',
                                  action=AddrFilenamePairAction)

    subparsers.add_parser(
        'version', help='Print esptool version')

    subparsers.add_parser('get_security_info', help='Get some security-related data')

    # internal sanity check - every operation matches a module function of the same name
    for operation in subparsers.choices.keys():
        assert operation in globals(), "%s should be a module function" % operation

    argv = expand_file_arguments(argv or sys.argv[1:])

    args = parser.parse_args(argv)
    print('esptool.py v%s' % __version__)

    # operation function can take 1 arg (args), 2 args (esp, arg)
    # or be a member function of the ESPLoader class.

    if args.operation is None:
        parser.print_help()
        sys.exit(1)

    # Forbid the usage of both --encrypt, which means encrypt all the given files,
    # and --encrypt-files, which represents the list of files to encrypt.
    # The reason is that allowing both at the same time increases the chances of
    # having contradictory lists (e.g. one file not available in one of list).
    if args.operation == "write_flash" and args.encrypt and args.encrypt_files is not None:
        raise FatalError("Options --encrypt and --encrypt-files must not be specified at the same time.")

    operation_func = globals()[args.operation]

    if PYTHON2:
        # This function is depreciated in Python3
        operation_args = inspect.getargspec(operation_func).args
    else:
        operation_args = inspect.getfullargspec(operation_func).args

    if operation_args[0] == 'esp':  # operation function takes an ESPLoader connection object
        if args.before != "no_reset_no_sync":
            initial_baud = min(ESPLoader.ESP_ROM_BAUD, args.baud)  # don't sync faster than the default baud rate
        else:
            initial_baud = args.baud

        if args.port is None:
            ser_list = get_port_list()
            print("Found %d serial ports" % len(ser_list))
        else:
            ser_list = [args.port]
        esp = esp or get_default_connected_device(ser_list, port=args.port, connect_attempts=args.connect_attempts,
                                                  initial_baud=initial_baud, chip=args.chip, trace=args.trace,
                                                  before=args.before)
        if esp is None:
            raise FatalError("Could not connect to an Espressif device on any of the %d available serial ports." % len(ser_list))

        if esp.secure_download_mode:
            print("Chip is %s in Secure Download Mode" % esp.CHIP_NAME)
        else:
            print("Chip is %s" % (esp.get_chip_description()))
            print("Features: %s" % ", ".join(esp.get_chip_features()))
            print("Crystal is %dMHz" % esp.get_crystal_freq())
            read_mac(esp, args)

        if not args.no_stub:
            if esp.secure_download_mode:
                print("WARNING: Stub loader is not supported in Secure Download Mode, setting --no-stub")
                args.no_stub = True
            else:
                esp = esp.run_stub()

        if args.override_vddsdio:
            esp.override_vddsdio(args.override_vddsdio)

        if args.baud > initial_baud:
            try:
                esp.change_baud(args.baud)
            except NotImplementedInROMError:
                print("WARNING: ROM doesn't support changing baud rate. Keeping initial baud rate %d" % initial_baud)

        # override common SPI flash parameter stuff if configured to do so
        if hasattr(args, "spi_connection") and args.spi_connection is not None:
            if esp.CHIP_NAME != "ESP32":
                raise FatalError("Chip %s does not support --spi-connection option." % esp.CHIP_NAME)
            print("Configuring SPI flash mode...")
            esp.flash_spi_attach(args.spi_connection)
        elif args.no_stub:
            print("Enabling default SPI flash mode...")
            # ROM loader doesn't enable flash unless we explicitly do it
            esp.flash_spi_attach(0)

        if hasattr(args, "flash_size"):
            print("Configuring flash size...")
            detect_flash_size(esp, args)
            if args.flash_size != 'keep':  # TODO: should set this even with 'keep'
                esp.flash_set_parameters(flash_size_bytes(args.flash_size))

        try:
            operation_func(esp, args)
        finally:
            try:  # Clean up AddrFilenamePairAction files
                for address, argfile in args.addr_filename:
                    argfile.close()
            except AttributeError:
                pass

        # Handle post-operation behaviour (reset or other)
        if operation_func == load_ram:
            # the ESP is now running the loaded image, so let it run
            print('Exiting immediately.')
        elif args.after == 'hard_reset':
            print('Hard resetting via RTS pin...')
            esp.hard_reset()
        elif args.after == 'soft_reset':
            print('Soft resetting...')
            # flash_finish will trigger a soft reset
            esp.soft_reset(False)
        elif args.after == 'no_reset_stub':
            print('Staying in flasher stub.')
        else:  # args.after == 'no_reset'
            print('Staying in bootloader.')
            if esp.IS_STUB:
                esp.soft_reset(True)  # exit stub back to ROM loader

        if not external_esp:
            esp._port.close()

    else:
        operation_func(args)


def get_port_list():
    if list_ports is None:
        raise FatalError("Listing all serial ports is currently not available. Please try to specify the port when "
                         "running esptool.py or update the pyserial package to the latest version")
    return sorted(ports.device for ports in list_ports.comports())


def expand_file_arguments(argv):
    """ Any argument starting with "@" gets replaced with all values read from a text file.
    Text file arguments can be split by newline or by space.
    Values are added "as-is", as if they were specified in this order on the command line.
    """
    new_args = []
    expanded = False
    for arg in argv:
        if arg.startswith("@"):
            expanded = True
            with open(arg[1:], "r") as f:
                for line in f.readlines():
                    new_args += shlex.split(line)
        else:
            new_args.append(arg)
    if expanded:
        print("esptool.py %s" % (" ".join(new_args[1:])))
        return new_args
    return argv


class FlashSizeAction(argparse.Action):
    """ Custom flash size parser class to support backwards compatibility with megabit size arguments.

    (At next major relase, remove deprecated sizes and this can become a 'normal' choices= argument again.)
    """
    def __init__(self, option_strings, dest, nargs=1, auto_detect=False, **kwargs):
        super(FlashSizeAction, self).__init__(option_strings, dest, nargs, **kwargs)
        self._auto_detect = auto_detect

    def __call__(self, parser, namespace, values, option_string=None):
        try:
            value = {
                '2m': '256KB',
                '4m': '512KB',
                '8m': '1MB',
                '16m': '2MB',
                '32m': '4MB',
                '16m-c1': '2MB-c1',
                '32m-c1': '4MB-c1',
            }[values[0]]
            print("WARNING: Flash size arguments in megabits like '%s' are deprecated." % (values[0]))
            print("Please use the equivalent size '%s'." % (value))
            print("Megabit arguments may be removed in a future release.")
        except KeyError:
            value = values[0]

        known_sizes = dict(ESP8266ROM.FLASH_SIZES)
        known_sizes.update(ESP32ROM.FLASH_SIZES)
        if self._auto_detect:
            known_sizes['detect'] = 'detect'
            known_sizes['keep'] = 'keep'
        if value not in known_sizes:
            raise argparse.ArgumentError(self, '%s is not a known flash size. Known sizes: %s' % (value, ", ".join(known_sizes.keys())))
        setattr(namespace, self.dest, value)


class SpiConnectionAction(argparse.Action):
    """ Custom action to parse 'spi connection' override. Values are SPI, HSPI, or a sequence of 5 pin numbers separated by commas.
    """
    def __call__(self, parser, namespace, value, option_string=None):
        if value.upper() == "SPI":
            value = 0
        elif value.upper() == "HSPI":
            value = 1
        elif "," in value:
            values = value.split(",")
            if len(values) != 5:
                raise argparse.ArgumentError(self, '%s is not a valid list of comma-separate pin numbers. Must be 5 numbers - CLK,Q,D,HD,CS.' % value)
            try:
                values = tuple(int(v, 0) for v in values)
            except ValueError:
                raise argparse.ArgumentError(self, '%s is not a valid argument. All pins must be numeric values' % values)
            if any([v for v in values if v > 33 or v < 0]):
                raise argparse.ArgumentError(self, 'Pin numbers must be in the range 0-33.')
            # encode the pin numbers as a 32-bit integer with packed 6-bit values, the same way ESP32 ROM takes them
            # TODO: make this less ESP32 ROM specific somehow...
            clk, q, d, hd, cs = values
            value = (hd << 24) | (cs << 18) | (d << 12) | (q << 6) | clk
        else:
            raise argparse.ArgumentError(self, '%s is not a valid spi-connection value. '
                                         'Values are SPI, HSPI, or a sequence of 5 pin numbers CLK,Q,D,HD,CS).' % value)
        setattr(namespace, self.dest, value)


class AddrFilenamePairAction(argparse.Action):
    """ Custom parser class for the address/filename pairs passed as arguments """
    def __init__(self, option_strings, dest, nargs='+', **kwargs):
        super(AddrFilenamePairAction, self).__init__(option_strings, dest, nargs, **kwargs)

    def __call__(self, parser, namespace, values, option_string=None):
        # validate pair arguments
        pairs = []
        for i in range(0, len(values), 2):
            try:
                address = int(values[i], 0)
            except ValueError:
                raise argparse.ArgumentError(self, 'Address "%s" must be a number' % values[i])
            try:
                argfile = open(values[i + 1], 'rb')
            except IOError as e:
                raise argparse.ArgumentError(self, e)
            except IndexError:
                raise argparse.ArgumentError(self, 'Must be pairs of an address and the binary filename to write there')
            pairs.append((address, argfile))

        # Sort the addresses and check for overlapping
        end = 0
        for address, argfile in sorted(pairs, key=lambda x: x[0]):
            argfile.seek(0, 2)  # seek to end
            size = argfile.tell()
            argfile.seek(0)
            sector_start = address & ~(ESPLoader.FLASH_SECTOR_SIZE - 1)
            sector_end = ((address + size + ESPLoader.FLASH_SECTOR_SIZE - 1) & ~(ESPLoader.FLASH_SECTOR_SIZE - 1)) - 1
            if sector_start < end:
                message = 'Detected overlap at address: 0x%x for file: %s' % (address, argfile.name)
                raise argparse.ArgumentError(self, message)
            end = sector_end
        setattr(namespace, self.dest, pairs)


# Binary stub code (see flasher_stub dir for source & details)
ESP8266ROM.STUB_CODE = eval(zlib.decompress(base64.b64decode(b"""
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\
cuMsUokxn/4fuCei1Q==\
""")))
ESP32ROM.STUB_CODE = eval(zlib.decompress(base64.b64decode(b"""
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\
78nnHAf8JCY0ydR0mqZf/gdCFgp2\
""")))
ESP32S2ROM.STUB_CODE = eval(zlib.decompress(base64.b64decode(b"""
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\
""")))
ESP32S3BETA2ROM.STUB_CODE = eval(zlib.decompress(base64.b64decode(b"""
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\
zdp0Ph615sUhPwkJRXGWj/P48/8AMJEgWg==\
""")))
ESP32C3ROM.STUB_CODE = eval(zlib.decompress(base64.b64decode(b"""
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\
""")))


def _main():
    try:
        main()
    except FatalError as e:
        print('\nA fatal error occurred: %s' % e)
        sys.exit(2)


if __name__ == '__main__':
    _main()
