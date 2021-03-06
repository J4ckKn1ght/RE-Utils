import os
import sys
import clr

sys.path.append("..\\B2R2")
clr.AddReference("MyUtils")
from MyUtils import *

import Utils
from string import printable
from unicorn import *


def hook_mem_invalid(uc, type, address, size, value, user_data):
    if type == UC_MEM_READ_UNMAPPED:
        print(">>> Missing memory is being READ at 0x%x, data size = %u, data value = 0x%x\n" % (address, size, value))
    return False


class Emulator:
    def __init__(self, fileName):
        self.binary = Common.Binary(fileName)
        self.uc = None
        self.assembler = None
        self.disassmbler = None

    def readData(self, address, number, size):
        data = self.uc.mem_read(address, number * size)
        return Utils.d2n(data, size)

    def readString(self, address):
        data = self.uc.mem_read(address, 1)[0]
        address += 1
        string = ''
        while chr(data) in printable:
            string += chr(data)
            data = self.uc.mem_read(address, 1)[0]
            address += 1
            if data == 0:
                break
        return string

    def writeData(self, address, data, size):
        if type(data) != list:
            data = [data]
        for value in data:
            data = Utils.n2d(value, size)
            self.uc.mem_write(address, data)
            address += size

    def writeNumber(self, address, number, size):
        data = Utils.n2d(number, size)
        self.uc.mem_write(address, data)

    def writeString(self, address, string):
        self.writeData(address, string, 1)

    def addHook(self, hookFunc):
        self.uc.hook_add(UC_HOOK_CODE, hookFunc, user_data=self)

    def getMaxAddress(self):
        end = 0
        for func in self.binary.Functions:
            if end < func.getMaxAddr():
                end = func.getMaxAddr()
        return end

    def initBeforeRun(self):
        self.uc.hook_add(UC_HOOK_MEM_READ_UNMAPPED | UC_HOOK_MEM_WRITE_UNMAPPED, hook_mem_invalid)

    def getInstrAt(self, address, size=16):
        data = bytes(self.readData(address, size, 1))
        instr = list(self.disassmbler.disasm(data, address))[0]
        return "0x%x: %s %s" % (instr.address, instr.mnemonic, instr.op_str)
