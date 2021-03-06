from Emulator import Emulator
from unicorn import *
from unicorn.x86_const import *
from keystone import *
from capstone import *
import logging
import random


class EmulatorX64(Emulator):
    def __init__(self, fileName):
        super(EmulatorX64, self).__init__(fileName)
        self.uc = Uc(UC_ARCH_X86, UC_MODE_64)
        self.disassmbler = Cs(CS_ARCH_X86, CS_MODE_64)
        self.assembler = Ks(KS_ARCH_X86, KS_MODE_64)
        self.initMemory()

    def initMemory(self):
        segments = list(self.binary.segments())
        for seg in segments:
            address = seg.Address
            size = seg.Size
            data = bytes(self.binary.readData(address, size))
            if address % 0x1000 != 0:
                address = address & (~0xfff)
            if size % 0x100 != 0:
                size = (size & ~0xfff) + (0x1000)
            print("[Info] Map at 0x%x with size 0x%x" % (address, size))
            self.uc.mem_map(address, size)
            self.uc.mem_write(address, data)

        stackStart = 0x7ffffffde000
        stackSize = 0x21000
        self.uc.mem_map(stackStart - stackSize, stackSize)
        stackMiddle = stackStart - stackSize // 2
        self.uc.reg_write(UC_X86_REG_RSP, stackMiddle)
        self.uc.reg_write(UC_X86_REG_RBP, stackMiddle)
        self.uc.reg_write(UC_X86_REG_RIP, self.binary.FileInfo.EntryPoint)

        #Init canary
        try:
            self.uc.mem_map(0, 0x1000)
        except:
            pass
        canary = random.randrange(0, 2**64 -1)
        self.writeData(0x28, canary, 8)

    def start(self, address=None, end=None):
        self.initBeforeRun()
        if address != None and end == None:
            end = self.getMaxAddress()
        elif address == None and end == None:
            address = self.binary.FileInfo.EntryPoint
            end = self.getMaxAddress()
        try:
            self.lastLogAddress = address
            self.uc.emu_start(address, end)
        except UcError as ucError:
            if ucError.errno == UC_ERR_FETCH_UNMAPPED:
                print("[Error] Memory UNMAPPED")
                print("[Info] Emulator Stopped!!")
            else:
                print("[Error] " + str(ucError))