from x86_64 import *


def hook_code(mu, address, size, user_data):
    emulator = user_data
    emulator.lastLogAddress = address
    # print(emulator.getInstrAt(address, size))
    if address == 0x4005bb:
        print(emulator.uc.reg_read(UC_X86_REG_RAX))


fileName = "D:\\Binary\\test"
emulator = EmulatorX64(fileName)
emulator.addHook(hook_code)
emulator.start(0x4005a7, 0x400658)
