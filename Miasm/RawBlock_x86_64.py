from miasm.analysis.binary import Container
from miasm.analysis.machine import Machine
from miasm.analysis.simplifier import IRCFGSimplifierSSA, IRCFGSimplifierCommon
from miasm.arch.x86.ira import ir_a_x86_64 as ira
from future.utils import viewitems, viewvalues
from miasm.ir.ir import AssignBlock, IRBlock


def is_addr_ro_variable(bs, addr, size):
    try:
        _ = bs.getbytes(addr, size // 8)
    except IOError:
        return False
    return True


class IRADelModCallStack(ira):

    def call_effects(self, addr, instr):
        assignblks, extra = super(IRADelModCallStack, self).call_effects(addr, instr)
        out = []
        for assignblk in assignblks:
            dct = dict(assignblk)
            dct = {
                dst: src for (dst, src) in viewitems(dct) if dst != self.sp
            }
            out.append(AssignBlock(dct, assignblk.instr))
        return out, extra


class IRAOutRegs(ira):
    def get_out_regs(self, block):
        regs_todo = super(self.__class__, self).get_out_regs(block)
        out = {}
        for assignblk in block:
            for dst in assignblk:
                reg = self.ssa_var.get(dst, None)
                if reg is None:
                    continue
                if reg in regs_todo:
                    out[reg] = dst
        return set(viewvalues(out))


class CustomIRCFGSimplifierSSA(IRCFGSimplifierSSA):
    def do_simplify(self, ssa, head):
        super(CustomIRCFGSimplifierSSA, self).do_simplify(ssa, head)

    def simplify(self, ircfg, head):
        ssa = self.ircfg_to_ssa(ircfg, head)
        ssa = self.do_simplify_loop(ssa, head)
        ircfg = self.ssa_to_unssa(ssa, head)
        ircfg_simplifier = IRCFGSimplifierCommon(self.ir_arch)
        ircfg_simplifier.simplify(ircfg, head)
        return ircfg


class Block:
    def __init__(self, raw, address):
        self.cont = Container.fallback_container(raw + b'\xC3', vm=None, addr=address)
        self.address = address
        self.machine = Machine('x86_64')
        self.mdis = self.machine.dis_engine(self.cont.bin_stream, loc_db = self.cont.loc_db)
        self.asmcfg = self.mdis.dis_multiblock(self.address)
        self.head = self.asmcfg.getby_offset(self.address).loc_key
        self.orignal_ira = self.machine.ira(self.mdis.loc_db)
        self.orginal_ircfg = self.orignal_ira.new_ircfg_from_asmcfg(self.asmcfg)
        self.common_simplifier = IRCFGSimplifierCommon(self.orignal_ira)
        self.common_simplifier.simplify(self.orginal_ircfg, self.head)
        self.custom_ira1 = IRADelModCallStack(self.mdis.loc_db)
        self.custom_ira2 = IRAOutRegs(self.mdis.loc_db)
        self.ircfg = self.custom_ira1.new_ircfg_from_asmcfg(self.asmcfg)
        self.simplify()

    def simplify(self):
        simplifier = IRCFGSimplifierCommon(self.custom_ira1)
        simplifier.simplify(self.ircfg, self.head)
        for loc in self.ircfg.leaves():
            irblock = self.ircfg.blocks.get(loc)
            if irblock is None:
                continue
            regs = {}
            for reg in self.custom_ira1.get_out_regs(irblock):
                regs[reg] = reg
            assignblks = list(irblock)
            newAssignBlk = AssignBlock(regs, assignblks[-1].instr)
            assignblks.append(newAssignBlk)
            newIrBlock = IRBlock(irblock.loc_key, assignblks)
            self.ircfg.blocks[loc] = newIrBlock
        simplifier = CustomIRCFGSimplifierSSA(self.custom_ira2)
        simplifier.simplify(self.ircfg, self.head)

