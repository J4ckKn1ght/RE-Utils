
module MyUtils.CFF
open B2R2.BinGraph
open B2R2.FrontEnd
open B2R2.FrontEnd.Intel

let get3Instrs (instrs:Instruction list) =
    let length = instrs.Length - 3
    if length >= 0 then
        [for i = 0 to length do yield (instrs.Item i :?> IntelInstruction,
                                       instrs.Item (i + 1) :?> IntelInstruction,
                                       instrs.Item (i + 2) :?> IntelInstruction)]
    else
        []

let get4Instrs (instrs:Instruction list) =
    let length = instrs.Length - 4
    if length >= 0 then
        [for i = 0 to length do yield (instrs.Item i :?> IntelInstruction,
                                       instrs.Item (i + 1) :?> IntelInstruction,
                                       instrs.Item (i + 2) :?> IntelInstruction,
                                       instrs.Item (i + 3) :?> IntelInstruction)]
    else
        []

let get5Instrs (instrs:Instruction list) =
    let length = instrs.Length - 5
    if length >= 0 then
        [for i = 0 to length do yield (instrs.Item i :?> IntelInstruction,
                                       instrs.Item (i + 1) :?> IntelInstruction,
                                       instrs.Item (i + 2) :?> IntelInstruction,
                                       instrs.Item (i + 3) :?> IntelInstruction,
                                       instrs.Item (i + 4) :?> IntelInstruction)]
    else
        []

let get6Instrs (instrs:Instruction list) =
    let length = instrs.Length - 6
    if length >= 0 then
        [for i = 0 to length do yield (instrs.Item i :?> IntelInstruction,
                                       instrs.Item (i + 1) :?> IntelInstruction,
                                       instrs.Item (i + 2) :?> IntelInstruction,
                                       instrs.Item (i + 3) :?> IntelInstruction,
                                       instrs.Item (i + 4) :?> IntelInstruction,
                                       instrs.Item (i + 5) :?> IntelInstruction)]
    else
        []

let get7Instrs (instrs:Instruction list) =
    let length = instrs.Length - 7
    if length >= 0 then
        [for i = 0 to length do yield (instrs.Item i :?> IntelInstruction,
                                       instrs.Item (i + 1) :?> IntelInstruction,
                                       instrs.Item (i + 2) :?> IntelInstruction,
                                       instrs.Item (i + 3) :?> IntelInstruction,
                                       instrs.Item (i + 4) :?> IntelInstruction,
                                       instrs.Item (i + 5) :?> IntelInstruction,
                                       instrs.Item (i + 6) :?> IntelInstruction)]
    else
        []

let ppOperand (op:Operand) =
    let opStr = op.ToString()
    let space = opStr.IndexOf(' ')
    opStr.Substring(space + 1).Replace("L", "").ToLower()

let private flatteningDecodePattern (ins1:Instruction) (ins2:Instruction) =
  (*
    sub reg1, imm
    mov mem, reg2
    reg1 = reg2
    -> address of mov instruction
  *)
  let intelIns1 = ins1 :?> IntelInstruction
  let intelIns2 = ins2 :?> IntelInstruction
  let info1 = intelIns1.Info
  let info2 = intelIns2.Info
  match (info1.Opcode, info2.Opcode, info1.Operands, info2.Operands) with
  |(Opcode.SUB, Opcode.MOV, TwoOperands(arg1_1, arg1_2), TwoOperands(arg2_1, arg2_2)) ->
      match (arg1_1, arg1_2, arg2_1, arg2_2) with
      | (OprReg(_), OprImm(_), OprMem(_), OprReg(_)) -> if arg1_1 = arg2_2 then Some ins2.Address else None
      | _ -> None
  | _ -> None

let private getDeadCodeGlatterningVertex (listDeadCode) (block:DisasmVertex) =
    let instrs = block.VData.Instrs
    let rec findloop = function
    | [] -> []
    | [ins] -> []
    | ins1::ins2::instrs ->
        let address = flatteningDecodePattern ins1 ins2
        if address.IsNone then
            findloop (ins2::instrs)
        else
            address.Value::(findloop instrs)
    let listDeadCode = listDeadCode @ findloop instrs
    listDeadCode

let stateVariableOffset (cfg:DisasmCFG) =
    let root = cfg.GetRoot()
    let lastIns = root.VData.LastInstr :?> IntelInstruction
    match lastIns.Info.Operands with
    | TwoOperands(mem, img) ->
        match mem with
        | OprMem(_, _, offset, _) -> offset
        | _ -> None
    | _ -> None

let getCMovInsInVertex (listCMov) (block : DisasmVertex) =
    let instrs = block.VData.Instrs
    let rec findCMov (instrs : Instruction list) =
        match instrs with
        | [] -> []
        | instr :: instrs ->
            let intelIns = instr :?> IntelInstruction
            if intelIns.Info.Opcode.ToString().Contains("CMOV") then
                intelIns.Address :: (findCMov instrs)
            else
                findCMov instrs
    let listCMov = listCMov @ (findCMov instrs)
    listCMov

let getCMovInsList (cfg:DisasmCFG) =
    let instrs = cfg.FoldVertex getCMovInsInVertex []
    instrs

let getMainDispatch (cfg:DisasmCFG) =
    let root = cfg.GetRoot()
    root.Succs.Head.VData

let getPreDispatch (cfg:DisasmCFG) =
    let root = cfg.GetRoot()
    let mainDispatch = root.Succs.Head
    let preDispatch = mainDispatch.Preds
    if preDispatch.Item 0 <> mainDispatch then
        (preDispatch.Item 0)
    else
        (preDispatch.Item 1)

let mainBlockList (cfg:DisasmCFG) =
    let preDispatch = getPreDispatch cfg
    let listMainBlock = preDispatch.Preds
    List.filter (fun (x:Vertex<DisassemblyBBL>) -> (List.length x.VData.Instrs) > 1) listMainBlock

let getDeadCodeInFunc (cfg:DisasmCFG) =
    let listDeadCode = []
    let listDeadCode = cfg.FoldVertex getDeadCodeGlatterningVertex listDeadCode
    listDeadCode

let newAsmInfo (dst:Operand, reg1:Operand, reg2:Operand, startIns:Instruction, endIns:Instruction) =
    let address = startIns.Address
    let size = endIns.Address - address + (endIns.Length |> uint64)
    (ppOperand dst, ppOperand reg1, ppOperand reg2, address, size)

let addPattern1 (block:DisasmVertex) =
    (* a = -(-b + (-c))
    mov reg, reg
    sub reg, reg1
    mov reg, reg
    sub reg, reg2
    add reg, reg
    mov reg, reg
    sub dst, reg
    ->
    mov dst, reg1
    add dst, reg2
    *)
    let pattern = fun (ins1:IntelInstruction, ins2:IntelInstruction, ins3:IntelInstruction, ins4:IntelInstruction, ins5:IntelInstruction, ins6:IntelInstruction, ins7:IntelInstruction)
                     ->
                        match (ins1.Info.Opcode, ins2.Info.Opcode, ins3.Info.Opcode, ins4.Info.Opcode, ins5.Info.Opcode, ins6.Info.Opcode, ins7.Info.Opcode) with
                        | (Opcode.MOV, Opcode.SUB, Opcode.MOV, Opcode.SUB, Opcode.ADD, Opcode.MOV, Opcode.SUB) -> true
                        | _ -> false
    let newAsmInfo = fun (ins1:IntelInstruction, ins2:IntelInstruction, _, ins4:IntelInstruction, _, _, ins7:IntelInstruction) ->
                          match (ins2.Info.Operands, ins4.Info.Operands, ins7.Info.Operands) with
                          | (TwoOperands(_, reg1), TwoOperands(_, reg2), TwoOperands(dst, _)) ->
                            let dst, reg1, reg2, address, size = newAsmInfo (dst, reg1, reg2, ins1, ins7)
                            let newAsm = if dst = reg1 then
                                            "add " + reg1 + ", " + reg2
                                          elif dst = reg2 then
                                            "add " + reg2 + ", " + reg1
                                          else
                                            "mov " + dst + ", " + reg1 + "\nadd " + dst + ", " + reg2
                            (address, size, newAsm)
                          | _ -> (0UL, 0UL, "")
    let checkset = get7Instrs block.VData.Instrs
    if checkset.Length = 0 then
      []
    else
      let checkset = List.filter pattern checkset
      List.map newAsmInfo checkset

let addPattern2 (block:DisasmVertex) =
    (* a = -(-b + (-c))
    mov reg, reg
    sub reg, reg1
    mov reg, reg
    sub reg, reg2
    add reg, reg
    sub dst, reg
    ->
    mov dst, reg1
    add dst, reg2
    *)
    let pattern = fun (ins1:IntelInstruction, ins2:IntelInstruction, ins3:IntelInstruction, ins4:IntelInstruction, ins5:IntelInstruction, ins6:IntelInstruction)
                     ->
                        match (ins1.Info.Opcode, ins2.Info.Opcode, ins3.Info.Opcode, ins4.Info.Opcode, ins5.Info.Opcode, ins6.Info.Opcode) with
                        | (Opcode.MOV, Opcode.SUB, Opcode.MOV, Opcode.SUB, Opcode.ADD, Opcode.SUB) -> true
                        | _ -> false
    let newAsmInfo = fun (ins1:IntelInstruction, ins2:IntelInstruction, _, ins4:IntelInstruction, _, ins6:IntelInstruction) ->
                          match (ins2.Info.Operands, ins4.Info.Operands, ins6.Info.Operands) with
                          | (TwoOperands(_, reg1), TwoOperands(_, reg2), TwoOperands(dst, _)) ->
                            let dst, reg1, reg2, address, size = newAsmInfo (dst, reg1, reg2, ins1, ins6)
                            let newAsm = "mov " + dst + ", " + reg1 + "\nadd " + dst + ", " + reg2
                            (address, size, newAsm)
                          | _ -> (0UL, 0UL, "")
    let checkset = get6Instrs block.VData.Instrs
    if checkset.Length = 0 then
      []
    else
      let checkset = List.filter pattern checkset
      List.map newAsmInfo checkset

let addPattern3 (block:DisasmVertex) =
    (* a = b + r; a = a + c; a = a - r
    mov reg, imm
    add reg, reg
    add reg1, reg2
    mov reg, imm
    sub dst, reg
    ->
    add reg1, reg2
    *)

    let pattern = fun (ins1:IntelInstruction, ins2:IntelInstruction, ins3:IntelInstruction, ins4:IntelInstruction, ins5:IntelInstruction)
                     ->
                        match (ins1.Info.Opcode, ins2.Info.Opcode, ins3.Info.Opcode, ins4.Info.Opcode, ins5.Info.Opcode) with
                        | (Opcode.MOV, Opcode.ADD, Opcode.ADD, Opcode.MOV, Opcode.SUB) -> true
                        | _ -> false
    let newAsmInfo = fun (ins1:IntelInstruction, _, ins3:IntelInstruction, _, ins5:IntelInstruction) ->
                          let address = ins1.Address
                          let size = ins5.Address - address + (ins5.Length |> uint64)
                          (address, size, ins3.Disasm())
    let checkset = get5Instrs block.VData.Instrs
    if checkset.Length = 0 then
      []
    else
      let checkset = List.filter pattern checkset
      List.map newAsmInfo checkset

let addPattern4 (block:DisasmVertex) =
    (* a = b - r; a = a + c; a = a + r
    mov reg, imm
    sub reg, reg
    add reg1, reg2
    mov reg, imm
    add dst, reg
    ->
    add reg1, reg2
    *)
    let pattern = fun (ins1:IntelInstruction, ins2:IntelInstruction, ins3:IntelInstruction, ins4:IntelInstruction, ins5:IntelInstruction)
                     ->
                        match (ins1.Info.Opcode, ins2.Info.Opcode, ins3.Info.Opcode, ins4.Info.Opcode, ins5.Info.Opcode) with
                        | (Opcode.MOV, Opcode.SUB, Opcode.ADD, Opcode.MOV, Opcode.ADD) -> true
                        | _ -> false
    let newAsmInfo = fun (ins1:IntelInstruction, _, ins3:IntelInstruction, _, ins5:IntelInstruction) ->
                          let address = ins1.Address
                          let size = ins5.Address - address + (ins5.Length |> uint64)
                          (address, size, ins3.Disasm())
    let checkset = get5Instrs block.VData.Instrs
    if checkset.Length = 0 then
      []
    else
      let checkset = List.filter pattern checkset
      List.map newAsmInfo checkset

let addPattern5 (block:DisasmVertex) =
    (*
    mov reg, reg
    sub reg, reg1
    sub reg2, reg
    ->
    add reg2, reg1
    *)
    let pattern = fun (ins1:IntelInstruction, ins2:IntelInstruction, ins3:IntelInstruction)
                     ->
                        match (ins1.Info.Opcode, ins2.Info.Opcode, ins3.Info.Opcode) with
                        | (Opcode.MOV, Opcode.SUB, Opcode.SUB) ->
                            match (ins1.Info.Operands, ins2.Info.Operands, ins3.Info.Operands) with
                            | (TwoOperands(regT1, reg0), TwoOperands(regT2, reg1), TwoOperands(reg2, regT3))
                                -> if (regT1 = regT2) && (regT2 = regT3) then
                                       true
                                   else
                                       false
                            | _ -> false
                        | _ -> false
    let newAsmInfo = fun (ins1:IntelInstruction, ins2:IntelInstruction, ins3:IntelInstruction) ->
                          match (ins2.Info.Operands, ins3.Info.Operands) with
                          | (TwoOperands(_, reg1), TwoOperands(reg2, _)) ->
                            let dst, reg1, reg2, address, size = newAsmInfo (reg2, reg1, reg2, ins1, ins3)
                            (address, size, "add " + reg2 + ", " + reg1)
                          | _ -> (0UL, 0UL, "")
    let checkset = get3Instrs block.VData.Instrs
    if checkset.Length = 0 then
      []
    else
      let checkset = List.filter pattern checkset
      List.map newAsmInfo checkset

let subPattern1 (block:DisasmVertex) =
    (* a = b + r; a = a - c; a = a - r
    mov reg, imm
    add reg, reg
    sub reg1, reg2
    mov reg, imm
    sub reg, reg
    ->
    sub reg1, reg2
    *)
    let pattern = fun (ins1:IntelInstruction, ins2:IntelInstruction, ins3:IntelInstruction, ins4:IntelInstruction, ins5:IntelInstruction)
                     ->
                        match (ins1.Info.Opcode, ins2.Info.Opcode, ins3.Info.Opcode, ins4.Info.Opcode, ins5.Info.Opcode) with
                        | (Opcode.MOV, Opcode.ADD, Opcode.SUB, Opcode.MOV, Opcode.SUB) -> true
                        | _ -> false

    let newAsmInfo = fun (ins1:IntelInstruction, _ , ins3:IntelInstruction, _, ins5:IntelInstruction) ->
                         let address = ins1.Address
                         let size = ins5.Address - address + (ins5.Length |> uint64)
                         let newAsm = ins3.Disasm()
                         (address, size, newAsm)
    let checkset = get5Instrs block.VData.Instrs
    if checkset.Length = 0 then
      []
    else
      let checkset = List.filter pattern checkset
      List.map newAsmInfo checkset

let subPattern2 (block:DisasmVertex) =
    (* a = b - r; a = a - c; a = a + r
    mov reg, imm
    sub reg, reg
    sub reg1, reg2
    mov reg, imm
    add reg, reg
    ->
    sub reg1, reg2
    *)
    let pattern = fun (ins1:IntelInstruction, ins2:IntelInstruction, ins3:IntelInstruction, ins4:IntelInstruction, ins5:IntelInstruction)
                     ->
                        match (ins1.Info.Opcode, ins2.Info.Opcode, ins3.Info.Opcode, ins4.Info.Opcode, ins5.Info.Opcode) with
                        | (Opcode.MOV, Opcode.SUB, Opcode.SUB, Opcode.MOV, Opcode.ADD) -> true
                        | _ -> false
    let newAsmInfo = fun (ins1:IntelInstruction, _ , ins3:IntelInstruction, _, ins5:IntelInstruction) ->
                          let address = ins1.Address
                          let size = ins5.Address - address + (ins5.Length |> uint64)
                          let newAsm = ins3.Disasm()
                          (address, size, newAsm)
    let checkset = get5Instrs block.VData.Instrs
    if checkset.Length = 0 then
      []
    else
      let checkset = List.filter pattern checkset
      List.map newAsmInfo checkset


let orPattern (block:DisasmVertex) =
    (*
    mov reg, reg1
    and reg, reg
    xor reg, reg2
    or dst, reg
    ->
    mov dst, reg1
    or dst, reg2
    *)
    let pattern = fun (ins1:IntelInstruction, ins2:IntelInstruction, ins3:IntelInstruction, ins4:IntelInstruction)
                     ->
                        match (ins1.Info.Opcode, ins2.Info.Opcode, ins3.Info.Opcode, ins4.Info.Opcode) with
                        | (Opcode.MOV, Opcode.AND, Opcode.XOR, Opcode.OR) -> true
                        | _ -> false
    let newAsmInfo = fun (ins1:IntelInstruction, ins2:IntelInstruction, ins3:IntelInstruction, ins4:IntelInstruction) ->
                          match (ins1.Info.Operands, ins3.Info.Operands, ins4.Info.Operands) with
                          | (TwoOperands(_, reg1), TwoOperands(_, reg2), TwoOperands(dst, _)) ->
                            let dst, reg1, reg2, address, size = newAsmInfo (dst, reg1, reg2, ins2, ins4)
                            (address, size, "mov " + dst + ", " + reg1 + "\nor " + dst + ", " + reg2)
                          | _ -> (0UL, 0UL, "")
    let checkset = get4Instrs block.VData.Instrs
    if checkset.Length = 0 then
      []
    else
      let checkset = List.filter pattern checkset
      List.map newAsmInfo checkset

let xorPattern (block:DisasmVertex) =
    (*
    mov reg, reg1
    xor reg, imm
    mov reg, reg2
    and reg, reg
    xor reg, imm
    and reg, reg
    or dst, reg
    ->
    mov dst, reg1
    xor dst, reg2
    *)
    let pattern = fun (ins1:IntelInstruction, ins2:IntelInstruction, ins3:IntelInstruction, ins4:IntelInstruction, ins5:IntelInstruction, ins6:IntelInstruction, ins7:IntelInstruction)
                     ->
                        match (ins1.Info.Opcode, ins2.Info.Opcode, ins3.Info.Opcode, ins4.Info.Opcode, ins5.Info.Opcode, ins6.Info.Opcode, ins7.Info.Opcode) with
                        | (Opcode.MOV, Opcode.XOR, Opcode.MOV, Opcode.AND, Opcode.XOR, Opcode.AND, Opcode.OR) -> true
                        | _ -> false
    let newAsmInfo = fun (ins1:IntelInstruction, _, ins3:IntelInstruction, _, _, _, ins7:IntelInstruction) ->
                          match (ins1.Info.Operands, ins3.Info.Operands, ins7.Info.Operands) with
                          | (TwoOperands(_, reg1), TwoOperands(_, reg2), TwoOperands(dst, _)) ->
                            let dst, reg1, reg2, address, size = newAsmInfo (dst, reg1, reg2, ins1, ins7)
                            let newAsm = "mov " + dst + ", " + reg1 + "\nxor " + dst + ", " + reg2
                            (address, size, newAsm)
                          | _ -> (0UL, 0UL, "")
    let checkset = get7Instrs block.VData.Instrs
    if checkset.Length = 0 then
      []
    else
      let checkset = List.filter pattern checkset
      List.map newAsmInfo checkset

let notPattern (block:DisasmVertex) =
    (*
    mov reg, reg1
    xor reg, imm
    and reg, imm
    xor reg, imm
    and reg, reg
    or dst, reg
    ->
    xor reg1, 0xFFFFFFFFFFFFFFFF
    mov dst, reg1
    *)
    let pattern = fun (ins1:IntelInstruction, ins2:IntelInstruction, ins3:IntelInstruction, ins4:IntelInstruction, ins5:IntelInstruction, ins6:IntelInstruction)
                     ->
                        match (ins1.Info.Opcode, ins2.Info.Opcode, ins3.Info.Opcode, ins4.Info.Opcode, ins5.Info.Opcode, ins6.Info.Opcode) with
                        | (Opcode.MOV, Opcode.XOR, Opcode.AND, Opcode.XOR, Opcode.AND, Opcode.OR) -> true
                        | _ -> false
    let newAsmInfo = fun (ins1:IntelInstruction, _, _, _, _, ins6:IntelInstruction) ->
                            match (ins1.Info.Operands, ins6.Info.Operands) with
                            | (TwoOperands(_, reg1), TwoOperands(dst, _)) ->
                                let reg1 = ppOperand reg1
                                let dst = ppOperand dst
                                let newAsm = "xor " + reg1 + ", 0xFFFFFFFFFFFFFFFF" +   "\nmov " + dst + ", " + reg1
                                let address = ins1.Address
                                let size = ins6.Address - address + (ins1.Length |> uint64)
                                (address, size, newAsm)
                            | _ -> (0UL, 0UL, "")
    let checkset = get6Instrs block.VData.Instrs
    if checkset.Length = 0 then
        []
    else
        let checkset = List.filter pattern checkset
        List.map newAsmInfo checkset