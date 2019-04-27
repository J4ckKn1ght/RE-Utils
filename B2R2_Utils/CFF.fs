module MyUtils.CFF
open B2R2.BinGraph
open B2R2.FrontEnd
open B2R2.FrontEnd.Intel

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

let private getDeadCodeGlatterningVertex (listDeadCode) (vertex:DisasmVertex) =
    let instrs = vertex.VData.Instrs
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

let stateVariableOffset (func : Function) =
    let root = func.DisasmCFG.GetRoot()
    let lastIns = root.VData.LastInstr :?> IntelInstruction
    match lastIns.Info.Operands with
    | TwoOperands(mem, img) ->
        match mem with
        | OprMem(_, _, offset, _) -> offset
        | _ -> None
    | _ -> None

let getCMovInsInVertex (listCMov) (vertex : DisasmVertex) =
    let instrs = vertex.VData.Instrs
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

let getCMovInsList (func : Function) =
    let instrs = func.DisasmCFG.FoldVertex getCMovInsInVertex []
    instrs

let getMainDispatch (func : Function) =
    let root = func.DisasmCFG.GetRoot()
    root.Succs.Head.VData

let getPreDispatch (func : Function) =
    let root = func.DisasmCFG.GetRoot()
    let mainDispatch = root.Succs.Head
    let preDispatch = mainDispatch.Preds
    if preDispatch.Item 0 <> mainDispatch then
        (preDispatch.Item 0)
    else
        (preDispatch.Item 1)

let mainBlockList (func:Function) =
    let preDispatch = getPreDispatch func
    let listMainBlock = preDispatch.Preds
    List.filter (fun (x:Vertex<DisassemblyBBL>) -> (List.length x.VData.Instrs) > 1) listMainBlock

let getDeadCodeInFunc (func:Function) =
    let listDeadCode = []
    let listDeadCode = func.DisasmCFG.FoldVertex getDeadCodeGlatterningVertex listDeadCode
    listDeadCode