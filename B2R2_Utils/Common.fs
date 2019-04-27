namespace MyUtils


module Common =

  open System.Text
  open B2R2.FrontEnd
  open B2R2
  open B2R2.BinGraph
  open B2R2.BinIR.LowUIR


  let getHandler (binaryFile:string) =
    BinHandler.Init (ISA.DefaultISA, ArchOperationMode.NoMode, true, 0UL, binaryFile)

  let getBinEssence (handler:BinHandler) =
    BinEssence.Init false handler

  let getAllFunction (binEssence:BinEssence) =
    binEssence.Functions.Values |> List.ofSeq

  let private disasmIns hdl (disasm: StringBuilder) ins =
    let insStr = BinHandler.DisasmInstr hdl true true ins
    disasm.Append(insStr)

  let private disasmVertex (disasm:StringBuilder, hdl) (vertex:DisasmVertex) =
    let instrs = vertex.VData.Instrs
    let disasm = disasm.Append("loc_" + vertex.VData.AddrRange.Min.ToString ("X") + ":").Append("\n")
    let rec disasmLoop sb = function
    | [] -> sb
    | [ins] -> disasmIns hdl sb ins
    | ins :: instrs ->
      disasmLoop ((disasmIns hdl sb ins).Append("\n")) instrs
    let disasm = disasmLoop disasm instrs
    disasm.Append("\n\n"), hdl

  let disasmFunc (func:Function) (handler:BinHandler) =
    let disasm = StringBuilder()
    let disasm, _ = func.DisasmCFG.FoldVertex disasmVertex (disasm, handler)
    disasm.ToString()

  let private liftStmt (ir:StringBuilder) stmt =
    let irStr = Pp.stmtToString stmt
    ir.Append(irStr)

  let private liftVertex (ir:StringBuilder) (vertex:IRVertex) =
    let stmts = List.toArray vertex.VData.Stmts |> LocalOptimizer.Optimize |> Array.toList
    let address, _ = vertex.VData.Ppoint
    let ir = ir.Append("loc_" + address.ToString ("X") + ":\n")
    let rec irLoop ir = function
    | [] -> ir
    | [stmt] -> liftStmt ir stmt
    | stmt :: stmts ->
      irLoop ((liftStmt ir stmt).Append("\n")) stmts
    let ir = irLoop ir stmts
    ir.Append("\n\n")

  let liftFunc (func:Function) =
    let ir = StringBuilder()
    let ir = func.IRCFG.FoldVertex liftVertex ir
    ir.ToString()

  let getFunctionAt (address:Addr) (binEssence:BinEssence) =
    binEssence.Functions.Item address

  let private deadCodePattern stmt1 stmt2 =
    match (stmt1, stmt2) with
    | (ISMark(address, length), IEMark(addres2)) -> Some address
    | _ -> None

  let private getDeadCodeBlock (listDeadCode) (block:IRVertex) =
    let stmts = List.toArray block.VData.Stmts |> LocalOptimizer.Optimize |> Array.toList
    let len = List.length stmts
    let rec findDeadCodeLoop = function
    | [] -> []
    | [stmt] -> []
    | stmt1::stmt2::stmts ->
        let address = (deadCodePattern stmt1 stmt2)
        if address.IsSome then
            address.Value::(findDeadCodeLoop (stmt2::stmts))
        else
            findDeadCodeLoop stmts
    let listDeadCode = listDeadCode @ (findDeadCodeLoop stmts)
    listDeadCode

  let getDeadCodeInFunc (func:Function) =
    let listDeadCode = []
    let listDeadCode = func.IRCFG.FoldVertex getDeadCodeBlock listDeadCode
    listDeadCode