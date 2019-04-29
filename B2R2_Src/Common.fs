namespace MyUtils


module Common =

  open System.Text
  open B2R2.FrontEnd
  open B2R2
  open B2R2.BinGraph
  open B2R2.BinIR.LowUIR


  type Func(func:Function, handler:BinHandler) =
    let getBlock (blocks) (block) =
        blocks @ [block]

    let deadCodePattern stmt1 stmt2 =
        match (stmt1, stmt2) with
        | (ISMark(address, length), IEMark(addres2)) -> Some address
        | _ -> None

    let getDeadCodeBlock (listDeadCode) (block:IRVertex) =
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

    member this.address = func.Entry
    member this.disasmCFG = func.DisasmCFG
    member this.name = func.Name
    member this.irCFG = func.IRCFG
    member this.ssaCFG = func.SSACFG
    member this.handler = handler

    member this.disasmIns (ins:Instruction) =
        BinHandler.DisasmInstr this.handler true true ins

    member this.liftStmt (stmt:Stmt) =
        Pp.stmtToString stmt

    member this.disasmBlock (block:DisasmVertex) =
        let instrs = block.VData.Instrs
        let disasm = "loc_" + block.VData.AddrRange.Min.ToString ("X") + ":\n"
        let rec disasmLoop = function
        | [] -> ""
        | [ins] -> this.disasmIns(ins)
        | ins :: instrs -> this.disasmIns(ins) + "\n" + disasmLoop instrs
        let disasm = disasm + disasmLoop instrs
        disasm

    member this.liftBlock (block:IRVertex) =
        let stmts = List.toArray block.VData.Stmts |> LocalOptimizer.Optimize |> Array.toList
        let stmts = List.filter (fun stmt -> match stmt with
                                             | IEMark(_) -> false
                                             | ISMark(_) -> false
                                             | _ -> true) stmts
        let address, _ = block.VData.Ppoint
        let ir = "loc_" + address.ToString ("X") + ":\n"
        let rec liftLoop = function
        | [] -> ""
        | [stmt] -> this.liftStmt stmt
        | stmt :: stmts -> this.liftStmt stmt + "\n" + liftLoop stmts
        let ir = ir + liftLoop stmts
        ir

    member this.asmBlocks=
        this.disasmCFG.FoldVertex getBlock ([])

    member this.irBlocks =
        this.irCFG.FoldVertex getBlock ([])

    member this.getDeadCode =
        this.irCFG.FoldVertex getDeadCodeBlock []

    member this.getMaxAddr =
        let blocks = this.asmBlocks
        let max = [for block in blocks do yield block.VData.AddrRange.Max] |> List.max
        max

    member this.dumpFunc =
        let maxAddress = this.getMaxAddr
        let minAddress = this.address
        let size = maxAddress - minAddress |> int
        this.handler.ReadBytes(minAddress, size)

    member this.dumpBlockAt (address:Addr) =
        let block = List.find (fun (block:DisasmVertex) -> block.VData.AddrRange.Min = address) this.asmBlocks
        let size = block.VData.AddrRange.Max - block.VData.AddrRange.Min |> uint32
        let size = size - block.VData.LastInstr.Length |> int
        this.handler.ReadBytes(block.VData.AddrRange.Min , size)


  type Binary(fileName:string) =
    member this.fileName = fileName
    member this.handler = BinHandler.Init(ISA.DefaultISA, ArchOperationMode.NoMode, true, 0UL, fileName)
    member this.essence = BinEssence.Init false this.handler
    member this.functions = this.essence.Functions.Values |> List.ofSeq |> List.map (fun (func:Function) -> Func(func, this.handler))

    member this.getFuncAt (address:Addr) =
        List.find (fun (func:Func) -> func.address = address) this.functions
