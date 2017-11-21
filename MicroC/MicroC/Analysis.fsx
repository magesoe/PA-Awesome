#load "Domain.fsx"
#load "ProgramGraph.fsx"
#load "WorklistAlgo.fsx"
open Domain
open System
open ProgramGraph
open WorklistAlgo
open System.Dynamic

let transferBit kill gen (current: Set<'a>) ((s1,a,s2): Edge) =
  current
  |> Set.filter (fun x -> (kill x a) |> not)
  |> Set.union (gen (s1,a,s2))

let killRD ((var,_): string * State) (a: Domain.Action) =
  match a with
  | S(VarAssign(x,_))
  | S(Read x) -> var = x
  | _ -> false

let genRD ((_,a,s2): Edge) =
  match a with
  | S(VarAssign(x,_))
  | S(ArrayAssign(x,_,_))
  | S(Read x) -> Set.singleton (x,s2)
  | _ -> Set.empty

let doRDAnalysis program = 
  let _start,_end,pg = getProgramGraph program    
  let nStart, pgMap = getNumberedPGMap _start pg
  let init = 
    pgMap
    |> getFV
    |> Set.map (fun x -> (x, Undefined))

  nStart, pgMap, workListAlgo (transferBit killRD genRD) Set.isSubset pgMap [|(O nStart, init)|]

let killLV (var: string) (a: Domain.Action) =
  match a with
  | S(VarAssign(x,_))
  | S(Read x)
  | D(DVar x)
  | D(DArray (x,_)) -> var = x
  | _ -> false

let genLV ((_,a,s2): Edge) =
  match a with
  | S(VarAssign(_,aexp))
  | S(ArrayAssign(_,aexp,_))
  | S(Write aexp)
  | A aexp -> getFVA aexp
  | S(If(bexp,_))
  | S(IfElse(bexp,_,_))
  | S(While(bexp,_))
  | B bexp -> getFVB bexp
  | _ -> Set.empty


let doLVAnalysis program = 
  let _start,_end,pg = getProgramGraph program    
  let nStart, pgMap = getNumberedPGMap _start pg
  let init = 
    pgMap
    |> getFinalStates
    |> Set.map (fun s -> s,Set.empty)
    |> Set.toArray

  nStart, pgMap, workListAlgo (transferBit killLV genLV) Set.isSubset (reversePgMap pgMap) init

//doRDAnalysis program



doLVAnalysis program

