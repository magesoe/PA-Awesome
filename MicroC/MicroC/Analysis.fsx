#load "Domain.fsx"
#load "AnalysisStructures.fsx"
open Domain
open System
open ProgramGraph
open WorklistAlgo
open AnalysisStructures
open System.Dynamic

let doRDAnalysis program = 
  let _start,_end,pg = getProgramGraph program    
  let nStart, pgMap = getNumberedPGMap _start pg
  let init = 
    pgMap
    |> getFV
    |> Set.map (fun x -> (x, Undefined))

  nStart, pgMap, workListAlgo (transferBit killRD genRD) Set.isSubset Set.union pgMap [|(O nStart, init)|] Set.empty

let doLVAnalysis program = 
  let _start,_end,pg = getProgramGraph program    
  let nStart, pgMap = getNumberedPGMap _start pg
  let init = 
    pgMap
    |> getFinalStates
    |> Set.map (fun s -> s,Set.empty)
    |> Set.toArray

  nStart, pgMap, workListAlgo (transferBit killLV genLV) Set.isSubset Set.union (reversePgMap pgMap) init Set.empty

let doDetectSignsAnalysis program = 
  let _start,_end,pg = getProgramGraph program    
  let nStart, pgMap = getNumberedPGMap _start pg

  let fv = pgMap |> getFV

  let init = 
    fv
    |> Set.fold (fun map x -> 
      Map.add x (Set.ofArray [|Positive;Negative;Zero|]) map
      ) Map.empty
  
  let bottomValue =
    fv
    |> Set.fold (fun map x -> 
      Map.add x (Set.empty) map
      ) Map.empty

  let isPartOf (m1: Map<'a,Set<'b>>) (m2: Map<'a,Set<'b>>) =
    if m1.IsEmpty && (m2.IsEmpty |> not) then false else
    let res = 
      m1
      |> Map.forall (fun x v ->
        let m2' = m2.[x]
        if v.IsEmpty && (m2'.IsEmpty |> not) then false else
        v
        |> Set.forall (fun s ->
          Set.contains s m2' 
          )
        )
    printfn "partOf %A\n %A\n %A\n" m1 m2 res
    res

  let combine (m1: Map<string,Set<SignsLattice>>) (m2: Map<string,Set<SignsLattice>>) =
    if m1.IsEmpty then m2 else
    if m2.IsEmpty then m1 else
    
    let res =
      m1
      |> Map.fold (fun map x v ->
        match Map.tryFind x map with
        | Some v' -> Map.add x (Set.union v v') map
        | None -> Map.add x v map
        ) m2
        
    res
    
  nStart, pgMap, workListAlgo transferSigns isPartOf combine pgMap [|(O nStart,init)|] bottomValue

let program = 
  DSeq(DVar("x"),DVar("y")),
  Seq(VarAssign("y", V 1), 
    Seq(Read "x", 
      Seq(While(Great(Var "x", V 1), Seq(VarAssign("y", Mult(Var "x", Var "y")),VarAssign("x", Sub(Var "x", V 1))
          )), Write(Var "y"))))



//doRDAnalysis program
//doLVAnalysis program
//doDetectSignsAnalysis program

