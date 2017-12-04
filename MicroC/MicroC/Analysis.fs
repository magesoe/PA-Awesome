module Analysis
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


let doIntervalAnalysis min max program = 
  let _start,_end,pg = getProgramGraph program    
  let nStart, pgMap = getNumberedPGMap _start pg

  let fv = pgMap |> getFV

  let init = 
    fv
    |> Set.fold (fun map x -> 
      Map.add x (Int(NegInfinity, Infinity)) map
      ) Map.empty
  
  let bottomValue =
    fv
    |> Set.fold (fun map x -> 
      Map.add x (Bottom) map
      ) Map.empty

  let isPartOf (m1: Map<'a,IntervalLattice>) (m2: Map<'a,IntervalLattice>) =
    if m1.IsEmpty && (m2.IsEmpty |> not) then false else
    let res = 
      m1
      |> Map.forall (fun x v ->
        match v,m2.[x] with
        | (Bottom,Bottom) -> true
        | (Bottom,_) -> true
        | (Int(_,_), Bottom) -> false
        | (Int(z1, z2), Int(a1, a2)) -> 
          let a1',a2' = unionInterval (z1,z2,a1,a2)
          if a1 = a1' && a2 = a2' then true else false
        
        )
    res

  let combine (m1: Map<string,IntervalLattice>) (m2: Map<string,IntervalLattice>) =
    if m1.IsEmpty then m2 else
    if m2.IsEmpty then m1 else
    
    let res =
      m1
      |> Map.fold (fun map x v ->
        match Map.tryFind x map with
        | Some v' -> 
          let combined =
            match v,m2.[x] with
            | (Bottom,Bottom) -> Bottom
            | (Bottom,x)
            | (x,Bottom) -> x
            | (Int(z1, z2), Int(a1, a2)) -> 
              Int(unionInterval (z1,z2,a1,a2))
          Map.add x combined map
        | None -> Map.add x v map
        ) m2
        
    res
    
  nStart, pgMap, workListAlgo (transferInterval min max) isPartOf combine pgMap [|(O nStart,init)|] bottomValue




let pFact = 
  DSeq(DVar("x"),DVar("y")),
  Seq(VarAssign("y", V 1), 
    Seq(Read "x", 
      Seq(While(Great(Var "x", V 1), Seq(VarAssign("y", Mult(Var "x", Var "y")),VarAssign("x", Sub(Var "x", V 1))
          )), Write(Var "y"))))

let pDoS =
  DSeq(DVar "i",DSeq(DVar "x", DArray("A", V 10))),
  Seq(VarAssign("i", V 0),
    While(Less(Var "i", V 10),
      Seq(Read "x",
        IfElse(Eq(Var "x",V 0),
          Seq(ArrayAssign("A", V 0, Var "x"), VarAssign("i", Add(Var "i", V 1))),
          Continue))))

let pInterval =
  DSeq(DVar "x", DSeq(DVar "y", DVar "z")),
  Seq(VarAssign("y", V 2), 
    Seq(VarAssign("x", V 0),
      Seq(Read "z",
        Seq(While(LessEq(Var "x", V 3), Seq(VarAssign("x", Add(Var "x", V 1)), VarAssign("y", Mult(Var "y", Var "y")))),
          Seq(VarAssign("z", V 0), VarAssign("x", Div(Var "x", Var "z")))))))

let printMap res =
  for x in res do
    printfn "%A" x
