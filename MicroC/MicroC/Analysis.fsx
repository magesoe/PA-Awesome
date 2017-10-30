#load "Domain.fsx"
#load "ProgramGraph.fsx"
open Domain
open System
open ProgramGraph
open System.Dynamic

let getAssigns (assigns: Map<string,Set<(string * Guid)>>) (x: string) =
  match Map.tryFind x assigns with
  | Some xs -> xs.Add(x,Guid.Empty)
  | None -> failwith "Assignment is found, but is not in map of assigns"

let killRD (var: string) (a: Domain.Action) =
  match a with
  | S(VarAssign(x,_))
  | S(Read x) -> var = x
  | _ -> false

let genRD ((_,a,s2): Edge) =
  match a with
  | S(VarAssign(x,_))
  | S(ArrayAssign(x,_))
  | S(Read x) -> Set.singleton (x,s2)
  | _ -> Set.empty

let isPartOfRD = Set.isSubset
let combineResRD = Set.union
let transferRD (current: Set<string * State>) ((s1,a,s2): Edge) =
  current
  |> Set.filter (fun (var,_) -> (killRD var a) |> not)
  |> Set.union (genRD (s1,a,s2))

let workListAlgo transfer isPartOf combineRes (pgMap: ProgramGraphMap) (initial: (State * Set<'a>)[]) =
  let rec workListAlgo' (transfer: Set<'a> -> Edge -> Set<'a>) (isPartOf: Set<'a> -> Set<'a> -> bool) 
    (combineRes: Set<'a> -> Set<'a> -> Set<'a>) (pgMap: ProgramGraphMap)
    (w: Edge list) (res: Map<State, Set<'a>>) =
    if w.IsEmpty then res else
    let s1,a,s2 = w.Head
    let fromRes = res.[s1]
    let toRes = res.[s2]
    let transferRes = transfer fromRes w.Head
    match isPartOf transferRes toRes with
    | true -> workListAlgo' transfer isPartOf combineRes pgMap w.Tail res
    | false ->
      let newRes =
        res
        |> Map.add s2 (combineRes toRes transferRes)
      let newEdges = 
        if pgMap.ContainsKey s2 |> not then w.Tail else
        pgMap.[s2]
        |> List.fold (fun es (a',s') -> (s2, a', s') :: es) w.Tail
      workListAlgo' transfer isPartOf combineRes pgMap newEdges newRes

  let res = 
    initial
    |> Array.fold (fun map (s,v) -> Map.add s v map) 
      (pgMap |> Map.fold (fun map s1 v ->
        v
        |> List.fold (fun map' (_,s2) -> Map.add s2 Set.empty map')
          (Map.add s1 Set.empty map)
        ) Map.empty)

  let w =
    pgMap
    |> Map.fold (fun w' s1 edges ->
      edges
      |> List.fold (fun edges' (a, s2) ->
        (s1,a,s2) :: edges') w'
      ) []
  workListAlgo' transfer isPartOf combineRes pgMap w res
  
let _start,_end,pg = getProgramGraph program    
let pgMap = getOrderedPGMap _start pg
let init = 
  pgMap
  |> getFV
  |> Set.map (fun x -> (x, Ordered Undefined))

workListAlgo transferRD isPartOfRD combineResRD pgMap [|(Ordered (OV 0), init)|]