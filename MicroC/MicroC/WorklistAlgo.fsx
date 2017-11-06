#load "Domain.fsx"
#load "ProgramGraph.fsx"
open Domain
open ProgramGraph

let workListAlgo transfer isPartOf combineRes pgMap initial =
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
