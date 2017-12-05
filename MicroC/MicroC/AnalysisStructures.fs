module AnalysisStructures
open Domain

let transferBit kill gen (current: Set<'a>) ((s1,a,s2): Edge) =
  current
  |> Set.filter (fun x -> (kill x a) |> not)
  |> Set.union (gen (s1,a,s2))
