module ReachingDefinition

open Domain

let killRD ((var,_): string * State) (a: Domain.Action) =
  match a with
  | S(VarAssign(x,_))
  | S(Read x)
  | D(DVar x)
  | D(DArray(x,_)) -> var = x
  | _ -> false

let genRD ((_,a,s2): Edge) =
  match a with
  | S(VarAssign(x,_))
  | S(ArrayAssign(x,_,_))
  | S(Read x)
  | S(ReadArray(x,_))
  | D(DVar x) 
  | D(DArray(x,_)) -> Set.singleton (x,s2)
  | _ -> Set.empty
