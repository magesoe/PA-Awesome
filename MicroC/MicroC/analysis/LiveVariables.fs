module LiveVariables
open Domain
open ProgramGraph

let killLV (var: string) (a: Domain.Action) =
  match a with
  | S(VarAssign(x,_))
  | S(Read x)
  | D(DVar x)
  | D(DArray(x,_)) -> var = x
  | _ -> false

let genLV ((_,a,s2): Edge) =
  match a with
  | S(VarAssign(_,aexp))
  | S(ReadArray(_,aexp))
  | S(Write aexp) -> getFVA aexp
  | S(ArrayAssign(_,iexp,aexp)) -> Set.union (getFVA iexp) (getFVA aexp)
  | B bexp -> getFVB bexp
  | _ -> Set.empty