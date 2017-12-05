module Domain
open System
type Declaration = 
  DVar of string 
  | DArray of string * AExp
  | DEmpty 
  | DSeq of Declaration * Declaration
and BExp = 
  BV of bool 
  | Less of AExp * AExp
  | LessEq of AExp * AExp
  | Great of AExp * AExp
  | GreatEq of AExp * AExp
  | Eq of AExp * AExp
  | NotEq of AExp * AExp
  | And of BExp * BExp
  | Or of BExp * BExp
  | Neg of BExp

and AExp =
  V of int
  | Var of string
  | Array of string * AExp
  | Add of AExp * AExp
  | Sub of AExp * AExp
  | Mult of AExp * AExp
  | Div of AExp * AExp

type Statement =
  VarAssign of string * AExp
  | ArrayAssign of string * AExp * AExp
  | Seq of Statement * Statement
  | Block of Declaration * Statement
  | If of BExp * Statement
  | IfElse of BExp * Statement * Statement
  | While of BExp * Statement
  | Break
  | Continue
  | Read of string
  | ReadArray of string * AExp
  | Write of AExp

type Program = Declaration * Statement
type State = UO of Guid | O of int | Undefined
type Action = S of Statement | A of AExp | B of BExp | D of Declaration
type Edge = State * Action * State
type ProgramGraphMap = Map<State, (Action * State) list>

type SignsLattice = Positive | Negative | Zero
type IntervalValues = Infinity | NegInfinity | IntV of int
type IntervalLattice = Bottom | Int of IntervalValues * IntervalValues
type IntervalSigma = Map<string, IntervalLattice>
type WorklistMethod = FIFO | LIFO


let (++) a b = Array.append a b

let getFV (pg: ProgramGraphMap) =
    pg
    |> Map.fold (fun fv _ dest ->
      dest
      |> List.fold (fun (fv': Set<string>) (a,_) ->
        match a with
        | S(VarAssign(s,_)) -> fv'.Add s
        | S(ArrayAssign(s,_,_)) -> fv'.Add s
        | S(Read s) -> fv'.Add s
        | _ -> fv'
        ) fv
      ) Set.empty

let rec getFVA (aExp: AExp) =
  match aExp with
  | V _ -> Set.empty
  | Var x -> Set.singleton x
  | Array(x,i) -> Set.union (Set.singleton x) (getFVA i)
  | Add(a1,a2) -> Set.union (getFVA a1) (getFVA a2)
  | Sub(a1,a2) -> Set.union (getFVA a1) (getFVA a2)
  | Mult(a1,a2) -> Set.union (getFVA a1) (getFVA a2)
  | Div(a1,a2) -> Set.union (getFVA a1) (getFVA a2)

let rec getFVB (bExp: BExp) =
  match bExp with
  | BV _ -> Set.empty 
  | Less(a1,a2) -> Set.union (getFVA a1) (getFVA a2)
  | LessEq(a1,a2) -> Set.union (getFVA a1) (getFVA a2)
  | Great(a1,a2) -> Set.union (getFVA a1) (getFVA a2)
  | GreatEq(a1,a2) -> Set.union (getFVA a1) (getFVA a2)
  | Eq(a1,a2) -> Set.union (getFVA a1) (getFVA a2)
  | NotEq(a1,a2) -> Set.union (getFVA a1) (getFVA a2)
  | And(b1,b2) -> Set.union (getFVB b1) (getFVB b2)
  | Or(b1,b2) -> Set.union (getFVB b1) (getFVB b2)
  | Neg b -> getFVB b