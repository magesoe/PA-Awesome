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
  | Break
  | Continue
  | Read of string
  | ReadArray of string * AExp
  | Write of AExp
  | Seq of Statement * Statement
  | Block of Declaration * Statement
  | If of BExp * Statement
  | IfElse of BExp * Statement * Statement
  | While of BExp * Statement

type Program = Declaration * Statement
type State = UO of Guid | O of int | Undefined
type Action = S of Statement | B of BExp | D of Declaration
type Edge = State * Action * State
type ProgramGraphMap = Map<State, (Action * State) list>

let (++) a b = Array.append a b