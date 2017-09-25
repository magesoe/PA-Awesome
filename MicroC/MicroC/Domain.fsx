﻿open System
type Declaration = 
  DVar of string 
  | DArray of string 
  | DEmpty 
  | DSeq of Declaration * Declaration

type BExp = 
  V of bool 
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
  | Array of string
  | Add of AExp * AExp
  | Sub of AExp * AExp
  | Mult of AExp * AExp
  | Div of AExp * AExp

type Statement =
  VarAssign of string * AExp
  | ArrayAssign of string * AExp
  | Seq of Statement * Statement
  | Block of Declaration * Statement
  | If of BExp * Statement
  | IfElse of BExp * Statement * Statement
  | While of BExp * Statement
  | Break
  | Continue
  | Read of string
  | Write of AExp

type Program = Declaration * Statement

type Id = Guid
type State = Id
type Action = S of Statement | A of AExp | B of BExp | D of Declaration
type Edge = State * Action * State
type ProgramGraph = Map<State, (State * Action) list>

let (++) a b = Array.append a b