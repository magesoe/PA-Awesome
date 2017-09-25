#load "Domain.fsx"
open Domain
open System

let PgBExp (_start: State) (_end: State) (_break: State) (_continue: State) (bexp: BExp) = [|(_start,B bexp,_end)|]
let PgAExp (_start: State) (_end: State) (_break: State) (_continue: State) (aexp: AExp) = [|(_start,A aexp,_end)|]

let rec PgStatement (_start: State) (_end: State) 
  (_break: State) (_continue: State) (statement: Statement) = 
  match statement with
  | VarAssign(s,a) -> [|(_start,S statement,_end)|]
  | ArrayAssign(s,a) -> [|(_start,S statement,_end)|]
  | Seq(s1,s2) -> 
    let newState = Guid.NewGuid()   
    PgStatement _start newState _break _continue s1 ++ 
    PgStatement newState _end _break _continue s2
  | Block(d,s) ->
    let tmpState = Guid.NewGuid()
    let pgD = PgDeclaration _start tmpState _break _continue d
    let pgS = 
      if pgD = Array.empty 
      then 
        PgStatement _start _end _break _continue s
      else
        PgStatement tmpState _end _break _continue s
    pgD ++ pgS
  | If(b,s) -> 
      let tmpState = Guid.NewGuid()
      PgBExp _start tmpState _break _continue b ++
      PgStatement tmpState _start _break _continue s
  | IfElse(b,s1,s2) ->
      let tmpState = Guid.NewGuid()
      PgBExp _start tmpState _break _continue b ++
      PgStatement tmpState _end _break _continue s1 ++
      PgStatement tmpState _end _break _continue s2
  | While(b,s) ->
    let startStatement = Guid.NewGuid()
    PgBExp _start startStatement _break _continue b ++
    PgBExp _start _end _break _continue (Neg(b)) ++
    PgStatement startStatement _start _end _start s
  | Break -> [|(_start,S statement,_break)|]
  | Continue -> [|(_start,S statement,_continue)|]
  | Read s -> [|(_start,S statement,_end)|]
  | Write a -> [|(_start,S statement,_end)|]

and PgDeclaration (_start: State) (_end: State) 
  (_break: State) (_continue: State) (declaration: Declaration) =
  match declaration with
  | DVar s -> [|(_start,D declaration,_end)|]
  | DArray s -> [|(_start,D declaration,_end)|]
  | DEmpty -> [||]
  | DSeq(d1,d2) -> 
    let newState = Guid.NewGuid()   
    PgDeclaration _start newState _break _continue d1 ++
    PgDeclaration newState _end _break _continue d2


let GetProgramGraph ((d,s): Program) =
  let tmpState = Guid.NewGuid()
  let _start = Guid.NewGuid()
  let _end = Guid.NewGuid()
  PgDeclaration _start tmpState tmpState tmpState d ++ 
  PgStatement tmpState _end _end _end s
  |> Array.fold (fun g (s,a,e) ->
    match Map.tryFind s g with
    | Some ends -> Map.add s ((a,e) :: ends) g
    | None -> Map.add s [(a,e)] g
    ) Map.empty


let GetFV (pg: ProgramGraph) =
    pg
    |> Map.fold (fun fv _ dest ->
      dest
      |> List.map (fun (_,a) -> a)
      |> List.fold (fun (fv': Set<string>) a ->
        match a with
        | S(VarAssign(s,_)) -> fv'.Add s
        | S(ArrayAssign(s,_)) -> fv'.Add s
        | S(Read s) -> fv'.Add s
        | _ -> fv'
        ) fv
      ) Set.empty

let program = 
  DSeq(DVar("x"),DVar("y")),
  Seq(VarAssign("y", V 1), 
    Seq(Read "x", 
      Seq(While(Great(Var "x", V 1), Seq(VarAssign("y", Mult(Var "x", Var "y")),VarAssign("x", Sub(Var "x", V 1))
          )), Write(Var "y"))))
GetProgramGraph program