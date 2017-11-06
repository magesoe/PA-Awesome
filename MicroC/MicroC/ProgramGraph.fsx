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
    let newState = Unordered (Guid.NewGuid())   
    PgStatement _start newState _break _continue s1 ++ 
    PgStatement newState _end _break _continue s2
  | Block(d,s) ->
    let tmpState = Unordered (Guid.NewGuid())
    let pgD = PgDeclaration _start tmpState _break _continue d
    let pgS = 
      if pgD = Array.empty 
      then 
        PgStatement _start _end _break _continue s
      else
        PgStatement tmpState _end _break _continue s
    pgD ++ pgS
  | If(b,s) -> 
      let tmpState = Unordered (Guid.NewGuid())
      PgBExp _start tmpState _break _continue b ++
      PgStatement tmpState _start _break _continue s
  | IfElse(b,s1,s2) ->
      let tmpState = Unordered (Guid.NewGuid())
      PgBExp _start tmpState _break _continue b ++
      PgStatement tmpState _end _break _continue s1 ++
      PgStatement tmpState _end _break _continue s2
  | While(b,s) ->
    let startStatement = Unordered (Guid.NewGuid())
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
    let newState = Unordered (Guid.NewGuid())
    PgDeclaration _start newState _break _continue d1 ++
    PgDeclaration newState _end _break _continue d2


let getProgramGraph ((d,s): Program) =
  let _start = Unordered (Guid.NewGuid())
  let _end = Unordered (Guid.NewGuid())
  _start,_end,
  PgStatement _start _end _end _end (Block(d,s))

let getProgramGraphMap (pg: Edge[]) =
  pg
  |> Array.fold (fun map (s1,a,s2) ->
    match Map.tryFind s1 map with
    | Some edges -> Map.add s1 ((a,s2) :: edges) map
    | None -> Map.add s1 [(a,s2)] map
    ) Map.empty

let getFV (pg: ProgramGraphMap) =
    pg
    |> Map.fold (fun fv _ dest ->
      dest
      |> List.fold (fun (fv': Set<string>) (a,_) ->
        match a with
        | S(VarAssign(s,_)) -> fv'.Add s
        | S(ArrayAssign(s,_)) -> fv'.Add s
        | S(Read s) -> fv'.Add s
        | _ -> fv'
        ) fv
      ) Set.empty

let rec getFVA (aExp: AExp) =
  match aExp with
  | V _ -> Set.empty
  | Var x -> Set.singleton x
  | Array x -> Set.singleton x
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

let getFinalStates (pgMap: ProgramGraphMap) =
  pgMap
  |> Map.fold (fun final _ edges ->
    edges
    |> List.filter (fun (_,s) -> pgMap.ContainsKey s |> not)
    |> List.map (fun (_,s) -> s)
    |> Set.ofList
    |> Set.union final
    ) Set.empty

let reverseGraph (edges: Edge[]) = 
  edges
  |> Array.map (fun (s1,a,s2) -> s2,a,s1)

let getOrderedPG (start: State) (pg: ProgramGraphMap) =
  let _start = Ordered (OV 0)
  let rec getOrdered (i: int) (current: State) (pg: ProgramGraphMap) (ordered: Edge list) =
    match Map.tryFind current pg with
    | None -> i,ordered
    | Some edges ->
      edges
      |> List.fold (fun (i', ordered') (a,s2) ->
        getOrdered (i + 1) s2 (Map.remove current pg) ((Ordered (OV i), a, Ordered (OV i')) :: ordered')
        ) (i + 1, ordered)

  let _end, ordered = getOrdered 0 start pg []
  _start, Ordered (OV _end), (ordered |> List.toArray)

let getOrderedPGMap s pg =
  let map = getProgramGraphMap pg
  let _,_,pg' = getOrderedPG s map
  getProgramGraphMap pg'

let program = 
  DSeq(DVar("x"),DVar("y")),
  Seq(VarAssign("y", V 1), 
    Seq(Read "x", 
      Seq(While(Great(Var "x", V 1), Seq(VarAssign("y", Mult(Var "x", Var "y")),VarAssign("x", Sub(Var "x", V 1))
          )), Write(Var "y"))))

