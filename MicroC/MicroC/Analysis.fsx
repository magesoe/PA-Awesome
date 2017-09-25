#load "Domain.fsx"
#load "ProgramGraph.fsx"
open Domain
open System

let getAssigns (assigns: Map<string,Set<(string * Guid)>>) (x: string) =
  match Map.tryFind x assigns with
  | Some xs -> xs.Add(x,Guid.Empty)
  | None -> failwith "Assignment is found, but is not in map of assigns"

let killRD (assigns: Map<string,Set<(string * Guid)>>) ((s,a): State * Domain.Action) =
  match a with
  | S(VarAssign(x,_))
  | S(Read x) -> getAssigns assigns x
  | _ -> Set.empty

let genRD ((s,a): State * Domain.Action) =
  match a with
  | S(VarAssign(x,_))
  | S(ArrayAssign(x,_))
  | S(Read x) -> Set.singleton (x,s)
  | _ -> Set.empty
