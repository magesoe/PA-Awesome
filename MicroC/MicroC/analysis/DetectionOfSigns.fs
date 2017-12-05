module DetectionOfSigns
open Domain

let plusSign (s1: SignsLattice, s2: SignsLattice) = 
  match s1,s2 with
  | (Negative, Zero)
  | (Zero, Negative)
  | (Negative, Negative) -> Set.singleton Negative

  | (Positive, Zero)
  | (Zero, Positive)
  | (Positive, Positive) -> Set.singleton Positive

  | (Positive, Negative)
  | (Negative, Positive) -> Set.ofArray [|Negative;Positive;Zero|]

  | (Zero, Zero) -> Set.singleton Zero

let subtractSign (s1: SignsLattice, s2: SignsLattice) = 
  match s1,s2 with
  | (Negative, Zero)
  | (Zero, Negative)
  | (Negative, Negative) -> Set.singleton Negative

  | (Positive, Zero)
  | (Zero, Positive)
  | (Positive, Positive) -> Set.singleton Positive

  | (Positive, Negative)
  | (Negative, Positive) -> Set.ofArray [|Negative;Positive;Zero|]

  | (Zero, Zero) -> Set.singleton Zero

let productSign (s1: SignsLattice, s2: SignsLattice) = 
  match s1,s2 with
  | (Positive, Positive)
  | (Negative, Negative) -> Set.singleton Positive
  
  | (Zero, Negative)
  | (Negative, Zero)
  | (Positive, Zero)
  | (Zero, Positive)
  | (Zero, Zero) -> Set.singleton Zero

  | (Positive, Negative)
  | (Negative, Positive) -> Set.singleton Negative

let divisionSign (s1: SignsLattice, s2: SignsLattice) = 
  match s1,s2 with
  | (Positive, Positive)
  | (Negative, Negative) -> Set.singleton Positive
  
  | (Zero, Negative)
  | (Zero, Positive) -> Set.singleton Zero

  | (Negative, Zero)
  | (Positive, Zero)
  | (Zero, Zero) -> Set.empty

  | (Positive, Negative)
  | (Negative, Positive) -> Set.singleton Negative


let lessSign (s1: SignsLattice, s2: SignsLattice) = 
  match s1,s2 with
  | (Positive, Positive)
  | (Negative, Negative) -> Set.ofArray [|true;false|]
  
  | (Zero, Zero)
  | (Zero, Negative)
  | (Positive, Negative)
  | (Positive, Zero) -> Set.singleton false
  
  | (Zero, Positive)
  | (Negative, Zero)
  | (Negative, Positive) -> Set.singleton true

let lessEqSign (s1: SignsLattice, s2: SignsLattice) = 
  match s1,s2 with
  | (Positive, Positive)
  | (Negative, Negative) -> Set.ofArray [|true;false|]
  
  | (Zero, Negative)
  | (Positive, Negative)
  | (Positive, Zero) -> Set.singleton false
  
  | (Zero, Zero)
  | (Zero, Positive)
  | (Negative, Zero)
  | (Negative, Positive) -> Set.singleton true

let eqSign (s1: SignsLattice, s2: SignsLattice) = 
  match s1,s2 with
  | (Positive, Positive)
  | (Negative, Negative) -> Set.ofArray [|true;false|]
  
  | (Zero, Negative)
  | (Positive, Negative)
  | (Zero, Positive)
  | (Negative, Zero)
  | (Negative, Positive)
  | (Positive, Zero) -> Set.singleton false
  
  | (Zero, Zero) -> Set.singleton true

let notEqSign (s1: SignsLattice, s2: SignsLattice) = 
  match s1,s2 with
  | (Positive, Positive)
  | (Negative, Negative) -> Set.ofArray [|true;false|]
  
  | (Zero, Negative)
  | (Positive, Negative)
  | (Zero, Positive)
  | (Negative, Zero)
  | (Negative, Positive)
  | (Positive, Zero) -> Set.singleton true
  
  | (Zero, Zero) -> Set.singleton false

let greatSign (s1: SignsLattice, s2: SignsLattice) = 
  match s1,s2 with
  | (Positive, Positive)
  | (Negative, Negative) -> Set.ofArray [|true;false|]
  
  | (Zero, Negative)
  | (Positive, Negative)
  | (Positive, Zero) -> Set.singleton true
  
  | (Zero, Zero)
  | (Zero, Positive)
  | (Negative, Zero)
  | (Negative, Positive) -> Set.singleton false

let greatEqSign (s1: SignsLattice, s2: SignsLattice) = 
  match s1,s2 with
  | (Positive, Positive)
  | (Negative, Negative) -> Set.ofArray [|true;false|]
  
  | (Zero, Zero)
  | (Zero, Negative)
  | (Positive, Negative)
  | (Positive, Zero) -> Set.singleton true
  
  | (Zero, Positive)
  | (Negative, Zero)
  | (Negative, Positive) -> Set.singleton false

let rec getBasic (sigma: (string * Set<SignsLattice>) list) =
  match sigma with
  | [] -> [|[]|]
  | (x,signs) :: xs -> 
    let prev = getBasic xs
    signs
    |> Set.toArray
    |> Array.collect (fun sign ->
      prev
      |> Array.map (fun res -> (x, Set.singleton sign) :: res)
      )

let rec allPairs l1 l2 =
    let listPair v l = List.fold(fun acc x -> (v,x)::acc) [] l
    match l1 with
    | []    -> []
    | x::xs -> let res = listPair x l2 
               List.fold (fun acc x -> x::acc) res (allPairs xs l2);;
    
let rec getOperatorResAExp sigma a1 a2 (f: SignsLattice * SignsLattice -> Set<'a>) =
  let s1 = aexpToSigns sigma a1
  let s2 = aexpToSigns sigma a2
  allPairs (Set.toList s1) (Set.toList s2) 
  |> List.map f
  |> Set.unionMany

and getOperatorResBExp sigma a1 a2 f =
  getBasic (Map.toList sigma)
  |> Array.Parallel.map Map.ofList
  |> Array.filter (fun sigma' ->
    getOperatorResAExp sigma' a1 a2 f
    |> Set.contains true
    )
  |> Array.fold (fun combinedSigma current ->
    current
    |> Map.fold (fun combinedSigma' x signs ->
      match Map.tryFind x combinedSigma' with
      | Some s -> Map.add x (Set.union s signs) combinedSigma'
      | None -> Map.add x signs combinedSigma'
      ) combinedSigma
    ) Map.empty
 
 and getAndOr sigma b1 b2 f =
  let sb1 = bexpToSigns sigma b1
  let sb2 = bexpToSigns sigma b2
  sb1 
  |> Map.map (fun x s1 ->
    f s1 sb2.[x]
    )

and aexpToSigns (sigma: Map<string, Set<SignsLattice>>) (exp: AExp) =
  match exp with
  | V n -> 
    Set.singleton( 
      match n with
      | n when n < 0 -> Negative
      | n when n > 0 -> Positive
      | _ -> Zero)
  | Var x -> sigma.[x]
  | Array(x,i) -> 
    if aexpToSigns sigma i = Set.singleton Negative then Set.empty else sigma.[x]
  | Add(a1,a2) -> getOperatorResAExp sigma a1 a2 plusSign
  | Sub(a1,a2) -> getOperatorResAExp sigma a1 a2 subtractSign
  | Mult(a1,a2) -> getOperatorResAExp sigma a1 a2 productSign
  | Div(a1,a2) -> getOperatorResAExp sigma a1 a2 divisionSign

and bexpToSigns (sigma: Map<string, Set<SignsLattice>>) (exp: BExp) =
  match exp with
  | BV true -> sigma
  | BV false -> Map.empty
  | Neg bexp ->
    let fv = getFVB bexp

    bexpToSigns sigma bexp
    |> Map.fold (fun currentSigma x signs ->
      if signs = Set.empty || (Set.contains x fv |> not) then currentSigma else
      Map.add x (Set.difference currentSigma.[x] signs) currentSigma
      ) sigma
  | Less(a1,a2) -> getOperatorResBExp sigma a1 a2 lessSign
  | LessEq(a1,a2) -> getOperatorResBExp sigma a1 a2 lessEqSign
  | Great(a1,a2) -> getOperatorResBExp sigma a1 a2 greatSign
  | GreatEq(a1,a2) -> getOperatorResBExp sigma a1 a2 greatEqSign
  | Eq(a1,a2) -> getOperatorResBExp sigma a1 a2 eqSign
  | NotEq(a1,a2) -> getOperatorResBExp sigma a1 a2 notEqSign
  | And(b1,b2) -> getAndOr sigma b1 b2 Set.intersect
  | Or(b1,b2) -> getAndOr sigma b1 b2 Set.union


let transferSigns (sigma: Map<string,Set<SignsLattice>>) ((s1,a,s2): Edge) =
  match a with
  | S(Write _)
  | S Break
  | S Continue -> sigma
  | S(VarAssign(x,aexp)) -> Map.add x (aexpToSigns sigma aexp) sigma
  | S(ArrayAssign(x,iexp,aexp)) ->
    let si = aexpToSigns sigma iexp
    let sa = aexpToSigns sigma aexp
    let newSign =
      if si = Set.singleton Negative then Set.empty else Set.union sigma.[x] sa
    Map.add x newSign sigma
  | S(Read x) -> Map.add x (Set.ofArray [|Negative;Positive;Zero|]) sigma
  | S(ReadArray(x,i)) ->
    let si = aexpToSigns sigma i
    let newSign = 
      if si = Set.singleton Negative then Set.empty else Set.ofArray [|Negative;Positive;Zero|]
    Map.add x newSign sigma

  | D(DVar x) -> Map.add x (Set.ofArray [|Zero|]) sigma
  | D(DArray(x,i)) ->
    let si = aexpToSigns sigma i
    let newSign = 
      if si = Set.singleton Negative then Set.empty else Set.singleton Zero
    Map.add x newSign sigma
   
  | B bexp -> bexpToSigns sigma bexp

  | _ -> failwith "Unknown action"