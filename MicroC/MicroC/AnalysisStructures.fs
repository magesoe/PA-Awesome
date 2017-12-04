module AnalysisStructures

open Domain
open System
open ProgramGraph
open WorklistAlgo
open System.Dynamic

let transferBit kill gen (current: Set<'a>) ((s1,a,s2): Edge) =
  current
  |> Set.filter (fun x -> (kill x a) |> not)
  |> Set.union (gen (s1,a,s2))

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


type SignsLattice = Positive | Negative | Zero


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
    
let rec getOperatorResAExp sigma a1 a2 (f: SignsLattice * SignsLattice -> Set<'a>) =
  let s1 = aexpToSigns sigma a1
  let s2 = aexpToSigns sigma a2
  Seq.allPairs s1 s2
  |> Seq.map f
  |> Set.unionMany

and getOperatorResBExp sigma a1 a2 f =
  getBasic (Map.toList sigma)
  |> Array.Parallel.map Map.ofList
  |> Array.filter (fun sigma' ->
    getOperatorResAExp sigma' a1 a2 f
    |> Set.contains true
    )
  |> Array.fold (fun bigSigma current ->
    current
    |> Map.fold (fun bigSigma' x signs ->
      match Map.tryFind x bigSigma' with
      | Some s -> Map.add x (Set.union s signs) bigSigma'
      | None -> Map.add x signs bigSigma'
      ) bigSigma
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
      if si.Contains Positive then Set.ofArray [|Negative;Positive;Zero|] else Set.empty
    Map.add x newSign sigma


  | D(DVar x) -> Map.add x (Set.ofArray [|Zero|]) sigma
  | D(DArray(x,i)) ->
    let si = aexpToSigns sigma i
    let newSign = 
      if si.Contains Positive then Set.singleton Zero else Set.empty
    Map.add x newSign sigma
   
  | B bexp -> bexpToSigns sigma bexp

  | _ -> failwith "Unknown action"

type IntervalValues = Infinity | NegInfinity | IntV of int
type IntervalLattice = Bottom | Int of IntervalValues * IntervalValues
type IntervalSigma = Map<string, IntervalLattice>

let addIV = function
  | (Infinity,_)
  | (_,Infinity) -> Some Infinity
  | (NegInfinity,_)
  | (_,NegInfinity) -> Some NegInfinity
  | (IntV n1, IntV n2) -> Some (IntV (n1 + n2))

let subIV = function
  | (Infinity,Infinity)
  | (NegInfinity,NegInfinity) -> None
  | (NegInfinity,_)
  | (_,Infinity) -> Some NegInfinity
  | (Infinity,_)
  | (_,NegInfinity) -> Some Infinity
  | (IntV n1, IntV n2) -> Some (IntV (n1 - n2))

let multIV = function
  | (Infinity,_)
  | (_,Infinity) -> Some Infinity
  | (NegInfinity,_)
  | (_,NegInfinity) -> Some NegInfinity
  | (IntV n1, IntV n2) -> Some (IntV (n1 * n2))

let divIV = function
  | (_,IntV 0) -> None
  | (Infinity,IntV _) -> Some Infinity
  | (IntV _,NegInfinity) -> Some NegInfinity
  | (IntV _, Infinity) 
  | (IntV _, NegInfinity) -> Some (IntV 0)
  | (IntV n1, IntV n2) -> Some (IntV (n1 / n2))
  | _ -> None

let minIV (v1: IntervalValues) (v2: IntervalValues) =
  match v1,v2 with
  | (Infinity,x)
  | (x,Infinity) -> x
  | (NegInfinity,_)
  | (_,NegInfinity) -> NegInfinity
  | (IntV n1, IntV n2) -> if n1 < n2 then IntV n1 else IntV n2

let maxIV (v1: IntervalValues) (v2: IntervalValues) =
  match v1,v2 with
  | (NegInfinity,x)
  | (x,NegInfinity) -> x
  | (Infinity,_)
  | (_,Infinity) -> Infinity
  | (IntV n1, IntV n2) -> if n1 > n2 then IntV n1 else IntV n2

let getBound z11 z12 z21 z22 (order: IntervalValues -> IntervalValues -> IntervalValues) 
  (op: IntervalValues * IntervalValues -> IntervalValues option) =
  let bounds =
    [|op (z11,z21); op (z11,z22); op (z12,z21); op (z12,z22)|]
    |> Array.filter Option.isSome
    |> Array.map Option.get
  if bounds = Array.empty then None else 
    Some (Array.reduce order bounds)


let newBound min max z11 z12 z21 z22 f =
  let min' = getBound z11 z12 z21 z22 minIV f
  let max' = getBound z11 z12 z21 z22 maxIV f
  if min' = None || max' = None then Bottom else
  let first =
    match min'.Value with
    | NegInfinity -> NegInfinity
    | Infinity -> IntV max
    | IntV n when n < min -> NegInfinity
    | IntV n when n > max -> IntV max
    | IntV n -> IntV n
  let second =
    match max'.Value with
    | Infinity -> Infinity
    | NegInfinity -> IntV min
    | IntV n when n > max -> Infinity
    | IntV n when n < min -> IntV min
    | IntV n -> IntV n
  Int(first,second)

let addInt min max (z1: IntervalLattice) (z2: IntervalLattice) =
  match z1,z2 with
  | (Bottom,_)
  | (_,Bottom) -> Bottom
  | (Int(z11,z12), Int(z21,z22)) -> newBound min max z11 z12 z21 z22 addIV

let subInt min max (z1: IntervalLattice) (z2: IntervalLattice) =
  match z1,z2 with
  | (Bottom,_)
  | (_,Bottom) -> Bottom
  | (Int(z11,z12), Int(z21,z22)) -> newBound min max z11 z12 z21 z22 subIV

let multInt min max (z1: IntervalLattice) (z2: IntervalLattice) =
  match z1,z2 with
  | (Bottom,_)
  | (_,Bottom) -> Bottom
  | (Int(z11,z12), Int(z21,z22)) -> newBound min max z11 z12 z21 z22 multIV

let divInt min max (z1: IntervalLattice) (z2: IntervalLattice) =
  match z1,z2 with
  | (Bottom,_)
  | (_,Bottom) -> Bottom
  | (Int(z11,z12), Int(z21,z22)) -> newBound min max z11 z12 z21 z22 divIV

let isLessInterval (v1: IntervalValues) (v2: IntervalValues) =
  match v1,v2 with
  | (Infinity,_)
  | (IntV _, NegInfinity) -> false
  | (IntV n1, IntV n2) when n1 >= n2 -> false
  | _ -> true

let subtractInterval (keep: IntervalLattice) (subtract: IntervalLattice) =
  match keep,subtract with
  | (Bottom,_) -> Bottom
  | (x,Bottom) -> x
  | (Int(k1,k2),Int(s1,s2)) ->
    match isLessInterval s1 k1, isLessInterval k2 s2 with
    | true, true -> Bottom
    | true, false -> Int(s2,k2)
    | false, true -> Int(k1,s1)
    | false, false -> Int(k1,k2)

let intersectInterval ((z1,z2,a1,a2): IntervalValues * IntervalValues * IntervalValues * IntervalValues) =
  let min =
    match z1,a1 with
    | (NegInfinity,x) 
    | (x,NegInfinity) -> x
    | (Infinity,_)
    | (_,Infinity) -> Infinity
    | (IntV n1, IntV n2) ->
      if n1 > n2 then IntV n1 else IntV n2

  let max =
    match z2,a2 with
    | (Infinity,x) 
    | (x,Infinity) -> x
    | (NegInfinity,_)
    | (_,NegInfinity) -> NegInfinity
    | (IntV n1, IntV n2) ->
      if n1 < n2 then IntV n1 else IntV n2
  min,max


let unionInterval ((z1,z2,a1,a2): IntervalValues * IntervalValues * IntervalValues * IntervalValues) =
  let min =
    match z1,a1 with
    | (NegInfinity,_) 
    | (_,NegInfinity) -> NegInfinity
    | (Infinity,x)
    | (x,Infinity) -> x
    | (IntV n1, IntV n2) ->
      if n1 < n2 then IntV n1 else IntV n2

  let max =
    match z2,a2 with
    | (Infinity,_) 
    | (_,Infinity) -> Infinity
    | (NegInfinity,x)
    | (x,NegInfinity) -> x
    | (IntV n1, IntV n2) ->
      if n1 > n2 then IntV n1 else IntV n2
  min,max

let lessInt (z1: IntervalLattice) (z2: IntervalLattice) =
  match z1,z2 with
  | (Bottom,_)
  | (_,Bottom) -> Bottom
  | (Int(z11,z12), Int(_,z22)) ->
    match isLessInterval z22 z12, isLessInterval z22 z11 with
    | true, true -> Bottom
    | true, false -> Int(z11,z22)
    | false, _ -> Int(z11,z12)

let greatInt (z1: IntervalLattice) (z2: IntervalLattice) =
  match z1,z2 with
  | (Bottom,_)
  | (_,Bottom) -> Bottom
  | (Int(z11,z12), Int(z21,_)) ->
    match isLessInterval z21 z12, isLessInterval z21 z11 with
    | true, true -> Bottom
    | true, false -> Int(z21,z12)
    | false, _ -> Int(z11,z12)

let intersectToInt z11 z12 z21 z22 =
  if isLessInterval z12 z21 || isLessInterval z22 z11 then Bottom else
  Int(intersectInterval(z11,z12,z21,z22))

let unionToInt z11 z12 z21 z22 = Int(unionInterval(z11,z12,z21,z22))

let eqInt (z1: IntervalLattice) (z2: IntervalLattice) =
  match z1,z2 with
  | (Bottom,_)
  | (_,Bottom) -> Bottom
  | (Int(z11,z12), Int(z21,z22)) -> intersectToInt z11 z12 z21 z22
    

let notEqInt (z1: IntervalLattice) (z2: IntervalLattice) =
  match z1,z2 with
  | (Bottom,_)
  | (_,Bottom) -> Bottom
  | (Int(z11,z12), Int(z21,z22)) -> unionToInt z11 z12 z21 z22
    

let rec aexpToInt (min: int) (max: int) (sigma: IntervalSigma) (aexp: AExp) =
  match aexp with
  | V n when min <= n && n <= max -> Int(IntV n, IntV n)
  | V n when n < min -> Int(NegInfinity, IntV min)
  | V n when n > max -> Int(IntV max, Infinity)
  | V _ -> failwith "Unknown case number interval analysis"
  | Var x -> sigma.[x]
  | Array(x,i) -> 
    match aexpToInt min max sigma i with
    | Bottom
    | Int(_,NegInfinity) -> Bottom
    | Int(_,IntV n) when n < 0 -> Bottom
    | _ -> sigma.[x]

  | Add(a1,a2) -> getOpIntAExp min max sigma a1 a2 addInt
  | Sub(a1,a2) -> getOpIntAExp min max sigma a1 a2 subInt
  | Mult(a1,a2) -> getOpIntAExp min max sigma a1 a2 multInt
  | Div(a1,a2) -> getOpIntAExp min max sigma a1 a2 divInt

and getOpIntAExp min max (sigma: Map<string, IntervalLattice>) (a1: AExp) (a2: AExp) f =
  let s1 = aexpToInt min max sigma a1
  let s2 = aexpToInt min max sigma a2
  f min max s1 s2

and bexpToInt (min: int) (max: int) (sigma: Map<string, IntervalLattice>) (exp: BExp) =
  match exp with
  | BV true -> sigma
  | BV false -> Map.empty
  | Neg bexp ->
    let fv = getFVB bexp

    bexpToInt min max sigma bexp
    |> Map.fold (fun currentSigma x interval ->
      if interval = Bottom || (Set.contains x fv |> not) then currentSigma else
      Map.add x (subtractInterval currentSigma.[x] interval) currentSigma
      ) sigma
  | Less(a1,a2) -> getOpIntBExp min max sigma a1 a2 lessInt
  | LessEq(a1,a2) -> getOpIntBExp min max sigma a1 a2 lessInt
  | Great(a1,a2) -> getOpIntBExp min max sigma a1 a2 greatInt
  | GreatEq(a1,a2) -> getOpIntBExp min max sigma a1 a2 greatInt
  | Eq(a1,a2) -> getOpIntBExp min max sigma a1 a2 eqInt
  | NotEq(a1,a2) -> getOpIntBExp min max sigma a1 a2 greatInt
  | And(b1,b2) -> getAndOrInt min max sigma b1 b2 intersectToInt
  | Or(b1,b2) -> getAndOrInt min max sigma b1 b2 unionToInt

and getOpIntBExp min max sigma a1 a2 f =
  let keys = 
    sigma
    |> Map.toArray
    |> Array.map fst
  let fv = Set.union (getFVA a1) (getFVA a2)
  let result =
    keys
    |> Array.map (fun x ->
      if Set.contains x fv |> not then x,sigma.[x] else
      let sigma' =
        keys
        |> Array.map (fun x' -> x',Int(NegInfinity,Infinity))
        |> Map.ofArray
        |> Map.add x sigma.[x]
      let l1 = aexpToInt min max sigma' a1
      let l2 = aexpToInt min max sigma' a2
      match f l1 l2, sigma.[x] with
      | (Bottom,_)
      | (_,Bottom) -> x,Bottom
      | (Int(new1,new2),Int(cur1,cur2)) ->
        //if isLessInterval new2 cur1 || isLessInterval cur2 new1 then printfn "not overlap"; x,Bottom else
        x,Int(intersectInterval(new1,new2,cur1,cur2))
      )
    |> Map.ofArray
  //printfn "res %A" result
  if
    result
    |> Map.filter (fun k _ -> Set.contains k fv)
    |> Map.forall (fun _ v -> v = Bottom)
  then
    keys
    |> Array.map (fun x' -> x',Bottom)
    |> Map.ofArray
  else
    result

 and getAndOrInt min max sigma b1 b2 f =
  let sb1 = bexpToInt min max sigma b1
  let sb2 = bexpToInt min max sigma b2
  sb1 
  |> Map.map (fun x s1 ->
    match s1, sb2.[x] with
    | (Bottom,_)
    | (_,Bottom) -> Bottom
    | (Int(z11,z12),Int(z21,z22)) ->
      f z11 z12 z21 z22
    )


let transferInterval min max (sigma: Map<string,IntervalLattice>) ((s1,a,s2): Edge) =
  match a with
  | S(Write _)
  | S Break
  | S Continue -> sigma
  | S(VarAssign(x,aexp)) -> 
    Map.add x (aexpToInt min max sigma aexp) sigma
  | S(ArrayAssign(x,iexp,aexp)) ->
    let si = aexpToInt min max sigma iexp
    let sa = aexpToInt min max sigma aexp
    let current = sigma.[x]
    match current,sa,si with
    | (Bottom,_,_) -> sigma
    | (_,_,Int(_,NegInfinity)) 
    | (_,_,Bottom) -> Map.add x Bottom sigma
    | (_,_,Int(_,IntV(n))) when n < 0 -> Map.add x Bottom sigma
    | (Int(IntV z1, IntV z2),Int(IntV a1, IntV a2),_) ->
      let combined =
        match z1,z2,a1,a2 with
        | (z1,_,a1,_) when a1 < z1 && a1 < min ->
          NegInfinity,IntV min
        | (_,z2,_,a2) when a2 > z2 && a2 > max ->
          IntV max,Infinity
        | (z1,z2,a1,a2) when a1 < z1 && z2 < a2 ->
          IntV a1, IntV a2
        | (z1,z2,a1,a2) when a1 < z1 && a2 <= z2 ->
          IntV a1, IntV z2
        | (z1,z2,a1,a2) when z1 <= a1 && z2 < a2 ->
          IntV z1, IntV a2
        | (z1,z2,_,_) -> IntV z1, IntV z2

      Map.add x (Int(combined)) sigma
    | _ -> failwith "Unknown case when assigning to array interval analysis"
  
  | S(Read x) -> Map.add x (Int(NegInfinity, Infinity)) sigma
  | S(ReadArray(x,i)) ->
    match aexpToInt min max sigma i with
    | Bottom 
    | Int(_,NegInfinity) -> Map.add x Bottom sigma
    | Int(_,IntV n) when n < 0 -> Map.add x Bottom sigma
    | _ -> Map.add x (Int(NegInfinity, Infinity)) sigma
  
  | D(DVar x) -> 
    let interval =
      if 0 < min then Int(NegInfinity, IntV min)
      else if 0 > max then Int(IntV max, Infinity)
      else Int(IntV 0, IntV 0)
    Map.add x interval sigma
  | D(DArray(x,i)) ->
    match aexpToInt min max sigma i with
    | Bottom 
    | Int(_,NegInfinity) -> Map.add x Bottom sigma
    | Int(_,IntV n) when n < 0 && min < 0 && max > 0 -> Map.add x Bottom sigma
    | _ -> 
      let interval =
        if 0 < min then Int(NegInfinity, IntV min)
        else if 0 > max then Int(IntV max, Infinity)
        else Int(IntV 0, IntV 0)
      Map.add x interval sigma

  | B bexp -> bexpToInt min max sigma bexp

  | _ -> failwith "Unknown action"