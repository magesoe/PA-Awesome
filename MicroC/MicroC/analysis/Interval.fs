module Interval
open Domain

let addIV = function
  | (Infinity,NegInfinity)
  | (NegInfinity,Infinity) -> None
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
  | (Infinity,NegInfinity)
  | (NegInfinity,Infinity) -> None
  | (Infinity,_)
  | (_,Infinity) -> Some Infinity
  | (NegInfinity,_)
  | (_,NegInfinity) -> Some NegInfinity
  | (IntV n1, IntV n2) -> Some (IntV (n1 * n2))

let divIV = function
  | (_,IntV 0) -> None
  | (Infinity,IntV _) -> Some Infinity
  | (NegInfinity,IntV _) -> Some NegInfinity
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

  | Add(a1,a2) -> getOpIntAExp min max sigma a1 a2 addIV
  | Sub(a1,a2) -> getOpIntAExp min max sigma a1 a2 subIV
  | Mult(a1,a2) -> getOpIntAExp min max sigma a1 a2 multIV
  | Div(a1,a2) -> getOpIntAExp min max sigma a1 a2 divIV

and getOpIntAExp min max (sigma: Map<string, IntervalLattice>) (a1: AExp) (a2: AExp) f =
  let s1 = aexpToInt min max sigma a1
  let s2 = aexpToInt min max sigma a2
  match s1,s2 with
  | (Bottom,_)
  | (_,Bottom) -> Bottom
  | (Int(z11,z12), Int(z21,z22)) -> newBound min max z11 z12 z21 z22 f

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
        x,Int(intersectInterval(new1,new2,cur1,cur2))
      )
    |> Map.ofArray

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