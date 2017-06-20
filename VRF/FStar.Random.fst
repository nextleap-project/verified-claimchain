module FStar.Random

open FStar.Seq

type cmp = f: (nat -> nat -> Tot bool){total_order nat f}
type product (f:cmp) = 
    |Mk: number: int -> divisors: list nat{List.length divisors > 0 /\ List.sorted f divisors } -> product f

val productDivisorsLength: #f:cmp ->  number: product f -> Tot(nat)
let productDivisorsLength #f number = 
    match number with 
        |Mk _ divisors -> List.length divisors

assume val isPrime: #operations: nat -> number: int -> Tot(bool)
assume val isPrimePr:  #f:cmp ->  #operations : nat -> number : product  f-> Tot(bool)

assume val genPrime: #operations : nat -> Tot(int)
assume val genPrimePr: #f:cmp -> #operations: nat -> Tot(r: product f {productDivisorsLength r = 1})

assume val factorize: #f:cmp -> number: int -> Tot(product f)

assume val isCoPrimeII: number: int -> coPrimeWith: int -> Tot(bool)
assume val isCoPrimeIPr:  #f:cmp -> number : int -> coPrimeWith: product f -> Tot(bool)
assume val isCoPrimePrPr:  #f:cmp -> number : product f -> coPrimeWith : product f -> Tot(bool)

assume val listCommonEntities: a: eqtype ->  lst: list a -> lst2: list a -> Tot(bool)

assume val multiply:  #f:cmp -> a: product f -> b: product f -> Tot(product f)

val generateM: #f:cmp -> #operations: nat ->  seed: int -> 
            reseedCounter: nat -> counter : nat {counter < reseedCounter} -> 
            Tot(b: bool & (if b then (m: product f) else unit))(decreases (reseedCounter - counter))

let rec generateM #f #operations seed reseedCounter counter = 
    let p = genPrimePr #f #operations in 
    let q = genPrimePr #f #operations in 
    let m = multiply #f p q in
    let r = isCoPrimeIPr seed m in 
    if r then 
        (|true, m|)
    else if (counter+1) < reseedCounter then 
        generateM #f #operations seed reseedCounter (counter + 1) 
    else (|false, ()|)

val _BBSRandom : #f: cmp ->  #operations: nat -> 
        seed: int-> reseedCounter: nat -> 
        lengthRequired: nat-> Tot(b: bool * s: seq nat{Seq.length s = lengthRequired})

let _BBSRandom #f #operations seed reseedCounter lengthRequired = 
    let seq = Seq.create lengthRequired 0 in (true, seq)