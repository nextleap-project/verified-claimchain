module Spec.VRF

open FStar.UInt32
open FStar.UInt8
open FStar.Seq


let prime = pow2 255 - 19
let n = 2
type elem: Type0 = e: int{e>=0 /\ e < prime}
type point = | Proj: x: elem -> y: elem -> point



let bytes =  seq FStar.UInt8.t
let lbytes (l: nat) = b: seq UInt8.t {length b = l}
let key = lbytes 32

let order = 2

assume val scalarAddition: p: point -> q: point -> Tot(r: point)
assume val scalarMultiplication : p: point -> k: key -> Tot(r: point)

assume val haclScalarMultiplication : p: point -> k: key -> Tot(point)

(*let op_Star_At = scalarAddition  *)
let op_Star_Star = scalarMultiplication

assume val _ECVRF_hash_to_curve: input: bytes -> 
            public_key: 'a -> Tot(point)

assume val random:     max: nat{max < pow2 256} -> Tot(random : nat {random <= max})    
assume val natToBytes : number : nat {number < pow2 256} -> Tot(key)    

val randBytes: max: nat{max < pow2 256} -> Tot(key) 
let randBytes max = 
    let rand = random max in natToBytes rand

assume val _ECVRF_hash_points : generator: point -> h:  point -> 
            public_key: point -> gamma : point -> 
            gk : point -> hk : point -> 
            Tot(int)

assume val pointToBytesTemp: a: point -> Tot(key)

assume val _ECP2OS : gamma: point -> Tot(bytes)
assume val _I2OSP: value1: int -> n: int -> Tot(bytes)

assume val seqConcat : s1: seq 'a -> s2: seq 'a -> 
            Tot(r:seq 'a{Seq.length    r = Seq.length s1 + Seq.length s2})

val _ECVRF_prove: input: bytes ->  public_key: point -> 
            private_key : point -> generator : point-> Tot(bytes) 
            (*) Tot(proof: bytes{Seq.len proof = 5 * n + 1}) *)

let _ECVRF_prove input public_key private_key generator = 
    let h = _ECVRF_hash_to_curve input public_key in 
    let private_key_as_bytes = pointToBytesTemp private_key in 
    let gamma = scalarMultiplication h private_key_as_bytes in 
    let k_ = random (order-1) in 
    let k =  natToBytes k_ in  
    let gk = scalarMultiplication generator k in  (* k< (2^8)^32 = 2^(8*32) = 2^(2^3 * 2^ 5 = 256) *) (* *)
    let hk = scalarMultiplication h k in 
    let c = _ECVRF_hash_points generator h public_key gamma gk hk in (*int*)
    let cq = op_Multiply c  prime in  (*int*)
    let s = k_ - cq (* int *) in 
    let fst = _ECP2OS gamma in 
    let snd = _I2OSP c n in 
    let thd = _I2OSP s ( op_Multiply 2 n) in 
    let pi = seqConcat fst (seqConcat snd thd) in pi


val _ECVRF_rec : counter: nat -> counter_local: nat{counter_local < counter} -> 
                s: seq 'a {Seq.length s > counter} -> r_temp : seq 'a ->
                Tot(r: seq 'a)(decreases (counter - counter_local))

let rec _ECVRF_rec counter counter_local s r_temp =
    let r_temp = seqConcat r_temp (Seq.create 1 (Seq.index s counter_local)) in 
    if (counter_local + 1) < counter 
        then _ECVRF_rec counter (counter_local +1) s r_temp
    else 
        r_temp

val _ECVRF_proof2hash: pi: bytes{Seq.length pi = op_Multiply 5 n + 1} -> Tot(hash: bytes)
let _ECVRF_proof2hash pi = 
    let r_temp = Seq.createEmpty in 
     _ECVRF_rec (op_Multiply 2 n + 1) 2 pi r_temp


assume val _ECVRF_decode_proof: 
        pi: bytes {Seq.length pi = op_Multiply 5 n + 1} -> Tot(point * key * key)


val _ECVRF_verify : generator: point ->  public_key : point ->
        pi: bytes {Seq.length pi = op_Multiply 5 n +1} -> 
        input : bytes -> 
        Tot(bool)

assume val _isPointOnTheCurve :  p: point -> Tot(bool)        

assume val equal : s1: bytes -> s2: bytes -> Tot(bool)

assume val bytesToInt: s: bytes -> Tot(int)

let _ECVRF_verify generator public_key pi input = 
    let gamma, c, s = _ECVRF_decode_proof pi in 
    if not(_isPointOnTheCurve gamma) then false else
    let pkc = scalarMultiplication public_key c in 
    let gs = scalarMultiplication generator s in 
    let u  = scalarAddition pkc gs in 
    let h = _ECVRF_hash_to_curve input public_key in 
    let gammac = scalarMultiplication gamma c in 
    let hs = scalarMultiplication h s in 
    let v = scalarAddition gammac hs in 
    let c_prime = _ECVRF_hash_points generator h public_key gamma u v in 
    (bytesToInt c) = c_prime