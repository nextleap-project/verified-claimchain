module Spec.VRF

open FStar.UInt32
open FStar.UInt8
open FStar.Seq
open FStar.Option

open FStar.Mul
open FStar.Seq
open FStar.UInt8
open FStar.Endianness
open Spec.Lib
open Spec.Curve25519.Lemmas
open Spec.Curve25519

let bytes =  seq FStar.UInt8.t
let key = lbytes 32
let order = 2
let field = 100000000000

let positive_point_const = Seq.create 1 2uy
let negative_point_const = Seq.create 1 3uy

assume val scalarMultiplication: point:serialized_point -> k: scalar -> Tot serialized_point
assume val scalarAddition: p: serialized_point -> q: serialized_point -> Tot serialized_point
assume val isPointOnCurve: p: option serialized_point -> Tot(bool)

assume val _ECP2OS : gamma: serialized_point -> Tot(bytes)
assume val _OS2ECP : bytes -> Tot(serialized_point)
assume val _I2OSP: value1: int -> n: int -> Tot(bytes)
assume val _OS2IP: bytes -> nat

assume val hash: a: bytes -> Tot(bytes)

val seqConcat : s1: seq 'a -> s2: seq 'a -> 
            Tot(r:seq 'a{Seq.length    r = Seq.length s1 + Seq.length s2})

let seqConcat s1 s2 = 
    FStar.Seq.append s1 s2             

val _helper_ECVRF_hash_to_curve : 
    ctr : nat -> input: bytes -> pk: bytes -> Tot(r: option serialized_point{isPointOnCurve r})(decreases(field - ctr))

let rec _helper_ECVRF_hash_to_curve ctr input pk = 
    let _CTR = _I2OSP ctr 4 in 
    let toHash = seqConcat input pk in 
    let toHash = seqConcat toHash _CTR in 
    let hash = hash toHash in 
    let possible_point = seqConcat positive_point_const hash in 
        if isPointOnCurve (Some possible_point) then Some possible_point 
        else
            let possible_point    = seqConcat negative_point_const hash in 
                if isPointOnCurve (Some possible_point) then Some possible_point 
                else 
                    if (ctr +1) < field 
                        then _helper_ECVRF_hash_to_curve (ctr+1) input pk 
                    else None    


val _ECVRF_hash_to_curve: input: bytes -> 
            public_key: (serialized_point) -> Tot(option serialized_point)            

let _ECVRF_hash_to_curve input public_key = 
    let ctr = 0 in 
    let pk = _ECP2OS public_key in 
    let point = _helper_ECVRF_hash_to_curve ctr input pk in point

assume val random:     max: nat -> Tot(random : nat {random <= max})    

val randBytes: max: nat -> Tot(bytes) 
let randBytes max = 
    let rand = random max in _I2OSP rand 32 (* in octets = log_2 field / 8  *)

val _ECVRF_hash_points : generator: serialized_point -> h:  serialized_point -> 
            public_key: serialized_point -> gamma : serialized_point -> 
            gk : serialized_point -> hk : serialized_point -> 
            Tot(int)

let _ECVRF_hash_points generator h public_key gamma gk hk = 
    let p = _ECP2OS generator in 
    let p = seqConcat p (_ECP2OS h) in 
    let p = seqConcat p (_ECP2OS public_key) in 
    let p = seqConcat p (_ECP2OS gamma) in 
    let p = seqConcat p (_ECP2OS gk) in 
    let p = seqConcat p (_ECP2OS hk) in 
    let h' = hash p in 
    let h = fst (FStar.Seq.split h' n) in 
    _OS2IP h

val _ECVRF_prove: input: bytes ->  public_key: serialized_point -> 
            private_key : bytes (* private key in this scope is a mupliplier of the generator *)
            -> generator : serialized_point-> Tot(option bytes) 
            (*) Tot(proof: bytes{Seq.len proof = 5 * n + 1}) *)

let _ECVRF_prove input public_key private_key generator = 
    let h = _ECVRF_hash_to_curve input public_key in 
        if isNone h then None (* trying to convert the hash to point, 
        if it was not possible returns None *)
        else 
            let h = get h in 
    let gamma = scalarMultiplication h private_key in 
    let k =  randBytes field in  (* random in sequence  *)
        let gk = scalarMultiplication generator k in  (* k< (2^8)^32 = 2^(8*32) = 2^(2^3 * 2^ 5 = 256) *) (* *)
        let hk = scalarMultiplication h k in 
    let c = _ECVRF_hash_points generator h public_key gamma gk hk in (*int*)
            let cq = op_Multiply c field in  (*int*)
            let cqmodq = cq % field in 
            let k_ = _OS2IP k in (* random was generated in the seq -> cast to nat *)
    let s = k_ - cqmodq (* int *) in 
            let fst = _ECP2OS gamma in 
            let snd = _I2OSP c n in 
            let thd = _I2OSP s ( op_Multiply 2 n) in 
    let pi = seqConcat fst (seqConcat snd thd) in Some pi
(*)

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
        pi: bytes {Seq.length pi = op_Multiply 5 n + 1} -> 
        Tot(tuple3 (option serialized_point) key key)


val _ECVRF_verify : generator: serialized_point ->  public_key : serialized_point ->
        pi: bytes {Seq.length pi = op_Multiply 5 n +1} -> 
        input : bytes -> 
        Tot(bool)

assume val bytesToInt: s: bytes -> Tot(int)

let _ECVRF_verify generator public_key pi input = 
    let gamma, c, s = _ECVRF_decode_proof pi in 
    if not(isPointOnCurve gamma) then false else
    if isNone gamma then false
        else let gamma = get gamma in 
    let pkc = scalarMultiplication public_key c in 
    let gs = scalarMultiplication generator s in 
    let u  = scalarAddition pkc gs in 
    let h = _ECVRF_hash_to_curve input public_key in 
        if isNone h then false
    else 
    let h = get h in 
    let gammac = scalarMultiplication gamma c in 
    let hs = scalarMultiplication h s in 
    let v = scalarAddition gammac hs in 
    let c_prime = _ECVRF_hash_points generator h public_key gamma u v in 
    (bytesToInt c) = c_prime