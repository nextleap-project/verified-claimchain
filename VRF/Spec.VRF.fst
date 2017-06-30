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
open Spec.SHA2_256



let bytes =  seq FStar.UInt8.t
let key = lbytes 32
let order = 2
let field = 100000000000

let n = 32

let positive_point_const = Seq.create 1 2uy
let negative_point_const = Seq.create 1 3uy

assume val scalarMultiplication: point:serialized_point -> k: scalar -> Tot serialized_point
assume val scalarAddition: p: serialized_point -> q: serialized_point -> Tot serialized_point
assume val isPointOnCurve: p: option serialized_point -> Tot(bool)
assume val deserializePoint: serialized_point -> Tot (tuple2 int int) (* I am just a wrapper *)

(* PRIME NUMBER CASE! *)

assume val _OS2ECP : bytes -> Tot(serialized_point)

val nat_to_uint8: x: int {x < 256} -> Tot(FStar.UInt8.t)
let nat_to_uint8 x = FStar.UInt8.uint_to_t x

val uint8_to_int : x: FStar.UInt8.t -> Tot(int)
let uint8_to_int x = FStar.UInt8.v x

val _helper_I2OSP: value: int -> n: nat -> counter : nat {counter <= n} -> s: bytes -> Tot (r: bytes {Seq.length r = Seq.length s})
let rec _helper_I2OSP value n counter s = 
    let mask = 256 in 
    let r = value %256 in 
    let r = nat_to_uint8 r in 
    let s = upd s counter r in 
    let number = value / mask  in 
        if (counter +1 <=n) then 
            _helper_I2OSP value n (counter +1) s
        else s

val _I2OSP: value1: int -> n: int{n > 0} -> Tot(r: bytes{Seq.length r = n})
let _I2OSP value1 n = 
    if (pow2 n <= value1) then Seq.create n 0uy
    else 
        let s = Seq.create n 0uy in 
         (_helper_I2OSP value1 n 0 s)

val _helper_OS2IP: s: bytes  -> counter: nat {counter < Seq.length s} -> number: int -> Tot (int)
let rec _helper_OS2IP s counter number = 
    let temp = Seq.index s counter in 
    let temp = uint8_to_int temp in 
    let number = number + (op_Multiply (pow2 8*counter) temp) in 
    if (counter + 1 = Seq.length s) then number else _helper_OS2IP s (counter+1) number

val _OS2IP: s: bytes{Seq.length s > 0} -> nat

let _OS2IP s = 
    _helper_OS2IP s 0 0

val seqConcat : s1: seq 'a -> s2: seq 'a -> 
            Tot(r:seq 'a{Seq.length    r = Seq.length s1 + Seq.length s2})

let seqConcat s1 s2 = 
    FStar.Seq.append s1 s2     

val _ECP2OS : gamma: serialized_point -> Tot(r: bytes {Seq.length r = (op_Multiply 2 n) + 1})
let _ECP2OS gamma = 
    let x,y = deserializePoint gamma in 
    let y' = y / 2 in 
    let x = _I2OSP x (op_Multiply 2 n) in 
    if y' = 0 then 
        seqConcat positive_point_const x
    else
        seqConcat negative_point_const x    

val hash: input: bytes{Seq.length input < pow2 61} -> Tot(bytes)    
let hash input = 
    Spec.SHA2_256.hash input

val _helper_ECVRF_hash_to_curve : 
    ctr : nat -> input: bytes{Seq.length input < pow2 61 - (op_Multiply 2 n) - 5 } -> pk: bytes -> Tot(r: option serialized_point{isPointOnCurve r})(decreases(field - ctr))

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


val _ECVRF_hash_to_curve: input: bytes{Seq.length input < pow2 61 - (op_Multiply 2 n) - 5 } -> 
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
    let p = _ECP2OS generator in (*2n +1 = 33 *)
    let p = seqConcat p (_ECP2OS h) in (* 66  *)
    let p = seqConcat p (_ECP2OS public_key) (* 99 *) in 
    let p = seqConcat p (_ECP2OS gamma)  (* still less than 2pow 61 *)in 
    let p = seqConcat p (_ECP2OS gk) in 
    let p = seqConcat p (_ECP2OS hk) in 
    let h' = hash p in 
    let h = fst (FStar.Seq.split h' n) in 
    _OS2IP h

val _ECVRF_prove: input: bytes {Seq.length input < pow2 61 - (op_Multiply 2 n) - 5 } ->  public_key: serialized_point -> 
            private_key : bytes (* private key in this scope is a mupliplier of the generator *)
            -> generator : serialized_point->  
            Tot(proof: option bytes {Some?proof ==> Seq.length (Some?.v proof) = (op_Multiply 5 n) + 1})
            (*Tot(proof: option bytes{Seq.length proof = 5 * n + 1})  *)

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
            let snd = _I2OSP c n in (* Seq length snd = n*)
            let thd = _I2OSP s ( op_Multiply 2 n) (* Seq.length thr = 2n *) in 
    let pi = seqConcat fst (seqConcat snd thd) in Some pi

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


val _ECVRF_decode_proof: 
        pi: bytes {Seq.length pi = op_Multiply 5 n + 1} -> 
        Tot(tuple3 (option serialized_point) bytes bytes) (* due to the fact that
         we do point multiplication using seq of bytes, 
        the operation to cast the value to int and to sequence 
        back is decided to be needless*)

let _ECVRF_decode_proof pi = 
    let gamma, cs = Seq.split pi ((op_Multiply 2 n)+1) in 
    let c, s = Seq.split cs n in 
    (Some(_OS2ECP gamma), c, s)


val _ECVRF_verify : generator: serialized_point ->  public_key : serialized_point ->
        pi: bytes {Seq.length pi = op_Multiply 5 n +1} -> 
        input : bytes -> 
        Tot(bool)

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
    (_OS2IP c) = c_prime
