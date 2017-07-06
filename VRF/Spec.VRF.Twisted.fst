module Spec.VRF

open FStar.UInt32
open FStar.UInt8
open FStar.Seq
open FStar.Option

open FStar.Mul
open FStar.Seq
open FStar.UInt


open FStar.Endianness
open Spec.Curve25519
open Spec.Ed25519
(*)
open Spec.SHA2_256
*)


let bytes =  seq FStar.UInt8.t
let key = lbytes 32
let order = 2
let field = 100000000000

let n = 32

let positive_point_const = Seq.create 1 2uy
let negative_point_const = Seq.create 1 3uy

type twisted_edward_point = ext_point

val scalarMultiplication : point : twisted_edward_point -> k: bytes -> Tot twisted_edward_point
let scalarMultiplication point k = 
    Spec.Ed25519.point_mul k point

val scalarAddition : p : twisted_edward_point -> q: twisted_edward_point -> Tot twisted_edward_point
let scalarAddition p q = 
    Spec.Ed25519.point_add p q 

val isPointOnCurve: point : option twisted_edward_point -> Tot bool
let isPointOnCurve point =
    if isNone point then false else
    let point = get point in 
    let px, py, pz, pt = point in 
    let zinv = modp_inv pz in 
    let x = fmul px zinv in 
    let y = fmul py zinv in 
    let x2 = fmul x x in 
    let x3 = fmul x2 x in 
    let y2 = fmul y y in 
    let ax2 = fmul 486662 x2 in 
    let r = y2 - x3 - ax2 - x in 
    (r%prime) = 0

val serializePoint : point: twisted_edward_point -> Tot bytes
let serializePoint point = point_compress point

val deserializePoint : b: bytes{Seq.length b = 32} -> Tot (option twisted_edward_point)
let deserializePoint b = point_decompress b

val _OS2ECP : point: bytes -> Tot(option twisted_edward_point)
let _OS2ECP point = deserializePoint point

val _ECP2OS : gamma: twisted_edward_point -> Tot(r: bytes {Seq.length r = 32})
let _ECP2OS gamma = serializePoint gamma

val nat_to_uint8: x: int {x < 256} -> Tot(FStar.UInt8.t)
let nat_to_uint8 x = FStar.UInt8.uint_to_t (to_uint_t 8 x)

val uint8_to_int : x: FStar.UInt8.t -> Tot(int)
let uint8_to_int x = FStar.UInt8.v x

val _helper_I2OSP: value: nat -> s: bytes -> counter : nat {counter < Seq.length s} -> 
        Tot (r: bytes {Seq.length r = Seq.length s})(decreases (Seq.length s - counter))
let rec _helper_I2OSP value s counter  = 
    let mask = 256 in 
    let r = value % mask in 
    let r = nat_to_uint8 r in 
    let s = upd s counter r in 
    let number = value / mask  in 
        if (counter +1 <Seq.length s) then 
            _helper_I2OSP value s (counter +1)
        else s

val _I2OSP: value: nat -> n: int{n > 0} -> Tot(r: bytes{Seq.length r = n})
let _I2OSP value n = 
    if (pow2 n <= value) then Seq.create n 0uy
    else 
        let s = Seq.create n 0uy in 
         (_helper_I2OSP value s 0)

val _helper_OS2IP: s: bytes  -> counter: nat {counter < Seq.length s} -> number: nat -> 
    Tot (nat)(decreases (Seq.length s - counter))
let rec _helper_OS2IP s counter number = 
    let temp = Seq.index s counter in 
    let temp = uint8_to_int temp in 
    let number = number + (op_Multiply (pow2 8*counter) temp) in 
    if (counter + 1 = Seq.length s) then 
        number 
    else _helper_OS2IP s (counter+1) number

val _OS2IP: s: bytes{Seq.length s > 0} -> nat

let _OS2IP s = 
    _helper_OS2IP s 0 0

val seqConcat : s1: seq 'a -> s2: seq 'a -> 
            Tot(r:seq 'a{Seq.length    r = Seq.length s1 + Seq.length s2})

let seqConcat s1 s2 = 
    FStar.Seq.append s1 s2     

val hash: input: bytes{Seq.length input < pow2 61} -> Tot(bytes)    
let hash input = 
    Spec.SHA2_256.hash input

val _helper_ECVRF_hash_to_curve : 
    ctr : nat -> input: bytes{Seq.length input < pow2 61 - (op_Multiply 2 n) - 5 } -> pk: bytes ->
        Tot(r: option twisted_edward_point{isPointOnCurve r})(decreases(field - ctr)) 

let rec _helper_ECVRF_hash_to_curve ctr input pk = 
    let _CTR = _I2OSP ctr 4 in 
    let toHash = seqConcat input pk in 
    let toHash = seqConcat toHash _CTR in 
    let hash = hash toHash in 
    let possible_point = seqConcat positive_point_const hash in 
    let possible_point = _OS2ECP possible_point in 
    if isNone possible_point then None else
        if isPointOnCurve possible_point then possible_point 
        else
            let possible_point    = seqConcat negative_point_const hash in 
            let possible_point = _OS2ECP possible_point in 
            if isNone possible_point then None else
                if isPointOnCurve possible_point then possible_point 
                else 
                    if (ctr +1) < field 
                        then _helper_ECVRF_hash_to_curve (ctr+1) input pk 
                    else None    

val _ECVRF_hash_to_curve: input: bytes{Seq.length input < pow2 61 - (op_Multiply 2 n) - 5 } -> 
            public_key: (twisted_edward_point) -> Tot(option twisted_edward_point)            

let _ECVRF_hash_to_curve input public_key = 
    let ctr = 0 in 
    let pk = _ECP2OS public_key in 
    let point = _helper_ECVRF_hash_to_curve ctr input pk in point

assume val random:     max: nat -> Tot(random : nat {random <= max})    

val randBytes: max: nat -> Tot(bytes) 
let randBytes max = 
    let rand = random max in _I2OSP rand 32 (* in octets = log_2 field / 8  *)

val _ECVRF_hash_points : generator: twisted_edward_point -> h:  twisted_edward_point -> 
            public_key: twisted_edward_point -> gamma : twisted_edward_point -> 
            gk : twisted_edward_point -> hk : twisted_edward_point -> 
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

val _ECVRF_prove: input: bytes {Seq.length input < pow2 61 - (op_Multiply 2 n) - 5 } ->  public_key: twisted_edward_point -> 
            private_key : bytes (* private key in this scope is a mupliplier of the generator *)
            -> generator : twisted_edward_point->  
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
        Tot(tuple3 (option twisted_edward_point) bytes bytes) (* due to the fact that
         we do point multiplication using seq of bytes, 
        the operation to cast the value to int and to sequence 
        back is decided to be needless*)

let _ECVRF_decode_proof pi = 
    let gamma, cs = Seq.split pi ((op_Multiply 2 n)+1) in 
    let c, s = Seq.split cs n in 
    ((_OS2ECP gamma), c, s)


val _ECVRF_verify : generator: twisted_edward_point ->  public_key : twisted_edward_point ->
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