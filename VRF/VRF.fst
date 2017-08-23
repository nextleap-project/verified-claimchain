module VRF

open FStar.HyperStack
open FStar.ST
open FStar.Buffer

open Hacl.UInt8
open Hacl.UInt32
open FStar.UInt32

open Hacl.Bignum25519
open Hacl.Impl.Ed25519.PointAdd

open Hacl.Impl.Ed25519.ExtPoint
open Hacl.Impl.Ed25519.PointCompress

type bytes = buffer FStar.UInt8.t
type hbytes = buffer Hacl.UInt8.t

private let uint32_t  = FStar.UInt32.t
private let uint64_t = FStar.UInt64.t


let max_input_len_8 = pow2 61

(* SHA2 *)
let size_word = 4ul 
let size_hash_w   = 8ul 
let size_block_w  = 16ul  // 16 words (Working data block size)
let size_hash     = size_word *^ size_hash_w

let n = 32ul


assume val hash: hash: bytes {length hash = v size_hash} ->
	input: bytes {length input < max_input_len_8 /\ disjoint hash input} -> 
	len : uint32_t {v len = length input} -> 
	Stack unit 
		(requires 
			(fun h0 -> live h0 hash /\ live h0 input))
		(ensures	
			(fun h0 _ h1 -> live h0 input /\ live h0 hash /\ live h1 hash /\ modifies_1 hash h0 h1))

val scalarAddition:
  out:point ->
  p:point{disjoint p out} ->
  q:point{disjoint q out} ->
  Stack unit
    (requires (fun h -> live h out /\ live h p /\ live h q  /\
      (
        let x1 = as_seq h (getx p) in
        let y1 = as_seq h (gety p) in
        let z1 = as_seq h (getz p) in
        let t1 = as_seq h (gett p) in

        let x2 = as_seq h (getx q) in
        let y2 = as_seq h (gety q) in
        let z2 = as_seq h (getz q) in
        let t2 = as_seq h (gett q) in
        red_513 x1 /\ red_513 y1 /\ red_513 z1 /\ red_513 t1 /\
        red_513 x2 /\ red_513 y2 /\ red_513 z2 /\ red_513 t2)
      ))
    (ensures (fun h0 _ h1 -> live h1 out /\ live h0 p /\ live h0 q /\ modifies_1 out h0 h1 /\
      (
        let x1 = as_seq h0 (getx p) in
        let y1 = as_seq h0 (gety p) in
        let z1 = as_seq h0 (getz p) in
        let t1 = as_seq h0 (gett p) in
        let x2 = as_seq h0 (getx q) in
        let y2 = as_seq h0 (gety q) in
        let z2 = as_seq h0 (getz q) in
        let t2 = as_seq h0 (gett q) in
        let x3 = as_seq h1 (getx out) in
        let y3 = as_seq h1 (gety out) in
        let z3 = as_seq h1 (getz out) in
        let t3 = as_seq h1 (gett out) in
        (seval x3, seval y3, seval z3, seval t3) ==
          Spec.Ed25519.point_add (seval x1, seval y1, seval z1, seval t1)
                                 (seval x2, seval y2, seval z2, seval t2)
        /\ red_513 x3 /\ red_513 y3 /\ red_513 z3 /\ red_513 t3)
  ))

let scalarAddition out p q = 
	point_add out p q

assume val scalarMultiplication : out: point -> p: point ->  k:buffer Hacl.UInt8.t{length k = 32 } -> 
	Stack unit
		(requires
			(fun h0 -> live h0 p /\ live h0 k /\ live h0 out)
		)
		(ensures
			(fun h0 _ h1 -> live h1 p /\ live h1 k /\ live h0 out /\ modifies_1 k h0 h1)	
		)

assume val isPointOnCurve: p: point -> Stack bool
	(requires (fun h0 -> live h0 p))	
	(ensures (fun h0 _ h1 -> live h1 p))	

val _ECP2OS: out: hbytes{length out = 32} -> p: point -> Stack unit 
	(requires
		(fun h0 -> live h0 out /\ live h0 p  /\
			red_513 (as_seq h0 (Hacl.Impl.Ed25519.ExtPoint.getx p)) /\
			red_513 (as_seq h0 (Hacl.Impl.Ed25519.ExtPoint.gety p)) /\
			red_513 (as_seq h0 (Hacl.Impl.Ed25519.ExtPoint.getz p)) /\
			red_513 (as_seq h0 (Hacl.Impl.Ed25519.ExtPoint.gett p))
		)
	)
	(ensures
		(fun h0 _ h1 -> 
			live h0 out /\ live h1 out /\ live h1 p /\  modifies_1 out h0 h1 
			(*/\ h1.[out] == Spec.Ed25519.point_compress(Hacl.Impl.Ed25519.ExtPoint.as_point h0 p)*)
		)
	)

let _ECP2OS out p = point_compress out p



assume val random: random: bytes {length random = 32} -> 	
	Stack unit 
		(requires 
			(fun h0 -> live h0 random)
		)
		(ensures 
			(fun h0 _ h1 -> live h0 random /\ modifies_1 random h0 h1)
		)

assume val _ECVRF_hash_to_curve:
	output: point -> 
	input: bytes {length input < max_input_len_8 - 36} ->
	len_input : uint32_t {v len_input = length input} -> 
	public_key: point -> 
	Stack bool 
		(requires
			(fun h0 -> live h0 output /\ live h0 input /\ live h0 public_key)
		)
		(ensures
			(fun h0 _ h1 -> live h1 output /\ live h1 input /\ live h1 public_key /\ modifies_1 output h0 h1)
		)

assume val _ECVRF_hash_points: out: bytes -> 
	p1: point -> 
	p2:point -> 
	p3: point ->
	p4: point -> 
	p5: point -> 
	p6: point -> 
	Stack unit 
		(requires
			(fun h0 ->live h0 out /\ live h0 p1 /\  live h0 p2 /\  live h0 p3 /\  live h0 p4 /\  live h0 p5 /\  live h0 p6 )
		)

		(ensures
			(fun h0 _ h1 -> live h0 out /\ live h0 p1 /\  live h0 p2 /\  
			live h0 p3 /\  live h0 p4 /\  live h0 p5 /\  live h0 p6 /\ modifies_1 out h0 h1 )
		)

assume val pointCreate: unit -> Stack (p:point)
		(requires 
			(fun h0 -> true)
		)
		(ensures
			(fun h0 r h1 -> true)
		)
(*))
assume val testFunc : p: point -> Stack unit 
	(requires
		(fun h0 -> live h0 p)
	)
	(ensures
		(fun h0 _ h1 -> live h1 p)
	)

val a: unit -> Stack unit
	(requires (fun h0 -> true))
	(ensures (fun h0 _ h1 -> true))

let a () = 
	let point = pointCreate () in 
	testFunc point; ()
*)



assume val bytesMultiplication: out: bytes -> m1: bytes -> m2 : uint64_t -> mod: uint64_t -> Stack unit 
	(requires (fun h0 -> live h0 out /\ live h0 m1))
	(ensures (fun h0 _ h1 -> live h1 m1 /\ modifies_1 out h0 h1))

assume val bytesInverse: out: bytes -> m: bytes -> Stack unit
	(requires(fun h0 -> live h0 out /\ live h0 m))
	(ensures (fun h0 _ h1 -> live h1 m /\ modifies_1 out h0 h1))	

assume val bytesAddition: out: bytes -> m1: bytes -> m2: bytes -> Stack unit
	(requires (fun h0 -> live h0 out /\ live h0 m1 /\ live h0 m2))
	(ensures (fun h0 _ h1 -> live h1 out /\ modifies_1 out h0 h1 /\ live h1 m1 /\ live h1 m2))

assume val bytesConcat: out: bytes -> m1: bytes -> m2: bytes -> Stack unit
	(requires (fun h0 -> live h0 out /\ live h0 m1 /\ live h0 m2))
	(ensures (fun h0 _ h1 -> live h1 out /\ live h1 m1 /\ live h1 m2 /\ modifies_1 out h0 h1))

assume val bytesSplit: out: bytes -> m: bytes ->  p1: int -> p2: int -> Stack unit
	(requires (fun h0 -> live h0 out /\ live h0 m))
	(ensures (fun h0 _ h1 -> live h1 out /\ live h1 m /\ modifies_1 out h0 h1 ))

val _ECVRF_prove: 
	proof: bytes {length proof = v (n *^ 4ul) } ->
	input: bytes {length input < max_input_len_8 - 36  } ->
	len_input : uint32_t {v len_input = length input} -> 
	public_key: point -> 
	private_key: buffer Hacl.UInt8.t {length private_key = 32} -> 
	generator: point -> 
	field: uint64_t -> 
	Stack bool 
		(requires 
			(fun h0 -> live h0 input /\ live h0 public_key /\ live h0 private_key /\ live h0 generator /\ live h0 proof )
		)
		(ensures
			(fun h0 _ h1 -> live h0 input /\ live h0 public_key /\ 
			live h0 private_key /\ live h0 generator /\ live h0 proof /\ modifies_1 proof h0 h1)
		)

let _ECVRF_prove proof input len_input public_key private_key generator field  = 
	let h = pointCreate() in 
	let hashResult = _ECVRF_hash_to_curve h input len_input public_key in 
		if hashResult = false then false else 
		let gamma = pointCreate () in 
	scalarMultiplication gamma h private_key; 
		let k = create 0uy 32ul in 
		let gk = pointCreate() in 
		let hk = pointCreate() in 
	random k; 
	scalarMultiplication gk generator k;
	scalarMultiplication hk h k;
		let c = create 0uy 32ul in
	_ECVRF_hash_points c generator h public_key gamma gk hk; 
		let cqmod = create 0uy 32ul in 
	bytesMultiplication cqmod c field field; (* smaller than field*)
	bytesInverse cqmod cqmod;
		let s = create 0uy 32ul in 
	bytesAddition s k cqmod;
		let fstsnd = create 0uy 64ul in 
		let fst = create 0uy 32ul in 
	_ECP2OS fst gamma;
	bytesConcat fstsnd fst c;
	bytesConcat proof fstsnd s; true

val _ECVRF_proof2hash: out: bytes -> proof: bytes -> Stack unit
(requires (fun h0 -> live h0 out /\ live h0 proof))
(ensures (fun h0 _ h1 -> live h1 out /\ live h1 proof))

let _ECVRF_proof2hash out proof = 
	bytesSplit out proof 0 1

assume val _ECVRF_decode_proof: gamma:  point -> c: bytes -> s : bytes -> pi: bytes -> Stack bool
(requires (fun h0 -> live h0 gamma /\ live h0 c /\ live h0 s /\ live h0 pi))
(ensures (fun h0 _ h1 -> live h1 gamma /\ live h1 c /\ live h1 s /\ 
	live h1 pi /\ modifies_1 gamma h0 h1 /\ modifies_1 c h0 h1 /\ modifies_1 s h0 h1 ))


val _ECVRF_verify: generator: point -> public_key : point -> pi: bytes -> input: bytes ->
len_input : uint32_t {v len_input = length input} ->  Stack bool
(requires (fun h0 -> live h0 generator /\ live h0 public_key /\ live h0 pi /\ live h0 input))
(ensures (fun h0 _ h1 -> live h1 generator /\ live h1 public_key /\ live h1 pi /\ live h1 input))

let _ECVRF_verify generator public_key pi input len_input = 
		let gamma = pointCreate () in 
		let c = create 0uy 32ul in  
		let s = create 0uy 32ul in 
	let decoded = _ECVRF_decode_proof gamma c s pi in 
		if not(decoded)  then false 
		else if not(isPointOnCurve gamma) then false
		else 
		let pkc = pointCreate() in 
		let gs = pointCreate() in 
	scalarMultiplication pkc public_key c;
	scalarMultiplication gs generator s;
		let u = pointCreate () in 
	scalarAddition u pkc gs; 
		let h = pointCreate () in 
	let h_ = _ECVRF_hash_to_curve h input len_input public_key in 
		if not(h_) then false else 
		let gammac = pointCreate() in 
		let hs = pointCreate() in 
	scalarMultiplication gammac gamma c; 
	scalarMultiplication hs h s; 	
		let v = pointCreate() in 
	scalarAddition v gammac hs; 
		let c_prime = create 0uy 32ul in 
	_ECVRF_hash_points c_prime generator h public_key gamma u v;
	(c = c_prime)