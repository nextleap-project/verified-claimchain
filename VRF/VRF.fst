module VRF

open FStar.HyperStack
open FStar.ST
open FStar.Buffer

open Hacl.UInt8
open Hacl.UInt32
open FStar.UInt32

open Hacl.Impl.Ed25519.ExtPoint


type bytes = buffer FStar.UInt8.t
private let uint32_t  = FStar.UInt32.t


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

assume val scalarAddition: out: point ->
    p: point -> 
    q: point -> 
    Stack unit 
        (requires
            (fun h0 -> live h0 out /\ live h0 p /\ live h0 q)
        )
        (ensures 
            (fun h0  _ h1 -> live h0 out /\ live h0 p /\ live h0 q /\ modifies_1 out h0 h1)
        )

assume val scalarMultiplication : out: point -> p: point ->  k:buffer Hacl.UInt8.t{length k = 32 } -> 
    Stack unit
        (requires
            (fun h0 -> live h0 p /\ live h0 k /\ live h0 out)
        )
        (ensures
            (fun h0 _ h1 -> live h0 p /\ live h0 k /\ live h0 out /\ modifies_1 k h0 h1)    
        )


val _ECVRF_prove:  pbuffer: point ->
    input: bytes {length input < max_input_len_8 - 36  } ->
    len_input : uint32_t {v len_input = length input} -> 
    public_key: point -> 
    private_key: buffer Hacl.UInt8.t {length private_key = 32} -> 
    generator: point -> 
    proof: bytes {length proof = v (n *^ 4ul) } ->
    Stack unit 
        (requires 
            (fun h0 -> live h0 input /\ live h0 public_key /\ live h0 private_key /\ live h0 generator /\ live h0 proof )
        )
        (ensures
            (fun h0 _ h1 -> live h0 input /\ live h0 public_key /\ live h0 private_key /\ live h0 generator /\ live h0 proof /\ modifies_1 proof h0 h1)
        )

assume val random: random: bytes {length random = 32} ->     
    Stack unit 
        (requires 
            (fun h0 -> live h0 random)
        )
        (ensures 
            (fun h0 _ h1 -> live h0 random /\ modifies_1 random h0 h1)
        )

assume val _ECVRF_hash_to_curve:hash: bytes -> 
    input: bytes {length input < max_input_len_8 - 36} ->
    len_input : uint32_t {v len_input = length input} -> 
    public_key: point -> 
    Stack unit 
        (requires
            (fun h0 -> live h0 hash /\ live h0 input /\ live h0 public_key)
        )
        (ensures
            (fun h0 _ h1 -> live h0 hash /\ live h0 input /\ live h0 public_key /\ modifies_1 hash h0 h1)
        )

assume val _ECVRF_hash_points: out: point -> 
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

let _ECVRF_prove gamma gk hk input len_input public_key private_key generator proof = 
        let hash = create 0uy 32ul in 
    l_ECVRF_hash_to_curve hash input len_input public_key; 
    scalarMultiplication gamma hash private_key; 
        let rbuffer = create 0uy 32ul in 
    random rbuffer; 
    scalarMultiplication gk generator k;
    scalarMultiplication hk h k;
        let hashpoint = create 0uy 32ul;
    _ECVRF_hash_points hashpoint generator h public_key gamma gk hk;