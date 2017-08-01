module Spec.Claim.MerkleTree

open FStar.Seq
open FStar.Mul
open FStar.List.Tot

open Spec.Claim.Common

type hash_t = bytes

type merkleTree (#a : eqtype) : nat -> hash_t ->Type = 
    |MLeaf: element : a -> merkleTree #a 0 (hash (toBytes element))
    |MNode: #level: nat -> #h1: hash_t -> #h2: hash_t -> 
        lnode: merkleTree #a level h1->
        rnode: merkleTree #a level h2-> 
        merkleTree #a (level+1) (concat h1 h2)


type merklePair (#a: eqtype) (n:nat) = h:hash_t & (merkleTree #a n h)


val _merkleTreeGenerationL0: #a: eqtype -> l:list a -> Tot (r: list (merklePair #a 0){List.length l = List.length r})
        (decreases (List.length l))

let rec _merkleTreeGenerationL0 #a l = 
    match l with
    | hd1:: tl ->let h = hash (toBytes hd1) in 
                    let element = (|h, MLeaf hd1|)
                    in  List.append [element] (_merkleTreeGenerationL0 #a tl)
    | [] -> [] 

val merkleTreeGenerationL0: #a: eqtype ->k: nat ->  l: list a {List.length l = pow2 k }->
    Tot (r: list (merklePair #a 0) {List.length r = List.length l})

let merkleTreeGenerationL0 #a k l = 
    _merkleTreeGenerationL0 #a l

val _merkleTreeGenerationLn: #a: eqtype -> level: nat-> l: list (merklePair #a level) {List.length l % 2 = 0}->
    ML (r: list (merklePair #a (level+1)){List.length r = List.length l /2})
    (*Tot(r: list (merklePair #a (level+1)) {List.length l = pow2 (k-1)})*)

let rec _merkleTreeGenerationLn #a level l = 
    assert (List.length l % 2 = 0);
    match l with 
    | hd::hd1::tl -> let (|hd_hash,hd_body|) = hd in 
                     let (|hd1_hash, hd1_body|) = hd1 in 
                     let node = MNode #a #level #hd_hash #hd1_hash hd_body hd1_body in
                     let hash = concat hd_hash hd1_hash in 
                     let element = (|hash, node|) in 
                     assert(List.length tl = List.length l - 2); 
                     List.append [element] (_merkleTreeGenerationLn #a level tl)
    | [] -> []


val merkleTreeGenerationLn: #a: eqtype -> level: nat -> k: nat -> l: list(merklePair #a level) {List.length l = pow2 k /\ k>0} ->
    ML (r:list (merklePair #a (level +1)) {List.length r = pow2 (k-1)})

let merkleTreeGenerationLn #a level k l = 
    _merkleTreeGenerationLn #a level l 

val _merkleListGeneration: #a: eqtype -> level: nat -> k: nat -> l: list(merklePair #a level){List.length l = pow2 k /\ k > 0} -> ML (hash_t)
let rec _merkleListGeneration #a level k l = 
    let l_new = merkleTreeGenerationLn #a level k l in  
        assert (List.length l_new = pow2 (k-1)); 
    if (List.length l_new = 1) then
            (    
                assert ((k-1) = 0);
                let elem = hd l_new in 
                let (|hash, b|) = elem 
                in hash
            )
    else if (List.length l_new > 1) then 
        (
            assert ((k-1) > 0);
            _merkleListGeneration #a (level+1) (k-1) l_new
        )
    else 
        Seq.createEmpty

val merkleListGeneration: #a: eqtype -> k: nat ->  l: list a{List.length l = pow2 k} -> ML (hash_t)
let merkleListGeneration #a k l = 
    let treeLeafs = merkleTreeGenerationL0 #a k l in 
    if (List.length treeLeafs = 1) then 
            (
                let elem = hd treeLeafs in 
                let (|hash, body|) = elem in 
                hash
            )
    else 
        (
            assert (k>0);
             _merkleListGeneration #a 0 k treeLeafs
        )

assume val queryMerkleTree: hash: bytes -> key: bytes -> Tot bytes
