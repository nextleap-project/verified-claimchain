module M
open FStar.List.Tot
open FStar.Seq
open FStar.UInt8

type bytes = seq nat
type hash_t = bytes

assume val hash: 'a -> Tot bytes
assume val concat : a: bytes -> b: bytes -> Tot bytes


type merkleTree (#a : eqtype) : nat -> hash_t ->Type = 
    |MLeaf: element : a -> merkleTree #a 0 (hash element)
    |MNode: #level: nat -> #h1: hash_t -> #h2: hash_t -> 
        lnode: merkleTree #a level h1->
        rnode: merkleTree #a level h2-> 
        merkleTree #a (level+1) (concat h1 h2)


val merkleTreeGeneration       