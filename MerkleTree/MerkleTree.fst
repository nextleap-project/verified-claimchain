module MerkleTree

open HashFunction

assume val concatHashes:fst: suint8_p{length fst = v hash_hashsize_256} -> 
						snd : suint8_p{length snd = v hash_hashsize_256} -> 
						result : suint8_p{length result = length fst + length snd} -> 
						Stack unit (requires (fun h0 -> live h0 fst /\ like h0 snd))
						(ensures fun h0 _ h1 -> live h1 fst /\ live h1 snd /\ live h1 result /\ modifies_1 result h0 h1 ))

type MerkleTreeElement  = 
| MerkleTreeRoot:
	hash: suint8_p{length hash = v lengthHash} -> 
	leftLeaf: MerkleTreeElement  -> 
	rightLeaf: option(MerkleTreeElement) -> 
	root: option(MerkleTreeElement) -> MerkleTreeElement 
| MerkleTreeHashLeaf : 
	leaf: MerkleTreeElement ->
	hash: suint8_p{length hash = v lengthHash} -> 
	root : MerkleTreeElement ->MerkleTreeElement 
| MerkleTreeLeaf : 
	element: suint8_p -> 
	length : uint32_t{v len = length element} -> 
	root: MerkleTreeElement -> MerkleTreeElement


assume val equal: mt: MerkleTreeElement -> mt2 : MerkleTreeElement -> Tot (bool)

val isRoot: mt: MerkleTreeElement -> Tot(bool)
let isRoot mt = 
	match mt with 
	| MerkleTreeRoot _ _ _ _ -> true
	| _ -> false

val isHashLeaf: mt: MerkleTreeElement -> Tot(bool)
let isHashLeaf mt = 
	match mt with 
	| MerkleTreeHashLeaf _ _ _ -> true
	| _ -> false

val isTreeLeaf: mt: MerkleTreeElement -> Tot(bool)
let isTreeLeaf mt = 
	match mt with 
	|MerkleTreeLeaf _ _ _ -> true
	| _ -> false

val getRoot : mt : MerkleTreeElement{isTreeLeaf mt || isHashLeaf mt} -> Tot(MerkleTreeElement)
let getRoot mt = 
	match mt with 
	|MerkleTreeLeaf _ _ root -> root
	| MerkleTreeHashLeaf _ _ root -> root

val TreeLeafHash : leaf: MerkleTreeElement{isTreeLeaf leaf} -> root : MerkleTreeElement{isHashLeaf root /\ equal(getRoot length) (root) } -> 

(*)
val sha2_256:
  hash :suint8_p{length hash = v hash_hashsize_256} ->
  input:suint8_p ->
  len  :uint32_t{v len = length input} ->
  Stack unit
        (requires (fun h0 -> live h0 hash /\ live h0 input))
        (ensures  (fun h0 _ h1 -> live h1 hash /\ modifies_1 hash h0 h1))
(*)


