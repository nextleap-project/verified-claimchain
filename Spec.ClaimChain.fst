module Spec.ClaimChain

open FStar.Seq
open Spec.Claim
open SkipList2.Statement

open HashFunction
open FStar.Constructive

let bytes =  seq FStar.UInt8.t
(*)

type path = list bool

val get_elt:  #h:hash -> path:path -> tree:merkleTree (List.length path) h -> f: cmpClaim -> Tot data f
             (decreases path)
let rec get_elt #h path tree =
  match path with
    | [] -> MLeaf?.element tree
    | bit::path' ->
      if bit then
  get_elt #(MNode?.h1 tree) path' (MNode?.lnode tree)
      else
  get_elt #(MNode?.h2 tree) path' (MNode?.rnode tree)


(*
 * type for the proof stream which is a list of hashes and looked up data
 *)
type proof =
  | Mk_proof: data:data -> pstream:list hash -> proof

val lenp: proof -> Tot nat
let lenp p = List.length (Mk_proof?.pstream p)

val p_tail: p:proof{lenp p > 0} -> Tot proof
let p_tail p = Mk_proof (Mk_proof?.data p) (Cons?.tl (Mk_proof?.pstream p))

let p_data = Mk_proof?.data

let p_stream = Mk_proof?.pstream

(*
 * verifier takes as input a proof stream for certain lookup path
 * and computes the expected root node hash
 *)
val verifier: path:path -> p:proof{lenp p = List.length path} -> Tot hash
let rec verifier path p =
  match path with
    | [] -> hashFunc (serialize(p_data p))

    | bit::path' ->
      match p_stream p with
  | hd::_ ->
    let h' = verifier path' (p_tail p) in
    if bit then
      hashFunc (hashConcat h' hd)
    else
      hashFunc (hashConcat hd h')

(*
 * prover function, generates a proof stream for a path
 *)


val prover: #h:hash ->
            path:path ->
            tree:merkleTree (List.length path) h ->
            Tot (p:proof{lenp p = List.length path})
      (decreases path)

let rec prover #h path tree =
  match path with
    | [] -> Mk_proof (MLeaf?.element tree) []
    | bit::path' ->
      let MNode #dc #hl #hr left right  = tree in
      if bit then
  let p = prover path' left in
  Mk_proof (p_data p) (hr::(p_stream p))
      else
  let p = prover path' right in
  Mk_proof (p_data p) (hl::(p_stream p))

(*
 * correctness theorem: honest prover's proof stream is accepted by the verifier
 *)

 (*)
val correctness: #h:hash ->
                 path:path ->
                 tree:merkleTree (List.length path) h ->
                 p:proof{p = prover path tree} ->
                 Lemma (requires True) (ensures (verifier path p = h))
                 (decreases path)
let rec correctness #h path tree p =
  match path with
    | [] -> ()
    | bit::path' ->
      if bit then
  correctness #(MNode?.h1 tree) path' (MNode?.lnode tree) (p_tail p)
      else
  correctness #(MNode?.h2 tree) path' (MNode?.rnode tree) (p_tail p)

(*
 * We prove a standard security definition that if verifier can be tricked into
 * accepting a proof of existence of an element, when the element is not actually
 * present, then we can provide a constructive proof of hash collision
 *)

type hash_collision =
    cexists (fun n -> cexists (fun (s1:data) -> cexists (fun (s2:data) ->
             u:unit{ s1 = hashFunc s2 /\ not (s1 = s2)})))

(*
 * security theorem: Only way a verifier can be tricked into accepting proof
 * stream for an non existent element is if there is a hash collision.
 *)
val security: #h:hash ->
              path:path ->
              tree:mtree (len path) h ->
              p:proof{lenp p = len path /\ verifier path p = h /\
                      not (get_elt path tree = p_data p)} ->
              Tot hash_collision
              (decreases path)
let rec security #h path tree p =
  match path with
    | [] -> ExIntro data_size (ExIntro (p_data p) (ExIntro (L?.data tree) ()))

    | bit::path' ->
      let N #dc #h1 #h2 left right = tree in
      let h' = verifier path' (p_tail p) in
      let hd = Cons?.hd (p_stream p) in
      if bit then
  if h' = h1 then
    security path' left (p_tail p)
  else
    ExIntro (hash_size + hash_size) (ExIntro (Concat h1 h2) (ExIntro (Concat h' hd) ()))
      else
  if h' = h2 then
    security path' right (p_tail p)
  else
    ExIntro (hash_size + hash_size) (ExIntro (Concat h1 h2) (ExIntro (Concat hd h') ()))

*)
*)
type claimChain (f: cmpClaim ) = 
	|InitClaimChain : 
			nonce: nat ->
			id: bytes -> (* reference to ClaimChain to have claims that states ClaimChainState and revocation
			equally it could be used as a ref to chaimChain = skipList + index *) 
			meta : metadata -> 
			claims: claimCh f -> 
			state: bytes -> (* hash? *)
			hash: bytes {hash = (let c1 = concat (toBytes nonce) id in 
									let c2 = concat c1 (toBytes meta) in 
										let c3 = concat c2 (toBytes claims) in 
											let c4 = concat c3 state in 
												c4
								)
						} -> 
			claimChain f


type hash = seq nat
type data (f: cmpClaim )  = claimChain f

assume val serialize: #f: cmpClaim ->  d: data f -> Tot(seq nat)

noeq type merkleTree: level:nat -> h: hash -> Type  = 
| MLeaf: #f: cmpClaim -> element : data f -> merkleTree 0 (hashFunc (serialize element))
| MNode: #level: nat -> #h1: hash -> #h2 : hash -> 
		lnode: merkleTree level h1 ->
		rnode: merkleTree level h2 -> 
		merkleTree (level+1) (hashConcat h1 h2)

val mtClChain: f: cmpClaim ->  cl: claimChain f -> merkleTree 0 (hashFunc (serialize cl))