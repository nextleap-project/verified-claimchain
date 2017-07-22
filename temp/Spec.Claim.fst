module Spec.Claim

open FStar.Seq
open SkipList2.Statement
open SkipList2.Insertion2
open SkipList2.Properties
open SkipList2.Search


open Spec.Claim.Key


assume val sign : input: bytes -> bytes
assume val verify : signature: bytes -> data: bytes -> Tot bool

assume val toBytes: input : 'a -> bytes
assume val concat: bytes-> bytes -> bytes

assume val signVerif: input: bytes -> 
	Lemma 
	(ensures (verify (sign input) input == true ))

(* Authenticity of information *)

type time = nat

type claim = 
	|InitClaim: 
		label: string -> 
		timeStamp: (k : time) ->  (* here I use time as some kind of nonce for signatures (in case of having
		not randomized sigs) *)
		test: list int -> 
		signature : bytes{verify signature (toBytes test) } -> claim (* test purposes*)
	|KeyBindingClaim: 
		label: string -> 
		timeStamp : (k : time { k> 0}) -> 
		meta: metadata -> 
		key: bytes -> 
		signature : bytes {verify signature (concat (toBytes meta) (toBytes key))}  -> claim
	|ClaimChainState: 
		label: string -> 
		timeStamp: (k : time { k> 0}) -> 
		id: bytes -> 
		state: bytes-> 
		signature : bytes{verify signature (concat id state)} -> claim
	|Revocation: 
		label : string -> 
		timeStamp : (k : time { k> 0}) -> 
		id: bytes -> 
		signature : bytes{verify signature id}-> claim

val getClaimLabel: cl: claim -> time
let getClaimLabel cl = 
	match cl with
	| InitClaim  label _ _ -> timeStamp
	| KeyBindingClaim  label _ _ _ -> timeStamp
	| ClaimChainState  label _ _ _  -> timeStamp
	| Revocation label _ _ -> timeStamp


val getClaimTimeStamp: cl: claim -> time
let getClaimTimeStamp cl = 
	match cl with
	| InitClaim _ timeStamp _  -> timeStamp
	| KeyBindingClaim _ timeStamp _ _ -> timeStamp
	| ClaimChainState _ timeStamp _ _  -> timeStamp
	| Revocation _ timeStamp _ -> timeStamp