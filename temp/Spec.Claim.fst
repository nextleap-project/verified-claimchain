module Spec.Claim

open FStar.Seq
open Spec.Claim.Keys
open Spec.Claim.Common
open Spec.Claim.Metadata

type claim = 
	|Empty: 
		label: string -> 
		timeStamp: (k : time) ->  (* here I use time as some kind of nonce for signatures (in case of having
		not randomized sigs) *)
		signature : bytes {verify signature (concat (toBytes label) (toBytes timeStamp))} ->  claim (* test purposes*)
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

val getClaimLabel: cl: claim -> string
let getClaimLabel cl = 
	match cl with
	| Empty  label _ _ -> label
	| KeyBindingClaim  label _ _ _ _ -> label
	| ClaimChainState  label _ _ _ _  -> label
	| Revocation label _ _ _-> label

assume val getClaimBody: cl: claim -> bytes

val getClaimTimeStamp: cl: claim -> time
let getClaimTimeStamp cl = 
	match cl with
	| Empty _ timeStamp _   -> timeStamp
	| KeyBindingClaim _ timeStamp _ _ _ -> timeStamp
	| ClaimChainState _ timeStamp _ _ _ -> timeStamp
	| Revocation _ timeStamp _ _ -> timeStamp
