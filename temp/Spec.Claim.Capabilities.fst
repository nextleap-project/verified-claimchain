module Spec.Claim.Capabilities

open FStar.Seq
open Spec.Claim
open Spec.Claim.Metadata
open Spec.Claim.Keys

type key = bytes

assume val sharedSecret : k1: key -> k2: key -> Tot key
assume val h3: 'a -> bytes
assume val h4: 'a -> bytes

assume val enc : key: key -> plain : bytes -> Tot bytes



val encodeCapability : privateKeyDH : key -> 
		publicKeyReader: key -> 
		nonce: bytes -> 
		claimLabel: string -> 
		k: bytes 0 -> Tot(tuple2 (la: bytes) (pa : bytes))

let encodeCapability privateKeyDH publicKeyReader nonce claimLabel k = 
	let s = sharedSecret privateKeyDH publicKeyReader in 
	let claimLabel = toBytes claimLabel in 
	let la1 = concat nonce s in 
	let body = concat la1 claimLabel in 
	let la = h3 body in 
	let key = h4 body in 
	let pa = enc key k in 
	(la, pa)