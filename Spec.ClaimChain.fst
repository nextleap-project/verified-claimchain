module Spec.ClaimChain

open FStar.Seq
open Spec.Claim

let bytes =  seq FStar.UInt8.t

type claimChain = 
|InitChaimChain : 
			id: bytes -> 
			meta : metadata -> 
			claims: list claim -> 
			state: bytes -> 
			claimChain


private val getMetadata: c: claimChain -> metadata
let getMetadata c = 
	match c with 
	| InitChaimChain _ meta _ _ -> meta

private val getClaims : c: claimChain -> list claim
let getClaims c = 
	match c with 
	| InitChaimChain _ _ claims _ -> claims	

val addElement: c: claimChain -> e: 'a -> Tot ( r: claimChain{getClaims c = getClaims r})
let addElement c e = 
	let metadata = getMetadata c in 
	let blocks = getClaims c in 
	InitChaimChain c.id metadata blocks c.state