module Spec.ClaimChain

open FStar.Seq
open Spec.Claim

let bytes =  seq FStar.UInt8.t

type indentifier = 
|InitIndent : source: string -> identifier : option string -> indentifier

type keyEnt = 
|InitKeyEnt : source: string -> key: bytes -> keyEnt


type metadata = 
|InitMetadata: screen_name: option string ->
				real_name: option string -> 
				identifiers: list indentifier -> 
				keys: list keyEnt -> 
				metadata


type claimChain = 
|InitChaimChain : meta : metadata -> 
			claims: list claim -> 
			claimChain


private val getMetadata: c: claimChain -> metadata
let getMetadata c = 
	match c with 
	| InitChaimChain meta _ -> meta

private val getClaims : c: claimChain -> list claim
let getClaims c = 
	match c with 
	| InitChaimChain _ claims -> claims	

val addElement: c: claimChain -> e: 'a -> Tot ( r: claimChain{getClaims c = getClaims r})
let addElement c e = 
	let metadata = getMetadata c in 
	let blocks = getClaims c in 
	InitChaimChain metadata blocks