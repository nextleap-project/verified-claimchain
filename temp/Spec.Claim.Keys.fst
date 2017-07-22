module Spec.Claim.Keys

open FStar.Seq
open SkipList2.Statement
open SkipList2.Insertion2
open SkipList2.Properties
open SkipList2.Search

let bytes =  seq FStar.UInt8.t

type keyEnt = 
|InitKeyEnt : source: string -> key: bytes -> keyEnt
|PkSig: key : bytes -> keyEnt
|PkVRF : key : bytes -> keyEnt 
|PkDH : key : bytes -> keyEnt

val isKeyEntPkSig: k: keyEnt -> Tot bool
let isKeyEntPkSig k = 
	match k with 
	|PkSig _ -> true 
	|_ -> false


val isKeyEntPkVRF: k: keyEnt -> Tot bool
let isKeyEntPkVRF k = 
	match k with 
	|PkVRF _ -> true 
	|_ -> false

val isKeyEntPkDH: k: keyEnt -> Tot bool
let isKeyEntPkDH k = 
	match k with 
	|PkDH _ -> true 
	|_ -> false

type cryptoKeyEnt = 
| CryptoKeyEnt : keys: list keyEnt
	{
	(exists (k: keyEnt). isKeyEntPkSig k == true) /\
	(exists (l: keyEnt). isKeyEntPkDH l == true) /\
	(exists (m: keyEnt). isKeyEntPkVRF m == true)
	} -> cryptoKeyEnt



