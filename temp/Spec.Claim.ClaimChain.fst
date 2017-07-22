module Spec.ClaimChain

open FStar.Seq
open Spec.Claim
open SkipList2.Statement

open HashFunction
open FStar.Constructive

open Spec.Claim.Metadata
open Spec.Claim.Keys


let bytes =  seq FStar.UInt8.t

type time = nat

assume val sign : input: bytes -> Tot bytes
assume val verify : signature: bytes -> data: bytes -> Tot bool

assume val toBytes: input : 'a ->Tot bytes
assume val concat: bytes-> bytes -> bytes

assume val signVerif: input: bytes -> 
  Lemma 
  (ensures (verify (sign input) input == true ))

assume val random: unit -> Tot bytes

type claimChainBlock  = 
	|InitClaimChain : 
			id: bytes -> (* reference to ClaimChain to have claims that states ClaimChainState and revocation
			equally it could be used as a ref to chaimChain = skipList + index *) 
      nonce: nat ->
      t: time -> 
			meta : metadata -> 
			claimsCiphered: bytes -> 
			state: bytes -> (* id + hash + time *)
			hashPrevious:bytes -> 
      signature :bytes -> 
    ->    
			claimChainBlock f


type kv (a: eqtype) (b:eqtype) = 
  |MkKV : key: a -> value : b -> kv a b      

assume val vrf: bytes -> (tuple2 (bytes) (bytes))
assume val enc : key: bytes -> plain: bytes -> Tot(bytes)
assume val h1: bytes -> bytes
assume val h2: bytes -> bytes

val claimEncoding : 
  privateKeyVRF: bytes -> 
  nonce: nat -> 
  claim_label: string -> 
  claim_body : string -> Tot (tuple2 (bytes) (kv bytes bytes)) 

let claimEncoding privateKeyVRF nonce claim = 
  let claim_label = getClaimLabel claim in 
  let claim_body = getClaimBosy claim in 
  let ncl = concat nonce claim_label in 
  let k, proof = vrf ncl in 
  let l = h1 k in 
  let ke = h2 k in 
  let c = enc ke (concat proof claim_body) in 
  (k, MkKV l c)



val cipherClaims: cls: list claim -> 
  privateKeyVRF: bytes -> Tot list bytes
let cipherClaims cls privateKeyVRF= 
    let nonce = random () in 
    let f = claimEncoding privateKeyVRF nonce in 
    List.map cls f

  

val generateBlockGenesis: (* self signed*) meta: metadata -> cls: list claim -> claimChainBlock

let generateBlockGenesis meta cls = 
