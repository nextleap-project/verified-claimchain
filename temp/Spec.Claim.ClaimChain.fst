module Spec.Claim.ClaimChain

open FStar.Seq
open Spec.Claim

open Spec.Claim.Metadata
open Spec.Claim.Keys
open Spec.Claim.Capabilities
open Spec.Claim.Common
open Spec.Claim.MerkleTree

type claimChainBlock  = 
	|InitClaimChain : 
			id: nat -> (* reference to ClaimChain to have claims that states ClaimChainState and revocationequally it could be used as a ref to chaimChain = skipList + index *) 
      nonce: nat ->
      t: time -> 
			meta : metadata -> 
			claimsCiphered: bytes -> 
			state: bytes -> (* id + hash + time *)
			hashPrevious:bytes -> 
      signature :bytes ->    
			claimChainBlock

val cipherClaims: cls: list claim -> 
  privateKeyVRF: bytes -> ML (list (tuple2 (bytes) (kv bytes bytes)))

let cipherClaims cls privateKeyVRF= 
    let nonce = random () in 
    let f = claimEncoding privateKeyVRF nonce in 
    List.map f cls

(*)
val generateBlockGenesis: (* self signed*) meta: metadata -> claimChainBlock

let generateBlockGenesis meta  k cls = 
    let id = 0 in 
    let nonce = random () in 
    let t = getTime () in 
    let keys = getKeys meta in 
    let key = crKeySearchPkSig keys in 
    let key = getKeyAsBytes key in 
    let claimsCiphered = cipherClaims cls key in 
    let hashMerkleTree = merkleListGeneration #claim k claimsCiphered in 
    let state = concat (concat (toBytes id) (toBytes nonce)) (concat (toBytes time) (hashMerkleTree)) in 
    let hashPrevious = createEmpty 0 in 
      let c1 = concat (toBytes id) (toBytes nonce) in 
      let c2 = concat c1 (toBytes time) in 
      let c3 = concat c2 (toBytes metadata) in 
      let c4 = concat c3 claimsCiphered in 
      let c5 = concat c4 state in 
      let c6 = concat c5 hashPrevious in 
    let signature = enc (keySearchPkSig metadata.keys) c6  in  
    InitClaimChain id nonce t meta claimsCiphered state hashPrevious signature
(*)
val generateBlock: bl: claimChainBlock -> k: nat -> cls : list claim {length cls = pow2 k } -> claimChainBlock

let generateBlock bl k cls = 
    let id = (bl.id + 1) in 
    let nonce = random () in 
    let t = getTime () in 
    let metadata = bl.meta in 
    let key = keySearchPkVRF metadata.keys in 
    let claimsCiphered = cipherClaims cls key in 
    let hashMerkleTree = merkleListGeneration #claim k cls in 
    let state = concat (concat (toBytes id) (toBytes nonce)) (concat (toBytes time) (hashMerkleTree)) in 
      let c1 = concat (toBytes bl.id) (toBytes bl.nonce) in 
      let c2 = concat c1 (toBytes bl.t) in 
      let c3 = concat c2 (toBytes bl.meta) in 
      let c4 = concat c3 bl.claimsCiphered in 
      let c5 = concat c4 bl.state in 
      let c6 = concat c5 bl.hashPrevious in 
    let hashPrevious = hash c6 in 
      let c1 = concat (toBytes id) (toBytes nonce) in 
      let c2 = concat c1 (toBytes time) in 
      let c3 = concat c2 (toBytes metadata) in 
      let c4 = concat c3 claimsCiphered in 
      let c5 = concat c4 state in 
      let c6 = concat c5 hashPrevious in 
    let signature = enc (keySearchPkSig metadata.keys) c6  in   
    InitClaimChain id nonce t metadata claimsCiphered state hashPrevious signature

    


