module Spec.Claim.Capabilities

open Spec.Claim
open Spec.Claim.Metadata
open Spec.Claim.Keys
open Spec.Claim.Common
open Spec.Claim.Map

val claimEncoding : 
  privateKeyVRF: bytes -> 
  nonce: bytes -> 
  claim: claim -> Tot (kv (bytes) (tuple2 bytes bytes)) 

let claimEncoding privateKeyOwnerVRF nonce claim = 
  let claimLabel = getClaimLabel claim in
  let claimLabel = toBytes claimLabel in  
  let claimBody = getClaimBody claim in 
  let ncl = concat nonce claimLabel in 
  let k, proof = vrf privateKeyOwnerVRF ncl in 
  let l = h1 k in 
  let ke = h2 k in 
  let c = enc ke (concat proof claimBody) in 
  MkKV k (l, c)

val encodeCapability : privateKeyDH : key -> 
        publicKeyReaderDH: key -> 
        nonce: bytes -> 
        claimLabel: string -> 
        k: bytes -> Tot(tuple2 (la: bytes) (pa : bytes))

let encodeCapability privateKeyOwnerDH publicKeyReaderDH nonce claimLabel k = 
    let s = sharedSecret privateKeyOwnerDH publicKeyReaderDH in 
    let claimLabel = toBytes claimLabel in 
    let la1 = concat nonce s in 
    let body = concat la1 claimLabel in 
    let la = h3 body in 
    let key = h4 body in 
    let pa = enc key k in 
(la, pa)

val computeCapabilityLookupKey : privateKeyOwnerDH: key -> 
            publicKeyReaderDH: key -> 
            nonce: bytes -> 
            claimLabel : string -> 
            Tot (lookUpKey : bytes)

let computeCapabilityLookupKey privateKeyOwnerDH publicKeyReaderDH nonce claimLabel = 
    let s = sharedSecret privateKeyOwnerDH publicKeyReaderDH in 
    let claimLabel = toBytes claimLabel in 
    let la1 = concat nonce s in 
    let body = concat la1 claimLabel in 
    let la = h3 body in la

val decodeCapability: privateKeyReaderDH: key -> 
        ownerPublicKeyDH: key -> 
        nonce : bytes -> 
        claimLabel : string ->
        capabilityCiphered: bytes -> 
        Tot (tuple2 (k: bytes) (l: bytes))
        
let decodeCapability privateKeyReaderDH ownerPublicKeyDH nonce claimLabel capabilityCiphered = 
    let s = sharedSecret privateKeyReaderDH ownerPublicKeyDH in 
    let claimLabel = toBytes claimLabel in
    let la1 =  concat nonce s in 
    let body = concat la1 claimLabel in 
    let key = h4 body in 
    let k = dec key capabilityCiphered in 
    let l = h1 k in 
    (k, l)





val decodeClaim: publicKeyOwnerVRF: key -> nonce: bytes -> claimLabel: string -> k: bytes -> cipheredClaim: bytes -> Tot (claimBody : option bytes)

let decodeClaim publicKeyOwnerVRF nonce claimLabel k cipheredClaim = 
  let ke = h2 k in 
  let claimLabel = toBytes claimLabel in  
  let proofClaim = dec ke cipheredClaim in 
  let (proof, claim) = divideHashProof proofClaim in 
  let vrfPr = vrfProof k proof (concat nonce claimLabel) in 
    if vrfPr = true then 
      Some claim 
    else 
      None


