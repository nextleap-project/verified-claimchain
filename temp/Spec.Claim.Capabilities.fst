module Spec.Claim.Capabilities

open FStar.Seq
open Spec.Claim
open Spec.Claim.Metadata
open Spec.Claim.Keys

type key = bytes

assume val sharedSecret : k1: key -> k2: key -> Tot key


assume val h1: 'a -> bytes
assume val h2: 'a -> bytes
assume val h3: 'a -> bytes
assume val h4: 'a -> bytes

type kv (a: eqtype) (b:eqtype) = 
  |MkKV : key: a -> value : b -> kv a b      

assume val vrf: bytes -> (tuple2 (bytes) (bytes))
assume val enc : key: bytes -> plain: bytes -> Tot(bytes)
assume val dec: key: bytes -> ciphered: bytes -> Tot bytes
assume val lemmaEncDec : key: bytes -> plain: bytes -> Lemma (ensures( plain =  (let cipherText = enc key plain in 
                                                                        dec key cipherText )))
assume val getTime: unit -> time




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