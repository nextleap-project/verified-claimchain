module Spec.Claim.ClaimChain

open FStar.Seq
open FStar.List.Tot
open FStar.Option

open Spec.Claim
open Spec.Claim.Metadata
open Spec.Claim.Keys
open Spec.Claim.Capabilities
open Spec.Claim.Common
open Spec.Claim.MerkleTree
open Spec.Claim.Map

type claimChainBlock  = 
	|InitClaimChain : 
     (* reference to ClaimChain to have claims that states ClaimChainState and revocationequally it could be used as a ref to chaimChain = skipList + index *) 
      nonce: bytes ->
      t: time -> 
			meta : metadata -> 
			hashMT: bytes -> 
			hashPrevious:bytes -> 
      hash: bytes -> 
      signature :bytes ->   
			claimChainBlock

val cipherClaims: cls:  map string claim-> nonce: bytes -> 
  privateKeyVRF: bytes -> ML (map string (kv (bytes) (tuple2 bytes bytes)))

let cipherClaims cls nonce privateKeyVRF= 
    let v = Spec.Claim.Map.values cls in (* list claims *)
    assert(length v = size cls);
    let f = claimEncoding privateKeyVRF nonce in 
    let lst = lemma_map_imp v f in 
    lemma_map v f; 
    assert(length lst = length v);
    let keys = Spec.Claim.Map.keySet cls in 
    MapList keys lst

val oneUserEncoding: privateKeyDH: key ->  
        row:  kv key (list string) -> 
        claims: (map string (kv (bytes) (tuple2 bytes bytes))) -> 
        nonce : bytes -> 
        ML (list (tuple2 (la: bytes) (pa : bytes)))

let rec oneUserEncoding privateKeyDH row claims nonce= 
    let labels = row.value in 
      match labels with 
      | hd:: tl ->  let claim = Spec.Claim.Map.get claims hd in (*option kv of bytes + tuple b b  *) 
                    let elem =   
                      (if isSome claim then 
                        let claimI = FStar.Option.get claim in 
                        let k = claimI.key in 
                        [encodeCapability privateKeyDH row.key nonce hd k]
                      else [])
                    in List.append elem (oneUserEncoding privateKeyDH (MkKV row.key tl) claims nonce) 
      | [] -> []              

val _allUserEncoding : accessControl: map (publicKeyReader: key) (labels: list string){size accessControl > 0} -> 
                        privateKeyDH: key -> 
                        claims: (map string (kv (bytes) (tuple2 bytes bytes))) -> 
                        nonce : bytes -> 
                        counter: nat{counter < size accessControl} -> 
                        l: (list (tuple2 (la: bytes) (pa : bytes))) -> 
                      ML (list (tuple2 (la: bytes) (pa : bytes)))
                      
let rec _allUserEncoding accessControl privateKeyDH claims nonce counter l = 
      let keyValue = Spec.Claim.Map.index accessControl counter in 
      let r = oneUserEncoding privateKeyDH keyValue claims nonce  in 
      if (counter + 1 < size accessControl) then 
        let l =  List.append l r in _allUserEncoding accessControl privateKeyDH claims nonce (counter +1) l
      else l                

val allUserEncoding: accessControl: map (publicKeyReader: key) (labels: list string){size accessControl > 0}-> 
                        privateKeyDH: key -> 
                        claims: (map string (kv (bytes) (tuple2 bytes bytes))) -> 
                        nonce : bytes -> 
                         ML (list (tuple2 (la: bytes) (pa : bytes)))

let allUserEncoding accessControl privateKeyDH claims nonce = 
      _allUserEncoding accessControl privateKeyDH claims nonce 0 [] 

assume val lstComplete: list 'a -> Tot (k: nat & (l: list 'a {List.length l = pow2 k}))

val fKeys: a: kv (bytes) (tuple2 bytes bytes) -> tuple2 bytes bytes
let fKeys a = a.value

private val generateBlockGeneral:  privateKeyDH: key ->privateKeyVRF: key ->   listClaims: map string claim -> 
    accessControl: map (publicKeyReader: key) (labels: list string) {size accessControl > 0} -> 
    meta: metadata -> reference: option(list claimChainBlock) -> ML claimChainBlock

let generateBlockGeneral privateKeyDH privateKeyVRF listClaims accessControl meta reference = 
    let nonce = random () in 
    let t = getTime () in 
    let listEncodedClaims = cipherClaims listClaims nonce privateKeyVRF in  (* ML (map string (kv (bytes) (tuple2 bytes bytes))) *)
    let claims = values listEncodedClaims in (*  (tuple2 bytes bytes)) *)
    let claims = List.map fKeys claims in 
    let vrfs = keySet listEncodedClaims in 
    let encodings = allUserEncoding accessControl privateKeyDH listEncodedClaims nonce in (* (list (tuple2 (la: bytes) (pa : bytes))) *) 
    let listMT = List.append claims encodings in 
    let (|k, lst|) = lstComplete listMT in 
    let hashMerkleTree = merkleListGeneration k lst in 
    let hashPrevious = 
      (
        if isNone reference 
            then Seq.createEmpty
        else   
          (
              if FStar.List.Tot.length (FStar.Option.get reference) > 0 then 
                 (FStar.List.Tot.hd (FStar.Option.get reference)).hash 
              else 
                  Seq.createEmpty
          )
      ) in 
    let hash = concat 
      (concat 
          (concat 
            (concat (toBytes nonce) (toBytes t))
            (toBytes metadata)
          ) 
          hashMerkleTree)
    hashPrevious in  
    let signature = sign hash in 
    InitClaimChain nonce t meta hashMerkleTree hashPrevious hash signature

val generateBlockGenesis: privateKeyDH: key ->privateKeyVRF: key ->  listClaims: map string claim -> 
    accessControl: map (publicKeyReader: key) (labels: list string) {size accessControl > 0} -> 
    meta: metadata -> ML claimChainBlock

let generateBlockGenesis  privateKeyDH privateKeyVRF listClaims accessControl meta = 
    generateBlockGeneral  privateKeyDH privateKeyVRF listClaims accessControl meta None 

val generateBlock: privateKeyDH: key -> privateKeyVRF:key ->  listClaims: map string claim -> 
    accessControl: map (publicKeyReader: key) (labels: list string) {size accessControl > 0}  ->
    previousList: list claimChainBlock{length previousList > 0} -> 
    ML claimChainBlock

let generateBlock  privateKeyDH privateKeyVRF listClaims accessControl previousList = 
  let previous = hd previousList in 
  generateBlockGeneral  privateKeyDH privateKeyVRF  listClaims accessControl (previous.meta) (Some previousList) 



val claimRetrieval: privateKeyReaderDH: key -> 
                    publicKeyReaderDH: key -> 
                    publicKeyOwnerDH:key -> 
                    publicKeyOwnerVRF : key -> 
                    tree_hash: bytes -> 
                    nonce: bytes -> claimLabel: string -> Tot (option bytes)

let claimRetrieval privateKeyReaderDH publicKeyReaderDH publicKeyOwnerDH publicKeyOwnerVRF tree_hash nonce claimLabel= 
  let lookUpKey = computeCapabilityLookupKey privateKeyReaderDH publicKeyReaderDH nonce claimLabel in 
  let capabilityCiphered = queryMerkleTree tree_hash lookUpKey in
  let (k, l) = decodeCapability privateKeyReaderDH publicKeyOwnerDH nonce claimLabel capabilityCiphered in 
  let c = queryMerkleTree tree_hash l  in 
  let claimBody = decodeClaim publicKeyOwnerVRF nonce claimLabel k c in claimBody