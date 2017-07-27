module Spec.Claim.Common

open FStar.Seq

type bytes = seq nat
type time = nat
type key = bytes

assume val toBytes: input : 'a ->Tot bytes
assume val concat: bytes-> bytes -> bytes

assume val sharedSecret : k1: key -> k2: key -> Tot key

assume val hash: bytes  -> bytes
assume val h1: bytes -> bytes
assume val h2: bytes -> bytes
assume val h3: bytes -> bytes
assume val h4: bytes -> bytes

assume val vrf: keyVRF: bytes -> plaintext: bytes -> Tot(tuple2 (bytes) (bytes))
assume val vrfProof: hash: bytes -> proof: bytes -> plainText: bytes -> Tot bool

assume val divideHashProof: bytes -> (bytes * bytes)

assume val enc : key: bytes -> plain: bytes -> Tot(bytes)
assume val dec: key: bytes -> ciphered: bytes -> Tot bytes
assume val lemmaEncDec : key: bytes -> plain: bytes -> Lemma (ensures( plain =  (let cipherText = enc key plain in 
                                                                        dec key cipherText )))

assume val getTime: unit -> time
assume val random: unit -> Tot bytes


assume val sign : input: bytes -> Tot bytes
assume val verify : signature: bytes -> data: bytes -> Tot bool
assume val signVerif: input: bytes -> 
  Lemma 
  (ensures (verify (sign input) input == true ))
