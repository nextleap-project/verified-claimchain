module Spec.Claim

open FStar.Seq

let bytes =  seq FStar.UInt8.t

type keyEnt = 
|InitKeyEnt : source: string -> key: bytes -> keyEnt

type indentifier = 
|InitIndent : source: string -> identifier : option string -> indentifier

assume val hash: list 'a -> bytes

type metadata = 
|InitMetadata: screen_name: option string ->
				real_name: option string -> 
				identifiers: list indentifier -> 
				keys: list keyEnt -> 
				hashMetadata: bytes ->
				metadata



assume val sign : input: bytes -> bytes
assume val verify : signature: bytes -> data: bytes -> Tot bool

assume val toBytes: input : 'a -> bytes
assume val concat: bytes-> bytes -> bytes

(* Authenticity of information *)
type claim = 
	|InitClaim: test: list int -> signature : bytes{verify signature (toBytes test) } -> claim (* test purposes*)
	|KeyBindingClaim: meta: metadata -> key: bytes -> signature : bytes {verify signature (concat (toBytes meta) (toBytes key))}  -> claim
	|ClaimChainState: id: bytes -> state: bytes-> signature : bytes{verify signature (concat id state)} -> claim
	|Revocation: id: bytes -> signature : bytes{verify signature id}-> claim


