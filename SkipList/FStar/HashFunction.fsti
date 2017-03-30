module HashFunction

open HashFunctionImpl

(* <Aliases> *)

module Buffer = FStar.Buffer
private let uint32_t  = FStar.UInt32.t
private let suint8_t  = Hacl.UInt8.t
private let suint8_p  = Buffer.buffer suint8_t
(* </Aliases> *)


val lengthHash: uint32_t	
val hashFunc:   hash: suint8_p {length hash = v lengthHash} -> 
				input : suint8_p ->
				len : uint32_t {v len = length input} -> 
				Stack unit
				(requires (fun h0 -> live h0 hash /\ live h0 input))
				(ensures (fun h0 _ h1 -> live h1 hash /\ modifies_1 hash h0 h1))

val lengthHashLocal: uint32_t
val hashLocal : hash: suint8_p {length hash = v lengthHash} -> 
				input : suint8_p ->
				len : uint32_t {v len = length input} -> 
				Stack unit
				(requires (fun h0 -> live h0 hash /\ live h0 input))
				(ensures (fun h0 _ h1 -> live h1 hash /\ modifies_1 hash h0 h1))


