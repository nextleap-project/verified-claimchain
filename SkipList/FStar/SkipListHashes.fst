module SkipListHashes

open HashFunctionImpl


assume val createBuff: size:FStar.UInt32.t -> buffer:suint8_p{length buffer = size}
assume val valueToBuff:#a :eqtype -> value: a -> suint8_p
assume val intToBuff: value: FStar.UInt32 -> suint8_p 
assume val bufferConcat : b1 : suint8_p -> b2: suint8_p -> b3:suint8_p{length b3 = length b1 + length b2}
assume val lstToBuff: #a :eqtype -> value: list(skipList a) -> suint8_p

val hashF: #a: eqtype ->  value: a -> levels: FStar.UInt32.t -> lst:list(skipList a) -> hash:suint8_p -> suint8_p
let hashF #a value levels lst =
	let tempbuff1 = createBuff size1 in 
	let tempbuff2 = createBuff size2 in 
	let tempbuff3 = createBuff size3 in 
	let tempbuff4 = createBuff size4 in 
	let tempbuff5 = createBuff size5 in 
	valueToBuff value tempbuff1;
	intToBuff levels tempbuff2; 
	bufferConcat buff1 buff2 tempbuff3; 
	lstToBuff lst tempbuff4;
	bufferConcat buff3 buff4 tempbuff5
	hashLocal tempbuff5 hash