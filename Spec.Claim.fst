module Spec.Claim

open FStar.Seq
open SkipList2.Statement
open SkipList2.Insertion2
open SkipList2.Properties
open SkipList2.Search

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
	|NullMetadata : metadata				



assume val sign : input: bytes -> bytes
assume val verify : signature: bytes -> data: bytes -> Tot bool

assume val toBytes: input : 'a -> bytes
assume val concat: bytes-> bytes -> bytes

assume val signVerif: input: bytes -> 
	Lemma 
	(ensures (verify (sign input) input == true ))

(* Authenticity of information *)

type time = nat

type claim = 
	|InitClaim: 
		timeStamp: (k : time{k = 0}) ->  
		test: list int -> 
		signature : bytes{verify signature (toBytes test) } -> claim (* test purposes*)
	|KeyBindingClaim: 
		timeStamp : (k : time { k> 0}) -> 
		meta: metadata -> 
		key: bytes -> 
		signature : bytes {verify signature (concat (toBytes meta) (toBytes key))}  -> claim
	|ClaimChainState: 
		timeStamp: (k : time { k> 0}) -> 
		id: bytes -> 
		state: bytes-> 
		signature : bytes{verify signature (concat id state)} -> claim
	|Revocation: 
		timeStamp : (k : time { k> 0}) -> 
		id: bytes -> 
		signature : bytes{verify signature id}-> claim

val getTimeStamp: cl: claim -> time
let getTimeStamp cl = 
	match cl with
	| InitClaim timeStamp _ _ -> timeStamp
	| KeyBindingClaim timeStamp _ _ _ -> timeStamp
	| ClaimChainState timeStamp _ _ _  -> timeStamp
	| Revocation timeStamp _ _ -> timeStamp

val func_ord_claim: claim1: claim -> claim2: claim -> Tot(r: bool)
let func_ord_claim claim1 claim2 = 
	if claim1 = claim2 then true else
	getTimeStamp claim1 < getTimeStamp claim2


type cmp (a:eqtype) =  f:(a -> a -> Tot bool){total_order a f}
type cmpClaim = f: (claim -> claim -> Tot bool) {total_order claim f}

val getClaimMax: unit -> Tot claim
let getClaimMax () = 
	let l = [0] in 
	let data = toBytes l  in 
	let signature =  sign data in 
	signVerif data; assert(verify (sign data) data == true);
	InitClaim 0 l signature  

type claimCh (f: cmpClaim ) = skipList claim f

val createEmptyClaimChaim : #f: cmpClaim -> size: nat {size > 0} -> claimCh f

let createEmptyClaimChaim #f size= 
	SkipList2.Statement.create #claim #f (getClaimMax()) size

val addClaim:  #f: cmpClaim ->  cl: claim -> max_level: nat ->chain : claimCh f{SkipList2.Statement.length chain > 0} -> claimCh f
let addClaim #f cl max_level chain = 
	match cl with 
		|InitClaim _ _ _ -> chain
		| _ -> 
			assert(getTimeStamp cl > 0);
			SkipList2.Properties.lemma_last_element_biggest #claim #f chain cl;
			assert(f cl (last_element_values #claim #f chain));
			if (Seq.mem cl (SkipList2.Statement.getValues chain) = true) 
				then chain 
			else 
			(
				assert (Seq.mem cl (SkipList2.Statement.getValues chain) = false);
				SkipList2.Insertion2.addition #claim #f cl chain max_level				
			)
				


val getFirstElement: #f: cmpClaim -> chain: claimCh f{SkipList2.Statement.length chain > 0} -> Tot claim
let getFirstElement #f chain = 
	SkipList2.Statement.hd #claim #f chain


val getLastElement : #f: cmpClaim -> chain : claimCh f{SkipList2.Statement.length chain > 0} -> Tot claim
let getLastElement #f chain = 
	last_element_values #claim #f chain

(*val nextElement: #a: eqtype -> #f: cmp a -> sl: skipList a f {Sl.length sl > 1}-> element: a -> Tot(option (a))*)
val getNextElement : #f : cmpClaim -> chain : claimCh f {SkipList2.Statement.length chain > 1} -> cl: claim -> Tot (option (claim))
let getNextElement #f chain cl = 
	SkipList2.Search.nextElement #claim #f chain cl 

val getPreviousElement: #f: cmpClaim -> chain : claimCh f {SkipList2.Statement.length chain > 1} -> cl: claim -> Tot(option (claim))
let getPreviousElement #f chain cl = 
	SkipList2.Search.prevElement #claim #f chain cl

(*)
let func_ord_claim_lemma () : Lemma (total_order claim func_ord_claim) = ()

let comp = func_ord_claim

val func_ord_claim4 : unit -> f:(claim -> claim -> Tot bool)
let func_ord_claim4 () = comp

type total_order (a:eqtype) (f: (a -> a -> Tot bool)) =
    (forall a. f a a)                                           (* reflexivity   *)
    /\ (forall a1 a2. (f a1 a2 /\ a1<>a2)  <==> not (f a2 a1))  (* anti-symmetry *)
    /\ (forall a1 a2 a3. f a1 a2 /\ f a2 a3 ==> f a1 a3)        (* transitivity  *)
type tot_ord (a:eqtype) = f:(a -> a -> Tot bool){total_order a f}
(*)
let func_ord_claim4 cmp claim = func_ord_claim
