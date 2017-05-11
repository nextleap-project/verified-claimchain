module Test2

open SkipList2.Statement
open SkipList2.Properties
open FStar.Option
open FStar.Seq
open FStar.List.Tot

module Sl = SkipList2.Statement
module List = FStar.List.Tot
module Seq = FStar.Seq



val tail_mem : 	#a : eqtype -> 
			f: cmp a -> 
			pivot : a -> 
			s : seq a {Seq.sorted f s /\ Seq.length s > 0 /\ Seq.mem pivot  s = false /\ f (Seq.index s (Seq.length s -1)) pivot } ->
			Lemma (ensures (forall y. (Seq.mem y s ==> f y pivot)))(decreases (Seq.length s))

let rec tail_mem #a f pivot s = 
	if (Seq.length s = 1) then () else
	tail_mem #a f pivot (Seq.tail s)	

val tail_mem_wrapper: #a : eqtype -> 
			f: cmp a -> 
			pivot : a -> 
			s : seq a {Seq.sorted f s /\ Seq.length s > 0 /\ 
					Seq.mem pivot  s = false /\ f (Seq.index s (Seq.length s -1)) pivot } -> 
			Tot(r: seq a {(forall y. (Seq.mem y r ==> f y pivot))})

let tail_mem_wrapper #a f pivot s = 
	tail_mem #a f pivot s; s		

val right_tail_mem: #a: eqtype -> f: cmp a -> pivot : a -> s: seq a { Seq.sorted f s /\ Seq.length s > 0 /\ Seq.mem pivot s = false /\ 
			f pivot (Seq.index s 0)} -> 
			Lemma (ensures (forall y. (Seq.mem y s ==> f pivot y)))(decreases (Seq.length s))

let rec right_tail_mem #a f pivot s = 
	if (Seq.length s = 1) then () else
	right_tail_mem #a f pivot (Seq.tail s)	

val right_tail_mem_wrapper: #a: eqtype -> f: cmp a -> pivot : a -> 
			s: seq a { Seq.sorted f s /\ Seq.length s > 0 /\ Seq.mem pivot s = false /\ 
			f pivot (Seq.index s 0)} -> 
			Tot(r: seq a {(forall y. (Seq.mem y r ==> f pivot y))})	

let right_tail_mem_wrapper #a f pivot s = 
	right_tail_mem #a f pivot s; s	

assume val temp_lemma_split: #a : eqtype -> f: cmp a -> pivot : a -> s: seq a 
								{Seq.sorted f s /\ Seq.length s > 0 /\ 
								Seq.mem pivot  s = false} ->
								place : nat {place <= Seq.length s} -> 
								Lemma (ensures 
									( 
										(Seq.sorted f (fst(Seq.split s place))) /\ 
										(Seq.length (fst(Seq.split s place)) > 0) /\
										(Seq.mem pivot (fst(Seq.split s place)) = false) /\
										(Seq.sorted f (snd(Seq.split s place))) /\ 
										(Seq.length (snd(Seq.split s place)) > 0) /\
										(Seq.mem pivot (snd(Seq.split s place)) = false) 
								))

val temp_lemma_split_wrapper: #a : eqtype -> f: cmp a -> pivot : a -> 
								s: seq a 
									{Seq.sorted f s /\ Seq.length s > 0 /\ 
									Seq.mem pivot  s = false} ->
								place : nat {place <= Seq.length s } ->  
								Tot(r: seq a
								{
									(Seq.sorted f r)/\ 
									(Seq.length r > 0) /\
									(Seq.mem pivot r = false)
								})

let temp_lemma_split_wrapper #a f pivot s place =
	let r = fst(Seq.split s place) in temp_lemma_split #a f pivot s place; r

val temp_lemma_split_wrapper_right: #a : eqtype -> f: cmp a -> pivot : a -> 
								s: seq a 
									{Seq.sorted f s /\ Seq.length s > 0 /\ 
									Seq.mem pivot  s = false} ->
								place : nat {place <= Seq.length s } ->  
								Tot(r: seq a
								{
									(Seq.sorted f r)/\ 
									(Seq.length r > 0) /\
									(Seq.mem pivot r = false)
								})

let temp_lemma_split_wrapper_right #a f pivot s place =
	let r = snd(Seq.split s place) in temp_lemma_split #a f pivot s place; r

val tail_mem_split: #a : eqtype -> 
					f: cmp a -> 
					pivot : a ->
					s: seq a{Seq.sorted f s /\ Seq.length s > 0 /\ Seq.mem pivot s = false } -> 
					place : nat{place < Seq.length	s /\ f (Seq.index s place) pivot} -> 
					Tot(r: seq a {(forall y. (Seq.mem y r ==> f y pivot))})

let tail_mem_split #a f pivot s place = 
	let seq_new = temp_lemma_split_wrapper #a f pivot s (place +1)  in 
	tail_mem_wrapper #a f pivot seq_new

val right_tail_mem_split : #a : eqtype -> 
					f: cmp a -> 
					pivot : a ->
					s: seq a{Seq.sorted f s /\ Seq.length s > 0 /\ Seq.mem pivot s = false } -> 
					place : nat{(place + 1) < Seq.length	s /\ f pivot (Seq.index s (place+1))} -> 
					Tot(r: seq a {(forall y. (Seq.mem y r ==> f pivot y ))})

let right_tail_mem_split #a f pivot s place = 
	let seq_new = temp_lemma_split_wrapper_right #a f pivot s (place + 1)  in 
	right_tail_mem_wrapper #a f pivot seq_new

val main_lemma_split: #a : eqtype -> 
					f: cmp a -> 
					pivot : a ->
					s: seq a{Seq.sorted f s /\ Seq.length s > 0 /\ Seq.mem pivot s = false } ->
					place : nat{(place + 1) < Seq.length s /\ f (Seq.index s place) pivot /\ f pivot (Seq.index s (place+1))} -> 
					Tot(r1: seq a {(forall y. (Seq.mem y r1 ==> f y pivot))} * r2: seq a {(forall y. (Seq.mem y r2 ==> f pivot y ))})

let main_lemma_split #a f pivot s place =
	(tail_mem_split #a f pivot s place, right_tail_mem_split #a f pivot s place )

val sorted_seq_concat_wrapper : #a: eqtype -> f: cmp a ->pivot : a -> s1: seq a 
			{Seq.sorted f s1 /\ (forall y. (Seq.mem y s1 ==> f y pivot))} ->  
			s2: seq a {Seq.sorted f s2 /\ (forall y. (Seq.mem y s2 ==> f pivot y))}  ->
		  Tot(s3: seq a{Seq.sorted f s3 /\ Seq.length s3 = Seq.length s1 + Seq.length s2 + 1}) 

let sorted_seq_concat_wrapper #a f pivot s1 s2 = 
		let s3 = (Seq.append s1 (cons pivot s2)) in 
		FStar.Seq.Properties.sorted_concat_lemma #a f s1 pivot s2; 
		s3  	

assume val sorted_seq_concat_wrapper : #a: eqtype -> f: cmp a ->pivot : a -> s1: seq a 
			{Seq.sorted f s1 /\ (forall y. (Seq.mem y s1 ==> f y pivot))} ->  
			s2: seq a {Seq.sorted f s2 /\ (forall y. (Seq.mem y s2 ==> f pivot y))}  ->
		  Tot(s3: seq a{Seq.sorted f s3 /\ Seq.length s3 = Seq.length s1 + Seq.length s2 + 1}) 

val split_0 : #a: eqtype -> s: seq a{Seq.length s > 0} -> Lemma(
															ensures(
																Seq.equal (snd(Seq.split s 0)) s))
let split_0 #a s = ()

val ordered_addition_0: 
	#a: eqtype -> f: cmp a -> pivot: a -> s2: seq a {Seq.sorted f s2 /\ (forall y. (Seq.mem y s2 ==> f pivot y))} ->
				Tot(s3: seq a{Seq.sorted f s3 /\ Seq.length s3 = Seq.length s2 + 1}) 

let ordered_addition_0 #a f pivot s2 = 
		let s1 = Seq.createEmpty in 
		sorted_seq_concat_wrapper #a f pivot s1 s2 

assume val searchPlace : #a : eqtype -> f: cmp(a)  ->  sl: skipList a f{Sl.length sl > 0} -> value: a-> 
                Tot(place: nat{ 
				place < (Sl.length sl) /\
				f (Seq.index (getValues sl) place) value /\
				(place = 0  \/  f value (Seq.index (getValues sl) (place+1)) value)}) 

let main #a f sl value = 
	let place = searchPlace #a f sl value in 
	let s = getValues sl in 
	if place = 0 then ordered_addition_0 #a f value (right_tail_mem_split #a f value s place) 
	else let r = main_lemma_split #a f value s place in 
		let r1 = fst r in 
		let r2 = snd r in 
		sorted_seq_concat_wrapper #a f value r1 r2 
