module SkipList2.Seq.Properties

open FStar.Seq
open FStar.Option

module Seq = FStar.Seq
module List = FStar.List.Tot

type cmp (a:eqtype) = f:(a -> a -> Tot bool){total_order a f}

val seqLast: s: seq 'a {Seq.length s > 0}-> Tot 'a
let seqLast s = 
	(Seq.index s (Seq.length s -1))

val tail_mem : 	#a : eqtype -> #f: cmp a -> 
			pivot : a -> 
			s : seq a {Seq.sorted f s /\ Seq.length s > 0 /\ Seq.mem pivot  s = false /\ f (seqLast s) pivot } ->
			Lemma (ensures (forall y. (Seq.mem y s ==> f y pivot)))(decreases (Seq.length s))

let rec tail_mem #a #f pivot s = 
	if (Seq.length s = 1) then () else
	tail_mem #a #f pivot (Seq.tail s)	

val tail_mem_wrapper: #a : eqtype -> 
			#f: cmp a -> 
			pivot : a -> 
			s : seq a {Seq.sorted f s /\ Seq.length s > 0 /\ 
					Seq.mem pivot  s = false /\ f (seqLast s) pivot } -> 
			Tot(r: seq a {(forall y. (Seq.mem y r ==> f y pivot))})

let tail_mem_wrapper #a #f pivot s = 
	tail_mem #a #f pivot s; s		

val right_tail_mem: #a: eqtype -> #f: cmp a -> pivot : a -> s: seq a { Seq.sorted f s /\ Seq.length s > 0 /\ Seq.mem pivot s = false /\ 
			f pivot (Seq.index s 0)} -> 
			Lemma (ensures (forall y. (Seq.mem y s ==> f pivot y)))(decreases (Seq.length s))

let rec right_tail_mem #a #f pivot s = 
	if (Seq.length s = 1) then () else
	right_tail_mem #a #f pivot (Seq.tail s)	

val right_tail_mem_wrapper: #a: eqtype -> #f: cmp a -> pivot : a -> 
			s: seq a { Seq.sorted f s /\ Seq.length s > 0 /\ Seq.mem pivot s = false /\ 
			f pivot (Seq.index s 0)} -> 
			Tot(r: seq a {(forall y. (Seq.mem y r ==> f pivot y))})	

let right_tail_mem_wrapper #a #f pivot s = right_tail_mem #a #f pivot s; s	

assume val temp_lemma_split: #a : eqtype -> #f: cmp a -> pivot : a -> s: seq a 
								{Seq.sorted f s /\ Seq.length s > 0 /\ 
								Seq.mem pivot  s = false} ->
								place : nat {place < Seq.length s} -> 
								Lemma (ensures 
									( 
										(Seq.sorted f (fst(Seq.split s place))) /\ 
										(Seq.length (fst(Seq.split s place)) > 0) /\
										(Seq.mem pivot (fst(Seq.split s place)) = false) /\
										(Seq.sorted f (snd(Seq.split s place))) /\ 
										(Seq.length (snd(Seq.split s place)) > 0) /\
										(Seq.mem pivot (snd(Seq.split s place)) = false) 
								))

val temp_lemma_split_wrapper: #a : eqtype -> #f: cmp a -> pivot : a -> 
								s: seq a 
									{Seq.sorted f s /\ Seq.length s > 0 /\ 
									Seq.mem pivot  s = false} ->
								place : nat {place < Seq.length s  } ->  
								Tot(r: seq a
								{
									(Seq.sorted f r)/\ 
									(Seq.length r > 0) /\
									(Seq.mem pivot r = false) /\ Seq.length r = place
								})

let temp_lemma_split_wrapper #a #f pivot s place =
	let r = fst(Seq.split s place) in 
		temp_lemma_split #a #f pivot s place; r

val temp_lemma_split_wrapper_right: #a : eqtype -> #f: cmp a -> pivot : a -> 
								s: seq a 
									{Seq.sorted f s /\ Seq.length s > 0 /\ 
									Seq.mem pivot  s = false} ->
								place : nat {place < Seq.length s  } ->  
								Tot(r: seq a
								{
									(Seq.sorted f r)/\ 
									(Seq.length r > 0) /\
									(Seq.mem pivot r = false) /\ Seq.length r = (Seq.length s) - place
								})

let temp_lemma_split_wrapper_right #a #f pivot s place =
	let r = snd(Seq.split s place) in temp_lemma_split #a #f pivot s place; r

val tail_mem_split: #a : eqtype -> 
					#f: cmp a -> 
					pivot : a ->
					s: seq a{Seq.sorted f s /\ Seq.length s > 0 /\ Seq.mem pivot s = false } -> 
					place : nat{place < Seq.length	s -1 /\ f (Seq.index s place) pivot} -> 
					Tot(r: seq a {(forall y. (Seq.mem y r ==> f y pivot))})

let tail_mem_split #a #f pivot s place = 
	let seq_new = temp_lemma_split_wrapper #a #f pivot s (place+1)  in 
	tail_mem_wrapper #a #f pivot seq_new

val right_tail_mem_split : #a : eqtype -> 
					#f: cmp a -> 
					pivot : a ->
					s: seq a{Seq.sorted f s /\ Seq.length s > 0 /\ Seq.mem pivot s = false } -> 
					place : nat{place < Seq.length s  /\ f pivot (Seq.index s (place))} -> 
					Tot(r: seq a {(forall y. (Seq.mem y r ==> f pivot y ))})

let right_tail_mem_split #a #f pivot s place = 
	let seq_new = temp_lemma_split_wrapper_right #a #f pivot s (place)  in 
	right_tail_mem_wrapper #a #f pivot seq_new

val main_lemma_split: #a : eqtype -> 
					#f: cmp a -> 
					pivot : a ->
					s: seq a{Seq. sorted f s /\ Seq.length s > 0 /\ Seq.mem pivot s = false } ->
					place : nat{place  < Seq.length s -1  /\ f (Seq.index s place) pivot /\ f pivot (Seq.index s (place+1))} -> 
					Tot(r1: seq a {(forall y. (Seq.mem y r1 ==> f y pivot))} * r2: seq a {(forall y. (Seq.mem y r2 ==> f pivot y ))})

let main_lemma_split #a #f pivot s place =
	(tail_mem_split #a #f pivot s (place), right_tail_mem_split #a #f pivot s (place+1))

val split_0 : #a: eqtype -> s: seq a{Seq.length s > 0} -> Lemma(
															ensures(
																Seq.equal (snd(Seq.split s 0)) s))
let split_0 #a s = ()

val sorted_seq_concat_wrapper : #a: eqtype -> #f: cmp a ->pivot : a -> s1: seq a 
			{Seq.sorted f s1 /\ (forall y. (Seq.mem y s1 ==> f y pivot))} ->  
			s2: seq a {Seq.sorted f s2 /\ (forall y. (Seq.mem y s2 ==> f pivot y))}  ->
		  	Tot(s3: seq a{Seq.sorted f s3 /\ Seq.length s3 = Seq.length s1 + Seq.length s2 + 1}) 

let sorted_seq_concat_wrapper #a #f pivot s1 s2 = 
		let s3 = (Seq.append s1 (cons pivot s2)) in 
		FStar.Seq.Properties.sorted_concat_lemma #a f s1 pivot s2; 
		s3  
(*pivot is not used*)
val ordered_addition_0: 
	#a: eqtype -> #f: cmp a -> pivot: a -> s2: seq a {Seq.sorted f s2 /\ (forall y. (Seq.mem y s2 ==> f pivot y))} ->
				Tot(s3: seq a{Seq.sorted f s3 /\ Seq.length s3 = Seq.length s2 + 1}) 

let ordered_addition_0 #a #f pivot s2 = 
		let s1 = Seq.createEmpty in 
		sorted_seq_concat_wrapper #a #f pivot s1 s2 	

val upd: l: list 'a -> counter: nat -> value: 'a -> Tot(r: list 'a{List.length l = List.length r})
let rec upd l counter value = 
	match l with
	| hd::tl -> if (counter = 0) then value:: tl else hd::upd tl (counter-1) value
	| [] -> []		