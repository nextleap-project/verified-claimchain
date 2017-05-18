module SkipList2.Insertion2

open SkipList2.Statement
open SkipList2.Properties
open FStar.Option
open FStar.Seq
open FStar.List.Tot

module Sl = SkipList2.Statement
module List = FStar.List.Tot
module Seq = FStar.Seq


type searchResult (a:eqtype) (f:cmp a) (sl: skipList a f) (value: a) (counter_global_previous: nat) = 
| NotFound: 
	counter_global : nat 
		{
		counter_global > counter_global_previous /\
		counter_global < (Sl.length sl -1) /\ 
		(f (getValue sl counter_global) value)
		}
	-> searchResult a f sl value counter_global_previous
| Found:  
	place: nat
		{ 
			(place+1) < Sl.length sl /\
			(f value (getValue sl (place +1))) /\
			(f (getValue sl place) value)
		}
	 -> searchResult a f sl value counter_global_previous


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

let right_tail_mem_wrapper #a #f pivot s = 
	right_tail_mem #a #f pivot s; s	

assume val temp_lemma_split: #a : eqtype -> #f: cmp a -> pivot : a -> s: seq a 
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

val temp_lemma_split_wrapper: #a : eqtype -> #f: cmp a -> pivot : a -> 
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

let temp_lemma_split_wrapper #a #f pivot s place =
	let r = fst(Seq.split s place) in temp_lemma_split #a #f pivot s place; r

val temp_lemma_split_wrapper_right: #a : eqtype -> #f: cmp a -> pivot : a -> 
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

let temp_lemma_split_wrapper_right #a #f pivot s place =
	let r = snd(Seq.split s place) in temp_lemma_split #a #f pivot s place; r

val tail_mem_split: #a : eqtype -> 
					#f: cmp a -> 
					pivot : a ->
					s: seq a{Seq.sorted f s /\ Seq.length s > 0 /\ Seq.mem pivot s = false } -> 
					place : nat{place < Seq.length	s /\ f (Seq.index s place) pivot} -> 
					Tot(r: seq a {(forall y. (Seq.mem y r ==> f y pivot))})

let tail_mem_split #a #f pivot s place = 
	let seq_new = temp_lemma_split_wrapper #a #f pivot s (place +1)  in 
	tail_mem_wrapper #a #f pivot seq_new

val right_tail_mem_split : #a : eqtype -> 
					#f: cmp a -> 
					pivot : a ->
					s: seq a{Seq.sorted f s /\ Seq.length s > 0 /\ Seq.mem pivot s = false } -> 
					place : nat{(place + 1) < Seq.length	s /\ f pivot (Seq.index s (place+1))} -> 
					Tot(r: seq a {(forall y. (Seq.mem y r ==> f pivot y ))})

let right_tail_mem_split #a #f pivot s place = 
	let seq_new = temp_lemma_split_wrapper_right #a #f pivot s (place + 1)  in 
	right_tail_mem_wrapper #a #f pivot seq_new

val main_lemma_split: #a : eqtype -> 
					#f: cmp a -> 
					pivot : a ->
					s: seq a{Seq.sorted f s /\ Seq.length s > 0 /\ Seq.mem pivot s = false } ->
					place : nat{(place + 1) < Seq.length s /\ f (Seq.index s place) pivot /\ f pivot (Seq.index s (place+1))} -> 
					Tot(r1: seq a {(forall y. (Seq.mem y r1 ==> f y pivot))} * r2: seq a {(forall y. (Seq.mem y r2 ==> f pivot y ))})

let main_lemma_split #a #f pivot s place =
	(tail_mem_split #a #f pivot s place, right_tail_mem_split #a #f pivot s place )

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


val ordered_addition_0: 
	#a: eqtype -> #f: cmp a -> pivot: a -> s2: seq a {Seq.sorted f s2 /\ (forall y. (Seq.mem y s2 ==> f pivot y))} ->
				Tot(s3: seq a{Seq.sorted f s3 /\ Seq.length s3 = Seq.length s2 + 1}) 

let ordered_addition_0 #a #f pivot s2 = 
		let s1 = Seq.createEmpty in 
		sorted_seq_concat_wrapper #a #f pivot s1 s2 

val change_values: #a: eqtype -> #f: cmp a -> value : a -> sl: skipList a f{Sl.length sl > 1 /\ Seq.mem value (getValues sl) = false} -> 
		  place: nat{ 
				(place < (Sl.length sl -1 )) /\
				(
					(place = 0 /\ f value (Seq.index (getValues sl) 0))  \/ 
						(
							(f value (Seq.index (getValues sl) (place+1)))
				 			/\ (f (Seq.index (getValues sl) place) value)
						)
				)
			}->
		Tot(s3: seq a{Seq.sorted f s3 /\ Seq.length s3 = Sl.length sl+ 1 
	}) 
(*)
(*Tot(r: seq a {(forall y. (Seq.mem y r ==> f pivot y ))})*)
let change_values #a #f value sl place = 
	let s = getValues sl in 
	if (place = 0) then 
		let sequence = right_tail_mem_split #a #f value s place in 
		ordered_addition_0 #a #f value sequence
	else 		
		let s = main_lemma_split #a #f value s place in 
		let s1 = fst s in 
		let s2 = snd s in sorted_seq_concat_wrapper #a #f value s1 s2

(*)
private val searchPlaceIndex: #a: eqtype -> #f: cmp a -> sl : skipList a f{Sl.length sl> 1} -> value: a-> 
						counter_global: nat{counter_global < (Sl.length sl -1) /\ 
							(f (Seq.index (getValues sl) counter_global ) value) } -> 
						counter_local : nat{ counter_local <List.length
								(getIndex sl counter_global)} ->
						Tot(searchResult a f sl value counter_global)(decreases(List.length (getIndex sl counter_global) - counter_local))

let rec searchPlaceIndex #a #f sl value counter_global counter_local  = 
	let values = getValues sl in 
	let index = lemma_index_1_2_wrapper #a #f sl counter_global counter_local in 
	lemma_last_element_biggest #a #f sl value;
	if  (f value (Seq.index values index)) then 
		(
			if (f (Seq.index values (index-1)) value ) then 
				Found (index-1)
			else if (counter_local  = (List.length (getIndex sl counter_global) -1)) then
				let result = lemma_index_3 #a #f sl	counter_global in 
				Found counter_global	
			else 
				let counter_local = counter_local + 1 in  searchPlaceIndex #a #f sl value counter_global counter_local 
		)		
	else NotFound index	(* if inf -> not exist*)

val searchPlaceSequence: #a:eqtype-> #f: cmp(a) ->sl: skipList a f{Sl.length sl> 1}-> value : a -> 
			counter_global:nat{counter_global < (Sl.length sl -1) /\ 
			(f (Seq.index (getValues sl) counter_global) value) }  -> 
			Tot(place: nat{ 
				place < (Sl.length sl -1) /\
				(f value (Seq.index (getValues sl) (place+1))) /\
				(f (Seq.index (getValues sl) place) value)
				})
			(decreases (Sl.length sl - counter_global))

let rec searchPlaceSequence #a #f sl value counter_global =
	let result = searchPlaceIndex #a #f sl value counter_global 0 in 
		match result with 	
			| Found index ->  index 
			| NotFound counter_global_new ->  
				searchPlaceSequence #a #f sl value (counter_global_new)

val searchPlace : #a : eqtype -> #f: cmp(a)  ->  sl: skipList a f{Sl.length sl > 1} -> value: a-> 
                Tot(place: nat{ 
				(place < (Sl.length sl -1 )) /\
				(
					(place = 0 /\ f value (Seq.index (getValues sl) 0))  \/ 
						(
							(f value (Seq.index (getValues sl) (place+1)))
				 			/\ (f (Seq.index (getValues sl) place) value)
						)
				)
			})

let searchPlace #a #f  sl value =
	let counter_global = 0 in 
	if (f value (Seq.index (getValues sl) counter_global)) then 
		counter_global
	else if (Sl.length sl = 1) then (lemma_last_element_biggest #a #f sl value; counter_global)
	else
		searchPlaceSequence #a #f sl value counter_global
(*)
val addition: #a: eqtype -> #f: cmp a -> 
		sl: skipList a f {Sl.length sl > 0}-> 
		value : a -> Tot (r: skipList a f{Sl.length r = Sl.length sl + 1})

let addition #a #f sl value  = 
	let place = searchPlace #a #f sl value in 
	let values = change_values #a f sl value place in 
	let indexes = change_indexes #a #f sl value place in 
	Mk values indexes 
