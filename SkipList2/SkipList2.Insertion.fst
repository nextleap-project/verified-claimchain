module SkipList2.Insertion

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
		counter_global < (Sl.length sl-1) /\ 
		(f (Seq.index (getValues sl) (counter_global)) value = false)
		}
	-> searchResult a f sl value counter_global_previous
| Found:  
	place: nat
		{ 
			place < Sl.length sl /\
			f (Seq.index (getValues sl) place) value /\
			(place - 1 < 0 \/  f (Seq.index (getValues sl) (place-1)) value = false)
		}
	 -> searchResult a f sl value counter_global_previous


assume val change_indexes: #a : eqtype -> #f : cmp a -> sl:skipList a f {Sl.length sl > 0} -> value: a -> 
					place: nat {place < Sl.length sl /\ 
					f (Seq.index (getValues sl) place) value /\
					(place = 0 \/ f(Seq.index (getValues sl) (place -1)) value = false)
					} -> 
					Tot(r: seq (non_empty_list nat) {Seq.length r = Sl.length sl + 1 })

val sorted_seq_concat_wrapper : #a: eqtype -> f: cmp a ->pivot : a -> s1: seq a 
			{Seq.sorted f s1 /\ (forall y. (Seq.mem y s1 ==> f y pivot))} ->  
			s2: seq a {Seq.sorted f s2 /\ (forall y. (Seq.mem y s2 ==> f pivot y))}  ->
		  Tot(s3: seq a{Seq.sorted f s3 /\ Seq.length s3 = Seq.length s1 + Seq.length s2 + 1}) 

let sorted_seq_concat_wrapper #a f pivot s1 s2 = 
		let s3 = (Seq.append s1 (cons pivot s2)) in 
		FStar.Seq.Properties.sorted_concat_lemma #a f s1 pivot s2; 
		s3  

assume val lemma_ch1:#a:eqtype -> f: cmp a ->  sl: skipList a f -> value : a -> 
		 place: nat{ 
				place < (Sl.length sl) /\
				f (Seq.index (getValues sl) place) value /\
				(place - 1 < 0 \/  f (Seq.index (getValues sl) (place-1)) value = false)} ->
		 Lemma (ensures (
		 	(Seq.sorted f (fst (Seq.split #a (Sl.getValues sl) place))) /\
		 	(forall y. (Seq.mem y (fst (Seq.split #a (Sl.getValues sl) place))
		 	==> f y value))))

val lemma_ch1_wrapper: #a: eqtype -> f: cmp a -> sl: skipList a f -> value : a -> 
				place: nat{ 
				place < (Sl.length sl) /\
				f (Seq.index (getValues sl) place) value /\
				(place - 1 < 0 \/  f (Seq.index (getValues sl) (place-1)) value = false)} ->
				Tot(s1: seq a { Seq.sorted f s1 /\
				(forall y. (Seq.mem y (fst (Seq.split #a (Sl.getValues sl) place))==> f y value))})


let lemma_ch1_wrapper #a f sl value place = 
			let values = fst (Seq.split #a (Sl.getValues sl) place) in 
			lemma_ch1 #a f sl value place; values				

assume val lemma_ch2:#a:eqtype -> f: cmp a ->  sl: skipList a f -> value : a -> 
		 place: nat{ 
				place < (Sl.length sl) /\
				f (Seq.index (getValues sl) place) value /\
				(place - 1 < 0 \/  f (Seq.index (getValues sl) (place-1)) value = false)} ->
		 Lemma (ensures (
		 	(Seq.sorted f (snd (Seq.split #a (Sl.getValues sl) place))) /\
		 	(forall y. (Seq.mem y (snd (Seq.split #a (Sl.getValues sl) place))
		 	==> f value y))))

val lemma_ch2_wrapper: #a: eqtype -> f: cmp a -> sl: skipList a f -> value : a -> 
				place: nat{ 
				place < (Sl.length sl) /\
				f (Seq.index (getValues sl) place) value /\
				(place - 1 < 0 \/  f (Seq.index (getValues sl) (place-1)) value = false)} ->
				Tot(s1: seq a { Seq.sorted f s1 /\
				(forall y. (Seq.mem y (snd (Seq.split #a (Sl.getValues sl) place))==> f value y))})

let lemma_ch2_wrapper #a f sl value place = 
			let values = snd (Seq.split #a (Sl.getValues sl) place) in 
			lemma_ch2 #a f sl value place; values		

val change_values: #a: eqtype -> f: cmp a -> sl: skipList a f -> value : a -> 
		 place: nat{ 
				place < (Sl.length sl) /\
				f (Seq.index (getValues sl) place) value /\
				(place - 1 < 0 \/  f (Seq.index (getValues sl) (place-1)) value = false)} ->
		Tot(s3: seq a{Seq.sorted f s3 /\ 
		Seq.length s3 = Sl.length sl+ 1 
	}) 

let change_values #a f sl value place = 
	let s1 = lemma_ch1_wrapper #a f sl value place in 
	let s2 = lemma_ch2_wrapper #a f sl value place in 
	sorted_seq_concat_wrapper #a f value s1 s2 

private val searchPlaceIndex: #a: eqtype -> #f: cmp a -> sl : skipList a f{Sl.length sl> 1} -> value: a-> 
						counter_global: nat{counter_global < (Sl.length sl -1) /\ 
							(f (Seq.index (getValues sl) counter_global ) value = false) } -> 
						counter_local : nat{ counter_local <List.length
								(getIndex sl counter_global)} ->
						Tot(searchResult a f sl value counter_global)(decreases(List.length (getIndex sl counter_global) - counter_local))

let rec searchPlaceIndex #a #f sl value counter_global counter_local  = 
	let values = getValues sl in 
	let index = lemma_index_1_2_wrapper #a #f sl counter_global counter_local in 
	if  (f (Seq.index values index) value) then (*more*)
		(
			if (f (Seq.index values (index - 1)) value = false) then 
				Found index
			else if (counter_local = List.length (getIndex sl counter_global)-1) then
				let index = lemma_index_3 #a #f sl; index in 
				Found index	
			else 
				let counter_local = counter_local + 1 in  searchPlaceIndex #a #f sl value counter_global counter_local 
		)		
	else NotFound index		

val searchPlaceSequence: #a:eqtype-> #f: cmp(a) ->sl: skipList a f{Sl.length sl> 1}-> value : a -> 
			counter_global:nat{counter_global < (Sl.length sl -1) /\ 
			(f (Seq.index (getValues sl) counter_global) value = false) }  -> 
			Tot(place: nat{ 
				place < (Sl.length sl) /\
				f (Seq.index (getValues sl) place) value /\
				(place - 1 < 0 \/  f (Seq.index (getValues sl) (place-1)) value = false)})
			(decreases (Sl.length sl - counter_global))

let rec searchPlaceSequence #a #f sl value counter_global =
	let result = searchPlaceIndex #a #f sl value counter_global 0 in 
		match result with 	
			| Found index ->  index 
			| NotFound counter_global_new ->  
					if ((counter_global_new) <  (Sl.length sl -1)) then 
						searchPlaceSequence #a #f sl value (counter_global_new)
					else  (counter_global_new+1)

val searchPlace : #a : eqtype -> #f: cmp(a)  ->  sl: skipList a f{Sl.length sl > 0} -> value: a-> 
                Tot(place: nat{ 
				place < (Sl.length sl) /\
				f (Seq.index (getValues sl) place) value /\
				(place - 1 < 0 \/  f (Seq.index (getValues sl) (place-1)) value = false)})

let searchPlace #a #f  sl value =
	let counter_global = 0 in 
	if (f (Seq.index (getValues sl) counter_global) value) then 
		counter_global
	else if (Sl.length sl = 1) then (lemma_last_element_biggest #a #f sl value; counter_global)
	else
		searchPlaceSequence #a #f sl value counter_global

val addition: #a: eqtype -> #f: cmp a -> 
		sl: skipList a f {Sl.length sl > 0}-> 
		value : a -> Tot (r: skipList a f{Sl.length r = Sl.length sl + 1})

let addition #a #f sl value  = 
	let place = searchPlace #a #f sl value in 
	let values = change_values #a f sl value place in 
	let indexes = change_indexes #a #f sl value place in 
	Mk values indexes 
