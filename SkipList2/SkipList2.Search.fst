module SkipList2.Search

open SkipList2.Statement
open SkipList2.Properties
open SkipList2.Insertion2
open FStar.Option
open FStar.Seq
open FStar.List.Tot

module Sl = SkipList2.Statement
module List = FStar.List.Tot
module Seq = FStar.Seq

val nextElement: #a: eqtype -> #f: cmp a -> sl: skipList a f {Sl.length sl > 1}-> element: a -> Tot(option (a))
val nextIndex: #a: eqtype -> #f: cmp a -> sl: skipList a f {Sl.length sl > 1} -> index: nat -> Tot(option(a))

val prevElement: #a: eqtype -> #f: cmp a -> sl: skipList a f {Sl.length sl > 1}-> element: a -> Tot(option(a))
val prevIndex: #a: eqtype -> #f : cmp a -> sl:  skipList a f{Sl.length sl > 1} -> index : nat -> Tot(option(a))

val search: #a: eqtype -> #f: cmp a -> sl: skipList a f {Sl.length sl > 1}-> element : a -> 
		Tot(option(place: nat { place < Sl.length sl /\ element = getValue sl place}))		

val exist: #a: eqtype -> #f: cmp a -> sl: skipList a f{Sl.length sl >1} -> element : a -> Tot(bool)

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
	option(
		place: nat
			{ 
				place < Sl.length sl /\ value = getValue sl place
			}
	)
	 -> searchResult a f sl value counter_global_previous

private val searchPlaceIndex: #a: eqtype -> #f : cmp a -> 
	sl: skipList a f {Sl.length sl > 1} -> 
	value : a -> 
	counter_global: nat {counter_global < Sl.length sl } -> 
	counter_local : nat {counter_local < List.length (getIndex sl counter_global)}-> 
	Tot(searchResult a f sl value counter_global)

let rec searchPlaceIndex #a #f sl value counter_global counter_local = 
	let values = getValues sl in 
	let index = lemma_index_1_2_wrapper #a #f sl counter_global counter_local in 
	lemma_last_element_biggest #a #f sl value;
	if (value = Seq.index values index) then Found (Some index)
	else if (f (Seq.index values index) value) then 
		NotFound index
	else if ((f value (Seq.index values index)) && (counter_local > (List.length (getIndex sl counter_global) -1))) 
		then searchPlaceIndex #a #f sl value counter_global (counter_local+1)
	else Found(None)

private val searchPlaceSequence: #a: eqtype ->  #f : cmp a ->  
						sl: skipList a f {Sl.length sl > 1} ->  
						value : a -> counter_global:nat {counter_global < (Sl.length sl)}->
						Tot(option(place: nat { place < Sl.length sl /\ value = getValue sl place}))
						(decreases(Sl.length sl- counter_global))

let rec searchPlaceSequence #a #f sl value counter_global = 
	let result = searchPlaceIndex #a #f sl value counter_global 0 in 
	match result with 
		| Found a -> a 
		| NotFound counter_global_new -> searchPlaceSequence #a #f sl value counter_global_new		

private val searchPlace: #a : eqtype -> #f: cmp(a) -> sl: skipList a f {Sl.length sl > 1} -> value : a -> 
			Tot(option(place: nat { place < Sl.length sl /\ value = getValue sl place}))

let searchPlace #a #f sl value =
	let counter_global = 0 in 
	if (value = (Seq.index(getValues sl) counter_global)) then 
		Some counter_global 
	else if (Sl.length sl = 1) then None
	else 
		searchPlaceSequence #a #f sl value counter_global	

let search #a #f sl element = 
	searchPlace #a #f sl element

let nextElement #a #f sl element = 
	let place = searchPlace #a #f sl element in 
	match place with
		| None -> None 
		| Some place -> 
			if ((place +1) < Sl.length sl) then 
				Some(getValue sl (place+1))
			else None	
let nextIndex #a #f sl index = 
	if (index + 1 < Sl.length sl) then 
		Some (getValue sl (index+1))
	else None			

let prevElement #a #f sl element = 
	let place = searchPlace #a #f sl element in 
	match place with 
		| None -> None
		| Some place -> 
			if (place -1) > 0 then 
				Some (getValue sl (place-1))
			else None	

let prevIndex #a #f sl index = 
	if (index -1 > 0 && (index-1) < Sl.length sl) then 
		Some (getValue sl (index -1)) 
	else None	

let exist #a #f sl element = 
	let r = search #a #f sl element in 
	match r with 
	| None -> false
	| Some _ -> true

val _forall: listFrom : list nat -> predicate: (nat -> Tot bool) -> pred_yes: (nat -> Tot nat) -> pred_no : (nat -> Tot nat) -> 
			Tot(r: list nat{List.length listFrom = List.length r})

let rec _forall listFrom predicate pred_yes pred_no = 
	match listFrom with 
	| [] -> []
	| a::tl -> let elem = if predicate a then pred_yes a 
				else pred_no a in elem :: 
				_forall tl predicate pred_yes pred_no 
