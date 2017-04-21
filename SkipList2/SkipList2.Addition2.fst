module SkipList2.Addition2

module SL =  SkipList2.Statement
module List = FStar.List.Tot
open SkipList2.Statement
open FStar.Option
open FStar.Seq
open FStar.List.Tot
open SkipList2.Properties


module Sl = SkipList2.Statement

type searchResult (a:eqtype) (f:cmp a)= 
| Blank: searchResult a f 
| NotFound: sl: skipList a f -> result : nat {result < SkipList2.Statement.length sl}-> searchResult a f 
| Found: sl: skipList a f ->  value: a -> 
	place: nat
	{ 
		place<Seq.length (getValues sl) && 
		f (Seq.index (getValues sl) place) value && 
		(place - 1 < 0 ||  f (Seq.index (getValues sl) (place-1)) value = false)
	} -> searchResult a f 

(*)
val test2 : #a: eqtype -> #f: (cmp a) -> sl: skipList a f  -> counter : nat {counter < SL.length sl}-> Tot(n: nat{n < SL.length sl})
let test2 #a #f sl counter = lemma_indexes #a #f sl counter; List.hd (getIndex sl counter)
*)

val lemma_index_1_wrapper: #a: eqtype -> #f: (cmp a) -> sl: skipList a f -> 
		counter_global: nat{counter_global < Sl.length sl} -> 
		counter_local : nat{ counter_local <List.length
				(getIndex sl counter_global)} -> Tot(r: nat{ r< Sl.length sl} )
let lemma_index_1_wrapper #a #f sl counter_global counter_local = 
	let i = getIndex sl counter_global in 
	let l = List.index i counter_local in
	lemma_index_1 #a #f sl; l

val lemma_index_2_wrapper: #a: eqtype -> #f: (cmp a) -> sl: skipList a f -> 
		counter_global: nat{counter_global < Sl.length sl} -> 
		counter_local : nat{ counter_local <List.length
				(getIndex sl counter_global)} -> Tot(r: nat{ r > counter_global} )
let lemma_index_2_wrapper #a #f sl counter_global counter_local = 
	let i = getIndex sl counter_global in 
	let l = List.index i counter_local in
	lemma_index_2 #a #f sl; l



(*)

type miou = lst: list nat

val a : x: nat -> Tot(bool)
let a x = x > 5

val test : lstm : miou{List.length lstm > 10 /\ (forall i. a
(List.index lstm i)) } -> counter: nat{counter < List.length lstm} ->
Tot(r:nat{r > 5})


let test lstm counter = List.index lstm counter