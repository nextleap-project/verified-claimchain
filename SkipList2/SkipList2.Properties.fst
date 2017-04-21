module SkipList2.Properties

open FStar.Seq
open FStar.Option
open SkipList2.Statement
module List = FStar.List.Tot

type cmp (a:eqtype) = f:(a -> a -> Tot bool){total_order a f}

(*)
assume val lemma_index_1 : #a: eqtype -> #f:(cmp a) -> sl: skipList a f -> 
	Lemma(ensures 
		(forall (counter:nat{counter<(length sl)}). List.for_all (fun (x:nat) -> x < length sl) (getIndex sl counter)))
*)

assume val lemma_index_1: #a: eqtype -> #f: (cmp a) -> sl: skipList a f  -> 
	Lemma(ensures
		(forall (counter_global: nat {counter_global < length sl}) 
		(counter_local : nat 
			{counter_local <List.length
				(getIndex sl counter_global)}). 
		(fun (x: nat) -> x < length sl) (List.index(getIndex sl counter_global) counter_local)))

assume val lemma_index_2: #a: eqtype -> #f: (cmp a) -> sl: skipList a f  -> 
	Lemma(ensures
		(forall (counter_global: nat {counter_global < length sl}) 
		(counter_local : nat 
			{counter_local <List.length
				(getIndex sl counter_global)}). 
		(fun (x: nat) -> x > counter_global) (List.index(getIndex sl counter_global) counter_local)))

assume val lemma_index_3 : #a : eqtype -> #f:(cmp a) -> sl: skipList a f ->
	Lemma(ensures
		(forall (counter : nat {counter < (length sl - 1)}).
				List.index (getIndex sl counter) (List.length (getIndex sl counter) -1 ) = (counter + 1)
		)
	)
(*)
val equal_whole_slice: #a: eqtype -> #f:(cmp a) ->
			s:seq a {sorted f s} -> 
			Lemma (ensures(equal (Seq.slice s 0 (Seq.length s)) s))
let equal_whole_slice #a #f s = ()

val lemma_tail_size: s: seq 'a{length s > 0} -> Lemma (ensures (Seq.length s - 1 = (Seq.length (Seq.tail s ))))
let lemma_tail_size s = ()			

val lemma_sorted_tail : #a: eqtype -> #f:(cmp a) ->
			s:seq a {sorted f s && length s > 0} -> 
			Lemma (ensures (sorted f (Seq.tail s)))
let lemma_sorted_tail #a #f s = ()	

val lemma_tail_slice : #a: eqtype -> #f:(cmp a) ->
			s:seq a {sorted f s && Seq.length s > 0} ->
			Lemma (ensures
				(equal (Seq.tail(Seq.slice s 0 (Seq.length s))) (Seq.tail s)
			))	
let lemma_tail_slice #a #f s= ()

val lemma_one_step_slice: #a : eqtype -> #f:(cmp a) -> 
			s: seq a {sorted f s  && Seq.length s > 0} ->
			Lemma (ensures
				(equal (Seq.slice s 1 (Seq.length s)) (Seq.tail(Seq.slice s 0 (Seq.length s))))
			)
let lemma_one_step_slice #a #f s = ()

(*slice j<=length s*)
val lemma_one_step_slice_gen: #a: eqtype -> #f:(cmp a) -> 
			s: seq a {sorted f s  && Seq.length s > 1} ->
			n: nat { (n+1) <= length s} ->
			Lemma (ensures (equal (Seq.slice s (n+1) (Seq.length s)) (Seq.tail(Seq.slice s n (Seq.length s)))))

let lemma_one_step_slice_gen #a #f s n = ()			

val l1 : #a: eqtype -> #f:(cmp a) ->s: seq a {sorted f s } ->
			Lemma (ensures(sorted f (Seq.slice s 0 (Seq.length s))))

let l1 #a #f s = equal_whole_slice #a #f s	

val lemma_level_down: #a : eqtype -> #f:(cmp a) ->
			s: seq a {sorted f s  && length s > 1 } ->
			n: nat { n < length s} ->
			Lemma 
			(requires (sorted f (Seq.slice s n (Seq.length s ))))
			(ensures(sorted f (Seq.slice s (n+1) (Seq.length s))))

let lemma_level_down #a #f s n=  
		lemma_one_step_slice_gen #a #f s n 	
		
val sorted_slice: #a : eqtype -> #f:(cmp a) -> 
			s: seq a {sorted f s && length s > 1}  -> 
			n: nat{(n < length s )} -> 
			Lemma(ensures (sorted f (Seq.slice s n (Seq.length s))))(decreases  (n))

let rec sorted_slice  #a #f s n = 
	if n = 0 then l1 #a #f s 
	else if (n = 1) then (sorted_slice #a #f s (n-1))
	else (sorted_slice #a #f s (n-1); lemma_level_down #a #f s (n-1))
