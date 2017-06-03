module SkipList2.Split

open SkipList2.Statement
open SkipList2.Properties
open SkipList2.Seq.Properties
open FStar.Option
open FStar.Seq
open FStar.List.Tot

module Sl = SkipList2.Statement
module List = FStar.List.Tot
module Seq = FStar.Seq

(* proved by Ben *)
assume val lemma_split: #a : eqtype -> #f: cmp a-> s: seq a 
								{Seq.sorted f s /\ Seq.length s > 0} ->
								place : nat {place < Seq.length s} -> 
								Lemma (ensures 
									( 
										(Seq.sorted f (fst(Seq.split s place))) /\ 
										(Seq.sorted f (snd(Seq.split s place)))
								))

								
assume val lemma_more : #a: eqtype -> #f: cmp a -> sl: skipList a f {Sl.length sl > 0} -> 
		Lemma(ensures(forall 
			(counter_global : nat{counter_global < Sl.length sl}) 
			(counter_local : nat {counter_local < List.length (getIndex sl counter_global)}) .
			List.index (getIndex sl counter_global) counter_local > counter_global))

assume val lemma_mem: #a: eqtype -> #f: cmp a ->max: a -> 
		sl: skipList a f {forall y. Seq.mem y (getValues sl) ==> f y max} -> 
		place: nat {place < Sl.length sl - 1} -> 
		Lemma(ensures (let fst, snd = Seq.split (getValues sl) place in forall y. Seq.mem y fst ==> f y max)) 



val _reg_indexes_elem: 
		element : nat  -> 
		predicate: (nat-> bool) ->
		predicate_l : (nat -> nat) ->
		predicate_r : (nat -> nat) -> Tot nat

let _reg_indexes_elem element predicate predicate_l predicate_r = 
		if predicate element then predicate_l element else predicate_r	element					

val _reg_indexes_lst: 
		l: list nat-> 
		predicate: (nat -> bool) ->
		predicate_l : (nat -> nat) ->
		predicate_r : (nat -> nat) ->
		Tot(r: list nat {List.length l = List.length r})

let rec _reg_indexes_lst l predicate predicate_l predicate_r = 
		match l with 
		| hd:: tl -> _reg_indexes_elem hd predicate predicate_l predicate_r :: 
						_reg_indexes_lst tl predicate predicate_l predicate_r
		| [] -> []				

val reg_indexes_seq : 
		s: seq(non_empty_list nat) -> 
		counter: nat {counter < Seq.length s - 1} ->(*for all elements excluding the last one *)
		predicate: (nat -> bool) ->
		predicate_l : (nat -> nat) ->
		predicate_r : (nat -> nat) ->
		Tot(r: seq(non_empty_list nat) {Seq.length r = Seq.length s})
		(decreases(Seq.length s - counter))

let rec reg_indexes_seq  s counter predicate predicate_l predicate_r = 
		let lst = Seq.index s counter in 
		let lst_new = _reg_indexes_lst lst predicate predicate_l predicate_r in
		assert(List.length lst_new = List.length lst);
		let s = Seq.upd s counter lst_new in 
		if ((counter+1) < Seq.length s -1 ) then 
			reg_indexes_seq s (counter +1) predicate predicate_l predicate_r
		else s

val reg_indexes: (* generate predicates and to call the needed functions for both seqs*)
		s1: seq(non_empty_list nat){Seq.length s1 > 1}  ->
		place: nat -> Tot(r1: seq(non_empty_list nat) {Seq.length s1 = Seq.length r1})

let reg_indexes s1 place = 
		let left_predicate (a:nat) = (a >= place) in 
		let left_predicate_l (a:nat) = a in 
		let left_predicate_r (a:nat) = place in 
		let r1 = reg_indexes_seq s1 0 left_predicate left_predicate_l left_predicate_r in r1

val add_infinity: 
		#a: eqtype -> #f: cmp a -> s: seq a{Seq.sorted f s /\ Seq.length s > 0} -> 
		fst_i: seq (non_empty_list nat) -> 
		max: a {forall y. Seq.mem y s ==> f y max} -> 
		Tot(r: seq a {Seq.sorted f r /\ Seq.length r = Seq.length s + 1 } *
			i: seq (non_empty_list nat) {Seq.length i = Seq.length fst_i + 1})


(*val ordered_addition_left_mem: #a : eqtype -> #f: cmp a -> pivot : a -> 
		s1: seq a {Seq.length s1 > 0 /\ Seq.sorted f s1 /\ (forall y. Seq.mem y s1 ==> f y pivot)} ->
		Tot (s3: seq a {Seq.sorted f s3}) *)
let add_infinity #a #f s fst_i max = 
	let r = ordered_addition_left_mem #a #f max s in 
	let i_inf = [0] in 
	let i = snoc fst_i i_inf in 
	(r, i)	

val split: #a: eqtype -> #f: cmp a -> 
			sl : skipList a f {Sl.length sl > 0} -> 
			place: nat {place > 0 /\ place < Sl.length sl -1} -> 
			max: a {forall y. Seq.mem y (getValues sl) ==> f y max} -> 
			Tot(skipList a f * skipList a f)


val right_part_list: place : nat ->l_temp: non_empty_list nat->  indexes: list nat{
	(forall (counter_local: nat { counter_local < List.length indexes}) . 
		List.index indexes counter_local > place )}-> counter: nat {counter <= List.length indexes} ->
	Tot(r:non_empty_list nat)(decreases (List.length indexes - counter))
let rec right_part_list place l_temp indexes counter = 
	if (counter = List.length indexes) 
		then l_temp 
		else
			let elem = List.index indexes counter in 
			assert(elem > place); 
			let l_temp = List.append l_temp [elem - place] in 
				right_part_list place l_temp indexes (counter +1) 

val right_part: #a: eqtype -> #f: cmp a ->place : nat  -> 
				sl: skipList a f {Sl.length sl > 0} -> 
				s_temp : seq (non_empty_list nat) {Seq.length s_temp= Sl.length sl - place} ->
				i: nat{place + i < Sl.length sl -1} -> 
				Tot (r: seq (non_empty_list nat){Seq.length r = Sl.length sl - place })(decreases (Sl.length sl - i))

let rec right_part #a #f place sl s_temp i = 
	let indexes = getIndex sl (place + i) in lemma_more #a #f sl;
	assert(forall (counter_local: nat { counter_local < List.length indexes}) . List.index indexes counter_local > place );
	let fst_elem = List.index indexes 0 in 
	assert (fst_elem > place);
	let lst = right_part_list place [fst_elem - place] indexes 1 in 
	let s_temp = Seq.upd s_temp i lst in 
	let i = i + 1 in 
	if (place + i< Sl.length sl -1) 
		then 
			right_part #a #f place sl s_temp i 
		else
			s_temp

let split #a #f sl place max = 
	let fst_v, snd_v = Seq.split (Sl.getValues sl) place in lemma_split #a #f (Sl.getValues sl) place;
	let fst_i, snd_i = Seq.split (Sl.getIndexes sl) place in lemma_mem #a #f max sl place; 
	let fst_v, fst_i = add_infinity #a #f fst_v fst_i max in 
	let fst_i = reg_indexes fst_i place in 
	let snd_i = right_part #a #f place sl (Seq.create (Sl.length sl - place) [place + 1]) 0 in  
	let sl1 = Sl.Mk #a #f fst_v fst_i in 
	let sl2 = Sl.Mk #a #f snd_v snd_i in 
	(sl1, sl2)


