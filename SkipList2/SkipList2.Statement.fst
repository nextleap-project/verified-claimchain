module SkipList2.Statement

open FStar.Seq
open FStar.Option
open SkipList2.Seq.Properties

module Seq = FStar.Seq.Base
module SeqPr = FStar.Seq.Properties
module List = FStar.List.Tot


type cmp (a:eqtype) = f:(a -> a -> Tot bool){total_order a f}
type non_empty_list 'a = lst: list 'a{Cons? lst}

(* total order f a a = true *)
(*the easiest ex is <= *)
type skipList(a:eqtype) (f:cmp a) = 
| Mk:  values: seq(a)
			{sorted f values/\ length values >0 /\
				(forall (e:a). f e (let length = length values in 
										let length = length -1 in 
											Seq.index values length ) )
				 }-> 
		indexes : seq(non_empty_list nat)
		{Seq.length values = Seq.length indexes} -> r: skipList a f

val getValues : #a: eqtype -> #f: cmp(a)-> sl:skipList a f-> Tot(seq a)
let getValues #a #f sl = 
	match sl with 
	| Mk v i -> v

val length: #a: eqtype -> #f: cmp(a) -> sl: skipList a f -> Tot(nat)
let length #a #f sl =
	let values = getValues sl in 
	Seq.length values	

val lemma_lengthSkipList: #a: eqtype -> #f: cmp a -> sl: skipList a f -> Lemma (ensures (length sl > 0))
let lemma_lengthSkipList #a #f sl = ()		

val getIndexes: #a : eqtype-> #f: cmp(a) -> sl:skipList a f -> Tot(seq(non_empty_list nat))
let getIndexes #a #f sl = 
	match sl with 
	| Mk v i -> i

val getValue: #a:eqtype-> #f: cmp(a) -> sl: skipList a f->nth:nat{nth <  length sl} -> Tot(a)
let getValue #a #f sl nth = 
	let values = getValues #a sl in Seq.index values nth


val getIndex: #a:eqtype-> #f: cmp(a) -> sl:skipList a f-> nth : nat{nth <  length sl} -> Tot(non_empty_list nat)
let getIndex #a #f sl nth = 
	let indexes = getIndexes #a sl in Seq.index indexes nth

val getCurrentValue: #a: eqtype -> #f:cmp(a) -> sl: skipList a f -> Tot(a)
let getCurrentValue #a #f sl = 
	getValue #a #f sl 0

val getCurrentIndex: #a : eqtype -> #f:cmp(a) -> sl : skipList a f -> Tot(non_empty_list nat)
let getCurrentIndex #a #f sl = 
	getIndex #a #f sl 0

val getTuple: #a:eqtype-> #f: cmp(a) -> sl: skipList a f->nth:nat{nth <  length sl} -> Tot(a*list nat)
let getTuple #a #f sl nth = 
	let v = getValue #a sl nth in 
	let i = getIndex #a sl nth in (v,i)


val hd_: #a:eqtype-> #f: cmp(a) -> sl:skipList a f-> option(a)
let hd_ #a #f sl = 
	let values = getValues #a sl in 
	if (Seq.length values > 0) 
		then Some (getValue #a sl 0)
	else 
		None

val hd: #a:eqtype-> #f: cmp(a) -> sl:skipList a f -> Tot(a)
let hd #a #f sl = 
	getValue #a sl 0

val split_sized : s1: seq 'a -> s2:seq 'a{Seq.length s1 = Seq.length s2} -> 
				  Lemma (ensures forall a. Seq.length (snd(split s1 a)) = Seq.length (snd(split s2 a)))
				  (decreases (Seq.length s1))

let rec split_sized s1 s2 = 
	let decrease = 1 in 
	if (Seq.length s1 > decrease) then 
		let s1 = snd(split s1 decrease) in 
		let s2 = snd(split s2 decrease) in split_sized s1 s2 
	else ()	
	

val tl : #a:eqtype-> #f: cmp(a) -> sl: skipList a f{length sl >1 } -> Tot(skipList a f) 
let tl #a #f sl = 
	let values = getValues sl in 
	let indexes = getIndexes sl in 
	let values = snd (split values 1) in 
	let indexes = snd (split indexes 1) in 
	Mk values indexes

val tl_ : #a:eqtype-> #f: cmp(a) -> sl:skipList a f-> Tot(option(skipList a f))
let tl_ #a #f sl = 
	if Seq.length(getValues sl) >1 then 
	Some(tl sl) else None

val tl_countered : #a : eqtype -> #f: cmp(a) -> 
					slo: (option (skipList a f)) -> counter : nat -> 
					Tot(option (skipList a f))(decreases (counter))

let rec tl_countered #a #f slo counter = 
	if counter = 0 then slo 
	else match slo with 
	| None -> None 
	| Some sl -> let slo = tl_ sl 
in tl_countered #a #f slo (counter - 1)

val tlcountered: #a: eqtype -> #f:cmp(a) -> sl: skipList a f -> 
				counter : nat{ counter < length sl} -> Tot(skipList a f)(decreases(length sl))
let rec tlcountered #a #f sl counter = 
	if counter = 0 then sl else
    tlcountered (tl sl) (counter -1)

private val lst_z_g: lst: non_empty_list nat ->value_to_put: nat -> elements_number: nat -> counter : nat {counter <= elements_number}-> 
	Tot(non_empty_list nat)(decreases (elements_number - counter))

let rec lst_z_g lst value_to_put elements_number counter  = 
	if (counter) = elements_number then lst else
	let lst = List.append lst [value_to_put] in 
	lst_z_g lst value_to_put elements_number (counter + 1) 

val create : #a : eqtype -> #f:cmp a -> 
	value_max : a{forall (e : a). f e value_max} -> 
	elements_number: nat {elements_number > 0} ->
	Tot(skipList a f)

let create #a #f value_max elements_number = 
	let seq_values = create #a 1 value_max in 
	let lst_indexes = lst_z_g [0] 0 elements_number 0 in 
	let seq_indexes = create 1 lst_indexes in 
	Mk seq_values seq_indexes

val last_element_indexed: #a: eqtype -> #f: cmp a -> sl: skipList a f {length sl > 1} -> 
							counter_global: nat{counter_global < (length sl -1)} -> 
		Tot nat 
let last_element_indexed #a #f sl counter_global = 
	let ind = getIndex sl counter_global in 
	let len = (List.length ind) -1  in 
	List.index ind len

val last_element_values: #a: eqtype -> #f: cmp a -> sl: skipList a f -> Tot(a)
let last_element_values #a #f sl = 
	let values = getValues sl in 
	let length = Seq.length values -1 in 
	Seq.index values length 

(*)
val lemma_last_element_biggest: #a : eqtype -> 
		#f: cmp a  ->  sl: skipList a f ->
		Lemma (ensures (forall (i:nat {i < (length sl -1)}). 
			f (getValue sl i) (last_element_values sl)))	

let lemma_last_element_biggest #a #f sl = () *)
