module Test

open FStar.Seq
open FStar.Option
open SkipList2.Statement
module List = FStar.List.Tot
module Sl = SkipList2.Statement


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

val seqLast: s: seq 'a{Seq.length s > 0} -> Tot('a)
let seqLast s = let len = Seq.length s in Seq.index s (len -1)

val tail_mem : 	#a : eqtype -> #f: cmp a -> 
			pivot : a -> 
			s : seq a {Seq.sorted f s /\ Seq.length s > 0  /\ f (seqLast s) pivot } ->
			Lemma (ensures (forall y. (Seq.mem y s ==> f y pivot)))(decreases (Seq.length s))

let rec tail_mem #a #f pivot s = 
	if (Seq.length s = 1) then () else
	tail_mem #a #f pivot (Seq.tail s)

val tail_mem_wrapper: #a : eqtype -> 
			#f: cmp a -> 
			pivot : a -> 
			s : seq a {Seq.sorted f s /\ Seq.length s > 0 /\ f (seqLast s) pivot } -> 
			Tot(r: seq a {(forall y. (Seq.mem y r ==> f y pivot))})

let tail_mem_wrapper #a #f pivot s = tail_mem #a #f pivot s; s	

val sorted_seq_concat_wrapper : #a: eqtype -> #f: cmp a ->pivot : a -> s1: seq a 
			{Seq.sorted f s1 /\ (forall y. (Seq.mem y s1 ==> f y pivot))} ->  
			s2: seq a {Seq.sorted f s2 /\ (forall y. (Seq.mem y s2 ==> f pivot y))}  ->
		  	Tot(s3: seq a{Seq.sorted f s3 /\ Seq.length s3 = Seq.length s1 + Seq.length s2 + 1}) 

let sorted_seq_concat_wrapper #a #f pivot s1 s2 = 
		let s3 = (Seq.append s1 (cons pivot s2)) in 
		FStar.Seq.Properties.sorted_concat_lemma #a f s1 pivot s2; 
		s3  

val ordered_addition_l: #a : eqtype -> #f : cmp a -> pivot : a -> 
			s1: seq a {Seq.length s1 > 0
			/\ Seq.sorted f s1 /\ f (seqLast s1) pivot} ->
			Tot(s3: seq a {Seq.sorted f s3}) 

let ordered_addition_l #a #f pivot s1 = 
		let s2 = Seq.createEmpty in 
		let s1 = tail_mem_wrapper #a #f pivot s1 in 
		sorted_seq_concat_wrapper #a #f pivot s1 s2			



(* val snoc : #a:Type -> seq a -> a -> Tot (seq a)
let snoc #a s x = Seq.append s (Seq.create 1 x)*)
val ordered_l_lemma: #a: eqtype -> #f: cmp a -> pivot : a -> s1: seq a{Seq.length s1 > 0 /\ Seq.sorted f s1 /\ f (seqLast s1) pivot} 
			-> Lemma(ensures (Seq.sorted f (Seq.append s1 (cons pivot (Seq.createEmpty)))))

let ordered_l_lemma #a #f pivot s1 = 
	let s2 = Seq.createEmpty in 
	let s1 = tail_mem_wrapper #a #f pivot s1 in 
	let s3 = (Seq.append s1 (cons pivot s2)) in 
	FStar.Seq.Properties.sorted_concat_lemma #a f s1 pivot s2 
 
private val ordered_l_lemma1 : #a: eqtype -> #f: cmp a -> pivot : a -> 
			s1: seq a {Seq.length s1> 0 /\ Seq.sorted f s1 /\ f (seqLast s1) pivot} ->
			Lemma(ensures(
				Seq.eq 
					(Seq.append (snoc s1 pivot) Seq.createEmpty)
					(Seq.append s1 (cons pivot (Seq.createEmpty))) = true))	

let ordered_l_lemma1 #a #f pivot s1 = ()

private val ordered_l_lemma2 : #a: eqtype -> #f: cmp a -> pivot : a -> 
		s1: seq a {Seq.length s1 > 0 /\ Seq.sorted f s1 /\ f (seqLast s1) pivot} -> 
			Lemma(ensures (
				Seq.eq 
					(Seq.snoc s1 pivot)
					(Seq.append s1 (cons pivot (Seq.createEmpty)))
				= true))
let ordered_l_lemma2 #a #f pivot s1 = ()

private val ordered_l_lemma3:  #a: eqtype -> #f: cmp a -> pivot : a -> 
			s1: seq a{Seq.length s1 > 0 /\ Seq.sorted f s1 /\ f (seqLast s1) pivot} 
			-> Lemma(ensures (Seq.sorted f (Seq.snoc s1 pivot)))

let ordered_l_lemma3 #a #f pivot s1 = 
	let s2 = Seq.createEmpty in 
	let s1 = tail_mem_wrapper #a #f pivot s1 in 
	let s3 = (Seq.append s1 (cons pivot s2)) in 
	FStar.Seq.Properties.sorted_concat_lemma #a f s1 pivot s2; ordered_l_lemma2 #a #f pivot s1			

val ordered_addition_r: 
	#a: eqtype -> #f: cmp a -> pivot: a -> s2: seq a {Seq.sorted f s2 /\ (forall y. (Seq.mem y s2 ==> f pivot y))} ->
				Tot(s3: seq a{Seq.sorted f s3 /\ Seq.length s3 = Seq.length s2 + 1}) 

let ordered_addition_r #a #f pivot s2 = 
		let s1 = Seq.createEmpty in 
		sorted_seq_concat_wrapper #a #f pivot s1 s2 

val lemma_temp1: #a: eqtype -> #f: cmp a -> s: seq a{Seq.sorted f s} -> pl: nat {pl < Seq.length s -1} ->
				Lemma(ensures(f (Seq.index s pl ) (Seq.index s (pl+1))))

let lemma_temp1 #a #f s pl = if pl = 0 then () else admit()

val lemma_temp: #a : eqtype -> #f: cmp a -> place: nat{place > 0}-> 
					s: seq a {Seq.sorted f s /\ place < Seq.length s -1} -> 
					Lemma
						(requires
							(Seq.sorted f (fst (Seq.split s place))))
						(ensures 
							(Seq.sorted f (fst (Seq.split s (place+1))))
					) 

let lemma_temp #a #f place s =  
	let splitted_seq = fst (Seq.split s place) in 
	let last_element_seq = seqLast splitted_seq in 
	let element = Seq.index s place in 
	lemma_temp1 #a #f s (place-1);
	ordered_l_lemma3 #a #f element splitted_seq;
	assert(Seq.eq (Seq.snoc splitted_seq element) (fst(Seq.split s (place+1))) = true)

val lemma_left_split_sorted: #a: eqtype -> #f: cmp a -> place: nat ->  
							s: seq a {Seq.sorted f s /\ place < Seq.length s - 1} ->
							Lemma(ensures (Seq.sorted f (fst (Seq.split s place)))) 

let rec lemma_left_split_sorted #a #f place s =  
	if place = 1 then () else admit()

val lemma_right_split_sorted: #a : eqtype -> #f : cmp a -> place : nat -> 
						s: seq a {Seq.sorted f s /\ place < Seq.length s - 1} -> 
						Lemma (ensures (Seq.sorted f (snd (Seq.split s place))))

let rec lemma_right_split_sorted #a #f place s = 
	if place = Seq.length s then () else admit() 



