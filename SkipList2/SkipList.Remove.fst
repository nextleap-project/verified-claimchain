module SkipList2.Remove

open SkipList2.Statement
open SkipList2.Properties
open SkipList2.Seq.Properties
open FStar.Option
open FStar.Seq
open FStar.List.Tot

module Sl = SkipList2.Statement
module List = FStar.List.Tot
module Seq = FStar.Seq


assume val lemma_more : #a: eqtype -> #f: cmp a -> sl: skipList a f {Sl.length sl > 0} -> 
        Lemma(ensures(forall 
            (counter_global : nat{counter_global < Sl.length sl}) 
            (counter_local : nat {counter_local < List.length (getIndex sl counter_global)}) .
            List.index (getIndex sl counter_global) counter_local > counter_global))

 val rebuildIndexesList:#a: eqtype -> #f : cmp a -> sl: skipList a f {Sl.length sl > 1} ->  
                                 index: nat -> lst: non_empty_list nat
                                    {forall (counter_local: nat {counter_local < List.length lst}).
                                    List.index lst counter_local > index} ->
                                lst_return : non_empty_list nat ->    
                                counter: nat {counter < List.length lst} -> 
                                lst_deleted: non_empty_list nat -> 
                                 place: nat ->
                                   ML(non_empty_list nat)

let rec rebuildIndexesList #a #f sl index lst lst_return counter lst_deleted place = 
    let hd = List.index lst counter in 
    let header = 
        if (hd < place) then hd 
        else if (hd = place) then 
            (if (List.length lst_deleted > counter) 
                then  (List.index lst_deleted counter) 
                else (Sl.length sl - 2)
            )
        else (hd -1) 
    in 
    let lst_return = SkipList2.Seq.Properties.upd lst_return counter header in 
    if ((counter + 1) < List.length lst) 
        then rebuildIndexesList #a #f sl index lst lst_return (counter +1) lst_deleted place
    else lst_return                        

val rebuildIndexesSeq: #a: eqtype -> #f: cmp a -> sl: skipList a f {Sl.length sl > 1} -> 
            place : nat {place < Sl.length sl - 1} ->
            new_indexes: seq (non_empty_list nat) {Seq.length new_indexes =  Sl.length sl - 1} -> 
            counter: nat {counter < Sl.length sl} (* for the last - just copy*) -> 
            ML(r: seq (non_empty_list nat) {Seq.length r = Sl.length sl - 1})

let rec rebuildIndexesSeq #a #f sl place new_indexes counter = 
            if (counter = place) then 
                rebuildIndexesSeq #a #f sl place new_indexes (counter +1) (* just skip the element*)
            else 
                let indexes = getIndex sl counter in lemma_more #a #f sl;
                let rebuilt_list = rebuildIndexesList #a #f sl counter indexes indexes 0 (getIndex sl place) place in
                let index_for_update = if counter > place then (counter - 1) else counter in  
                let new_indexes = Seq.upd new_indexes index_for_update rebuilt_list in
                if ((counter +1) < Sl.length sl) then 
                    rebuildIndexesSeq #a #f sl place new_indexes (counter +1) 
                else new_indexes     


val rebuildIndexes: #a: eqtype -> #f: cmp a ->sl: skipList a f {Sl.length sl > 1} -> 
            place : nat {place < Sl.length sl - 1} -> 
            ML(r: seq (non_empty_list nat){ Seq.length r = Sl.length sl - 1})

let rebuildIndexes #a #f sl place = 
        let seq_replace = Seq.create (Sl.length sl - 1) [0] in 
        rebuildIndexesSeq #a #f sl place seq_replace 0 

val concat: #a: eqtype ->#f: cmp a ->  s1 : seq a {Seq.sorted f s1 } -> s2: seq a {Seq.sorted f s2 /\
(Seq.length s1 > 0 /\ Seq.length s2 > 0 /\ f (seqLast s1) (seqFirst s2))} -> 
    Tot(s3: seq a {Seq.sorted f s3 /\ Seq.length s3 = Seq.length s1 + Seq.length s2})

let concat #a #f s1 s2 = 
        let pivot = seqFirst s2 in 
        let seq2 = Seq.tail s2 in 
        assert(f (seqLast s1) pivot);
        if (Seq.length seq2 = 0 ) then 
            ordered_addition_l #a #f pivot s1
        else (
            tail_mem_left_wrapper #a #f pivot seq2; 
            assert(forall y. (Seq.mem y seq2 ==> f pivot y));
            assert(Seq.sorted f seq2);
            tail_mem #a #f pivot s1; 
            assert(forall y. (Seq.mem y s1 ==> f y pivot));
            let r = sorted_seq_concat_wrapper #a #f pivot s1 seq2 
            in r
        )


assume val lemma_split: #a : eqtype -> #f: cmp a-> 
            s: seq a {Seq.length s > 0 /\ Seq.sorted f s} ->
                                place : nat {place <= Seq.length s} -> 
                                Lemma (ensures 
                                    ( 
                                        (Seq.sorted f (fst(Seq.split s place))) /\ 
                                        (Seq.sorted f (snd(Seq.split s place)))
                                ))

assume val lemma_sorted : #a: eqtype -> #f : cmp a -> s: seq a {Seq.sorted f s} ->
            place : nat {place > 0 /\ place < Seq.length s -1 } -> 
            Lemma (ensures (f (Seq.index s (place -1)) (Seq.index s place)))

val rebuildSequence: #a: eqtype ->  #f: cmp a -> s:seq a{Seq.sorted f s /\ Seq.length s > 1 } ->  
                place: nat {place < Seq.length s - 1} ->
                Tot (r: seq a {Seq.sorted f r /\ Seq.length r = Seq.length s - 1})


let rebuildSequence #a #f s place = 
    let s1, s2 = Seq.split s place in (*place < Seq.length s -1  - it means that there is at least ONE element in right seq*)
    lemma_split #a #f s place;
    let s3, s4 = Seq.split s2 1 in(* s3 has one element, while s4 could not have any*)
    lemma_split #a #f s2 1;
    if Seq.length s1 = 0 then s4
    else if (Seq.length s4 = 0) then s1
    else
        (
            lemma_sorted #a #f s place; 
            assert(f (Seq.index s (place -1)) (Seq.index s (place)));
            assert(f (seqLast s1) (seqFirst s4));    
            concat #a #f s1 s4
        )        

val remove: #a: eqtype -> #f : cmp a -> 
        sl: skipList a f {Sl.length sl > 1} -> 
        place : nat {place < Sl.length sl - 1} ->
        ML(r: skipList a f {Sl.length sl = Sl.length r + 1})

let remove #a #f sl place = 
    let values = Sl.getValues sl in 
    let indexes = Sl.getIndexes sl in 
    let values_new = rebuildSequence #a #f values place in 
    let indexes_new = rebuildIndexes #a #f sl place in 
    Sl.Mk #a #f values_new indexes_new 
