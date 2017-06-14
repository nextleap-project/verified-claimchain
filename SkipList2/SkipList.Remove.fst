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

 val rebuildSequence: #a: eqtype ->  #f: cmp a -> s:seq a{Seq.sorted f s /\ Seq.length s > 1 } ->  
                place: nat {place < Seq.length s - 1} ->
                Tot (r: seq a {Seq.sorted f r /\ Seq.length r = Seq.length s - 1})

assume val concat: #a: eqtype ->#f: cmp a ->  s1 : seq a {Seq.sorted f s1 } -> s2: seq a {Seq.sorted f s2} -> 
    Tot(s3: seq a {Seq.sorted f s3 /\ Seq.length s3 = Seq.length s1 + Seq.length s2})

assume val lemma_split: #a : eqtype -> #f: cmp a-> 
            s: seq a {Seq.length s > 0 /\ Seq.sorted f s} ->
                                place : nat {place <= Seq.length s} -> 
                                Lemma (ensures 
                                    ( 
                                        (Seq.sorted f (fst(Seq.split s place))) /\ 
                                        (Seq.sorted f (snd(Seq.split s place)))
                                ))

let rebuildSequence #a #f s place = 
    let s1, s2 = Seq.split s place in 
    assert(Seq.length s1 + Seq.length s2 = Seq.length s);
    lemma_split #a #f s place;
    let s3, s4 = Seq.split s2 1 in 
    assert(Seq.length s4 = Seq.length s - Seq.length s1 -1);
    lemma_split #a #f s2 1;
    assert (Seq.sorted f s4);
    assert(Seq.sorted f s1);
    let r = concat #a #f s1 s4    
    in r            

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
