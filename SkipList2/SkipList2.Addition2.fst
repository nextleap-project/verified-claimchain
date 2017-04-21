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
| NotFound: sl: skipList a f -> result : nat {result < SkipList2.Statement.length sl}-> searchResult a f 
| Found: sl: skipList a f ->  value: a -> 
    (place: nat{ 
                            place < Sl.length sl /\
                            f (Seq.index (getValues sl) place) value /\
                            (place - 1 < 0 \/  f (Seq.index (getValues sl) (place-1)) value = false)
                        })
     -> searchResult a f 

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

val lemma_index_1_2_wrapper: #a: eqtype -> #f: (cmp a) -> sl: skipList a f -> 
        counter_global: nat{counter_global < Sl.length sl} -> 
        counter_local : nat{ counter_local <List.length
                (getIndex sl counter_global)} -> Tot(r: nat{ r > counter_global /\ r< Sl.length sl} )
let lemma_index_1_2_wrapper #a #f sl counter_global counter_local = 
    let i = getIndex sl counter_global in 
    let l = List.index i counter_local in
    lemma_index_1 #a #f sl; lemma_index_2 #a #f sl; l    

val lemma_index_3_wrapper : #a : eqtype -> #f:(cmp a) -> sl: skipList a f -> 
                            counter_global: nat {counter_global < Sl.length sl}
    -> Tot(r: nat {r = counter_global + 1})
let lemma_index_3_wrapper #a #f sl counter_global = 
    let index = List.index(getIndex sl counter_global) (List.length (getIndex sl counter_global) -1) in 
    lemma_index_3 #a #f sl; index
            
private val temp_func: #a: eqtype -> #f: cmp a -> 
                        sl : skipList a f -> 
                        value: a-> 
                        counter_global: nat{counter_global < Sl.length sl /\ 
                            (f (Seq.index (getValues sl) counter_global) value = false) } -> 
                        counter_local : nat{ counter_local <List.length
                                (getIndex sl counter_global)} ->
                        Tot(searchResult a f )(decreases(List.length (getIndex sl counter_global) - counter_local))
let rec temp_func #a #f sl value counter_global counter_local  = 
    let values = getValues sl in 
    let index = lemma_index_1_2_wrapper #a #f sl counter_global counter_local in 
    if  (f (Seq.index values index) value) then (*more*)
        (
            if (f (Seq.index values (index - 1)) value = false) then 
                Found sl value index
            else if (counter_local = List.length (getIndex sl counter_global)-1) then
                let index = lemma_index_3 #a #f sl; index in 
                Found sl value index    
            else 
                let counter_local = counter_local + 1 in  temp_func #a #f sl value counter_global counter_local 
        )        
    else NotFound sl index  