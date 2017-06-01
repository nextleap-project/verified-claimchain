module SkipList2.Insertion2

open SkipList2.Statement
open SkipList2.Properties
open SkipList2.Seq.Properties
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
        counter_global < (Sl.length sl -1) /\ 
        (f (getValue sl counter_global) value)
        }
    -> searchResult a f sl value counter_global_previous
| Found:  
    place: nat
        { 
            (place+1) < Sl.length sl /\
            (f value (getValue sl (place +1))) /\
            (f (getValue sl place) value)
        }
     -> searchResult a f sl value counter_global_previous

val change_values: #a: eqtype -> #f: cmp a -> value : a -> sl: skipList a f{Sl.length sl > 0 /\ Seq.mem value (getValues sl) = false} -> 
         place: nat{ 
                (
                    (place = 0 /\ f value (Seq.index (getValues sl) 0))  
                    \/ (    
                            place < (Sl.length sl -1) /\
                            f value (Seq.index (getValues sl) (place+1))/\ 
                            f (Seq.index (getValues sl) place) value
                        )
                )
            }->
        Tot(s3: seq a{Seq.sorted f s3 /\ Seq.length s3 = Sl.length sl+ 1 }) 

let change_values #a #f value sl place = 
    let s = getValues sl in 
    if (place = 0 && f value (Seq.index (getValues sl) 0)) then  
        let s = right_tail_mem_split #a #f value s place in 
        let e = ordered_addition_0 #a #f value s in 
        e
    else         
        let s = main_lemma_split #a #f value s place in 
        let s1 = fst s in 
        let s2 = snd s in sorted_seq_concat_wrapper #a #f value s1 s2

private val searchPlaceIndex: #a: eqtype -> #f: cmp a -> sl : skipList a f{Sl.length sl> 0} -> value: a-> 
                        counter_global: nat{counter_global < (Sl.length sl -1) /\ 
                            (f (Seq.index (getValues sl) counter_global ) value) } -> 
                        counter_local : nat{ counter_local <List.length
                                (getIndex sl counter_global)} ->
                        Tot(searchResult a f sl value counter_global)(decreases(List.length (getIndex sl counter_global) - counter_local))

let rec searchPlaceIndex #a #f sl value counter_global counter_local  = 
    let values = getValues sl in 
    let index = lemma_index_1_2_wrapper #a #f sl counter_global counter_local in 
    lemma_last_element_biggest #a #f sl value;
    if  (f value (Seq.index values index)) then 
        (
            if (f (Seq.index values (index-1)) value ) then 
                Found (index-1)
            else if (counter_local  = (List.length (getIndex sl counter_global) -1)) then
                let result = lemma_index_3 #a #f sl    counter_global in 
                Found counter_global    
            else 
                let counter_local = counter_local + 1 in  searchPlaceIndex #a #f sl value counter_global counter_local 
        )        
    else NotFound index    (* if inf -> not exist*)

val searchPlaceSequence: #a:eqtype-> #f: cmp(a) ->sl: skipList a f{Sl.length sl> 0}-> value : a -> 
            counter_global:nat{counter_global < (Sl.length sl -1) /\ 
            (f (Seq.index (getValues sl) counter_global) value) }  -> 
            Tot(place: nat{ 
                place < (Sl.length sl -1) /\
                (f value (Seq.index (getValues sl) (place+1))) /\
                (f (Seq.index (getValues sl) place) value)
                })
            (decreases (Sl.length sl - counter_global))

let rec searchPlaceSequence #a #f sl value counter_global =
    let result = searchPlaceIndex #a #f sl value counter_global 0 in 
        match result with     
            | Found index ->  index 
            | NotFound counter_global_new ->  
                searchPlaceSequence #a #f sl value (counter_global_new)

val searchPlace : #a : eqtype -> #f: cmp(a)  ->  sl: skipList a f{Sl.length sl > 0} -> value: a-> 
                Tot(place: nat{ 
                (
                    (place = 0 /\ f value (Seq.index (getValues sl) 0))  
                    \/ (    
                            place < (Sl.length sl -1) /\
                            f value (Seq.index (getValues sl) (place+1))/\ 
                            f (Seq.index (getValues sl) place) value
                        )
                )
            })

let searchPlace #a #f  sl value =
    let counter_global = 0 in 
        if (f value 
            (Seq.index 
                (getValues sl) counter_global)) 
        then counter_global
        else if (Sl.length sl = 1) then 
            (lemma_last_element_biggest #a #f sl value; counter_global)
    else
        searchPlaceSequence #a #f sl value counter_global

val change_index_elevel: index2: nat -> place : nat ->level_current: nat-> 
            level_required : nat -> index1: nat -> lst: non_empty_list nat -> 
             Tot(nat * list nat)

let change_index_elevel index2 place level_current level_required index1 lst = 
    if (index2 < place) then (index2, lst)
    else if (index1 < place && index2 > place) then (
        if(level_required < level_current) then 
            let lst_upd = SkipList2.Seq.Properties.upd lst level_current index2 in (place, lst_upd)
        else (index2 +1, lst)
        )
    else (index2 +1, lst)

val change_indexes_llevel: index: list nat -> counter: nat -> place: nat -> level: nat -> index_local: nat -> 
            lst: non_empty_list nat -> 
            Tot(r: list nat{List.length index = List.length r } * list: non_empty_list nat)

let rec change_indexes_llevel index counter place level index_local lst = 
    match index with 
    | [] -> ([], lst)
    | a::tl -> let element = change_index_elevel a place counter level index_local lst in 
               let header = fst element in 
               let changed_list = snd element in 
               let rec_tail = change_indexes_llevel tl (counter+1) place level index_local changed_list in 
               (header:: fst rec_tail, snd rec_tail)

val change_indexes_slevel : #a: eqtype -> #f: cmp a -> 
            sl: skipList a f -> 
            place: nat {place < Sl.length sl}  -> 
            level: nat ->  i: nat {i<Sl.length sl} -> lst: non_empty_list nat  -> 
            Tot(r: seq (non_empty_list nat){Seq.length r = Seq.length (getIndexes sl) } 
            * list: non_empty_list nat )(decreases (Sl.length sl - i))

let rec change_indexes_slevel #a #f sl place level i lst = 
    let index = getIndex sl i in 
    let element = change_indexes_llevel index 0 place level i lst in
    let lst_computed = fst element in 
    let lst_for_place = snd element in  
    let s = Seq.upd (getIndexes sl) i lst_computed in 
    if ((i +1) < Sl.length sl -1 ) 
        then change_indexes_slevel #a #f sl place level (i+1) lst_for_place
    else 
        (s, lst)

val l_append: b: list 'a -> c: list 'a -> Lemma(ensures (List.length (List.append b c ) = List.length b + List.length c))
let rec l_append b c = 
    match b with 
    |[] -> ()
    | hd::tl -> l_append tl c

val append_one_elem: b: list 'a -> c: 'a -> Tot(r: list 'a {List.length r = List.length b + 1})
let append_one_elem b c = let l = List.append b [c] in  l_append b [c]; l

val _create: lst: list 'a -> 
            counter : nat{counter >= List.length lst} -> 
            value : 'a -> Tot(r: list 'a{List.length r = counter})(decreases (counter - (List.length lst)))

let rec _create lst counter value =
    if length lst = counter then lst 
    else _create (append_one_elem lst value) counter value

val create: lst : list 'a -> counter : nat{counter > 0 /\ counter >= List.length lst} -> 
                value : 'a -> Tot(r: non_empty_list 'a{List.length r = counter})
let create lst counter value = _create lst counter value

val change_indexes: #a: eqtype -> #f: cmp a -> sl: skipList a f{Sl.length sl > 0} -> place : nat {place < Sl.length sl} ->
    level : nat{level > 0} -> Tot(r: seq(non_empty_list nat){Seq.length r = Sl.length sl + 1})

let change_indexes #a #f sl place level = 
    let lst = create [] level 0 in 
    let element = change_indexes_slevel #a #f sl place level 0 lst in 
    let seq = fst element in 
        let new_part = snd element in 
        let new_part = SkipList2.Seq.Properties.upd new_part 0 (place + 1) in 
    let seq = Seq.split seq place in 
    let left_part = fst seq in 
    let right_part = snd seq in 
    let center = Seq.create 1 new_part in 
    let left_part = Seq.append left_part center in Seq.append left_part right_part

assume val generate_level:flag: bool-> max_level: int -> Tot(level: nat {max_level >= level /\ level > 0})

val addition: #a: eqtype -> #f: cmp a -> 
        value : a  -> 
        sl: skipList a f {Sl.length sl > 0 /\ Seq.mem value (getValues sl) = false /\ f value (last_element_values sl)} -> 
        max_level: nat -> Tot(r: skipList a f
                                    {(Sl.length r = Sl.length sl + 1)}) 

let addition #a #f value sl max_level  = 
    let place = searchPlace #a #f sl value in 
    let level = generate_level (place = 0) max_level in  
    let values = change_values #a #f value sl place in 
    let indexes = change_indexes #a #f sl place level in 
    Mk values indexes