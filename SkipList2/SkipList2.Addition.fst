module SkipList2.Addition

open FStar.Seq
open FStar.List
open SkipList2.Statement


type searchResult = 
|Found: result: bool -> searchResult
|NotFound: result : nat -> searchResult

val sequence_change: sq: seq 'a ->place: nat {Seq.length sq > place} -> value: 'a ->Tot (result: seq 'a{Seq.length sq = Seq.length result})
let sequence_change #a sq place value = upd sq place value

private val f: lst: (non_empty_list nat)-> counter: nat -> lst_previous :list nat -> level:nat -> place : nat -> ML(non_empty_list nat)
let rec f lst counter lst_previous level place =
        match lst_previous with
            |hd:: tl -> let elem =
                (if hd = place && counter > level then
                    [hd + 1] else [hd])
                    in f (List.append lst elem) (counter +1) tl level place
            |[] -> lst

val tree_treatment_before : lst_previous: (non_empty_list nat) -> level:nat-> place : nat-> ML(non_empty_list nat)
let tree_treatment_before lst_previous level place =
    let prelist = [] in 
    match lst_previous with |hd::tl -> 
        let prelist = 
                if hd = place (* counter > 0 by default*)
                    then List.append prelist [hd+1] 
                else 
                    List.append prelist [hd] 
        in 
            f prelist 1 (FStar.List.tl lst_previous) level place

private val f2: lst: (non_empty_list nat)  -> counter: nat -> lst_previous : list nat -> ML(non_empty_list nat)
let rec f2 lst counter lst_previous =
        match lst_previous with
            |hd:: tl -> let elem = [hd + 1] 
                    in f2 (List.append lst elem) (counter +1) tl
            |[] -> lst

val tree_treatment_after : lst_previous: (non_empty_list nat) -> ML(non_empty_list nat)
let tree_treatment_after lst_previous =
    let prelist = [] in 
        match lst_previous with |hd::tl ->
            let prelist = 
                List.append prelist [hd+1] in     
    f2 prelist 0 lst_previous

private val sl_search:#a: eqtype -> #f:cmp(a) ->  
            sl: skipList a f -> counter :nat{ SkipList2.Statement.length sl > counter}  -> 
            required_level: nat -> ML(nat)

let rec sl_search #a #f sl counter required_level = 
    let index = getIndex sl counter in 
    let length = List.length index in 
    if length >= required_level  
        then counter 
    else if (counter+1 < SkipList2.Statement.length sl) then sl_search sl (counter +1 ) required_level else (SkipList2.Statement.length sl -1)

(* place will be length -1 element - due to infinity at the end.  *)
private val list_search :#a: eqtype -> #f:cmp(a) ->  sl : skipList a f -> 
level: nat -> lst: (non_empty_list nat) -> counter : nat -> place : nat{(place+1) < SkipList2.Statement.length sl} 
(*there exists AT LEAST ONE MORE ELEMENT*)->  ML(non_empty_list nat)
let rec list_search #a #f sl level lst counter place=
    if counter > level then 
        lst 
    else 
        let lst = List.append lst [(sl_search sl place counter)] in 
            list_search sl level lst (counter+1) place

private val current_place_gen :#a: eqtype -> #f:cmp(a) -> 
sl: skipList a f -> level : nat -> place : nat {(place+1) <SkipList2.Statement.length sl  }
-> ML(non_empty_list nat)
let current_place_gen #a #f sl level place  =
    let next_element = getCurrentValue sl in 
    list_search sl level [place + 1] 0 place



(*NB: this sequnces are not total orders *)
val _update_indexes:#a: eqtype -> #f:cmp(a) ->  
                sl: skipList a f-> place: nat {place+1 < length sl} -> level: nat ->
                counter : nat {counter < length sl} -> 
                sequence_regenerated: seq(non_empty_list nat){Seq.length sequence_regenerated = length sl + 1} -> 
                ML(r: seq(non_empty_list nat){Seq.length r = Seq.length sequence_regenerated })
let rec _update_indexes #a #f sl place level counter sequence_regenerated =
    if counter = length sl then sequence_regenerated else (
        let indexes = getIndexes sl in 
            if counter < place then 
                let treeNew =  tree_treatment_before (getIndex sl counter) level place in 
                    _update_indexes sl place level (counter+1) (sequence_change sequence_regenerated counter treeNew)
            else if counter = place then 
                let sequence_regenerated = sequence_change sequence_regenerated counter (current_place_gen sl level place) in 
                    if (counter + 1  = length sl) then 
                        sequence_regenerated (* completed*) 
                    else
                        _update_indexes sl place level (counter+1) sequence_regenerated 
            else 
                let treeNew = tree_treatment_after (getIndex sl counter) in  (**)
                if (counter + 1 = length sl) then 
                    sequence_regenerated else
                _update_indexes sl place level (counter +1 ) (sequence_change  sequence_regenerated counter treeNew ))



val shiftSequence: sequence_init: seq 'a{Seq.length sequence_init > 0} -> i: nat{Seq.length sequence_init > (i+1) } -> 
                    value : 'a -> Tot(r: seq 'a{Seq.length r = Seq.length sequence_init +1 })
let shiftSequence sequence_init i value= 
    let first_part = Seq.slice sequence_init 0 i in (* length = i - 0*)
    let second_part = Seq.create 1 value in (*length = 1 *)
    let third_part = Seq.slice sequence_init (i) (Seq.length sequence_init) in (*length = length - i*)
    let temp = (Seq.append first_part second_part) in 
    Seq.append temp third_part

val update_indexes: #a: eqtype -> #f: cmp(a) ->sl: skipList a  f -> place:nat {place + 1 < length sl} -> level:nat ->
                        ML(r: seq (non_empty_list nat){Seq.length (getIndexes sl) +1 = Seq.length r  })

let update_indexes #a #f sl place level = 
    let sequence_init = getIndexes sl in 
    let sequence_regenerated = shiftSequence sequence_init place [0] in 
    _update_indexes sl place level 0 sequence_regenerated
                
(*)
assume val searchPlace : #a : eqtype -> #f: cmp(a) ->  comparator: (a-> a -> Tot int) -> el: a -> sl: skipList a f -> 
            Tot(r: nat {(r+1) < SkipList2.Statement.length sl
                 && comparator (Seq.index (getValues sl) (r-1)) el  = 1 && comparator (Seq.index (getValues sl) (r)) el  = -1})
            
                    
assume val inputValue : #a : eqtype -> #f: cmp(a) ->
                    el : a -> sl: skipList a f -> 
                    place : nat{place<SkipList2.Statement.length sl} ->
                    Tot(r:seq a {FStar.Seq.Properties.sorted f r &&
                    Seq.length r = Seq.length(getIndexes sl)+1 })
