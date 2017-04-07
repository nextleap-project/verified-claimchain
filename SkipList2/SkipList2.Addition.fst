module R

open FStar.List
open SkipList2.Statement
open FStar.Seq.Base

type searchResult = 
|Found: result: bool -> searchResult
|NotFound: result : nat -> searchResult


assume val sequence_change: sq: seq 'a ->place: nat {Seq.length sq > place} -> value: 'a -> Tot seq 'a (*same size*)

private val f: lst: list nat -> counter: nat -> lst_previous : list nat -> level:nat -> place : nat -> ML(list nat)
let rec f lst counter lst_previous level place =
        match lst_previous with
            |hd:: tl -> let elem =
                (if hd = place && counter > level then
                    [hd + 1] else [hd])
                    in f (List.append lst elem) (counter +1) tl level place
            |[] -> lst

val tree_treatment_before : lst_previous: list nat -> level:nat-> place : nat-> ML(list nat )
let tree_treatment_before lst_previous level place =
     f [] 0 lst_previous level place



private val f2: lst: list nat -> counter: nat -> lst_previous : list nat -> ML(list nat)
let rec f2 lst counter lst_previous =
        match lst_previous with
            |hd:: tl -> let elem = [hd + 1] 
                    in f2 (List.append lst elem) (counter +1) tl
            |[] -> lst

val tree_treatment_after : lst_previous: list nat -> ML(list nat)
let tree_treatment_after lst_previous =     
    f2 [] 0 lst_previous

private val sl_search:#a: eqtype -> #f:cmp(a) ->  sl: skipList a f -> counter :nat{ length sl > counter}  -> required_level: nat -> ML(nat)
let rec sl_search #a #f sl counter  required_level = 
    let index = getIndex sl counter in 
    let length = List.length index in 
    if length >= required_level 
        then counter 
    else sl_search (counter + 1) sl required_level

private val list_search :#a: eqtype -> #f:cmp(a) ->  level: nat -> lst: list(nat) -> counter : nat ->sl:skipList a f ->  ML list(nat)

let rec list_search #a #f level lst counter place sl=
    if counter > level then lst 
    else let lst = List.append lst [(sl_search sl place counter)] in 
        list_search level lst (counter+1) 

let current_place_gen level sl place =
    list_search level [] 0

val update_indexes:#a: eqtype -> #f:cmp(a) ->  
                sl: skipList a -> place: nat {place < length sl} -> 
                counter : nat {counter <= length sl} -> sequence_regenerated: seq a -> ML(seq a)
let rec update_indexes sl place level counter sequence_regenerated =
    if counter = length sl then sequence_regenerated else (
        let indexes = getIndexes sl in 
            if counter < place then 
                let treeNew =  tree_treatment_before (getIndex sl counter) level place in 
                    update_indexes  place level (counter+1) (sequence_change sequence_regenerated)
            else if counter = place then 
                    update_indexes  place level (counter+1) (sequence_change (current_place_gen indexes place)) 
            else 
                let treeNew = tree_treatment_after (getIndex sl counter) in 
update_indexes place level (counter +1 ) (sequence_change sequence_regenerated))
