module SkipList2.Statement

open FStar.Seq
open FStar.Option


module Seq = FStar.Seq.Base
module List = FStar.List.Tot


type cmp (a:eqtype) = f:(a -> a -> Tot bool){total_order a f}
type cmpL(a:eqtype) = f:(a-> a -> Tot int)
type non_empty_list 'a = lst: list 'a{Cons? lst}



type skipList(a:eqtype) (f:cmp a) = 
| Mk:  values: seq(a){sorted f values}-> 
indexes : seq(non_empty_list nat)
{Seq.length values = Seq.length indexes} -> skipList a f 



val getValues : #a: eqtype -> #f: cmp(a)-> sl:skipList a f-> Tot(seq a)
let getValues #a #f sl = 
    match sl with 
    | Mk v i -> v

val getIndexes: #a : eqtype-> #f: cmp(a) -> sl:skipList a f -> Tot(seq(non_empty_list nat))
let getIndexes #a #f sl = 
    match sl with 
    | Mk v i -> i

val getValue: #a:eqtype-> #f: cmp(a) -> sl: skipList a f->nth:nat{nth <  Seq.length(getValues #a sl)} -> Tot(a)
let getValue #a #f sl nth = 
    let values = getValues #a sl in Seq.index values nth

val getIndex: #a:eqtype-> #f: cmp(a) -> sl:skipList a f-> nth : nat{nth <  Seq.length(getIndexes #a sl)} -> Tot(list nat)
let getIndex #a #f sl nth = 
    let indexes = getIndexes #a sl in Seq.index indexes nth

val getTuple: #a:eqtype-> #f: cmp(a) -> sl: skipList a f->nth:nat{nth <  Seq.length(getIndexes #a sl)} -> Tot(a*list nat)
let getTuple #a #f sl nth = 
    let v = getValue #a sl nth in 
    let i = getIndex #a sl nth in (v,i)

val insert: #a:eqtype-> #f: cmp(a) ->sl: skipList a f-> Tot(skipList a f)


type searchResult = 
|Found: result: bool -> searchResult
|NotFound: result : nat -> searchResult

private val temp_func: #a:eqtype ->comparator : (a -> a -> Tot int) -> 
                        values: seq(a){Seq.length values > 0} -> 
                        indexes: non_empty_list nat ->
                        value : a -> Tot(searchResult)(decreases (List.length indexes))

let rec temp_func #a comparator values indexes value = 
                let counter = FStar.List.Tot.length indexes in 
                if counter >= Seq.length values then (*!!!!!!!!!!!!!!!*)
                    Found false 
                else
                    if (comparator(Seq.index values counter) value =1) 
                        then (if List.length indexes = 1  then (Found false) 
                                else let lst = List.tl indexes 
                                    in  temp_func comparator values lst value)
                    else if (comparator (Seq.index values counter) value = 0 )
                        then (Found true)
                    else  (NotFound counter)

val length: #a: eqtype -> #f: cmp(a) -> sl: skipList a f -> Tot(nat)
let length #a #f sl =
    let values = getValues sl in 
    Seq.length values

(*)
val search_: #a:eqtype-> #f: cmp(a) ->sl: skipList a f -> 
value : a -> comparator:(a -> a -> Tot int)-> counter:nat{counter < Seq.length(getIndexes sl)} -> ML(bool)

let rec search_ #a #f sl value comparator counter= 
    let values = getValues sl in 
        if Seq.length values <= 0 then false 
        else 
            let indexes = getIndex sl counter in 
            let result = temp_func comparator values indexes value in 
            match result with 
            |Found r -> r 
            |NotFound r -> search_ #a #f sl value comparator r

val search : #a:eqtype ->  #f:cmp(a) -> sl: skipList a f -> value : a -> comparator: cmpL(a) -> ML(bool)
let search #a #f sl value comparator =
    search_ #a #f sl value comparator 0


val remove: #a:eqtype-> #f: cmp(a) ->sl: skipList a f-> Tot (skipList a f )
val isOrdered: #a:eqtype-> #f: cmp(a) -> sl: skipList a f-> Tot(bool)
val length: #a:eqtype-> #f: cmp(a) -> sl:skipList a f-> Tot(nat)
val for_all: #a:eqtype-> #f: cmp(a) ->fnc:(a -> Tot bool) -> sl: skipList a f-> Tot (bool)
*)

val hd_: #a:eqtype-> #f: cmp(a) -> sl:skipList a f-> option(a)
let hd_ #a #f sl = 
    let values = getValues #a sl in 
    if (Seq.length values > 0) 
        then Some (getValue #a sl 0)
    else 
        None

val hd: #a:eqtype-> #f: cmp(a) -> sl:skipList a f{Seq.length (getIndexes #a sl) > 0} -> Tot(a)
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

val tl : #a:eqtype-> #f: cmp(a) -> sl: skipList a f{Seq.length(getValues sl) >1 } -> Tot(skipList a f) 
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
