module SkipList2.Statement

open FStar.Seq

module Seq = FStar.Seq.Base

type cmp (a:eqtype) = f:(a -> a -> Tot bool){total_order a f}
type cmpL(a:eqtype) = f:(a-> a -> Tot int)

type skipList(a:eqtype) (f:cmp a) = 
| Mk:  values: seq(a){sorted f values}-> indexes : seq(list nat){Seq.length values = Seq.length indexes} -> skipList a f

val getValues : #a: eqtype -> #f: cmp(a)-> sl:skipList a f-> Tot(seq a)
let getValues #a #f sl = 
    match sl with 
    | Mk v i -> v

val getIndexes: #a : eqtype-> #f: cmp(a) -> sl:skipList a f -> Tot(seq(list nat))
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
val search: #a:eqtype-> #f: cmp(a) ->sl: skipList a f-> Tot(bool)
val remove: #a:eqtype-> #f: cmp(a) ->sl: skipList a f-> Tot (skipList a f )
val isOrdered: #a:eqtype-> #f: cmp(a) -> sl: skipList a f-> Tot(bool)
val length: #a:eqtype-> #f: cmp(a) -> sl:skipList a f-> Tot(nat)
val for_all: #a:eqtype-> #f: cmp(a) ->fnc:(a -> Tot bool) -> sl: skipList a f-> Tot (bool)

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
