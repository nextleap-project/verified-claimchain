module SkipList2.Statement

open FStar.Seq

module Seq = FStar.Seq.Base

type cmp (a:eqtype) = f:(a -> a -> Tot bool)
type cmpL(a:eqtype) = f:(a-> a -> Tot int)

type skipList(a:eqtype) = 
| Mk: values: seq(a) -> indexes : seq(list nat){Seq.length values = Seq.length indexes} -> skipList a

val getValues : #a: eqtype -> sl:skipList a-> Tot(seq a)
let getValues #a sl = 
match sl with 
| Mk v i -> v

val getIndexes: #a : eqtype -> sl:skipList a -> Tot(seq(list nat))
let getIndexes #a sl = 
match sl with 
| Mk v i -> i

val getValue: #a:eqtype -> sl: skipList a ->nth:nat{nth < Seq.length(getValues #a sl)} -> Tot(a)
let getValue #a sl nth = 
let values = getValues #a sl in Seq.index values nth

val getIndex: #a:eqtype -> sl:skipList a -> nth : nat{nth < Seq.length(getIndexes #a sl)} -> Tot(list nat)
let getIndex #a sl nth = 
let indexes = getIndexes #a sl in Seq.index indexes nth

val getTuple: #a:eqtype -> sl: skipList a ->nth:nat{nth < Seq.length(getIndexes #a sl)} -> Tot(a*list nat)
let getTuple #a sl nth = 
let v = getValue #a sl nth in 
let i = getIndex #a sl nth in (v,i)

val insert: #a:eqtype ->sl: skipList a -> Tot(skipList a)
val search: #a:eqtype ->sl: skipList a -> Tot(bool)
val remove: #a:eqtype ->sl: skipList a -> Tot (skipList a)
val isOrdered: #a:eqtype -> sl: skipList a -> Tot(bool)
val length: #a:eqtype -> sl:skipList a -> Tot(nat)
val for_all: #a:eqtype ->f:(a -> Tot bool) -> sl: skipList a -> Tot (bool)

val hd_: #a:eqtype -> sl:skipList a -> option(a)
let hd_ #a sl = 
let values = getValues #a sl in 
if (Seq.length values > 0) 
then Some (getValue #a sl 0)
else 
None

val hd: #a:eqtype -> sl:skipList a{Seq.length (getIndexes #a sl) > 0} -> Tot(a)
let hd #a sl = 
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

val tl : #a:eqtype -> sl: skipList a{Seq.length(getValues sl) >1 } -> Tot(skipList a)
let tl #a sl = 
let values = getValues sl in 
let indexes = getIndexes sl in 
let values = snd (split values 1) in 
let indexes = snd (split indexes 1) in 
Mk values indexes

val tl_ : #a:eqtype -> sl:skipList a -> Tot(option(skipList a))
let tl_ #a sl = 
if Seq.length(getValues sl) >1 then 
Some(tl sl) else None
