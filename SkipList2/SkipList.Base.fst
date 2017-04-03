module SkipList2.Statement

open FStar.Seq

module Seq = FStar.Seq.Base

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
val hd: #a:eqtype -> sl:skipList a -> a
val tl : #a:eqtype -> sl: skipList a -> Tot(skipList a)
