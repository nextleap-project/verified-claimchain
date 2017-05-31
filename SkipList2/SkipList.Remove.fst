module SkipList.Remove


(* last element is less than the next one*)
val _change_values: #a: eqtype -> #f: cmp a -> s1: seq a {Seq.sorted f s /\ element = Seq.index_last} ->  s: seq a {Seq.sorted f s }-> index: nat {index > place /\ index < Seq.length s} -> 
Tot (r: seq a {Seq.sorted f s }) 
let _change_values #a #f s index = 
	assert (f (Seq.index last ) (Seq.index s index)  );
	let s1 = append_right s1 (Seq.index s index);
	assert (Seq.sorted f s1)

val change_values: #a: eqtype -> #f: cmp a -> s: seq a {Seq.sorted  f s } -> Tot(r: seq a {Seq.sorted f r})
let change_values #a #f s = 
	_change_values #a #f s place
	
	

val _change_indexes_seq: #a: eqtype -> #f : cmp a -> s: seq a -> counter_global : nat {counter_global < Seq.length s} -> 
	Tot(r: seq a {Seq.length s = Seq.length r + 1})

let _change_indexes_seq : #a: eqtype -> #f: cmp a -> s: seq a -> counter_local : nat {counter_local < List.length (getIndex s counter_global)} -> 
	let 

val change_indexes: #a: eqtype -> #f : cmp a -> s: seq a -> Tot(r: seq a {Seq.length s = Seq.length r + 1})
let change_indexes #a #f s = 
		

val change: #a: eqtype -> #f: cmp a -> sl: skipList a f {Sl.length sl > 1} -> Tot(r: skipList a f {Sl.length sl= Sl.length r + 1 })
let change 