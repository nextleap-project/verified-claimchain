val test:  #a: eqtype -> #f: cmp a -> s: seq a {Seq.sorted f s /\ Seq.length s = 10 } -> 
			place: nat {place > 0 /\ place < Seq.length s} -> 
			Tot(unit)

let test #a #f s place = 
	assert(f (Seq.index s 0) (Seq.index s 1));
	assert(f (Seq.index s 1) (Seq.index s 2));
	assert(f (Seq.index s 2) (Seq.index s 3));
	assert(f (Seq.index s 3) (Seq.index s 4));
	assert(f (Seq.index s 4) (Seq.index s 5));	
	assert(f (Seq.index s 5) (Seq.index s 6));
	assert(f (Seq.index s 6) (Seq.index s 7));
	assert(f (Seq.index s 7) (Seq.index s 8)); ()


val test : #a: eqtype -> #f: cmp a -> s: seq a {Seq.sorted f s /\ Seq.length s = 10 } -> 
			place: nat {place > 0 /\ place < Seq.length s} -> 
			Tot(unit)
let rec test #a #f s place	= 
	if (place = 1) then (
		assert(f (Seq.index s (place -1)) (Seq.index s place))
	) 
	else (
		test #a #f s (place -1); 
		assert(f (Seq.index  s (place-1)) (Seq.index s place))
		); ()

val test2: #a: eqtype -> #f: cmp a -> 
			s: seq a {Seq.sorted f s /\ Seq.length s > 1} -> 
			place : nat {place > 1 /\ place < Seq.length s -1 /\ f (Seq.index s (place -1 )) (Seq.index s place)} -> Tot(unit) (*)
			Lemma(
				ensures (f (Seq.index s place) (Seq.index s (place +1)))
			)*)

let test2 #a #f s place = 
	assert(f (Seq.index s (place -1)) (Seq.index s place));
	assert(f (Seq.index s place) (Seq.index s (place+1))); ()
		

