module SkipList.Statement 

open FStar.List.Tot
open FStar.Option
(*open HashFunction*)
(*
type skipList 'a = 
| Empty: skipList 'a
| Mk: value : 'a -> levels : int{levels > 0}-> a: list(skipList 'a){length a = levels}-> skipList 'a
*)

type cmp (a:eqtype) = f:(a -> a -> Tot bool)
type cmpL(a:eqtype) = f:(a-> a -> Tot int)

type skipList (a:eqtype) =
|Mk: value : a -> levels: FStar.UInt32.t -> lst:list(skipList a)  -> skipList a
|MkRoot : skipList a

(*<Discriminators>*)
val isMk: #a: eqtype ->  skipList a -> Tot bool
let isMk #a sl = 
	match sl with 
	|Mk v l a-> true 
	| _ -> false

val isRoot: #a: eqtype ->  skipList a -> Tot bool
let isRoot #a sl = 
	match sl with 
	|Mk v l a-> false 
	| _ -> true
(* </Discriminators>*)

(* <SkipListLeaf>*)
type skipListLeaf (a:eqtype) = |Sls : el: skipList a {isMk el} -> skipListLeaf a

val getSkipListFromSLL: #a : eqtype ->  leaf: skipListLeaf a -> sl: skipList a{isMk sl}
let getSkipListFromSLL #a leaf = 
	match leaf with Sls a -> a
(* </SkipListLeaf>*)

val getValue: #a:eqtype -> sl: skipList a {isMk sl} -> a 
let getValue #a sl = 
	match sl with |Mk v l a -> v

val getList: #a:eqtype -> sl:skipList a{isMk sl} -> list(skipList a)
let getList #a sl = 
	match sl with |Mk v l a -> a

val getLevel: #a:eqtype -> sl:skipList a{isMk sl} -> FStar.UInt32.t
let getLevel #a sl =
match sl with |Mk v l a -> l


val hd: #a:eqtype -> sl: skipList a {isMk sl} -> Tot (a)
let hd #a sl = 
	getValue sl

val tls : #a:eqtype ->  sl: skipList a {isMk sl} -> Tot (list(skipList a))
let tls #a sl = 
	match sl with
	|Mk v l a -> a

(*takes skipList and returns nth link to it*)
val tl: #a: eqtype-> sl:skipList a {isMk sl} -> level: nat -> Tot (option (skipList a))
let tl #a sl level = 
let lst = tls sl in FStar.List.Tot.Base.nth lst level


(* we assume that skiplist could be represented as usual list*)
(* tl_last will return the last element in lst*)
val tl_last:#a : eqtype -> sl:list(skipList a) -> Tot (skipList a)
let tl_last #a sl = 
let l = FStar.List.Tot.Base.length sl in 
let elemLast = FStar.List.Tot.Base.nth sl l in get elemLast

val tl_last_elem: #a : eqtype -> sl:skipList a {isMk sl}-> Tot (skipList a)
let tl_last_elem #a sl = 
	let lst = getList sl in tl_last lst

val length : #a :eqtype ->  sl: skipList a-> ML(nat)
let rec length #a sl = 
	match sl with 
	| Mk v l a -> let elem = tl_last_elem sl in 1 + length elem
	| _-> 0

val nth: #a:eqtype ->  sl : skipList a -> n: nat -> ML(option(a))
let rec nth #a sl n = 
	match sl with 
	| Mk v l a -> if n = 0 then Some v else nth (tl_last_elem sl) (n-1)
	| _-> None

val nth_sl : #a:eqtype -> sl:skipList a -> n:nat -> ML(option(skipList a))
let rec nth_sl #a sl n = 
	match  sl with
	| Mk v l a  -> if n = 0 then Some sl else nth_sl (tl_last_elem sl) (n-1)
	| _ -> None

val for_all: #a:eqtype -> sl: skipList a -> f: (a -> Tot bool) -> Tot(bool)
let rec for_all #a sl f = 
match sl with
| _ -> true 
| Mk v l a -> (f v) &&  (for_all (tl_last_elem sl) f)


val isOrdered:#a: eqtype -> comparator:cmp(a) ->  sl:skipList a -> Tot bool
let rec isOrdered #a comparator sl=
	match sl with 
	| _ -> true
	| Mk v l a -> comparator v (hd (tl_last_elem sl)) && isOrdered comparator (tl_last_elem sl)

val isOrdered2 : #a:eqtype ->comparator:cmpL(a)->  sl :skipList a -> Tot bool 
let rec isOrdered2 #a comparator sl= 
	match sl with
	| _ -> true
	| Mk v l a -> (comparator v (hd (tl_last_elem sl)) = 0) && isOrdered2 comparator (tl_last_elem sl)
