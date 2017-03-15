module SkipListStatement    

open FStar.List.Tot
open FStar.Option
(*
type skipList 'a = 
    | Empty: skipList 'a
    | Mk: value : 'a -> levels : int{levels > 0}->  a: list(skipList 'a){length a = levels}-> skipList    'a
*)

type skipList 'a =
     | Empty : skipList 'a
     | Mk: value : 'a -> levels : int -> a:list(skipList 'a){length a > 0} -> skipList 'a 
     | MkEmpty: value : 'a -> skipList 'a 
(*)
val test: v: 'a  -> levels : int ->  a:list(skipList 'a) -> skipList 'a 
let test v l a = 
    Mk v l a

val test1: v: 'a  -> levels : int ->  a:list(skipList 'a) ->  int
let test1 v l a = 
    let a = Mk v l a in 
    match a with 
    | Empty -> 0
    | Mk v l a -> l
*)
val isEmpty : skipList 'a -> Tot bool
let isEmpty sl = 
    match sl with 
    |Empty -> true
    |_ -> false

val isMk: skipList 'a -> Tot bool
let isMk sl = 
    match sl with 
    |Mk v l a-> true 
    | _ -> false

val isMkEmpty : skipList 'a -> Tot bool
let isMkEmpty sl = 
    match sl with 
    |MkEmpty v -> true
    | _ -> false

val isH: skipList 'a -> Tot bool
let isH sl = 
    match sl with 
    | Mk v _ _ -> true
    | MkEmpty v -> true
    | _ -> false

val hd: sl:skipList 'a{isH sl} -> Tot 'a
let hd  sl =
    match sl with 
    |Mk v l a  -> v
    |MkEmpty v -> v

val tls : sl: skipList 'a {isMk sl } -> Tot (list(skipList 'a))
let tls sl = 
    match sl with
    |Mk v l a -> a

val tails : sl: skipList 'a  -> Tot (option (list (skipList 'a))) 
let tails sl = 
    match sl with
    | Mk v l a -> Some a
    | _ -> None

(*takes skipList and returns nth link to it*)
val tl: sl:skipList 'a {isMk sl} -> level: nat -> Tot (option (skipList 'a))
let tl sl level = 
    let lst = tls sl in FStar.List.Tot.Base.nth lst level

val tail: sl:skipList 'a -> level:nat -> Tot (option (skipList 'a))
let tail sl level = 
    match sl with 
    |Mk v l a -> FStar.List.Tot.Base.nth (tls sl) level
    |_ -> None    

val isConsList: skipList 'a -> Tot bool
let isConsList sl = 
    match sl with 
    | Mk v l a -> true && (FStar.List.Tot.Base.length a > 0)
    | _ -> false

(* we assume that skiplist could be represented as usual list*)
(* tl_last will return the last element in lst*)
val tl_last: sl:list(skipList 'a){length sl > 0} -> Tot (skipList 'a)
let tl_last sl = 
    let l = FStar.List.Tot.Base.length sl in 
    let elemLast = FStar.List.Tot.Base.nth sl l in get elemLast

val lengthLL : sl:skipList 'a -> ML(nat)
let rec lengthLL sl = 
    match sl with 
    | Mk v l a -> 
        let l = FStar.List.Tot.Base.length a in 
        let elemLast = FStar.List.Tot.Base.nth a l in 
        let elemLast = get elemLast in 
        let lenCurrent = lengthLL elemLast in 1 + lenCurrent
    | _ -> 0

val nth: sl: skipList 'a  -> n:nat ->  option('a) 
let rec nth sl n = 
    mathc sl with 
    | Empty -> None
    | MkEmpty v -> if n = 0 then Some v else None
    | Mk v l a -> if n = 0 then Some v else nth (tl_last a) (n-1)

val for_all: sl: skipList 'a ->  f: ('a -> Tot bool) -> Tot(option bool)
let rec for_all sl f = 
    match sl with
        | Empty -> None
        | MkEmpty v -> Some (f v)
        | Mk v l a -> Some ((f v) && (for_all (tl_last a) f))    

val cmp : #a:Type{isComparable a} -> v1 : a -> v2: a -> Tot bool
let cmp v1 v2 = 
    v1 > v2

val isOrdered: sl:skipList    -> Tot bool
let rec isOrdered sl =
    match sl with 
        | Empty -> true
        | MkEmpty _ -> true
        | Mk v l a -> cmp v (hd (tl_last a)) && isOrdered sl
        
type searchResult = 
| Exists: b : bool -> searchResult 
| NextLeaf : sl : skipList 'a -> searchResult
| EndOfSearch : searchResult

val f : sl:list(skipList 'a) -> value: 'a -> Tot searchResult
let rec f sl value = 
	match sl with 
	|hd::tl -> 	if hd == value then Exists 
				else
					(
						match tl with 
						| tl1 :: t2 -> (v h) >  value && (v tl1) < value then NextLeaf hd else f tl value
						| [] -> EndOfSearch
					)
	| [] -> EndOfSearch				

val f2: sl : skipList 'a -> value: 'a -> Tot bool
let rec f2 sl value = 
	match sl with 
	| Empty -> false
	| MkEmpty v -> if v = value then true else false
	| Mk v l a -> if v = value then true else
					let r = f a in 
					match r with 
						| Exists -> true
						| NextLeaf l -> f2 l value
						| EndOfSearch -> false        
        

(*
val append: skipList 'a -> skipList 'a -> Tot (skipList 'a)

val appendElem: skipList 'a -> 'a -> Tot(skipList 'a)

(*val exists: skipList 'a -> 'a -> Tot bool*)

*)
