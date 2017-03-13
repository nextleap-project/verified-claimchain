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

val lengthTotal: skipList 'a -> Tot nat
(*)
val nth : skipList 'a  -> 'a

val count: #a:eqtype -> a -> skipList a -> Tot nat

val append: skipList 'a -> skipList 'a -> Tot (skipList 'a)

val appendElem: skipList 'a -> 'a -> Tot(skipList 'a)

(*val exists: skipList 'a -> 'a -> Tot bool*)

*)
