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
     | Mk: value : 'a -> levels : int -> a:list(skipList 'a) -> skipList 'a 
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
    | MkEmpty v _ _ -> true
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
    |MkEmpty _ _ _ ->  failwith "head of empty list"

(*takes skipList and returns nth link to it*)
val tl: sl:skipList 'a {isMk sl} -> level: nat -> Tot (option (skipList 'a))
let tl sl level = 
    let lst = tls sl in FStar.List.Tot.Base.nth lst level

val isConsList: skipList 'a -> Tot bool
let isConsList sl = 
    match sl with 
    | Mk v l a -> true && (FStar.List.Tot.Base.length a > 0)
    | _ -> false

(* we assume that skiplist could be represented as usual list*)
(* tl_last will return the last element in lst*)
val tl_lastC : sl:skipList 'a  ->Tot(skipList 'a)
let tl_lastC sl = 
    let lst = tls sl in  (* I am list of skipList of 'a *)
    (* we assume that there is at least one element*)
    let len = FStar.List.Tot.Base.length lst in
    let elem = FStar.List.Tot.Base.nth lst len in get elem

let rec lengthLL sl = 
    match sl with 
    | Empty -> 0
    | MkEmpty v l a -> 0
    | Mk v l a -> 1

(*)
(*length LL counts the quantity of elements as Linked List*)
val lengthLL: skipList 'a -> Tot nat
let rec lengthLL sl = 
    match sl with 
    | Empty -> 0
    | Mk v l a -> 1 + lengthLL (tl_last sl)

val lengthTotal: skipList 'a -> Tot nat
(*)
val nth : skipList 'a  -> 'a

val count: #a:eqtype -> a -> skipList a -> Tot nat

val append: skipList 'a -> skipList 'a -> Tot (skipList 'a)

val appendElem: skipList 'a -> 'a -> Tot(skipList 'a)

(*val exists: skipList 'a -> 'a -> Tot bool*)

*)
