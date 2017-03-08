module SkipListStatement    

open FStar.List.Tot


(*
type skipList 'a = 
    | Empty: skipList 'a
    | Mk: value : 'a -> levels : int{levels > 0}->  a: list(skipList 'a){length a = levels}-> skipList    'a
*)

type skipList 'a =
     | Empty : skipList 'a
     | Mk: value : 'a -> levels : int -> a:list(skipList 'a) -> skipList 'a 

val test: v: 'a  -> levels : int ->  a:list(skipList 'a) -> skipList 'a 
let test v l a = 
    Mk v l a

val test1: v: 'a  -> levels : int ->  a:list(skipList 'a) ->  int
let test1 v l a = 
    let a = Mk v l a in 
    match a with 
    | Empty -> 0
    | Mk v l a -> l

val isEmpty : skipList 'a -> Tot bool

let isEmpty sl = 
    match sl with 
    |Empty -> true
    |_ -> false

val isCons: skipList 'a -> Tot bool
let isCons sl = 
    match sl with 
    |Mk v l a-> true 
    | _ -> false

val isH: skipList 'a -> Tot bool
let isH sl = 
    match sl with 
    | Mk v _ _ -> true
    | _ -> false

val hd: sl:skipList 'a{isH sl} -> Tot 'a
let hd  sl =
    match sl with 
    Mk v l a  -> v

val tl: sl:skipList 'a {isCons sl} -> Tot (skipList 'a)


(*)
val length: skipList 'a -> Tot nat

val nth : skipList 'a  -> 'a

val count: #a:eqtype -> a -> skipList a -> Tot nat

val append: skipList 'a -> skipList 'a -> Tot (skipList 'a)

val appendElem: skipList 'a -> 'a -> Tot(skipList 'a)

(*val exists: skipList 'a -> 'a -> Tot bool*)

*)