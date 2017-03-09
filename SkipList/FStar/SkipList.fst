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

val tls : sl: skipList 'a {isCons sl } -> Tot (list(skipList 'a))
let tls sl = 
    match sl with
    Mk v l a -> a

(*takes skipList and returns nth link to it*)
val tl: sl:skipList 'a {isCons sl} -> level: nat -> Tot (option (skipList 'a))
let tl sl level = 
    let lst = tls sl in FStar.List.Tot.Base.nth lst level

val isConsList: skipList 'a -> Tot bool
let isConsList sl = 
    match sl with 
    | Mk v l a -> true && (FStar.List.Tot.Base.length a > 0)
    | _ -> false

(*)
val tl_last : sl:skipList 'a {isCons sl} -> Tot (option (skipList 'a))
let tl_last sl = 
    let lst = tls sl in 
    let len = FStar.List.Tot.Base.length lst in tl lst len
(*
)val length: skipList 'a -> Tot nat
let rec length sl = 
    match sl with
    | None -> 0
    | a -> match a with
        Mk v l a -> 1 + length (tl_last sl) 
(*)
val nth : skipList 'a  -> 'a

val count: #a:eqtype -> a -> skipList a -> Tot nat

val append: skipList 'a -> skipList 'a -> Tot (skipList 'a)

val appendElem: skipList 'a -> 'a -> Tot(skipList 'a)

(*val exists: skipList 'a -> 'a -> Tot bool*)

*)