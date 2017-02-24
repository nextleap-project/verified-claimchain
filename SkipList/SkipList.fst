module SkipListStatement    

open FStar.List.Tot

type skipList 'a = 
    | Empty: skipList 'a
    | Mk: value : 'a -> levels : int{levels > 0}->  a: list(skipList 'a){length a = levels}-> skipList    'a

val isEmpty : skipList 'a -> Tot bool

val hd: l:skipList 'a{Cons? l} -> Tot 'a

val tl: l:skipList 'a {Cons? l} -> Tot (skipList 'a)

val length: skipList 'a -> Tot nat

val nth : skipList 'a  -> 'a

val count: #a:eqtype -> a -> skipList a -> Tot nat

val append: skipList 'a -> skipList 'a -> Tot (skipList 'a)

val appendElem: skipList 'a -> 'a -> Tot(skipList 'a)

val exists: skipList 'a -> 'a -> Tot bool