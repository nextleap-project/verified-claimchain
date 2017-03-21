module ExistsSkipList    

open FStar.List.Tot
open FStar.Option


type skipList 'a =
|Mk: value : 'a -> levels: int -> a:list(skipList 'a) -> skipList 'a
|MkRoot : skipList 'a

type searchResult 'a= 
| Exists: sl : skipList 'a -> searchResult 'a
| NextLeaf : sl : skipList 'a -> searchResult 'a
| NotExists : searchResult 'a


type total_order (a:eqtype) (f: (a -> a -> Tot bool)) =
(forall a1 a2. (f a1 a2 /\ f a2 a1) ==> a1 = a2) (* anti-symmetry *)
/\ (forall a1 a2 a3. f a1 a2 /\ f a2 a3 ==> f a1 a3) (* transitivity *)
/\ (forall a1 a2. f a1 a2 \/ f a2 a1) (* totality *)

type cmp (a:eqtype) = f:(a -> a -> Tot bool) (* Sorry Jonathan, I am not gonna prove this{total_order a f}*)
type cmpL(a:eqtype) = f:(a -> a -> Tot int)

val f1 : #a : eqtype ->  f:cmpL(a) -> lst: list(skipList a) -> value : a -> ML(searchResult a)
let rec f1 #a f lst value = 
match lst with 
|hd::tl -> (match hd with 
    | MkRoot -> f1 #a f tl value
    | Mk v l a -> if ((f v value) = 1) then f1 f tl value (*MORE*)
                  else if  ((f v value) = 0) then Exists hd (*EQUAL*)
                  else NextLeaf hd) 
| [] ->  NotExists                  
(*)
val searchT: sl: skipList 'a -> value : 'a -> ML bool
let rec searchT sl value = 
    match sl with 
    | Mk v l a -> 
        let sr = f1 a value in
        match sr with
        |Exists sl -> true
        |NotExists -> false
        |NextLeaf leaf -> searchT leaf value 


val find: sl: skipList 'a -> value : 'a -> ML bool
let find sl value = 
    match sl with 
    | MkRoot -> false
    | Mk v l a -> searchT sl value
