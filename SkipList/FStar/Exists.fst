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

(*type total_order (a:eqtype) (f: (a -> a -> Tot bool)) =
(forall a1 a2. (f a1 a2 /\ f a2 a1) ==> a1 = a2) (* anti-symmetry *)
/\ (forall a1 a2 a3. f a1 a2 /\ f a2 a3 ==> f a1 a3) (* transitivity *)
/\ (forall a1 a2. f a1 a2 \/ f a2 a1) (* totality *)*)

type cmp (a:eqtype) = f:(a -> a -> Tot bool) (* Sorry Jonathan, I am not gonna prove this{total_order a f}*)
type cmpL(a:eqtype) = f:(a -> a -> Tot int)

val func_temp : #a : eqtype ->  comparatorInt:cmpL(a) -> lst: list(skipList a) -> value : a -> ML(searchResult a)
let rec func_temp #a f lst value = 
match lst with 
|hd::tl -> (match hd with 
    | MkRoot -> func_temp #a comparatorInt tl value
    | Mk v l a -> if ((comparatorInt v value) = 1) then func_temp comparatorInt tl value (*MORE*)
                  else if  ((comparatorInt v value) = 0) then Exists hd (*EQUAL*)
                  else NextLeaf hd) 
| [] ->  NotExists  


val searchT: #a: eqtype -> comparatorInt:cmpL(a) -> sl: skipList a(*isMk*) -> value : a -> ML bool
let rec searchT #a comparatorInt sl value = 
    match sl with 
    | Mk v l a -> let sr = func_temp comparatorInt a value in (* only this -> clause*)
    match sr with 
    | Exists sl -> true
    | NotExists -> false
    | NextLeaf leaf -> searchT comparatorInt leaf value (*NB : it returns NL iff in func_temp it is in Mk   *)

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
