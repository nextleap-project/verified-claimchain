module SkipList.Exists

open FStar.List.Tot
open FStar.Option
open SkipList.Statement 

type searchResult 'a=
| Exists: sl : skipList 'a{isMk sl} -> searchResult 'a
| NextLeaf : sl : skipList 'a{isMk sl} -> searchResult 'a
| NotExists : searchResult 'a

(*type total_order (a:eqtype) (f: (a -> a -> Tot bool)) =
(forall a1 a2. (f a1 a2 /\ f a2 a1) ==> a1 = a2) (* anti-symmetry *)
/\ (forall a1 a2 a3. f a1 a2 /\ f a2 a3 ==> f a1 a3) (* transitivity *)
/\ (forall a1 a2. f a1 a2 \/ f a2 a1) (* totality *)*)

val func_temp : #a : eqtype ->  comparatorInt:cmpL(a) -> lst:list(skipList a) -> value : a -> ML(searchResult a)
let rec func_temp #a comparatorInt lst value =
match lst with
    |hd::tl -> (match hd with
            | MkRoot -> func_temp #a comparatorInt tl value
            | Mk v l a -> if ((comparatorInt v value) = 1) then func_temp
        comparatorInt tl value (*MORE*)
                          else if  ((comparatorInt v value) = 0) then Exists hd (*EQUAL*)
                          else NextLeaf hd)
    | [] ->  NotExists
    
val searchT: #a: eqtype -> comparatorInt:cmpL(a) -> sl: skipList a{isMk sl} -> value : a -> ML bool
let rec searchT #a comparatorInt sl value =
    match sl with
    | Mk v l a -> let sr = func_temp comparatorInt a value in (* only
this -> clause*)
    match sr with
    | Exists sl -> true
    | NotExists -> false
    | NextLeaf leaf -> searchT comparatorInt leaf value (*NB : it
returns NL iff in func_temp it is in Mk   *)

val find: #a: eqtype -> comparatorInt:cmpL(a) -> sl: skipList a -> value : a -> ML bool
let find  #a comparatorInt sl value =
    match sl with
    | MkRoot -> false
    | Mk v l a -> searchT comparatorInt sl value
