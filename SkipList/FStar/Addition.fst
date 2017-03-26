module AdditionSkipList    

open FStar.List.Tot
open FStar.Option
open SkipListStatement
open ListExpansion


type sca (a:eqtype) = 
| Mk : memoryFrom : list (option (skipList a)) -> memoryTo : list (option (skipList a))-> sca a

type searchResult (a:eqtype)= 
| Exists: sl : skipList a -> searchResult a
| NextLeaf : sl : skipList a -> searchResult a
| NotExists : searchResult a



val generateSCA_ : #a : eqtype -> c: nat ->level:nat -> lstFrom : list (option (skipList a)) -> lstTo:list (option (skipList a)) -> ML(sca a)
let rec generateSCA_ #a c  level lstFrom lstTo = 
        if c< level then 
            let lstFrom = FStar.List.Tot.append lstFrom [None] in 
            let lstTo = FStar.List.Tot.append lstTo [None] in 
            generateSCA_ (c+1) level lstFrom lstTo 
        else
            Mk lstFrom lstTo

val generateSCA:#a : eqtype ->  level:nat  -> ML(sca a)
let generateSCA #a level = 
    let el : (list (option (skipList a))) = [] in 
    generateSCA_ #a 0 level el el 

(*val replace: lst: list 'a -> counter : nat -> value : 'a -> Tot(list 'a) *)

val scaReplace: #a : eqtype ->  f: option (skipList a)  -> t: option (skipList a) -> level : nat -> sca_ent: sca a -> sca a
let scaReplace #a f t level sca_ent = 
     match sca_ent with 
     | Mk memoryFrom memoryTo ->
     let memoryFrom =  ListExpansion.replace memoryFrom level f in 
     let memoryTo = ListExpansion.replace memoryTo level t in 
     Mk memoryFrom memoryTo

val scaReplaceLeveled: #a : eqtype ->  sl: skipList a{isMk sl} -> sca_ent: sca a -> level: nat -> sca a
let scaReplaceLeveled #a sl sca_ent level = 
     match sl with 
     |SkipListStatement.Mk v l a ->
         let levelEl =  FStar.List.Tot.nth a level in 
         scaReplace (Some sl) levelEl level sca_ent

val updateSca_:#a: eqtype -> sl:skipList a{isMk sl} -> level : nat -> sca_ent : sca a-> c: nat->  ML(sca a)
let rec updateSca_ #a sl level sca_ent c =  
    match sl with 
    | SkipListStatement.Mk v l a ->
            if (c > level && c < l) 
                then 
                let sca_ent = scaReplaceLeveled sl sca_ent level (*  c < l that was after MK!!!!*)
                 in updateSca_  sl level sca_ent (c+1)
            else sca_ent    


val updateSca : #a : eqtype ->  sl: skipList a{isMk sl}  ->level: nat -> sca_ent: sca a -> ML(sca a)
let updateSca #a sl level sca_ent =  
    updateSca_ #a sl level sca_ent 0

(*)

val func_temp : #a: eqtype -> comparatorInt: cmpL(a) ->  lst:list (skipList a) -> value : a ->level: nat->sca: sca a  ->  ML (tuple:(searchResult a * sca a))
let rec func_temp #a comparatorInt lst value level sca=
match lst with
    |hd::tl -> (match hd with
            | MkRoot -> func_temp comparatorInt tl value level sca
            | Mk v l a -> let sca = updateSca hd level sca in if ((comparatorInt v value) = 1) then func_temp
        comparatorInt tl value level sca (*MORE*)
                          else if  ((comparatorInt v value) = 0) then ((Exists hd), sca) (*EQUAL*)
                          else ((NextLeaf hd, sca))
    | [] ->  (NotExists, sca)
    
val searchT: #a: eqtype -> comparatorInt:cmpL(a) -> sl: skipList a{isMk sl} -> value : a ->level: nat->sca: sca a  -> ML sca a
let rec searchT #a comparatorInt sl value level sca=
    match sl with
    | Mk v l a -> let sr = func_temp comparatorInt a value level sca in (* only
this -> clause*)
    match (snd sr) with
    | Exists sl -> (*idk *) sca 
    | NotExists -> sca
    | NextLeaf leaf -> searchT comparatorInt leaf value level sca (*NB : it
returns NL iff in func_temp it is in Mk   *)

val buildLevelTree: #a : eqtype -> comparatorInt: cmpL(a) -> sl: skipList a-> value : a  -> level: nat -> sca: sca a -> sca a
let buildLevelTree #a comparatorInt sl value  level sca= 
    match sl with 
    | MkRoot -> sca
    | Mk v l a -> searchT comparatorInt sl value level sca

val insert: #a : eqtype -> comparatorInt: cmpL(a) -> sl: skipList 'a ->  skipList 'a
let insert sl = 
    let sca = generateSCA in 
    let level = generateLevel level in 
    match sl with 
    | MkRoot -> createLeaf sca sl value level
    | Mk v l a -> let sca = buildLevelTree sl sca in createLeaf sca sl value level
*)
