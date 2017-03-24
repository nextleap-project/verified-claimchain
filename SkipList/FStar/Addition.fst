module AdditionSkipList    

open FStar.List.Tot
open FStar.Option


type skipList 'a =
|Mk: value : 'a -> levels: int -> a:list(skipList 'a) -> skipList 'a
|MkRoot : skipList 'a

type sca 'a = 
| Mk : memoryFrom : list (option skipList 'a ) -> memoryTo : list (option skipList 'a )-> sca 'a

type searchResult 'a= 
| Exists: sl : skipList 'a -> searchResult 'a
| NextLeaf : sl : skipList 'a -> searchResult 'a
| NotExists : searchResult 'a


assume val generateLevel: maxLevel : nat -> nat

val generateSCA: #a : eqtype ->  level:nat -> sca a
let generateSCA leve = 
	let rec f c lstFrom lstTo = 
	if c< level then 
		let lstFrom = FStar.List.Tot.append lstFrom [None] in 
		let lstTo = FStar.List.Tot.append lstTo [None] in 
		f (c+1) lstFrom lstTo 
	else
		Mk lstFrom lstTo	

val scaReplace: #a : eqtype ->  f: option (skipList a)  -> t: option (skipList a) ->
	level : nat -> sca: sca a -> sca a
let scaReplace = 
 	match sca with 
 	| Mk memoryFrom memoryTo ->
 	let memoryFrom =  ListExpansion.replace memoryFrom f level in 
 	let memoryTo = ListExpansion.replace memoryTo f level in 
 	Mk memoryFrom memoryTo

val scaReplaceLeveled: #a : eqtype ->  sl: skipList a{isMk} -> sca: sca a -> level: nat -> sca a
let scaReplaceLeveled #a sl sca level = 
 	match sl with 
 	|Mk v l a ->
 		let levelEl =  FStar.List.Tot.nth a level in 
 		scaReplace (Some sl) levelEl level sca

val updateSca : #a : eqtype ->  sl: skipList a{isMk}  ->level: nat -> sca: sca a -> sca a
let updateSca sl level sca= 
	match sl with 
	|MK v l a -> 
		let rec f c = 
		let sca = 
			if (c > level && c < l) then scaReplaceLeveled sl sca level (*  c < l that was after MK!!!!*);f (c+1) 
		in f 0


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
