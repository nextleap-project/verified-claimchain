module Test

open IntegerExpansion


val computeMaxLevel: elements: nat{elements > 1} -> Tot(nat)
let computeMaxLevel elements = 
    IntegerExpansion.log2Tot elements

type skipList 'a =
|Mk: value : 'a -> levels: int -> a:list(skipList 'a) -> skipList 'a
|MkRoot : skipList 'a

type sca 'a = 
| Mk : memoryFrom : list (option skipList 'a ) -> memoryTo : list (option skipList 'a )-> sca 'a

val generateSCA: level:nat -> sca 'a
let generateSCA sca = 
	let rec f c lstFrom lstTo = 
	if c > level then 
		let lstFrom = FStar.List.Tot.append lstFrom [None] in 
		let lstTo = FStar.List.Tot.append lstTo [None] in 
		f (c+1) lstFrom lstTo 
	else
		Mk lstFrom lstTo	

assume val generateLevel: maxLevel : nat -> nat

val scaReplace: f: option (skipList 'a)  -> t: option (skipList 'a) ->
	level : nat -> sca: sca 'a -> sca 'a
let scaReplace = 
 	match sca with 
 	| Mk memoryFrom memoryTo ->
 	let memoryFrom =  ListExpansion.replace memoryFrom f level in 
 	let memoryTo = ListExpansion.replace memoryTo f level in 
 	Mk memoryFrom memoryTo

 val scaReplaceL: sl: skipList 'a{isMk} -> sca: sca 'a -> level: nat -> sca 'a
 let scaReplaceL sl sca level = 
 	match sl with 
 	|Mk v l a ->
 		let level =  FStar.List.Tot.nth a level in 
 		scaReplace (Some sl) level level sca

val scaReplaceSl : sl: skipList 'a{isMk}  ->level: nat -> sca: sca 'a -> sca 'a
let scaReplaceSl sl level sca= 
	match sl with 
	|MK v l a -> 
		let rec f c = 
		let sca = 
			if c > level then scaReplaceL sl sca level 
		in f (c+1) in f 0

val buildLevelTree : sl: skipList 'a -> sca 'a -> value : 'a-> sca 'a
let buildLevelTree sl sca =
	match sl with
	|Mk v l a -> if v < sl then scaReplaceSl else sca
	|MkRoot -> sca

val generateA : memoryTo : list( option skipList 'a )->level:nat ->  sl:skipList{isRoot}-> list skipList 'a
let generateA memoryTo level sl= 
	let rec f c l= 
 	if c > level then l
    else if c > (FStar.List.Tot.length memoryTo) then let l =  FStar.List.Tot.append l (get(FStar.List.Tot.nth)) in f (c+1) l 
	else  let l = FStar.List.Tot.append l [sl]; f (c+1) l


val getFirst: sl:skipList 'a{isMk} -> skipList 'a
let getFirst sl = 
	match  sl with
	| Mk v l a -> FStar.List.nth a 0

val getTail: sl:skipList 'a -> skipList 'a {isRoot}
let getTail sl = 
	let rec f sl= 
	match sl with 
	|Mk v l a -> f (getFirst a) 
	|MkRoot -> sl

val createLeaf : sca : sca 'a -> sl:skipList 'a ->value:'a -> level:nat-> skipList 'a
let createLeaf sca sl value =
	match sca with |Mk memoryFrom memoryTo ->let lstTo = generateA memoryTo level (getTail sl); Mk value (FStar.List.Tot.length lstTo) lstTo


val insert: skipList 'a ->level:nat ->  skipList 'a
let insert sl = 
	let sca = generateSCA in 
	let level = generateLevel level in 
	match sl with 
	| MkRoot -> createLeaf sca sl value level
	| Mk v l a -> let sca = buildLevelTree sl sca in createLeaf sca sl value level
