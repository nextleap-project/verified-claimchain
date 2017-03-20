module Test

open IntegerExpansion


val computeMaxLevel: elements: nat{elements > 1} -> Tot(nat)
let computeMaxLevel elements = 
    IntegerExpansion.log2Tot elements

type skipList 'a =
|Mk: value : 'a -> levels: int -> a:list(skipList 'a) -> skipList 'a
|MkRoot : skipList 'a

type sca 'a =
| Mk: memory : list ((option skipList 'a)* (option skipList 'a))

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
assume val buildLevelTree : sl: skipList 'a -> sca 'a -> sca 'a

val scaReplace: f: option(skipList 'a) -> t: option (skipList 'a )->
	level : nat -> sca: sca 'a -> sca 'a
let scaReplace = 
 	match sca with 
 	| Mk memoryFrom memoryTo ->
 	let memoryFrom =  ListExpansion.replace memoryFrom f level in 
 	let memoryTo = ListExpansion.replace memoryTo f level in 
 	Mk memoryFrom memoryTo

val createLeaf : sca : sca 'a -> sl:skipList 'a ->value:'a ->  skipList 'a
let createLeaf sca sl value =


val insert: skipList 'a ->level:nat ->  skipList 'a
let insert sl = 
	let sca = generateSCA in 
	let level = generateLevel level in 
	match sl with 
	| MkRoot -> createLeaf sca sl level
	| Mk v l a -> let sca = buildLevelTree sl sca in createLeaf sca sl level
