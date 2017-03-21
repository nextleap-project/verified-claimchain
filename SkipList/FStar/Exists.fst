type skipList 'a =
|Mk: value : 'a -> levels: int -> a:list(skipList 'a) -> skipList 'a
|MkRoot : skipList 'a

type searchResult = 
| Exists: sl : skipList 'a -> searchResult 
| NextLeaf : sl : skipList 'a -> searchResult
| NotExists : searchResult


let rec f1 lst value = 
match lst with 
|hd::tl -> match hd with 
	| MkRoot -> f1 tl 
	| Mk v l a -> if v > value then f1 tl value
				  else if  v == value then Exists hd
				  else NextLeaf hd
| [] ->  NotExists				  

let rec searchT sl{isMk} value = 
match sl with 
| Mk v l a -> let sr = f1 a value in 
	match sr with
	|Exists sl -> true
	|NotExists -> false
	|NextLeaf leaf -> searchT leaf value

let exists sl value = 
	match sl with 
	| MkRoot -> false
	| Mk v l a -> searchT sl value
