module Spec.Claim.Map


type kv (a: eqtype) (b:eqtype) = 
  |MkKV : key: a -> value : b -> kv a b      

type map (a: eqtype) (b:eqtype) = 
	|MapCons: list (kv a b) -> map a b
	|MapList: list a -> list b -> map a b 
 
assume val size: #a: eqtype -> #b: eqtype -> map a b -> nat
val isEmpty: #a: eqtype -> #b: eqtype -> map a b -> bool 
val containsKey: #a: eqtype -> #b: eqtype -> map a b -> bool
val containsValue: #a: eqtype -> #b: eqtype -> map a b -> bool
assume val get: #a: eqtype -> #b: eqtype -> map a b -> key: a -> option b
val put: #a: eqtype -> #b: eqtype -> map a b -> a -> b -> map a b 
val remove: #a: eqtype -> #b: eqtype -> map a b -> map a b
val putAll: #a: eqtype -> #b: eqtype -> map a b -> list (kv a b) -> map a b
assume val putAll2: #a: eqtype -> #b: eqtype -> map a b -> list a -> list b -> map a b 
val clear: #a: eqtype -> #b: eqtype -> map a b -> map a b 
assume val keySet: #a: eqtype -> #b: eqtype -> map a b -> list a
assume val values: #a: eqtype -> #b: eqtype -> map a b -> list b
val equals: #a: eqtype -> #b: eqtype -> map a b -> bool
val hashCode: #a: eqtype -> #b: eqtype -> map a b -> int
assume val index: #a: eqtype -> #b: eqtype -> m: map a b ->index : nat {index < size m} ->  kv a b 

