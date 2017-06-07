module MerkleTree

open HashFunction
open FStar.Seq
open FStar.Option

type hash = seq nat
type data = seq nat

type merkleTree: level:nat -> h: hash -> Type  = 
| MLeaf: element : data -> merkleTree 0 (hashFunc element)
| MNode: #level: nat -> #h1: hash -> #h2 : hash -> 
        lnode: merkleTree level h1 ->
        rnode: option(merkleTree level h2) -> 
        merkleTree (level+1) (hashConcat h1 h2)

type stack  = 
| Mk : element : seq nat -> len: nat {len = Seq.length element} -> stack 


val get_elem: st: stack -> seq nat
let get_elem st = 
    match st with 
    | Mk a _ -> a

val get_len_stack : st: stack -> nat
let get_len st = 
    match st with 
    | Mk _ l -> l

val push: st: stack -> el: nat-> Tot stack
let push st el = 
    match st with 
    |Mk s l -> Mk (Seq.snoc s el) (l +1)

val pop : st: stack  -> Tot stack
let pop st = st
    (*match st with 
    | Mk s l -> Mk (Seq.tail s) (l - 1) *)


val path_gen :treeLength: nat ->  #l1 : nat -> 
    #h1: hash -> m: merkleTree l1 h1{l1 <= treeLength}  -> #h2: hash -> m2 : option(merkleTree l1 h2) ->
    st: stack{get_len st = treeLength - l1} -> element : data -> ML((r:bool) * (st:stack))(decreases (l1))

let rec path_gen treeLength #l1 #h1 m #h2 m2 st element = 
    match m with 
    |MLeaf a -> if a = element then (true, st) else let st = pop st in  (false, st)
    |MNode lnode rnode -> 
        let st = push st 0 in 
        let r = path_gen treeLength lnode rnode st element in 
        match r with 
        |(true, st) -> (true, st)
        |(false, st) -> 
            match m2 with 
                |None ->let st = pop st in  (false, st)                           
                |Some el -> let st = push st 1 in
                path_gen treeLength el None st element

