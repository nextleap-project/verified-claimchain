module Spec.Claim.Map

open FStar.List.Tot
open FStar.Seq.Properties

module List = FStar.List.Tot

type kv (a: eqtype) (b:eqtype) = 
  |MkKV : key: a -> value : b -> kv a b  

val equalKV: #a: eqtype -> #b: eqtype -> kv1: kv a b -> kv2:  kv a b -> Tot bool
let equalKV #a #b kv1 kv2 = 
    (kv1.key = kv2.key) && (kv1.value = kv2.value)
    


type map (a: eqtype) (b:eqtype) = 
    |MapCons: list (kv a b) -> map a b
    |MapList: l1: list a -> l2: list b{length l1 = length l2} -> map a b 

val isMapCons: #a: eqtype -> #b: eqtype -> map a b -> bool
let isMapCons #a #b m = 
    match m with 
    | MapCons _ -> true    
    | MapList _ _ -> false    

val isMapList: #a: eqtype -> #b: eqtype -> map a b -> bool
let isMapList #a #b m = 
    match m with 
    | MapCons _ -> false    
    | MapList _ _ -> true            
 
val size: #a: eqtype -> #b: eqtype -> map a b -> nat
let size #a #b map = 
    match  map with
    | MapCons lst -> length lst
    | MapList l1 _-> length l1 

val isEmpty: #a: eqtype -> #b: eqtype -> map a b -> bool 
let isEmpty #a #b map = size #a #b map = 0

private val _containsKeyKV:#a: eqtype -> #b : eqtype ->  l: list (kv a b) -> element: a -> counter : int -> Tot int
let rec _containsKeyKV #a #b l element counter = 
    match l with 
    | hd:: tl -> if hd.key = element then counter else _containsKeyKV tl element (counter+1)
    | [] -> -1

private val _containsKey:#a: eqtype -> list a -> element : a -> counter: int-> Tot int
let rec _containsKey #a l element counter = 
    match l with 
    |hd:: tl -> if hd = element then counter else _containsKey #a tl element (counter +1)
    | [] -> -1

val containsKey: #a: eqtype -> #b: eqtype -> map a b -> a -> bool
let containsKey #a #b map key = 
    match map with 
    | MapCons lst -> let r =  _containsKeyKV lst key 0 in r > -1
    | MapList l1 l2 -> let r = _containsKey l1 key 0 in r > -1

private val _containsValueKV: #a: eqtype -> #b: eqtype -> l: list (kv a b) -> element : b -> counter : int -> Tot int
let rec _containsValueKV #a #b l element counter = 
    match l with 
    | hd::tl -> if hd.value = element then counter else _containsValueKV tl element (counter+1)
    | [] -> -1

private val _containsValue:  #b: eqtype -> list b -> element : b -> counter: int-> Tot int
let rec _containsValue #b l element counter = 
    match l with 
    |hd::tl -> if hd = element then counter else _containsValue #b tl element (counter+1)
    |[] -> -1

val containsValue: #a: eqtype -> #b: eqtype -> map a b -> b -> bool
let containsValue #a #b map value = 
    match  map with
    | MapCons lst  -> let r = _containsValueKV lst value 0 in r > -1
    | MapList l1 l2     -> let r = _containsValue  #b l2 value 0 in r > -1

val get: #a: eqtype -> #b: eqtype -> map a b -> key: a -> option b
let get #a #b map key = 
    match map with 
    | MapCons lst -> let i = _containsKeyKV #a #b lst key 0 in 
                        if (i > -1 && i < length lst) 
                            then Some (FStar.List.Tot.index lst i).value
                        else None
    | MapList l1 l2 -> let i = _containsKey #a l1 key 0 in 
                            if (i > -1 && i < length l2)
                                then Some (FStar.List.Tot.index l2 i)
                            else None                    

val append_len: l1: list 'a -> l2: list 'a -> 
            Lemma (ensures (length (append l1 l2) = length l1 + length l2))

let rec append_len l1 l2 = 
    match l1 with 
    | [] -> ()
    | hd::tl -> append_len tl l2            

val put: #a: eqtype -> #b: eqtype -> m: map a b -> e1: a -> e2: b -> 
        Tot (r: map a b {isMapList m = isMapList r /\ isMapCons m = isMapCons r /\ size r = size m +1})
let put #a #b m e1 e2 = 
    match m with 
    |MapCons list -> let temp = MkKV e1 e2 in 
                        append_len list [temp];
                        MapCons (List.append list [temp])
    |MapList l1 l2 -> assert (length l1 = length l2); 
                      let l1_2 = append l1 [e1] in 
                      append_len l1 [e1];
                      assert(length l1_2 = (length l1 + 1));
                      let l2_2 = append l2 [e2] in 
                      append_len l2 [e2];
                      assert(length l1_2  = length l2_2);
                      MapList l1_2 l2_2

val put2: #a: eqtype -> #b:eqtype -> m: map a b -> e: kv a b -> 
    Tot(r: map a b {isMapList m = isMapList r /\ isMapCons m = isMapCons r /\ size r = size m + 1})
let put2 #a #b m e = 
    match m with 
    |MapCons list -> append_len list [e];
                        MapCons (List.append list [e])
    |MapList l1 l2 -> let key = e.key in 
                        let value = e.value in 
                        let keys = append l1 [key] in 
                        let values = append l2 [value] in 
                        append_len l1 [key];
                        append_len l2 [value];
                        assert(length keys = length values);
                        MapList keys values

(*)
val _split_list: l: list 'a -> 
        counter: nat -> 
        index_finish: nat{index_finish < length l /\ counter < index_finish} -> l_temp: list 'a -> 
        Tot (list 'a)(decreases (index_finish - counter))
let rec _split_list l counter index_finish l_temp = 
    let element = index l counter in 
    let l_temp = append l_temp [element] in 
    if (counter +1 < index_finish)
        then _split_list l (counter+1) index_finish l_temp
    else l_temp
*)

assume val split_list: l: list 'a ->index_start: nat ->
     index_finish : nat -> 
     Tot (r:list 'a{length r = index_finish - index_start})
(*let split_list l index_start index_finish = 
    let counter = index_start in 
    _split_list l counter index_finish []
*)

val remove: #a: eqtype -> #b: eqtype -> m: map a b -> a -> map a b
let remove #a #b m key  = 
    match m with 
    | MapCons lst -> let i = _containsKeyKV #a #b lst key 0 in 
                        if (i > -1 && i < length lst) 
                            then 
                                (
                                    let lst_fst = split_list lst 0 i in 
                                    let lst_snd = split_list lst i (length lst)  
                                    in MapCons (append lst_fst lst_snd)
                                )    
                        else
                            m        
    | MapList l1 l2 -> m                        

val putAll: #a: eqtype -> #b: eqtype -> m: map a b -> 
            l: list (kv a b) -> Tot(r: map a b{size r = size m + length l /\
                                        isMapList m = isMapList r /\ isMapCons m = isMapCons r})
                                (decreases (length l))
let rec putAll #a #b m lst = 
    match lst with 
    | hd::tl -> let m = put2 #a #b m hd in putAll #a #b m tl
    | [] -> m

val putAll2: #a: eqtype -> #b: eqtype -> m: map a b -> 
            lstA: list a -> lstB: list b{length lstA = length lstB} -> 
            Tot (r: map a b{size r = size m + length lstA /\ isMapList m = isMapList r /\ isMapCons m = isMapCons r})
            (decreases (length lstA))

let rec putAll2 #a #b m lstA lstB = 
    match lstA with 
    |hdA::tlA ->let m1 = put2 #a #b m (MkKV (hdA) (hd lstB)) in 
                assert(length (tlA) =  length (tl lstB));
                putAll2 #a #b m1 (tlA) (tl lstB)
    |[] -> m            

val clear: #a: eqtype -> #b: eqtype -> map a b -> map a b (*very important method, but for the commmon java sense *)
let clear #a #b m = 
    match m with 
    | MapCons _ -> MapCons [] 
    | MapList _ _ -> MapList [] []

val createEmptyC: #a: eqtype -> #b: eqtype ->Tot(m : map a b {isMapCons m= true/\ size m = 0})
let createEmptyC #a #b = 
    MapCons [] 

val createEmptyL: #a: eqtype -> #b: eqtype -> Tot (m: map a b {isMapList m = true /\ size m = 0})
let createEmptyL #a #b = 
    MapList [] [] 

val keySet: #a: eqtype -> #b: eqtype -> m: map a b -> Tot(l: list a{length l = size m})
let keySet #a #b m = 
    match m with 
    | MapCons lst -> FStar.List.Tot.map (fun (x: kv a b) -> x.key) lst
    | MapList l1 _ -> l1

val values: #a: eqtype -> #b: eqtype -> m:map a b -> Tot(l: list b{length l = size m})
let values #a #b m = 
    match m with 
    | MapCons lst -> FStar.List.Tot.map  (fun (x: kv a b) -> x.value) lst
    | MapList _ l2 -> l2

val _mapToMapList: #a: eqtype -> #b: eqtype -> m: map a b -> Tot(r: map a b{isMapList r = true /\ size m = size r})

let _mapToMapList #a #b m = 
    let keys = keySet #a #b m in 
    let values = values #a #b m in 
    assert(length keys = length values);
    let map = createEmptyL #a #b in 
    putAll2 #a #b map keys values 

val _mapToMapCons: #a: eqtype -> #b: eqtype -> m: map a b {size m >0} -> 
        Tot(r: map a b {isMapCons r = true /\ size m = size r})

let _mapToMapCons #a #b m = 
    match m with 
    | MapCons _ -> m 
    | MapList l1 l2 -> 
        let empty = createEmptyC #a #b in 
        putAll2 #a #b empty l1 l2

val pairs: #a: eqtype-> #b: eqtype -> m: map a b{size m > 0} -> Tot (list (kv a b))
let pairs #a #b m = 
    match m with 
    | MapCons lst -> lst 
    | MapList _ _ ->    let newMap =  _mapToMapCons #a #b m in 
                        match newMap with 
                        MapCons lst -> lst

assume val sorted: #a: eqtype  -> (a -> a -> Tot bool) -> s:list a -> Tot bool (decreases (length s))

assume val sort: #a: eqtype ->  l: list a ->f: (a -> a -> Tot bool){total_order a f} -> Tot (r: list a {sorted f r /\ length l = length r})

val _equals: #a: eqtype -> #b: eqtype -> l1: list (kv a b) -> 
    l2: list (kv a b){length l1 = length l2}-> counter: nat{counter < length l1} -> Tot bool (decreases (length l1 - counter))

let rec _equals #a #b l1 l2 counter = 
    let e1 = index l1 counter in 
    let e2 = index l2 counter in 
    equalKV e1 e2 && 
        (
            if (counter + 1 < length l1) 
                then _equals #a #b l1 l2 (counter+1) 
            else true
        )

val equals: #a: eqtype -> #b: eqtype -> 
        m1: map a b -> m2: map a b {size m1 = size m2 /\ size m1 > 0} -> 
        f:((kv a b) -> (kv a b) -> Tot bool){total_order (kv a b) f} -> bool

let equals #a #b m1 m2 f = 
    let m1 = _mapToMapCons #a #b m1 in 
    let m2 = _mapToMapCons #a #b m2 in 
    let m1 = sort (match m1 with | MapCons lst -> lst) f in 
    let m2 = sort (match m2 with | MapCons lst -> lst) f in 
    assert(length m1 = length m2);
    _equals #a #b m1 m2 0

val index: #a: eqtype -> #b: eqtype -> m: map a b ->i : nat {i < size m} ->  kv a b 
let index #a #b m i = 
    match m with 
    |MapCons lst -> index lst i
    |MapList l1 l2 -> let key = index l1 i in 
                        let value = index l2 i in 
                        MkKV key value