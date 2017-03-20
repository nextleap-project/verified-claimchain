module ListExpansion

open FStar.List.Tot
open FStar.Option


val replace: lst: list 'a -> counter : nat -> value : 'a -> Tot(list 'a)

let replace lst counter value =
let rec f lst c lst_temp=
match lst with
| hd::tl -> let lst_temp  = 
    (if c = counter 
        then FStar.List.Tot.append lst_temp [value] 
        else FStar.List.Tot.append lst_temp [hd])   
    in  f tl (c+1) lst_temp
| [] -> lst_temp
in f lst 0 []
