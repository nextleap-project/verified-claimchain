module IntegerExpansion

open FStar.List.Tot
open FStar.Option

private val temp_log : r: nat  -> n : nat  -> ML(nat)
let rec temp_log r n = 
    if n >= (pow2 r) 
        then r 
        else temp_log (r+1) n


val log2 : n:nat{n>1}-> ML(int)
let log2 n = 
    temp_log 1 n
