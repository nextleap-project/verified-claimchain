module Test

open IntegerExpansion


val computeMaxLevel: elements: nat{elements > 1} -> Tot(nat)
let computeMaxLevel elements = 
    IntegerExpansion.log2Tot elements
