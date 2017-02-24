module SkipListStatement    

open FStar.List.Tot

type skipList 'a = 
    | Empty: skipList 'a
    | Mk: value : 'a -> levels : int{levels > 0}->  a: list(skipList 'a){length a = levels}-> skipList    'a