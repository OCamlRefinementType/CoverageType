type bool = True | False
type 'a tree = Leaf | Node of 'a * 'a tree * 'a tree

val ( == ) : 'a. 'a -> 'a -> bool
val ( != ) : 'a. 'a -> 'a -> bool
val ( < ) : int -> int -> bool
val ( <= ) : int -> int -> bool
val ( > ) : int -> int -> bool
val ( >= ) : int -> int -> bool
val ( + ) : int -> int -> int
val ( - ) : int -> int -> int
val ( mod ) : int -> int -> int

val depth : 'a tree -> int -> bool
val leaf : 'a tree -> bool
val root : 'a tree -> 'a -> bool
val lch : 'a tree -> 'a tree -> bool
val rch : 'a tree -> 'a tree -> bool
val lower_bound : int tree -> int -> bool
val upper_bound : int tree -> int -> bool
val bst : int tree -> bool
