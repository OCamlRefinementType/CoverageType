type bool = True | False
type 'a rbtree = Rbtleaf | Rbtnode of bool * 'a rbtree * 'a * 'a rbtree

val ( == ) : 'a. 'a -> 'a -> bool
val ( != ) : 'a. 'a -> 'a -> bool
val ( < ) : int -> int -> bool
val ( <= ) : int -> int -> bool
val ( > ) : int -> int -> bool
val ( >= ) : int -> int -> bool
val ( + ) : int -> int -> int
val ( - ) : int -> int -> int
val ( mod ) : int -> int -> int

val num_black : 'a rbtree -> int -> bool
val rb_leaf : 'a rbtree -> bool
val rb_root : 'a rbtree -> 'a -> bool
val rb_root_color : 'a rbtree -> bool -> bool
val rb_lch : 'a rbtree -> 'a rbtree -> bool
val rb_rch : 'a rbtree -> 'a rbtree -> bool
val no_red_red : 'a rbtree -> bool
