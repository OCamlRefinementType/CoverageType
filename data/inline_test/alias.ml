type record1 = { a : int; b : bool }
type record2 = { c : float; d : record1 list }
type record3 = { e : record1; d : record2 list }

val x : record1 * record2 * record3
