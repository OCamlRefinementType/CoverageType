val small_string : string gen
val frequency : int list -> (int -> 'a gen) -> 'a gen
val return : 'a -> 'a gen
val int_range : int -> int -> int gen
val string_size : int gen -> string gen
val ( >>= ) : 'a1 gen -> ('a1 -> 'a2 gen) -> 'a2 gen
val ( >|= ) : 'a1 gen -> ('a1 -> 'a2) -> 'a2 gen

type shell_header = { branch : Hash.t }
type operation = { shell : shell_header; proto : string }

let operation_proto_gen : string gen = small_string

let operation_mock_proto_gen : string gen =
  let (len_gen : int gen) =
    frequency [ 9; 1 ] (fun (i : int) ->
        if i == 0 then return 0
        else if i == 1 then int_range 0 31
        else return Err)
  in
  string_size len_gen

let operation_gen (block_hash_gen : Hash.t gen) : operation gen =
  block_hash_gen >>= fun (branch : Hash.t) ->
  operation_proto_gen >|= fun (proto : string) -> { shell = { branch }; proto }
