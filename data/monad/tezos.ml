type shell_header = { branch : hash_t }
type operation = { shell : shell_header; proto : byte }

let operation_proto_gen = small_string

let operation_mock_proto_gen =
  let (len_gen : int gen) =
    frequency [ 9; 1 ] (fun (i : int) ->
        if i == 0 then return 0
        else if i == 1 then int_range 0 31
        else return Err)
  in
  string_size len_gen

let operation_gen block_hash_gen =
  prod_block_hash_gen >>= fun branch ->
  operation_proto_gen >|= fun proto ->
  { shell = { branch }; proto = Bytes.of_string proto }
