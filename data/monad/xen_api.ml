let[@library] oneofl (b1 : baseType) ?r:(l : 'b1 list) =
  M (list_mem l v : [%v: 'b1])

let[@library] frequencyl (b1 : baseType) ?r:(l : (int * 'b1) list) =
  M (list_snd_mem l v : [%v: 'b1])

let[@library] is_testable_kind ?r:(fk : int) =
  (v == is_testable_kind fk : [%v: bool])

let[@library] has_immediate_timeout ?r:(fk : int) =
  (v == has_immediate_timeout fk : [%v: bool])

let[@library] return (b1 : baseType) ?r:(x : 'b1) = M (v == x : [%v: 'b1])

let[@library] ( >|= ) (b1 : baseType) (b2 : baseType) (p1 : 'b1 -> bool)
    (p2 : 'b1 -> 'b2 -> bool) ?r:(_ = M (p1 v : [%v: 'b1]))
    ?r:(_ = fun ?r:(x = ((p1 v : [%v: 'b1]) [@over])) -> (p2 x v : [%v: 'b2])) =
  M (fun ((x [@ex]) : 'b1) -> p1 x && p2 x v : [%v: 'b2])

let[@library] ( >>= ) (b1 : baseType) (b2 : baseType) (p1 : 'b1 -> bool)
    (p2 : 'b1 -> 'b2 -> bool) ?r:(_ = M (p1 v : [%v: 'b1]))
    ?r:(_ = fun ?r:(x = ((p1 v : [%v: 'b1]) [@over])) -> M (p2 x v : [%v: 'b2]))
    =
  M (fun ((x [@ex]) : 'b1) -> p1 x && p2 x v : [%v: 'b2])

let[@library] int_bound ?r:(n = ((0 <= v : [%v: int]) [@over])) =
  M (0 <= v && v <= n : [%v: int])

let[@library] union (b1 : baseType) (p1 : 'b1 -> bool) (p2 : 'b1 -> bool)
    ?r:(_ = M (p1 v : [%v: 'b1])) ?r:(_ = M (p2 v : [%v: 'b1])) =
  M (p1 v || p2 v : [%v: 'b1])

let[@library] list_size (p1 : int -> bool) ?r:(_ = M (p1 v : [%v: int]))
    ?r:(_ = M (wf_select_fd_spec v : [%v: select_fd_spec])) =
  M (wf_select_fd_spec_list v && p1 (list_len v) : [%v: select_fd_spec list])

let[@library] list_repeat ?r:(n = ((0 <= v : [%v: int]) [@over]))
    ?r:(_ = M (wf_select_fd_spec v : [%v: select_fd_spec])) =
  M (wf_select_fd_spec_list v && list_len v == n : [%v: select_fd_spec list])

let[@library] delay_of_size ?r:(total_delay : float) ?r:(size : int) =
  M (wf_delay_size v total_delay size : [%v: Delay.t option])

let fd_size_gen : int gen =
  let (ocaml_unix_buffer_size : int) = 65536 in
  oneofl
    [
      0;
      1;
      100;
      4096;
      ocaml_unix_buffer_size - 1;
      ocaml_unix_buffer_size;
      ocaml_unix_buffer_size + 1;
      2 * ocaml_unix_buffer_size;
      (10 * ocaml_unix_buffer_size) + 3;
    ]

let[@assert] fd_size_gen = M (wf_fd_size v : [%v: int])
let file_kind_gen : int gen = oneofl [ 0; 1; 2; 3; 4; 5; 6 ]
let[@assert] file_kind_gen = M (wf_file_kind v : [%v: int])
let timeout_gen : float gen = oneofl [ 0.0; 0.001; 0.1; 0.3 ]
let[@assert] timeout_gen = M (wf_timeouts v : [%v: float])
let total_delay_gen : float gen = oneofl [ 0.001; 0.01; 0.1; 0.4 ]
let[@assert] total_delay_gen = M (wf_total_delay v : [%v: float])
let size_bound_gen : int gen = frequencyl [ (4, 0); (4, 2); (2, 10); (1, 100) ]
let[@assert] size_bound_gen = M (wf_size_bound v : [%v: int])

let testable_file_kind_gen : int gen =
  file_kind_gen >|= fun (fk : int) -> if is_testable_kind fk then fk else Err

let[@assert] testable_file_kind_gen = M (is_testable_kind v : [%v: int])

let select_fd_spec_gen : select_fd_spec gen =
  testable_file_kind_gen >>= fun (kind : int) ->
  timeout_gen >|= fun (wait : float) ->
  let (w : float) = if has_immediate_timeout kind then 0. else wait in
  { kind; wait = w }

let[@assert] select_fd_spec_gen = M (wf_select_fd_spec v : [%v: select_fd_spec])

let file_list_gen : select_fd_spec list gen =
  size_bound_gen >>= fun (size_bound : int) ->
  let (size_gen : int gen) = int_bound size_bound in
  (* generates 2 kinds of lists:
     - lists that contain only a single file kind
     - lists that contain multiple file kinds

     This is important for testing [select], because a single
       [Unix.S_REG] would cause it to return immediately,
       making it unlikely that we're actually testing the behaviour for other file descriptors.
  *)
  union
    (size_gen >>= fun (size : int) -> list_repeat size select_fd_spec_gen)
    (list_size size_gen select_fd_spec_gen)

let[@assert] file_list_gen =
  M (wf_select_fd_spec_list v : [%v: select_fd_spec list])

let fd_gen : fd gen =
  (* order matters here for shrinking: shrink timeout first so that shrinking completes sooner! *)
  total_delay_gen >>= fun (total_delay : float) ->
  fd_size_gen >>= fun (s : int) ->
  testable_file_kind_gen >>= fun (kind : int) ->
  let (size : int) = if kind == 0 then 512 else s in
  delay_of_size total_delay size >>= fun (delay : Delay.t option) ->
  (* see observations.ml, we can't easily change size afterwards *)
  return { size; delay_read = delay; delay_write = delay; kind }

let[@assert] fd_gen = M (wf_fd v : [%v: fd])
