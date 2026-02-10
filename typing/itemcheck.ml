open Language
open Zutils
open Bidirect
open Zdatatype

type task =
  | TypeCheck of string * Nt.t rty
  | ValidCheck of string * Nt.t prop
  | SatCheck of string * Nt.t prop

type type_result = Success of built_in_ctx | Fail

type task_result =
  | TypeCheckResult of string * type_result
  | ValidResult of string * Nt.t prop * Prover.valid_result
  | SatResult of string * Nt.t prop * Prover.smt_result

let _type_check_info name rty =
  TypecheckerLog.result @@ fun _ ->
  Pp.printf "@{<bold>Type Check %s:@}\n" name;
  Pp.printf "@{<bold>check against with:@} %s\n" (layout_rty rty)

let _type_check_succ name =
  TypecheckerLog.result @@ fun _ ->
  Pp.printf "@{<bold>@{<yellow>Task %s, type check succeeded@}@}\n" name

let _type_check_fail name =
  TypecheckerLog.result @@ fun _ ->
  Pp.printf "@{<bold>@{<red>Task %s, type check failed@}@}\n" name

let _type_check_result_info name result =
  match result with
  | Success _ ->
      TypecheckerLog.result @@ fun _ ->
      Pp.printf "@{<bold>@{<yellow>Task %s, type check succeeded@}@}\n" name
  | Fail ->
      TypecheckerLog.result @@ fun _ ->
      Pp.printf "@{<bold>@{<red>Task %s, type check failed@}@}\n" name

let _valid_result_info name prop = function
  | Prover.SmtValid ->
      Pp.printf "@{<bold>@{<yellow>Query %s (%s) is valid.@}@}\n" name
        (layout_prop prop)
  | SmtInvalid ->
      Pp.printf "@{<bold>@{<red>Query %s (%s) is invalid.@}@}\n" name
        (layout_prop prop)
  | Unknown reason ->
      let reason = Option.value ~default:"unknown" reason in
      Pp.printf "@{<bold>@{<red>Query %s (%s) is unknown: %s.@}@}\n" name
        (layout_prop prop) reason

let _sat_result_info name prop = function
  | Prover.SmtSat ->
      Pp.printf "@{<bold>@{<yellow>Query %s (%s) is sat.@}@}\n" name
        (layout_prop prop)
  | SmtUnsat ->
      Pp.printf "@{<bold>@{<red>Query %s (%s) is unsat.@}@}\n" name
        (layout_prop prop)
  | Unknown reason ->
      let reason = Option.value ~default:"unknown" reason in
      Pp.printf "@{<bold>@{<red>Query %s (%s) is unknown: %s.@}@}\n" name
        (layout_prop prop) reason

let _task_result_info = function
  | TypeCheckResult (name, result) -> _type_check_result_info name result
  | ValidResult (name, prop, res) -> _valid_result_info name prop res
  | SatResult (name, prop, res) -> _sat_result_info name prop res

let mk_imp_m bctx items =
  List.fold_left
    (fun (bctx, imp_m) item ->
      match item with
      | MFuncImp { name; body; _ } -> (bctx, StrMap.add name.x body imp_m)
      | MRty { is_assumption = true; name; rty } ->
          (rty_add_to_right bctx name#:rty, imp_m)
      | _ -> (bctx, imp_m))
    (bctx, StrMap.empty) items

let mk_invs items =
  List.fold_left
    (fun m -> function
      | MLocalRty { host_name; name; rty; _ } ->
          StrMap.update host_name
            (function
              | None -> Some [ name#:rty ] | Some l -> Some ((name#:rty) :: l))
            m
      | _ -> m)
    StrMap.empty items

let mk_tasks items =
  List.filter_map
    (function
      | MRty { is_assumption = false; name; rty } ->
          Some (TypeCheck (name, rty))
      | MCheckValid { name; prop } -> Some (ValidCheck (name, prop))
      | MCheckSat { name; prop } -> Some (SatCheck (name, prop))
      | _ -> None)
    items

let item_check bctx inv_m imp_m (name, rty) =
  let imp =
    StrMap.find
      (spf "The source code of given refinement type '%s' is missing." name)
      imp_m name
  in
  let () =
    TypecheckerLog.result @@ fun _ ->
    Pp.printf "@{<bold>imp_m(%s)@}\n%s\n" name (layout_typed_term imp)
  in
  let () = Statistic.create_stat name imp in
  let () = Statistic.stat_update_rty (name, counter_rty_qt_qpred rty) in
  let invs = match StrMap.find_opt inv_m name with None -> [] | Some l -> l in
  let sol, rty = instantiate_rty_by_nty [%here] rty imp.ty in
  let invs = List.map (fun x -> x#=>(map_rty (Nt.msubst_nt sol))) invs in
  let () = _type_check_info name rty in
  let time, res =
    clock (fun () ->
        term_type_check bctx (Common.Rctx.emp name [] invs) (imp, rty))
  in
  let () = Statistic.stat_total_time (name, time) in
  let () = Statistic.store_stat stat_file in
  let res =
    match res with
    | Some _ -> Success (rty_add_to_right bctx name#:rty)
    | None -> Fail
  in
  _type_check_result_info name res;
  res

let check_prop_valid name prop =
  let res = Prover.check_valid [%here] prop in
  _valid_result_info name prop res;
  res

let check_prop_sat name prop =
  let res = Prover.check_sat [%here] prop in
  _sat_result_info name prop res;
  res

let check_task bctx inv_m imp_m task =
  match task with
  | TypeCheck (name, rty) ->
      TypeCheckResult (name, item_check bctx inv_m imp_m (name, rty))
  | ValidCheck (name, prop) ->
      ValidResult (name, prop, check_prop_valid name prop)
  | SatCheck (name, prop) -> SatResult (name, prop, check_prop_sat name prop)

let is_success = function
  | TypeCheckResult (_, Success _) -> true
  | ValidResult (_, _, Prover.SmtValid) -> true
  | SatResult (_, _, Prover.SmtSat) -> true
  | _ -> false

let result_name = function
  | TypeCheckResult (name, _) -> name
  | ValidResult (name, _, _) -> name
  | SatResult (name, _, _) -> name

let struc_check bctx items =
  let bctx, imp_m = mk_imp_m bctx items in
  let inv_m = mk_invs items in
  let tasks = mk_tasks items in
  let _, passed, failed =
    List.fold_left
      (fun (bctx, passed, failed) task ->
        let result = check_task bctx inv_m imp_m task in
        if is_success result then
          let bctx =
            match result with
            | TypeCheckResult (_, Success bctx) -> bctx
            | _ -> bctx
          in
          (bctx, passed @ [ result ], failed)
        else (bctx, passed, failed @ [ result ]))
      (bctx, [], []) tasks
  in
  let () =
    TypecheckerLog.result @@ fun _ ->
    Pp.printf "@{<bold>Summary (total %i tasks):@}\n" (List.length tasks)
  in
  let () =
    match failed with
    | [] ->
        TypecheckerLog.result @@ fun _ ->
        Pp.printf "@{<bold>@{<yellow>All tasks succeeded@}@}\n"
    | _ -> TypecheckerLog.result @@ fun _ -> List.iter _task_result_info failed
  in
  let passed = List.map result_name passed in
  let failed = List.map result_name failed in
  (Some bctx, passed, failed)
