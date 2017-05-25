open Prims
let tc_one_file remaining uenv =
  let uu____26 = uenv in
  match uu____26 with
  | (dsenv,env) ->
      let uu____40 =
        match remaining with
        | intf::impl::remaining1 when
            FStar_Universal.needs_interleaving intf impl ->
            let uu____61 =
              FStar_Universal.tc_one_file dsenv env (Some intf) impl in
            (match uu____61 with
             | (uu____76,dsenv1,env1) ->
                 (((Some intf), impl), dsenv1, env1, remaining1))
        | intf_or_impl::remaining1 ->
            let uu____93 =
              FStar_Universal.tc_one_file dsenv env None intf_or_impl in
            (match uu____93 with
             | (uu____108,dsenv1,env1) ->
                 ((None, intf_or_impl), dsenv1, env1, remaining1))
        | [] -> failwith "Impossible" in
      (match uu____40 with
       | ((intf,impl),dsenv1,env1,remaining1) ->
           ((intf, impl), (dsenv1, env1), None, remaining1))
let tc_prims:
  Prims.unit -> (FStar_ToSyntax_Env.env* FStar_TypeChecker_Env.env) =
  fun uu____165  ->
    let uu____166 = FStar_Universal.tc_prims () in
    match uu____166 with | (uu____174,dsenv,env) -> (dsenv, env)
type env_t = (FStar_ToSyntax_Env.env* FStar_TypeChecker_Env.env)
type modul_t = FStar_Syntax_Syntax.modul option
type stack_t = (env_t* modul_t) Prims.list
let pop uu____199 msg =
  match uu____199 with
  | (uu____203,env) ->
      (FStar_Universal.pop_context env msg; FStar_Options.pop ())
type push_kind =
  | SyntaxCheck
  | LaxCheck
  | FullCheck
let uu___is_SyntaxCheck: push_kind -> Prims.bool =
  fun projectee  ->
    match projectee with | SyntaxCheck  -> true | uu____209 -> false
let uu___is_LaxCheck: push_kind -> Prims.bool =
  fun projectee  ->
    match projectee with | LaxCheck  -> true | uu____213 -> false
let uu___is_FullCheck: push_kind -> Prims.bool =
  fun projectee  ->
    match projectee with | FullCheck  -> true | uu____217 -> false
let push:
  (FStar_ToSyntax_Env.env* FStar_TypeChecker_Env.env) ->
    push_kind ->
      Prims.bool ->
        Prims.string -> (FStar_ToSyntax_Env.env* FStar_TypeChecker_Env.env)
  =
  fun uu____230  ->
    fun kind  ->
      fun restore_cmd_line_options1  ->
        fun msg  ->
          match uu____230 with
          | (dsenv,tcenv) ->
              let tcenv1 =
                let uu___209_241 = tcenv in
                {
                  FStar_TypeChecker_Env.solver =
                    (uu___209_241.FStar_TypeChecker_Env.solver);
                  FStar_TypeChecker_Env.range =
                    (uu___209_241.FStar_TypeChecker_Env.range);
                  FStar_TypeChecker_Env.curmodule =
                    (uu___209_241.FStar_TypeChecker_Env.curmodule);
                  FStar_TypeChecker_Env.gamma =
                    (uu___209_241.FStar_TypeChecker_Env.gamma);
                  FStar_TypeChecker_Env.gamma_cache =
                    (uu___209_241.FStar_TypeChecker_Env.gamma_cache);
                  FStar_TypeChecker_Env.modules =
                    (uu___209_241.FStar_TypeChecker_Env.modules);
                  FStar_TypeChecker_Env.expected_typ =
                    (uu___209_241.FStar_TypeChecker_Env.expected_typ);
                  FStar_TypeChecker_Env.sigtab =
                    (uu___209_241.FStar_TypeChecker_Env.sigtab);
                  FStar_TypeChecker_Env.is_pattern =
                    (uu___209_241.FStar_TypeChecker_Env.is_pattern);
                  FStar_TypeChecker_Env.instantiate_imp =
                    (uu___209_241.FStar_TypeChecker_Env.instantiate_imp);
                  FStar_TypeChecker_Env.effects =
                    (uu___209_241.FStar_TypeChecker_Env.effects);
                  FStar_TypeChecker_Env.generalize =
                    (uu___209_241.FStar_TypeChecker_Env.generalize);
                  FStar_TypeChecker_Env.letrecs =
                    (uu___209_241.FStar_TypeChecker_Env.letrecs);
                  FStar_TypeChecker_Env.top_level =
                    (uu___209_241.FStar_TypeChecker_Env.top_level);
                  FStar_TypeChecker_Env.check_uvars =
                    (uu___209_241.FStar_TypeChecker_Env.check_uvars);
                  FStar_TypeChecker_Env.use_eq =
                    (uu___209_241.FStar_TypeChecker_Env.use_eq);
                  FStar_TypeChecker_Env.is_iface =
                    (uu___209_241.FStar_TypeChecker_Env.is_iface);
                  FStar_TypeChecker_Env.admit =
                    (uu___209_241.FStar_TypeChecker_Env.admit);
                  FStar_TypeChecker_Env.lax = (kind = LaxCheck);
                  FStar_TypeChecker_Env.lax_universes =
                    (uu___209_241.FStar_TypeChecker_Env.lax_universes);
                  FStar_TypeChecker_Env.type_of =
                    (uu___209_241.FStar_TypeChecker_Env.type_of);
                  FStar_TypeChecker_Env.universe_of =
                    (uu___209_241.FStar_TypeChecker_Env.universe_of);
                  FStar_TypeChecker_Env.use_bv_sorts =
                    (uu___209_241.FStar_TypeChecker_Env.use_bv_sorts);
                  FStar_TypeChecker_Env.qname_and_index =
                    (uu___209_241.FStar_TypeChecker_Env.qname_and_index)
                } in
              let dsenv1 =
                FStar_ToSyntax_Env.set_syntax_only dsenv (kind = SyntaxCheck) in
              let res = FStar_Universal.push_context (dsenv1, tcenv1) msg in
              (FStar_Options.push ();
               if restore_cmd_line_options1
               then
                 (let uu____248 =
                    FStar_Options.restore_cmd_line_options false in
                  FStar_All.pipe_right uu____248 FStar_Pervasives.ignore)
               else ();
               res)
let mark:
  (FStar_ToSyntax_Env.env* FStar_TypeChecker_Env.env) ->
    (FStar_ToSyntax_Env.env* FStar_TypeChecker_Env.env)
  =
  fun uu____256  ->
    match uu____256 with
    | (dsenv,env) ->
        let dsenv1 = FStar_ToSyntax_Env.mark dsenv in
        let env1 = FStar_TypeChecker_Env.mark env in
        (FStar_Options.push (); (dsenv1, env1))
let reset_mark uu____276 =
  match uu____276 with
  | (uu____279,env) ->
      let dsenv = FStar_ToSyntax_Env.reset_mark () in
      let env1 = FStar_TypeChecker_Env.reset_mark env in
      (FStar_Options.pop (); (dsenv, env1))
let cleanup uu____292 =
  match uu____292 with
  | (dsenv,env) -> FStar_TypeChecker_Env.cleanup_interactive env
let commit_mark:
  (FStar_ToSyntax_Env.env* FStar_TypeChecker_Env.env) ->
    (FStar_ToSyntax_Env.env* FStar_TypeChecker_Env.env)
  =
  fun uu____303  ->
    match uu____303 with
    | (dsenv,env) ->
        let dsenv1 = FStar_ToSyntax_Env.commit_mark dsenv in
        let env1 = FStar_TypeChecker_Env.commit_mark env in (dsenv1, env1)
let check_frag:
  (FStar_ToSyntax_Env.env* FStar_TypeChecker_Env.env) ->
    FStar_Syntax_Syntax.modul option ->
      (FStar_Parser_ParseIt.input_frag* Prims.bool) ->
        (FStar_Syntax_Syntax.modul option* (FStar_ToSyntax_Env.env*
          FStar_TypeChecker_Env.env)* Prims.int) option
  =
  fun uu____330  ->
    fun curmod  ->
      fun frag  ->
        match uu____330 with
        | (dsenv,env) ->
            (try
               let uu____362 =
                 FStar_Universal.tc_one_fragment curmod dsenv env frag in
               match uu____362 with
               | Some (m,dsenv1,env1) ->
                   let uu____384 =
                     let uu____391 = FStar_Errors.get_err_count () in
                     (m, (dsenv1, env1), uu____391) in
                   Some uu____384
               | uu____401 -> None
             with
             | FStar_Errors.Error (msg,r) when
                 let uu____423 = FStar_Options.trace_error () in
                 Prims.op_Negation uu____423 ->
                 (FStar_TypeChecker_Err.add_errors env [(msg, r)]; None)
             | FStar_Errors.Err msg when
                 let uu____436 = FStar_Options.trace_error () in
                 Prims.op_Negation uu____436 ->
                 ((let uu____438 =
                     let uu____442 =
                       let uu____445 = FStar_TypeChecker_Env.get_range env in
                       (msg, uu____445) in
                     [uu____442] in
                   FStar_TypeChecker_Err.add_errors env uu____438);
                  None))
let deps_of_our_file:
  Prims.string -> (Prims.string Prims.list* Prims.string option) =
  fun filename  ->
    let deps =
      FStar_Dependencies.find_deps_if_needed
        FStar_Parser_Dep.VerifyFigureItOut [filename] in
    let uu____465 =
      FStar_List.partition
        (fun x  ->
           let uu____471 = FStar_Parser_Dep.lowercase_module_name x in
           let uu____472 = FStar_Parser_Dep.lowercase_module_name filename in
           uu____471 <> uu____472) deps in
    match uu____465 with
    | (deps1,same_name) ->
        let maybe_intf =
          match same_name with
          | intf::impl::[] ->
              ((let uu____489 =
                  (let uu____490 = FStar_Parser_Dep.is_interface intf in
                   Prims.op_Negation uu____490) ||
                    (let uu____491 = FStar_Parser_Dep.is_implementation impl in
                     Prims.op_Negation uu____491) in
                if uu____489
                then
                  let uu____492 =
                    FStar_Util.format2
                      "Found %s and %s but not an interface + implementation"
                      intf impl in
                  FStar_Util.print_warning uu____492
                else ());
               Some intf)
          | impl::[] -> None
          | uu____495 ->
              ((let uu____498 =
                  FStar_Util.format1 "Unsupported: ended up with %s"
                    (FStar_String.concat " " same_name) in
                FStar_Util.print_warning uu____498);
               None) in
        (deps1, maybe_intf)
type m_timestamps =
  (Prims.string option* Prims.string* FStar_Util.time option*
    FStar_Util.time) Prims.list
let rec tc_deps:
  modul_t ->
    stack_t ->
      env_t ->
        Prims.string Prims.list ->
          m_timestamps -> (stack_t* env_t* m_timestamps)
  =
  fun m  ->
    fun stack  ->
      fun env  ->
        fun remaining  ->
          fun ts  ->
            match remaining with
            | [] -> (stack, env, ts)
            | uu____531 ->
                let stack1 = (env, m) :: stack in
                let env1 =
                  let uu____542 =
                    let uu____543 = FStar_Options.lax () in
                    if uu____543 then LaxCheck else FullCheck in
                  push env uu____542 true "typecheck_modul" in
                let uu____545 = tc_one_file remaining env1 in
                (match uu____545 with
                 | ((intf,impl),env2,modl,remaining1) ->
                     let uu____578 =
                       let intf_t =
                         match intf with
                         | Some intf1 ->
                             let uu____586 =
                               FStar_Util.get_file_last_modification_time
                                 intf1 in
                             Some uu____586
                         | None  -> None in
                       let impl_t =
                         FStar_Util.get_file_last_modification_time impl in
                       (intf_t, impl_t) in
                     (match uu____578 with
                      | (intf_t,impl_t) ->
                          tc_deps m stack1 env2 remaining1
                            ((intf, impl, intf_t, impl_t) :: ts)))
let update_deps:
  Prims.string ->
    modul_t ->
      stack_t -> env_t -> m_timestamps -> (stack_t* env_t* m_timestamps)
  =
  fun filename  ->
    fun m  ->
      fun stk  ->
        fun env  ->
          fun ts  ->
            let is_stale intf impl intf_t impl_t =
              let impl_mt = FStar_Util.get_file_last_modification_time impl in
              (FStar_Util.is_before impl_t impl_mt) ||
                (match (intf, intf_t) with
                 | (Some intf1,Some intf_t1) ->
                     let intf_mt =
                       FStar_Util.get_file_last_modification_time intf1 in
                     FStar_Util.is_before intf_t1 intf_mt
                 | (None ,None ) -> false
                 | (uu____652,uu____653) ->
                     failwith
                       "Impossible, if the interface is None, the timestamp entry should also be None") in
            let rec iterate depnames st env' ts1 good_stack good_ts =
              let match_dep depnames1 intf impl =
                match intf with
                | None  ->
                    (match depnames1 with
                     | dep1::depnames' ->
                         if dep1 = impl
                         then (true, depnames')
                         else (false, depnames1)
                     | uu____717 -> (false, depnames1))
                | Some intf1 ->
                    (match depnames1 with
                     | depintf::dep1::depnames' ->
                         if (depintf = intf1) && (dep1 = impl)
                         then (true, depnames')
                         else (false, depnames1)
                     | uu____734 -> (false, depnames1)) in
              let rec pop_tc_and_stack env1 stack ts2 =
                match ts2 with
                | [] -> env1
                | uu____781::ts3 ->
                    (pop env1 "";
                     (let uu____803 =
                        let uu____811 = FStar_List.hd stack in
                        let uu____816 = FStar_List.tl stack in
                        (uu____811, uu____816) in
                      match uu____803 with
                      | ((env2,uu____830),stack1) ->
                          pop_tc_and_stack env2 stack1 ts3)) in
              match ts1 with
              | ts_elt::ts' ->
                  let uu____864 = ts_elt in
                  (match uu____864 with
                   | (intf,impl,intf_t,impl_t) ->
                       let uu____882 = match_dep depnames intf impl in
                       (match uu____882 with
                        | (b,depnames') ->
                            let uu____893 =
                              (Prims.op_Negation b) ||
                                (is_stale intf impl intf_t impl_t) in
                            if uu____893
                            then
                              let env1 =
                                pop_tc_and_stack env'
                                  (FStar_List.rev_append st []) ts1 in
                              tc_deps m good_stack env1 depnames good_ts
                            else
                              (let uu____905 =
                                 let uu____913 = FStar_List.hd st in
                                 let uu____918 = FStar_List.tl st in
                                 (uu____913, uu____918) in
                               match uu____905 with
                               | (stack_elt,st') ->
                                   iterate depnames' st' env' ts' (stack_elt
                                     :: good_stack) (ts_elt :: good_ts))))
              | [] -> tc_deps m good_stack env' depnames good_ts in
            let uu____958 = deps_of_our_file filename in
            match uu____958 with
            | (filenames,uu____967) ->
                iterate filenames (FStar_List.rev_append stk []) env
                  (FStar_List.rev_append ts []) [] []
let json_to_str: FStar_Util.json -> Prims.string =
  fun uu___199_998  ->
    match uu___199_998 with
    | FStar_Util.JsonNull  -> "null"
    | FStar_Util.JsonBool b ->
        FStar_Util.format1 "bool (%s)" (if b then "true" else "false")
    | FStar_Util.JsonInt i ->
        let uu____1002 = FStar_Util.string_of_int i in
        FStar_Util.format1 "int (%s)" uu____1002
    | FStar_Util.JsonStr s -> FStar_Util.format1 "string (%s)" s
    | FStar_Util.JsonList uu____1004 -> "list (...)"
    | FStar_Util.JsonAssoc uu____1006 -> "dictionary (...)"
exception UnexpectedJsonType of (Prims.string* FStar_Util.json)
let uu___is_UnexpectedJsonType: Prims.exn -> Prims.bool =
  fun projectee  ->
    match projectee with
    | UnexpectedJsonType uu____1017 -> true
    | uu____1020 -> false
let __proj__UnexpectedJsonType__item__uu___:
  Prims.exn -> (Prims.string* FStar_Util.json) =
  fun projectee  ->
    match projectee with | UnexpectedJsonType uu____1031 -> uu____1031
let js_fail expected got = raise (UnexpectedJsonType (expected, got))
let js_int: FStar_Util.json -> Prims.int =
  fun uu___200_1048  ->
    match uu___200_1048 with
    | FStar_Util.JsonInt i -> i
    | other -> js_fail "int" other
let js_str: FStar_Util.json -> Prims.string =
  fun uu___201_1053  ->
    match uu___201_1053 with
    | FStar_Util.JsonStr s -> s
    | other -> js_fail "string" other
let js_list k uu___202_1071 =
  match uu___202_1071 with
  | FStar_Util.JsonList l -> FStar_List.map k l
  | other -> js_fail "list" other
let js_assoc: FStar_Util.json -> (Prims.string* FStar_Util.json) Prims.list =
  fun uu___203_1083  ->
    match uu___203_1083 with
    | FStar_Util.JsonAssoc a -> a
    | other -> js_fail "dictionary" other
let js_pushkind: FStar_Util.json -> push_kind =
  fun s  ->
    let uu____1098 = js_str s in
    match uu____1098 with
    | "syntax" -> SyntaxCheck
    | "lax" -> LaxCheck
    | "full" -> FullCheck
    | uu____1099 -> js_fail "push_kind" s
let js_reductionrule: FStar_Util.json -> FStar_TypeChecker_Normalize.step =
  fun s  ->
    let uu____1103 = js_str s in
    match uu____1103 with
    | "beta" -> FStar_TypeChecker_Normalize.Beta
    | "delta" ->
        FStar_TypeChecker_Normalize.UnfoldUntil
          FStar_Syntax_Syntax.Delta_constant
    | "iota" -> FStar_TypeChecker_Normalize.Iota
    | "zeta" -> FStar_TypeChecker_Normalize.Zeta
    | uu____1104 -> js_fail "reduction rule" s
type query' =
  | Exit
  | DescribeProtocol
  | DescribeRepl
  | Pop
  | Push of (push_kind* Prims.string* Prims.int* Prims.int* Prims.bool)
  | AutoComplete of Prims.string
  | Lookup of (Prims.string* (Prims.string* Prims.int* Prims.int) option*
  Prims.string Prims.list)
  | Compute of (Prims.string* FStar_TypeChecker_Normalize.step Prims.list
  option)
  | Search of Prims.string
  | ProtocolViolation of Prims.string
and query = {
  qq: query';
  qid: Prims.string;}
let uu___is_Exit: query' -> Prims.bool =
  fun projectee  ->
    match projectee with | Exit  -> true | uu____1149 -> false
let uu___is_DescribeProtocol: query' -> Prims.bool =
  fun projectee  ->
    match projectee with | DescribeProtocol  -> true | uu____1153 -> false
let uu___is_DescribeRepl: query' -> Prims.bool =
  fun projectee  ->
    match projectee with | DescribeRepl  -> true | uu____1157 -> false
let uu___is_Pop: query' -> Prims.bool =
  fun projectee  -> match projectee with | Pop  -> true | uu____1161 -> false
let uu___is_Push: query' -> Prims.bool =
  fun projectee  ->
    match projectee with | Push _0 -> true | uu____1171 -> false
let __proj__Push__item___0:
  query' -> (push_kind* Prims.string* Prims.int* Prims.int* Prims.bool) =
  fun projectee  -> match projectee with | Push _0 -> _0
let uu___is_AutoComplete: query' -> Prims.bool =
  fun projectee  ->
    match projectee with | AutoComplete _0 -> true | uu____1198 -> false
let __proj__AutoComplete__item___0: query' -> Prims.string =
  fun projectee  -> match projectee with | AutoComplete _0 -> _0
let uu___is_Lookup: query' -> Prims.bool =
  fun projectee  ->
    match projectee with | Lookup _0 -> true | uu____1218 -> false
let __proj__Lookup__item___0:
  query' ->
    (Prims.string* (Prims.string* Prims.int* Prims.int) option* Prims.string
      Prims.list)
  = fun projectee  -> match projectee with | Lookup _0 -> _0
let uu___is_Compute: query' -> Prims.bool =
  fun projectee  ->
    match projectee with | Compute _0 -> true | uu____1258 -> false
let __proj__Compute__item___0:
  query' ->
    (Prims.string* FStar_TypeChecker_Normalize.step Prims.list option)
  = fun projectee  -> match projectee with | Compute _0 -> _0
let uu___is_Search: query' -> Prims.bool =
  fun projectee  ->
    match projectee with | Search _0 -> true | uu____1282 -> false
let __proj__Search__item___0: query' -> Prims.string =
  fun projectee  -> match projectee with | Search _0 -> _0
let uu___is_ProtocolViolation: query' -> Prims.bool =
  fun projectee  ->
    match projectee with | ProtocolViolation _0 -> true | uu____1294 -> false
let __proj__ProtocolViolation__item___0: query' -> Prims.string =
  fun projectee  -> match projectee with | ProtocolViolation _0 -> _0
let interactive_protocol_vernum: Prims.int = Prims.parse_int "1"
let interactive_protocol_features: Prims.string Prims.list =
  ["autocomplete";
  "compute";
  "describe-protocol";
  "describe-repl";
  "exit";
  "lookup";
  "lookup/documentation";
  "lookup/definition";
  "pop";
  "peek";
  "push";
  "search"]
exception InvalidQuery of Prims.string
let uu___is_InvalidQuery: Prims.exn -> Prims.bool =
  fun projectee  ->
    match projectee with
    | InvalidQuery uu____1316 -> true
    | uu____1317 -> false
let __proj__InvalidQuery__item__uu___: Prims.exn -> Prims.string =
  fun projectee  ->
    match projectee with | InvalidQuery uu____1324 -> uu____1324
type query_status =
  | QueryOK
  | QueryNOK
  | QueryViolatesProtocol
let uu___is_QueryOK: query_status -> Prims.bool =
  fun projectee  ->
    match projectee with | QueryOK  -> true | uu____1328 -> false
let uu___is_QueryNOK: query_status -> Prims.bool =
  fun projectee  ->
    match projectee with | QueryNOK  -> true | uu____1332 -> false
let uu___is_QueryViolatesProtocol: query_status -> Prims.bool =
  fun projectee  ->
    match projectee with
    | QueryViolatesProtocol  -> true
    | uu____1336 -> false
let try_assoc key a =
  let uu____1358 =
    FStar_Util.try_find
      (fun uu____1364  -> match uu____1364 with | (k,uu____1368) -> k = key)
      a in
  FStar_Util.map_option FStar_Pervasives.snd uu____1358
let wrap_js_failure: Prims.string -> Prims.string -> FStar_Util.json -> query
  =
  fun qid  ->
    fun expected  ->
      fun got  ->
        let uu____1380 =
          let uu____1381 =
            let uu____1382 = json_to_str got in
            FStar_Util.format2 "JSON decoding failed: expected %s, got %s"
              expected uu____1382 in
          ProtocolViolation uu____1381 in
        { qq = uu____1380; qid }
let unpack_interactive_query: FStar_Util.json -> query =
  fun json  ->
    let assoc1 errloc key a =
      let uu____1402 = try_assoc key a in
      match uu____1402 with
      | Some v1 -> v1
      | None  ->
          let uu____1405 =
            let uu____1406 =
              FStar_Util.format2 "Missing key [%s] in %s." key errloc in
            InvalidQuery uu____1406 in
          raise uu____1405 in
    let request = FStar_All.pipe_right json js_assoc in
    let qid =
      let uu____1415 = assoc1 "query" "query-id" request in
      FStar_All.pipe_right uu____1415 js_str in
    try
      let query =
        let uu____1418 = assoc1 "query" "query" request in
        FStar_All.pipe_right uu____1418 js_str in
      let args =
        let uu____1423 = assoc1 "query" "args" request in
        FStar_All.pipe_right uu____1423 js_assoc in
      let arg k = assoc1 "[args]" k args in
      let try_arg k =
        let uu____1436 = try_assoc k args in
        match uu____1436 with
        | Some (FStar_Util.JsonNull ) -> None
        | other -> other in
      let uu____1441 =
        match query with
        | "exit" -> Exit
        | "pop" -> Pop
        | "describe-protocol" -> DescribeProtocol
        | "describe-repl" -> DescribeRepl
        | "peek"|"push" ->
            let uu____1442 =
              let uu____1448 =
                let uu____1449 = arg "kind" in
                FStar_All.pipe_right uu____1449 js_pushkind in
              let uu____1450 =
                let uu____1451 = arg "code" in
                FStar_All.pipe_right uu____1451 js_str in
              let uu____1452 =
                let uu____1453 = arg "line" in
                FStar_All.pipe_right uu____1453 js_int in
              let uu____1454 =
                let uu____1455 = arg "column" in
                FStar_All.pipe_right uu____1455 js_int in
              (uu____1448, uu____1450, uu____1452, uu____1454,
                (query = "peek")) in
            Push uu____1442
        | "autocomplete" ->
            let uu____1456 =
              let uu____1457 = arg "partial-symbol" in
              FStar_All.pipe_right uu____1457 js_str in
            AutoComplete uu____1456
        | "lookup" ->
            let uu____1458 =
              let uu____1467 =
                let uu____1468 = arg "symbol" in
                FStar_All.pipe_right uu____1468 js_str in
              let uu____1469 =
                let uu____1474 =
                  let uu____1479 = try_arg "location" in
                  FStar_All.pipe_right uu____1479
                    (FStar_Util.map_option js_assoc) in
                FStar_All.pipe_right uu____1474
                  (FStar_Util.map_option
                     (fun loc  ->
                        let uu____1507 =
                          let uu____1508 = assoc1 "[location]" "filename" loc in
                          FStar_All.pipe_right uu____1508 js_str in
                        let uu____1509 =
                          let uu____1510 = assoc1 "[location]" "line" loc in
                          FStar_All.pipe_right uu____1510 js_int in
                        let uu____1511 =
                          let uu____1512 = assoc1 "[location]" "column" loc in
                          FStar_All.pipe_right uu____1512 js_int in
                        (uu____1507, uu____1509, uu____1511))) in
              let uu____1513 =
                let uu____1515 = arg "requested-info" in
                FStar_All.pipe_right uu____1515 (js_list js_str) in
              (uu____1467, uu____1469, uu____1513) in
            Lookup uu____1458
        | "compute" ->
            let uu____1522 =
              let uu____1527 =
                let uu____1528 = arg "term" in
                FStar_All.pipe_right uu____1528 js_str in
              let uu____1529 =
                let uu____1532 = try_arg "rules" in
                FStar_All.pipe_right uu____1532
                  (FStar_Util.map_option (js_list js_reductionrule)) in
              (uu____1527, uu____1529) in
            Compute uu____1522
        | "search" ->
            let uu____1540 =
              let uu____1541 = arg "terms" in
              FStar_All.pipe_right uu____1541 js_str in
            Search uu____1540
        | uu____1542 ->
            let uu____1543 = FStar_Util.format1 "Unknown query '%s'" query in
            ProtocolViolation uu____1543 in
      { qq = uu____1441; qid }
    with | InvalidQuery msg -> { qq = (ProtocolViolation msg); qid }
    | UnexpectedJsonType (expected,got) -> wrap_js_failure qid expected got
let validate_interactive_query: query -> query =
  fun uu___204_1550  ->
    match uu___204_1550 with
    | { qq = Push (SyntaxCheck ,uu____1551,uu____1552,uu____1553,false );
        qid;_} ->
        {
          qq =
            (ProtocolViolation
               "Cannot use 'kind': 'syntax' with 'query': 'push'");
          qid
        }
    | other -> other
let read_interactive_query: FStar_Util.stream_reader -> query =
  fun stream  ->
    try
      let uu____1560 = FStar_Util.read_line stream in
      match uu____1560 with
      | None  -> FStar_All.exit (Prims.parse_int "0")
      | Some line ->
          let uu____1563 = FStar_Util.json_of_string line in
          (match uu____1563 with
           | None  ->
               { qq = (ProtocolViolation "Json parsing failed."); qid = "?" }
           | Some request ->
               let uu____1566 = unpack_interactive_query request in
               validate_interactive_query uu____1566)
    with | InvalidQuery msg -> { qq = (ProtocolViolation msg); qid = "?" }
    | UnexpectedJsonType (expected,got) -> wrap_js_failure "?" expected got
let rec json_of_fstar_option: FStar_Options.option_val -> FStar_Util.json =
  fun uu___205_1573  ->
    match uu___205_1573 with
    | FStar_Options.Bool b -> FStar_Util.JsonBool b
    | FStar_Options.String s|FStar_Options.Path s -> FStar_Util.JsonStr s
    | FStar_Options.Int n1 -> FStar_Util.JsonInt n1
    | FStar_Options.List vs ->
        let uu____1579 = FStar_List.map json_of_fstar_option vs in
        FStar_Util.JsonList uu____1579
    | FStar_Options.Unset  -> FStar_Util.JsonNull
let json_of_opt json_of_a opt_a =
  let uu____1600 = FStar_Util.map_option json_of_a opt_a in
  FStar_Util.dflt FStar_Util.JsonNull uu____1600
let json_of_pos: FStar_Range.pos -> FStar_Util.json =
  fun pos  ->
    let uu____1605 =
      let uu____1607 =
        let uu____1608 = FStar_Range.line_of_pos pos in
        FStar_Util.JsonInt uu____1608 in
      let uu____1609 =
        let uu____1611 =
          let uu____1612 = FStar_Range.col_of_pos pos in
          FStar_Util.JsonInt uu____1612 in
        [uu____1611] in
      uu____1607 :: uu____1609 in
    FStar_Util.JsonList uu____1605
let json_of_range_fields:
  Prims.string -> FStar_Range.pos -> FStar_Range.pos -> FStar_Util.json =
  fun file  ->
    fun b  ->
      fun e  ->
        let uu____1622 =
          let uu____1626 =
            let uu____1630 =
              let uu____1633 = json_of_pos b in ("beg", uu____1633) in
            let uu____1634 =
              let uu____1638 =
                let uu____1641 = json_of_pos e in ("end", uu____1641) in
              [uu____1638] in
            uu____1630 :: uu____1634 in
          ("fname", (FStar_Util.JsonStr file)) :: uu____1626 in
        FStar_Util.JsonAssoc uu____1622
let json_of_use_range: FStar_Range.range -> FStar_Util.json =
  fun r  ->
    let uu____1653 = FStar_Range.file_of_use_range r in
    let uu____1654 = FStar_Range.start_of_use_range r in
    let uu____1655 = FStar_Range.end_of_use_range r in
    json_of_range_fields uu____1653 uu____1654 uu____1655
let json_of_def_range: FStar_Range.range -> FStar_Util.json =
  fun r  ->
    let uu____1659 = FStar_Range.file_of_range r in
    let uu____1660 = FStar_Range.start_of_range r in
    let uu____1661 = FStar_Range.end_of_range r in
    json_of_range_fields uu____1659 uu____1660 uu____1661
let json_of_issue_level: FStar_Errors.issue_level -> FStar_Util.json =
  fun i  ->
    FStar_Util.JsonStr
      (match i with
       | FStar_Errors.ENotImplemented  -> "not-implemented"
       | FStar_Errors.EInfo  -> "info"
       | FStar_Errors.EWarning  -> "warning"
       | FStar_Errors.EError  -> "error")
let json_of_issue: FStar_Errors.issue -> FStar_Util.json =
  fun issue  ->
    let uu____1668 =
      let uu____1672 =
        let uu____1676 =
          let uu____1680 =
            let uu____1683 =
              let uu____1684 =
                let uu____1686 =
                  match issue.FStar_Errors.issue_range with
                  | None  -> []
                  | Some r ->
                      let uu____1690 = json_of_use_range r in [uu____1690] in
                let uu____1691 =
                  match issue.FStar_Errors.issue_range with
                  | Some r when
                      r.FStar_Range.def_range <> r.FStar_Range.use_range ->
                      let uu____1695 = json_of_def_range r in [uu____1695]
                  | uu____1696 -> [] in
                FStar_List.append uu____1686 uu____1691 in
              FStar_Util.JsonList uu____1684 in
            ("ranges", uu____1683) in
          [uu____1680] in
        ("message", (FStar_Util.JsonStr (issue.FStar_Errors.issue_message)))
          :: uu____1676 in
      ("level", (json_of_issue_level issue.FStar_Errors.issue_level)) ::
        uu____1672 in
    FStar_Util.JsonAssoc uu____1668
type lookup_result =
  {
  lr_name: Prims.string;
  lr_def_range: FStar_Range.range option;
  lr_typ: Prims.string option;
  lr_doc: Prims.string option;
  lr_def: Prims.string option;}
let json_of_lookup_result: lookup_result -> FStar_Util.json =
  fun lr  ->
    let uu____1756 =
      let uu____1760 =
        let uu____1764 =
          let uu____1767 = json_of_opt json_of_def_range lr.lr_def_range in
          ("defined-at", uu____1767) in
        let uu____1768 =
          let uu____1772 =
            let uu____1775 =
              json_of_opt (fun _0_33  -> FStar_Util.JsonStr _0_33) lr.lr_typ in
            ("type", uu____1775) in
          let uu____1776 =
            let uu____1780 =
              let uu____1783 =
                json_of_opt (fun _0_34  -> FStar_Util.JsonStr _0_34)
                  lr.lr_doc in
              ("documentation", uu____1783) in
            let uu____1784 =
              let uu____1788 =
                let uu____1791 =
                  json_of_opt (fun _0_35  -> FStar_Util.JsonStr _0_35)
                    lr.lr_def in
                ("definition", uu____1791) in
              [uu____1788] in
            uu____1780 :: uu____1784 in
          uu____1772 :: uu____1776 in
        uu____1764 :: uu____1768 in
      ("name", (FStar_Util.JsonStr (lr.lr_name))) :: uu____1760 in
    FStar_Util.JsonAssoc uu____1756
let json_of_protocol_info: (Prims.string* FStar_Util.json) Prims.list =
  let js_version = FStar_Util.JsonInt interactive_protocol_vernum in
  let js_features =
    let uu____1809 =
      FStar_List.map (fun _0_36  -> FStar_Util.JsonStr _0_36)
        interactive_protocol_features in
    FStar_All.pipe_left (fun _0_37  -> FStar_Util.JsonList _0_37) uu____1809 in
  [("version", js_version); ("features", js_features)]
let write_json: FStar_Util.json -> Prims.unit =
  fun json  ->
    (let uu____1822 = FStar_Util.string_of_json json in
     FStar_Util.print_raw uu____1822);
    FStar_Util.print_raw "\n"
let write_response:
  Prims.string -> query_status -> FStar_Util.json -> Prims.unit =
  fun qid  ->
    fun status  ->
      fun response  ->
        let qid1 = FStar_Util.JsonStr qid in
        let status1 =
          match status with
          | QueryOK  -> FStar_Util.JsonStr "success"
          | QueryNOK  -> FStar_Util.JsonStr "failure"
          | QueryViolatesProtocol  -> FStar_Util.JsonStr "protocol-violation" in
        write_json
          (FStar_Util.JsonAssoc
             [("kind", (FStar_Util.JsonStr "response"));
             ("query-id", qid1);
             ("status", status1);
             ("response", response)])
let write_message: Prims.string -> Prims.string -> Prims.unit =
  fun level  ->
    fun contents  ->
      write_json
        (FStar_Util.JsonAssoc
           [("kind", (FStar_Util.JsonStr "message"));
           ("level", (FStar_Util.JsonStr level));
           ("contents", (FStar_Util.JsonStr contents))])
let write_hello: Prims.unit -> Prims.unit =
  fun uu____1860  ->
    let js_version = FStar_Util.JsonInt interactive_protocol_vernum in
    let js_features =
      let uu____1863 =
        FStar_List.map (fun _0_38  -> FStar_Util.JsonStr _0_38)
          interactive_protocol_features in
      FStar_Util.JsonList uu____1863 in
    write_json
      (FStar_Util.JsonAssoc (("kind", (FStar_Util.JsonStr "protocol-info"))
         :: json_of_protocol_info))
type repl_state =
  {
  repl_line: Prims.int;
  repl_column: Prims.int;
  repl_fname: Prims.string;
  repl_stack: stack_t;
  repl_curmod: modul_t;
  repl_env: env_t;
  repl_ts: m_timestamps;
  repl_stdin: FStar_Util.stream_reader;}
let json_of_repl_state:
  repl_state -> (Prims.string* FStar_Util.json) Prims.list =
  fun st  ->
    let opts_and_defaults =
      let opt_docs =
        let uu____1938 = FStar_Options.docs () in
        FStar_Util.smap_of_list uu____1938 in
      let get_doc k = FStar_Util.smap_try_find opt_docs k in
      FStar_List.map
        (fun uu____1954  ->
           match uu____1954 with
           | (k,v1) ->
               let uu____1964 = FStar_Options.get_option k in
               let uu____1965 = get_doc k in (k, uu____1964, uu____1965, v1))
        FStar_Options.defaults in
    let uu____1968 =
      let uu____1971 =
        let uu____1972 =
          FStar_List.map
            (fun uu____1980  ->
               match uu____1980 with
               | (uu____1987,fstname,uu____1989,uu____1990) ->
                   FStar_Util.JsonStr fstname) st.repl_ts in
        FStar_Util.JsonList uu____1972 in
      ("loaded-dependencies", uu____1971) in
    let uu____1995 =
      let uu____1999 =
        let uu____2002 =
          let uu____2003 =
            FStar_List.map
              (fun uu____2010  ->
                 match uu____2010 with
                 | (name,value,doc1,dflt1) ->
                     let uu____2022 =
                       let uu____2026 =
                         let uu____2030 =
                           let uu____2033 = json_of_fstar_option value in
                           ("value", uu____2033) in
                         let uu____2034 =
                           let uu____2038 =
                             let uu____2041 = json_of_fstar_option dflt1 in
                             ("default", uu____2041) in
                           let uu____2042 =
                             let uu____2046 =
                               let uu____2049 =
                                 json_of_opt
                                   (fun _0_39  -> FStar_Util.JsonStr _0_39)
                                   doc1 in
                               ("documentation", uu____2049) in
                             [uu____2046] in
                           uu____2038 :: uu____2042 in
                         uu____2030 :: uu____2034 in
                       ("name", (FStar_Util.JsonStr name)) :: uu____2026 in
                     FStar_Util.JsonAssoc uu____2022) opts_and_defaults in
          FStar_Util.JsonList uu____2003 in
        ("options", uu____2002) in
      [uu____1999] in
    uu____1968 :: uu____1995
let run_exit st =
  ((QueryOK, FStar_Util.JsonNull), (FStar_Util.Inr (Prims.parse_int "0")))
let run_describe_protocol st =
  ((QueryOK, (FStar_Util.JsonAssoc json_of_protocol_info)),
    (FStar_Util.Inl st))
let run_describe_repl st =
  let uu____2117 =
    let uu____2120 =
      let uu____2121 = json_of_repl_state st in
      FStar_Util.JsonAssoc uu____2121 in
    (QueryOK, uu____2120) in
  (uu____2117, (FStar_Util.Inl st))
let run_protocol_violation st message =
  ((QueryViolatesProtocol, (FStar_Util.JsonStr message)),
    (FStar_Util.Inl st))
let run_pop st =
  match st.repl_stack with
  | [] ->
      ((QueryNOK, (FStar_Util.JsonStr "Too many pops")), (FStar_Util.Inl st))
  | (env,curmod)::stack ->
      (pop st.repl_env "#pop";
       if (FStar_List.length stack) = (FStar_List.length st.repl_ts)
       then cleanup env
       else ();
       ((QueryOK, FStar_Util.JsonNull),
         (FStar_Util.Inl
            ((let uu___216_2199 = st in
              {
                repl_line = (uu___216_2199.repl_line);
                repl_column = (uu___216_2199.repl_column);
                repl_fname = (uu___216_2199.repl_fname);
                repl_stack = stack;
                repl_curmod = curmod;
                repl_env = env;
                repl_ts = (uu___216_2199.repl_ts);
                repl_stdin = (uu___216_2199.repl_stdin)
              })))))
let run_push st kind text1 line column1 peek_only =
  let uu____2238 = ((st.repl_stack), (st.repl_env), (st.repl_ts)) in
  match uu____2238 with
  | (stack,env,ts) ->
      let uu____2251 =
        if (FStar_List.length stack) = (FStar_List.length ts)
        then
          let uu____2274 =
            update_deps st.repl_fname st.repl_curmod stack env ts in
          (true, uu____2274)
        else (false, (stack, env, ts)) in
      (match uu____2251 with
       | (restore_cmd_line_options1,(stack1,env1,ts1)) ->
           let stack2 = (env1, (st.repl_curmod)) :: stack1 in
           let env2 = push env1 kind restore_cmd_line_options1 "#push" in
           let env_mark = mark env2 in
           let frag =
             {
               FStar_Parser_ParseIt.frag_text = text1;
               FStar_Parser_ParseIt.frag_line = line;
               FStar_Parser_ParseIt.frag_col = column1
             } in
           let res = check_frag env_mark st.repl_curmod (frag, false) in
           let errors =
             let uu____2321 = FStar_Errors.report_all () in
             FStar_All.pipe_right uu____2321 (FStar_List.map json_of_issue) in
           (FStar_Errors.clear ();
            (let st' =
               let uu___217_2327 = st in
               {
                 repl_line = line;
                 repl_column = column1;
                 repl_fname = (uu___217_2327.repl_fname);
                 repl_stack = stack2;
                 repl_curmod = (uu___217_2327.repl_curmod);
                 repl_env = (uu___217_2327.repl_env);
                 repl_ts = ts1;
                 repl_stdin = (uu___217_2327.repl_stdin)
               } in
             match res with
             | Some (curmod,env3,nerrs) when
                 (nerrs = (Prims.parse_int "0")) && (peek_only = false) ->
                 let env4 = commit_mark env3 in
                 ((QueryOK, (FStar_Util.JsonList errors)),
                   (FStar_Util.Inl
                      (let uu___218_2356 = st' in
                       {
                         repl_line = (uu___218_2356.repl_line);
                         repl_column = (uu___218_2356.repl_column);
                         repl_fname = (uu___218_2356.repl_fname);
                         repl_stack = (uu___218_2356.repl_stack);
                         repl_curmod = curmod;
                         repl_env = env4;
                         repl_ts = (uu___218_2356.repl_ts);
                         repl_stdin = (uu___218_2356.repl_stdin)
                       })))
             | uu____2357 ->
                 let env3 = reset_mark env_mark in
                 let uu____2368 =
                   run_pop
                     (let uu___219_2375 = st' in
                      {
                        repl_line = (uu___219_2375.repl_line);
                        repl_column = (uu___219_2375.repl_column);
                        repl_fname = (uu___219_2375.repl_fname);
                        repl_stack = (uu___219_2375.repl_stack);
                        repl_curmod = (uu___219_2375.repl_curmod);
                        repl_env = env3;
                        repl_ts = (uu___219_2375.repl_ts);
                        repl_stdin = (uu___219_2375.repl_stdin)
                      }) in
                 (match uu____2368 with
                  | (uu____2382,st'') ->
                      let status = if peek_only then QueryOK else QueryNOK in
                      ((status, (FStar_Util.JsonList errors)), st'')))))
let run_lookup st symbol pos_opt requested_info =
  let uu____2436 = st.repl_env in
  match uu____2436 with
  | (dsenv,tcenv) ->
      let info_of_lid_str lid_str =
        let lid =
          let uu____2456 =
            FStar_List.map FStar_Ident.id_of_text
              (FStar_Util.split lid_str ".") in
          FStar_Ident.lid_of_ids uu____2456 in
        let lid1 =
          let uu____2459 =
            FStar_ToSyntax_Env.resolve_to_fully_qualified_name dsenv lid in
          FStar_All.pipe_left (FStar_Util.dflt lid) uu____2459 in
        let uu____2462 = FStar_TypeChecker_Env.try_lookup_lid tcenv lid1 in
        FStar_All.pipe_right uu____2462
          (FStar_Util.map_option
             (fun uu____2488  ->
                match uu____2488 with
                | ((uu____2498,typ),r) -> ((FStar_Util.Inr lid1), typ, r))) in
      let docs_of_lid lid =
        let uu____2510 = FStar_ToSyntax_Env.try_lookup_doc dsenv lid in
        FStar_All.pipe_right uu____2510
          (FStar_Util.map_option FStar_Pervasives.fst) in
      let def_of_lid lid =
        let uu____2527 = FStar_TypeChecker_Env.lookup_qname tcenv lid in
        FStar_Util.bind_opt uu____2527
          (fun uu___206_2547  ->
             match uu___206_2547 with
             | (FStar_Util.Inr (se,uu____2559),uu____2560) ->
                 let uu____2575 = FStar_Syntax_Print.sigelt_to_string se in
                 Some uu____2575
             | uu____2576 -> None) in
      let info_at_pos_opt =
        FStar_Util.bind_opt pos_opt
          (fun uu____2601  ->
             match uu____2601 with
             | (file,row,col) ->
                 FStar_TypeChecker_Err.info_at_pos tcenv file row col) in
      let info_opt =
        match info_at_pos_opt with
        | Some uu____2627 -> info_at_pos_opt
        | None  -> if symbol = "" then None else info_of_lid_str symbol in
      let response =
        match info_opt with
        | None  -> (QueryNOK, FStar_Util.JsonNull)
        | Some (name_or_lid,typ,rng) ->
            let name =
              match name_or_lid with
              | FStar_Util.Inl name -> name
              | FStar_Util.Inr lid -> FStar_Ident.string_of_lid lid in
            let typ_str =
              if FStar_List.mem "type" requested_info
              then
                let uu____2683 =
                  FStar_TypeChecker_Normalize.term_to_string tcenv typ in
                Some uu____2683
              else None in
            let doc_str =
              match name_or_lid with
              | FStar_Util.Inr lid when
                  FStar_List.mem "documentation" requested_info ->
                  docs_of_lid lid
              | uu____2689 -> None in
            let def_str =
              match name_or_lid with
              | FStar_Util.Inr lid when
                  FStar_List.mem "definition" requested_info ->
                  def_of_lid lid
              | uu____2696 -> None in
            let def_range =
              if FStar_List.mem "defined-at" requested_info
              then Some rng
              else None in
            let result =
              {
                lr_name = name;
                lr_def_range = def_range;
                lr_typ = typ_str;
                lr_doc = doc_str;
                lr_def = def_str
              } in
            let uu____2704 = json_of_lookup_result result in
            (QueryOK, uu____2704) in
      (response, (FStar_Util.Inl st))
let run_completions st search_term =
  let uu____2727 = st.repl_env in
  match uu____2727 with
  | (dsenv,tcenv) ->
      let rec measure_anchored_match search_term1 candidate =
        match (search_term1, candidate) with
        | ([],uu____2757) -> Some ([], (Prims.parse_int "0"))
        | (uu____2765,[]) -> None
        | (hs::ts,hc::tc) ->
            let hc_text = FStar_Ident.text_of_id hc in
            if FStar_Util.starts_with hc_text hs
            then
              (match ts with
               | [] -> Some (candidate, (FStar_String.length hs))
               | uu____2795 ->
                   let uu____2797 = measure_anchored_match ts tc in
                   FStar_All.pipe_right uu____2797
                     (FStar_Util.map_option
                        (fun uu____2816  ->
                           match uu____2816 with
                           | (matched,len) ->
                               ((hc :: matched),
                                 (((FStar_String.length hc_text) +
                                     (Prims.parse_int "1"))
                                    + len)))))
            else None in
      let rec locate_match needle candidate =
        let uu____2852 = measure_anchored_match needle candidate in
        match uu____2852 with
        | Some (matched,n1) -> Some ([], matched, n1)
        | None  ->
            (match candidate with
             | [] -> None
             | hc::tc ->
                 let uu____2894 = locate_match needle tc in
                 FStar_All.pipe_right uu____2894
                   (FStar_Util.map_option
                      (fun uu____2923  ->
                         match uu____2923 with
                         | (prefix1,matched,len) ->
                             ((hc :: prefix1), matched, len)))) in
      let str_of_ids ids =
        let uu____2949 = FStar_List.map FStar_Ident.text_of_id ids in
        FStar_Util.concat_l "." uu____2949 in
      let match_lident_against needle lident =
        locate_match needle
          (FStar_List.append lident.FStar_Ident.ns [lident.FStar_Ident.ident]) in
      let shorten_namespace uu____2978 =
        match uu____2978 with
        | (prefix1,matched,match_len) ->
            let naked_match =
              match matched with
              | uu____2996::[] -> true
              | uu____2997 -> false in
            let uu____2999 =
              FStar_ToSyntax_Env.shorten_module_path dsenv prefix1
                naked_match in
            (match uu____2999 with
             | (stripped_ns,shortened) ->
                 let uu____3014 = str_of_ids shortened in
                 let uu____3015 = str_of_ids matched in
                 let uu____3016 = str_of_ids stripped_ns in
                 (uu____3014, uu____3015, uu____3016, match_len)) in
      let prepare_candidate uu____3027 =
        match uu____3027 with
        | (prefix1,matched,stripped_ns,match_len) ->
            if prefix1 = ""
            then (matched, stripped_ns, match_len)
            else
              ((Prims.strcat prefix1 (Prims.strcat "." matched)),
                stripped_ns,
                (((FStar_String.length prefix1) + match_len) +
                   (Prims.parse_int "1"))) in
      let needle = FStar_Util.split search_term "." in
      let all_lidents_in_env = FStar_TypeChecker_Env.lidents tcenv in
      let matches =
        let case_a_find_transitive_includes orig_ns m id =
          let exported_names =
            FStar_ToSyntax_Env.transitive_exported_ids dsenv m in
          let matched_length =
            FStar_List.fold_left
              (fun out  ->
                 fun s  ->
                   ((FStar_String.length s) + out) + (Prims.parse_int "1"))
              (FStar_String.length id) orig_ns in
          FStar_All.pipe_right exported_names
            (FStar_List.filter_map
               (fun n1  ->
                  if FStar_Util.starts_with n1 id
                  then
                    let lid =
                      FStar_Ident.lid_of_ns_and_id (FStar_Ident.ids_of_lid m)
                        (FStar_Ident.id_of_text n1) in
                    let uu____3109 =
                      FStar_ToSyntax_Env.resolve_to_fully_qualified_name
                        dsenv lid in
                    FStar_Option.map
                      (fun fqn  ->
                         let uu____3117 =
                           let uu____3119 =
                             FStar_List.map FStar_Ident.id_of_text orig_ns in
                           FStar_List.append uu____3119
                             [fqn.FStar_Ident.ident] in
                         ([], uu____3117, matched_length)) uu____3109
                  else None)) in
        let case_b_find_matches_in_env uu____3138 =
          let matches =
            FStar_List.filter_map (match_lident_against needle)
              all_lidents_in_env in
          FStar_All.pipe_right matches
            (FStar_List.filter
               (fun uu____3174  ->
                  match uu____3174 with
                  | (ns,id,uu____3182) ->
                      let uu____3187 =
                        let uu____3189 = FStar_Ident.lid_of_ids id in
                        FStar_ToSyntax_Env.resolve_to_fully_qualified_name
                          dsenv uu____3189 in
                      (match uu____3187 with
                       | None  -> false
                       | Some l ->
                           let uu____3191 =
                             FStar_Ident.lid_of_ids (FStar_List.append ns id) in
                           FStar_Ident.lid_equals l uu____3191))) in
        let uu____3192 = FStar_Util.prefix needle in
        match uu____3192 with
        | (ns,id) ->
            let matched_ids =
              match ns with
              | [] -> case_b_find_matches_in_env ()
              | uu____3217 ->
                  let l = FStar_Ident.lid_of_path ns FStar_Range.dummyRange in
                  let uu____3220 =
                    FStar_ToSyntax_Env.resolve_module_name dsenv l true in
                  (match uu____3220 with
                   | None  -> case_b_find_matches_in_env ()
                   | Some m -> case_a_find_transitive_includes ns m id) in
            FStar_All.pipe_right matched_ids
              (FStar_List.map
                 (fun x  ->
                    let uu____3253 = shorten_namespace x in
                    prepare_candidate uu____3253)) in
      let json_candidates =
        let uu____3260 =
          FStar_Util.sort_with
            (fun uu____3268  ->
               fun uu____3269  ->
                 match (uu____3268, uu____3269) with
                 | ((cd1,ns1,uu____3284),(cd2,ns2,uu____3287)) ->
                     (match FStar_String.compare cd1 cd2 with
                      | _0_40 when _0_40 = (Prims.parse_int "0") ->
                          FStar_String.compare ns1 ns2
                      | n1 -> n1)) matches in
        FStar_List.map
          (fun uu____3298  ->
             match uu____3298 with
             | (candidate,ns,match_len) ->
                 FStar_Util.JsonList
                   [FStar_Util.JsonInt match_len;
                   FStar_Util.JsonStr ns;
                   FStar_Util.JsonStr candidate]) uu____3260 in
      ((QueryOK, (FStar_Util.JsonList json_candidates)), (FStar_Util.Inl st))
let run_compute st term rules =
  let run_and_rewind st1 task =
    let env_mark = mark st1.repl_env in
    let results = task st1 in
    let env = reset_mark env_mark in
    let st' =
      let uu___220_3368 = st1 in
      {
        repl_line = (uu___220_3368.repl_line);
        repl_column = (uu___220_3368.repl_column);
        repl_fname = (uu___220_3368.repl_fname);
        repl_stack = (uu___220_3368.repl_stack);
        repl_curmod = (uu___220_3368.repl_curmod);
        repl_env = env;
        repl_ts = (uu___220_3368.repl_ts);
        repl_stdin = (uu___220_3368.repl_stdin)
      } in
    (results, (FStar_Util.Inl st')) in
  let dummy_let_fragment term1 =
    let dummy_decl = FStar_Util.format1 "let __compute_dummy__ = (%s)" term1 in
    {
      FStar_Parser_ParseIt.frag_text = dummy_decl;
      FStar_Parser_ParseIt.frag_line = (Prims.parse_int "0");
      FStar_Parser_ParseIt.frag_col = (Prims.parse_int "0")
    } in
  let normalize_term1 tcenv rules1 t =
    FStar_TypeChecker_Normalize.normalize rules1 tcenv t in
  let find_let_body ses =
    match ses with
    | {
        FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let
          ((uu____3400,{ FStar_Syntax_Syntax.lbname = uu____3401;
                         FStar_Syntax_Syntax.lbunivs = uu____3402;
                         FStar_Syntax_Syntax.lbtyp = uu____3403;
                         FStar_Syntax_Syntax.lbeff = uu____3404;
                         FStar_Syntax_Syntax.lbdef = def;_}::[]),uu____3406,uu____3407);
        FStar_Syntax_Syntax.sigrng = uu____3408;
        FStar_Syntax_Syntax.sigquals = uu____3409;
        FStar_Syntax_Syntax.sigmeta = uu____3410;_}::[] -> Some def
    | uu____3429 -> None in
  let parse1 frag =
    let uu____3439 = FStar_Parser_ParseIt.parse (FStar_Util.Inr frag) in
    match uu____3439 with
    | FStar_Util.Inl (FStar_Util.Inr decls,uu____3452) -> Some decls
    | uu____3475 -> None in
  let desugar dsenv decls =
    let uu____3495 = FStar_ToSyntax_ToSyntax.desugar_decls dsenv decls in
    snd uu____3495 in
  let typecheck tcenv decls =
    let uu____3508 = FStar_TypeChecker_Tc.tc_decls tcenv decls in
    match uu____3508 with | (ses,uu____3516,uu____3517) -> ses in
  let rules1 =
    FStar_List.append
      (match rules with
       | Some rules1 -> rules1
       | None  ->
           [FStar_TypeChecker_Normalize.Beta;
           FStar_TypeChecker_Normalize.Iota;
           FStar_TypeChecker_Normalize.Zeta;
           FStar_TypeChecker_Normalize.UnfoldUntil
             FStar_Syntax_Syntax.Delta_constant])
      [FStar_TypeChecker_Normalize.Inlining;
      FStar_TypeChecker_Normalize.Eager_unfolding;
      FStar_TypeChecker_Normalize.Primops] in
  run_and_rewind st
    (fun st1  ->
       let uu____3530 = st1.repl_env in
       match uu____3530 with
       | (dsenv,tcenv) ->
           let frag = dummy_let_fragment term in
           (match st1.repl_curmod with
            | None  ->
                (QueryNOK, (FStar_Util.JsonStr "Current module unset"))
            | uu____3538 ->
                let uu____3539 = parse1 frag in
                (match uu____3539 with
                 | None  ->
                     (QueryNOK,
                       (FStar_Util.JsonStr "Count not parse this term"))
                 | Some decls ->
                     (try
                        let decls1 = desugar dsenv decls in
                        let ses = typecheck tcenv decls1 in
                        match find_let_body ses with
                        | None  ->
                            (QueryNOK,
                              (FStar_Util.JsonStr
                                 "Typechecking yielded an unexpected term"))
                        | Some def ->
                            let normalized = normalize_term1 tcenv rules1 def in
                            let uu____3566 =
                              let uu____3567 =
                                FStar_Syntax_Print.term_to_string normalized in
                              FStar_Util.JsonStr uu____3567 in
                            (QueryOK, uu____3566)
                      with
                      | e ->
                          let uu____3572 =
                            let uu____3573 = FStar_Errors.issue_of_exn e in
                            match uu____3573 with
                            | Some issue ->
                                let uu____3576 =
                                  FStar_Errors.format_issue issue in
                                FStar_Util.JsonStr uu____3576
                            | None  -> raise e in
                          (QueryNOK, uu____3572)))))
type search_term' =
  | NameContainsStr of Prims.string
  | TypeContainsLid of FStar_Ident.lid
and search_term = {
  st_negate: Prims.bool;
  st_term: search_term';}
let uu___is_NameContainsStr: search_term' -> Prims.bool =
  fun projectee  ->
    match projectee with | NameContainsStr _0 -> true | uu____3593 -> false
let __proj__NameContainsStr__item___0: search_term' -> Prims.string =
  fun projectee  -> match projectee with | NameContainsStr _0 -> _0
let uu___is_TypeContainsLid: search_term' -> Prims.bool =
  fun projectee  ->
    match projectee with | TypeContainsLid _0 -> true | uu____3605 -> false
let __proj__TypeContainsLid__item___0: search_term' -> FStar_Ident.lid =
  fun projectee  -> match projectee with | TypeContainsLid _0 -> _0
let st_cost: search_term' -> Prims.int =
  fun uu___207_3623  ->
    match uu___207_3623 with
    | NameContainsStr str -> - (FStar_String.length str)
    | TypeContainsLid lid -> Prims.parse_int "1"
type search_candidate =
  {
  sc_lid: FStar_Ident.lid;
  sc_typ: FStar_Syntax_Syntax.typ option FStar_ST.ref;
  sc_fvars: FStar_Ident.lid FStar_Util.set option FStar_ST.ref;}
let sc_of_lid: FStar_Ident.lid -> search_candidate =
  fun lid  ->
    let uu____3674 = FStar_Util.mk_ref None in
    let uu____3679 = FStar_Util.mk_ref None in
    { sc_lid = lid; sc_typ = uu____3674; sc_fvars = uu____3679 }
let sc_typ:
  FStar_TypeChecker_Env.env -> search_candidate -> FStar_Syntax_Syntax.typ =
  fun tcenv  ->
    fun sc  ->
      let uu____3697 = FStar_ST.read sc.sc_typ in
      match uu____3697 with
      | Some t -> t
      | None  ->
          let typ =
            let uu____3706 =
              FStar_TypeChecker_Env.try_lookup_lid tcenv sc.sc_lid in
            match uu____3706 with
            | None  ->
                FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown None
                  FStar_Range.dummyRange
            | Some ((uu____3722,typ),uu____3724) -> typ in
          (FStar_ST.write sc.sc_typ (Some typ); typ)
let sc_fvars:
  FStar_TypeChecker_Env.env ->
    search_candidate -> FStar_Ident.lid FStar_Util.set
  =
  fun tcenv  ->
    fun sc  ->
      let uu____3744 = FStar_ST.read sc.sc_fvars in
      match uu____3744 with
      | Some fv -> fv
      | None  ->
          let fv =
            let uu____3758 = sc_typ tcenv sc in
            FStar_Syntax_Free.fvars uu____3758 in
          (FStar_ST.write sc.sc_fvars (Some fv); fv)
let json_of_search_result:
  FStar_ToSyntax_Env.env ->
    FStar_TypeChecker_Env.env -> search_candidate -> FStar_Util.json
  =
  fun dsenv  ->
    fun tcenv  ->
      fun sc  ->
        let typ_str =
          let uu____3775 = sc_typ tcenv sc in
          FStar_Syntax_Print.term_to_string uu____3775 in
        let uu____3776 =
          let uu____3780 =
            let uu____3783 =
              let uu____3784 =
                let uu____3785 =
                  FStar_ToSyntax_Env.shorten_lid dsenv sc.sc_lid in
                uu____3785.FStar_Ident.str in
              FStar_Util.JsonStr uu____3784 in
            ("lid", uu____3783) in
          [uu____3780; ("type", (FStar_Util.JsonStr typ_str))] in
        FStar_Util.JsonAssoc uu____3776
exception InvalidSearch of Prims.string
let uu___is_InvalidSearch: Prims.exn -> Prims.bool =
  fun projectee  ->
    match projectee with
    | InvalidSearch uu____3797 -> true
    | uu____3798 -> false
let __proj__InvalidSearch__item__uu___: Prims.exn -> Prims.string =
  fun projectee  ->
    match projectee with | InvalidSearch uu____3805 -> uu____3805
let run_search st search_str =
  let uu____3824 = st.repl_env in
  match uu____3824 with
  | (dsenv,tcenv) ->
      let empty_fv_set = FStar_Syntax_Syntax.new_fv_set () in
      let st_matches candidate term =
        let found =
          match term.st_term with
          | NameContainsStr str ->
              FStar_Util.contains (candidate.sc_lid).FStar_Ident.str str
          | TypeContainsLid lid ->
              let uu____3845 = sc_fvars tcenv candidate in
              FStar_Util.set_mem lid uu____3845 in
        found <> term.st_negate in
      let parse1 search_str1 =
        let parse_one term =
          let negate = FStar_Util.starts_with term "-" in
          let term1 =
            if negate
            then FStar_Util.substring_from term (Prims.parse_int "1")
            else term in
          let beg_quote = FStar_Util.starts_with term1 "\"" in
          let end_quote = FStar_Util.ends_with term1 "\"" in
          let strip_quotes str =
            if (FStar_String.length str) < (Prims.parse_int "2")
            then raise (InvalidSearch "Empty search term")
            else
              FStar_Util.substring str (Prims.parse_int "1")
                ((FStar_String.length term1) - (Prims.parse_int "2")) in
          let parsed =
            if beg_quote <> end_quote
            then
              let uu____3873 =
                let uu____3874 =
                  FStar_Util.format1 "Improperly quoted search term: %s"
                    term1 in
                InvalidSearch uu____3874 in
              raise uu____3873
            else
              if beg_quote
              then
                (let uu____3876 = strip_quotes term1 in
                 NameContainsStr uu____3876)
              else
                (let lid = FStar_Ident.lid_of_str term1 in
                 let uu____3879 =
                   FStar_ToSyntax_Env.resolve_to_fully_qualified_name dsenv
                     lid in
                 match uu____3879 with
                 | None  ->
                     let uu____3881 =
                       let uu____3882 =
                         FStar_Util.format1 "Unknown identifier: %s" term1 in
                       InvalidSearch uu____3882 in
                     raise uu____3881
                 | Some lid1 -> TypeContainsLid lid1) in
          { st_negate = negate; st_term = parsed } in
        let terms =
          FStar_List.map parse_one (FStar_Util.split search_str1 " ") in
        let cmp x y = (st_cost x.st_term) - (st_cost y.st_term) in
        FStar_Util.sort_with cmp terms in
      let pprint_one term =
        let uu____3897 =
          match term.st_term with
          | NameContainsStr s -> FStar_Util.format1 "\"%s\"" s
          | TypeContainsLid l -> FStar_Util.format1 "%s" l.FStar_Ident.str in
        Prims.strcat (if term.st_negate then "-" else "") uu____3897 in
      let results =
        try
          let terms = parse1 search_str in
          let all_lidents = FStar_TypeChecker_Env.lidents tcenv in
          let all_candidates = FStar_List.map sc_of_lid all_lidents in
          let matches_all candidate =
            FStar_List.for_all (st_matches candidate) terms in
          let cmp r1 r2 =
            FStar_Util.compare (r1.sc_lid).FStar_Ident.str
              (r2.sc_lid).FStar_Ident.str in
          let results = FStar_List.filter matches_all all_candidates in
          let sorted1 = FStar_Util.sort_with cmp results in
          let js =
            FStar_Options.with_saved_options
              (fun uu____3933  ->
                 FStar_Options.set_option "print_effect_args"
                   (FStar_Options.Bool true);
                 FStar_List.map (json_of_search_result dsenv tcenv) sorted1) in
          match results with
          | [] ->
              let kwds =
                let uu____3938 = FStar_List.map pprint_one terms in
                FStar_Util.concat_l " " uu____3938 in
              let uu____3940 =
                let uu____3941 =
                  FStar_Util.format1 "No results found for query [%s]" kwds in
                InvalidSearch uu____3941 in
              raise uu____3940
          | uu____3944 -> (QueryOK, (FStar_Util.JsonList js))
        with | InvalidSearch s -> (QueryNOK, (FStar_Util.JsonStr s)) in
      (results, (FStar_Util.Inl st))
let run_query:
  repl_state ->
    query' ->
      ((query_status* FStar_Util.json)* (repl_state,Prims.int)
        FStar_Util.either)
  =
  fun st  ->
    fun uu___208_3973  ->
      match uu___208_3973 with
      | Exit  -> run_exit st
      | DescribeProtocol  -> run_describe_protocol st
      | DescribeRepl  -> run_describe_repl st
      | Pop  -> run_pop st
      | Push (kind,text1,l,c,peek) -> run_push st kind text1 l c peek
      | AutoComplete search_term -> run_completions st search_term
      | Lookup (symbol,pos_opt,rqi) -> run_lookup st symbol pos_opt rqi
      | Compute (term,rules) -> run_compute st term rules
      | Search term -> run_search st term
      | ProtocolViolation query -> run_protocol_violation st query
let rec go: repl_state -> Prims.unit =
  fun st  ->
    let query = read_interactive_query st.repl_stdin in
    let uu____4011 = let uu____4018 = run_query st in uu____4018 query.qq in
    match uu____4011 with
    | ((status,response),state_opt) ->
        (write_response query.qid status response;
         (match state_opt with
          | FStar_Util.Inl st' -> go st'
          | FStar_Util.Inr exitcode -> FStar_All.exit exitcode))
let interactive_error_handler: FStar_Errors.error_handler =
  let issues = FStar_Util.mk_ref [] in
  let add_one1 e =
    let uu____4048 = let uu____4050 = FStar_ST.read issues in e :: uu____4050 in
    FStar_ST.write issues uu____4048 in
  let count_errors uu____4061 =
    let uu____4062 =
      let uu____4064 = FStar_ST.read issues in
      FStar_List.filter
        (fun e  -> e.FStar_Errors.issue_level = FStar_Errors.EError)
        uu____4064 in
    FStar_List.length uu____4062 in
  let report1 uu____4075 =
    let uu____4076 = FStar_ST.read issues in
    FStar_List.sortWith FStar_Errors.compare_issues uu____4076 in
  let clear1 uu____4084 = FStar_ST.write issues [] in
  {
    FStar_Errors.eh_add_one = add_one1;
    FStar_Errors.eh_count_errors = count_errors;
    FStar_Errors.eh_report = report1;
    FStar_Errors.eh_clear = clear1
  }
let interactive_printer: FStar_Util.printer =
  {
    FStar_Util.printer_prinfo = (write_message "info");
    FStar_Util.printer_prwarning = (write_message "warning");
    FStar_Util.printer_prerror = (write_message "error")
  }
let interactive_mode': Prims.string -> Prims.unit =
  fun filename  ->
    write_hello ();
    (let uu____4094 = deps_of_our_file filename in
     match uu____4094 with
     | (filenames,maybe_intf) ->
         let env = tc_prims () in
         let uu____4108 = tc_deps None [] env filenames [] in
         (match uu____4108 with
          | (stack,env1,ts) ->
              let initial_range =
                let uu____4124 =
                  FStar_Range.mk_pos (Prims.parse_int "1")
                    (Prims.parse_int "0") in
                let uu____4125 =
                  FStar_Range.mk_pos (Prims.parse_int "1")
                    (Prims.parse_int "0") in
                FStar_Range.mk_range "<input>" uu____4124 uu____4125 in
              let env2 =
                let uu____4129 =
                  FStar_TypeChecker_Env.set_range (snd env1) initial_range in
                ((fst env1), uu____4129) in
              let env3 =
                match maybe_intf with
                | Some intf -> FStar_Universal.load_interface_decls env2 intf
                | None  -> env2 in
              let init_st =
                let uu____4137 = FStar_Util.open_stdin () in
                {
                  repl_line = (Prims.parse_int "1");
                  repl_column = (Prims.parse_int "0");
                  repl_fname = filename;
                  repl_stack = stack;
                  repl_curmod = None;
                  repl_env = env3;
                  repl_ts = ts;
                  repl_stdin = uu____4137
                } in
              let uu____4138 =
                (FStar_Options.record_hints ()) ||
                  (FStar_Options.use_hints ()) in
              if uu____4138
              then
                let uu____4139 =
                  let uu____4140 = FStar_Options.file_list () in
                  FStar_List.hd uu____4140 in
                FStar_SMTEncoding_Solver.with_hints_db uu____4139
                  (fun uu____4142  -> go init_st)
              else go init_st))
let interactive_mode: Prims.string -> Prims.unit =
  fun filename  ->
    FStar_Util.set_printer interactive_printer;
    FStar_Errors.set_handler interactive_error_handler;
    (let uu____4150 =
       let uu____4151 = FStar_Options.codegen () in
       FStar_Option.isSome uu____4151 in
     if uu____4150
     then
       FStar_Util.print_warning
         "code-generation is not supported in interactive mode, ignoring the codegen flag"
     else ());
    (try interactive_mode' filename
     with
     | e -> (FStar_Errors.set_handler FStar_Errors.default_handler; raise e))