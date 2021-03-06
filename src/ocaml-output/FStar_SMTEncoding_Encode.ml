open Prims
let add_fuel x tl1 =
  let uu____16 = FStar_Options.unthrottle_inductives () in
  if uu____16 then tl1 else x :: tl1
let withenv c uu____39 = match uu____39 with | (a,b) -> (a, b, c)
let vargs args =
  FStar_List.filter
    (fun uu___101_74  ->
       match uu___101_74 with
       | (FStar_Util.Inl uu____79,uu____80) -> false
       | uu____83 -> true) args
let subst_lcomp_opt s l =
  match l with
  | Some (FStar_Util.Inl l1) ->
      let uu____114 =
        let uu____117 =
          let uu____118 =
            let uu____121 = l1.FStar_Syntax_Syntax.comp () in
            FStar_Syntax_Subst.subst_comp s uu____121 in
          FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp uu____118 in
        FStar_Util.Inl uu____117 in
      Some uu____114
  | uu____126 -> l
let escape: Prims.string -> Prims.string =
  fun s  -> FStar_Util.replace_char s '\'' '_'
let mk_term_projector_name:
  FStar_Ident.lident -> FStar_Syntax_Syntax.bv -> Prims.string =
  fun lid  ->
    fun a  ->
      let a1 =
        let uu___126_140 = a in
        let uu____141 =
          FStar_Syntax_Util.unmangle_field_name a.FStar_Syntax_Syntax.ppname in
        {
          FStar_Syntax_Syntax.ppname = uu____141;
          FStar_Syntax_Syntax.index =
            (uu___126_140.FStar_Syntax_Syntax.index);
          FStar_Syntax_Syntax.sort = (uu___126_140.FStar_Syntax_Syntax.sort)
        } in
      let uu____142 =
        FStar_Util.format2 "%s_%s" lid.FStar_Ident.str
          (a1.FStar_Syntax_Syntax.ppname).FStar_Ident.idText in
      FStar_All.pipe_left escape uu____142
let primitive_projector_by_pos:
  FStar_TypeChecker_Env.env ->
    FStar_Ident.lident -> Prims.int -> Prims.string
  =
  fun env  ->
    fun lid  ->
      fun i  ->
        let fail uu____155 =
          let uu____156 =
            FStar_Util.format2
              "Projector %s on data constructor %s not found"
              (Prims.string_of_int i) lid.FStar_Ident.str in
          failwith uu____156 in
        let uu____157 = FStar_TypeChecker_Env.lookup_datacon env lid in
        match uu____157 with
        | (uu____160,t) ->
            let uu____162 =
              let uu____163 = FStar_Syntax_Subst.compress t in
              uu____163.FStar_Syntax_Syntax.n in
            (match uu____162 with
             | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                 let uu____178 = FStar_Syntax_Subst.open_comp bs c in
                 (match uu____178 with
                  | (binders,uu____182) ->
                      if
                        (i < (Prims.parse_int "0")) ||
                          (i >= (FStar_List.length binders))
                      then fail ()
                      else
                        (let b = FStar_List.nth binders i in
                         mk_term_projector_name lid (fst b)))
             | uu____193 -> fail ())
let mk_term_projector_name_by_pos:
  FStar_Ident.lident -> Prims.int -> Prims.string =
  fun lid  ->
    fun i  ->
      let uu____200 =
        FStar_Util.format2 "%s_%s" lid.FStar_Ident.str
          (Prims.string_of_int i) in
      FStar_All.pipe_left escape uu____200
let mk_term_projector:
  FStar_Ident.lident -> FStar_Syntax_Syntax.bv -> FStar_SMTEncoding_Term.term
  =
  fun lid  ->
    fun a  ->
      let uu____207 =
        let uu____210 = mk_term_projector_name lid a in
        (uu____210,
          (FStar_SMTEncoding_Term.Arrow
             (FStar_SMTEncoding_Term.Term_sort,
               FStar_SMTEncoding_Term.Term_sort))) in
      FStar_SMTEncoding_Util.mkFreeV uu____207
let mk_term_projector_by_pos:
  FStar_Ident.lident -> Prims.int -> FStar_SMTEncoding_Term.term =
  fun lid  ->
    fun i  ->
      let uu____217 =
        let uu____220 = mk_term_projector_name_by_pos lid i in
        (uu____220,
          (FStar_SMTEncoding_Term.Arrow
             (FStar_SMTEncoding_Term.Term_sort,
               FStar_SMTEncoding_Term.Term_sort))) in
      FStar_SMTEncoding_Util.mkFreeV uu____217
let mk_data_tester env l x =
  FStar_SMTEncoding_Term.mk_tester (escape l.FStar_Ident.str) x
type varops_t =
  {
  push: Prims.unit -> Prims.unit;
  pop: Prims.unit -> Prims.unit;
  mark: Prims.unit -> Prims.unit;
  reset_mark: Prims.unit -> Prims.unit;
  commit_mark: Prims.unit -> Prims.unit;
  new_var: FStar_Ident.ident -> Prims.int -> Prims.string;
  new_fvar: FStar_Ident.lident -> Prims.string;
  fresh: Prims.string -> Prims.string;
  string_const: Prims.string -> FStar_SMTEncoding_Term.term;
  next_id: Prims.unit -> Prims.int;
  mk_unique: Prims.string -> Prims.string;}
let varops: varops_t =
  let initial_ctr = Prims.parse_int "100" in
  let ctr = FStar_Util.mk_ref initial_ctr in
  let new_scope uu____433 =
    let uu____434 = FStar_Util.smap_create (Prims.parse_int "100") in
    let uu____436 = FStar_Util.smap_create (Prims.parse_int "100") in
    (uu____434, uu____436) in
  let scopes =
    let uu____447 = let uu____453 = new_scope () in [uu____453] in
    FStar_Util.mk_ref uu____447 in
  let mk_unique y =
    let y1 = escape y in
    let y2 =
      let uu____478 =
        let uu____480 = FStar_ST.read scopes in
        FStar_Util.find_map uu____480
          (fun uu____497  ->
             match uu____497 with
             | (names1,uu____504) -> FStar_Util.smap_try_find names1 y1) in
      match uu____478 with
      | None  -> y1
      | Some uu____509 ->
          (FStar_Util.incr ctr;
           (let uu____514 =
              let uu____515 =
                let uu____516 = FStar_ST.read ctr in
                Prims.string_of_int uu____516 in
              Prims.strcat "__" uu____515 in
            Prims.strcat y1 uu____514)) in
    let top_scope =
      let uu____521 =
        let uu____526 = FStar_ST.read scopes in FStar_List.hd uu____526 in
      FStar_All.pipe_left FStar_Pervasives.fst uu____521 in
    FStar_Util.smap_add top_scope y2 true; y2 in
  let new_var pp rn =
    FStar_All.pipe_left mk_unique
      (Prims.strcat pp.FStar_Ident.idText
         (Prims.strcat "__" (Prims.string_of_int rn))) in
  let new_fvar lid = mk_unique lid.FStar_Ident.str in
  let next_id1 uu____565 = FStar_Util.incr ctr; FStar_ST.read ctr in
  let fresh1 pfx =
    let uu____576 =
      let uu____577 = next_id1 () in
      FStar_All.pipe_left Prims.string_of_int uu____577 in
    FStar_Util.format2 "%s_%s" pfx uu____576 in
  let string_const s =
    let uu____582 =
      let uu____584 = FStar_ST.read scopes in
      FStar_Util.find_map uu____584
        (fun uu____601  ->
           match uu____601 with
           | (uu____607,strings) -> FStar_Util.smap_try_find strings s) in
    match uu____582 with
    | Some f -> f
    | None  ->
        let id = next_id1 () in
        let f =
          let uu____616 = FStar_SMTEncoding_Util.mk_String_const id in
          FStar_All.pipe_left FStar_SMTEncoding_Term.boxString uu____616 in
        let top_scope =
          let uu____619 =
            let uu____624 = FStar_ST.read scopes in FStar_List.hd uu____624 in
          FStar_All.pipe_left FStar_Pervasives.snd uu____619 in
        (FStar_Util.smap_add top_scope s f; f) in
  let push1 uu____652 =
    let uu____653 =
      let uu____659 = new_scope () in
      let uu____664 = FStar_ST.read scopes in uu____659 :: uu____664 in
    FStar_ST.write scopes uu____653 in
  let pop1 uu____691 =
    let uu____692 =
      let uu____698 = FStar_ST.read scopes in FStar_List.tl uu____698 in
    FStar_ST.write scopes uu____692 in
  let mark1 uu____725 = push1 () in
  let reset_mark1 uu____729 = pop1 () in
  let commit_mark1 uu____733 =
    let uu____734 = FStar_ST.read scopes in
    match uu____734 with
    | (hd1,hd2)::(next1,next2)::tl1 ->
        (FStar_Util.smap_fold hd1
           (fun key  ->
              fun value  -> fun v1  -> FStar_Util.smap_add next1 key value)
           ();
         FStar_Util.smap_fold hd2
           (fun key  ->
              fun value  -> fun v1  -> FStar_Util.smap_add next2 key value)
           ();
         FStar_ST.write scopes ((next1, next2) :: tl1))
    | uu____794 -> failwith "Impossible" in
  {
    push = push1;
    pop = pop1;
    mark = mark1;
    reset_mark = reset_mark1;
    commit_mark = commit_mark1;
    new_var;
    new_fvar;
    fresh = fresh1;
    string_const;
    next_id = next_id1;
    mk_unique
  }
let unmangle: FStar_Syntax_Syntax.bv -> FStar_Syntax_Syntax.bv =
  fun x  ->
    let uu___127_803 = x in
    let uu____804 =
      FStar_Syntax_Util.unmangle_field_name x.FStar_Syntax_Syntax.ppname in
    {
      FStar_Syntax_Syntax.ppname = uu____804;
      FStar_Syntax_Syntax.index = (uu___127_803.FStar_Syntax_Syntax.index);
      FStar_Syntax_Syntax.sort = (uu___127_803.FStar_Syntax_Syntax.sort)
    }
type binding =
  | Binding_var of (FStar_Syntax_Syntax.bv* FStar_SMTEncoding_Term.term)
  | Binding_fvar of (FStar_Ident.lident* Prims.string*
  FStar_SMTEncoding_Term.term option* FStar_SMTEncoding_Term.term option)
let uu___is_Binding_var: binding -> Prims.bool =
  fun projectee  ->
    match projectee with | Binding_var _0 -> true | uu____827 -> false
let __proj__Binding_var__item___0:
  binding -> (FStar_Syntax_Syntax.bv* FStar_SMTEncoding_Term.term) =
  fun projectee  -> match projectee with | Binding_var _0 -> _0
let uu___is_Binding_fvar: binding -> Prims.bool =
  fun projectee  ->
    match projectee with | Binding_fvar _0 -> true | uu____851 -> false
let __proj__Binding_fvar__item___0:
  binding ->
    (FStar_Ident.lident* Prims.string* FStar_SMTEncoding_Term.term option*
      FStar_SMTEncoding_Term.term option)
  = fun projectee  -> match projectee with | Binding_fvar _0 -> _0
let binder_of_eithervar v1 = (v1, None)
type cache_entry =
  {
  cache_symbol_name: Prims.string;
  cache_symbol_arg_sorts: FStar_SMTEncoding_Term.sort Prims.list;
  cache_symbol_decls: FStar_SMTEncoding_Term.decl Prims.list;
  cache_symbol_assumption_names: Prims.string Prims.list;}
type env_t =
  {
  bindings: binding Prims.list;
  depth: Prims.int;
  tcenv: FStar_TypeChecker_Env.env;
  warn: Prims.bool;
  cache: cache_entry FStar_Util.smap;
  nolabels: Prims.bool;
  use_zfuel_name: Prims.bool;
  encode_non_total_function_typ: Prims.bool;
  current_module_name: Prims.string;}
let mk_cache_entry env tsym cvar_sorts t_decls =
  let names1 =
    FStar_All.pipe_right t_decls
      (FStar_List.collect
         (fun uu___102_1039  ->
            match uu___102_1039 with
            | FStar_SMTEncoding_Term.Assume a ->
                [a.FStar_SMTEncoding_Term.assumption_name]
            | uu____1042 -> [])) in
  {
    cache_symbol_name = tsym;
    cache_symbol_arg_sorts = cvar_sorts;
    cache_symbol_decls = t_decls;
    cache_symbol_assumption_names = names1
  }
let use_cache_entry: cache_entry -> FStar_SMTEncoding_Term.decl Prims.list =
  fun ce  ->
    [FStar_SMTEncoding_Term.RetainAssumptions
       (ce.cache_symbol_assumption_names)]
let print_env: env_t -> Prims.string =
  fun e  ->
    let uu____1050 =
      FStar_All.pipe_right e.bindings
        (FStar_List.map
           (fun uu___103_1054  ->
              match uu___103_1054 with
              | Binding_var (x,uu____1056) ->
                  FStar_Syntax_Print.bv_to_string x
              | Binding_fvar (l,uu____1058,uu____1059,uu____1060) ->
                  FStar_Syntax_Print.lid_to_string l)) in
    FStar_All.pipe_right uu____1050 (FStar_String.concat ", ")
let lookup_binding env f = FStar_Util.find_map env.bindings f
let caption_t: env_t -> FStar_Syntax_Syntax.term -> Prims.string option =
  fun env  ->
    fun t  ->
      let uu____1093 =
        FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low in
      if uu____1093
      then
        let uu____1095 = FStar_Syntax_Print.term_to_string t in
        Some uu____1095
      else None
let fresh_fvar:
  Prims.string ->
    FStar_SMTEncoding_Term.sort ->
      (Prims.string* FStar_SMTEncoding_Term.term)
  =
  fun x  ->
    fun s  ->
      let xsym = varops.fresh x in
      let uu____1106 = FStar_SMTEncoding_Util.mkFreeV (xsym, s) in
      (xsym, uu____1106)
let gen_term_var:
  env_t ->
    FStar_Syntax_Syntax.bv ->
      (Prims.string* FStar_SMTEncoding_Term.term* env_t)
  =
  fun env  ->
    fun x  ->
      let ysym = Prims.strcat "@x" (Prims.string_of_int env.depth) in
      let y =
        FStar_SMTEncoding_Util.mkFreeV
          (ysym, FStar_SMTEncoding_Term.Term_sort) in
      (ysym, y,
        (let uu___128_1118 = env in
         {
           bindings = ((Binding_var (x, y)) :: (env.bindings));
           depth = (env.depth + (Prims.parse_int "1"));
           tcenv = (uu___128_1118.tcenv);
           warn = (uu___128_1118.warn);
           cache = (uu___128_1118.cache);
           nolabels = (uu___128_1118.nolabels);
           use_zfuel_name = (uu___128_1118.use_zfuel_name);
           encode_non_total_function_typ =
             (uu___128_1118.encode_non_total_function_typ);
           current_module_name = (uu___128_1118.current_module_name)
         }))
let new_term_constant:
  env_t ->
    FStar_Syntax_Syntax.bv ->
      (Prims.string* FStar_SMTEncoding_Term.term* env_t)
  =
  fun env  ->
    fun x  ->
      let ysym =
        varops.new_var x.FStar_Syntax_Syntax.ppname
          x.FStar_Syntax_Syntax.index in
      let y = FStar_SMTEncoding_Util.mkApp (ysym, []) in
      (ysym, y,
        (let uu___129_1131 = env in
         {
           bindings = ((Binding_var (x, y)) :: (env.bindings));
           depth = (uu___129_1131.depth);
           tcenv = (uu___129_1131.tcenv);
           warn = (uu___129_1131.warn);
           cache = (uu___129_1131.cache);
           nolabels = (uu___129_1131.nolabels);
           use_zfuel_name = (uu___129_1131.use_zfuel_name);
           encode_non_total_function_typ =
             (uu___129_1131.encode_non_total_function_typ);
           current_module_name = (uu___129_1131.current_module_name)
         }))
let new_term_constant_from_string:
  env_t ->
    FStar_Syntax_Syntax.bv ->
      Prims.string -> (Prims.string* FStar_SMTEncoding_Term.term* env_t)
  =
  fun env  ->
    fun x  ->
      fun str  ->
        let ysym = varops.mk_unique str in
        let y = FStar_SMTEncoding_Util.mkApp (ysym, []) in
        (ysym, y,
          (let uu___130_1147 = env in
           {
             bindings = ((Binding_var (x, y)) :: (env.bindings));
             depth = (uu___130_1147.depth);
             tcenv = (uu___130_1147.tcenv);
             warn = (uu___130_1147.warn);
             cache = (uu___130_1147.cache);
             nolabels = (uu___130_1147.nolabels);
             use_zfuel_name = (uu___130_1147.use_zfuel_name);
             encode_non_total_function_typ =
               (uu___130_1147.encode_non_total_function_typ);
             current_module_name = (uu___130_1147.current_module_name)
           }))
let push_term_var:
  env_t -> FStar_Syntax_Syntax.bv -> FStar_SMTEncoding_Term.term -> env_t =
  fun env  ->
    fun x  ->
      fun t  ->
        let uu___131_1157 = env in
        {
          bindings = ((Binding_var (x, t)) :: (env.bindings));
          depth = (uu___131_1157.depth);
          tcenv = (uu___131_1157.tcenv);
          warn = (uu___131_1157.warn);
          cache = (uu___131_1157.cache);
          nolabels = (uu___131_1157.nolabels);
          use_zfuel_name = (uu___131_1157.use_zfuel_name);
          encode_non_total_function_typ =
            (uu___131_1157.encode_non_total_function_typ);
          current_module_name = (uu___131_1157.current_module_name)
        }
let lookup_term_var:
  env_t -> FStar_Syntax_Syntax.bv -> FStar_SMTEncoding_Term.term =
  fun env  ->
    fun a  ->
      let aux a' =
        lookup_binding env
          (fun uu___104_1173  ->
             match uu___104_1173 with
             | Binding_var (b,t) when FStar_Syntax_Syntax.bv_eq b a' ->
                 Some (b, t)
             | uu____1181 -> None) in
      let uu____1184 = aux a in
      match uu____1184 with
      | None  ->
          let a2 = unmangle a in
          let uu____1191 = aux a2 in
          (match uu____1191 with
           | None  ->
               let uu____1197 =
                 let uu____1198 = FStar_Syntax_Print.bv_to_string a2 in
                 let uu____1199 = print_env env in
                 FStar_Util.format2
                   "Bound term variable not found (after unmangling): %s in environment: %s"
                   uu____1198 uu____1199 in
               failwith uu____1197
           | Some (b,t) -> t)
      | Some (b,t) -> t
let new_term_constant_and_tok_from_lid:
  env_t -> FStar_Ident.lident -> (Prims.string* Prims.string* env_t) =
  fun env  ->
    fun x  ->
      let fname = varops.new_fvar x in
      let ftok = Prims.strcat fname "@tok" in
      let uu____1219 =
        let uu___132_1220 = env in
        let uu____1221 =
          let uu____1223 =
            let uu____1224 =
              let uu____1231 =
                let uu____1233 = FStar_SMTEncoding_Util.mkApp (ftok, []) in
                FStar_All.pipe_left (fun _0_29  -> Some _0_29) uu____1233 in
              (x, fname, uu____1231, None) in
            Binding_fvar uu____1224 in
          uu____1223 :: (env.bindings) in
        {
          bindings = uu____1221;
          depth = (uu___132_1220.depth);
          tcenv = (uu___132_1220.tcenv);
          warn = (uu___132_1220.warn);
          cache = (uu___132_1220.cache);
          nolabels = (uu___132_1220.nolabels);
          use_zfuel_name = (uu___132_1220.use_zfuel_name);
          encode_non_total_function_typ =
            (uu___132_1220.encode_non_total_function_typ);
          current_module_name = (uu___132_1220.current_module_name)
        } in
      (fname, ftok, uu____1219)
let try_lookup_lid:
  env_t ->
    FStar_Ident.lident ->
      (Prims.string* FStar_SMTEncoding_Term.term option*
        FStar_SMTEncoding_Term.term option) option
  =
  fun env  ->
    fun a  ->
      lookup_binding env
        (fun uu___105_1255  ->
           match uu___105_1255 with
           | Binding_fvar (b,t1,t2,t3) when FStar_Ident.lid_equals b a ->
               Some (t1, t2, t3)
           | uu____1277 -> None)
let contains_name: env_t -> Prims.string -> Prims.bool =
  fun env  ->
    fun s  ->
      let uu____1289 =
        lookup_binding env
          (fun uu___106_1291  ->
             match uu___106_1291 with
             | Binding_fvar (b,t1,t2,t3) when b.FStar_Ident.str = s ->
                 Some ()
             | uu____1301 -> None) in
      FStar_All.pipe_right uu____1289 FStar_Option.isSome
let lookup_lid:
  env_t ->
    FStar_Ident.lident ->
      (Prims.string* FStar_SMTEncoding_Term.term option*
        FStar_SMTEncoding_Term.term option)
  =
  fun env  ->
    fun a  ->
      let uu____1314 = try_lookup_lid env a in
      match uu____1314 with
      | None  ->
          let uu____1331 =
            let uu____1332 = FStar_Syntax_Print.lid_to_string a in
            FStar_Util.format1 "Name not found: %s" uu____1332 in
          failwith uu____1331
      | Some s -> s
let push_free_var:
  env_t ->
    FStar_Ident.lident ->
      Prims.string -> FStar_SMTEncoding_Term.term option -> env_t
  =
  fun env  ->
    fun x  ->
      fun fname  ->
        fun ftok  ->
          let uu___133_1363 = env in
          {
            bindings = ((Binding_fvar (x, fname, ftok, None)) ::
              (env.bindings));
            depth = (uu___133_1363.depth);
            tcenv = (uu___133_1363.tcenv);
            warn = (uu___133_1363.warn);
            cache = (uu___133_1363.cache);
            nolabels = (uu___133_1363.nolabels);
            use_zfuel_name = (uu___133_1363.use_zfuel_name);
            encode_non_total_function_typ =
              (uu___133_1363.encode_non_total_function_typ);
            current_module_name = (uu___133_1363.current_module_name)
          }
let push_zfuel_name: env_t -> FStar_Ident.lident -> Prims.string -> env_t =
  fun env  ->
    fun x  ->
      fun f  ->
        let uu____1375 = lookup_lid env x in
        match uu____1375 with
        | (t1,t2,uu____1383) ->
            let t3 =
              let uu____1389 =
                let uu____1393 =
                  let uu____1395 = FStar_SMTEncoding_Util.mkApp ("ZFuel", []) in
                  [uu____1395] in
                (f, uu____1393) in
              FStar_SMTEncoding_Util.mkApp uu____1389 in
            let uu___134_1398 = env in
            {
              bindings = ((Binding_fvar (x, t1, t2, (Some t3))) ::
                (env.bindings));
              depth = (uu___134_1398.depth);
              tcenv = (uu___134_1398.tcenv);
              warn = (uu___134_1398.warn);
              cache = (uu___134_1398.cache);
              nolabels = (uu___134_1398.nolabels);
              use_zfuel_name = (uu___134_1398.use_zfuel_name);
              encode_non_total_function_typ =
                (uu___134_1398.encode_non_total_function_typ);
              current_module_name = (uu___134_1398.current_module_name)
            }
let try_lookup_free_var:
  env_t -> FStar_Ident.lident -> FStar_SMTEncoding_Term.term option =
  fun env  ->
    fun l  ->
      let uu____1408 = try_lookup_lid env l in
      match uu____1408 with
      | None  -> None
      | Some (name,sym,zf_opt) ->
          (match zf_opt with
           | Some f when env.use_zfuel_name -> Some f
           | uu____1435 ->
               (match sym with
                | Some t ->
                    (match t.FStar_SMTEncoding_Term.tm with
                     | FStar_SMTEncoding_Term.App (uu____1440,fuel::[]) ->
                         let uu____1443 =
                           let uu____1444 =
                             let uu____1445 =
                               FStar_SMTEncoding_Term.fv_of_term fuel in
                             FStar_All.pipe_right uu____1445
                               FStar_Pervasives.fst in
                           FStar_Util.starts_with uu____1444 "fuel" in
                         if uu____1443
                         then
                           let uu____1447 =
                             let uu____1448 =
                               FStar_SMTEncoding_Util.mkFreeV
                                 (name, FStar_SMTEncoding_Term.Term_sort) in
                             FStar_SMTEncoding_Term.mk_ApplyTF uu____1448
                               fuel in
                           FStar_All.pipe_left (fun _0_30  -> Some _0_30)
                             uu____1447
                         else Some t
                     | uu____1451 -> Some t)
                | uu____1452 -> None))
let lookup_free_var env a =
  let uu____1470 = try_lookup_free_var env a.FStar_Syntax_Syntax.v in
  match uu____1470 with
  | Some t -> t
  | None  ->
      let uu____1473 =
        let uu____1474 =
          FStar_Syntax_Print.lid_to_string a.FStar_Syntax_Syntax.v in
        FStar_Util.format1 "Name not found: %s" uu____1474 in
      failwith uu____1473
let lookup_free_var_name env a =
  let uu____1491 = lookup_lid env a.FStar_Syntax_Syntax.v in
  match uu____1491 with | (x,uu____1498,uu____1499) -> x
let lookup_free_var_sym env a =
  let uu____1523 = lookup_lid env a.FStar_Syntax_Syntax.v in
  match uu____1523 with
  | (name,sym,zf_opt) ->
      (match zf_opt with
       | Some
           { FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.App (g,zf);
             FStar_SMTEncoding_Term.freevars = uu____1544;
             FStar_SMTEncoding_Term.rng = uu____1545;_}
           when env.use_zfuel_name -> (g, zf)
       | uu____1553 ->
           (match sym with
            | None  -> ((FStar_SMTEncoding_Term.Var name), [])
            | Some sym1 ->
                (match sym1.FStar_SMTEncoding_Term.tm with
                 | FStar_SMTEncoding_Term.App (g,fuel::[]) -> (g, [fuel])
                 | uu____1567 -> ((FStar_SMTEncoding_Term.Var name), []))))
let tok_of_name: env_t -> Prims.string -> FStar_SMTEncoding_Term.term option
  =
  fun env  ->
    fun nm  ->
      FStar_Util.find_map env.bindings
        (fun uu___107_1576  ->
           match uu___107_1576 with
           | Binding_fvar (uu____1578,nm',tok,uu____1581) when nm = nm' ->
               tok
           | uu____1586 -> None)
let mkForall_fuel' n1 uu____1603 =
  match uu____1603 with
  | (pats,vars,body) ->
      let fallback uu____1619 =
        FStar_SMTEncoding_Util.mkForall (pats, vars, body) in
      let uu____1622 = FStar_Options.unthrottle_inductives () in
      if uu____1622
      then fallback ()
      else
        (let uu____1624 = fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort in
         match uu____1624 with
         | (fsym,fterm) ->
             let add_fuel1 tms =
               FStar_All.pipe_right tms
                 (FStar_List.map
                    (fun p  ->
                       match p.FStar_SMTEncoding_Term.tm with
                       | FStar_SMTEncoding_Term.App
                           (FStar_SMTEncoding_Term.Var "HasType",args) ->
                           FStar_SMTEncoding_Util.mkApp
                             ("HasTypeFuel", (fterm :: args))
                       | uu____1643 -> p)) in
             let pats1 = FStar_List.map add_fuel1 pats in
             let body1 =
               match body.FStar_SMTEncoding_Term.tm with
               | FStar_SMTEncoding_Term.App
                   (FStar_SMTEncoding_Term.Imp ,guard::body'::[]) ->
                   let guard1 =
                     match guard.FStar_SMTEncoding_Term.tm with
                     | FStar_SMTEncoding_Term.App
                         (FStar_SMTEncoding_Term.And ,guards) ->
                         let uu____1657 = add_fuel1 guards in
                         FStar_SMTEncoding_Util.mk_and_l uu____1657
                     | uu____1659 ->
                         let uu____1660 = add_fuel1 [guard] in
                         FStar_All.pipe_right uu____1660 FStar_List.hd in
                   FStar_SMTEncoding_Util.mkImp (guard1, body')
               | uu____1663 -> body in
             let vars1 = (fsym, FStar_SMTEncoding_Term.Fuel_sort) :: vars in
             FStar_SMTEncoding_Util.mkForall (pats1, vars1, body1))
let mkForall_fuel:
  (FStar_SMTEncoding_Term.pat Prims.list Prims.list*
    FStar_SMTEncoding_Term.fvs* FStar_SMTEncoding_Term.term) ->
    FStar_SMTEncoding_Term.term
  = mkForall_fuel' (Prims.parse_int "1")
let head_normal: env_t -> FStar_Syntax_Syntax.term -> Prims.bool =
  fun env  ->
    fun t  ->
      let t1 = FStar_Syntax_Util.unmeta t in
      match t1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_arrow uu____1689 -> true
      | FStar_Syntax_Syntax.Tm_refine uu____1697 -> true
      | FStar_Syntax_Syntax.Tm_bvar uu____1702 -> true
      | FStar_Syntax_Syntax.Tm_uvar uu____1703 -> true
      | FStar_Syntax_Syntax.Tm_abs uu____1712 -> true
      | FStar_Syntax_Syntax.Tm_constant uu____1727 -> true
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____1729 =
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Eager_unfolding_only] env.tcenv
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          FStar_All.pipe_right uu____1729 FStar_Option.isNone
      | FStar_Syntax_Syntax.Tm_app
          ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
             FStar_Syntax_Syntax.tk = uu____1743;
             FStar_Syntax_Syntax.pos = uu____1744;
             FStar_Syntax_Syntax.vars = uu____1745;_},uu____1746)
          ->
          let uu____1761 =
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Eager_unfolding_only] env.tcenv
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          FStar_All.pipe_right uu____1761 FStar_Option.isNone
      | uu____1774 -> false
let head_redex: env_t -> FStar_Syntax_Syntax.term -> Prims.bool =
  fun env  ->
    fun t  ->
      let uu____1781 =
        let uu____1782 = FStar_Syntax_Util.un_uinst t in
        uu____1782.FStar_Syntax_Syntax.n in
      match uu____1781 with
      | FStar_Syntax_Syntax.Tm_abs
          (uu____1785,uu____1786,Some (FStar_Util.Inr (l,flags))) ->
          ((FStar_Ident.lid_equals l FStar_Syntax_Const.effect_Tot_lid) ||
             (FStar_Ident.lid_equals l FStar_Syntax_Const.effect_GTot_lid))
            ||
            (FStar_List.existsb
               (fun uu___108_1815  ->
                  match uu___108_1815 with
                  | FStar_Syntax_Syntax.TOTAL  -> true
                  | uu____1816 -> false) flags)
      | FStar_Syntax_Syntax.Tm_abs
          (uu____1817,uu____1818,Some (FStar_Util.Inl lc)) ->
          FStar_Syntax_Util.is_tot_or_gtot_lcomp lc
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____1845 =
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Eager_unfolding_only] env.tcenv
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          FStar_All.pipe_right uu____1845 FStar_Option.isSome
      | uu____1858 -> false
let whnf: env_t -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term =
  fun env  ->
    fun t  ->
      let uu____1865 = head_normal env t in
      if uu____1865
      then t
      else
        FStar_TypeChecker_Normalize.normalize
          [FStar_TypeChecker_Normalize.Beta;
          FStar_TypeChecker_Normalize.WHNF;
          FStar_TypeChecker_Normalize.Exclude
            FStar_TypeChecker_Normalize.Zeta;
          FStar_TypeChecker_Normalize.Eager_unfolding;
          FStar_TypeChecker_Normalize.EraseUniverses] env.tcenv t
let norm: env_t -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term =
  fun env  ->
    fun t  ->
      FStar_TypeChecker_Normalize.normalize
        [FStar_TypeChecker_Normalize.Beta;
        FStar_TypeChecker_Normalize.Exclude FStar_TypeChecker_Normalize.Zeta;
        FStar_TypeChecker_Normalize.Eager_unfolding;
        FStar_TypeChecker_Normalize.EraseUniverses] env.tcenv t
let trivial_post: FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term =
  fun t  ->
    let uu____1876 =
      let uu____1877 = FStar_Syntax_Syntax.null_binder t in [uu____1877] in
    let uu____1878 =
      FStar_Syntax_Syntax.fvar FStar_Syntax_Const.true_lid
        FStar_Syntax_Syntax.Delta_constant None in
    FStar_Syntax_Util.abs uu____1876 uu____1878 None
let mk_Apply:
  FStar_SMTEncoding_Term.term ->
    (Prims.string* FStar_SMTEncoding_Term.sort) Prims.list ->
      FStar_SMTEncoding_Term.term
  =
  fun e  ->
    fun vars  ->
      FStar_All.pipe_right vars
        (FStar_List.fold_left
           (fun out  ->
              fun var  ->
                match snd var with
                | FStar_SMTEncoding_Term.Fuel_sort  ->
                    let uu____1905 = FStar_SMTEncoding_Util.mkFreeV var in
                    FStar_SMTEncoding_Term.mk_ApplyTF out uu____1905
                | s ->
                    let uu____1908 = FStar_SMTEncoding_Util.mkFreeV var in
                    FStar_SMTEncoding_Util.mk_ApplyTT out uu____1908) e)
let mk_Apply_args:
  FStar_SMTEncoding_Term.term ->
    FStar_SMTEncoding_Term.term Prims.list -> FStar_SMTEncoding_Term.term
  =
  fun e  ->
    fun args  ->
      FStar_All.pipe_right args
        (FStar_List.fold_left FStar_SMTEncoding_Util.mk_ApplyTT e)
let is_app: FStar_SMTEncoding_Term.op -> Prims.bool =
  fun uu___109_1920  ->
    match uu___109_1920 with
    | FStar_SMTEncoding_Term.Var "ApplyTT" -> true
    | FStar_SMTEncoding_Term.Var "ApplyTF" -> true
    | uu____1921 -> false
let is_an_eta_expansion:
  env_t ->
    FStar_SMTEncoding_Term.fv Prims.list ->
      FStar_SMTEncoding_Term.term -> FStar_SMTEncoding_Term.term option
  =
  fun env  ->
    fun vars  ->
      fun body  ->
        let rec check_partial_applications t xs =
          match ((t.FStar_SMTEncoding_Term.tm), xs) with
          | (FStar_SMTEncoding_Term.App
             (app,f::{
                       FStar_SMTEncoding_Term.tm =
                         FStar_SMTEncoding_Term.FreeV y;
                       FStar_SMTEncoding_Term.freevars = uu____1949;
                       FStar_SMTEncoding_Term.rng = uu____1950;_}::[]),x::xs1)
              when (is_app app) && (FStar_SMTEncoding_Term.fv_eq x y) ->
              check_partial_applications f xs1
          | (FStar_SMTEncoding_Term.App
             (FStar_SMTEncoding_Term.Var f,args),uu____1964) ->
              let uu____1969 =
                ((FStar_List.length args) = (FStar_List.length xs)) &&
                  (FStar_List.forall2
                     (fun a  ->
                        fun v1  ->
                          match a.FStar_SMTEncoding_Term.tm with
                          | FStar_SMTEncoding_Term.FreeV fv ->
                              FStar_SMTEncoding_Term.fv_eq fv v1
                          | uu____1979 -> false) args (FStar_List.rev xs)) in
              if uu____1969 then tok_of_name env f else None
          | (uu____1982,[]) ->
              let fvs = FStar_SMTEncoding_Term.free_variables t in
              let uu____1985 =
                FStar_All.pipe_right fvs
                  (FStar_List.for_all
                     (fun fv  ->
                        let uu____1987 =
                          FStar_Util.for_some
                            (FStar_SMTEncoding_Term.fv_eq fv) vars in
                        Prims.op_Negation uu____1987)) in
              if uu____1985 then Some t else None
          | uu____1990 -> None in
        check_partial_applications body (FStar_List.rev vars)
type label = (FStar_SMTEncoding_Term.fv* Prims.string* FStar_Range.range)
type labels = label Prims.list
type pattern =
  {
  pat_vars: (FStar_Syntax_Syntax.bv* FStar_SMTEncoding_Term.fv) Prims.list;
  pat_term:
    Prims.unit ->
      (FStar_SMTEncoding_Term.term* FStar_SMTEncoding_Term.decls_t);
  guard: FStar_SMTEncoding_Term.term -> FStar_SMTEncoding_Term.term;
  projections:
    FStar_SMTEncoding_Term.term ->
      (FStar_Syntax_Syntax.bv* FStar_SMTEncoding_Term.term) Prims.list;}
exception Let_rec_unencodeable
let uu___is_Let_rec_unencodeable: Prims.exn -> Prims.bool =
  fun projectee  ->
    match projectee with
    | Let_rec_unencodeable  -> true
    | uu____2081 -> false
let encode_const: FStar_Const.sconst -> FStar_SMTEncoding_Term.term =
  fun uu___110_2084  ->
    match uu___110_2084 with
    | FStar_Const.Const_unit  -> FStar_SMTEncoding_Term.mk_Term_unit
    | FStar_Const.Const_bool (true ) ->
        FStar_SMTEncoding_Term.boxBool FStar_SMTEncoding_Util.mkTrue
    | FStar_Const.Const_bool (false ) ->
        FStar_SMTEncoding_Term.boxBool FStar_SMTEncoding_Util.mkFalse
    | FStar_Const.Const_char c ->
        let uu____2086 =
          let uu____2090 =
            let uu____2092 =
              let uu____2093 =
                FStar_SMTEncoding_Util.mkInteger' (FStar_Util.int_of_char c) in
              FStar_SMTEncoding_Term.boxInt uu____2093 in
            [uu____2092] in
          ("FStar.Char.Char", uu____2090) in
        FStar_SMTEncoding_Util.mkApp uu____2086
    | FStar_Const.Const_int (i,None ) ->
        let uu____2101 = FStar_SMTEncoding_Util.mkInteger i in
        FStar_SMTEncoding_Term.boxInt uu____2101
    | FStar_Const.Const_int (i,Some uu____2103) ->
        failwith "Machine integers should be desugared"
    | FStar_Const.Const_string (bytes,uu____2112) ->
        let uu____2115 = FStar_All.pipe_left FStar_Util.string_of_bytes bytes in
        varops.string_const uu____2115
    | FStar_Const.Const_range r -> FStar_SMTEncoding_Term.mk_Range_const
    | FStar_Const.Const_effect  -> FStar_SMTEncoding_Term.mk_Term_type
    | c ->
        let uu____2119 =
          let uu____2120 = FStar_Syntax_Print.const_to_string c in
          FStar_Util.format1 "Unhandled constant: %s" uu____2120 in
        failwith uu____2119
let as_function_typ:
  env_t ->
    (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun t0  ->
      let rec aux norm1 t =
        let t1 = FStar_Syntax_Subst.compress t in
        match t1.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_arrow uu____2139 -> t1
        | FStar_Syntax_Syntax.Tm_refine uu____2147 ->
            let uu____2152 = FStar_Syntax_Util.unrefine t1 in
            aux true uu____2152
        | uu____2153 ->
            if norm1
            then let uu____2154 = whnf env t1 in aux false uu____2154
            else
              (let uu____2156 =
                 let uu____2157 =
                   FStar_Range.string_of_range t0.FStar_Syntax_Syntax.pos in
                 let uu____2158 = FStar_Syntax_Print.term_to_string t0 in
                 FStar_Util.format2 "(%s) Expected a function typ; got %s"
                   uu____2157 uu____2158 in
               failwith uu____2156) in
      aux true t0
let curried_arrow_formals_comp:
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.binders* FStar_Syntax_Syntax.comp)
  =
  fun k  ->
    let k1 = FStar_Syntax_Subst.compress k in
    match k1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
        FStar_Syntax_Subst.open_comp bs c
    | uu____2179 ->
        let uu____2180 = FStar_Syntax_Syntax.mk_Total k1 in ([], uu____2180)
let is_arithmetic_primitive head1 args =
  match ((head1.FStar_Syntax_Syntax.n), args) with
  | (FStar_Syntax_Syntax.Tm_fvar fv,uu____2208::uu____2209::[]) ->
      ((((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.op_Addition) ||
           (FStar_Syntax_Syntax.fv_eq_lid fv
              FStar_Syntax_Const.op_Subtraction))
          ||
          (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.op_Multiply))
         || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.op_Division))
        || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.op_Modulus)
  | (FStar_Syntax_Syntax.Tm_fvar fv,uu____2212::[]) ->
      FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.op_Minus
  | uu____2214 -> false
let rec encode_binders:
  FStar_SMTEncoding_Term.term option ->
    FStar_Syntax_Syntax.binders ->
      env_t ->
        (FStar_SMTEncoding_Term.fv Prims.list* FStar_SMTEncoding_Term.term
          Prims.list* env_t* FStar_SMTEncoding_Term.decls_t*
          FStar_Syntax_Syntax.bv Prims.list)
  =
  fun fuel_opt  ->
    fun bs  ->
      fun env  ->
        (let uu____2352 =
           FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low in
         if uu____2352
         then
           let uu____2353 = FStar_Syntax_Print.binders_to_string ", " bs in
           FStar_Util.print1 "Encoding binders %s\n" uu____2353
         else ());
        (let uu____2355 =
           FStar_All.pipe_right bs
             (FStar_List.fold_left
                (fun uu____2391  ->
                   fun b  ->
                     match uu____2391 with
                     | (vars,guards,env1,decls,names1) ->
                         let uu____2434 =
                           let x = unmangle (fst b) in
                           let uu____2443 = gen_term_var env1 x in
                           match uu____2443 with
                           | (xxsym,xx,env') ->
                               let uu____2457 =
                                 let uu____2460 =
                                   norm env1 x.FStar_Syntax_Syntax.sort in
                                 encode_term_pred fuel_opt uu____2460 env1 xx in
                               (match uu____2457 with
                                | (guard_x_t,decls') ->
                                    ((xxsym,
                                       FStar_SMTEncoding_Term.Term_sort),
                                      guard_x_t, env', decls', x)) in
                         (match uu____2434 with
                          | (v1,g,env2,decls',n1) ->
                              ((v1 :: vars), (g :: guards), env2,
                                (FStar_List.append decls decls'), (n1 ::
                                names1)))) ([], [], env, [], [])) in
         match uu____2355 with
         | (vars,guards,env1,decls,names1) ->
             ((FStar_List.rev vars), (FStar_List.rev guards), env1, decls,
               (FStar_List.rev names1)))
and encode_term_pred:
  FStar_SMTEncoding_Term.term option ->
    FStar_Syntax_Syntax.typ ->
      env_t ->
        FStar_SMTEncoding_Term.term ->
          (FStar_SMTEncoding_Term.term* FStar_SMTEncoding_Term.decls_t)
  =
  fun fuel_opt  ->
    fun t  ->
      fun env  ->
        fun e  ->
          let uu____2548 = encode_term t env in
          match uu____2548 with
          | (t1,decls) ->
              let uu____2555 =
                FStar_SMTEncoding_Term.mk_HasTypeWithFuel fuel_opt e t1 in
              (uu____2555, decls)
and encode_term_pred':
  FStar_SMTEncoding_Term.term option ->
    FStar_Syntax_Syntax.typ ->
      env_t ->
        FStar_SMTEncoding_Term.term ->
          (FStar_SMTEncoding_Term.term* FStar_SMTEncoding_Term.decls_t)
  =
  fun fuel_opt  ->
    fun t  ->
      fun env  ->
        fun e  ->
          let uu____2563 = encode_term t env in
          match uu____2563 with
          | (t1,decls) ->
              (match fuel_opt with
               | None  ->
                   let uu____2572 = FStar_SMTEncoding_Term.mk_HasTypeZ e t1 in
                   (uu____2572, decls)
               | Some f ->
                   let uu____2574 =
                     FStar_SMTEncoding_Term.mk_HasTypeFuel f e t1 in
                   (uu____2574, decls))
and encode_arith_term:
  env_t ->
    (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.args ->
        (FStar_SMTEncoding_Term.term* FStar_SMTEncoding_Term.decls_t)
  =
  fun env  ->
    fun head1  ->
      fun args_e  ->
        let uu____2580 = encode_args args_e env in
        match uu____2580 with
        | (arg_tms,decls) ->
            let head_fv =
              match head1.FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_fvar fv -> fv
              | uu____2592 -> failwith "Impossible" in
            let unary arg_tms1 =
              let uu____2599 = FStar_List.hd arg_tms1 in
              FStar_SMTEncoding_Term.unboxInt uu____2599 in
            let binary arg_tms1 =
              let uu____2608 =
                let uu____2609 = FStar_List.hd arg_tms1 in
                FStar_SMTEncoding_Term.unboxInt uu____2609 in
              let uu____2610 =
                let uu____2611 =
                  let uu____2612 = FStar_List.tl arg_tms1 in
                  FStar_List.hd uu____2612 in
                FStar_SMTEncoding_Term.unboxInt uu____2611 in
              (uu____2608, uu____2610) in
            let mk_default uu____2617 =
              let uu____2618 =
                lookup_free_var_sym env head_fv.FStar_Syntax_Syntax.fv_name in
              match uu____2618 with
              | (fname,fuel_args) ->
                  FStar_SMTEncoding_Util.mkApp'
                    (fname, (FStar_List.append fuel_args arg_tms)) in
            let mk_l op mk_args ts =
              let uu____2663 = FStar_Options.smtencoding_l_arith_native () in
              if uu____2663
              then
                let uu____2664 = let uu____2665 = mk_args ts in op uu____2665 in
                FStar_All.pipe_right uu____2664 FStar_SMTEncoding_Term.boxInt
              else mk_default () in
            let mk_nl nm op ts =
              let uu____2688 = FStar_Options.smtencoding_nl_arith_wrapped () in
              if uu____2688
              then
                let uu____2689 = binary ts in
                match uu____2689 with
                | (t1,t2) ->
                    let uu____2694 =
                      FStar_SMTEncoding_Util.mkApp (nm, [t1; t2]) in
                    FStar_All.pipe_right uu____2694
                      FStar_SMTEncoding_Term.boxInt
              else
                (let uu____2697 =
                   FStar_Options.smtencoding_nl_arith_native () in
                 if uu____2697
                 then
                   let uu____2698 = op (binary ts) in
                   FStar_All.pipe_right uu____2698
                     FStar_SMTEncoding_Term.boxInt
                 else mk_default ()) in
            let add1 = mk_l FStar_SMTEncoding_Util.mkAdd binary in
            let sub1 = mk_l FStar_SMTEncoding_Util.mkSub binary in
            let minus = mk_l FStar_SMTEncoding_Util.mkMinus unary in
            let mul1 = mk_nl "_mul" FStar_SMTEncoding_Util.mkMul in
            let div1 = mk_nl "_div" FStar_SMTEncoding_Util.mkDiv in
            let modulus = mk_nl "_mod" FStar_SMTEncoding_Util.mkMod in
            let ops =
              [(FStar_Syntax_Const.op_Addition, add1);
              (FStar_Syntax_Const.op_Subtraction, sub1);
              (FStar_Syntax_Const.op_Multiply, mul1);
              (FStar_Syntax_Const.op_Division, div1);
              (FStar_Syntax_Const.op_Modulus, modulus);
              (FStar_Syntax_Const.op_Minus, minus)] in
            let uu____2788 =
              let uu____2794 =
                FStar_List.tryFind
                  (fun uu____2806  ->
                     match uu____2806 with
                     | (l,uu____2813) ->
                         FStar_Syntax_Syntax.fv_eq_lid head_fv l) ops in
              FStar_All.pipe_right uu____2794 FStar_Util.must in
            (match uu____2788 with
             | (uu____2838,op) ->
                 let uu____2846 = op arg_tms in (uu____2846, decls))
and encode_term:
  FStar_Syntax_Syntax.typ ->
    env_t -> (FStar_SMTEncoding_Term.term* FStar_SMTEncoding_Term.decls_t)
  =
  fun t  ->
    fun env  ->
      let t0 = FStar_Syntax_Subst.compress t in
      (let uu____2853 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv)
           (FStar_Options.Other "SMTEncoding") in
       if uu____2853
       then
         let uu____2854 = FStar_Syntax_Print.tag_of_term t in
         let uu____2855 = FStar_Syntax_Print.tag_of_term t0 in
         let uu____2856 = FStar_Syntax_Print.term_to_string t0 in
         FStar_Util.print3 "(%s) (%s)   %s\n" uu____2854 uu____2855
           uu____2856
       else ());
      (match t0.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Tm_delayed uu____2860 ->
           let uu____2881 =
             let uu____2882 =
               FStar_All.pipe_left FStar_Range.string_of_range
                 t.FStar_Syntax_Syntax.pos in
             let uu____2883 = FStar_Syntax_Print.tag_of_term t0 in
             let uu____2884 = FStar_Syntax_Print.term_to_string t0 in
             let uu____2885 = FStar_Syntax_Print.term_to_string t in
             FStar_Util.format4 "(%s) Impossible: %s\n%s\n%s\n" uu____2882
               uu____2883 uu____2884 uu____2885 in
           failwith uu____2881
       | FStar_Syntax_Syntax.Tm_unknown  ->
           let uu____2888 =
             let uu____2889 =
               FStar_All.pipe_left FStar_Range.string_of_range
                 t.FStar_Syntax_Syntax.pos in
             let uu____2890 = FStar_Syntax_Print.tag_of_term t0 in
             let uu____2891 = FStar_Syntax_Print.term_to_string t0 in
             let uu____2892 = FStar_Syntax_Print.term_to_string t in
             FStar_Util.format4 "(%s) Impossible: %s\n%s\n%s\n" uu____2889
               uu____2890 uu____2891 uu____2892 in
           failwith uu____2888
       | FStar_Syntax_Syntax.Tm_bvar x ->
           let uu____2896 =
             let uu____2897 = FStar_Syntax_Print.bv_to_string x in
             FStar_Util.format1 "Impossible: locally nameless; got %s"
               uu____2897 in
           failwith uu____2896
       | FStar_Syntax_Syntax.Tm_ascribed (t1,k,uu____2902) ->
           encode_term t1 env
       | FStar_Syntax_Syntax.Tm_meta (t1,uu____2932) -> encode_term t1 env
       | FStar_Syntax_Syntax.Tm_name x ->
           let t1 = lookup_term_var env x in (t1, [])
       | FStar_Syntax_Syntax.Tm_fvar v1 ->
           let uu____2941 =
             lookup_free_var env v1.FStar_Syntax_Syntax.fv_name in
           (uu____2941, [])
       | FStar_Syntax_Syntax.Tm_type uu____2947 ->
           (FStar_SMTEncoding_Term.mk_Term_type, [])
       | FStar_Syntax_Syntax.Tm_uinst (t1,uu____2950) -> encode_term t1 env
       | FStar_Syntax_Syntax.Tm_constant c ->
           let uu____2956 = encode_const c in (uu____2956, [])
       | FStar_Syntax_Syntax.Tm_arrow (binders,c) ->
           let module_name = env.current_module_name in
           let uu____2971 = FStar_Syntax_Subst.open_comp binders c in
           (match uu____2971 with
            | (binders1,res) ->
                let uu____2978 =
                  (env.encode_non_total_function_typ &&
                     (FStar_Syntax_Util.is_pure_or_ghost_comp res))
                    || (FStar_Syntax_Util.is_tot_or_gtot_comp res) in
                if uu____2978
                then
                  let uu____2981 = encode_binders None binders1 env in
                  (match uu____2981 with
                   | (vars,guards,env',decls,uu____2996) ->
                       let fsym =
                         let uu____3006 = varops.fresh "f" in
                         (uu____3006, FStar_SMTEncoding_Term.Term_sort) in
                       let f = FStar_SMTEncoding_Util.mkFreeV fsym in
                       let app = mk_Apply f vars in
                       let uu____3009 =
                         FStar_TypeChecker_Util.pure_or_ghost_pre_and_post
                           (let uu___135_3013 = env.tcenv in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___135_3013.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___135_3013.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___135_3013.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___135_3013.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___135_3013.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___135_3013.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                (uu___135_3013.FStar_TypeChecker_Env.expected_typ);
                              FStar_TypeChecker_Env.sigtab =
                                (uu___135_3013.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.is_pattern =
                                (uu___135_3013.FStar_TypeChecker_Env.is_pattern);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___135_3013.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___135_3013.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___135_3013.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___135_3013.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___135_3013.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___135_3013.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___135_3013.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___135_3013.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___135_3013.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___135_3013.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.type_of =
                                (uu___135_3013.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___135_3013.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.use_bv_sorts =
                                (uu___135_3013.FStar_TypeChecker_Env.use_bv_sorts);
                              FStar_TypeChecker_Env.qname_and_index =
                                (uu___135_3013.FStar_TypeChecker_Env.qname_and_index)
                            }) res in
                       (match uu____3009 with
                        | (pre_opt,res_t) ->
                            let uu____3020 =
                              encode_term_pred None res_t env' app in
                            (match uu____3020 with
                             | (res_pred,decls') ->
                                 let uu____3027 =
                                   match pre_opt with
                                   | None  ->
                                       let uu____3034 =
                                         FStar_SMTEncoding_Util.mk_and_l
                                           guards in
                                       (uu____3034, [])
                                   | Some pre ->
                                       let uu____3037 =
                                         encode_formula pre env' in
                                       (match uu____3037 with
                                        | (guard,decls0) ->
                                            let uu____3045 =
                                              FStar_SMTEncoding_Util.mk_and_l
                                                (guard :: guards) in
                                            (uu____3045, decls0)) in
                                 (match uu____3027 with
                                  | (guards1,guard_decls) ->
                                      let t_interp =
                                        let uu____3053 =
                                          let uu____3059 =
                                            FStar_SMTEncoding_Util.mkImp
                                              (guards1, res_pred) in
                                          ([[app]], vars, uu____3059) in
                                        FStar_SMTEncoding_Util.mkForall
                                          uu____3053 in
                                      let cvars =
                                        let uu____3069 =
                                          FStar_SMTEncoding_Term.free_variables
                                            t_interp in
                                        FStar_All.pipe_right uu____3069
                                          (FStar_List.filter
                                             (fun uu____3075  ->
                                                match uu____3075 with
                                                | (x,uu____3079) ->
                                                    x <> (fst fsym))) in
                                      let tkey =
                                        FStar_SMTEncoding_Util.mkForall
                                          ([], (fsym :: cvars), t_interp) in
                                      let tkey_hash =
                                        FStar_SMTEncoding_Term.hash_of_term
                                          tkey in
                                      let uu____3090 =
                                        FStar_Util.smap_try_find env.cache
                                          tkey_hash in
                                      (match uu____3090 with
                                       | Some cache_entry ->
                                           let uu____3095 =
                                             let uu____3096 =
                                               let uu____3100 =
                                                 FStar_All.pipe_right cvars
                                                   (FStar_List.map
                                                      FStar_SMTEncoding_Util.mkFreeV) in
                                               ((cache_entry.cache_symbol_name),
                                                 uu____3100) in
                                             FStar_SMTEncoding_Util.mkApp
                                               uu____3096 in
                                           (uu____3095,
                                             (FStar_List.append decls
                                                (FStar_List.append decls'
                                                   (FStar_List.append
                                                      guard_decls
                                                      (use_cache_entry
                                                         cache_entry)))))
                                       | None  ->
                                           let tsym =
                                             let uu____3111 =
                                               let uu____3112 =
                                                 FStar_Util.digest_of_string
                                                   tkey_hash in
                                               Prims.strcat "Tm_arrow_"
                                                 uu____3112 in
                                             varops.mk_unique uu____3111 in
                                           let cvar_sorts =
                                             FStar_List.map
                                               FStar_Pervasives.snd cvars in
                                           let caption =
                                             let uu____3119 =
                                               FStar_Options.log_queries () in
                                             if uu____3119
                                             then
                                               let uu____3121 =
                                                 FStar_TypeChecker_Normalize.term_to_string
                                                   env.tcenv t0 in
                                               Some uu____3121
                                             else None in
                                           let tdecl =
                                             FStar_SMTEncoding_Term.DeclFun
                                               (tsym, cvar_sorts,
                                                 FStar_SMTEncoding_Term.Term_sort,
                                                 caption) in
                                           let t1 =
                                             let uu____3127 =
                                               let uu____3131 =
                                                 FStar_List.map
                                                   FStar_SMTEncoding_Util.mkFreeV
                                                   cvars in
                                               (tsym, uu____3131) in
                                             FStar_SMTEncoding_Util.mkApp
                                               uu____3127 in
                                           let t_has_kind =
                                             FStar_SMTEncoding_Term.mk_HasType
                                               t1
                                               FStar_SMTEncoding_Term.mk_Term_type in
                                           let k_assumption =
                                             let a_name =
                                               Prims.strcat "kinding_" tsym in
                                             let uu____3139 =
                                               let uu____3143 =
                                                 FStar_SMTEncoding_Util.mkForall
                                                   ([[t_has_kind]], cvars,
                                                     t_has_kind) in
                                               (uu____3143, (Some a_name),
                                                 a_name) in
                                             FStar_SMTEncoding_Util.mkAssume
                                               uu____3139 in
                                           let f_has_t =
                                             FStar_SMTEncoding_Term.mk_HasType
                                               f t1 in
                                           let f_has_t_z =
                                             FStar_SMTEncoding_Term.mk_HasTypeZ
                                               f t1 in
                                           let pre_typing =
                                             let a_name =
                                               Prims.strcat "pre_typing_"
                                                 tsym in
                                             let uu____3156 =
                                               let uu____3160 =
                                                 let uu____3161 =
                                                   let uu____3167 =
                                                     let uu____3168 =
                                                       let uu____3171 =
                                                         let uu____3172 =
                                                           FStar_SMTEncoding_Term.mk_PreType
                                                             f in
                                                         FStar_SMTEncoding_Term.mk_tester
                                                           "Tm_arrow"
                                                           uu____3172 in
                                                       (f_has_t, uu____3171) in
                                                     FStar_SMTEncoding_Util.mkImp
                                                       uu____3168 in
                                                   ([[f_has_t]], (fsym ::
                                                     cvars), uu____3167) in
                                                 mkForall_fuel uu____3161 in
                                               (uu____3160,
                                                 (Some
                                                    "pre-typing for functions"),
                                                 (Prims.strcat module_name
                                                    (Prims.strcat "_" a_name))) in
                                             FStar_SMTEncoding_Util.mkAssume
                                               uu____3156 in
                                           let t_interp1 =
                                             let a_name =
                                               Prims.strcat "interpretation_"
                                                 tsym in
                                             let uu____3185 =
                                               let uu____3189 =
                                                 let uu____3190 =
                                                   let uu____3196 =
                                                     FStar_SMTEncoding_Util.mkIff
                                                       (f_has_t_z, t_interp) in
                                                   ([[f_has_t_z]], (fsym ::
                                                     cvars), uu____3196) in
                                                 FStar_SMTEncoding_Util.mkForall
                                                   uu____3190 in
                                               (uu____3189, (Some a_name),
                                                 (Prims.strcat module_name
                                                    (Prims.strcat "_" a_name))) in
                                             FStar_SMTEncoding_Util.mkAssume
                                               uu____3185 in
                                           let t_decls =
                                             FStar_List.append (tdecl ::
                                               decls)
                                               (FStar_List.append decls'
                                                  (FStar_List.append
                                                     guard_decls
                                                     [k_assumption;
                                                     pre_typing;
                                                     t_interp1])) in
                                           ((let uu____3210 =
                                               mk_cache_entry env tsym
                                                 cvar_sorts t_decls in
                                             FStar_Util.smap_add env.cache
                                               tkey_hash uu____3210);
                                            (t1, t_decls)))))))
                else
                  (let tsym = varops.fresh "Non_total_Tm_arrow" in
                   let tdecl =
                     FStar_SMTEncoding_Term.DeclFun
                       (tsym, [], FStar_SMTEncoding_Term.Term_sort, None) in
                   let t1 = FStar_SMTEncoding_Util.mkApp (tsym, []) in
                   let t_kinding =
                     let a_name =
                       Prims.strcat "non_total_function_typing_" tsym in
                     let uu____3221 =
                       let uu____3225 =
                         FStar_SMTEncoding_Term.mk_HasType t1
                           FStar_SMTEncoding_Term.mk_Term_type in
                       (uu____3225, (Some "Typing for non-total arrows"),
                         (Prims.strcat module_name (Prims.strcat "_" a_name))) in
                     FStar_SMTEncoding_Util.mkAssume uu____3221 in
                   let fsym = ("f", FStar_SMTEncoding_Term.Term_sort) in
                   let f = FStar_SMTEncoding_Util.mkFreeV fsym in
                   let f_has_t = FStar_SMTEncoding_Term.mk_HasType f t1 in
                   let t_interp =
                     let a_name = Prims.strcat "pre_typing_" tsym in
                     let uu____3234 =
                       let uu____3238 =
                         let uu____3239 =
                           let uu____3245 =
                             let uu____3246 =
                               let uu____3249 =
                                 let uu____3250 =
                                   FStar_SMTEncoding_Term.mk_PreType f in
                                 FStar_SMTEncoding_Term.mk_tester "Tm_arrow"
                                   uu____3250 in
                               (f_has_t, uu____3249) in
                             FStar_SMTEncoding_Util.mkImp uu____3246 in
                           ([[f_has_t]], [fsym], uu____3245) in
                         mkForall_fuel uu____3239 in
                       (uu____3238, (Some a_name),
                         (Prims.strcat module_name (Prims.strcat "_" a_name))) in
                     FStar_SMTEncoding_Util.mkAssume uu____3234 in
                   (t1, [tdecl; t_kinding; t_interp])))
       | FStar_Syntax_Syntax.Tm_refine uu____3264 ->
           let uu____3269 =
             let uu____3272 =
               FStar_TypeChecker_Normalize.normalize_refinement
                 [FStar_TypeChecker_Normalize.WHNF;
                 FStar_TypeChecker_Normalize.EraseUniverses] env.tcenv t0 in
             match uu____3272 with
             | { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_refine (x,f);
                 FStar_Syntax_Syntax.tk = uu____3277;
                 FStar_Syntax_Syntax.pos = uu____3278;
                 FStar_Syntax_Syntax.vars = uu____3279;_} ->
                 let uu____3286 = FStar_Syntax_Subst.open_term [(x, None)] f in
                 (match uu____3286 with
                  | (b,f1) ->
                      let uu____3300 =
                        let uu____3301 = FStar_List.hd b in fst uu____3301 in
                      (uu____3300, f1))
             | uu____3306 -> failwith "impossible" in
           (match uu____3269 with
            | (x,f) ->
                let uu____3313 = encode_term x.FStar_Syntax_Syntax.sort env in
                (match uu____3313 with
                 | (base_t,decls) ->
                     let uu____3320 = gen_term_var env x in
                     (match uu____3320 with
                      | (x1,xtm,env') ->
                          let uu____3329 = encode_formula f env' in
                          (match uu____3329 with
                           | (refinement,decls') ->
                               let uu____3336 =
                                 fresh_fvar "f"
                                   FStar_SMTEncoding_Term.Fuel_sort in
                               (match uu____3336 with
                                | (fsym,fterm) ->
                                    let tm_has_type_with_fuel =
                                      FStar_SMTEncoding_Term.mk_HasTypeWithFuel
                                        (Some fterm) xtm base_t in
                                    let encoding =
                                      FStar_SMTEncoding_Util.mkAnd
                                        (tm_has_type_with_fuel, refinement) in
                                    let cvars =
                                      let uu____3347 =
                                        let uu____3349 =
                                          FStar_SMTEncoding_Term.free_variables
                                            refinement in
                                        let uu____3353 =
                                          FStar_SMTEncoding_Term.free_variables
                                            tm_has_type_with_fuel in
                                        FStar_List.append uu____3349
                                          uu____3353 in
                                      FStar_Util.remove_dups
                                        FStar_SMTEncoding_Term.fv_eq
                                        uu____3347 in
                                    let cvars1 =
                                      FStar_All.pipe_right cvars
                                        (FStar_List.filter
                                           (fun uu____3369  ->
                                              match uu____3369 with
                                              | (y,uu____3373) ->
                                                  (y <> x1) && (y <> fsym))) in
                                    let xfv =
                                      (x1, FStar_SMTEncoding_Term.Term_sort) in
                                    let ffv =
                                      (fsym,
                                        FStar_SMTEncoding_Term.Fuel_sort) in
                                    let tkey =
                                      FStar_SMTEncoding_Util.mkForall
                                        ([], (ffv :: xfv :: cvars1),
                                          encoding) in
                                    let tkey_hash =
                                      FStar_SMTEncoding_Term.hash_of_term
                                        tkey in
                                    let uu____3392 =
                                      FStar_Util.smap_try_find env.cache
                                        tkey_hash in
                                    (match uu____3392 with
                                     | Some cache_entry ->
                                         let uu____3397 =
                                           let uu____3398 =
                                             let uu____3402 =
                                               FStar_All.pipe_right cvars1
                                                 (FStar_List.map
                                                    FStar_SMTEncoding_Util.mkFreeV) in
                                             ((cache_entry.cache_symbol_name),
                                               uu____3402) in
                                           FStar_SMTEncoding_Util.mkApp
                                             uu____3398 in
                                         (uu____3397,
                                           (FStar_List.append decls
                                              (FStar_List.append decls'
                                                 (use_cache_entry cache_entry))))
                                     | None  ->
                                         let module_name =
                                           env.current_module_name in
                                         let tsym =
                                           let uu____3414 =
                                             let uu____3415 =
                                               let uu____3416 =
                                                 FStar_Util.digest_of_string
                                                   tkey_hash in
                                               Prims.strcat "_Tm_refine_"
                                                 uu____3416 in
                                             Prims.strcat module_name
                                               uu____3415 in
                                           varops.mk_unique uu____3414 in
                                         let cvar_sorts =
                                           FStar_List.map
                                             FStar_Pervasives.snd cvars1 in
                                         let tdecl =
                                           FStar_SMTEncoding_Term.DeclFun
                                             (tsym, cvar_sorts,
                                               FStar_SMTEncoding_Term.Term_sort,
                                               None) in
                                         let t1 =
                                           let uu____3425 =
                                             let uu____3429 =
                                               FStar_List.map
                                                 FStar_SMTEncoding_Util.mkFreeV
                                                 cvars1 in
                                             (tsym, uu____3429) in
                                           FStar_SMTEncoding_Util.mkApp
                                             uu____3425 in
                                         let x_has_t =
                                           FStar_SMTEncoding_Term.mk_HasTypeWithFuel
                                             (Some fterm) xtm t1 in
                                         let t_has_kind =
                                           FStar_SMTEncoding_Term.mk_HasType
                                             t1
                                             FStar_SMTEncoding_Term.mk_Term_type in
                                         let t_haseq_base =
                                           FStar_SMTEncoding_Term.mk_haseq
                                             base_t in
                                         let t_haseq_ref =
                                           FStar_SMTEncoding_Term.mk_haseq t1 in
                                         let t_haseq1 =
                                           let uu____3439 =
                                             let uu____3443 =
                                               let uu____3444 =
                                                 let uu____3450 =
                                                   FStar_SMTEncoding_Util.mkIff
                                                     (t_haseq_ref,
                                                       t_haseq_base) in
                                                 ([[t_haseq_ref]], cvars1,
                                                   uu____3450) in
                                               FStar_SMTEncoding_Util.mkForall
                                                 uu____3444 in
                                             (uu____3443,
                                               (Some
                                                  (Prims.strcat "haseq for "
                                                     tsym)),
                                               (Prims.strcat "haseq" tsym)) in
                                           FStar_SMTEncoding_Util.mkAssume
                                             uu____3439 in
                                         let t_kinding =
                                           let uu____3460 =
                                             let uu____3464 =
                                               FStar_SMTEncoding_Util.mkForall
                                                 ([[t_has_kind]], cvars1,
                                                   t_has_kind) in
                                             (uu____3464,
                                               (Some "refinement kinding"),
                                               (Prims.strcat
                                                  "refinement_kinding_" tsym)) in
                                           FStar_SMTEncoding_Util.mkAssume
                                             uu____3460 in
                                         let t_interp =
                                           let uu____3474 =
                                             let uu____3478 =
                                               let uu____3479 =
                                                 let uu____3485 =
                                                   FStar_SMTEncoding_Util.mkIff
                                                     (x_has_t, encoding) in
                                                 ([[x_has_t]], (ffv :: xfv ::
                                                   cvars1), uu____3485) in
                                               FStar_SMTEncoding_Util.mkForall
                                                 uu____3479 in
                                             let uu____3497 =
                                               let uu____3499 =
                                                 FStar_Syntax_Print.term_to_string
                                                   t0 in
                                               Some uu____3499 in
                                             (uu____3478, uu____3497,
                                               (Prims.strcat
                                                  "refinement_interpretation_"
                                                  tsym)) in
                                           FStar_SMTEncoding_Util.mkAssume
                                             uu____3474 in
                                         let t_decls =
                                           FStar_List.append decls
                                             (FStar_List.append decls'
                                                [tdecl;
                                                t_kinding;
                                                t_interp;
                                                t_haseq1]) in
                                         ((let uu____3504 =
                                             mk_cache_entry env tsym
                                               cvar_sorts t_decls in
                                           FStar_Util.smap_add env.cache
                                             tkey_hash uu____3504);
                                          (t1, t_decls))))))))
       | FStar_Syntax_Syntax.Tm_uvar (uv,k) ->
           let ttm =
             let uu____3521 = FStar_Unionfind.uvar_id uv in
             FStar_SMTEncoding_Util.mk_Term_uvar uu____3521 in
           let uu____3525 = encode_term_pred None k env ttm in
           (match uu____3525 with
            | (t_has_k,decls) ->
                let d =
                  let uu____3533 =
                    let uu____3537 =
                      let uu____3538 =
                        let uu____3539 =
                          let uu____3540 = FStar_Unionfind.uvar_id uv in
                          FStar_All.pipe_left FStar_Util.string_of_int
                            uu____3540 in
                        FStar_Util.format1 "uvar_typing_%s" uu____3539 in
                      varops.mk_unique uu____3538 in
                    (t_has_k, (Some "Uvar typing"), uu____3537) in
                  FStar_SMTEncoding_Util.mkAssume uu____3533 in
                (ttm, (FStar_List.append decls [d])))
       | FStar_Syntax_Syntax.Tm_app uu____3546 ->
           let uu____3556 = FStar_Syntax_Util.head_and_args t0 in
           (match uu____3556 with
            | (head1,args_e) ->
                let uu____3584 =
                  let uu____3592 =
                    let uu____3593 = FStar_Syntax_Subst.compress head1 in
                    uu____3593.FStar_Syntax_Syntax.n in
                  (uu____3592, args_e) in
                (match uu____3584 with
                 | uu____3603 when head_redex env head1 ->
                     let uu____3611 = whnf env t in
                     encode_term uu____3611 env
                 | uu____3612 when is_arithmetic_primitive head1 args_e ->
                     encode_arith_term env head1 args_e
                 | (FStar_Syntax_Syntax.Tm_uinst
                    ({
                       FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                       FStar_Syntax_Syntax.tk = uu____3625;
                       FStar_Syntax_Syntax.pos = uu____3626;
                       FStar_Syntax_Syntax.vars = uu____3627;_},uu____3628),uu____3629::
                    (v1,uu____3631)::(v2,uu____3633)::[]) when
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Syntax_Const.lexcons_lid
                     ->
                     let uu____3671 = encode_term v1 env in
                     (match uu____3671 with
                      | (v11,decls1) ->
                          let uu____3678 = encode_term v2 env in
                          (match uu____3678 with
                           | (v21,decls2) ->
                               let uu____3685 =
                                 FStar_SMTEncoding_Util.mk_LexCons v11 v21 in
                               (uu____3685,
                                 (FStar_List.append decls1 decls2))))
                 | (FStar_Syntax_Syntax.Tm_fvar
                    fv,uu____3688::(v1,uu____3690)::(v2,uu____3692)::[]) when
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Syntax_Const.lexcons_lid
                     ->
                     let uu____3726 = encode_term v1 env in
                     (match uu____3726 with
                      | (v11,decls1) ->
                          let uu____3733 = encode_term v2 env in
                          (match uu____3733 with
                           | (v21,decls2) ->
                               let uu____3740 =
                                 FStar_SMTEncoding_Util.mk_LexCons v11 v21 in
                               (uu____3740,
                                 (FStar_List.append decls1 decls2))))
                 | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify
                    ),uu____3742) ->
                     let e0 =
                       let uu____3754 = FStar_List.hd args_e in
                       FStar_TypeChecker_Util.reify_body_with_arg env.tcenv
                         head1 uu____3754 in
                     ((let uu____3760 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug env.tcenv)
                           (FStar_Options.Other "SMTEncodingReify") in
                       if uu____3760
                       then
                         let uu____3761 =
                           FStar_Syntax_Print.term_to_string e0 in
                         FStar_Util.print1 "Result of normalization %s\n"
                           uu____3761
                       else ());
                      (let e =
                         let uu____3766 =
                           let uu____3767 =
                             FStar_TypeChecker_Util.remove_reify e0 in
                           let uu____3768 = FStar_List.tl args_e in
                           FStar_Syntax_Syntax.mk_Tm_app uu____3767
                             uu____3768 in
                         uu____3766 None t0.FStar_Syntax_Syntax.pos in
                       encode_term e env))
                 | (FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_reflect
                    uu____3777),(arg,uu____3779)::[]) -> encode_term arg env
                 | uu____3797 ->
                     let uu____3805 = encode_args args_e env in
                     (match uu____3805 with
                      | (args,decls) ->
                          let encode_partial_app ht_opt =
                            let uu____3838 = encode_term head1 env in
                            match uu____3838 with
                            | (head2,decls') ->
                                let app_tm = mk_Apply_args head2 args in
                                (match ht_opt with
                                 | None  ->
                                     (app_tm,
                                       (FStar_List.append decls decls'))
                                 | Some (formals,c) ->
                                     let uu____3877 =
                                       FStar_Util.first_N
                                         (FStar_List.length args_e) formals in
                                     (match uu____3877 with
                                      | (formals1,rest) ->
                                          let subst1 =
                                            FStar_List.map2
                                              (fun uu____3919  ->
                                                 fun uu____3920  ->
                                                   match (uu____3919,
                                                           uu____3920)
                                                   with
                                                   | ((bv,uu____3934),
                                                      (a,uu____3936)) ->
                                                       FStar_Syntax_Syntax.NT
                                                         (bv, a)) formals1
                                              args_e in
                                          let ty =
                                            let uu____3950 =
                                              FStar_Syntax_Util.arrow rest c in
                                            FStar_All.pipe_right uu____3950
                                              (FStar_Syntax_Subst.subst
                                                 subst1) in
                                          let uu____3955 =
                                            encode_term_pred None ty env
                                              app_tm in
                                          (match uu____3955 with
                                           | (has_type,decls'') ->
                                               let cvars =
                                                 FStar_SMTEncoding_Term.free_variables
                                                   has_type in
                                               let e_typing =
                                                 let uu____3965 =
                                                   let uu____3969 =
                                                     FStar_SMTEncoding_Util.mkForall
                                                       ([[has_type]], cvars,
                                                         has_type) in
                                                   let uu____3974 =
                                                     let uu____3975 =
                                                       let uu____3976 =
                                                         let uu____3977 =
                                                           FStar_SMTEncoding_Term.hash_of_term
                                                             app_tm in
                                                         FStar_Util.digest_of_string
                                                           uu____3977 in
                                                       Prims.strcat
                                                         "partial_app_typing_"
                                                         uu____3976 in
                                                     varops.mk_unique
                                                       uu____3975 in
                                                   (uu____3969,
                                                     (Some
                                                        "Partial app typing"),
                                                     uu____3974) in
                                                 FStar_SMTEncoding_Util.mkAssume
                                                   uu____3965 in
                                               (app_tm,
                                                 (FStar_List.append decls
                                                    (FStar_List.append decls'
                                                       (FStar_List.append
                                                          decls'' [e_typing]))))))) in
                          let encode_full_app fv =
                            let uu____3994 = lookup_free_var_sym env fv in
                            match uu____3994 with
                            | (fname,fuel_args) ->
                                let tm =
                                  FStar_SMTEncoding_Util.mkApp'
                                    (fname,
                                      (FStar_List.append fuel_args args)) in
                                (tm, decls) in
                          let head2 = FStar_Syntax_Subst.compress head1 in
                          let head_type =
                            match head2.FStar_Syntax_Syntax.n with
                            | FStar_Syntax_Syntax.Tm_uinst
                                ({
                                   FStar_Syntax_Syntax.n =
                                     FStar_Syntax_Syntax.Tm_name x;
                                   FStar_Syntax_Syntax.tk = uu____4017;
                                   FStar_Syntax_Syntax.pos = uu____4018;
                                   FStar_Syntax_Syntax.vars = uu____4019;_},uu____4020)
                                -> Some (x.FStar_Syntax_Syntax.sort)
                            | FStar_Syntax_Syntax.Tm_name x ->
                                Some (x.FStar_Syntax_Syntax.sort)
                            | FStar_Syntax_Syntax.Tm_uinst
                                ({
                                   FStar_Syntax_Syntax.n =
                                     FStar_Syntax_Syntax.Tm_fvar fv;
                                   FStar_Syntax_Syntax.tk = uu____4031;
                                   FStar_Syntax_Syntax.pos = uu____4032;
                                   FStar_Syntax_Syntax.vars = uu____4033;_},uu____4034)
                                ->
                                let uu____4039 =
                                  let uu____4040 =
                                    let uu____4043 =
                                      FStar_TypeChecker_Env.lookup_lid
                                        env.tcenv
                                        (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                                    FStar_All.pipe_right uu____4043
                                      FStar_Pervasives.fst in
                                  FStar_All.pipe_right uu____4040
                                    FStar_Pervasives.snd in
                                Some uu____4039
                            | FStar_Syntax_Syntax.Tm_fvar fv ->
                                let uu____4063 =
                                  let uu____4064 =
                                    let uu____4067 =
                                      FStar_TypeChecker_Env.lookup_lid
                                        env.tcenv
                                        (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                                    FStar_All.pipe_right uu____4067
                                      FStar_Pervasives.fst in
                                  FStar_All.pipe_right uu____4064
                                    FStar_Pervasives.snd in
                                Some uu____4063
                            | FStar_Syntax_Syntax.Tm_ascribed
                                (uu____4086,(FStar_Util.Inl t1,uu____4088),uu____4089)
                                -> Some t1
                            | FStar_Syntax_Syntax.Tm_ascribed
                                (uu____4127,(FStar_Util.Inr c,uu____4129),uu____4130)
                                -> Some (FStar_Syntax_Util.comp_result c)
                            | uu____4168 -> None in
                          (match head_type with
                           | None  -> encode_partial_app None
                           | Some head_type1 ->
                               let head_type2 =
                                 let uu____4188 =
                                   FStar_TypeChecker_Normalize.normalize_refinement
                                     [FStar_TypeChecker_Normalize.WHNF;
                                     FStar_TypeChecker_Normalize.EraseUniverses]
                                     env.tcenv head_type1 in
                                 FStar_All.pipe_left
                                   FStar_Syntax_Util.unrefine uu____4188 in
                               let uu____4189 =
                                 curried_arrow_formals_comp head_type2 in
                               (match uu____4189 with
                                | (formals,c) ->
                                    (match head2.FStar_Syntax_Syntax.n with
                                     | FStar_Syntax_Syntax.Tm_uinst
                                         ({
                                            FStar_Syntax_Syntax.n =
                                              FStar_Syntax_Syntax.Tm_fvar fv;
                                            FStar_Syntax_Syntax.tk =
                                              uu____4199;
                                            FStar_Syntax_Syntax.pos =
                                              uu____4200;
                                            FStar_Syntax_Syntax.vars =
                                              uu____4201;_},uu____4202)
                                         when
                                         (FStar_List.length formals) =
                                           (FStar_List.length args)
                                         ->
                                         encode_full_app
                                           fv.FStar_Syntax_Syntax.fv_name
                                     | FStar_Syntax_Syntax.Tm_fvar fv when
                                         (FStar_List.length formals) =
                                           (FStar_List.length args)
                                         ->
                                         encode_full_app
                                           fv.FStar_Syntax_Syntax.fv_name
                                     | uu____4226 ->
                                         if
                                           (FStar_List.length formals) >
                                             (FStar_List.length args)
                                         then
                                           encode_partial_app
                                             (Some (formals, c))
                                         else encode_partial_app None))))))
       | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
           let uu____4271 = FStar_Syntax_Subst.open_term' bs body in
           (match uu____4271 with
            | (bs1,body1,opening) ->
                let fallback uu____4286 =
                  let f = varops.fresh "Tm_abs" in
                  let decl =
                    FStar_SMTEncoding_Term.DeclFun
                      (f, [], FStar_SMTEncoding_Term.Term_sort,
                        (Some "Imprecise function encoding")) in
                  let uu____4291 =
                    FStar_SMTEncoding_Util.mkFreeV
                      (f, FStar_SMTEncoding_Term.Term_sort) in
                  (uu____4291, [decl]) in
                let is_impure lc =
                  match lc with
                  | FStar_Util.Inl lc1 ->
                      let uu____4302 =
                        FStar_Syntax_Util.is_pure_or_ghost_lcomp lc1 in
                      Prims.op_Negation uu____4302
                  | FStar_Util.Inr (eff,uu____4304) ->
                      let uu____4310 =
                        FStar_TypeChecker_Util.is_pure_or_ghost_effect
                          env.tcenv eff in
                      FStar_All.pipe_right uu____4310 Prims.op_Negation in
                let reify_comp_and_body env1 c body2 =
                  let reified_body =
                    FStar_TypeChecker_Util.reify_body env1.tcenv body2 in
                  let c1 =
                    match c with
                    | FStar_Util.Inl lc ->
                        let typ =
                          let uu____4355 = lc.FStar_Syntax_Syntax.comp () in
                          FStar_TypeChecker_Env.reify_comp
                            (let uu___136_4356 = env1.tcenv in
                             {
                               FStar_TypeChecker_Env.solver =
                                 (uu___136_4356.FStar_TypeChecker_Env.solver);
                               FStar_TypeChecker_Env.range =
                                 (uu___136_4356.FStar_TypeChecker_Env.range);
                               FStar_TypeChecker_Env.curmodule =
                                 (uu___136_4356.FStar_TypeChecker_Env.curmodule);
                               FStar_TypeChecker_Env.gamma =
                                 (uu___136_4356.FStar_TypeChecker_Env.gamma);
                               FStar_TypeChecker_Env.gamma_cache =
                                 (uu___136_4356.FStar_TypeChecker_Env.gamma_cache);
                               FStar_TypeChecker_Env.modules =
                                 (uu___136_4356.FStar_TypeChecker_Env.modules);
                               FStar_TypeChecker_Env.expected_typ =
                                 (uu___136_4356.FStar_TypeChecker_Env.expected_typ);
                               FStar_TypeChecker_Env.sigtab =
                                 (uu___136_4356.FStar_TypeChecker_Env.sigtab);
                               FStar_TypeChecker_Env.is_pattern =
                                 (uu___136_4356.FStar_TypeChecker_Env.is_pattern);
                               FStar_TypeChecker_Env.instantiate_imp =
                                 (uu___136_4356.FStar_TypeChecker_Env.instantiate_imp);
                               FStar_TypeChecker_Env.effects =
                                 (uu___136_4356.FStar_TypeChecker_Env.effects);
                               FStar_TypeChecker_Env.generalize =
                                 (uu___136_4356.FStar_TypeChecker_Env.generalize);
                               FStar_TypeChecker_Env.letrecs =
                                 (uu___136_4356.FStar_TypeChecker_Env.letrecs);
                               FStar_TypeChecker_Env.top_level =
                                 (uu___136_4356.FStar_TypeChecker_Env.top_level);
                               FStar_TypeChecker_Env.check_uvars =
                                 (uu___136_4356.FStar_TypeChecker_Env.check_uvars);
                               FStar_TypeChecker_Env.use_eq =
                                 (uu___136_4356.FStar_TypeChecker_Env.use_eq);
                               FStar_TypeChecker_Env.is_iface =
                                 (uu___136_4356.FStar_TypeChecker_Env.is_iface);
                               FStar_TypeChecker_Env.admit =
                                 (uu___136_4356.FStar_TypeChecker_Env.admit);
                               FStar_TypeChecker_Env.lax = true;
                               FStar_TypeChecker_Env.lax_universes =
                                 (uu___136_4356.FStar_TypeChecker_Env.lax_universes);
                               FStar_TypeChecker_Env.type_of =
                                 (uu___136_4356.FStar_TypeChecker_Env.type_of);
                               FStar_TypeChecker_Env.universe_of =
                                 (uu___136_4356.FStar_TypeChecker_Env.universe_of);
                               FStar_TypeChecker_Env.use_bv_sorts =
                                 (uu___136_4356.FStar_TypeChecker_Env.use_bv_sorts);
                               FStar_TypeChecker_Env.qname_and_index =
                                 (uu___136_4356.FStar_TypeChecker_Env.qname_and_index)
                             }) uu____4355 FStar_Syntax_Syntax.U_unknown in
                        let uu____4357 =
                          let uu____4358 = FStar_Syntax_Syntax.mk_Total typ in
                          FStar_Syntax_Util.lcomp_of_comp uu____4358 in
                        FStar_Util.Inl uu____4357
                    | FStar_Util.Inr (eff_name,uu____4365) -> c in
                  (c1, reified_body) in
                let codomain_eff lc =
                  match lc with
                  | FStar_Util.Inl lc1 ->
                      let uu____4396 =
                        let uu____4397 = lc1.FStar_Syntax_Syntax.comp () in
                        FStar_Syntax_Subst.subst_comp opening uu____4397 in
                      FStar_All.pipe_right uu____4396
                        (fun _0_31  -> Some _0_31)
                  | FStar_Util.Inr (eff,flags) ->
                      let new_uvar1 uu____4409 =
                        let uu____4410 =
                          FStar_TypeChecker_Rel.new_uvar
                            FStar_Range.dummyRange []
                            FStar_Syntax_Util.ktype0 in
                        FStar_All.pipe_right uu____4410 FStar_Pervasives.fst in
                      if
                        FStar_Ident.lid_equals eff
                          FStar_Syntax_Const.effect_Tot_lid
                      then
                        let uu____4418 =
                          let uu____4419 = new_uvar1 () in
                          FStar_Syntax_Syntax.mk_Total uu____4419 in
                        FStar_All.pipe_right uu____4418
                          (fun _0_32  -> Some _0_32)
                      else
                        if
                          FStar_Ident.lid_equals eff
                            FStar_Syntax_Const.effect_GTot_lid
                        then
                          (let uu____4423 =
                             let uu____4424 = new_uvar1 () in
                             FStar_Syntax_Syntax.mk_GTotal uu____4424 in
                           FStar_All.pipe_right uu____4423
                             (fun _0_33  -> Some _0_33))
                        else None in
                (match lopt with
                 | None  ->
                     ((let uu____4435 =
                         let uu____4436 =
                           FStar_Syntax_Print.term_to_string t0 in
                         FStar_Util.format1
                           "Losing precision when encoding a function literal: %s\n(Unnannotated abstraction in the compiler ?)"
                           uu____4436 in
                       FStar_Errors.warn t0.FStar_Syntax_Syntax.pos
                         uu____4435);
                      fallback ())
                 | Some lc ->
                     let lc1 = lc in
                     let uu____4451 =
                       (is_impure lc1) &&
                         (let uu____4452 =
                            FStar_TypeChecker_Env.is_reifiable env.tcenv lc1 in
                          Prims.op_Negation uu____4452) in
                     if uu____4451
                     then fallback ()
                     else
                       (let cache_size = FStar_Util.smap_size env.cache in
                        let uu____4457 = encode_binders None bs1 env in
                        match uu____4457 with
                        | (vars,guards,envbody,decls,uu____4472) ->
                            let uu____4479 =
                              let uu____4487 =
                                FStar_TypeChecker_Env.is_reifiable env.tcenv
                                  lc1 in
                              if uu____4487
                              then reify_comp_and_body envbody lc1 body1
                              else (lc1, body1) in
                            (match uu____4479 with
                             | (lc2,body2) ->
                                 let uu____4512 = encode_term body2 envbody in
                                 (match uu____4512 with
                                  | (body3,decls') ->
                                      let uu____4519 =
                                        let uu____4524 = codomain_eff lc2 in
                                        match uu____4524 with
                                        | None  -> (None, [])
                                        | Some c ->
                                            let tfun =
                                              FStar_Syntax_Util.arrow bs1 c in
                                            let uu____4536 =
                                              encode_term tfun env in
                                            (match uu____4536 with
                                             | (t1,decls1) ->
                                                 ((Some t1), decls1)) in
                                      (match uu____4519 with
                                       | (arrow_t_opt,decls'') ->
                                           let key_body =
                                             let uu____4555 =
                                               let uu____4561 =
                                                 let uu____4562 =
                                                   let uu____4565 =
                                                     FStar_SMTEncoding_Util.mk_and_l
                                                       guards in
                                                   (uu____4565, body3) in
                                                 FStar_SMTEncoding_Util.mkImp
                                                   uu____4562 in
                                               ([], vars, uu____4561) in
                                             FStar_SMTEncoding_Util.mkForall
                                               uu____4555 in
                                           let cvars =
                                             FStar_SMTEncoding_Term.free_variables
                                               key_body in
                                           let cvars1 =
                                             match arrow_t_opt with
                                             | None  -> cvars
                                             | Some t1 ->
                                                 let uu____4573 =
                                                   let uu____4575 =
                                                     FStar_SMTEncoding_Term.free_variables
                                                       t1 in
                                                   FStar_List.append
                                                     uu____4575 cvars in
                                                 FStar_Util.remove_dups
                                                   FStar_SMTEncoding_Term.fv_eq
                                                   uu____4573 in
                                           let tkey =
                                             FStar_SMTEncoding_Util.mkForall
                                               ([], cvars1, key_body) in
                                           let tkey_hash =
                                             FStar_SMTEncoding_Term.hash_of_term
                                               tkey in
                                           let uu____4586 =
                                             FStar_Util.smap_try_find
                                               env.cache tkey_hash in
                                           (match uu____4586 with
                                            | Some cache_entry ->
                                                let uu____4591 =
                                                  let uu____4592 =
                                                    let uu____4596 =
                                                      FStar_List.map
                                                        FStar_SMTEncoding_Util.mkFreeV
                                                        cvars1 in
                                                    ((cache_entry.cache_symbol_name),
                                                      uu____4596) in
                                                  FStar_SMTEncoding_Util.mkApp
                                                    uu____4592 in
                                                (uu____4591,
                                                  (FStar_List.append decls
                                                     (FStar_List.append
                                                        decls'
                                                        (FStar_List.append
                                                           decls''
                                                           (use_cache_entry
                                                              cache_entry)))))
                                            | None  ->
                                                let uu____4602 =
                                                  is_an_eta_expansion env
                                                    vars body3 in
                                                (match uu____4602 with
                                                 | Some t1 ->
                                                     let decls1 =
                                                       let uu____4609 =
                                                         let uu____4610 =
                                                           FStar_Util.smap_size
                                                             env.cache in
                                                         uu____4610 =
                                                           cache_size in
                                                       if uu____4609
                                                       then []
                                                       else
                                                         FStar_List.append
                                                           decls
                                                           (FStar_List.append
                                                              decls' decls'') in
                                                     (t1, decls1)
                                                 | None  ->
                                                     let cvar_sorts =
                                                       FStar_List.map
                                                         FStar_Pervasives.snd
                                                         cvars1 in
                                                     let fsym =
                                                       let module_name =
                                                         env.current_module_name in
                                                       let fsym =
                                                         let uu____4621 =
                                                           let uu____4622 =
                                                             FStar_Util.digest_of_string
                                                               tkey_hash in
                                                           Prims.strcat
                                                             "Tm_abs_"
                                                             uu____4622 in
                                                         varops.mk_unique
                                                           uu____4621 in
                                                       Prims.strcat
                                                         module_name
                                                         (Prims.strcat "_"
                                                            fsym) in
                                                     let fdecl =
                                                       FStar_SMTEncoding_Term.DeclFun
                                                         (fsym, cvar_sorts,
                                                           FStar_SMTEncoding_Term.Term_sort,
                                                           None) in
                                                     let f =
                                                       let uu____4627 =
                                                         let uu____4631 =
                                                           FStar_List.map
                                                             FStar_SMTEncoding_Util.mkFreeV
                                                             cvars1 in
                                                         (fsym, uu____4631) in
                                                       FStar_SMTEncoding_Util.mkApp
                                                         uu____4627 in
                                                     let app =
                                                       mk_Apply f vars in
                                                     let typing_f =
                                                       match arrow_t_opt with
                                                       | None  -> []
                                                       | Some t1 ->
                                                           let f_has_t =
                                                             FStar_SMTEncoding_Term.mk_HasTypeWithFuel
                                                               None f t1 in
                                                           let a_name =
                                                             Prims.strcat
                                                               "typing_" fsym in
                                                           let uu____4643 =
                                                             let uu____4644 =
                                                               let uu____4648
                                                                 =
                                                                 FStar_SMTEncoding_Util.mkForall
                                                                   ([[f]],
                                                                    cvars1,
                                                                    f_has_t) in
                                                               (uu____4648,
                                                                 (Some a_name),
                                                                 a_name) in
                                                             FStar_SMTEncoding_Util.mkAssume
                                                               uu____4644 in
                                                           [uu____4643] in
                                                     let interp_f =
                                                       let a_name =
                                                         Prims.strcat
                                                           "interpretation_"
                                                           fsym in
                                                       let uu____4656 =
                                                         let uu____4660 =
                                                           let uu____4661 =
                                                             let uu____4667 =
                                                               FStar_SMTEncoding_Util.mkEq
                                                                 (app, body3) in
                                                             ([[app]],
                                                               (FStar_List.append
                                                                  vars cvars1),
                                                               uu____4667) in
                                                           FStar_SMTEncoding_Util.mkForall
                                                             uu____4661 in
                                                         (uu____4660,
                                                           (Some a_name),
                                                           a_name) in
                                                       FStar_SMTEncoding_Util.mkAssume
                                                         uu____4656 in
                                                     let f_decls =
                                                       FStar_List.append
                                                         decls
                                                         (FStar_List.append
                                                            decls'
                                                            (FStar_List.append
                                                               decls''
                                                               (FStar_List.append
                                                                  (fdecl ::
                                                                  typing_f)
                                                                  [interp_f]))) in
                                                     ((let uu____4677 =
                                                         mk_cache_entry env
                                                           fsym cvar_sorts
                                                           f_decls in
                                                       FStar_Util.smap_add
                                                         env.cache tkey_hash
                                                         uu____4677);
                                                      (f, f_decls))))))))))
       | FStar_Syntax_Syntax.Tm_let
           ((uu____4679,{
                          FStar_Syntax_Syntax.lbname = FStar_Util.Inr
                            uu____4680;
                          FStar_Syntax_Syntax.lbunivs = uu____4681;
                          FStar_Syntax_Syntax.lbtyp = uu____4682;
                          FStar_Syntax_Syntax.lbeff = uu____4683;
                          FStar_Syntax_Syntax.lbdef = uu____4684;_}::uu____4685),uu____4686)
           -> failwith "Impossible: already handled by encoding of Sig_let"
       | FStar_Syntax_Syntax.Tm_let
           ((false
             ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inl x;
                FStar_Syntax_Syntax.lbunivs = uu____4704;
                FStar_Syntax_Syntax.lbtyp = t1;
                FStar_Syntax_Syntax.lbeff = uu____4706;
                FStar_Syntax_Syntax.lbdef = e1;_}::[]),e2)
           -> encode_let x t1 e1 e2 env encode_term
       | FStar_Syntax_Syntax.Tm_let uu____4722 ->
           (FStar_Errors.diag t0.FStar_Syntax_Syntax.pos
              "Non-top-level recursive functions are not yet fully encoded to the SMT solver; you may not be able to prove some facts";
            (let e = varops.fresh "let-rec" in
             let decl_e =
               FStar_SMTEncoding_Term.DeclFun
                 (e, [], FStar_SMTEncoding_Term.Term_sort, None) in
             let uu____4735 =
               FStar_SMTEncoding_Util.mkFreeV
                 (e, FStar_SMTEncoding_Term.Term_sort) in
             (uu____4735, [decl_e])))
       | FStar_Syntax_Syntax.Tm_match (e,pats) ->
           encode_match e pats FStar_SMTEncoding_Term.mk_Term_unit env
             encode_term)
and encode_let:
  FStar_Syntax_Syntax.bv ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.term ->
        FStar_Syntax_Syntax.term ->
          env_t ->
            (FStar_Syntax_Syntax.term ->
               env_t ->
                 (FStar_SMTEncoding_Term.term*
                   FStar_SMTEncoding_Term.decls_t))
              ->
              (FStar_SMTEncoding_Term.term* FStar_SMTEncoding_Term.decls_t)
  =
  fun x  ->
    fun t1  ->
      fun e1  ->
        fun e2  ->
          fun env  ->
            fun encode_body  ->
              let uu____4777 = encode_term e1 env in
              match uu____4777 with
              | (ee1,decls1) ->
                  let uu____4784 =
                    FStar_Syntax_Subst.open_term [(x, None)] e2 in
                  (match uu____4784 with
                   | (xs,e21) ->
                       let uu____4798 = FStar_List.hd xs in
                       (match uu____4798 with
                        | (x1,uu____4806) ->
                            let env' = push_term_var env x1 ee1 in
                            let uu____4808 = encode_body e21 env' in
                            (match uu____4808 with
                             | (ee2,decls2) ->
                                 (ee2, (FStar_List.append decls1 decls2)))))
and encode_match:
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.branch Prims.list ->
      FStar_SMTEncoding_Term.term ->
        env_t ->
          (FStar_Syntax_Syntax.term ->
             env_t ->
               (FStar_SMTEncoding_Term.term* FStar_SMTEncoding_Term.decls_t))
            -> (FStar_SMTEncoding_Term.term* FStar_SMTEncoding_Term.decls_t)
  =
  fun e  ->
    fun pats  ->
      fun default_case  ->
        fun env  ->
          fun encode_br  ->
            let uu____4830 =
              let uu____4834 =
                let uu____4835 =
                  FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown None
                    FStar_Range.dummyRange in
                FStar_Syntax_Syntax.null_bv uu____4835 in
              gen_term_var env uu____4834 in
            match uu____4830 with
            | (scrsym,scr',env1) ->
                let uu____4845 = encode_term e env1 in
                (match uu____4845 with
                 | (scr,decls) ->
                     let uu____4852 =
                       let encode_branch b uu____4868 =
                         match uu____4868 with
                         | (else_case,decls1) ->
                             let uu____4879 =
                               FStar_Syntax_Subst.open_branch b in
                             (match uu____4879 with
                              | (p,w,br) ->
                                  let uu____4900 = encode_pat env1 p in
                                  (match uu____4900 with
                                   | (env0,pattern) ->
                                       let guard = pattern.guard scr' in
                                       let projections =
                                         pattern.projections scr' in
                                       let env2 =
                                         FStar_All.pipe_right projections
                                           (FStar_List.fold_left
                                              (fun env2  ->
                                                 fun uu____4920  ->
                                                   match uu____4920 with
                                                   | (x,t) ->
                                                       push_term_var env2 x t)
                                              env1) in
                                       let uu____4925 =
                                         match w with
                                         | None  -> (guard, [])
                                         | Some w1 ->
                                             let uu____4940 =
                                               encode_term w1 env2 in
                                             (match uu____4940 with
                                              | (w2,decls2) ->
                                                  let uu____4948 =
                                                    let uu____4949 =
                                                      let uu____4952 =
                                                        let uu____4953 =
                                                          let uu____4956 =
                                                            FStar_SMTEncoding_Term.boxBool
                                                              FStar_SMTEncoding_Util.mkTrue in
                                                          (w2, uu____4956) in
                                                        FStar_SMTEncoding_Util.mkEq
                                                          uu____4953 in
                                                      (guard, uu____4952) in
                                                    FStar_SMTEncoding_Util.mkAnd
                                                      uu____4949 in
                                                  (uu____4948, decls2)) in
                                       (match uu____4925 with
                                        | (guard1,decls2) ->
                                            let uu____4964 =
                                              encode_br br env2 in
                                            (match uu____4964 with
                                             | (br1,decls3) ->
                                                 let uu____4972 =
                                                   FStar_SMTEncoding_Util.mkITE
                                                     (guard1, br1, else_case) in
                                                 (uu____4972,
                                                   (FStar_List.append decls1
                                                      (FStar_List.append
                                                         decls2 decls3))))))) in
                       FStar_List.fold_right encode_branch pats
                         (default_case, decls) in
                     (match uu____4852 with
                      | (match_tm,decls1) ->
                          let uu____4983 =
                            FStar_SMTEncoding_Term.mkLet'
                              ([((scrsym, FStar_SMTEncoding_Term.Term_sort),
                                  scr)], match_tm) FStar_Range.dummyRange in
                          (uu____4983, decls1)))
and encode_pat: env_t -> FStar_Syntax_Syntax.pat -> (env_t* pattern) =
  fun env  ->
    fun pat  ->
      (let uu____5005 =
         FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low in
       if uu____5005
       then
         let uu____5006 = FStar_Syntax_Print.pat_to_string pat in
         FStar_Util.print1 "Encoding pattern %s\n" uu____5006
       else ());
      (let uu____5008 = FStar_TypeChecker_Util.decorated_pattern_as_term pat in
       match uu____5008 with
       | (vars,pat_term) ->
           let uu____5018 =
             FStar_All.pipe_right vars
               (FStar_List.fold_left
                  (fun uu____5041  ->
                     fun v1  ->
                       match uu____5041 with
                       | (env1,vars1) ->
                           let uu____5069 = gen_term_var env1 v1 in
                           (match uu____5069 with
                            | (xx,uu____5081,env2) ->
                                (env2,
                                  ((v1,
                                     (xx, FStar_SMTEncoding_Term.Term_sort))
                                  :: vars1)))) (env, [])) in
           (match uu____5018 with
            | (env1,vars1) ->
                let rec mk_guard pat1 scrutinee =
                  match pat1.FStar_Syntax_Syntax.v with
                  | FStar_Syntax_Syntax.Pat_var uu____5128 ->
                      FStar_SMTEncoding_Util.mkTrue
                  | FStar_Syntax_Syntax.Pat_wild uu____5129 ->
                      FStar_SMTEncoding_Util.mkTrue
                  | FStar_Syntax_Syntax.Pat_dot_term uu____5130 ->
                      FStar_SMTEncoding_Util.mkTrue
                  | FStar_Syntax_Syntax.Pat_constant c ->
                      let uu____5136 =
                        let uu____5139 = encode_const c in
                        (scrutinee, uu____5139) in
                      FStar_SMTEncoding_Util.mkEq uu____5136
                  | FStar_Syntax_Syntax.Pat_cons (f,args) ->
                      let is_f =
                        let tc_name =
                          FStar_TypeChecker_Env.typ_of_datacon env1.tcenv
                            (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                        let uu____5158 =
                          FStar_TypeChecker_Env.datacons_of_typ env1.tcenv
                            tc_name in
                        match uu____5158 with
                        | (uu____5162,uu____5163::[]) ->
                            FStar_SMTEncoding_Util.mkTrue
                        | uu____5165 ->
                            mk_data_tester env1
                              (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                              scrutinee in
                      let sub_term_guards =
                        FStar_All.pipe_right args
                          (FStar_List.mapi
                             (fun i  ->
                                fun uu____5186  ->
                                  match uu____5186 with
                                  | (arg,uu____5192) ->
                                      let proj =
                                        primitive_projector_by_pos env1.tcenv
                                          (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                          i in
                                      let uu____5202 =
                                        FStar_SMTEncoding_Util.mkApp
                                          (proj, [scrutinee]) in
                                      mk_guard arg uu____5202)) in
                      FStar_SMTEncoding_Util.mk_and_l (is_f ::
                        sub_term_guards) in
                let rec mk_projections pat1 scrutinee =
                  match pat1.FStar_Syntax_Syntax.v with
                  | FStar_Syntax_Syntax.Pat_dot_term (x,uu____5222) ->
                      [(x, scrutinee)]
                  | FStar_Syntax_Syntax.Pat_var x -> [(x, scrutinee)]
                  | FStar_Syntax_Syntax.Pat_wild x -> [(x, scrutinee)]
                  | FStar_Syntax_Syntax.Pat_constant uu____5241 -> []
                  | FStar_Syntax_Syntax.Pat_cons (f,args) ->
                      let uu____5256 =
                        FStar_All.pipe_right args
                          (FStar_List.mapi
                             (fun i  ->
                                fun uu____5278  ->
                                  match uu____5278 with
                                  | (arg,uu____5287) ->
                                      let proj =
                                        primitive_projector_by_pos env1.tcenv
                                          (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                          i in
                                      let uu____5297 =
                                        FStar_SMTEncoding_Util.mkApp
                                          (proj, [scrutinee]) in
                                      mk_projections arg uu____5297)) in
                      FStar_All.pipe_right uu____5256 FStar_List.flatten in
                let pat_term1 uu____5313 = encode_term pat_term env1 in
                let pattern =
                  {
                    pat_vars = vars1;
                    pat_term = pat_term1;
                    guard = (mk_guard pat);
                    projections = (mk_projections pat)
                  } in
                (env1, pattern)))
and encode_args:
  FStar_Syntax_Syntax.args ->
    env_t ->
      (FStar_SMTEncoding_Term.term Prims.list*
        FStar_SMTEncoding_Term.decls_t)
  =
  fun l  ->
    fun env  ->
      let uu____5320 =
        FStar_All.pipe_right l
          (FStar_List.fold_left
             (fun uu____5335  ->
                fun uu____5336  ->
                  match (uu____5335, uu____5336) with
                  | ((tms,decls),(t,uu____5356)) ->
                      let uu____5367 = encode_term t env in
                      (match uu____5367 with
                       | (t1,decls') ->
                           ((t1 :: tms), (FStar_List.append decls decls'))))
             ([], [])) in
      match uu____5320 with | (l1,decls) -> ((FStar_List.rev l1), decls)
and encode_function_type_as_formula:
  FStar_Syntax_Syntax.typ ->
    env_t -> (FStar_SMTEncoding_Term.term* FStar_SMTEncoding_Term.decls_t)
  =
  fun t  ->
    fun env  ->
      let list_elements1 e =
        let uu____5401 = FStar_Syntax_Util.list_elements e in
        match uu____5401 with
        | Some l -> l
        | None  ->
            (FStar_Errors.warn e.FStar_Syntax_Syntax.pos
               "SMT pattern is not a list literal; ignoring the pattern";
             []) in
      let one_pat p =
        let uu____5416 =
          let uu____5426 = FStar_Syntax_Util.unmeta p in
          FStar_All.pipe_right uu____5426 FStar_Syntax_Util.head_and_args in
        match uu____5416 with
        | (head1,args) ->
            let uu____5454 =
              let uu____5462 =
                let uu____5463 = FStar_Syntax_Util.un_uinst head1 in
                uu____5463.FStar_Syntax_Syntax.n in
              (uu____5462, args) in
            (match uu____5454 with
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(uu____5474,uu____5475)::(e,uu____5477)::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Syntax_Const.smtpat_lid
                 -> e
             | (FStar_Syntax_Syntax.Tm_fvar fv,(e,uu____5505)::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Syntax_Const.smtpatT_lid
                 -> e
             | uu____5523 -> failwith "Unexpected pattern term") in
      let lemma_pats p =
        let elts = list_elements1 p in
        let smt_pat_or t1 =
          let uu____5550 =
            let uu____5560 = FStar_Syntax_Util.unmeta t1 in
            FStar_All.pipe_right uu____5560 FStar_Syntax_Util.head_and_args in
          match uu____5550 with
          | (head1,args) ->
              let uu____5589 =
                let uu____5597 =
                  let uu____5598 = FStar_Syntax_Util.un_uinst head1 in
                  uu____5598.FStar_Syntax_Syntax.n in
                (uu____5597, args) in
              (match uu____5589 with
               | (FStar_Syntax_Syntax.Tm_fvar fv,(e,uu____5611)::[]) when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Syntax_Const.smtpatOr_lid
                   -> Some e
               | uu____5631 -> None) in
        match elts with
        | t1::[] ->
            let uu____5646 = smt_pat_or t1 in
            (match uu____5646 with
             | Some e ->
                 let uu____5659 = list_elements1 e in
                 FStar_All.pipe_right uu____5659
                   (FStar_List.map
                      (fun branch1  ->
                         let uu____5670 = list_elements1 branch1 in
                         FStar_All.pipe_right uu____5670
                           (FStar_List.map one_pat)))
             | uu____5678 ->
                 let uu____5682 =
                   FStar_All.pipe_right elts (FStar_List.map one_pat) in
                 [uu____5682])
        | uu____5698 ->
            let uu____5700 =
              FStar_All.pipe_right elts (FStar_List.map one_pat) in
            [uu____5700] in
      let uu____5716 =
        let uu____5729 =
          let uu____5730 = FStar_Syntax_Subst.compress t in
          uu____5730.FStar_Syntax_Syntax.n in
        match uu____5729 with
        | FStar_Syntax_Syntax.Tm_arrow (binders,c) ->
            let uu____5757 = FStar_Syntax_Subst.open_comp binders c in
            (match uu____5757 with
             | (binders1,c1) ->
                 (match c1.FStar_Syntax_Syntax.n with
                  | FStar_Syntax_Syntax.Comp
                      { FStar_Syntax_Syntax.comp_univs = uu____5786;
                        FStar_Syntax_Syntax.effect_name = uu____5787;
                        FStar_Syntax_Syntax.result_typ = uu____5788;
                        FStar_Syntax_Syntax.effect_args =
                          (pre,uu____5790)::(post,uu____5792)::(pats,uu____5794)::[];
                        FStar_Syntax_Syntax.flags = uu____5795;_}
                      ->
                      let uu____5827 = lemma_pats pats in
                      (binders1, pre, post, uu____5827)
                  | uu____5840 -> failwith "impos"))
        | uu____5853 -> failwith "Impos" in
      match uu____5716 with
      | (binders,pre,post,patterns) ->
          let env1 =
            let uu___137_5889 = env in
            {
              bindings = (uu___137_5889.bindings);
              depth = (uu___137_5889.depth);
              tcenv = (uu___137_5889.tcenv);
              warn = (uu___137_5889.warn);
              cache = (uu___137_5889.cache);
              nolabels = (uu___137_5889.nolabels);
              use_zfuel_name = true;
              encode_non_total_function_typ =
                (uu___137_5889.encode_non_total_function_typ);
              current_module_name = (uu___137_5889.current_module_name)
            } in
          let uu____5890 = encode_binders None binders env1 in
          (match uu____5890 with
           | (vars,guards,env2,decls,uu____5905) ->
               let uu____5912 =
                 let uu____5919 =
                   FStar_All.pipe_right patterns
                     (FStar_List.map
                        (fun branch1  ->
                           let uu____5941 =
                             let uu____5946 =
                               FStar_All.pipe_right branch1
                                 (FStar_List.map
                                    (fun t1  -> encode_term t1 env2)) in
                             FStar_All.pipe_right uu____5946 FStar_List.unzip in
                           match uu____5941 with
                           | (pats,decls1) -> (pats, decls1))) in
                 FStar_All.pipe_right uu____5919 FStar_List.unzip in
               (match uu____5912 with
                | (pats,decls') ->
                    let decls'1 = FStar_List.flatten decls' in
                    let env3 =
                      let uu___138_6004 = env2 in
                      {
                        bindings = (uu___138_6004.bindings);
                        depth = (uu___138_6004.depth);
                        tcenv = (uu___138_6004.tcenv);
                        warn = (uu___138_6004.warn);
                        cache = (uu___138_6004.cache);
                        nolabels = true;
                        use_zfuel_name = (uu___138_6004.use_zfuel_name);
                        encode_non_total_function_typ =
                          (uu___138_6004.encode_non_total_function_typ);
                        current_module_name =
                          (uu___138_6004.current_module_name)
                      } in
                    let uu____6005 =
                      let uu____6008 = FStar_Syntax_Util.unmeta pre in
                      encode_formula uu____6008 env3 in
                    (match uu____6005 with
                     | (pre1,decls'') ->
                         let uu____6013 =
                           let uu____6016 = FStar_Syntax_Util.unmeta post in
                           encode_formula uu____6016 env3 in
                         (match uu____6013 with
                          | (post1,decls''') ->
                              let decls1 =
                                FStar_List.append decls
                                  (FStar_List.append
                                     (FStar_List.flatten decls'1)
                                     (FStar_List.append decls'' decls''')) in
                              let uu____6023 =
                                let uu____6024 =
                                  let uu____6030 =
                                    let uu____6031 =
                                      let uu____6034 =
                                        FStar_SMTEncoding_Util.mk_and_l (pre1
                                          :: guards) in
                                      (uu____6034, post1) in
                                    FStar_SMTEncoding_Util.mkImp uu____6031 in
                                  (pats, vars, uu____6030) in
                                FStar_SMTEncoding_Util.mkForall uu____6024 in
                              (uu____6023, decls1)))))
and encode_formula:
  FStar_Syntax_Syntax.typ ->
    env_t -> (FStar_SMTEncoding_Term.term* FStar_SMTEncoding_Term.decls_t)
  =
  fun phi  ->
    fun env  ->
      let debug1 phi1 =
        let uu____6047 =
          FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv)
            (FStar_Options.Other "SMTEncoding") in
        if uu____6047
        then
          let uu____6048 = FStar_Syntax_Print.tag_of_term phi1 in
          let uu____6049 = FStar_Syntax_Print.term_to_string phi1 in
          FStar_Util.print2 "Formula (%s)  %s\n" uu____6048 uu____6049
        else () in
      let enc f r l =
        let uu____6076 =
          FStar_Util.fold_map
            (fun decls  ->
               fun x  ->
                 let uu____6089 = encode_term (fst x) env in
                 match uu____6089 with
                 | (t,decls') -> ((FStar_List.append decls decls'), t)) [] l in
        match uu____6076 with
        | (decls,args) ->
            let uu____6106 =
              let uu___139_6107 = f args in
              {
                FStar_SMTEncoding_Term.tm =
                  (uu___139_6107.FStar_SMTEncoding_Term.tm);
                FStar_SMTEncoding_Term.freevars =
                  (uu___139_6107.FStar_SMTEncoding_Term.freevars);
                FStar_SMTEncoding_Term.rng = r
              } in
            (uu____6106, decls) in
      let const_op f r uu____6126 = let uu____6129 = f r in (uu____6129, []) in
      let un_op f l =
        let uu____6145 = FStar_List.hd l in FStar_All.pipe_left f uu____6145 in
      let bin_op f uu___111_6158 =
        match uu___111_6158 with
        | t1::t2::[] -> f (t1, t2)
        | uu____6166 -> failwith "Impossible" in
      let enc_prop_c f r l =
        let uu____6193 =
          FStar_Util.fold_map
            (fun decls  ->
               fun uu____6202  ->
                 match uu____6202 with
                 | (t,uu____6210) ->
                     let uu____6211 = encode_formula t env in
                     (match uu____6211 with
                      | (phi1,decls') ->
                          ((FStar_List.append decls decls'), phi1))) [] l in
        match uu____6193 with
        | (decls,phis) ->
            let uu____6228 =
              let uu___140_6229 = f phis in
              {
                FStar_SMTEncoding_Term.tm =
                  (uu___140_6229.FStar_SMTEncoding_Term.tm);
                FStar_SMTEncoding_Term.freevars =
                  (uu___140_6229.FStar_SMTEncoding_Term.freevars);
                FStar_SMTEncoding_Term.rng = r
              } in
            (uu____6228, decls) in
      let eq_op r uu___112_6245 =
        match uu___112_6245 with
        | uu____6248::e1::e2::[] ->
            let uu____6279 = enc (bin_op FStar_SMTEncoding_Util.mkEq) in
            uu____6279 r [e1; e2]
        | uu____6298::uu____6299::e1::e2::[] ->
            let uu____6338 = enc (bin_op FStar_SMTEncoding_Util.mkEq) in
            uu____6338 r [e1; e2]
        | l ->
            let uu____6358 = enc (bin_op FStar_SMTEncoding_Util.mkEq) in
            uu____6358 r l in
      let mk_imp1 r uu___113_6377 =
        match uu___113_6377 with
        | (lhs,uu____6381)::(rhs,uu____6383)::[] ->
            let uu____6404 = encode_formula rhs env in
            (match uu____6404 with
             | (l1,decls1) ->
                 (match l1.FStar_SMTEncoding_Term.tm with
                  | FStar_SMTEncoding_Term.App
                      (FStar_SMTEncoding_Term.TrueOp ,uu____6413) ->
                      (l1, decls1)
                  | uu____6416 ->
                      let uu____6417 = encode_formula lhs env in
                      (match uu____6417 with
                       | (l2,decls2) ->
                           let uu____6424 =
                             FStar_SMTEncoding_Term.mkImp (l2, l1) r in
                           (uu____6424, (FStar_List.append decls1 decls2)))))
        | uu____6426 -> failwith "impossible" in
      let mk_ite r uu___114_6441 =
        match uu___114_6441 with
        | (guard,uu____6445)::(_then,uu____6447)::(_else,uu____6449)::[] ->
            let uu____6478 = encode_formula guard env in
            (match uu____6478 with
             | (g,decls1) ->
                 let uu____6485 = encode_formula _then env in
                 (match uu____6485 with
                  | (t,decls2) ->
                      let uu____6492 = encode_formula _else env in
                      (match uu____6492 with
                       | (e,decls3) ->
                           let res = FStar_SMTEncoding_Term.mkITE (g, t, e) r in
                           (res,
                             (FStar_List.append decls1
                                (FStar_List.append decls2 decls3))))))
        | uu____6501 -> failwith "impossible" in
      let unboxInt_l f l =
        let uu____6520 = FStar_List.map FStar_SMTEncoding_Term.unboxInt l in
        f uu____6520 in
      let connectives =
        let uu____6532 =
          let uu____6541 = enc_prop_c (bin_op FStar_SMTEncoding_Util.mkAnd) in
          (FStar_Syntax_Const.and_lid, uu____6541) in
        let uu____6554 =
          let uu____6564 =
            let uu____6573 = enc_prop_c (bin_op FStar_SMTEncoding_Util.mkOr) in
            (FStar_Syntax_Const.or_lid, uu____6573) in
          let uu____6586 =
            let uu____6596 =
              let uu____6606 =
                let uu____6615 =
                  enc_prop_c (bin_op FStar_SMTEncoding_Util.mkIff) in
                (FStar_Syntax_Const.iff_lid, uu____6615) in
              let uu____6628 =
                let uu____6638 =
                  let uu____6648 =
                    let uu____6657 =
                      enc_prop_c (un_op FStar_SMTEncoding_Util.mkNot) in
                    (FStar_Syntax_Const.not_lid, uu____6657) in
                  [uu____6648;
                  (FStar_Syntax_Const.eq2_lid, eq_op);
                  (FStar_Syntax_Const.eq3_lid, eq_op);
                  (FStar_Syntax_Const.true_lid,
                    (const_op FStar_SMTEncoding_Term.mkTrue));
                  (FStar_Syntax_Const.false_lid,
                    (const_op FStar_SMTEncoding_Term.mkFalse))] in
                (FStar_Syntax_Const.ite_lid, mk_ite) :: uu____6638 in
              uu____6606 :: uu____6628 in
            (FStar_Syntax_Const.imp_lid, mk_imp1) :: uu____6596 in
          uu____6564 :: uu____6586 in
        uu____6532 :: uu____6554 in
      let rec fallback phi1 =
        match phi1.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_meta
            (phi',FStar_Syntax_Syntax.Meta_labeled (msg,r,b)) ->
            let uu____6819 = encode_formula phi' env in
            (match uu____6819 with
             | (phi2,decls) ->
                 let uu____6826 =
                   FStar_SMTEncoding_Term.mk
                     (FStar_SMTEncoding_Term.Labeled (phi2, msg, r)) r in
                 (uu____6826, decls))
        | FStar_Syntax_Syntax.Tm_meta uu____6827 ->
            let uu____6832 = FStar_Syntax_Util.unmeta phi1 in
            encode_formula uu____6832 env
        | FStar_Syntax_Syntax.Tm_match (e,pats) ->
            let uu____6861 =
              encode_match e pats FStar_SMTEncoding_Util.mkFalse env
                encode_formula in
            (match uu____6861 with | (t,decls) -> (t, decls))
        | FStar_Syntax_Syntax.Tm_let
            ((false
              ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inl x;
                 FStar_Syntax_Syntax.lbunivs = uu____6869;
                 FStar_Syntax_Syntax.lbtyp = t1;
                 FStar_Syntax_Syntax.lbeff = uu____6871;
                 FStar_Syntax_Syntax.lbdef = e1;_}::[]),e2)
            ->
            let uu____6887 = encode_let x t1 e1 e2 env encode_formula in
            (match uu____6887 with | (t,decls) -> (t, decls))
        | FStar_Syntax_Syntax.Tm_app (head1,args) ->
            let head2 = FStar_Syntax_Util.un_uinst head1 in
            (match ((head2.FStar_Syntax_Syntax.n), args) with
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,uu____6919::(x,uu____6921)::(t,uu____6923)::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Syntax_Const.has_type_lid
                 ->
                 let uu____6957 = encode_term x env in
                 (match uu____6957 with
                  | (x1,decls) ->
                      let uu____6964 = encode_term t env in
                      (match uu____6964 with
                       | (t1,decls') ->
                           let uu____6971 =
                             FStar_SMTEncoding_Term.mk_HasType x1 t1 in
                           (uu____6971, (FStar_List.append decls decls'))))
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(r,uu____6975)::(msg,uu____6977)::(phi2,uu____6979)::[])
                 when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Syntax_Const.labeled_lid
                 ->
                 let uu____7013 =
                   let uu____7016 =
                     let uu____7017 = FStar_Syntax_Subst.compress r in
                     uu____7017.FStar_Syntax_Syntax.n in
                   let uu____7020 =
                     let uu____7021 = FStar_Syntax_Subst.compress msg in
                     uu____7021.FStar_Syntax_Syntax.n in
                   (uu____7016, uu____7020) in
                 (match uu____7013 with
                  | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range
                     r1),FStar_Syntax_Syntax.Tm_constant
                     (FStar_Const.Const_string (s,uu____7028))) ->
                      let phi3 =
                        (FStar_Syntax_Syntax.mk
                           (FStar_Syntax_Syntax.Tm_meta
                              (phi2,
                                (FStar_Syntax_Syntax.Meta_labeled
                                   ((FStar_Util.string_of_unicode s), r1,
                                     false))))) None r1 in
                      fallback phi3
                  | uu____7044 -> fallback phi2)
             | uu____7047 when head_redex env head2 ->
                 let uu____7055 = whnf env phi1 in
                 encode_formula uu____7055 env
             | uu____7056 ->
                 let uu____7064 = encode_term phi1 env in
                 (match uu____7064 with
                  | (tt,decls) ->
                      let uu____7071 =
                        FStar_SMTEncoding_Term.mk_Valid
                          (let uu___141_7072 = tt in
                           {
                             FStar_SMTEncoding_Term.tm =
                               (uu___141_7072.FStar_SMTEncoding_Term.tm);
                             FStar_SMTEncoding_Term.freevars =
                               (uu___141_7072.FStar_SMTEncoding_Term.freevars);
                             FStar_SMTEncoding_Term.rng =
                               (phi1.FStar_Syntax_Syntax.pos)
                           }) in
                      (uu____7071, decls)))
        | uu____7075 ->
            let uu____7076 = encode_term phi1 env in
            (match uu____7076 with
             | (tt,decls) ->
                 let uu____7083 =
                   FStar_SMTEncoding_Term.mk_Valid
                     (let uu___142_7084 = tt in
                      {
                        FStar_SMTEncoding_Term.tm =
                          (uu___142_7084.FStar_SMTEncoding_Term.tm);
                        FStar_SMTEncoding_Term.freevars =
                          (uu___142_7084.FStar_SMTEncoding_Term.freevars);
                        FStar_SMTEncoding_Term.rng =
                          (phi1.FStar_Syntax_Syntax.pos)
                      }) in
                 (uu____7083, decls)) in
      let encode_q_body env1 bs ps body =
        let uu____7111 = encode_binders None bs env1 in
        match uu____7111 with
        | (vars,guards,env2,decls,uu____7133) ->
            let uu____7140 =
              let uu____7147 =
                FStar_All.pipe_right ps
                  (FStar_List.map
                     (fun p  ->
                        let uu____7170 =
                          let uu____7175 =
                            FStar_All.pipe_right p
                              (FStar_List.map
                                 (fun uu____7189  ->
                                    match uu____7189 with
                                    | (t,uu____7195) ->
                                        encode_term t
                                          (let uu___143_7196 = env2 in
                                           {
                                             bindings =
                                               (uu___143_7196.bindings);
                                             depth = (uu___143_7196.depth);
                                             tcenv = (uu___143_7196.tcenv);
                                             warn = (uu___143_7196.warn);
                                             cache = (uu___143_7196.cache);
                                             nolabels =
                                               (uu___143_7196.nolabels);
                                             use_zfuel_name = true;
                                             encode_non_total_function_typ =
                                               (uu___143_7196.encode_non_total_function_typ);
                                             current_module_name =
                                               (uu___143_7196.current_module_name)
                                           }))) in
                          FStar_All.pipe_right uu____7175 FStar_List.unzip in
                        match uu____7170 with
                        | (p1,decls1) -> (p1, (FStar_List.flatten decls1)))) in
              FStar_All.pipe_right uu____7147 FStar_List.unzip in
            (match uu____7140 with
             | (pats,decls') ->
                 let uu____7248 = encode_formula body env2 in
                 (match uu____7248 with
                  | (body1,decls'') ->
                      let guards1 =
                        match pats with
                        | ({
                             FStar_SMTEncoding_Term.tm =
                               FStar_SMTEncoding_Term.App
                               (FStar_SMTEncoding_Term.Var gf,p::[]);
                             FStar_SMTEncoding_Term.freevars = uu____7267;
                             FStar_SMTEncoding_Term.rng = uu____7268;_}::[])::[]
                            when
                            (FStar_Ident.text_of_lid
                               FStar_Syntax_Const.guard_free)
                              = gf
                            -> []
                        | uu____7276 -> guards in
                      let uu____7279 =
                        FStar_SMTEncoding_Util.mk_and_l guards1 in
                      (vars, pats, uu____7279, body1,
                        (FStar_List.append decls
                           (FStar_List.append (FStar_List.flatten decls')
                              decls''))))) in
      debug1 phi;
      (let phi1 = FStar_Syntax_Util.unascribe phi in
       let check_pattern_vars vars pats =
         let pats1 =
           FStar_All.pipe_right pats
             (FStar_List.map
                (fun uu____7313  ->
                   match uu____7313 with
                   | (x,uu____7317) ->
                       FStar_TypeChecker_Normalize.normalize
                         [FStar_TypeChecker_Normalize.Beta;
                         FStar_TypeChecker_Normalize.AllowUnboundUniverses;
                         FStar_TypeChecker_Normalize.EraseUniverses]
                         env.tcenv x)) in
         match pats1 with
         | [] -> ()
         | hd1::tl1 ->
             let pat_vars =
               let uu____7323 = FStar_Syntax_Free.names hd1 in
               FStar_List.fold_left
                 (fun out  ->
                    fun x  ->
                      let uu____7329 = FStar_Syntax_Free.names x in
                      FStar_Util.set_union out uu____7329) uu____7323 tl1 in
             let uu____7331 =
               FStar_All.pipe_right vars
                 (FStar_Util.find_opt
                    (fun uu____7343  ->
                       match uu____7343 with
                       | (b,uu____7347) ->
                           let uu____7348 = FStar_Util.set_mem b pat_vars in
                           Prims.op_Negation uu____7348)) in
             (match uu____7331 with
              | None  -> ()
              | Some (x,uu____7352) ->
                  let pos =
                    FStar_List.fold_left
                      (fun out  ->
                         fun t  ->
                           FStar_Range.union_ranges out
                             t.FStar_Syntax_Syntax.pos)
                      hd1.FStar_Syntax_Syntax.pos tl1 in
                  let uu____7362 =
                    let uu____7363 = FStar_Syntax_Print.bv_to_string x in
                    FStar_Util.format1
                      "SMT pattern misses at least one bound variable: %s"
                      uu____7363 in
                  FStar_Errors.warn pos uu____7362) in
       let uu____7364 = FStar_Syntax_Util.destruct_typ_as_formula phi1 in
       match uu____7364 with
       | None  -> fallback phi1
       | Some (FStar_Syntax_Util.BaseConn (op,arms)) ->
           let uu____7370 =
             FStar_All.pipe_right connectives
               (FStar_List.tryFind
                  (fun uu____7406  ->
                     match uu____7406 with
                     | (l,uu____7416) -> FStar_Ident.lid_equals op l)) in
           (match uu____7370 with
            | None  -> fallback phi1
            | Some (uu____7439,f) -> f phi1.FStar_Syntax_Syntax.pos arms)
       | Some (FStar_Syntax_Util.QAll (vars,pats,body)) ->
           (FStar_All.pipe_right pats
              (FStar_List.iter (check_pattern_vars vars));
            (let uu____7468 = encode_q_body env vars pats body in
             match uu____7468 with
             | (vars1,pats1,guard,body1,decls) ->
                 let tm =
                   let uu____7494 =
                     let uu____7500 =
                       FStar_SMTEncoding_Util.mkImp (guard, body1) in
                     (pats1, vars1, uu____7500) in
                   FStar_SMTEncoding_Term.mkForall uu____7494
                     phi1.FStar_Syntax_Syntax.pos in
                 (tm, decls)))
       | Some (FStar_Syntax_Util.QEx (vars,pats,body)) ->
           (FStar_All.pipe_right pats
              (FStar_List.iter (check_pattern_vars vars));
            (let uu____7512 = encode_q_body env vars pats body in
             match uu____7512 with
             | (vars1,pats1,guard,body1,decls) ->
                 let uu____7537 =
                   let uu____7538 =
                     let uu____7544 =
                       FStar_SMTEncoding_Util.mkAnd (guard, body1) in
                     (pats1, vars1, uu____7544) in
                   FStar_SMTEncoding_Term.mkExists uu____7538
                     phi1.FStar_Syntax_Syntax.pos in
                 (uu____7537, decls))))
type prims_t =
  {
  mk:
    FStar_Ident.lident ->
      Prims.string ->
        (FStar_SMTEncoding_Term.term* FStar_SMTEncoding_Term.decl Prims.list);
  is: FStar_Ident.lident -> Prims.bool;}
let prims: prims_t =
  let uu____7598 = fresh_fvar "a" FStar_SMTEncoding_Term.Term_sort in
  match uu____7598 with
  | (asym,a) ->
      let uu____7603 = fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort in
      (match uu____7603 with
       | (xsym,x) ->
           let uu____7608 = fresh_fvar "y" FStar_SMTEncoding_Term.Term_sort in
           (match uu____7608 with
            | (ysym,y) ->
                let quant vars body x1 =
                  let xname_decl =
                    let uu____7638 =
                      let uu____7644 =
                        FStar_All.pipe_right vars
                          (FStar_List.map FStar_Pervasives.snd) in
                      (x1, uu____7644, FStar_SMTEncoding_Term.Term_sort,
                        None) in
                    FStar_SMTEncoding_Term.DeclFun uu____7638 in
                  let xtok = Prims.strcat x1 "@tok" in
                  let xtok_decl =
                    FStar_SMTEncoding_Term.DeclFun
                      (xtok, [], FStar_SMTEncoding_Term.Term_sort, None) in
                  let xapp =
                    let uu____7659 =
                      let uu____7663 =
                        FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars in
                      (x1, uu____7663) in
                    FStar_SMTEncoding_Util.mkApp uu____7659 in
                  let xtok1 = FStar_SMTEncoding_Util.mkApp (xtok, []) in
                  let xtok_app = mk_Apply xtok1 vars in
                  let uu____7671 =
                    let uu____7673 =
                      let uu____7675 =
                        let uu____7677 =
                          let uu____7678 =
                            let uu____7682 =
                              let uu____7683 =
                                let uu____7689 =
                                  FStar_SMTEncoding_Util.mkEq (xapp, body) in
                                ([[xapp]], vars, uu____7689) in
                              FStar_SMTEncoding_Util.mkForall uu____7683 in
                            (uu____7682, None,
                              (Prims.strcat "primitive_" x1)) in
                          FStar_SMTEncoding_Util.mkAssume uu____7678 in
                        let uu____7698 =
                          let uu____7700 =
                            let uu____7701 =
                              let uu____7705 =
                                let uu____7706 =
                                  let uu____7712 =
                                    FStar_SMTEncoding_Util.mkEq
                                      (xtok_app, xapp) in
                                  ([[xtok_app]], vars, uu____7712) in
                                FStar_SMTEncoding_Util.mkForall uu____7706 in
                              (uu____7705,
                                (Some "Name-token correspondence"),
                                (Prims.strcat "token_correspondence_" x1)) in
                            FStar_SMTEncoding_Util.mkAssume uu____7701 in
                          [uu____7700] in
                        uu____7677 :: uu____7698 in
                      xtok_decl :: uu____7675 in
                    xname_decl :: uu____7673 in
                  (xtok1, uu____7671) in
                let axy =
                  [(asym, FStar_SMTEncoding_Term.Term_sort);
                  (xsym, FStar_SMTEncoding_Term.Term_sort);
                  (ysym, FStar_SMTEncoding_Term.Term_sort)] in
                let xy =
                  [(xsym, FStar_SMTEncoding_Term.Term_sort);
                  (ysym, FStar_SMTEncoding_Term.Term_sort)] in
                let qx = [(xsym, FStar_SMTEncoding_Term.Term_sort)] in
                let prims1 =
                  let uu____7761 =
                    let uu____7769 =
                      let uu____7775 =
                        let uu____7776 = FStar_SMTEncoding_Util.mkEq (x, y) in
                        FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool
                          uu____7776 in
                      quant axy uu____7775 in
                    (FStar_Syntax_Const.op_Eq, uu____7769) in
                  let uu____7782 =
                    let uu____7791 =
                      let uu____7799 =
                        let uu____7805 =
                          let uu____7806 =
                            let uu____7807 =
                              FStar_SMTEncoding_Util.mkEq (x, y) in
                            FStar_SMTEncoding_Util.mkNot uu____7807 in
                          FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool
                            uu____7806 in
                        quant axy uu____7805 in
                      (FStar_Syntax_Const.op_notEq, uu____7799) in
                    let uu____7813 =
                      let uu____7822 =
                        let uu____7830 =
                          let uu____7836 =
                            let uu____7837 =
                              let uu____7838 =
                                let uu____7841 =
                                  FStar_SMTEncoding_Term.unboxInt x in
                                let uu____7842 =
                                  FStar_SMTEncoding_Term.unboxInt y in
                                (uu____7841, uu____7842) in
                              FStar_SMTEncoding_Util.mkLT uu____7838 in
                            FStar_All.pipe_left
                              FStar_SMTEncoding_Term.boxBool uu____7837 in
                          quant xy uu____7836 in
                        (FStar_Syntax_Const.op_LT, uu____7830) in
                      let uu____7848 =
                        let uu____7857 =
                          let uu____7865 =
                            let uu____7871 =
                              let uu____7872 =
                                let uu____7873 =
                                  let uu____7876 =
                                    FStar_SMTEncoding_Term.unboxInt x in
                                  let uu____7877 =
                                    FStar_SMTEncoding_Term.unboxInt y in
                                  (uu____7876, uu____7877) in
                                FStar_SMTEncoding_Util.mkLTE uu____7873 in
                              FStar_All.pipe_left
                                FStar_SMTEncoding_Term.boxBool uu____7872 in
                            quant xy uu____7871 in
                          (FStar_Syntax_Const.op_LTE, uu____7865) in
                        let uu____7883 =
                          let uu____7892 =
                            let uu____7900 =
                              let uu____7906 =
                                let uu____7907 =
                                  let uu____7908 =
                                    let uu____7911 =
                                      FStar_SMTEncoding_Term.unboxInt x in
                                    let uu____7912 =
                                      FStar_SMTEncoding_Term.unboxInt y in
                                    (uu____7911, uu____7912) in
                                  FStar_SMTEncoding_Util.mkGT uu____7908 in
                                FStar_All.pipe_left
                                  FStar_SMTEncoding_Term.boxBool uu____7907 in
                              quant xy uu____7906 in
                            (FStar_Syntax_Const.op_GT, uu____7900) in
                          let uu____7918 =
                            let uu____7927 =
                              let uu____7935 =
                                let uu____7941 =
                                  let uu____7942 =
                                    let uu____7943 =
                                      let uu____7946 =
                                        FStar_SMTEncoding_Term.unboxInt x in
                                      let uu____7947 =
                                        FStar_SMTEncoding_Term.unboxInt y in
                                      (uu____7946, uu____7947) in
                                    FStar_SMTEncoding_Util.mkGTE uu____7943 in
                                  FStar_All.pipe_left
                                    FStar_SMTEncoding_Term.boxBool uu____7942 in
                                quant xy uu____7941 in
                              (FStar_Syntax_Const.op_GTE, uu____7935) in
                            let uu____7953 =
                              let uu____7962 =
                                let uu____7970 =
                                  let uu____7976 =
                                    let uu____7977 =
                                      let uu____7978 =
                                        let uu____7981 =
                                          FStar_SMTEncoding_Term.unboxInt x in
                                        let uu____7982 =
                                          FStar_SMTEncoding_Term.unboxInt y in
                                        (uu____7981, uu____7982) in
                                      FStar_SMTEncoding_Util.mkSub uu____7978 in
                                    FStar_All.pipe_left
                                      FStar_SMTEncoding_Term.boxInt
                                      uu____7977 in
                                  quant xy uu____7976 in
                                (FStar_Syntax_Const.op_Subtraction,
                                  uu____7970) in
                              let uu____7988 =
                                let uu____7997 =
                                  let uu____8005 =
                                    let uu____8011 =
                                      let uu____8012 =
                                        let uu____8013 =
                                          FStar_SMTEncoding_Term.unboxInt x in
                                        FStar_SMTEncoding_Util.mkMinus
                                          uu____8013 in
                                      FStar_All.pipe_left
                                        FStar_SMTEncoding_Term.boxInt
                                        uu____8012 in
                                    quant qx uu____8011 in
                                  (FStar_Syntax_Const.op_Minus, uu____8005) in
                                let uu____8019 =
                                  let uu____8028 =
                                    let uu____8036 =
                                      let uu____8042 =
                                        let uu____8043 =
                                          let uu____8044 =
                                            let uu____8047 =
                                              FStar_SMTEncoding_Term.unboxInt
                                                x in
                                            let uu____8048 =
                                              FStar_SMTEncoding_Term.unboxInt
                                                y in
                                            (uu____8047, uu____8048) in
                                          FStar_SMTEncoding_Util.mkAdd
                                            uu____8044 in
                                        FStar_All.pipe_left
                                          FStar_SMTEncoding_Term.boxInt
                                          uu____8043 in
                                      quant xy uu____8042 in
                                    (FStar_Syntax_Const.op_Addition,
                                      uu____8036) in
                                  let uu____8054 =
                                    let uu____8063 =
                                      let uu____8071 =
                                        let uu____8077 =
                                          let uu____8078 =
                                            let uu____8079 =
                                              let uu____8082 =
                                                FStar_SMTEncoding_Term.unboxInt
                                                  x in
                                              let uu____8083 =
                                                FStar_SMTEncoding_Term.unboxInt
                                                  y in
                                              (uu____8082, uu____8083) in
                                            FStar_SMTEncoding_Util.mkMul
                                              uu____8079 in
                                          FStar_All.pipe_left
                                            FStar_SMTEncoding_Term.boxInt
                                            uu____8078 in
                                        quant xy uu____8077 in
                                      (FStar_Syntax_Const.op_Multiply,
                                        uu____8071) in
                                    let uu____8089 =
                                      let uu____8098 =
                                        let uu____8106 =
                                          let uu____8112 =
                                            let uu____8113 =
                                              let uu____8114 =
                                                let uu____8117 =
                                                  FStar_SMTEncoding_Term.unboxInt
                                                    x in
                                                let uu____8118 =
                                                  FStar_SMTEncoding_Term.unboxInt
                                                    y in
                                                (uu____8117, uu____8118) in
                                              FStar_SMTEncoding_Util.mkDiv
                                                uu____8114 in
                                            FStar_All.pipe_left
                                              FStar_SMTEncoding_Term.boxInt
                                              uu____8113 in
                                          quant xy uu____8112 in
                                        (FStar_Syntax_Const.op_Division,
                                          uu____8106) in
                                      let uu____8124 =
                                        let uu____8133 =
                                          let uu____8141 =
                                            let uu____8147 =
                                              let uu____8148 =
                                                let uu____8149 =
                                                  let uu____8152 =
                                                    FStar_SMTEncoding_Term.unboxInt
                                                      x in
                                                  let uu____8153 =
                                                    FStar_SMTEncoding_Term.unboxInt
                                                      y in
                                                  (uu____8152, uu____8153) in
                                                FStar_SMTEncoding_Util.mkMod
                                                  uu____8149 in
                                              FStar_All.pipe_left
                                                FStar_SMTEncoding_Term.boxInt
                                                uu____8148 in
                                            quant xy uu____8147 in
                                          (FStar_Syntax_Const.op_Modulus,
                                            uu____8141) in
                                        let uu____8159 =
                                          let uu____8168 =
                                            let uu____8176 =
                                              let uu____8182 =
                                                let uu____8183 =
                                                  let uu____8184 =
                                                    let uu____8187 =
                                                      FStar_SMTEncoding_Term.unboxBool
                                                        x in
                                                    let uu____8188 =
                                                      FStar_SMTEncoding_Term.unboxBool
                                                        y in
                                                    (uu____8187, uu____8188) in
                                                  FStar_SMTEncoding_Util.mkAnd
                                                    uu____8184 in
                                                FStar_All.pipe_left
                                                  FStar_SMTEncoding_Term.boxBool
                                                  uu____8183 in
                                              quant xy uu____8182 in
                                            (FStar_Syntax_Const.op_And,
                                              uu____8176) in
                                          let uu____8194 =
                                            let uu____8203 =
                                              let uu____8211 =
                                                let uu____8217 =
                                                  let uu____8218 =
                                                    let uu____8219 =
                                                      let uu____8222 =
                                                        FStar_SMTEncoding_Term.unboxBool
                                                          x in
                                                      let uu____8223 =
                                                        FStar_SMTEncoding_Term.unboxBool
                                                          y in
                                                      (uu____8222,
                                                        uu____8223) in
                                                    FStar_SMTEncoding_Util.mkOr
                                                      uu____8219 in
                                                  FStar_All.pipe_left
                                                    FStar_SMTEncoding_Term.boxBool
                                                    uu____8218 in
                                                quant xy uu____8217 in
                                              (FStar_Syntax_Const.op_Or,
                                                uu____8211) in
                                            let uu____8229 =
                                              let uu____8238 =
                                                let uu____8246 =
                                                  let uu____8252 =
                                                    let uu____8253 =
                                                      let uu____8254 =
                                                        FStar_SMTEncoding_Term.unboxBool
                                                          x in
                                                      FStar_SMTEncoding_Util.mkNot
                                                        uu____8254 in
                                                    FStar_All.pipe_left
                                                      FStar_SMTEncoding_Term.boxBool
                                                      uu____8253 in
                                                  quant qx uu____8252 in
                                                (FStar_Syntax_Const.op_Negation,
                                                  uu____8246) in
                                              [uu____8238] in
                                            uu____8203 :: uu____8229 in
                                          uu____8168 :: uu____8194 in
                                        uu____8133 :: uu____8159 in
                                      uu____8098 :: uu____8124 in
                                    uu____8063 :: uu____8089 in
                                  uu____8028 :: uu____8054 in
                                uu____7997 :: uu____8019 in
                              uu____7962 :: uu____7988 in
                            uu____7927 :: uu____7953 in
                          uu____7892 :: uu____7918 in
                        uu____7857 :: uu____7883 in
                      uu____7822 :: uu____7848 in
                    uu____7791 :: uu____7813 in
                  uu____7761 :: uu____7782 in
                let mk1 l v1 =
                  let uu____8382 =
                    let uu____8387 =
                      FStar_All.pipe_right prims1
                        (FStar_List.find
                           (fun uu____8419  ->
                              match uu____8419 with
                              | (l',uu____8428) ->
                                  FStar_Ident.lid_equals l l')) in
                    FStar_All.pipe_right uu____8387
                      (FStar_Option.map
                         (fun uu____8461  ->
                            match uu____8461 with | (uu____8472,b) -> b v1)) in
                  FStar_All.pipe_right uu____8382 FStar_Option.get in
                let is l =
                  FStar_All.pipe_right prims1
                    (FStar_Util.for_some
                       (fun uu____8513  ->
                          match uu____8513 with
                          | (l',uu____8522) -> FStar_Ident.lid_equals l l')) in
                { mk = mk1; is }))
let pretype_axiom:
  env_t ->
    FStar_SMTEncoding_Term.term ->
      (Prims.string* FStar_SMTEncoding_Term.sort) Prims.list ->
        FStar_SMTEncoding_Term.decl
  =
  fun env  ->
    fun tapp  ->
      fun vars  ->
        let uu____8548 = fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort in
        match uu____8548 with
        | (xxsym,xx) ->
            let uu____8553 = fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort in
            (match uu____8553 with
             | (ffsym,ff) ->
                 let xx_has_type =
                   FStar_SMTEncoding_Term.mk_HasTypeFuel ff xx tapp in
                 let tapp_hash = FStar_SMTEncoding_Term.hash_of_term tapp in
                 let module_name = env.current_module_name in
                 let uu____8561 =
                   let uu____8565 =
                     let uu____8566 =
                       let uu____8572 =
                         let uu____8573 =
                           let uu____8576 =
                             let uu____8577 =
                               let uu____8580 =
                                 FStar_SMTEncoding_Util.mkApp
                                   ("PreType", [xx]) in
                               (tapp, uu____8580) in
                             FStar_SMTEncoding_Util.mkEq uu____8577 in
                           (xx_has_type, uu____8576) in
                         FStar_SMTEncoding_Util.mkImp uu____8573 in
                       ([[xx_has_type]],
                         ((xxsym, FStar_SMTEncoding_Term.Term_sort) ::
                         (ffsym, FStar_SMTEncoding_Term.Fuel_sort) :: vars),
                         uu____8572) in
                     FStar_SMTEncoding_Util.mkForall uu____8566 in
                   let uu____8593 =
                     let uu____8594 =
                       let uu____8595 =
                         let uu____8596 =
                           FStar_Util.digest_of_string tapp_hash in
                         Prims.strcat "_pretyping_" uu____8596 in
                       Prims.strcat module_name uu____8595 in
                     varops.mk_unique uu____8594 in
                   (uu____8565, (Some "pretyping"), uu____8593) in
                 FStar_SMTEncoding_Util.mkAssume uu____8561)
let primitive_type_axioms:
  FStar_TypeChecker_Env.env ->
    FStar_Ident.lident ->
      Prims.string ->
        FStar_SMTEncoding_Term.term -> FStar_SMTEncoding_Term.decl Prims.list
  =
  let xx = ("x", FStar_SMTEncoding_Term.Term_sort) in
  let x = FStar_SMTEncoding_Util.mkFreeV xx in
  let yy = ("y", FStar_SMTEncoding_Term.Term_sort) in
  let y = FStar_SMTEncoding_Util.mkFreeV yy in
  let mk_unit env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt in
    let uu____8626 =
      let uu____8627 =
        let uu____8631 =
          FStar_SMTEncoding_Term.mk_HasType
            FStar_SMTEncoding_Term.mk_Term_unit tt in
        (uu____8631, (Some "unit typing"), "unit_typing") in
      FStar_SMTEncoding_Util.mkAssume uu____8627 in
    let uu____8633 =
      let uu____8635 =
        let uu____8636 =
          let uu____8640 =
            let uu____8641 =
              let uu____8647 =
                let uu____8648 =
                  let uu____8651 =
                    FStar_SMTEncoding_Util.mkEq
                      (x, FStar_SMTEncoding_Term.mk_Term_unit) in
                  (typing_pred, uu____8651) in
                FStar_SMTEncoding_Util.mkImp uu____8648 in
              ([[typing_pred]], [xx], uu____8647) in
            mkForall_fuel uu____8641 in
          (uu____8640, (Some "unit inversion"), "unit_inversion") in
        FStar_SMTEncoding_Util.mkAssume uu____8636 in
      [uu____8635] in
    uu____8626 :: uu____8633 in
  let mk_bool env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt in
    let bb = ("b", FStar_SMTEncoding_Term.Bool_sort) in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let uu____8679 =
      let uu____8680 =
        let uu____8684 =
          let uu____8685 =
            let uu____8691 =
              let uu____8694 =
                let uu____8696 = FStar_SMTEncoding_Term.boxBool b in
                [uu____8696] in
              [uu____8694] in
            let uu____8699 =
              let uu____8700 = FStar_SMTEncoding_Term.boxBool b in
              FStar_SMTEncoding_Term.mk_HasType uu____8700 tt in
            (uu____8691, [bb], uu____8699) in
          FStar_SMTEncoding_Util.mkForall uu____8685 in
        (uu____8684, (Some "bool typing"), "bool_typing") in
      FStar_SMTEncoding_Util.mkAssume uu____8680 in
    let uu____8711 =
      let uu____8713 =
        let uu____8714 =
          let uu____8718 =
            let uu____8719 =
              let uu____8725 =
                let uu____8726 =
                  let uu____8729 =
                    FStar_SMTEncoding_Term.mk_tester "BoxBool" x in
                  (typing_pred, uu____8729) in
                FStar_SMTEncoding_Util.mkImp uu____8726 in
              ([[typing_pred]], [xx], uu____8725) in
            mkForall_fuel uu____8719 in
          (uu____8718, (Some "bool inversion"), "bool_inversion") in
        FStar_SMTEncoding_Util.mkAssume uu____8714 in
      [uu____8713] in
    uu____8679 :: uu____8711 in
  let mk_int env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt in
    let typing_pred_y = FStar_SMTEncoding_Term.mk_HasType y tt in
    let aa = ("a", FStar_SMTEncoding_Term.Int_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let bb = ("b", FStar_SMTEncoding_Term.Int_sort) in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let precedes =
      let uu____8763 =
        let uu____8764 =
          let uu____8768 =
            let uu____8770 =
              let uu____8772 =
                let uu____8774 = FStar_SMTEncoding_Term.boxInt a in
                let uu____8775 =
                  let uu____8777 = FStar_SMTEncoding_Term.boxInt b in
                  [uu____8777] in
                uu____8774 :: uu____8775 in
              tt :: uu____8772 in
            tt :: uu____8770 in
          ("Prims.Precedes", uu____8768) in
        FStar_SMTEncoding_Util.mkApp uu____8764 in
      FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid uu____8763 in
    let precedes_y_x =
      let uu____8780 = FStar_SMTEncoding_Util.mkApp ("Precedes", [y; x]) in
      FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid uu____8780 in
    let uu____8782 =
      let uu____8783 =
        let uu____8787 =
          let uu____8788 =
            let uu____8794 =
              let uu____8797 =
                let uu____8799 = FStar_SMTEncoding_Term.boxInt b in
                [uu____8799] in
              [uu____8797] in
            let uu____8802 =
              let uu____8803 = FStar_SMTEncoding_Term.boxInt b in
              FStar_SMTEncoding_Term.mk_HasType uu____8803 tt in
            (uu____8794, [bb], uu____8802) in
          FStar_SMTEncoding_Util.mkForall uu____8788 in
        (uu____8787, (Some "int typing"), "int_typing") in
      FStar_SMTEncoding_Util.mkAssume uu____8783 in
    let uu____8814 =
      let uu____8816 =
        let uu____8817 =
          let uu____8821 =
            let uu____8822 =
              let uu____8828 =
                let uu____8829 =
                  let uu____8832 =
                    FStar_SMTEncoding_Term.mk_tester "BoxInt" x in
                  (typing_pred, uu____8832) in
                FStar_SMTEncoding_Util.mkImp uu____8829 in
              ([[typing_pred]], [xx], uu____8828) in
            mkForall_fuel uu____8822 in
          (uu____8821, (Some "int inversion"), "int_inversion") in
        FStar_SMTEncoding_Util.mkAssume uu____8817 in
      let uu____8845 =
        let uu____8847 =
          let uu____8848 =
            let uu____8852 =
              let uu____8853 =
                let uu____8859 =
                  let uu____8860 =
                    let uu____8863 =
                      let uu____8864 =
                        let uu____8866 =
                          let uu____8868 =
                            let uu____8870 =
                              let uu____8871 =
                                let uu____8874 =
                                  FStar_SMTEncoding_Term.unboxInt x in
                                let uu____8875 =
                                  FStar_SMTEncoding_Util.mkInteger'
                                    (Prims.parse_int "0") in
                                (uu____8874, uu____8875) in
                              FStar_SMTEncoding_Util.mkGT uu____8871 in
                            let uu____8876 =
                              let uu____8878 =
                                let uu____8879 =
                                  let uu____8882 =
                                    FStar_SMTEncoding_Term.unboxInt y in
                                  let uu____8883 =
                                    FStar_SMTEncoding_Util.mkInteger'
                                      (Prims.parse_int "0") in
                                  (uu____8882, uu____8883) in
                                FStar_SMTEncoding_Util.mkGTE uu____8879 in
                              let uu____8884 =
                                let uu____8886 =
                                  let uu____8887 =
                                    let uu____8890 =
                                      FStar_SMTEncoding_Term.unboxInt y in
                                    let uu____8891 =
                                      FStar_SMTEncoding_Term.unboxInt x in
                                    (uu____8890, uu____8891) in
                                  FStar_SMTEncoding_Util.mkLT uu____8887 in
                                [uu____8886] in
                              uu____8878 :: uu____8884 in
                            uu____8870 :: uu____8876 in
                          typing_pred_y :: uu____8868 in
                        typing_pred :: uu____8866 in
                      FStar_SMTEncoding_Util.mk_and_l uu____8864 in
                    (uu____8863, precedes_y_x) in
                  FStar_SMTEncoding_Util.mkImp uu____8860 in
                ([[typing_pred; typing_pred_y; precedes_y_x]], [xx; yy],
                  uu____8859) in
              mkForall_fuel uu____8853 in
            (uu____8852, (Some "well-founded ordering on nat (alt)"),
              "well-founded-ordering-on-nat") in
          FStar_SMTEncoding_Util.mkAssume uu____8848 in
        [uu____8847] in
      uu____8816 :: uu____8845 in
    uu____8782 :: uu____8814 in
  let mk_str env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt in
    let bb = ("b", FStar_SMTEncoding_Term.String_sort) in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let uu____8921 =
      let uu____8922 =
        let uu____8926 =
          let uu____8927 =
            let uu____8933 =
              let uu____8936 =
                let uu____8938 = FStar_SMTEncoding_Term.boxString b in
                [uu____8938] in
              [uu____8936] in
            let uu____8941 =
              let uu____8942 = FStar_SMTEncoding_Term.boxString b in
              FStar_SMTEncoding_Term.mk_HasType uu____8942 tt in
            (uu____8933, [bb], uu____8941) in
          FStar_SMTEncoding_Util.mkForall uu____8927 in
        (uu____8926, (Some "string typing"), "string_typing") in
      FStar_SMTEncoding_Util.mkAssume uu____8922 in
    let uu____8953 =
      let uu____8955 =
        let uu____8956 =
          let uu____8960 =
            let uu____8961 =
              let uu____8967 =
                let uu____8968 =
                  let uu____8971 =
                    FStar_SMTEncoding_Term.mk_tester "BoxString" x in
                  (typing_pred, uu____8971) in
                FStar_SMTEncoding_Util.mkImp uu____8968 in
              ([[typing_pred]], [xx], uu____8967) in
            mkForall_fuel uu____8961 in
          (uu____8960, (Some "string inversion"), "string_inversion") in
        FStar_SMTEncoding_Util.mkAssume uu____8956 in
      [uu____8955] in
    uu____8921 :: uu____8953 in
  let mk_ref1 env reft_name uu____8993 =
    let r = ("r", FStar_SMTEncoding_Term.Ref_sort) in
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let refa =
      let uu____9004 =
        let uu____9008 =
          let uu____9010 = FStar_SMTEncoding_Util.mkFreeV aa in [uu____9010] in
        (reft_name, uu____9008) in
      FStar_SMTEncoding_Util.mkApp uu____9004 in
    let refb =
      let uu____9013 =
        let uu____9017 =
          let uu____9019 = FStar_SMTEncoding_Util.mkFreeV bb in [uu____9019] in
        (reft_name, uu____9017) in
      FStar_SMTEncoding_Util.mkApp uu____9013 in
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x refa in
    let typing_pred_b = FStar_SMTEncoding_Term.mk_HasType x refb in
    let uu____9023 =
      let uu____9024 =
        let uu____9028 =
          let uu____9029 =
            let uu____9035 =
              let uu____9036 =
                let uu____9039 = FStar_SMTEncoding_Term.mk_tester "BoxRef" x in
                (typing_pred, uu____9039) in
              FStar_SMTEncoding_Util.mkImp uu____9036 in
            ([[typing_pred]], [xx; aa], uu____9035) in
          mkForall_fuel uu____9029 in
        (uu____9028, (Some "ref inversion"), "ref_inversion") in
      FStar_SMTEncoding_Util.mkAssume uu____9024 in
    [uu____9023] in
  let mk_true_interp env nm true_tm =
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [true_tm]) in
    [FStar_SMTEncoding_Util.mkAssume
       (valid, (Some "True interpretation"), "true_interp")] in
  let mk_false_interp env nm false_tm =
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [false_tm]) in
    let uu____9079 =
      let uu____9080 =
        let uu____9084 =
          FStar_SMTEncoding_Util.mkIff
            (FStar_SMTEncoding_Util.mkFalse, valid) in
        (uu____9084, (Some "False interpretation"), "false_interp") in
      FStar_SMTEncoding_Util.mkAssume uu____9080 in
    [uu____9079] in
  let mk_and_interp env conj uu____9095 =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let l_and_a_b = FStar_SMTEncoding_Util.mkApp (conj, [a; b]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_and_a_b]) in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b]) in
    let uu____9112 =
      let uu____9113 =
        let uu____9117 =
          let uu____9118 =
            let uu____9124 =
              let uu____9125 =
                let uu____9128 =
                  FStar_SMTEncoding_Util.mkAnd (valid_a, valid_b) in
                (uu____9128, valid) in
              FStar_SMTEncoding_Util.mkIff uu____9125 in
            ([[l_and_a_b]], [aa; bb], uu____9124) in
          FStar_SMTEncoding_Util.mkForall uu____9118 in
        (uu____9117, (Some "/\\ interpretation"), "l_and-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____9113 in
    [uu____9112] in
  let mk_or_interp env disj uu____9152 =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let l_or_a_b = FStar_SMTEncoding_Util.mkApp (disj, [a; b]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_or_a_b]) in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b]) in
    let uu____9169 =
      let uu____9170 =
        let uu____9174 =
          let uu____9175 =
            let uu____9181 =
              let uu____9182 =
                let uu____9185 =
                  FStar_SMTEncoding_Util.mkOr (valid_a, valid_b) in
                (uu____9185, valid) in
              FStar_SMTEncoding_Util.mkIff uu____9182 in
            ([[l_or_a_b]], [aa; bb], uu____9181) in
          FStar_SMTEncoding_Util.mkForall uu____9175 in
        (uu____9174, (Some "\\/ interpretation"), "l_or-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____9170 in
    [uu____9169] in
  let mk_eq2_interp env eq2 tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let xx1 = ("x", FStar_SMTEncoding_Term.Term_sort) in
    let yy1 = ("y", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let x1 = FStar_SMTEncoding_Util.mkFreeV xx1 in
    let y1 = FStar_SMTEncoding_Util.mkFreeV yy1 in
    let eq2_x_y = FStar_SMTEncoding_Util.mkApp (eq2, [a; x1; y1]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [eq2_x_y]) in
    let uu____9226 =
      let uu____9227 =
        let uu____9231 =
          let uu____9232 =
            let uu____9238 =
              let uu____9239 =
                let uu____9242 = FStar_SMTEncoding_Util.mkEq (x1, y1) in
                (uu____9242, valid) in
              FStar_SMTEncoding_Util.mkIff uu____9239 in
            ([[eq2_x_y]], [aa; xx1; yy1], uu____9238) in
          FStar_SMTEncoding_Util.mkForall uu____9232 in
        (uu____9231, (Some "Eq2 interpretation"), "eq2-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____9227 in
    [uu____9226] in
  let mk_eq3_interp env eq3 tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let xx1 = ("x", FStar_SMTEncoding_Term.Term_sort) in
    let yy1 = ("y", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let x1 = FStar_SMTEncoding_Util.mkFreeV xx1 in
    let y1 = FStar_SMTEncoding_Util.mkFreeV yy1 in
    let eq3_x_y = FStar_SMTEncoding_Util.mkApp (eq3, [a; b; x1; y1]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [eq3_x_y]) in
    let uu____9289 =
      let uu____9290 =
        let uu____9294 =
          let uu____9295 =
            let uu____9301 =
              let uu____9302 =
                let uu____9305 = FStar_SMTEncoding_Util.mkEq (x1, y1) in
                (uu____9305, valid) in
              FStar_SMTEncoding_Util.mkIff uu____9302 in
            ([[eq3_x_y]], [aa; bb; xx1; yy1], uu____9301) in
          FStar_SMTEncoding_Util.mkForall uu____9295 in
        (uu____9294, (Some "Eq3 interpretation"), "eq3-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____9290 in
    [uu____9289] in
  let mk_imp_interp env imp tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let l_imp_a_b = FStar_SMTEncoding_Util.mkApp (imp, [a; b]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_imp_a_b]) in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b]) in
    let uu____9350 =
      let uu____9351 =
        let uu____9355 =
          let uu____9356 =
            let uu____9362 =
              let uu____9363 =
                let uu____9366 =
                  FStar_SMTEncoding_Util.mkImp (valid_a, valid_b) in
                (uu____9366, valid) in
              FStar_SMTEncoding_Util.mkIff uu____9363 in
            ([[l_imp_a_b]], [aa; bb], uu____9362) in
          FStar_SMTEncoding_Util.mkForall uu____9356 in
        (uu____9355, (Some "==> interpretation"), "l_imp-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____9351 in
    [uu____9350] in
  let mk_iff_interp env iff tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let l_iff_a_b = FStar_SMTEncoding_Util.mkApp (iff, [a; b]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_iff_a_b]) in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b]) in
    let uu____9407 =
      let uu____9408 =
        let uu____9412 =
          let uu____9413 =
            let uu____9419 =
              let uu____9420 =
                let uu____9423 =
                  FStar_SMTEncoding_Util.mkIff (valid_a, valid_b) in
                (uu____9423, valid) in
              FStar_SMTEncoding_Util.mkIff uu____9420 in
            ([[l_iff_a_b]], [aa; bb], uu____9419) in
          FStar_SMTEncoding_Util.mkForall uu____9413 in
        (uu____9412, (Some "<==> interpretation"), "l_iff-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____9408 in
    [uu____9407] in
  let mk_not_interp env l_not tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let l_not_a = FStar_SMTEncoding_Util.mkApp (l_not, [a]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_not_a]) in
    let not_valid_a =
      let uu____9457 = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
      FStar_All.pipe_left FStar_SMTEncoding_Util.mkNot uu____9457 in
    let uu____9459 =
      let uu____9460 =
        let uu____9464 =
          let uu____9465 =
            let uu____9471 =
              FStar_SMTEncoding_Util.mkIff (not_valid_a, valid) in
            ([[l_not_a]], [aa], uu____9471) in
          FStar_SMTEncoding_Util.mkForall uu____9465 in
        (uu____9464, (Some "not interpretation"), "l_not-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____9460 in
    [uu____9459] in
  let mk_forall_interp env for_all1 tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let xx1 = ("x", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let x1 = FStar_SMTEncoding_Util.mkFreeV xx1 in
    let l_forall_a_b = FStar_SMTEncoding_Util.mkApp (for_all1, [a; b]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_forall_a_b]) in
    let valid_b_x =
      let uu____9511 =
        let uu____9515 =
          let uu____9517 = FStar_SMTEncoding_Util.mk_ApplyTT b x1 in
          [uu____9517] in
        ("Valid", uu____9515) in
      FStar_SMTEncoding_Util.mkApp uu____9511 in
    let uu____9519 =
      let uu____9520 =
        let uu____9524 =
          let uu____9525 =
            let uu____9531 =
              let uu____9532 =
                let uu____9535 =
                  let uu____9536 =
                    let uu____9542 =
                      let uu____9545 =
                        let uu____9547 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a in
                        [uu____9547] in
                      [uu____9545] in
                    let uu____9550 =
                      let uu____9551 =
                        let uu____9554 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a in
                        (uu____9554, valid_b_x) in
                      FStar_SMTEncoding_Util.mkImp uu____9551 in
                    (uu____9542, [xx1], uu____9550) in
                  FStar_SMTEncoding_Util.mkForall uu____9536 in
                (uu____9535, valid) in
              FStar_SMTEncoding_Util.mkIff uu____9532 in
            ([[l_forall_a_b]], [aa; bb], uu____9531) in
          FStar_SMTEncoding_Util.mkForall uu____9525 in
        (uu____9524, (Some "forall interpretation"), "forall-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____9520 in
    [uu____9519] in
  let mk_exists_interp env for_some1 tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let xx1 = ("x", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let x1 = FStar_SMTEncoding_Util.mkFreeV xx1 in
    let l_exists_a_b = FStar_SMTEncoding_Util.mkApp (for_some1, [a; b]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_exists_a_b]) in
    let valid_b_x =
      let uu____9605 =
        let uu____9609 =
          let uu____9611 = FStar_SMTEncoding_Util.mk_ApplyTT b x1 in
          [uu____9611] in
        ("Valid", uu____9609) in
      FStar_SMTEncoding_Util.mkApp uu____9605 in
    let uu____9613 =
      let uu____9614 =
        let uu____9618 =
          let uu____9619 =
            let uu____9625 =
              let uu____9626 =
                let uu____9629 =
                  let uu____9630 =
                    let uu____9636 =
                      let uu____9639 =
                        let uu____9641 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a in
                        [uu____9641] in
                      [uu____9639] in
                    let uu____9644 =
                      let uu____9645 =
                        let uu____9648 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a in
                        (uu____9648, valid_b_x) in
                      FStar_SMTEncoding_Util.mkImp uu____9645 in
                    (uu____9636, [xx1], uu____9644) in
                  FStar_SMTEncoding_Util.mkExists uu____9630 in
                (uu____9629, valid) in
              FStar_SMTEncoding_Util.mkIff uu____9626 in
            ([[l_exists_a_b]], [aa; bb], uu____9625) in
          FStar_SMTEncoding_Util.mkForall uu____9619 in
        (uu____9618, (Some "exists interpretation"), "exists-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____9614 in
    [uu____9613] in
  let mk_range_interp env range tt =
    let range_ty = FStar_SMTEncoding_Util.mkApp (range, []) in
    let uu____9684 =
      let uu____9685 =
        let uu____9689 =
          FStar_SMTEncoding_Term.mk_HasTypeZ
            FStar_SMTEncoding_Term.mk_Range_const range_ty in
        let uu____9690 = varops.mk_unique "typing_range_const" in
        (uu____9689, (Some "Range_const typing"), uu____9690) in
      FStar_SMTEncoding_Util.mkAssume uu____9685 in
    [uu____9684] in
  let prims1 =
    [(FStar_Syntax_Const.unit_lid, mk_unit);
    (FStar_Syntax_Const.bool_lid, mk_bool);
    (FStar_Syntax_Const.int_lid, mk_int);
    (FStar_Syntax_Const.string_lid, mk_str);
    (FStar_Syntax_Const.ref_lid, mk_ref1);
    (FStar_Syntax_Const.true_lid, mk_true_interp);
    (FStar_Syntax_Const.false_lid, mk_false_interp);
    (FStar_Syntax_Const.and_lid, mk_and_interp);
    (FStar_Syntax_Const.or_lid, mk_or_interp);
    (FStar_Syntax_Const.eq2_lid, mk_eq2_interp);
    (FStar_Syntax_Const.eq3_lid, mk_eq3_interp);
    (FStar_Syntax_Const.imp_lid, mk_imp_interp);
    (FStar_Syntax_Const.iff_lid, mk_iff_interp);
    (FStar_Syntax_Const.not_lid, mk_not_interp);
    (FStar_Syntax_Const.forall_lid, mk_forall_interp);
    (FStar_Syntax_Const.exists_lid, mk_exists_interp);
    (FStar_Syntax_Const.range_lid, mk_range_interp)] in
  fun env  ->
    fun t  ->
      fun s  ->
        fun tt  ->
          let uu____9952 =
            FStar_Util.find_opt
              (fun uu____9970  ->
                 match uu____9970 with
                 | (l,uu____9980) -> FStar_Ident.lid_equals l t) prims1 in
          match uu____9952 with
          | None  -> []
          | Some (uu____10002,f) -> f env s tt
let encode_smt_lemma:
  env_t ->
    FStar_Syntax_Syntax.fv ->
      FStar_Syntax_Syntax.typ -> FStar_SMTEncoding_Term.decl Prims.list
  =
  fun env  ->
    fun fv  ->
      fun t  ->
        let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
        let uu____10039 = encode_function_type_as_formula t env in
        match uu____10039 with
        | (form,decls) ->
            FStar_List.append decls
              [FStar_SMTEncoding_Util.mkAssume
                 (form, (Some (Prims.strcat "Lemma: " lid.FStar_Ident.str)),
                   (Prims.strcat "lemma_" lid.FStar_Ident.str))]
let encode_free_var:
  env_t ->
    FStar_Syntax_Syntax.fv ->
      FStar_Syntax_Syntax.term ->
        FStar_Syntax_Syntax.term ->
          FStar_Syntax_Syntax.qualifier Prims.list ->
            (FStar_SMTEncoding_Term.decl Prims.list* env_t)
  =
  fun env  ->
    fun fv  ->
      fun tt  ->
        fun t_norm  ->
          fun quals  ->
            let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
            let uu____10071 =
              (let uu____10072 =
                 (FStar_Syntax_Util.is_pure_or_ghost_function t_norm) ||
                   (FStar_TypeChecker_Env.is_reifiable_function env.tcenv
                      t_norm) in
               FStar_All.pipe_left Prims.op_Negation uu____10072) ||
                (FStar_Syntax_Util.is_lemma t_norm) in
            if uu____10071
            then
              let uu____10076 = new_term_constant_and_tok_from_lid env lid in
              match uu____10076 with
              | (vname,vtok,env1) ->
                  let arg_sorts =
                    let uu____10088 =
                      let uu____10089 = FStar_Syntax_Subst.compress t_norm in
                      uu____10089.FStar_Syntax_Syntax.n in
                    match uu____10088 with
                    | FStar_Syntax_Syntax.Tm_arrow (binders,uu____10094) ->
                        FStar_All.pipe_right binders
                          (FStar_List.map
                             (fun uu____10111  ->
                                FStar_SMTEncoding_Term.Term_sort))
                    | uu____10114 -> [] in
                  let d =
                    FStar_SMTEncoding_Term.DeclFun
                      (vname, arg_sorts, FStar_SMTEncoding_Term.Term_sort,
                        (Some
                           "Uninterpreted function symbol for impure function")) in
                  let dd =
                    FStar_SMTEncoding_Term.DeclFun
                      (vtok, [], FStar_SMTEncoding_Term.Term_sort,
                        (Some "Uninterpreted name for impure function")) in
                  ([d; dd], env1)
            else
              (let uu____10123 = prims.is lid in
               if uu____10123
               then
                 let vname = varops.new_fvar lid in
                 let uu____10128 = prims.mk lid vname in
                 match uu____10128 with
                 | (tok,definition) ->
                     let env1 = push_free_var env lid vname (Some tok) in
                     (definition, env1)
               else
                 (let encode_non_total_function_typ =
                    lid.FStar_Ident.nsstr <> "Prims" in
                  let uu____10143 =
                    let uu____10149 = curried_arrow_formals_comp t_norm in
                    match uu____10149 with
                    | (args,comp) ->
                        let comp1 =
                          let uu____10160 =
                            FStar_TypeChecker_Env.is_reifiable_comp env.tcenv
                              comp in
                          if uu____10160
                          then
                            let uu____10161 =
                              FStar_TypeChecker_Env.reify_comp
                                (let uu___144_10162 = env.tcenv in
                                 {
                                   FStar_TypeChecker_Env.solver =
                                     (uu___144_10162.FStar_TypeChecker_Env.solver);
                                   FStar_TypeChecker_Env.range =
                                     (uu___144_10162.FStar_TypeChecker_Env.range);
                                   FStar_TypeChecker_Env.curmodule =
                                     (uu___144_10162.FStar_TypeChecker_Env.curmodule);
                                   FStar_TypeChecker_Env.gamma =
                                     (uu___144_10162.FStar_TypeChecker_Env.gamma);
                                   FStar_TypeChecker_Env.gamma_cache =
                                     (uu___144_10162.FStar_TypeChecker_Env.gamma_cache);
                                   FStar_TypeChecker_Env.modules =
                                     (uu___144_10162.FStar_TypeChecker_Env.modules);
                                   FStar_TypeChecker_Env.expected_typ =
                                     (uu___144_10162.FStar_TypeChecker_Env.expected_typ);
                                   FStar_TypeChecker_Env.sigtab =
                                     (uu___144_10162.FStar_TypeChecker_Env.sigtab);
                                   FStar_TypeChecker_Env.is_pattern =
                                     (uu___144_10162.FStar_TypeChecker_Env.is_pattern);
                                   FStar_TypeChecker_Env.instantiate_imp =
                                     (uu___144_10162.FStar_TypeChecker_Env.instantiate_imp);
                                   FStar_TypeChecker_Env.effects =
                                     (uu___144_10162.FStar_TypeChecker_Env.effects);
                                   FStar_TypeChecker_Env.generalize =
                                     (uu___144_10162.FStar_TypeChecker_Env.generalize);
                                   FStar_TypeChecker_Env.letrecs =
                                     (uu___144_10162.FStar_TypeChecker_Env.letrecs);
                                   FStar_TypeChecker_Env.top_level =
                                     (uu___144_10162.FStar_TypeChecker_Env.top_level);
                                   FStar_TypeChecker_Env.check_uvars =
                                     (uu___144_10162.FStar_TypeChecker_Env.check_uvars);
                                   FStar_TypeChecker_Env.use_eq =
                                     (uu___144_10162.FStar_TypeChecker_Env.use_eq);
                                   FStar_TypeChecker_Env.is_iface =
                                     (uu___144_10162.FStar_TypeChecker_Env.is_iface);
                                   FStar_TypeChecker_Env.admit =
                                     (uu___144_10162.FStar_TypeChecker_Env.admit);
                                   FStar_TypeChecker_Env.lax = true;
                                   FStar_TypeChecker_Env.lax_universes =
                                     (uu___144_10162.FStar_TypeChecker_Env.lax_universes);
                                   FStar_TypeChecker_Env.type_of =
                                     (uu___144_10162.FStar_TypeChecker_Env.type_of);
                                   FStar_TypeChecker_Env.universe_of =
                                     (uu___144_10162.FStar_TypeChecker_Env.universe_of);
                                   FStar_TypeChecker_Env.use_bv_sorts =
                                     (uu___144_10162.FStar_TypeChecker_Env.use_bv_sorts);
                                   FStar_TypeChecker_Env.qname_and_index =
                                     (uu___144_10162.FStar_TypeChecker_Env.qname_and_index)
                                 }) comp FStar_Syntax_Syntax.U_unknown in
                            FStar_Syntax_Syntax.mk_Total uu____10161
                          else comp in
                        if encode_non_total_function_typ
                        then
                          let uu____10169 =
                            FStar_TypeChecker_Util.pure_or_ghost_pre_and_post
                              env.tcenv comp1 in
                          (args, uu____10169)
                        else
                          (args,
                            (None, (FStar_Syntax_Util.comp_result comp1))) in
                  match uu____10143 with
                  | (formals,(pre_opt,res_t)) ->
                      let uu____10196 =
                        new_term_constant_and_tok_from_lid env lid in
                      (match uu____10196 with
                       | (vname,vtok,env1) ->
                           let vtok_tm =
                             match formals with
                             | [] ->
                                 FStar_SMTEncoding_Util.mkFreeV
                                   (vname, FStar_SMTEncoding_Term.Term_sort)
                             | uu____10209 ->
                                 FStar_SMTEncoding_Util.mkApp (vtok, []) in
                           let mk_disc_proj_axioms guard encoded_res_t vapp
                             vars =
                             FStar_All.pipe_right quals
                               (FStar_List.collect
                                  (fun uu___115_10233  ->
                                     match uu___115_10233 with
                                     | FStar_Syntax_Syntax.Discriminator d ->
                                         let uu____10236 =
                                           FStar_Util.prefix vars in
                                         (match uu____10236 with
                                          | (uu____10247,(xxsym,uu____10249))
                                              ->
                                              let xx =
                                                FStar_SMTEncoding_Util.mkFreeV
                                                  (xxsym,
                                                    FStar_SMTEncoding_Term.Term_sort) in
                                              let uu____10259 =
                                                let uu____10260 =
                                                  let uu____10264 =
                                                    let uu____10265 =
                                                      let uu____10271 =
                                                        let uu____10272 =
                                                          let uu____10275 =
                                                            let uu____10276 =
                                                              FStar_SMTEncoding_Term.mk_tester
                                                                (escape
                                                                   d.FStar_Ident.str)
                                                                xx in
                                                            FStar_All.pipe_left
                                                              FStar_SMTEncoding_Term.boxBool
                                                              uu____10276 in
                                                          (vapp, uu____10275) in
                                                        FStar_SMTEncoding_Util.mkEq
                                                          uu____10272 in
                                                      ([[vapp]], vars,
                                                        uu____10271) in
                                                    FStar_SMTEncoding_Util.mkForall
                                                      uu____10265 in
                                                  (uu____10264,
                                                    (Some
                                                       "Discriminator equation"),
                                                    (Prims.strcat
                                                       "disc_equation_"
                                                       (escape
                                                          d.FStar_Ident.str))) in
                                                FStar_SMTEncoding_Util.mkAssume
                                                  uu____10260 in
                                              [uu____10259])
                                     | FStar_Syntax_Syntax.Projector 
                                         (d,f) ->
                                         let uu____10287 =
                                           FStar_Util.prefix vars in
                                         (match uu____10287 with
                                          | (uu____10298,(xxsym,uu____10300))
                                              ->
                                              let xx =
                                                FStar_SMTEncoding_Util.mkFreeV
                                                  (xxsym,
                                                    FStar_SMTEncoding_Term.Term_sort) in
                                              let f1 =
                                                {
                                                  FStar_Syntax_Syntax.ppname
                                                    = f;
                                                  FStar_Syntax_Syntax.index =
                                                    (Prims.parse_int "0");
                                                  FStar_Syntax_Syntax.sort =
                                                    FStar_Syntax_Syntax.tun
                                                } in
                                              let tp_name =
                                                mk_term_projector_name d f1 in
                                              let prim_app =
                                                FStar_SMTEncoding_Util.mkApp
                                                  (tp_name, [xx]) in
                                              let uu____10314 =
                                                let uu____10315 =
                                                  let uu____10319 =
                                                    let uu____10320 =
                                                      let uu____10326 =
                                                        FStar_SMTEncoding_Util.mkEq
                                                          (vapp, prim_app) in
                                                      ([[vapp]], vars,
                                                        uu____10326) in
                                                    FStar_SMTEncoding_Util.mkForall
                                                      uu____10320 in
                                                  (uu____10319,
                                                    (Some
                                                       "Projector equation"),
                                                    (Prims.strcat
                                                       "proj_equation_"
                                                       tp_name)) in
                                                FStar_SMTEncoding_Util.mkAssume
                                                  uu____10315 in
                                              [uu____10314])
                                     | uu____10335 -> [])) in
                           let uu____10336 = encode_binders None formals env1 in
                           (match uu____10336 with
                            | (vars,guards,env',decls1,uu____10352) ->
                                let uu____10359 =
                                  match pre_opt with
                                  | None  ->
                                      let uu____10364 =
                                        FStar_SMTEncoding_Util.mk_and_l
                                          guards in
                                      (uu____10364, decls1)
                                  | Some p ->
                                      let uu____10366 = encode_formula p env' in
                                      (match uu____10366 with
                                       | (g,ds) ->
                                           let uu____10373 =
                                             FStar_SMTEncoding_Util.mk_and_l
                                               (g :: guards) in
                                           (uu____10373,
                                             (FStar_List.append decls1 ds))) in
                                (match uu____10359 with
                                 | (guard,decls11) ->
                                     let vtok_app = mk_Apply vtok_tm vars in
                                     let vapp =
                                       let uu____10382 =
                                         let uu____10386 =
                                           FStar_List.map
                                             FStar_SMTEncoding_Util.mkFreeV
                                             vars in
                                         (vname, uu____10386) in
                                       FStar_SMTEncoding_Util.mkApp
                                         uu____10382 in
                                     let uu____10391 =
                                       let vname_decl =
                                         let uu____10396 =
                                           let uu____10402 =
                                             FStar_All.pipe_right formals
                                               (FStar_List.map
                                                  (fun uu____10407  ->
                                                     FStar_SMTEncoding_Term.Term_sort)) in
                                           (vname, uu____10402,
                                             FStar_SMTEncoding_Term.Term_sort,
                                             None) in
                                         FStar_SMTEncoding_Term.DeclFun
                                           uu____10396 in
                                       let uu____10412 =
                                         let env2 =
                                           let uu___145_10416 = env1 in
                                           {
                                             bindings =
                                               (uu___145_10416.bindings);
                                             depth = (uu___145_10416.depth);
                                             tcenv = (uu___145_10416.tcenv);
                                             warn = (uu___145_10416.warn);
                                             cache = (uu___145_10416.cache);
                                             nolabels =
                                               (uu___145_10416.nolabels);
                                             use_zfuel_name =
                                               (uu___145_10416.use_zfuel_name);
                                             encode_non_total_function_typ;
                                             current_module_name =
                                               (uu___145_10416.current_module_name)
                                           } in
                                         let uu____10417 =
                                           let uu____10418 =
                                             head_normal env2 tt in
                                           Prims.op_Negation uu____10418 in
                                         if uu____10417
                                         then
                                           encode_term_pred None tt env2
                                             vtok_tm
                                         else
                                           encode_term_pred None t_norm env2
                                             vtok_tm in
                                       match uu____10412 with
                                       | (tok_typing,decls2) ->
                                           let tok_typing1 =
                                             match formals with
                                             | uu____10428::uu____10429 ->
                                                 let ff =
                                                   ("ty",
                                                     FStar_SMTEncoding_Term.Term_sort) in
                                                 let f =
                                                   FStar_SMTEncoding_Util.mkFreeV
                                                     ff in
                                                 let vtok_app_l =
                                                   mk_Apply vtok_tm [ff] in
                                                 let vtok_app_r =
                                                   mk_Apply f
                                                     [(vtok,
                                                        FStar_SMTEncoding_Term.Term_sort)] in
                                                 let guarded_tok_typing =
                                                   let uu____10452 =
                                                     let uu____10458 =
                                                       FStar_SMTEncoding_Term.mk_NoHoist
                                                         f tok_typing in
                                                     ([[vtok_app_l];
                                                      [vtok_app_r]], 
                                                       [ff], uu____10458) in
                                                   FStar_SMTEncoding_Util.mkForall
                                                     uu____10452 in
                                                 FStar_SMTEncoding_Util.mkAssume
                                                   (guarded_tok_typing,
                                                     (Some
                                                        "function token typing"),
                                                     (Prims.strcat
                                                        "function_token_typing_"
                                                        vname))
                                             | uu____10472 ->
                                                 FStar_SMTEncoding_Util.mkAssume
                                                   (tok_typing,
                                                     (Some
                                                        "function token typing"),
                                                     (Prims.strcat
                                                        "function_token_typing_"
                                                        vname)) in
                                           let uu____10474 =
                                             match formals with
                                             | [] ->
                                                 let uu____10483 =
                                                   let uu____10484 =
                                                     let uu____10486 =
                                                       FStar_SMTEncoding_Util.mkFreeV
                                                         (vname,
                                                           FStar_SMTEncoding_Term.Term_sort) in
                                                     FStar_All.pipe_left
                                                       (fun _0_34  ->
                                                          Some _0_34)
                                                       uu____10486 in
                                                   push_free_var env1 lid
                                                     vname uu____10484 in
                                                 ((FStar_List.append decls2
                                                     [tok_typing1]),
                                                   uu____10483)
                                             | uu____10489 ->
                                                 let vtok_decl =
                                                   FStar_SMTEncoding_Term.DeclFun
                                                     (vtok, [],
                                                       FStar_SMTEncoding_Term.Term_sort,
                                                       None) in
                                                 let vtok_fresh =
                                                   let uu____10494 =
                                                     varops.next_id () in
                                                   FStar_SMTEncoding_Term.fresh_token
                                                     (vtok,
                                                       FStar_SMTEncoding_Term.Term_sort)
                                                     uu____10494 in
                                                 let name_tok_corr =
                                                   let uu____10496 =
                                                     let uu____10500 =
                                                       let uu____10501 =
                                                         let uu____10507 =
                                                           FStar_SMTEncoding_Util.mkEq
                                                             (vtok_app, vapp) in
                                                         ([[vtok_app];
                                                          [vapp]], vars,
                                                           uu____10507) in
                                                       FStar_SMTEncoding_Util.mkForall
                                                         uu____10501 in
                                                     (uu____10500,
                                                       (Some
                                                          "Name-token correspondence"),
                                                       (Prims.strcat
                                                          "token_correspondence_"
                                                          vname)) in
                                                   FStar_SMTEncoding_Util.mkAssume
                                                     uu____10496 in
                                                 ((FStar_List.append decls2
                                                     [vtok_decl;
                                                     vtok_fresh;
                                                     name_tok_corr;
                                                     tok_typing1]), env1) in
                                           (match uu____10474 with
                                            | (tok_decl,env2) ->
                                                ((vname_decl :: tok_decl),
                                                  env2)) in
                                     (match uu____10391 with
                                      | (decls2,env2) ->
                                          let uu____10531 =
                                            let res_t1 =
                                              FStar_Syntax_Subst.compress
                                                res_t in
                                            let uu____10536 =
                                              encode_term res_t1 env' in
                                            match uu____10536 with
                                            | (encoded_res_t,decls) ->
                                                let uu____10544 =
                                                  FStar_SMTEncoding_Term.mk_HasType
                                                    vapp encoded_res_t in
                                                (encoded_res_t, uu____10544,
                                                  decls) in
                                          (match uu____10531 with
                                           | (encoded_res_t,ty_pred,decls3)
                                               ->
                                               let typingAx =
                                                 let uu____10552 =
                                                   let uu____10556 =
                                                     let uu____10557 =
                                                       let uu____10563 =
                                                         FStar_SMTEncoding_Util.mkImp
                                                           (guard, ty_pred) in
                                                       ([[vapp]], vars,
                                                         uu____10563) in
                                                     FStar_SMTEncoding_Util.mkForall
                                                       uu____10557 in
                                                   (uu____10556,
                                                     (Some "free var typing"),
                                                     (Prims.strcat "typing_"
                                                        vname)) in
                                                 FStar_SMTEncoding_Util.mkAssume
                                                   uu____10552 in
                                               let freshness =
                                                 let uu____10572 =
                                                   FStar_All.pipe_right quals
                                                     (FStar_List.contains
                                                        FStar_Syntax_Syntax.New) in
                                                 if uu____10572
                                                 then
                                                   let uu____10575 =
                                                     let uu____10576 =
                                                       let uu____10582 =
                                                         FStar_All.pipe_right
                                                           vars
                                                           (FStar_List.map
                                                              FStar_Pervasives.snd) in
                                                       let uu____10588 =
                                                         varops.next_id () in
                                                       (vname, uu____10582,
                                                         FStar_SMTEncoding_Term.Term_sort,
                                                         uu____10588) in
                                                     FStar_SMTEncoding_Term.fresh_constructor
                                                       uu____10576 in
                                                   let uu____10590 =
                                                     let uu____10592 =
                                                       pretype_axiom env2
                                                         vapp vars in
                                                     [uu____10592] in
                                                   uu____10575 :: uu____10590
                                                 else [] in
                                               let g =
                                                 let uu____10596 =
                                                   let uu____10598 =
                                                     let uu____10600 =
                                                       let uu____10602 =
                                                         let uu____10604 =
                                                           mk_disc_proj_axioms
                                                             guard
                                                             encoded_res_t
                                                             vapp vars in
                                                         typingAx ::
                                                           uu____10604 in
                                                       FStar_List.append
                                                         freshness
                                                         uu____10602 in
                                                     FStar_List.append decls3
                                                       uu____10600 in
                                                   FStar_List.append decls2
                                                     uu____10598 in
                                                 FStar_List.append decls11
                                                   uu____10596 in
                                               (g, env2))))))))
let declare_top_level_let:
  env_t ->
    FStar_Syntax_Syntax.fv ->
      FStar_Syntax_Syntax.term ->
        FStar_Syntax_Syntax.term ->
          ((Prims.string* FStar_SMTEncoding_Term.term option)*
            FStar_SMTEncoding_Term.decl Prims.list* env_t)
  =
  fun env  ->
    fun x  ->
      fun t  ->
        fun t_norm  ->
          let uu____10626 =
            try_lookup_lid env
              (x.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          match uu____10626 with
          | None  ->
              let uu____10649 = encode_free_var env x t t_norm [] in
              (match uu____10649 with
               | (decls,env1) ->
                   let uu____10664 =
                     lookup_lid env1
                       (x.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                   (match uu____10664 with
                    | (n1,x',uu____10683) -> ((n1, x'), decls, env1)))
          | Some (n1,x1,uu____10695) -> ((n1, x1), [], env)
let encode_top_level_val:
  env_t ->
    FStar_Syntax_Syntax.fv ->
      FStar_Syntax_Syntax.term ->
        FStar_Syntax_Syntax.qualifier Prims.list ->
          (FStar_SMTEncoding_Term.decl Prims.list* env_t)
  =
  fun env  ->
    fun lid  ->
      fun t  ->
        fun quals  ->
          let tt = norm env t in
          let uu____10728 = encode_free_var env lid t tt quals in
          match uu____10728 with
          | (decls,env1) ->
              let uu____10739 = FStar_Syntax_Util.is_smt_lemma t in
              if uu____10739
              then
                let uu____10743 =
                  let uu____10745 = encode_smt_lemma env1 lid tt in
                  FStar_List.append decls uu____10745 in
                (uu____10743, env1)
              else (decls, env1)
let encode_top_level_vals:
  env_t ->
    FStar_Syntax_Syntax.letbinding Prims.list ->
      FStar_Syntax_Syntax.qualifier Prims.list ->
        (FStar_SMTEncoding_Term.decl Prims.list* env_t)
  =
  fun env  ->
    fun bindings  ->
      fun quals  ->
        FStar_All.pipe_right bindings
          (FStar_List.fold_left
             (fun uu____10773  ->
                fun lb  ->
                  match uu____10773 with
                  | (decls,env1) ->
                      let uu____10785 =
                        let uu____10789 =
                          FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
                        encode_top_level_val env1 uu____10789
                          lb.FStar_Syntax_Syntax.lbtyp quals in
                      (match uu____10785 with
                       | (decls',env2) ->
                           ((FStar_List.append decls decls'), env2)))
             ([], env))
let is_tactic: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let fstar_tactics_tactic_lid =
      FStar_Syntax_Const.p2l ["FStar"; "Tactics"; "tactic"] in
    let uu____10803 = FStar_Syntax_Util.head_and_args t in
    match uu____10803 with
    | (hd1,args) ->
        let uu____10829 =
          let uu____10830 = FStar_Syntax_Util.un_uinst hd1 in
          uu____10830.FStar_Syntax_Syntax.n in
        (match uu____10829 with
         | FStar_Syntax_Syntax.Tm_fvar fv when
             FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_tactic_lid ->
             true
         | FStar_Syntax_Syntax.Tm_arrow (uu____10834,c) ->
             let effect_name = FStar_Syntax_Util.comp_effect_name c in
             FStar_Util.starts_with "FStar.Tactics"
               effect_name.FStar_Ident.str
         | uu____10847 -> false)
let encode_top_level_let:
  env_t ->
    (Prims.bool* FStar_Syntax_Syntax.letbinding Prims.list) ->
      FStar_Syntax_Syntax.qualifier Prims.list ->
        (FStar_SMTEncoding_Term.decl Prims.list* env_t)
  =
  fun env  ->
    fun uu____10862  ->
      fun quals  ->
        match uu____10862 with
        | (is_rec,bindings) ->
            let eta_expand1 binders formals body t =
              let nbinders = FStar_List.length binders in
              let uu____10911 = FStar_Util.first_N nbinders formals in
              match uu____10911 with
              | (formals1,extra_formals) ->
                  let subst1 =
                    FStar_List.map2
                      (fun uu____10951  ->
                         fun uu____10952  ->
                           match (uu____10951, uu____10952) with
                           | ((formal,uu____10962),(binder,uu____10964)) ->
                               let uu____10969 =
                                 let uu____10974 =
                                   FStar_Syntax_Syntax.bv_to_name binder in
                                 (formal, uu____10974) in
                               FStar_Syntax_Syntax.NT uu____10969) formals1
                      binders in
                  let extra_formals1 =
                    let uu____10979 =
                      FStar_All.pipe_right extra_formals
                        (FStar_List.map
                           (fun uu____10993  ->
                              match uu____10993 with
                              | (x,i) ->
                                  let uu____11000 =
                                    let uu___146_11001 = x in
                                    let uu____11002 =
                                      FStar_Syntax_Subst.subst subst1
                                        x.FStar_Syntax_Syntax.sort in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___146_11001.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___146_11001.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = uu____11002
                                    } in
                                  (uu____11000, i))) in
                    FStar_All.pipe_right uu____10979
                      FStar_Syntax_Util.name_binders in
                  let body1 =
                    let uu____11014 =
                      let uu____11016 =
                        let uu____11017 = FStar_Syntax_Subst.subst subst1 t in
                        uu____11017.FStar_Syntax_Syntax.n in
                      FStar_All.pipe_left (fun _0_35  -> Some _0_35)
                        uu____11016 in
                    let uu____11021 =
                      let uu____11022 = FStar_Syntax_Subst.compress body in
                      let uu____11023 =
                        let uu____11024 =
                          FStar_Syntax_Util.args_of_binders extra_formals1 in
                        FStar_All.pipe_left FStar_Pervasives.snd uu____11024 in
                      FStar_Syntax_Syntax.extend_app_n uu____11022
                        uu____11023 in
                    uu____11021 uu____11014 body.FStar_Syntax_Syntax.pos in
                  ((FStar_List.append binders extra_formals1), body1) in
            let destruct_bound_function flid t_norm e =
              let get_result_type c =
                let uu____11066 =
                  FStar_TypeChecker_Env.is_reifiable_comp env.tcenv c in
                if uu____11066
                then
                  FStar_TypeChecker_Env.reify_comp
                    (let uu___147_11067 = env.tcenv in
                     {
                       FStar_TypeChecker_Env.solver =
                         (uu___147_11067.FStar_TypeChecker_Env.solver);
                       FStar_TypeChecker_Env.range =
                         (uu___147_11067.FStar_TypeChecker_Env.range);
                       FStar_TypeChecker_Env.curmodule =
                         (uu___147_11067.FStar_TypeChecker_Env.curmodule);
                       FStar_TypeChecker_Env.gamma =
                         (uu___147_11067.FStar_TypeChecker_Env.gamma);
                       FStar_TypeChecker_Env.gamma_cache =
                         (uu___147_11067.FStar_TypeChecker_Env.gamma_cache);
                       FStar_TypeChecker_Env.modules =
                         (uu___147_11067.FStar_TypeChecker_Env.modules);
                       FStar_TypeChecker_Env.expected_typ =
                         (uu___147_11067.FStar_TypeChecker_Env.expected_typ);
                       FStar_TypeChecker_Env.sigtab =
                         (uu___147_11067.FStar_TypeChecker_Env.sigtab);
                       FStar_TypeChecker_Env.is_pattern =
                         (uu___147_11067.FStar_TypeChecker_Env.is_pattern);
                       FStar_TypeChecker_Env.instantiate_imp =
                         (uu___147_11067.FStar_TypeChecker_Env.instantiate_imp);
                       FStar_TypeChecker_Env.effects =
                         (uu___147_11067.FStar_TypeChecker_Env.effects);
                       FStar_TypeChecker_Env.generalize =
                         (uu___147_11067.FStar_TypeChecker_Env.generalize);
                       FStar_TypeChecker_Env.letrecs =
                         (uu___147_11067.FStar_TypeChecker_Env.letrecs);
                       FStar_TypeChecker_Env.top_level =
                         (uu___147_11067.FStar_TypeChecker_Env.top_level);
                       FStar_TypeChecker_Env.check_uvars =
                         (uu___147_11067.FStar_TypeChecker_Env.check_uvars);
                       FStar_TypeChecker_Env.use_eq =
                         (uu___147_11067.FStar_TypeChecker_Env.use_eq);
                       FStar_TypeChecker_Env.is_iface =
                         (uu___147_11067.FStar_TypeChecker_Env.is_iface);
                       FStar_TypeChecker_Env.admit =
                         (uu___147_11067.FStar_TypeChecker_Env.admit);
                       FStar_TypeChecker_Env.lax = true;
                       FStar_TypeChecker_Env.lax_universes =
                         (uu___147_11067.FStar_TypeChecker_Env.lax_universes);
                       FStar_TypeChecker_Env.type_of =
                         (uu___147_11067.FStar_TypeChecker_Env.type_of);
                       FStar_TypeChecker_Env.universe_of =
                         (uu___147_11067.FStar_TypeChecker_Env.universe_of);
                       FStar_TypeChecker_Env.use_bv_sorts =
                         (uu___147_11067.FStar_TypeChecker_Env.use_bv_sorts);
                       FStar_TypeChecker_Env.qname_and_index =
                         (uu___147_11067.FStar_TypeChecker_Env.qname_and_index)
                     }) c FStar_Syntax_Syntax.U_unknown
                else FStar_Syntax_Util.comp_result c in
              let rec aux norm1 t_norm1 =
                let uu____11088 = FStar_Syntax_Util.abs_formals e in
                match uu____11088 with
                | (binders,body,lopt) ->
                    (match binders with
                     | uu____11137::uu____11138 ->
                         let uu____11146 =
                           let uu____11147 =
                             FStar_Syntax_Subst.compress t_norm1 in
                           uu____11147.FStar_Syntax_Syntax.n in
                         (match uu____11146 with
                          | FStar_Syntax_Syntax.Tm_arrow (formals,c) ->
                              let uu____11174 =
                                FStar_Syntax_Subst.open_comp formals c in
                              (match uu____11174 with
                               | (formals1,c1) ->
                                   let nformals = FStar_List.length formals1 in
                                   let nbinders = FStar_List.length binders in
                                   let tres = get_result_type c1 in
                                   let uu____11200 =
                                     (nformals < nbinders) &&
                                       (FStar_Syntax_Util.is_total_comp c1) in
                                   if uu____11200
                                   then
                                     let uu____11218 =
                                       FStar_Util.first_N nformals binders in
                                     (match uu____11218 with
                                      | (bs0,rest) ->
                                          let c2 =
                                            let subst1 =
                                              FStar_List.map2
                                                (fun uu____11264  ->
                                                   fun uu____11265  ->
                                                     match (uu____11264,
                                                             uu____11265)
                                                     with
                                                     | ((x,uu____11275),
                                                        (b,uu____11277)) ->
                                                         let uu____11282 =
                                                           let uu____11287 =
                                                             FStar_Syntax_Syntax.bv_to_name
                                                               b in
                                                           (x, uu____11287) in
                                                         FStar_Syntax_Syntax.NT
                                                           uu____11282)
                                                formals1 bs0 in
                                            FStar_Syntax_Subst.subst_comp
                                              subst1 c1 in
                                          let body1 =
                                            FStar_Syntax_Util.abs rest body
                                              lopt in
                                          let uu____11289 =
                                            let uu____11300 =
                                              get_result_type c2 in
                                            (bs0, body1, bs0, uu____11300) in
                                          (uu____11289, false))
                                   else
                                     if nformals > nbinders
                                     then
                                       (let uu____11335 =
                                          eta_expand1 binders formals1 body
                                            tres in
                                        match uu____11335 with
                                        | (binders1,body1) ->
                                            ((binders1, body1, formals1,
                                               tres), false))
                                     else
                                       ((binders, body, formals1, tres),
                                         false))
                          | FStar_Syntax_Syntax.Tm_refine (x,uu____11387) ->
                              let uu____11392 =
                                let uu____11403 =
                                  aux norm1 x.FStar_Syntax_Syntax.sort in
                                fst uu____11403 in
                              (uu____11392, true)
                          | uu____11436 when Prims.op_Negation norm1 ->
                              let t_norm2 =
                                FStar_TypeChecker_Normalize.normalize
                                  [FStar_TypeChecker_Normalize.AllowUnboundUniverses;
                                  FStar_TypeChecker_Normalize.Beta;
                                  FStar_TypeChecker_Normalize.WHNF;
                                  FStar_TypeChecker_Normalize.Exclude
                                    FStar_TypeChecker_Normalize.Zeta;
                                  FStar_TypeChecker_Normalize.UnfoldUntil
                                    FStar_Syntax_Syntax.Delta_constant;
                                  FStar_TypeChecker_Normalize.EraseUniverses]
                                  env.tcenv t_norm1 in
                              aux true t_norm2
                          | uu____11438 ->
                              let uu____11439 =
                                let uu____11440 =
                                  FStar_Syntax_Print.term_to_string e in
                                let uu____11441 =
                                  FStar_Syntax_Print.term_to_string t_norm1 in
                                FStar_Util.format3
                                  "Impossible! let-bound lambda %s = %s has a type that's not a function: %s\n"
                                  flid.FStar_Ident.str uu____11440
                                  uu____11441 in
                              failwith uu____11439)
                     | uu____11454 ->
                         let uu____11455 =
                           let uu____11456 =
                             FStar_Syntax_Subst.compress t_norm1 in
                           uu____11456.FStar_Syntax_Syntax.n in
                         (match uu____11455 with
                          | FStar_Syntax_Syntax.Tm_arrow (formals,c) ->
                              let uu____11483 =
                                FStar_Syntax_Subst.open_comp formals c in
                              (match uu____11483 with
                               | (formals1,c1) ->
                                   let tres = get_result_type c1 in
                                   let uu____11501 =
                                     eta_expand1 [] formals1 e tres in
                                   (match uu____11501 with
                                    | (binders1,body1) ->
                                        ((binders1, body1, formals1, tres),
                                          false)))
                          | uu____11549 -> (([], e, [], t_norm1), false))) in
              aux false t_norm in
            (try
               let uu____11577 =
                 FStar_All.pipe_right bindings
                   (FStar_Util.for_all
                      (fun lb  ->
                         (FStar_Syntax_Util.is_lemma
                            lb.FStar_Syntax_Syntax.lbtyp)
                           || (is_tactic lb.FStar_Syntax_Syntax.lbtyp))) in
               if uu____11577
               then encode_top_level_vals env bindings quals
               else
                 (let uu____11584 =
                    FStar_All.pipe_right bindings
                      (FStar_List.fold_left
                         (fun uu____11625  ->
                            fun lb  ->
                              match uu____11625 with
                              | (toks,typs,decls,env1) ->
                                  ((let uu____11676 =
                                      FStar_Syntax_Util.is_lemma
                                        lb.FStar_Syntax_Syntax.lbtyp in
                                    if uu____11676
                                    then raise Let_rec_unencodeable
                                    else ());
                                   (let t_norm =
                                      whnf env1 lb.FStar_Syntax_Syntax.lbtyp in
                                    let uu____11679 =
                                      let uu____11687 =
                                        FStar_Util.right
                                          lb.FStar_Syntax_Syntax.lbname in
                                      declare_top_level_let env1 uu____11687
                                        lb.FStar_Syntax_Syntax.lbtyp t_norm in
                                    match uu____11679 with
                                    | (tok,decl,env2) ->
                                        let uu____11712 =
                                          let uu____11719 =
                                            let uu____11725 =
                                              FStar_Util.right
                                                lb.FStar_Syntax_Syntax.lbname in
                                            (uu____11725, tok) in
                                          uu____11719 :: toks in
                                        (uu____11712, (t_norm :: typs), (decl
                                          :: decls), env2))))
                         ([], [], [], env)) in
                  match uu____11584 with
                  | (toks,typs,decls,env1) ->
                      let toks1 = FStar_List.rev toks in
                      let decls1 =
                        FStar_All.pipe_right (FStar_List.rev decls)
                          FStar_List.flatten in
                      let typs1 = FStar_List.rev typs in
                      let mk_app1 curry f ftok vars =
                        match vars with
                        | [] ->
                            FStar_SMTEncoding_Util.mkFreeV
                              (f, FStar_SMTEncoding_Term.Term_sort)
                        | uu____11827 ->
                            if curry
                            then
                              (match ftok with
                               | Some ftok1 -> mk_Apply ftok1 vars
                               | None  ->
                                   let uu____11832 =
                                     FStar_SMTEncoding_Util.mkFreeV
                                       (f, FStar_SMTEncoding_Term.Term_sort) in
                                   mk_Apply uu____11832 vars)
                            else
                              (let uu____11834 =
                                 let uu____11838 =
                                   FStar_List.map
                                     FStar_SMTEncoding_Util.mkFreeV vars in
                                 (f, uu____11838) in
                               FStar_SMTEncoding_Util.mkApp uu____11834) in
                      let uu____11843 =
                        (FStar_All.pipe_right quals
                           (FStar_Util.for_some
                              (fun uu___116_11845  ->
                                 match uu___116_11845 with
                                 | FStar_Syntax_Syntax.HasMaskedEffect  ->
                                     true
                                 | uu____11846 -> false)))
                          ||
                          (FStar_All.pipe_right typs1
                             (FStar_Util.for_some
                                (fun t  ->
                                   let uu____11849 =
                                     (FStar_Syntax_Util.is_pure_or_ghost_function
                                        t)
                                       ||
                                       (FStar_TypeChecker_Env.is_reifiable_function
                                          env1.tcenv t) in
                                   FStar_All.pipe_left Prims.op_Negation
                                     uu____11849))) in
                      if uu____11843
                      then (decls1, env1)
                      else
                        if Prims.op_Negation is_rec
                        then
                          (match (bindings, typs1, toks1) with
                           | ({ FStar_Syntax_Syntax.lbname = uu____11869;
                                FStar_Syntax_Syntax.lbunivs = uvs;
                                FStar_Syntax_Syntax.lbtyp = uu____11871;
                                FStar_Syntax_Syntax.lbeff = uu____11872;
                                FStar_Syntax_Syntax.lbdef = e;_}::[],t_norm::[],
                              (flid_fv,(f,ftok))::[]) ->
                               let flid =
                                 (flid_fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                               let uu____11913 =
                                 let uu____11917 =
                                   FStar_TypeChecker_Env.open_universes_in
                                     env1.tcenv uvs [e; t_norm] in
                                 match uu____11917 with
                                 | (tcenv',uu____11928,e_t) ->
                                     let uu____11932 =
                                       match e_t with
                                       | e1::t_norm1::[] -> (e1, t_norm1)
                                       | uu____11939 -> failwith "Impossible" in
                                     (match uu____11932 with
                                      | (e1,t_norm1) ->
                                          ((let uu___150_11948 = env1 in
                                            {
                                              bindings =
                                                (uu___150_11948.bindings);
                                              depth = (uu___150_11948.depth);
                                              tcenv = tcenv';
                                              warn = (uu___150_11948.warn);
                                              cache = (uu___150_11948.cache);
                                              nolabels =
                                                (uu___150_11948.nolabels);
                                              use_zfuel_name =
                                                (uu___150_11948.use_zfuel_name);
                                              encode_non_total_function_typ =
                                                (uu___150_11948.encode_non_total_function_typ);
                                              current_module_name =
                                                (uu___150_11948.current_module_name)
                                            }), e1, t_norm1)) in
                               (match uu____11913 with
                                | (env',e1,t_norm1) ->
                                    let uu____11955 =
                                      destruct_bound_function flid t_norm1 e1 in
                                    (match uu____11955 with
                                     | ((binders,body,uu____11967,uu____11968),curry)
                                         ->
                                         ((let uu____11975 =
                                             FStar_All.pipe_left
                                               (FStar_TypeChecker_Env.debug
                                                  env1.tcenv)
                                               (FStar_Options.Other
                                                  "SMTEncoding") in
                                           if uu____11975
                                           then
                                             let uu____11976 =
                                               FStar_Syntax_Print.binders_to_string
                                                 ", " binders in
                                             let uu____11977 =
                                               FStar_Syntax_Print.term_to_string
                                                 body in
                                             FStar_Util.print2
                                               "Encoding let : binders=[%s], body=%s\n"
                                               uu____11976 uu____11977
                                           else ());
                                          (let uu____11979 =
                                             encode_binders None binders env' in
                                           match uu____11979 with
                                           | (vars,guards,env'1,binder_decls,uu____11995)
                                               ->
                                               let body1 =
                                                 let uu____12003 =
                                                   FStar_TypeChecker_Env.is_reifiable_function
                                                     env'1.tcenv t_norm1 in
                                                 if uu____12003
                                                 then
                                                   FStar_TypeChecker_Util.reify_body
                                                     env'1.tcenv body
                                                 else body in
                                               let app =
                                                 mk_app1 curry f ftok vars in
                                               let uu____12006 =
                                                 let uu____12011 =
                                                   FStar_All.pipe_right quals
                                                     (FStar_List.contains
                                                        FStar_Syntax_Syntax.Logic) in
                                                 if uu____12011
                                                 then
                                                   let uu____12017 =
                                                     FStar_SMTEncoding_Term.mk_Valid
                                                       app in
                                                   let uu____12018 =
                                                     encode_formula body1
                                                       env'1 in
                                                   (uu____12017, uu____12018)
                                                 else
                                                   (let uu____12024 =
                                                      encode_term body1 env'1 in
                                                    (app, uu____12024)) in
                                               (match uu____12006 with
                                                | (app1,(body2,decls2)) ->
                                                    let eqn =
                                                      let uu____12038 =
                                                        let uu____12042 =
                                                          let uu____12043 =
                                                            let uu____12049 =
                                                              FStar_SMTEncoding_Util.mkEq
                                                                (app1, body2) in
                                                            ([[app1]], vars,
                                                              uu____12049) in
                                                          FStar_SMTEncoding_Util.mkForall
                                                            uu____12043 in
                                                        let uu____12055 =
                                                          let uu____12057 =
                                                            FStar_Util.format1
                                                              "Equation for %s"
                                                              flid.FStar_Ident.str in
                                                          Some uu____12057 in
                                                        (uu____12042,
                                                          uu____12055,
                                                          (Prims.strcat
                                                             "equation_" f)) in
                                                      FStar_SMTEncoding_Util.mkAssume
                                                        uu____12038 in
                                                    let uu____12059 =
                                                      let uu____12061 =
                                                        let uu____12063 =
                                                          let uu____12065 =
                                                            let uu____12067 =
                                                              primitive_type_axioms
                                                                env1.tcenv
                                                                flid f app1 in
                                                            FStar_List.append
                                                              [eqn]
                                                              uu____12067 in
                                                          FStar_List.append
                                                            decls2
                                                            uu____12065 in
                                                        FStar_List.append
                                                          binder_decls
                                                          uu____12063 in
                                                      FStar_List.append
                                                        decls1 uu____12061 in
                                                    (uu____12059, env1))))))
                           | uu____12070 -> failwith "Impossible")
                        else
                          (let fuel =
                             let uu____12089 = varops.fresh "fuel" in
                             (uu____12089, FStar_SMTEncoding_Term.Fuel_sort) in
                           let fuel_tm = FStar_SMTEncoding_Util.mkFreeV fuel in
                           let env0 = env1 in
                           let uu____12092 =
                             FStar_All.pipe_right toks1
                               (FStar_List.fold_left
                                  (fun uu____12131  ->
                                     fun uu____12132  ->
                                       match (uu____12131, uu____12132) with
                                       | ((gtoks,env2),(flid_fv,(f,ftok))) ->
                                           let flid =
                                             (flid_fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                                           let g =
                                             let uu____12214 =
                                               FStar_Ident.lid_add_suffix
                                                 flid "fuel_instrumented" in
                                             varops.new_fvar uu____12214 in
                                           let gtok =
                                             let uu____12216 =
                                               FStar_Ident.lid_add_suffix
                                                 flid
                                                 "fuel_instrumented_token" in
                                             varops.new_fvar uu____12216 in
                                           let env3 =
                                             let uu____12218 =
                                               let uu____12220 =
                                                 FStar_SMTEncoding_Util.mkApp
                                                   (g, [fuel_tm]) in
                                               FStar_All.pipe_left
                                                 (fun _0_36  -> Some _0_36)
                                                 uu____12220 in
                                             push_free_var env2 flid gtok
                                               uu____12218 in
                                           (((flid, f, ftok, g, gtok) ::
                                             gtoks), env3)) ([], env1)) in
                           match uu____12092 with
                           | (gtoks,env2) ->
                               let gtoks1 = FStar_List.rev gtoks in
                               let encode_one_binding env01 uu____12306
                                 t_norm uu____12308 =
                                 match (uu____12306, uu____12308) with
                                 | ((flid,f,ftok,g,gtok),{
                                                           FStar_Syntax_Syntax.lbname
                                                             = lbn;
                                                           FStar_Syntax_Syntax.lbunivs
                                                             = uvs;
                                                           FStar_Syntax_Syntax.lbtyp
                                                             = uu____12335;
                                                           FStar_Syntax_Syntax.lbeff
                                                             = uu____12336;
                                                           FStar_Syntax_Syntax.lbdef
                                                             = e;_})
                                     ->
                                     let uu____12353 =
                                       let uu____12357 =
                                         FStar_TypeChecker_Env.open_universes_in
                                           env2.tcenv uvs [e; t_norm] in
                                       match uu____12357 with
                                       | (tcenv',uu____12372,e_t) ->
                                           let uu____12376 =
                                             match e_t with
                                             | e1::t_norm1::[] ->
                                                 (e1, t_norm1)
                                             | uu____12383 ->
                                                 failwith "Impossible" in
                                           (match uu____12376 with
                                            | (e1,t_norm1) ->
                                                ((let uu___151_12392 = env2 in
                                                  {
                                                    bindings =
                                                      (uu___151_12392.bindings);
                                                    depth =
                                                      (uu___151_12392.depth);
                                                    tcenv = tcenv';
                                                    warn =
                                                      (uu___151_12392.warn);
                                                    cache =
                                                      (uu___151_12392.cache);
                                                    nolabels =
                                                      (uu___151_12392.nolabels);
                                                    use_zfuel_name =
                                                      (uu___151_12392.use_zfuel_name);
                                                    encode_non_total_function_typ
                                                      =
                                                      (uu___151_12392.encode_non_total_function_typ);
                                                    current_module_name =
                                                      (uu___151_12392.current_module_name)
                                                  }), e1, t_norm1)) in
                                     (match uu____12353 with
                                      | (env',e1,t_norm1) ->
                                          ((let uu____12402 =
                                              FStar_All.pipe_left
                                                (FStar_TypeChecker_Env.debug
                                                   env01.tcenv)
                                                (FStar_Options.Other
                                                   "SMTEncoding") in
                                            if uu____12402
                                            then
                                              let uu____12403 =
                                                FStar_Syntax_Print.lbname_to_string
                                                  lbn in
                                              let uu____12404 =
                                                FStar_Syntax_Print.term_to_string
                                                  t_norm1 in
                                              let uu____12405 =
                                                FStar_Syntax_Print.term_to_string
                                                  e1 in
                                              FStar_Util.print3
                                                "Encoding let rec %s : %s = %s\n"
                                                uu____12403 uu____12404
                                                uu____12405
                                            else ());
                                           (let uu____12407 =
                                              destruct_bound_function flid
                                                t_norm1 e1 in
                                            match uu____12407 with
                                            | ((binders,body,formals,tres),curry)
                                                ->
                                                ((let uu____12429 =
                                                    FStar_All.pipe_left
                                                      (FStar_TypeChecker_Env.debug
                                                         env01.tcenv)
                                                      (FStar_Options.Other
                                                         "SMTEncoding") in
                                                  if uu____12429
                                                  then
                                                    let uu____12430 =
                                                      FStar_Syntax_Print.binders_to_string
                                                        ", " binders in
                                                    let uu____12431 =
                                                      FStar_Syntax_Print.term_to_string
                                                        body in
                                                    let uu____12432 =
                                                      FStar_Syntax_Print.binders_to_string
                                                        ", " formals in
                                                    let uu____12433 =
                                                      FStar_Syntax_Print.term_to_string
                                                        tres in
                                                    FStar_Util.print4
                                                      "Encoding let rec: binders=[%s], body=%s, formals=[%s], tres=%s\n"
                                                      uu____12430 uu____12431
                                                      uu____12432 uu____12433
                                                  else ());
                                                 if curry
                                                 then
                                                   failwith
                                                     "Unexpected type of let rec in SMT Encoding; expected it to be annotated with an arrow type"
                                                 else ();
                                                 (let uu____12437 =
                                                    encode_binders None
                                                      binders env' in
                                                  match uu____12437 with
                                                  | (vars,guards,env'1,binder_decls,uu____12455)
                                                      ->
                                                      let decl_g =
                                                        let uu____12463 =
                                                          let uu____12469 =
                                                            let uu____12471 =
                                                              FStar_List.map
                                                                FStar_Pervasives.snd
                                                                vars in
                                                            FStar_SMTEncoding_Term.Fuel_sort
                                                              :: uu____12471 in
                                                          (g, uu____12469,
                                                            FStar_SMTEncoding_Term.Term_sort,
                                                            (Some
                                                               "Fuel-instrumented function name")) in
                                                        FStar_SMTEncoding_Term.DeclFun
                                                          uu____12463 in
                                                      let env02 =
                                                        push_zfuel_name env01
                                                          flid g in
                                                      let decl_g_tok =
                                                        FStar_SMTEncoding_Term.DeclFun
                                                          (gtok, [],
                                                            FStar_SMTEncoding_Term.Term_sort,
                                                            (Some
                                                               "Token for fuel-instrumented partial applications")) in
                                                      let vars_tm =
                                                        FStar_List.map
                                                          FStar_SMTEncoding_Util.mkFreeV
                                                          vars in
                                                      let app =
                                                        let uu____12486 =
                                                          let uu____12490 =
                                                            FStar_List.map
                                                              FStar_SMTEncoding_Util.mkFreeV
                                                              vars in
                                                          (f, uu____12490) in
                                                        FStar_SMTEncoding_Util.mkApp
                                                          uu____12486 in
                                                      let gsapp =
                                                        let uu____12496 =
                                                          let uu____12500 =
                                                            let uu____12502 =
                                                              FStar_SMTEncoding_Util.mkApp
                                                                ("SFuel",
                                                                  [fuel_tm]) in
                                                            uu____12502 ::
                                                              vars_tm in
                                                          (g, uu____12500) in
                                                        FStar_SMTEncoding_Util.mkApp
                                                          uu____12496 in
                                                      let gmax =
                                                        let uu____12506 =
                                                          let uu____12510 =
                                                            let uu____12512 =
                                                              FStar_SMTEncoding_Util.mkApp
                                                                ("MaxFuel",
                                                                  []) in
                                                            uu____12512 ::
                                                              vars_tm in
                                                          (g, uu____12510) in
                                                        FStar_SMTEncoding_Util.mkApp
                                                          uu____12506 in
                                                      let body1 =
                                                        let uu____12516 =
                                                          FStar_TypeChecker_Env.is_reifiable_function
                                                            env'1.tcenv
                                                            t_norm1 in
                                                        if uu____12516
                                                        then
                                                          FStar_TypeChecker_Util.reify_body
                                                            env'1.tcenv body
                                                        else body in
                                                      let uu____12518 =
                                                        encode_term body1
                                                          env'1 in
                                                      (match uu____12518 with
                                                       | (body_tm,decls2) ->
                                                           let eqn_g =
                                                             let uu____12529
                                                               =
                                                               let uu____12533
                                                                 =
                                                                 let uu____12534
                                                                   =
                                                                   let uu____12542
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (gsapp,
                                                                    body_tm) in
                                                                   ([[gsapp]],
                                                                    (Some
                                                                    (Prims.parse_int
                                                                    "0")),
                                                                    (fuel ::
                                                                    vars),
                                                                    uu____12542) in
                                                                 FStar_SMTEncoding_Util.mkForall'
                                                                   uu____12534 in
                                                               let uu____12553
                                                                 =
                                                                 let uu____12555
                                                                   =
                                                                   FStar_Util.format1
                                                                    "Equation for fuel-instrumented recursive function: %s"
                                                                    flid.FStar_Ident.str in
                                                                 Some
                                                                   uu____12555 in
                                                               (uu____12533,
                                                                 uu____12553,
                                                                 (Prims.strcat
                                                                    "equation_with_fuel_"
                                                                    g)) in
                                                             FStar_SMTEncoding_Util.mkAssume
                                                               uu____12529 in
                                                           let eqn_f =
                                                             let uu____12558
                                                               =
                                                               let uu____12562
                                                                 =
                                                                 let uu____12563
                                                                   =
                                                                   let uu____12569
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (app,
                                                                    gmax) in
                                                                   ([[app]],
                                                                    vars,
                                                                    uu____12569) in
                                                                 FStar_SMTEncoding_Util.mkForall
                                                                   uu____12563 in
                                                               (uu____12562,
                                                                 (Some
                                                                    "Correspondence of recursive function to instrumented version"),
                                                                 (Prims.strcat
                                                                    "@fuel_correspondence_"
                                                                    g)) in
                                                             FStar_SMTEncoding_Util.mkAssume
                                                               uu____12558 in
                                                           let eqn_g' =
                                                             let uu____12577
                                                               =
                                                               let uu____12581
                                                                 =
                                                                 let uu____12582
                                                                   =
                                                                   let uu____12588
                                                                    =
                                                                    let uu____12589
                                                                    =
                                                                    let uu____12592
                                                                    =
                                                                    let uu____12593
                                                                    =
                                                                    let uu____12597
                                                                    =
                                                                    let uu____12599
                                                                    =
                                                                    FStar_SMTEncoding_Term.n_fuel
                                                                    (Prims.parse_int
                                                                    "0") in
                                                                    uu____12599
                                                                    ::
                                                                    vars_tm in
                                                                    (g,
                                                                    uu____12597) in
                                                                    FStar_SMTEncoding_Util.mkApp
                                                                    uu____12593 in
                                                                    (gsapp,
                                                                    uu____12592) in
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    uu____12589 in
                                                                   ([[gsapp]],
                                                                    (fuel ::
                                                                    vars),
                                                                    uu____12588) in
                                                                 FStar_SMTEncoding_Util.mkForall
                                                                   uu____12582 in
                                                               (uu____12581,
                                                                 (Some
                                                                    "Fuel irrelevance"),
                                                                 (Prims.strcat
                                                                    "@fuel_irrelevance_"
                                                                    g)) in
                                                             FStar_SMTEncoding_Util.mkAssume
                                                               uu____12577 in
                                                           let uu____12611 =
                                                             let uu____12616
                                                               =
                                                               encode_binders
                                                                 None formals
                                                                 env02 in
                                                             match uu____12616
                                                             with
                                                             | (vars1,v_guards,env3,binder_decls1,uu____12633)
                                                                 ->
                                                                 let vars_tm1
                                                                   =
                                                                   FStar_List.map
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    vars1 in
                                                                 let gapp =
                                                                   FStar_SMTEncoding_Util.mkApp
                                                                    (g,
                                                                    (fuel_tm
                                                                    ::
                                                                    vars_tm1)) in
                                                                 let tok_corr
                                                                   =
                                                                   let tok_app
                                                                    =
                                                                    let uu____12648
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    (gtok,
                                                                    FStar_SMTEncoding_Term.Term_sort) in
                                                                    mk_Apply
                                                                    uu____12648
                                                                    (fuel ::
                                                                    vars1) in
                                                                   let uu____12651
                                                                    =
                                                                    let uu____12655
                                                                    =
                                                                    let uu____12656
                                                                    =
                                                                    let uu____12662
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (tok_app,
                                                                    gapp) in
                                                                    ([
                                                                    [tok_app]],
                                                                    (fuel ::
                                                                    vars1),
                                                                    uu____12662) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____12656 in
                                                                    (uu____12655,
                                                                    (Some
                                                                    "Fuel token correspondence"),
                                                                    (Prims.strcat
                                                                    "fuel_token_correspondence_"
                                                                    gtok)) in
                                                                   FStar_SMTEncoding_Util.mkAssume
                                                                    uu____12651 in
                                                                 let uu____12673
                                                                   =
                                                                   let uu____12677
                                                                    =
                                                                    encode_term_pred
                                                                    None tres
                                                                    env3 gapp in
                                                                   match uu____12677
                                                                   with
                                                                   | 
                                                                   (g_typing,d3)
                                                                    ->
                                                                    let uu____12685
                                                                    =
                                                                    let uu____12687
                                                                    =
                                                                    let uu____12688
                                                                    =
                                                                    let uu____12692
                                                                    =
                                                                    let uu____12693
                                                                    =
                                                                    let uu____12699
                                                                    =
                                                                    let uu____12700
                                                                    =
                                                                    let uu____12703
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    v_guards in
                                                                    (uu____12703,
                                                                    g_typing) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____12700 in
                                                                    ([[gapp]],
                                                                    (fuel ::
                                                                    vars1),
                                                                    uu____12699) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____12693 in
                                                                    (uu____12692,
                                                                    (Some
                                                                    "Typing correspondence of token to term"),
                                                                    (Prims.strcat
                                                                    "token_correspondence_"
                                                                    g)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____12688 in
                                                                    [uu____12687] in
                                                                    (d3,
                                                                    uu____12685) in
                                                                 (match uu____12673
                                                                  with
                                                                  | (aux_decls,typing_corr)
                                                                    ->
                                                                    ((FStar_List.append
                                                                    binder_decls1
                                                                    aux_decls),
                                                                    (FStar_List.append
                                                                    typing_corr
                                                                    [tok_corr]))) in
                                                           (match uu____12611
                                                            with
                                                            | (aux_decls,g_typing)
                                                                ->
                                                                ((FStar_List.append
                                                                    binder_decls
                                                                    (
                                                                    FStar_List.append
                                                                    decls2
                                                                    (FStar_List.append
                                                                    aux_decls
                                                                    [decl_g;
                                                                    decl_g_tok]))),
                                                                  (FStar_List.append
                                                                    [eqn_g;
                                                                    eqn_g';
                                                                    eqn_f]
                                                                    g_typing),
                                                                  env02)))))))) in
                               let uu____12738 =
                                 let uu____12745 =
                                   FStar_List.zip3 gtoks1 typs1 bindings in
                                 FStar_List.fold_left
                                   (fun uu____12781  ->
                                      fun uu____12782  ->
                                        match (uu____12781, uu____12782) with
                                        | ((decls2,eqns,env01),(gtok,ty,lb))
                                            ->
                                            let uu____12868 =
                                              encode_one_binding env01 gtok
                                                ty lb in
                                            (match uu____12868 with
                                             | (decls',eqns',env02) ->
                                                 ((decls' :: decls2),
                                                   (FStar_List.append eqns'
                                                      eqns), env02)))
                                   ([decls1], [], env0) uu____12745 in
                               (match uu____12738 with
                                | (decls2,eqns,env01) ->
                                    let uu____12908 =
                                      let isDeclFun uu___117_12916 =
                                        match uu___117_12916 with
                                        | FStar_SMTEncoding_Term.DeclFun
                                            uu____12917 -> true
                                        | uu____12923 -> false in
                                      let uu____12924 =
                                        FStar_All.pipe_right decls2
                                          FStar_List.flatten in
                                      FStar_All.pipe_right uu____12924
                                        (FStar_List.partition isDeclFun) in
                                    (match uu____12908 with
                                     | (prefix_decls,rest) ->
                                         let eqns1 = FStar_List.rev eqns in
                                         ((FStar_List.append prefix_decls
                                             (FStar_List.append rest eqns1)),
                                           env01)))))
             with
             | Let_rec_unencodeable  ->
                 let msg =
                   let uu____12951 =
                     FStar_All.pipe_right bindings
                       (FStar_List.map
                          (fun lb  ->
                             FStar_Syntax_Print.lbname_to_string
                               lb.FStar_Syntax_Syntax.lbname)) in
                   FStar_All.pipe_right uu____12951
                     (FStar_String.concat " and ") in
                 let decl =
                   FStar_SMTEncoding_Term.Caption
                     (Prims.strcat "let rec unencodeable: Skipping: " msg) in
                 ([decl], env))
let rec encode_sigelt:
  env_t ->
    FStar_Syntax_Syntax.sigelt -> (FStar_SMTEncoding_Term.decls_t* env_t)
  =
  fun env  ->
    fun se  ->
      let nm =
        let uu____12984 = FStar_Syntax_Util.lid_of_sigelt se in
        match uu____12984 with | None  -> "" | Some l -> l.FStar_Ident.str in
      let uu____12987 = encode_sigelt' env se in
      match uu____12987 with
      | (g,env1) ->
          let g1 =
            match g with
            | [] ->
                let uu____12997 =
                  let uu____12998 = FStar_Util.format1 "<Skipped %s/>" nm in
                  FStar_SMTEncoding_Term.Caption uu____12998 in
                [uu____12997]
            | uu____12999 ->
                let uu____13000 =
                  let uu____13002 =
                    let uu____13003 =
                      FStar_Util.format1 "<Start encoding %s>" nm in
                    FStar_SMTEncoding_Term.Caption uu____13003 in
                  uu____13002 :: g in
                let uu____13004 =
                  let uu____13006 =
                    let uu____13007 =
                      FStar_Util.format1 "</end encoding %s>" nm in
                    FStar_SMTEncoding_Term.Caption uu____13007 in
                  [uu____13006] in
                FStar_List.append uu____13000 uu____13004 in
          (g1, env1)
and encode_sigelt':
  env_t ->
    FStar_Syntax_Syntax.sigelt -> (FStar_SMTEncoding_Term.decls_t* env_t)
  =
  fun env  ->
    fun se  ->
      let is_opaque_to_smt t =
        let uu____13017 =
          let uu____13018 = FStar_Syntax_Subst.compress t in
          uu____13018.FStar_Syntax_Syntax.n in
        match uu____13017 with
        | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string
            (bytes,uu____13022)) ->
            (FStar_Util.string_of_bytes bytes) = "opaque_to_smt"
        | uu____13025 -> false in
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____13028 ->
          failwith "impossible -- removed by tc.fs"
      | FStar_Syntax_Syntax.Sig_pragma uu____13031 -> ([], env)
      | FStar_Syntax_Syntax.Sig_main uu____13033 -> ([], env)
      | FStar_Syntax_Syntax.Sig_effect_abbrev uu____13035 -> ([], env)
      | FStar_Syntax_Syntax.Sig_sub_effect uu____13043 -> ([], env)
      | FStar_Syntax_Syntax.Sig_new_effect ed ->
          let uu____13046 =
            let uu____13047 =
              FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                (FStar_List.contains FStar_Syntax_Syntax.Reifiable) in
            FStar_All.pipe_right uu____13047 Prims.op_Negation in
          if uu____13046
          then ([], env)
          else
            (let close_effect_params tm =
               match ed.FStar_Syntax_Syntax.binders with
               | [] -> tm
               | uu____13067 ->
                   let uu____13068 =
                     let uu____13071 =
                       let uu____13072 =
                         let uu____13087 =
                           FStar_All.pipe_left (fun _0_37  -> Some _0_37)
                             (FStar_Util.Inr
                                (FStar_Syntax_Const.effect_Tot_lid,
                                  [FStar_Syntax_Syntax.TOTAL])) in
                         ((ed.FStar_Syntax_Syntax.binders), tm, uu____13087) in
                       FStar_Syntax_Syntax.Tm_abs uu____13072 in
                     FStar_Syntax_Syntax.mk uu____13071 in
                   uu____13068 None tm.FStar_Syntax_Syntax.pos in
             let encode_action env1 a =
               let uu____13140 =
                 new_term_constant_and_tok_from_lid env1
                   a.FStar_Syntax_Syntax.action_name in
               match uu____13140 with
               | (aname,atok,env2) ->
                   let uu____13150 =
                     FStar_Syntax_Util.arrow_formals_comp
                       a.FStar_Syntax_Syntax.action_typ in
                   (match uu____13150 with
                    | (formals,uu____13160) ->
                        let uu____13167 =
                          let uu____13170 =
                            close_effect_params
                              a.FStar_Syntax_Syntax.action_defn in
                          encode_term uu____13170 env2 in
                        (match uu____13167 with
                         | (tm,decls) ->
                             let a_decls =
                               let uu____13178 =
                                 let uu____13179 =
                                   let uu____13185 =
                                     FStar_All.pipe_right formals
                                       (FStar_List.map
                                          (fun uu____13193  ->
                                             FStar_SMTEncoding_Term.Term_sort)) in
                                   (aname, uu____13185,
                                     FStar_SMTEncoding_Term.Term_sort,
                                     (Some "Action")) in
                                 FStar_SMTEncoding_Term.DeclFun uu____13179 in
                               [uu____13178;
                               FStar_SMTEncoding_Term.DeclFun
                                 (atok, [], FStar_SMTEncoding_Term.Term_sort,
                                   (Some "Action token"))] in
                             let uu____13200 =
                               let aux uu____13229 uu____13230 =
                                 match (uu____13229, uu____13230) with
                                 | ((bv,uu____13257),(env3,acc_sorts,acc)) ->
                                     let uu____13278 = gen_term_var env3 bv in
                                     (match uu____13278 with
                                      | (xxsym,xx,env4) ->
                                          (env4,
                                            ((xxsym,
                                               FStar_SMTEncoding_Term.Term_sort)
                                            :: acc_sorts), (xx :: acc))) in
                               FStar_List.fold_right aux formals
                                 (env2, [], []) in
                             (match uu____13200 with
                              | (uu____13316,xs_sorts,xs) ->
                                  let app =
                                    FStar_SMTEncoding_Util.mkApp (aname, xs) in
                                  let a_eq =
                                    let uu____13330 =
                                      let uu____13334 =
                                        let uu____13335 =
                                          let uu____13341 =
                                            let uu____13342 =
                                              let uu____13345 =
                                                mk_Apply tm xs_sorts in
                                              (app, uu____13345) in
                                            FStar_SMTEncoding_Util.mkEq
                                              uu____13342 in
                                          ([[app]], xs_sorts, uu____13341) in
                                        FStar_SMTEncoding_Util.mkForall
                                          uu____13335 in
                                      (uu____13334, (Some "Action equality"),
                                        (Prims.strcat aname "_equality")) in
                                    FStar_SMTEncoding_Util.mkAssume
                                      uu____13330 in
                                  let tok_correspondence =
                                    let tok_term =
                                      FStar_SMTEncoding_Util.mkFreeV
                                        (atok,
                                          FStar_SMTEncoding_Term.Term_sort) in
                                    let tok_app = mk_Apply tok_term xs_sorts in
                                    let uu____13357 =
                                      let uu____13361 =
                                        let uu____13362 =
                                          let uu____13368 =
                                            FStar_SMTEncoding_Util.mkEq
                                              (tok_app, app) in
                                          ([[tok_app]], xs_sorts,
                                            uu____13368) in
                                        FStar_SMTEncoding_Util.mkForall
                                          uu____13362 in
                                      (uu____13361,
                                        (Some "Action token correspondence"),
                                        (Prims.strcat aname
                                           "_token_correspondence")) in
                                    FStar_SMTEncoding_Util.mkAssume
                                      uu____13357 in
                                  (env2,
                                    (FStar_List.append decls
                                       (FStar_List.append a_decls
                                          [a_eq; tok_correspondence])))))) in
             let uu____13378 =
               FStar_Util.fold_map encode_action env
                 ed.FStar_Syntax_Syntax.actions in
             match uu____13378 with
             | (env1,decls2) -> ((FStar_List.flatten decls2), env1))
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____13394,uu____13395)
          when FStar_Ident.lid_equals lid FStar_Syntax_Const.precedes_lid ->
          let uu____13396 = new_term_constant_and_tok_from_lid env lid in
          (match uu____13396 with | (tname,ttok,env1) -> ([], env1))
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____13407,t) ->
          let quals = se.FStar_Syntax_Syntax.sigquals in
          let will_encode_definition =
            let uu____13412 =
              FStar_All.pipe_right quals
                (FStar_Util.for_some
                   (fun uu___118_13414  ->
                      match uu___118_13414 with
                      | FStar_Syntax_Syntax.Assumption  -> true
                      | FStar_Syntax_Syntax.Projector uu____13415 -> true
                      | FStar_Syntax_Syntax.Discriminator uu____13418 -> true
                      | FStar_Syntax_Syntax.Irreducible  -> true
                      | uu____13419 -> false)) in
            Prims.op_Negation uu____13412 in
          if will_encode_definition
          then ([], env)
          else
            (let fv =
               FStar_Syntax_Syntax.lid_as_fv lid
                 FStar_Syntax_Syntax.Delta_constant None in
             let uu____13425 = encode_top_level_val env fv t quals in
             match uu____13425 with
             | (decls,env1) ->
                 let tname = lid.FStar_Ident.str in
                 let tsym =
                   FStar_SMTEncoding_Util.mkFreeV
                     (tname, FStar_SMTEncoding_Term.Term_sort) in
                 let uu____13437 =
                   let uu____13439 =
                     primitive_type_axioms env1.tcenv lid tname tsym in
                   FStar_List.append decls uu____13439 in
                 (uu____13437, env1))
      | FStar_Syntax_Syntax.Sig_assume (l,f) ->
          let uu____13444 = encode_formula f env in
          (match uu____13444 with
           | (f1,decls) ->
               let g =
                 let uu____13453 =
                   let uu____13454 =
                     let uu____13458 =
                       let uu____13460 =
                         let uu____13461 = FStar_Syntax_Print.lid_to_string l in
                         FStar_Util.format1 "Assumption: %s" uu____13461 in
                       Some uu____13460 in
                     let uu____13462 =
                       varops.mk_unique
                         (Prims.strcat "assumption_" l.FStar_Ident.str) in
                     (f1, uu____13458, uu____13462) in
                   FStar_SMTEncoding_Util.mkAssume uu____13454 in
                 [uu____13453] in
               ((FStar_List.append decls g), env))
      | FStar_Syntax_Syntax.Sig_let (lbs,uu____13466,attrs) when
          (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
             (FStar_List.contains FStar_Syntax_Syntax.Irreducible))
            ||
            (FStar_All.pipe_right attrs
               (FStar_Util.for_some is_opaque_to_smt))
          ->
          let uu____13474 =
            FStar_Util.fold_map
              (fun env1  ->
                 fun lb  ->
                   let lid =
                     let uu____13481 =
                       let uu____13486 =
                         FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
                       uu____13486.FStar_Syntax_Syntax.fv_name in
                     uu____13481.FStar_Syntax_Syntax.v in
                   let uu____13490 =
                     let uu____13491 =
                       FStar_TypeChecker_Env.try_lookup_val_decl env1.tcenv
                         lid in
                     FStar_All.pipe_left FStar_Option.isNone uu____13491 in
                   if uu____13490
                   then
                     let val_decl =
                       let uu___152_13506 = se in
                       {
                         FStar_Syntax_Syntax.sigel =
                           (FStar_Syntax_Syntax.Sig_declare_typ
                              (lid, (lb.FStar_Syntax_Syntax.lbunivs),
                                (lb.FStar_Syntax_Syntax.lbtyp)));
                         FStar_Syntax_Syntax.sigrng =
                           (uu___152_13506.FStar_Syntax_Syntax.sigrng);
                         FStar_Syntax_Syntax.sigquals =
                           (FStar_Syntax_Syntax.Irreducible ::
                           (se.FStar_Syntax_Syntax.sigquals));
                         FStar_Syntax_Syntax.sigmeta =
                           (uu___152_13506.FStar_Syntax_Syntax.sigmeta)
                       } in
                     let uu____13510 = encode_sigelt' env1 val_decl in
                     match uu____13510 with | (decls,env2) -> (env2, decls)
                   else (env1, [])) env (snd lbs) in
          (match uu____13474 with
           | (env1,decls) -> ((FStar_List.flatten decls), env1))
      | FStar_Syntax_Syntax.Sig_let
          ((uu____13527,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inr b2t1;
                          FStar_Syntax_Syntax.lbunivs = uu____13529;
                          FStar_Syntax_Syntax.lbtyp = uu____13530;
                          FStar_Syntax_Syntax.lbeff = uu____13531;
                          FStar_Syntax_Syntax.lbdef = uu____13532;_}::[]),uu____13533,uu____13534)
          when FStar_Syntax_Syntax.fv_eq_lid b2t1 FStar_Syntax_Const.b2t_lid
          ->
          let uu____13548 =
            new_term_constant_and_tok_from_lid env
              (b2t1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          (match uu____13548 with
           | (tname,ttok,env1) ->
               let xx = ("x", FStar_SMTEncoding_Term.Term_sort) in
               let x = FStar_SMTEncoding_Util.mkFreeV xx in
               let b2t_x = FStar_SMTEncoding_Util.mkApp ("Prims.b2t", [x]) in
               let valid_b2t_x =
                 FStar_SMTEncoding_Util.mkApp ("Valid", [b2t_x]) in
               let decls =
                 let uu____13571 =
                   let uu____13573 =
                     let uu____13574 =
                       let uu____13578 =
                         let uu____13579 =
                           let uu____13585 =
                             let uu____13586 =
                               let uu____13589 =
                                 FStar_SMTEncoding_Util.mkApp
                                   ("BoxBool_proj_0", [x]) in
                               (valid_b2t_x, uu____13589) in
                             FStar_SMTEncoding_Util.mkEq uu____13586 in
                           ([[b2t_x]], [xx], uu____13585) in
                         FStar_SMTEncoding_Util.mkForall uu____13579 in
                       (uu____13578, (Some "b2t def"), "b2t_def") in
                     FStar_SMTEncoding_Util.mkAssume uu____13574 in
                   [uu____13573] in
                 (FStar_SMTEncoding_Term.DeclFun
                    (tname, [FStar_SMTEncoding_Term.Term_sort],
                      FStar_SMTEncoding_Term.Term_sort, None))
                   :: uu____13571 in
               (decls, env1))
      | FStar_Syntax_Syntax.Sig_let (uu____13606,uu____13607,uu____13608)
          when
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some
               (fun uu___119_13614  ->
                  match uu___119_13614 with
                  | FStar_Syntax_Syntax.Discriminator uu____13615 -> true
                  | uu____13616 -> false))
          -> ([], env)
      | FStar_Syntax_Syntax.Sig_let (uu____13618,lids,uu____13620) when
          (FStar_All.pipe_right lids
             (FStar_Util.for_some
                (fun l  ->
                   let uu____13627 =
                     let uu____13628 = FStar_List.hd l.FStar_Ident.ns in
                     uu____13628.FStar_Ident.idText in
                   uu____13627 = "Prims")))
            &&
            (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
               (FStar_Util.for_some
                  (fun uu___120_13630  ->
                     match uu___120_13630 with
                     | FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen 
                         -> true
                     | uu____13631 -> false)))
          -> ([], env)
      | FStar_Syntax_Syntax.Sig_let ((false ,lb::[]),uu____13634,uu____13635)
          when
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some
               (fun uu___121_13645  ->
                  match uu___121_13645 with
                  | FStar_Syntax_Syntax.Projector uu____13646 -> true
                  | uu____13649 -> false))
          ->
          let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
          let l = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          let uu____13656 = try_lookup_free_var env l in
          (match uu____13656 with
           | Some uu____13660 -> ([], env)
           | None  ->
               let se1 =
                 let uu___153_13663 = se in
                 {
                   FStar_Syntax_Syntax.sigel =
                     (FStar_Syntax_Syntax.Sig_declare_typ
                        (l, (lb.FStar_Syntax_Syntax.lbunivs),
                          (lb.FStar_Syntax_Syntax.lbtyp)));
                   FStar_Syntax_Syntax.sigrng = (FStar_Ident.range_of_lid l);
                   FStar_Syntax_Syntax.sigquals =
                     (uu___153_13663.FStar_Syntax_Syntax.sigquals);
                   FStar_Syntax_Syntax.sigmeta =
                     (uu___153_13663.FStar_Syntax_Syntax.sigmeta)
                 } in
               encode_sigelt env se1)
      | FStar_Syntax_Syntax.Sig_let
          ((is_rec,bindings),uu____13669,uu____13670) ->
          encode_top_level_let env (is_rec, bindings)
            se.FStar_Syntax_Syntax.sigquals
      | FStar_Syntax_Syntax.Sig_bundle (ses,uu____13682) ->
          let uu____13687 = encode_sigelts env ses in
          (match uu____13687 with
           | (g,env1) ->
               let uu____13697 =
                 FStar_All.pipe_right g
                   (FStar_List.partition
                      (fun uu___122_13707  ->
                         match uu___122_13707 with
                         | FStar_SMTEncoding_Term.Assume
                             {
                               FStar_SMTEncoding_Term.assumption_term =
                                 uu____13708;
                               FStar_SMTEncoding_Term.assumption_caption =
                                 Some "inversion axiom";
                               FStar_SMTEncoding_Term.assumption_name =
                                 uu____13709;
                               FStar_SMTEncoding_Term.assumption_fact_ids =
                                 uu____13710;_}
                             -> false
                         | uu____13712 -> true)) in
               (match uu____13697 with
                | (g',inversions) ->
                    let uu____13721 =
                      FStar_All.pipe_right g'
                        (FStar_List.partition
                           (fun uu___123_13731  ->
                              match uu___123_13731 with
                              | FStar_SMTEncoding_Term.DeclFun uu____13732 ->
                                  true
                              | uu____13738 -> false)) in
                    (match uu____13721 with
                     | (decls,rest) ->
                         ((FStar_List.append decls
                             (FStar_List.append rest inversions)), env1))))
      | FStar_Syntax_Syntax.Sig_inductive_typ
          (t,uu____13749,tps,k,uu____13752,datas) ->
          let quals = se.FStar_Syntax_Syntax.sigquals in
          let is_logical =
            FStar_All.pipe_right quals
              (FStar_Util.for_some
                 (fun uu___124_13762  ->
                    match uu___124_13762 with
                    | FStar_Syntax_Syntax.Logic  -> true
                    | FStar_Syntax_Syntax.Assumption  -> true
                    | uu____13763 -> false)) in
          let constructor_or_logic_type_decl c =
            if is_logical
            then
              let uu____13770 = c in
              match uu____13770 with
              | (name,args,uu____13774,uu____13775,uu____13776) ->
                  let uu____13779 =
                    let uu____13780 =
                      let uu____13786 =
                        FStar_All.pipe_right args
                          (FStar_List.map
                             (fun uu____13793  ->
                                match uu____13793 with
                                | (uu____13797,sort,uu____13799) -> sort)) in
                      (name, uu____13786, FStar_SMTEncoding_Term.Term_sort,
                        None) in
                    FStar_SMTEncoding_Term.DeclFun uu____13780 in
                  [uu____13779]
            else FStar_SMTEncoding_Term.constructor_to_decl c in
          let inversion_axioms tapp vars =
            let uu____13817 =
              FStar_All.pipe_right datas
                (FStar_Util.for_some
                   (fun l  ->
                      let uu____13820 =
                        FStar_TypeChecker_Env.try_lookup_lid env.tcenv l in
                      FStar_All.pipe_right uu____13820 FStar_Option.isNone)) in
            if uu____13817
            then []
            else
              (let uu____13837 =
                 fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort in
               match uu____13837 with
               | (xxsym,xx) ->
                   let uu____13843 =
                     FStar_All.pipe_right datas
                       (FStar_List.fold_left
                          (fun uu____13854  ->
                             fun l  ->
                               match uu____13854 with
                               | (out,decls) ->
                                   let uu____13866 =
                                     FStar_TypeChecker_Env.lookup_datacon
                                       env.tcenv l in
                                   (match uu____13866 with
                                    | (uu____13872,data_t) ->
                                        let uu____13874 =
                                          FStar_Syntax_Util.arrow_formals
                                            data_t in
                                        (match uu____13874 with
                                         | (args,res) ->
                                             let indices =
                                               let uu____13903 =
                                                 let uu____13904 =
                                                   FStar_Syntax_Subst.compress
                                                     res in
                                                 uu____13904.FStar_Syntax_Syntax.n in
                                               match uu____13903 with
                                               | FStar_Syntax_Syntax.Tm_app
                                                   (uu____13912,indices) ->
                                                   indices
                                               | uu____13928 -> [] in
                                             let env1 =
                                               FStar_All.pipe_right args
                                                 (FStar_List.fold_left
                                                    (fun env1  ->
                                                       fun uu____13940  ->
                                                         match uu____13940
                                                         with
                                                         | (x,uu____13944) ->
                                                             let uu____13945
                                                               =
                                                               let uu____13946
                                                                 =
                                                                 let uu____13950
                                                                   =
                                                                   mk_term_projector_name
                                                                    l x in
                                                                 (uu____13950,
                                                                   [xx]) in
                                                               FStar_SMTEncoding_Util.mkApp
                                                                 uu____13946 in
                                                             push_term_var
                                                               env1 x
                                                               uu____13945)
                                                    env) in
                                             let uu____13952 =
                                               encode_args indices env1 in
                                             (match uu____13952 with
                                              | (indices1,decls') ->
                                                  (if
                                                     (FStar_List.length
                                                        indices1)
                                                       <>
                                                       (FStar_List.length
                                                          vars)
                                                   then failwith "Impossible"
                                                   else ();
                                                   (let eqs =
                                                      let uu____13972 =
                                                        FStar_List.map2
                                                          (fun v1  ->
                                                             fun a  ->
                                                               let uu____13980
                                                                 =
                                                                 let uu____13983
                                                                   =
                                                                   FStar_SMTEncoding_Util.mkFreeV
                                                                    v1 in
                                                                 (uu____13983,
                                                                   a) in
                                                               FStar_SMTEncoding_Util.mkEq
                                                                 uu____13980)
                                                          vars indices1 in
                                                      FStar_All.pipe_right
                                                        uu____13972
                                                        FStar_SMTEncoding_Util.mk_and_l in
                                                    let uu____13985 =
                                                      let uu____13986 =
                                                        let uu____13989 =
                                                          let uu____13990 =
                                                            let uu____13993 =
                                                              mk_data_tester
                                                                env1 l xx in
                                                            (uu____13993,
                                                              eqs) in
                                                          FStar_SMTEncoding_Util.mkAnd
                                                            uu____13990 in
                                                        (out, uu____13989) in
                                                      FStar_SMTEncoding_Util.mkOr
                                                        uu____13986 in
                                                    (uu____13985,
                                                      (FStar_List.append
                                                         decls decls'))))))))
                          (FStar_SMTEncoding_Util.mkFalse, [])) in
                   (match uu____13843 with
                    | (data_ax,decls) ->
                        let uu____14001 =
                          fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort in
                        (match uu____14001 with
                         | (ffsym,ff) ->
                             let fuel_guarded_inversion =
                               let xx_has_type_sfuel =
                                 if
                                   (FStar_List.length datas) >
                                     (Prims.parse_int "1")
                                 then
                                   let uu____14012 =
                                     FStar_SMTEncoding_Util.mkApp
                                       ("SFuel", [ff]) in
                                   FStar_SMTEncoding_Term.mk_HasTypeFuel
                                     uu____14012 xx tapp
                                 else
                                   FStar_SMTEncoding_Term.mk_HasTypeFuel ff
                                     xx tapp in
                               let uu____14015 =
                                 let uu____14019 =
                                   let uu____14020 =
                                     let uu____14026 =
                                       add_fuel
                                         (ffsym,
                                           FStar_SMTEncoding_Term.Fuel_sort)
                                         ((xxsym,
                                            FStar_SMTEncoding_Term.Term_sort)
                                         :: vars) in
                                     let uu____14034 =
                                       FStar_SMTEncoding_Util.mkImp
                                         (xx_has_type_sfuel, data_ax) in
                                     ([[xx_has_type_sfuel]], uu____14026,
                                       uu____14034) in
                                   FStar_SMTEncoding_Util.mkForall
                                     uu____14020 in
                                 let uu____14042 =
                                   varops.mk_unique
                                     (Prims.strcat "fuel_guarded_inversion_"
                                        t.FStar_Ident.str) in
                                 (uu____14019, (Some "inversion axiom"),
                                   uu____14042) in
                               FStar_SMTEncoding_Util.mkAssume uu____14015 in
                             let pattern_guarded_inversion =
                               let uu____14046 =
                                 (contains_name env "Prims.inversion") &&
                                   ((FStar_List.length datas) >
                                      (Prims.parse_int "1")) in
                               if uu____14046
                               then
                                 let xx_has_type_fuel =
                                   FStar_SMTEncoding_Term.mk_HasTypeFuel ff
                                     xx tapp in
                                 let pattern_guard =
                                   FStar_SMTEncoding_Util.mkApp
                                     ("Prims.inversion", [tapp]) in
                                 let uu____14054 =
                                   let uu____14055 =
                                     let uu____14059 =
                                       let uu____14060 =
                                         let uu____14066 =
                                           add_fuel
                                             (ffsym,
                                               FStar_SMTEncoding_Term.Fuel_sort)
                                             ((xxsym,
                                                FStar_SMTEncoding_Term.Term_sort)
                                             :: vars) in
                                         let uu____14074 =
                                           FStar_SMTEncoding_Util.mkImp
                                             (xx_has_type_fuel, data_ax) in
                                         ([[xx_has_type_fuel; pattern_guard]],
                                           uu____14066, uu____14074) in
                                       FStar_SMTEncoding_Util.mkForall
                                         uu____14060 in
                                     let uu____14082 =
                                       varops.mk_unique
                                         (Prims.strcat
                                            "pattern_guarded_inversion_"
                                            t.FStar_Ident.str) in
                                     (uu____14059, (Some "inversion axiom"),
                                       uu____14082) in
                                   FStar_SMTEncoding_Util.mkAssume
                                     uu____14055 in
                                 [uu____14054]
                               else [] in
                             FStar_List.append decls
                               (FStar_List.append [fuel_guarded_inversion]
                                  pattern_guarded_inversion)))) in
          let uu____14085 =
            let uu____14093 =
              let uu____14094 = FStar_Syntax_Subst.compress k in
              uu____14094.FStar_Syntax_Syntax.n in
            match uu____14093 with
            | FStar_Syntax_Syntax.Tm_arrow (formals,kres) ->
                ((FStar_List.append tps formals),
                  (FStar_Syntax_Util.comp_result kres))
            | uu____14123 -> (tps, k) in
          (match uu____14085 with
           | (formals,res) ->
               let uu____14138 = FStar_Syntax_Subst.open_term formals res in
               (match uu____14138 with
                | (formals1,res1) ->
                    let uu____14145 = encode_binders None formals1 env in
                    (match uu____14145 with
                     | (vars,guards,env',binder_decls,uu____14160) ->
                         let uu____14167 =
                           new_term_constant_and_tok_from_lid env t in
                         (match uu____14167 with
                          | (tname,ttok,env1) ->
                              let ttok_tm =
                                FStar_SMTEncoding_Util.mkApp (ttok, []) in
                              let guard =
                                FStar_SMTEncoding_Util.mk_and_l guards in
                              let tapp =
                                let uu____14180 =
                                  let uu____14184 =
                                    FStar_List.map
                                      FStar_SMTEncoding_Util.mkFreeV vars in
                                  (tname, uu____14184) in
                                FStar_SMTEncoding_Util.mkApp uu____14180 in
                              let uu____14189 =
                                let tname_decl =
                                  let uu____14195 =
                                    let uu____14196 =
                                      FStar_All.pipe_right vars
                                        (FStar_List.map
                                           (fun uu____14211  ->
                                              match uu____14211 with
                                              | (n1,s) ->
                                                  ((Prims.strcat tname n1),
                                                    s, false))) in
                                    let uu____14219 = varops.next_id () in
                                    (tname, uu____14196,
                                      FStar_SMTEncoding_Term.Term_sort,
                                      uu____14219, false) in
                                  constructor_or_logic_type_decl uu____14195 in
                                let uu____14224 =
                                  match vars with
                                  | [] ->
                                      let uu____14231 =
                                        let uu____14232 =
                                          let uu____14234 =
                                            FStar_SMTEncoding_Util.mkApp
                                              (tname, []) in
                                          FStar_All.pipe_left
                                            (fun _0_38  -> Some _0_38)
                                            uu____14234 in
                                        push_free_var env1 t tname
                                          uu____14232 in
                                      ([], uu____14231)
                                  | uu____14238 ->
                                      let ttok_decl =
                                        FStar_SMTEncoding_Term.DeclFun
                                          (ttok, [],
                                            FStar_SMTEncoding_Term.Term_sort,
                                            (Some "token")) in
                                      let ttok_fresh =
                                        let uu____14244 = varops.next_id () in
                                        FStar_SMTEncoding_Term.fresh_token
                                          (ttok,
                                            FStar_SMTEncoding_Term.Term_sort)
                                          uu____14244 in
                                      let ttok_app = mk_Apply ttok_tm vars in
                                      let pats = [[ttok_app]; [tapp]] in
                                      let name_tok_corr =
                                        let uu____14253 =
                                          let uu____14257 =
                                            let uu____14258 =
                                              let uu____14266 =
                                                FStar_SMTEncoding_Util.mkEq
                                                  (ttok_app, tapp) in
                                              (pats, None, vars, uu____14266) in
                                            FStar_SMTEncoding_Util.mkForall'
                                              uu____14258 in
                                          (uu____14257,
                                            (Some "name-token correspondence"),
                                            (Prims.strcat
                                               "token_correspondence_" ttok)) in
                                        FStar_SMTEncoding_Util.mkAssume
                                          uu____14253 in
                                      ([ttok_decl; ttok_fresh; name_tok_corr],
                                        env1) in
                                match uu____14224 with
                                | (tok_decls,env2) ->
                                    ((FStar_List.append tname_decl tok_decls),
                                      env2) in
                              (match uu____14189 with
                               | (decls,env2) ->
                                   let kindingAx =
                                     let uu____14289 =
                                       encode_term_pred None res1 env' tapp in
                                     match uu____14289 with
                                     | (k1,decls1) ->
                                         let karr =
                                           if
                                             (FStar_List.length formals1) >
                                               (Prims.parse_int "0")
                                           then
                                             let uu____14303 =
                                               let uu____14304 =
                                                 let uu____14308 =
                                                   let uu____14309 =
                                                     FStar_SMTEncoding_Term.mk_PreType
                                                       ttok_tm in
                                                   FStar_SMTEncoding_Term.mk_tester
                                                     "Tm_arrow" uu____14309 in
                                                 (uu____14308,
                                                   (Some "kinding"),
                                                   (Prims.strcat
                                                      "pre_kinding_" ttok)) in
                                               FStar_SMTEncoding_Util.mkAssume
                                                 uu____14304 in
                                             [uu____14303]
                                           else [] in
                                         let uu____14312 =
                                           let uu____14314 =
                                             let uu____14316 =
                                               let uu____14317 =
                                                 let uu____14321 =
                                                   let uu____14322 =
                                                     let uu____14328 =
                                                       FStar_SMTEncoding_Util.mkImp
                                                         (guard, k1) in
                                                     ([[tapp]], vars,
                                                       uu____14328) in
                                                   FStar_SMTEncoding_Util.mkForall
                                                     uu____14322 in
                                                 (uu____14321, None,
                                                   (Prims.strcat "kinding_"
                                                      ttok)) in
                                               FStar_SMTEncoding_Util.mkAssume
                                                 uu____14317 in
                                             [uu____14316] in
                                           FStar_List.append karr uu____14314 in
                                         FStar_List.append decls1 uu____14312 in
                                   let aux =
                                     let uu____14337 =
                                       let uu____14339 =
                                         inversion_axioms tapp vars in
                                       let uu____14341 =
                                         let uu____14343 =
                                           pretype_axiom env2 tapp vars in
                                         [uu____14343] in
                                       FStar_List.append uu____14339
                                         uu____14341 in
                                     FStar_List.append kindingAx uu____14337 in
                                   let g =
                                     FStar_List.append decls
                                       (FStar_List.append binder_decls aux) in
                                   (g, env2))))))
      | FStar_Syntax_Syntax.Sig_datacon
          (d,uu____14348,uu____14349,uu____14350,uu____14351,uu____14352)
          when FStar_Ident.lid_equals d FStar_Syntax_Const.lexcons_lid ->
          ([], env)
      | FStar_Syntax_Syntax.Sig_datacon
          (d,uu____14357,t,uu____14359,n_tps,uu____14361) ->
          let quals = se.FStar_Syntax_Syntax.sigquals in
          let uu____14366 = new_term_constant_and_tok_from_lid env d in
          (match uu____14366 with
           | (ddconstrsym,ddtok,env1) ->
               let ddtok_tm = FStar_SMTEncoding_Util.mkApp (ddtok, []) in
               let uu____14377 = FStar_Syntax_Util.arrow_formals t in
               (match uu____14377 with
                | (formals,t_res) ->
                    let uu____14399 =
                      fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort in
                    (match uu____14399 with
                     | (fuel_var,fuel_tm) ->
                         let s_fuel_tm =
                           FStar_SMTEncoding_Util.mkApp ("SFuel", [fuel_tm]) in
                         let uu____14408 =
                           encode_binders (Some fuel_tm) formals env1 in
                         (match uu____14408 with
                          | (vars,guards,env',binder_decls,names1) ->
                              let fields =
                                FStar_All.pipe_right names1
                                  (FStar_List.mapi
                                     (fun n1  ->
                                        fun x  ->
                                          let projectible = true in
                                          let uu____14446 =
                                            mk_term_projector_name d x in
                                          (uu____14446,
                                            FStar_SMTEncoding_Term.Term_sort,
                                            projectible))) in
                              let datacons =
                                let uu____14448 =
                                  let uu____14458 = varops.next_id () in
                                  (ddconstrsym, fields,
                                    FStar_SMTEncoding_Term.Term_sort,
                                    uu____14458, true) in
                                FStar_All.pipe_right uu____14448
                                  FStar_SMTEncoding_Term.constructor_to_decl in
                              let app = mk_Apply ddtok_tm vars in
                              let guard =
                                FStar_SMTEncoding_Util.mk_and_l guards in
                              let xvars =
                                FStar_List.map FStar_SMTEncoding_Util.mkFreeV
                                  vars in
                              let dapp =
                                FStar_SMTEncoding_Util.mkApp
                                  (ddconstrsym, xvars) in
                              let uu____14480 =
                                encode_term_pred None t env1 ddtok_tm in
                              (match uu____14480 with
                               | (tok_typing,decls3) ->
                                   let tok_typing1 =
                                     match fields with
                                     | uu____14488::uu____14489 ->
                                         let ff =
                                           ("ty",
                                             FStar_SMTEncoding_Term.Term_sort) in
                                         let f =
                                           FStar_SMTEncoding_Util.mkFreeV ff in
                                         let vtok_app_l =
                                           mk_Apply ddtok_tm [ff] in
                                         let vtok_app_r =
                                           mk_Apply f
                                             [(ddtok,
                                                FStar_SMTEncoding_Term.Term_sort)] in
                                         let uu____14514 =
                                           let uu____14520 =
                                             FStar_SMTEncoding_Term.mk_NoHoist
                                               f tok_typing in
                                           ([[vtok_app_l]; [vtok_app_r]],
                                             [ff], uu____14520) in
                                         FStar_SMTEncoding_Util.mkForall
                                           uu____14514
                                     | uu____14533 -> tok_typing in
                                   let uu____14538 =
                                     encode_binders (Some fuel_tm) formals
                                       env1 in
                                   (match uu____14538 with
                                    | (vars',guards',env'',decls_formals,uu____14553)
                                        ->
                                        let uu____14560 =
                                          let xvars1 =
                                            FStar_List.map
                                              FStar_SMTEncoding_Util.mkFreeV
                                              vars' in
                                          let dapp1 =
                                            FStar_SMTEncoding_Util.mkApp
                                              (ddconstrsym, xvars1) in
                                          encode_term_pred (Some fuel_tm)
                                            t_res env'' dapp1 in
                                        (match uu____14560 with
                                         | (ty_pred',decls_pred) ->
                                             let guard' =
                                               FStar_SMTEncoding_Util.mk_and_l
                                                 guards' in
                                             let proxy_fresh =
                                               match formals with
                                               | [] -> []
                                               | uu____14579 ->
                                                   let uu____14583 =
                                                     let uu____14584 =
                                                       varops.next_id () in
                                                     FStar_SMTEncoding_Term.fresh_token
                                                       (ddtok,
                                                         FStar_SMTEncoding_Term.Term_sort)
                                                       uu____14584 in
                                                   [uu____14583] in
                                             let encode_elim uu____14591 =
                                               let uu____14592 =
                                                 FStar_Syntax_Util.head_and_args
                                                   t_res in
                                               match uu____14592 with
                                               | (head1,args) ->
                                                   let uu____14621 =
                                                     let uu____14622 =
                                                       FStar_Syntax_Subst.compress
                                                         head1 in
                                                     uu____14622.FStar_Syntax_Syntax.n in
                                                   (match uu____14621 with
                                                    | FStar_Syntax_Syntax.Tm_uinst
                                                        ({
                                                           FStar_Syntax_Syntax.n
                                                             =
                                                             FStar_Syntax_Syntax.Tm_fvar
                                                             fv;
                                                           FStar_Syntax_Syntax.tk
                                                             = uu____14629;
                                                           FStar_Syntax_Syntax.pos
                                                             = uu____14630;
                                                           FStar_Syntax_Syntax.vars
                                                             = uu____14631;_},uu____14632)
                                                        ->
                                                        let encoded_head =
                                                          lookup_free_var_name
                                                            env'
                                                            fv.FStar_Syntax_Syntax.fv_name in
                                                        let uu____14642 =
                                                          encode_args args
                                                            env' in
                                                        (match uu____14642
                                                         with
                                                         | (encoded_args,arg_decls)
                                                             ->
                                                             let guards_for_parameter
                                                               arg xv =
                                                               let fv1 =
                                                                 match 
                                                                   arg.FStar_SMTEncoding_Term.tm
                                                                 with
                                                                 | FStar_SMTEncoding_Term.FreeV
                                                                    fv1 ->
                                                                    fv1
                                                                 | uu____14668
                                                                    ->
                                                                    failwith
                                                                    "Impossible: parameter must be a variable" in
                                                               let guards1 =
                                                                 FStar_All.pipe_right
                                                                   guards
                                                                   (FStar_List.collect
                                                                    (fun g 
                                                                    ->
                                                                    let uu____14676
                                                                    =
                                                                    let uu____14677
                                                                    =
                                                                    FStar_SMTEncoding_Term.free_variables
                                                                    g in
                                                                    FStar_List.contains
                                                                    fv1
                                                                    uu____14677 in
                                                                    if
                                                                    uu____14676
                                                                    then
                                                                    let uu____14684
                                                                    =
                                                                    FStar_SMTEncoding_Term.subst
                                                                    g fv1 xv in
                                                                    [uu____14684]
                                                                    else [])) in
                                                               FStar_SMTEncoding_Util.mk_and_l
                                                                 guards1 in
                                                             let uu____14686
                                                               =
                                                               FStar_List.fold_left
                                                                 (fun
                                                                    uu____14699
                                                                     ->
                                                                    fun arg 
                                                                    ->
                                                                    match uu____14699
                                                                    with
                                                                    | 
                                                                    (env2,arg_vars,eqns_or_guards,i)
                                                                    ->
                                                                    let uu____14721
                                                                    =
                                                                    let uu____14725
                                                                    =
                                                                    FStar_Syntax_Syntax.new_bv
                                                                    None
                                                                    FStar_Syntax_Syntax.tun in
                                                                    gen_term_var
                                                                    env2
                                                                    uu____14725 in
                                                                    (match uu____14721
                                                                    with
                                                                    | 
                                                                    (uu____14732,xv,env3)
                                                                    ->
                                                                    let eqns
                                                                    =
                                                                    if
                                                                    i < n_tps
                                                                    then
                                                                    let uu____14738
                                                                    =
                                                                    guards_for_parameter
                                                                    arg xv in
                                                                    uu____14738
                                                                    ::
                                                                    eqns_or_guards
                                                                    else
                                                                    (let uu____14740
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (arg, xv) in
                                                                    uu____14740
                                                                    ::
                                                                    eqns_or_guards) in
                                                                    (env3,
                                                                    (xv ::
                                                                    arg_vars),
                                                                    eqns,
                                                                    (i +
                                                                    (Prims.parse_int
                                                                    "1")))))
                                                                 (env', [],
                                                                   [],
                                                                   (Prims.parse_int
                                                                    "0"))
                                                                 encoded_args in
                                                             (match uu____14686
                                                              with
                                                              | (uu____14748,arg_vars,elim_eqns_or_guards,uu____14751)
                                                                  ->
                                                                  let arg_vars1
                                                                    =
                                                                    FStar_List.rev
                                                                    arg_vars in
                                                                  let ty =
                                                                    FStar_SMTEncoding_Util.mkApp
                                                                    (encoded_head,
                                                                    arg_vars1) in
                                                                  let xvars1
                                                                    =
                                                                    FStar_List.map
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    vars in
                                                                  let dapp1 =
                                                                    FStar_SMTEncoding_Util.mkApp
                                                                    (ddconstrsym,
                                                                    xvars1) in
                                                                  let ty_pred
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_HasTypeWithFuel
                                                                    (Some
                                                                    s_fuel_tm)
                                                                    dapp1 ty in
                                                                  let arg_binders
                                                                    =
                                                                    FStar_List.map
                                                                    FStar_SMTEncoding_Term.fv_of_term
                                                                    arg_vars1 in
                                                                  let typing_inversion
                                                                    =
                                                                    let uu____14770
                                                                    =
                                                                    let uu____14774
                                                                    =
                                                                    let uu____14775
                                                                    =
                                                                    let uu____14781
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders) in
                                                                    let uu____14787
                                                                    =
                                                                    let uu____14788
                                                                    =
                                                                    let uu____14791
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    (FStar_List.append
                                                                    elim_eqns_or_guards
                                                                    guards) in
                                                                    (ty_pred,
                                                                    uu____14791) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____14788 in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____14781,
                                                                    uu____14787) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____14775 in
                                                                    (uu____14774,
                                                                    (Some
                                                                    "data constructor typing elim"),
                                                                    (Prims.strcat
                                                                    "data_elim_"
                                                                    ddconstrsym)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____14770 in
                                                                  let subterm_ordering
                                                                    =
                                                                    if
                                                                    FStar_Ident.lid_equals
                                                                    d
                                                                    FStar_Syntax_Const.lextop_lid
                                                                    then
                                                                    let x =
                                                                    let uu____14804
                                                                    =
                                                                    varops.fresh
                                                                    "x" in
                                                                    (uu____14804,
                                                                    FStar_SMTEncoding_Term.Term_sort) in
                                                                    let xtm =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    x in
                                                                    let uu____14806
                                                                    =
                                                                    let uu____14810
                                                                    =
                                                                    let uu____14811
                                                                    =
                                                                    let uu____14817
                                                                    =
                                                                    let uu____14820
                                                                    =
                                                                    let uu____14822
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp1 in
                                                                    [uu____14822] in
                                                                    [uu____14820] in
                                                                    let uu____14825
                                                                    =
                                                                    let uu____14826
                                                                    =
                                                                    let uu____14829
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_tester
                                                                    "LexCons"
                                                                    xtm in
                                                                    let uu____14830
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp1 in
                                                                    (uu____14829,
                                                                    uu____14830) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____14826 in
                                                                    (uu____14817,
                                                                    [x],
                                                                    uu____14825) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____14811 in
                                                                    let uu____14840
                                                                    =
                                                                    varops.mk_unique
                                                                    "lextop" in
                                                                    (uu____14810,
                                                                    (Some
                                                                    "lextop is top"),
                                                                    uu____14840) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____14806
                                                                    else
                                                                    (let prec
                                                                    =
                                                                    let uu____14845
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    vars
                                                                    (FStar_List.mapi
                                                                    (fun i 
                                                                    ->
                                                                    fun v1 
                                                                    ->
                                                                    if
                                                                    i < n_tps
                                                                    then []
                                                                    else
                                                                    (let uu____14860
                                                                    =
                                                                    let uu____14861
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    v1 in
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    uu____14861
                                                                    dapp1 in
                                                                    [uu____14860]))) in
                                                                    FStar_All.pipe_right
                                                                    uu____14845
                                                                    FStar_List.flatten in
                                                                    let uu____14865
                                                                    =
                                                                    let uu____14869
                                                                    =
                                                                    let uu____14870
                                                                    =
                                                                    let uu____14876
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders) in
                                                                    let uu____14882
                                                                    =
                                                                    let uu____14883
                                                                    =
                                                                    let uu____14886
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    prec in
                                                                    (ty_pred,
                                                                    uu____14886) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____14883 in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____14876,
                                                                    uu____14882) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____14870 in
                                                                    (uu____14869,
                                                                    (Some
                                                                    "subterm ordering"),
                                                                    (Prims.strcat
                                                                    "subterm_ordering_"
                                                                    ddconstrsym)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____14865) in
                                                                  (arg_decls,
                                                                    [typing_inversion;
                                                                    subterm_ordering])))
                                                    | FStar_Syntax_Syntax.Tm_fvar
                                                        fv ->
                                                        let encoded_head =
                                                          lookup_free_var_name
                                                            env'
                                                            fv.FStar_Syntax_Syntax.fv_name in
                                                        let uu____14902 =
                                                          encode_args args
                                                            env' in
                                                        (match uu____14902
                                                         with
                                                         | (encoded_args,arg_decls)
                                                             ->
                                                             let guards_for_parameter
                                                               arg xv =
                                                               let fv1 =
                                                                 match 
                                                                   arg.FStar_SMTEncoding_Term.tm
                                                                 with
                                                                 | FStar_SMTEncoding_Term.FreeV
                                                                    fv1 ->
                                                                    fv1
                                                                 | uu____14928
                                                                    ->
                                                                    failwith
                                                                    "Impossible: parameter must be a variable" in
                                                               let guards1 =
                                                                 FStar_All.pipe_right
                                                                   guards
                                                                   (FStar_List.collect
                                                                    (fun g 
                                                                    ->
                                                                    let uu____14936
                                                                    =
                                                                    let uu____14937
                                                                    =
                                                                    FStar_SMTEncoding_Term.free_variables
                                                                    g in
                                                                    FStar_List.contains
                                                                    fv1
                                                                    uu____14937 in
                                                                    if
                                                                    uu____14936
                                                                    then
                                                                    let uu____14944
                                                                    =
                                                                    FStar_SMTEncoding_Term.subst
                                                                    g fv1 xv in
                                                                    [uu____14944]
                                                                    else [])) in
                                                               FStar_SMTEncoding_Util.mk_and_l
                                                                 guards1 in
                                                             let uu____14946
                                                               =
                                                               FStar_List.fold_left
                                                                 (fun
                                                                    uu____14959
                                                                     ->
                                                                    fun arg 
                                                                    ->
                                                                    match uu____14959
                                                                    with
                                                                    | 
                                                                    (env2,arg_vars,eqns_or_guards,i)
                                                                    ->
                                                                    let uu____14981
                                                                    =
                                                                    let uu____14985
                                                                    =
                                                                    FStar_Syntax_Syntax.new_bv
                                                                    None
                                                                    FStar_Syntax_Syntax.tun in
                                                                    gen_term_var
                                                                    env2
                                                                    uu____14985 in
                                                                    (match uu____14981
                                                                    with
                                                                    | 
                                                                    (uu____14992,xv,env3)
                                                                    ->
                                                                    let eqns
                                                                    =
                                                                    if
                                                                    i < n_tps
                                                                    then
                                                                    let uu____14998
                                                                    =
                                                                    guards_for_parameter
                                                                    arg xv in
                                                                    uu____14998
                                                                    ::
                                                                    eqns_or_guards
                                                                    else
                                                                    (let uu____15000
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (arg, xv) in
                                                                    uu____15000
                                                                    ::
                                                                    eqns_or_guards) in
                                                                    (env3,
                                                                    (xv ::
                                                                    arg_vars),
                                                                    eqns,
                                                                    (i +
                                                                    (Prims.parse_int
                                                                    "1")))))
                                                                 (env', [],
                                                                   [],
                                                                   (Prims.parse_int
                                                                    "0"))
                                                                 encoded_args in
                                                             (match uu____14946
                                                              with
                                                              | (uu____15008,arg_vars,elim_eqns_or_guards,uu____15011)
                                                                  ->
                                                                  let arg_vars1
                                                                    =
                                                                    FStar_List.rev
                                                                    arg_vars in
                                                                  let ty =
                                                                    FStar_SMTEncoding_Util.mkApp
                                                                    (encoded_head,
                                                                    arg_vars1) in
                                                                  let xvars1
                                                                    =
                                                                    FStar_List.map
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    vars in
                                                                  let dapp1 =
                                                                    FStar_SMTEncoding_Util.mkApp
                                                                    (ddconstrsym,
                                                                    xvars1) in
                                                                  let ty_pred
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_HasTypeWithFuel
                                                                    (Some
                                                                    s_fuel_tm)
                                                                    dapp1 ty in
                                                                  let arg_binders
                                                                    =
                                                                    FStar_List.map
                                                                    FStar_SMTEncoding_Term.fv_of_term
                                                                    arg_vars1 in
                                                                  let typing_inversion
                                                                    =
                                                                    let uu____15030
                                                                    =
                                                                    let uu____15034
                                                                    =
                                                                    let uu____15035
                                                                    =
                                                                    let uu____15041
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders) in
                                                                    let uu____15047
                                                                    =
                                                                    let uu____15048
                                                                    =
                                                                    let uu____15051
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    (FStar_List.append
                                                                    elim_eqns_or_guards
                                                                    guards) in
                                                                    (ty_pred,
                                                                    uu____15051) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____15048 in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____15041,
                                                                    uu____15047) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____15035 in
                                                                    (uu____15034,
                                                                    (Some
                                                                    "data constructor typing elim"),
                                                                    (Prims.strcat
                                                                    "data_elim_"
                                                                    ddconstrsym)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____15030 in
                                                                  let subterm_ordering
                                                                    =
                                                                    if
                                                                    FStar_Ident.lid_equals
                                                                    d
                                                                    FStar_Syntax_Const.lextop_lid
                                                                    then
                                                                    let x =
                                                                    let uu____15064
                                                                    =
                                                                    varops.fresh
                                                                    "x" in
                                                                    (uu____15064,
                                                                    FStar_SMTEncoding_Term.Term_sort) in
                                                                    let xtm =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    x in
                                                                    let uu____15066
                                                                    =
                                                                    let uu____15070
                                                                    =
                                                                    let uu____15071
                                                                    =
                                                                    let uu____15077
                                                                    =
                                                                    let uu____15080
                                                                    =
                                                                    let uu____15082
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp1 in
                                                                    [uu____15082] in
                                                                    [uu____15080] in
                                                                    let uu____15085
                                                                    =
                                                                    let uu____15086
                                                                    =
                                                                    let uu____15089
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_tester
                                                                    "LexCons"
                                                                    xtm in
                                                                    let uu____15090
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp1 in
                                                                    (uu____15089,
                                                                    uu____15090) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____15086 in
                                                                    (uu____15077,
                                                                    [x],
                                                                    uu____15085) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____15071 in
                                                                    let uu____15100
                                                                    =
                                                                    varops.mk_unique
                                                                    "lextop" in
                                                                    (uu____15070,
                                                                    (Some
                                                                    "lextop is top"),
                                                                    uu____15100) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____15066
                                                                    else
                                                                    (let prec
                                                                    =
                                                                    let uu____15105
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    vars
                                                                    (FStar_List.mapi
                                                                    (fun i 
                                                                    ->
                                                                    fun v1 
                                                                    ->
                                                                    if
                                                                    i < n_tps
                                                                    then []
                                                                    else
                                                                    (let uu____15120
                                                                    =
                                                                    let uu____15121
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    v1 in
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    uu____15121
                                                                    dapp1 in
                                                                    [uu____15120]))) in
                                                                    FStar_All.pipe_right
                                                                    uu____15105
                                                                    FStar_List.flatten in
                                                                    let uu____15125
                                                                    =
                                                                    let uu____15129
                                                                    =
                                                                    let uu____15130
                                                                    =
                                                                    let uu____15136
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders) in
                                                                    let uu____15142
                                                                    =
                                                                    let uu____15143
                                                                    =
                                                                    let uu____15146
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    prec in
                                                                    (ty_pred,
                                                                    uu____15146) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____15143 in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____15136,
                                                                    uu____15142) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____15130 in
                                                                    (uu____15129,
                                                                    (Some
                                                                    "subterm ordering"),
                                                                    (Prims.strcat
                                                                    "subterm_ordering_"
                                                                    ddconstrsym)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____15125) in
                                                                  (arg_decls,
                                                                    [typing_inversion;
                                                                    subterm_ordering])))
                                                    | uu____15156 ->
                                                        ((let uu____15158 =
                                                            let uu____15159 =
                                                              FStar_Syntax_Print.lid_to_string
                                                                d in
                                                            let uu____15160 =
                                                              FStar_Syntax_Print.term_to_string
                                                                head1 in
                                                            FStar_Util.format2
                                                              "Constructor %s builds an unexpected type %s\n"
                                                              uu____15159
                                                              uu____15160 in
                                                          FStar_Errors.warn
                                                            se.FStar_Syntax_Syntax.sigrng
                                                            uu____15158);
                                                         ([], []))) in
                                             let uu____15163 = encode_elim () in
                                             (match uu____15163 with
                                              | (decls2,elim) ->
                                                  let g =
                                                    let uu____15175 =
                                                      let uu____15177 =
                                                        let uu____15179 =
                                                          let uu____15181 =
                                                            let uu____15183 =
                                                              let uu____15184
                                                                =
                                                                let uu____15190
                                                                  =
                                                                  let uu____15192
                                                                    =
                                                                    let uu____15193
                                                                    =
                                                                    FStar_Syntax_Print.lid_to_string
                                                                    d in
                                                                    FStar_Util.format1
                                                                    "data constructor proxy: %s"
                                                                    uu____15193 in
                                                                  Some
                                                                    uu____15192 in
                                                                (ddtok, [],
                                                                  FStar_SMTEncoding_Term.Term_sort,
                                                                  uu____15190) in
                                                              FStar_SMTEncoding_Term.DeclFun
                                                                uu____15184 in
                                                            [uu____15183] in
                                                          let uu____15196 =
                                                            let uu____15198 =
                                                              let uu____15200
                                                                =
                                                                let uu____15202
                                                                  =
                                                                  let uu____15204
                                                                    =
                                                                    let uu____15206
                                                                    =
                                                                    let uu____15208
                                                                    =
                                                                    let uu____15209
                                                                    =
                                                                    let uu____15213
                                                                    =
                                                                    let uu____15214
                                                                    =
                                                                    let uu____15220
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (app,
                                                                    dapp) in
                                                                    ([[app]],
                                                                    vars,
                                                                    uu____15220) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____15214 in
                                                                    (uu____15213,
                                                                    (Some
                                                                    "equality for proxy"),
                                                                    (Prims.strcat
                                                                    "equality_tok_"
                                                                    ddtok)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____15209 in
                                                                    let uu____15227
                                                                    =
                                                                    let uu____15229
                                                                    =
                                                                    let uu____15230
                                                                    =
                                                                    let uu____15234
                                                                    =
                                                                    let uu____15235
                                                                    =
                                                                    let uu____15241
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    vars' in
                                                                    let uu____15247
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    (guard',
                                                                    ty_pred') in
                                                                    ([
                                                                    [ty_pred']],
                                                                    uu____15241,
                                                                    uu____15247) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____15235 in
                                                                    (uu____15234,
                                                                    (Some
                                                                    "data constructor typing intro"),
                                                                    (Prims.strcat
                                                                    "data_typing_intro_"
                                                                    ddtok)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____15230 in
                                                                    [uu____15229] in
                                                                    uu____15208
                                                                    ::
                                                                    uu____15227 in
                                                                    (FStar_SMTEncoding_Util.mkAssume
                                                                    (tok_typing1,
                                                                    (Some
                                                                    "typing for data constructor proxy"),
                                                                    (Prims.strcat
                                                                    "typing_tok_"
                                                                    ddtok)))
                                                                    ::
                                                                    uu____15206 in
                                                                  FStar_List.append
                                                                    uu____15204
                                                                    elim in
                                                                FStar_List.append
                                                                  decls_pred
                                                                  uu____15202 in
                                                              FStar_List.append
                                                                decls_formals
                                                                uu____15200 in
                                                            FStar_List.append
                                                              proxy_fresh
                                                              uu____15198 in
                                                          FStar_List.append
                                                            uu____15181
                                                            uu____15196 in
                                                        FStar_List.append
                                                          decls3 uu____15179 in
                                                      FStar_List.append
                                                        decls2 uu____15177 in
                                                    FStar_List.append
                                                      binder_decls
                                                      uu____15175 in
                                                  ((FStar_List.append
                                                      datacons g), env1)))))))))
and encode_sigelts:
  env_t ->
    FStar_Syntax_Syntax.sigelt Prims.list ->
      (FStar_SMTEncoding_Term.decl Prims.list* env_t)
  =
  fun env  ->
    fun ses  ->
      FStar_All.pipe_right ses
        (FStar_List.fold_left
           (fun uu____15268  ->
              fun se  ->
                match uu____15268 with
                | (g,env1) ->
                    let uu____15280 = encode_sigelt env1 se in
                    (match uu____15280 with
                     | (g',env2) -> ((FStar_List.append g g'), env2)))
           ([], env))
let encode_env_bindings:
  env_t ->
    FStar_TypeChecker_Env.binding Prims.list ->
      (FStar_SMTEncoding_Term.decls_t* env_t)
  =
  fun env  ->
    fun bindings  ->
      let encode_binding b uu____15316 =
        match uu____15316 with
        | (i,decls,env1) ->
            (match b with
             | FStar_TypeChecker_Env.Binding_univ uu____15334 ->
                 ((i + (Prims.parse_int "1")), [], env1)
             | FStar_TypeChecker_Env.Binding_var x ->
                 let t1 =
                   FStar_TypeChecker_Normalize.normalize
                     [FStar_TypeChecker_Normalize.Beta;
                     FStar_TypeChecker_Normalize.Eager_unfolding;
                     FStar_TypeChecker_Normalize.Simplify;
                     FStar_TypeChecker_Normalize.EraseUniverses] env1.tcenv
                     x.FStar_Syntax_Syntax.sort in
                 ((let uu____15339 =
                     FStar_All.pipe_left
                       (FStar_TypeChecker_Env.debug env1.tcenv)
                       (FStar_Options.Other "SMTEncoding") in
                   if uu____15339
                   then
                     let uu____15340 = FStar_Syntax_Print.bv_to_string x in
                     let uu____15341 =
                       FStar_Syntax_Print.term_to_string
                         x.FStar_Syntax_Syntax.sort in
                     let uu____15342 = FStar_Syntax_Print.term_to_string t1 in
                     FStar_Util.print3 "Normalized %s : %s to %s\n"
                       uu____15340 uu____15341 uu____15342
                   else ());
                  (let uu____15344 = encode_term t1 env1 in
                   match uu____15344 with
                   | (t,decls') ->
                       let t_hash = FStar_SMTEncoding_Term.hash_of_term t in
                       let uu____15354 =
                         let uu____15358 =
                           let uu____15359 =
                             let uu____15360 =
                               FStar_Util.digest_of_string t_hash in
                             Prims.strcat uu____15360
                               (Prims.strcat "_" (Prims.string_of_int i)) in
                           Prims.strcat "x_" uu____15359 in
                         new_term_constant_from_string env1 x uu____15358 in
                       (match uu____15354 with
                        | (xxsym,xx,env') ->
                            let t2 =
                              FStar_SMTEncoding_Term.mk_HasTypeWithFuel None
                                xx t in
                            let caption =
                              let uu____15371 = FStar_Options.log_queries () in
                              if uu____15371
                              then
                                let uu____15373 =
                                  let uu____15374 =
                                    FStar_Syntax_Print.bv_to_string x in
                                  let uu____15375 =
                                    FStar_Syntax_Print.term_to_string
                                      x.FStar_Syntax_Syntax.sort in
                                  let uu____15376 =
                                    FStar_Syntax_Print.term_to_string t1 in
                                  FStar_Util.format3 "%s : %s (%s)"
                                    uu____15374 uu____15375 uu____15376 in
                                Some uu____15373
                              else None in
                            let ax =
                              let a_name = Prims.strcat "binder_" xxsym in
                              FStar_SMTEncoding_Util.mkAssume
                                (t2, (Some a_name), a_name) in
                            let g =
                              FStar_List.append
                                [FStar_SMTEncoding_Term.DeclFun
                                   (xxsym, [],
                                     FStar_SMTEncoding_Term.Term_sort,
                                     caption)]
                                (FStar_List.append decls' [ax]) in
                            ((i + (Prims.parse_int "1")),
                              (FStar_List.append decls g), env'))))
             | FStar_TypeChecker_Env.Binding_lid (x,(uu____15387,t)) ->
                 let t_norm = whnf env1 t in
                 let fv =
                   FStar_Syntax_Syntax.lid_as_fv x
                     FStar_Syntax_Syntax.Delta_constant None in
                 let uu____15396 = encode_free_var env1 fv t t_norm [] in
                 (match uu____15396 with
                  | (g,env') ->
                      ((i + (Prims.parse_int "1")),
                        (FStar_List.append decls g), env'))
             | FStar_TypeChecker_Env.Binding_sig_inst
                 (uu____15409,se,uu____15411) ->
                 let uu____15414 = encode_sigelt env1 se in
                 (match uu____15414 with
                  | (g,env') ->
                      ((i + (Prims.parse_int "1")),
                        (FStar_List.append decls g), env'))
             | FStar_TypeChecker_Env.Binding_sig (uu____15424,se) ->
                 let uu____15428 = encode_sigelt env1 se in
                 (match uu____15428 with
                  | (g,env') ->
                      ((i + (Prims.parse_int "1")),
                        (FStar_List.append decls g), env'))) in
      let uu____15438 =
        FStar_List.fold_right encode_binding bindings
          ((Prims.parse_int "0"), [], env) in
      match uu____15438 with | (uu____15450,decls,env1) -> (decls, env1)
let encode_labels labs =
  let prefix1 =
    FStar_All.pipe_right labs
      (FStar_List.map
         (fun uu____15495  ->
            match uu____15495 with
            | (l,uu____15502,uu____15503) ->
                FStar_SMTEncoding_Term.DeclFun
                  ((fst l), [], FStar_SMTEncoding_Term.Bool_sort, None))) in
  let suffix =
    FStar_All.pipe_right labs
      (FStar_List.collect
         (fun uu____15524  ->
            match uu____15524 with
            | (l,uu____15532,uu____15533) ->
                let uu____15538 =
                  FStar_All.pipe_left
                    (fun _0_39  -> FStar_SMTEncoding_Term.Echo _0_39) (
                    fst l) in
                let uu____15539 =
                  let uu____15541 =
                    let uu____15542 = FStar_SMTEncoding_Util.mkFreeV l in
                    FStar_SMTEncoding_Term.Eval uu____15542 in
                  [uu____15541] in
                uu____15538 :: uu____15539)) in
  (prefix1, suffix)
let last_env: env_t Prims.list FStar_ST.ref = FStar_Util.mk_ref []
let init_env: FStar_TypeChecker_Env.env -> Prims.unit =
  fun tcenv  ->
    let uu____15553 =
      let uu____15555 =
        let uu____15556 = FStar_Util.smap_create (Prims.parse_int "100") in
        let uu____15558 =
          let uu____15559 = FStar_TypeChecker_Env.current_module tcenv in
          FStar_All.pipe_right uu____15559 FStar_Ident.string_of_lid in
        {
          bindings = [];
          depth = (Prims.parse_int "0");
          tcenv;
          warn = true;
          cache = uu____15556;
          nolabels = false;
          use_zfuel_name = false;
          encode_non_total_function_typ = true;
          current_module_name = uu____15558
        } in
      [uu____15555] in
    FStar_ST.write last_env uu____15553
let get_env: FStar_Ident.lident -> FStar_TypeChecker_Env.env -> env_t =
  fun cmn  ->
    fun tcenv  ->
      let uu____15569 = FStar_ST.read last_env in
      match uu____15569 with
      | [] -> failwith "No env; call init first!"
      | e::uu____15575 ->
          let uu___154_15577 = e in
          let uu____15578 = FStar_Ident.string_of_lid cmn in
          {
            bindings = (uu___154_15577.bindings);
            depth = (uu___154_15577.depth);
            tcenv;
            warn = (uu___154_15577.warn);
            cache = (uu___154_15577.cache);
            nolabels = (uu___154_15577.nolabels);
            use_zfuel_name = (uu___154_15577.use_zfuel_name);
            encode_non_total_function_typ =
              (uu___154_15577.encode_non_total_function_typ);
            current_module_name = uu____15578
          }
let set_env: env_t -> Prims.unit =
  fun env  ->
    let uu____15582 = FStar_ST.read last_env in
    match uu____15582 with
    | [] -> failwith "Empty env stack"
    | uu____15587::tl1 -> FStar_ST.write last_env (env :: tl1)
let push_env: Prims.unit -> Prims.unit =
  fun uu____15595  ->
    let uu____15596 = FStar_ST.read last_env in
    match uu____15596 with
    | [] -> failwith "Empty env stack"
    | hd1::tl1 ->
        let refs = FStar_Util.smap_copy hd1.cache in
        let top =
          let uu___155_15607 = hd1 in
          {
            bindings = (uu___155_15607.bindings);
            depth = (uu___155_15607.depth);
            tcenv = (uu___155_15607.tcenv);
            warn = (uu___155_15607.warn);
            cache = refs;
            nolabels = (uu___155_15607.nolabels);
            use_zfuel_name = (uu___155_15607.use_zfuel_name);
            encode_non_total_function_typ =
              (uu___155_15607.encode_non_total_function_typ);
            current_module_name = (uu___155_15607.current_module_name)
          } in
        FStar_ST.write last_env (top :: hd1 :: tl1)
let pop_env: Prims.unit -> Prims.unit =
  fun uu____15613  ->
    let uu____15614 = FStar_ST.read last_env in
    match uu____15614 with
    | [] -> failwith "Popping an empty stack"
    | uu____15619::tl1 -> FStar_ST.write last_env tl1
let mark_env: Prims.unit -> Prims.unit = fun uu____15627  -> push_env ()
let reset_mark_env: Prims.unit -> Prims.unit = fun uu____15630  -> pop_env ()
let commit_mark_env: Prims.unit -> Prims.unit =
  fun uu____15633  ->
    let uu____15634 = FStar_ST.read last_env in
    match uu____15634 with
    | hd1::uu____15640::tl1 -> FStar_ST.write last_env (hd1 :: tl1)
    | uu____15646 -> failwith "Impossible"
let init: FStar_TypeChecker_Env.env -> Prims.unit =
  fun tcenv  ->
    init_env tcenv;
    FStar_SMTEncoding_Z3.init ();
    FStar_SMTEncoding_Z3.giveZ3 [FStar_SMTEncoding_Term.DefPrelude]
let push: Prims.string -> Prims.unit =
  fun msg  -> push_env (); varops.push (); FStar_SMTEncoding_Z3.push msg
let pop: Prims.string -> Prims.unit =
  fun msg  -> pop_env (); varops.pop (); FStar_SMTEncoding_Z3.pop msg
let mark: Prims.string -> Prims.unit =
  fun msg  -> mark_env (); varops.mark (); FStar_SMTEncoding_Z3.mark msg
let reset_mark: Prims.string -> Prims.unit =
  fun msg  ->
    reset_mark_env ();
    varops.reset_mark ();
    FStar_SMTEncoding_Z3.reset_mark msg
let commit_mark: Prims.string -> Prims.unit =
  fun msg  ->
    commit_mark_env ();
    varops.commit_mark ();
    FStar_SMTEncoding_Z3.commit_mark msg
let open_fact_db_tags: env_t -> FStar_SMTEncoding_Term.fact_db_id Prims.list
  = fun env  -> []
let place_decl_in_fact_dbs:
  env_t ->
    FStar_SMTEncoding_Term.fact_db_id Prims.list ->
      FStar_SMTEncoding_Term.decl -> FStar_SMTEncoding_Term.decl
  =
  fun env  ->
    fun fact_db_ids  ->
      fun d  ->
        match (fact_db_ids, d) with
        | (uu____15695::uu____15696,FStar_SMTEncoding_Term.Assume a) ->
            FStar_SMTEncoding_Term.Assume
              (let uu___156_15700 = a in
               {
                 FStar_SMTEncoding_Term.assumption_term =
                   (uu___156_15700.FStar_SMTEncoding_Term.assumption_term);
                 FStar_SMTEncoding_Term.assumption_caption =
                   (uu___156_15700.FStar_SMTEncoding_Term.assumption_caption);
                 FStar_SMTEncoding_Term.assumption_name =
                   (uu___156_15700.FStar_SMTEncoding_Term.assumption_name);
                 FStar_SMTEncoding_Term.assumption_fact_ids = fact_db_ids
               })
        | uu____15701 -> d
let fact_dbs_for_lid:
  env_t -> FStar_Ident.lid -> FStar_SMTEncoding_Term.fact_db_id Prims.list =
  fun env  ->
    fun lid  ->
      let uu____15712 =
        let uu____15714 =
          let uu____15715 = FStar_Ident.lid_of_ids lid.FStar_Ident.ns in
          FStar_SMTEncoding_Term.Namespace uu____15715 in
        let uu____15716 = open_fact_db_tags env in uu____15714 :: uu____15716 in
      (FStar_SMTEncoding_Term.Name lid) :: uu____15712
let encode_top_level_facts:
  env_t ->
    FStar_Syntax_Syntax.sigelt ->
      (FStar_SMTEncoding_Term.decl Prims.list* env_t)
  =
  fun env  ->
    fun se  ->
      let fact_db_ids =
        FStar_All.pipe_right (FStar_Syntax_Util.lids_of_sigelt se)
          (FStar_List.collect (fact_dbs_for_lid env)) in
      let uu____15731 = encode_sigelt env se in
      match uu____15731 with
      | (g,env1) ->
          let g1 =
            FStar_All.pipe_right g
              (FStar_List.map (place_decl_in_fact_dbs env1 fact_db_ids)) in
          (g1, env1)
let encode_sig:
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.sigelt -> Prims.unit =
  fun tcenv  ->
    fun se  ->
      let caption decls =
        let uu____15756 = FStar_Options.log_queries () in
        if uu____15756
        then
          let uu____15758 =
            let uu____15759 =
              let uu____15760 =
                let uu____15761 =
                  FStar_All.pipe_right (FStar_Syntax_Util.lids_of_sigelt se)
                    (FStar_List.map FStar_Syntax_Print.lid_to_string) in
                FStar_All.pipe_right uu____15761 (FStar_String.concat ", ") in
              Prims.strcat "encoding sigelt " uu____15760 in
            FStar_SMTEncoding_Term.Caption uu____15759 in
          uu____15758 :: decls
        else decls in
      let env =
        let uu____15768 = FStar_TypeChecker_Env.current_module tcenv in
        get_env uu____15768 tcenv in
      let uu____15769 = encode_top_level_facts env se in
      match uu____15769 with
      | (decls,env1) ->
          (set_env env1;
           (let uu____15778 = caption decls in
            FStar_SMTEncoding_Z3.giveZ3 uu____15778))
let encode_modul:
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.modul -> Prims.unit =
  fun tcenv  ->
    fun modul  ->
      let name =
        FStar_Util.format2 "%s %s"
          (if modul.FStar_Syntax_Syntax.is_interface
           then "interface"
           else "module") (modul.FStar_Syntax_Syntax.name).FStar_Ident.str in
      (let uu____15789 = FStar_TypeChecker_Env.debug tcenv FStar_Options.Low in
       if uu____15789
       then
         let uu____15790 =
           FStar_All.pipe_right
             (FStar_List.length modul.FStar_Syntax_Syntax.exports)
             Prims.string_of_int in
         FStar_Util.print2
           "+++++++++++Encoding externals for %s ... %s exports\n" name
           uu____15790
       else ());
      (let env = get_env modul.FStar_Syntax_Syntax.name tcenv in
       let encode_signature env1 ses =
         FStar_All.pipe_right ses
           (FStar_List.fold_left
              (fun uu____15811  ->
                 fun se  ->
                   match uu____15811 with
                   | (g,env2) ->
                       let uu____15823 = encode_top_level_facts env2 se in
                       (match uu____15823 with
                        | (g',env3) -> ((FStar_List.append g g'), env3)))
              ([], env1)) in
       let uu____15836 =
         encode_signature
           (let uu___157_15840 = env in
            {
              bindings = (uu___157_15840.bindings);
              depth = (uu___157_15840.depth);
              tcenv = (uu___157_15840.tcenv);
              warn = false;
              cache = (uu___157_15840.cache);
              nolabels = (uu___157_15840.nolabels);
              use_zfuel_name = (uu___157_15840.use_zfuel_name);
              encode_non_total_function_typ =
                (uu___157_15840.encode_non_total_function_typ);
              current_module_name = (uu___157_15840.current_module_name)
            }) modul.FStar_Syntax_Syntax.exports in
       match uu____15836 with
       | (decls,env1) ->
           let caption decls1 =
             let uu____15852 = FStar_Options.log_queries () in
             if uu____15852
             then
               let msg = Prims.strcat "Externals for " name in
               FStar_List.append ((FStar_SMTEncoding_Term.Caption msg) ::
                 decls1)
                 [FStar_SMTEncoding_Term.Caption (Prims.strcat "End " msg)]
             else decls1 in
           (set_env
              (let uu___158_15857 = env1 in
               {
                 bindings = (uu___158_15857.bindings);
                 depth = (uu___158_15857.depth);
                 tcenv = (uu___158_15857.tcenv);
                 warn = true;
                 cache = (uu___158_15857.cache);
                 nolabels = (uu___158_15857.nolabels);
                 use_zfuel_name = (uu___158_15857.use_zfuel_name);
                 encode_non_total_function_typ =
                   (uu___158_15857.encode_non_total_function_typ);
                 current_module_name = (uu___158_15857.current_module_name)
               });
            (let uu____15859 =
               FStar_TypeChecker_Env.debug tcenv FStar_Options.Low in
             if uu____15859
             then FStar_Util.print1 "Done encoding externals for %s\n" name
             else ());
            (let decls1 = caption decls in FStar_SMTEncoding_Z3.giveZ3 decls1)))
let encode_query:
  (Prims.unit -> Prims.string) option ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term ->
        (FStar_SMTEncoding_Term.decl Prims.list*
          FStar_SMTEncoding_ErrorReporting.label Prims.list*
          FStar_SMTEncoding_Term.decl* FStar_SMTEncoding_Term.decl
          Prims.list)
  =
  fun use_env_msg  ->
    fun tcenv  ->
      fun q  ->
        (let uu____15894 =
           let uu____15895 = FStar_TypeChecker_Env.current_module tcenv in
           uu____15895.FStar_Ident.str in
         FStar_SMTEncoding_Z3.query_logging.FStar_SMTEncoding_Z3.set_module_name
           uu____15894);
        (let env =
           let uu____15897 = FStar_TypeChecker_Env.current_module tcenv in
           get_env uu____15897 tcenv in
         let bindings =
           FStar_TypeChecker_Env.fold_env tcenv
             (fun bs  -> fun b  -> b :: bs) [] in
         let uu____15904 =
           let rec aux bindings1 =
             match bindings1 with
             | (FStar_TypeChecker_Env.Binding_var x)::rest ->
                 let uu____15925 = aux rest in
                 (match uu____15925 with
                  | (out,rest1) ->
                      let t =
                        let uu____15943 =
                          FStar_Syntax_Util.destruct_typ_as_formula
                            x.FStar_Syntax_Syntax.sort in
                        match uu____15943 with
                        | Some uu____15947 ->
                            let uu____15948 =
                              FStar_Syntax_Syntax.new_bv None
                                FStar_TypeChecker_Common.t_unit in
                            FStar_Syntax_Util.refine uu____15948
                              x.FStar_Syntax_Syntax.sort
                        | uu____15949 -> x.FStar_Syntax_Syntax.sort in
                      let t1 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Normalize.Eager_unfolding;
                          FStar_TypeChecker_Normalize.Beta;
                          FStar_TypeChecker_Normalize.Simplify;
                          FStar_TypeChecker_Normalize.EraseUniverses]
                          env.tcenv t in
                      let uu____15952 =
                        let uu____15954 =
                          FStar_Syntax_Syntax.mk_binder
                            (let uu___159_15955 = x in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___159_15955.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___159_15955.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = t1
                             }) in
                        uu____15954 :: out in
                      (uu____15952, rest1))
             | uu____15958 -> ([], bindings1) in
           let uu____15962 = aux bindings in
           match uu____15962 with
           | (closing,bindings1) ->
               let uu____15976 =
                 FStar_Syntax_Util.close_forall_no_univs
                   (FStar_List.rev closing) q in
               (uu____15976, bindings1) in
         match uu____15904 with
         | (q1,bindings1) ->
             let uu____15989 =
               let uu____15992 =
                 FStar_List.filter
                   (fun uu___125_15994  ->
                      match uu___125_15994 with
                      | FStar_TypeChecker_Env.Binding_sig uu____15995 ->
                          false
                      | uu____15999 -> true) bindings1 in
               encode_env_bindings env uu____15992 in
             (match uu____15989 with
              | (env_decls,env1) ->
                  ((let uu____16010 =
                      ((FStar_TypeChecker_Env.debug tcenv FStar_Options.Low)
                         ||
                         (FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug tcenv)
                            (FStar_Options.Other "SMTEncoding")))
                        ||
                        (FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug tcenv)
                           (FStar_Options.Other "SMTQuery")) in
                    if uu____16010
                    then
                      let uu____16011 = FStar_Syntax_Print.term_to_string q1 in
                      FStar_Util.print1 "Encoding query formula: %s\n"
                        uu____16011
                    else ());
                   (let uu____16013 = encode_formula q1 env1 in
                    match uu____16013 with
                    | (phi,qdecls) ->
                        let uu____16025 =
                          let uu____16028 =
                            FStar_TypeChecker_Env.get_range tcenv in
                          FStar_SMTEncoding_ErrorReporting.label_goals
                            use_env_msg uu____16028 phi in
                        (match uu____16025 with
                         | (labels,phi1) ->
                             let uu____16038 = encode_labels labels in
                             (match uu____16038 with
                              | (label_prefix,label_suffix) ->
                                  let query_prelude =
                                    FStar_List.append env_decls
                                      (FStar_List.append label_prefix qdecls) in
                                  let qry =
                                    let uu____16059 =
                                      let uu____16063 =
                                        FStar_SMTEncoding_Util.mkNot phi1 in
                                      let uu____16064 =
                                        varops.mk_unique "@query" in
                                      (uu____16063, (Some "query"),
                                        uu____16064) in
                                    FStar_SMTEncoding_Util.mkAssume
                                      uu____16059 in
                                  let suffix =
                                    FStar_List.append label_suffix
                                      [FStar_SMTEncoding_Term.Echo "Done!"] in
                                  (query_prelude, labels, qry, suffix)))))))
let is_trivial:
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.typ -> Prims.bool =
  fun tcenv  ->
    fun q  ->
      let env =
        let uu____16077 = FStar_TypeChecker_Env.current_module tcenv in
        get_env uu____16077 tcenv in
      FStar_SMTEncoding_Z3.push "query";
      (let uu____16079 = encode_formula q env in
       match uu____16079 with
       | (f,uu____16083) ->
           (FStar_SMTEncoding_Z3.pop "query";
            (match f.FStar_SMTEncoding_Term.tm with
             | FStar_SMTEncoding_Term.App
                 (FStar_SMTEncoding_Term.TrueOp ,uu____16085) -> true
             | uu____16088 -> false)))