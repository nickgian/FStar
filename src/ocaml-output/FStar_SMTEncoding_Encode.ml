open Prims
let add_fuel x tl1 =
  let uu____16 = FStar_Options.unthrottle_inductives () in
  if uu____16 then tl1 else x :: tl1
let withenv c uu____39 = match uu____39 with | (a,b) -> (a, b, c)
let vargs args =
  FStar_List.filter
    (fun uu___104_74  ->
       match uu___104_74 with
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
        let uu___129_140 = a in
        let uu____141 =
          FStar_Syntax_Util.unmangle_field_name a.FStar_Syntax_Syntax.ppname in
        {
          FStar_Syntax_Syntax.ppname = uu____141;
          FStar_Syntax_Syntax.index =
            (uu___129_140.FStar_Syntax_Syntax.index);
          FStar_Syntax_Syntax.sort = (uu___129_140.FStar_Syntax_Syntax.sort)
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
                         mk_term_projector_name lid (Prims.fst b)))
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
  let new_scope uu____410 =
    let uu____411 = FStar_Util.smap_create (Prims.parse_int "100") in
    let uu____413 = FStar_Util.smap_create (Prims.parse_int "100") in
    (uu____411, uu____413) in
  let scopes =
    let uu____424 = let uu____430 = new_scope () in [uu____430] in
    FStar_Util.mk_ref uu____424 in
  let mk_unique y =
    let y1 = escape y in
    let y2 =
      let uu____455 =
        let uu____457 = FStar_ST.read scopes in
        FStar_Util.find_map uu____457
          (fun uu____474  ->
             match uu____474 with
             | (names1,uu____481) -> FStar_Util.smap_try_find names1 y1) in
      match uu____455 with
      | None  -> y1
      | Some uu____486 ->
          (FStar_Util.incr ctr;
           (let uu____491 =
              let uu____492 =
                let uu____493 = FStar_ST.read ctr in
                Prims.string_of_int uu____493 in
              Prims.strcat "__" uu____492 in
            Prims.strcat y1 uu____491)) in
    let top_scope =
      let uu____498 =
        let uu____503 = FStar_ST.read scopes in FStar_List.hd uu____503 in
      FStar_All.pipe_left Prims.fst uu____498 in
    FStar_Util.smap_add top_scope y2 true; y2 in
  let new_var pp rn =
    FStar_All.pipe_left mk_unique
      (Prims.strcat pp.FStar_Ident.idText
         (Prims.strcat "__" (Prims.string_of_int rn))) in
  let new_fvar lid = mk_unique lid.FStar_Ident.str in
  let next_id1 uu____542 = FStar_Util.incr ctr; FStar_ST.read ctr in
  let fresh1 pfx =
    let uu____553 =
      let uu____554 = next_id1 () in
      FStar_All.pipe_left Prims.string_of_int uu____554 in
    FStar_Util.format2 "%s_%s" pfx uu____553 in
  let string_const s =
    let uu____559 =
      let uu____561 = FStar_ST.read scopes in
      FStar_Util.find_map uu____561
        (fun uu____578  ->
           match uu____578 with
           | (uu____584,strings) -> FStar_Util.smap_try_find strings s) in
    match uu____559 with
    | Some f -> f
    | None  ->
        let id = next_id1 () in
        let f =
          let uu____593 = FStar_SMTEncoding_Util.mk_String_const id in
          FStar_All.pipe_left FStar_SMTEncoding_Term.boxString uu____593 in
        let top_scope =
          let uu____596 =
            let uu____601 = FStar_ST.read scopes in FStar_List.hd uu____601 in
          FStar_All.pipe_left Prims.snd uu____596 in
        (FStar_Util.smap_add top_scope s f; f) in
  let push1 uu____629 =
    let uu____630 =
      let uu____636 = new_scope () in
      let uu____641 = FStar_ST.read scopes in uu____636 :: uu____641 in
    FStar_ST.write scopes uu____630 in
  let pop1 uu____668 =
    let uu____669 =
      let uu____675 = FStar_ST.read scopes in FStar_List.tl uu____675 in
    FStar_ST.write scopes uu____669 in
  let mark1 uu____702 = push1 () in
  let reset_mark1 uu____706 = pop1 () in
  let commit_mark1 uu____710 =
    let uu____711 = FStar_ST.read scopes in
    match uu____711 with
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
    | uu____771 -> failwith "Impossible" in
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
    let uu___130_780 = x in
    let uu____781 =
      FStar_Syntax_Util.unmangle_field_name x.FStar_Syntax_Syntax.ppname in
    {
      FStar_Syntax_Syntax.ppname = uu____781;
      FStar_Syntax_Syntax.index = (uu___130_780.FStar_Syntax_Syntax.index);
      FStar_Syntax_Syntax.sort = (uu___130_780.FStar_Syntax_Syntax.sort)
    }
type binding =
  | Binding_var of (FStar_Syntax_Syntax.bv* FStar_SMTEncoding_Term.term)
  | Binding_fvar of (FStar_Ident.lident* Prims.string*
  FStar_SMTEncoding_Term.term Prims.option* FStar_SMTEncoding_Term.term
  Prims.option)
let uu___is_Binding_var: binding -> Prims.bool =
  fun projectee  ->
    match projectee with | Binding_var _0 -> true | uu____802 -> false
let __proj__Binding_var__item___0:
  binding -> (FStar_Syntax_Syntax.bv* FStar_SMTEncoding_Term.term) =
  fun projectee  -> match projectee with | Binding_var _0 -> _0
let uu___is_Binding_fvar: binding -> Prims.bool =
  fun projectee  ->
    match projectee with | Binding_fvar _0 -> true | uu____826 -> false
let __proj__Binding_fvar__item___0:
  binding ->
    (FStar_Ident.lident* Prims.string* FStar_SMTEncoding_Term.term
      Prims.option* FStar_SMTEncoding_Term.term Prims.option)
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
         (fun uu___105_1001  ->
            match uu___105_1001 with
            | FStar_SMTEncoding_Term.Assume a ->
                [a.FStar_SMTEncoding_Term.assumption_name]
            | uu____1004 -> [])) in
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
    let uu____1012 =
      FStar_All.pipe_right e.bindings
        (FStar_List.map
           (fun uu___106_1016  ->
              match uu___106_1016 with
              | Binding_var (x,uu____1018) ->
                  FStar_Syntax_Print.bv_to_string x
              | Binding_fvar (l,uu____1020,uu____1021,uu____1022) ->
                  FStar_Syntax_Print.lid_to_string l)) in
    FStar_All.pipe_right uu____1012 (FStar_String.concat ", ")
let lookup_binding env f = FStar_Util.find_map env.bindings f
let caption_t: env_t -> FStar_Syntax_Syntax.term -> Prims.string Prims.option
  =
  fun env  ->
    fun t  ->
      let uu____1055 =
        FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low in
      if uu____1055
      then
        let uu____1057 = FStar_Syntax_Print.term_to_string t in
        Some uu____1057
      else None
let fresh_fvar:
  Prims.string ->
    FStar_SMTEncoding_Term.sort ->
      (Prims.string* FStar_SMTEncoding_Term.term)
  =
  fun x  ->
    fun s  ->
      let xsym = varops.fresh x in
      let uu____1068 = FStar_SMTEncoding_Util.mkFreeV (xsym, s) in
      (xsym, uu____1068)
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
        (let uu___131_1080 = env in
         {
           bindings = ((Binding_var (x, y)) :: (env.bindings));
           depth = (env.depth + (Prims.parse_int "1"));
           tcenv = (uu___131_1080.tcenv);
           warn = (uu___131_1080.warn);
           cache = (uu___131_1080.cache);
           nolabels = (uu___131_1080.nolabels);
           use_zfuel_name = (uu___131_1080.use_zfuel_name);
           encode_non_total_function_typ =
             (uu___131_1080.encode_non_total_function_typ);
           current_module_name = (uu___131_1080.current_module_name)
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
        (let uu___132_1093 = env in
         {
           bindings = ((Binding_var (x, y)) :: (env.bindings));
           depth = (uu___132_1093.depth);
           tcenv = (uu___132_1093.tcenv);
           warn = (uu___132_1093.warn);
           cache = (uu___132_1093.cache);
           nolabels = (uu___132_1093.nolabels);
           use_zfuel_name = (uu___132_1093.use_zfuel_name);
           encode_non_total_function_typ =
             (uu___132_1093.encode_non_total_function_typ);
           current_module_name = (uu___132_1093.current_module_name)
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
          (let uu___133_1109 = env in
           {
             bindings = ((Binding_var (x, y)) :: (env.bindings));
             depth = (uu___133_1109.depth);
             tcenv = (uu___133_1109.tcenv);
             warn = (uu___133_1109.warn);
             cache = (uu___133_1109.cache);
             nolabels = (uu___133_1109.nolabels);
             use_zfuel_name = (uu___133_1109.use_zfuel_name);
             encode_non_total_function_typ =
               (uu___133_1109.encode_non_total_function_typ);
             current_module_name = (uu___133_1109.current_module_name)
           }))
let push_term_var:
  env_t -> FStar_Syntax_Syntax.bv -> FStar_SMTEncoding_Term.term -> env_t =
  fun env  ->
    fun x  ->
      fun t  ->
        let uu___134_1119 = env in
        {
          bindings = ((Binding_var (x, t)) :: (env.bindings));
          depth = (uu___134_1119.depth);
          tcenv = (uu___134_1119.tcenv);
          warn = (uu___134_1119.warn);
          cache = (uu___134_1119.cache);
          nolabels = (uu___134_1119.nolabels);
          use_zfuel_name = (uu___134_1119.use_zfuel_name);
          encode_non_total_function_typ =
            (uu___134_1119.encode_non_total_function_typ);
          current_module_name = (uu___134_1119.current_module_name)
        }
let lookup_term_var:
  env_t -> FStar_Syntax_Syntax.bv -> FStar_SMTEncoding_Term.term =
  fun env  ->
    fun a  ->
      let aux a' =
        lookup_binding env
          (fun uu___107_1135  ->
             match uu___107_1135 with
             | Binding_var (b,t) when FStar_Syntax_Syntax.bv_eq b a' ->
                 Some (b, t)
             | uu____1143 -> None) in
      let uu____1146 = aux a in
      match uu____1146 with
      | None  ->
          let a2 = unmangle a in
          let uu____1153 = aux a2 in
          (match uu____1153 with
           | None  ->
               let uu____1159 =
                 let uu____1160 = FStar_Syntax_Print.bv_to_string a2 in
                 let uu____1161 = print_env env in
                 FStar_Util.format2
                   "Bound term variable not found (after unmangling): %s in environment: %s"
                   uu____1160 uu____1161 in
               failwith uu____1159
           | Some (b,t) -> t)
      | Some (b,t) -> t
let new_term_constant_and_tok_from_lid:
  env_t -> FStar_Ident.lident -> (Prims.string* Prims.string* env_t) =
  fun env  ->
    fun x  ->
      let fname = varops.new_fvar x in
      let ftok = Prims.strcat fname "@tok" in
      let uu____1181 =
        let uu___135_1182 = env in
        let uu____1183 =
          let uu____1185 =
            let uu____1186 =
              let uu____1193 =
                let uu____1195 = FStar_SMTEncoding_Util.mkApp (ftok, []) in
                FStar_All.pipe_left (fun _0_29  -> Some _0_29) uu____1195 in
              (x, fname, uu____1193, None) in
            Binding_fvar uu____1186 in
          uu____1185 :: (env.bindings) in
        {
          bindings = uu____1183;
          depth = (uu___135_1182.depth);
          tcenv = (uu___135_1182.tcenv);
          warn = (uu___135_1182.warn);
          cache = (uu___135_1182.cache);
          nolabels = (uu___135_1182.nolabels);
          use_zfuel_name = (uu___135_1182.use_zfuel_name);
          encode_non_total_function_typ =
            (uu___135_1182.encode_non_total_function_typ);
          current_module_name = (uu___135_1182.current_module_name)
        } in
      (fname, ftok, uu____1181)
let try_lookup_lid:
  env_t ->
    FStar_Ident.lident ->
      (Prims.string* FStar_SMTEncoding_Term.term Prims.option*
        FStar_SMTEncoding_Term.term Prims.option) Prims.option
  =
  fun env  ->
    fun a  ->
      lookup_binding env
        (fun uu___108_1217  ->
           match uu___108_1217 with
           | Binding_fvar (b,t1,t2,t3) when FStar_Ident.lid_equals b a ->
               Some (t1, t2, t3)
           | uu____1239 -> None)
let contains_name: env_t -> Prims.string -> Prims.bool =
  fun env  ->
    fun s  ->
      let uu____1251 =
        lookup_binding env
          (fun uu___109_1253  ->
             match uu___109_1253 with
             | Binding_fvar (b,t1,t2,t3) when b.FStar_Ident.str = s ->
                 Some ()
             | uu____1263 -> None) in
      FStar_All.pipe_right uu____1251 FStar_Option.isSome
let lookup_lid:
  env_t ->
    FStar_Ident.lident ->
      (Prims.string* FStar_SMTEncoding_Term.term Prims.option*
        FStar_SMTEncoding_Term.term Prims.option)
  =
  fun env  ->
    fun a  ->
      let uu____1276 = try_lookup_lid env a in
      match uu____1276 with
      | None  ->
          let uu____1293 =
            let uu____1294 = FStar_Syntax_Print.lid_to_string a in
            FStar_Util.format1 "Name not found: %s" uu____1294 in
          failwith uu____1293
      | Some s -> s
let push_free_var:
  env_t ->
    FStar_Ident.lident ->
      Prims.string -> FStar_SMTEncoding_Term.term Prims.option -> env_t
  =
  fun env  ->
    fun x  ->
      fun fname  ->
        fun ftok  ->
          let uu___136_1325 = env in
          {
            bindings = ((Binding_fvar (x, fname, ftok, None)) ::
              (env.bindings));
            depth = (uu___136_1325.depth);
            tcenv = (uu___136_1325.tcenv);
            warn = (uu___136_1325.warn);
            cache = (uu___136_1325.cache);
            nolabels = (uu___136_1325.nolabels);
            use_zfuel_name = (uu___136_1325.use_zfuel_name);
            encode_non_total_function_typ =
              (uu___136_1325.encode_non_total_function_typ);
            current_module_name = (uu___136_1325.current_module_name)
          }
let push_zfuel_name: env_t -> FStar_Ident.lident -> Prims.string -> env_t =
  fun env  ->
    fun x  ->
      fun f  ->
        let uu____1337 = lookup_lid env x in
        match uu____1337 with
        | (t1,t2,uu____1345) ->
            let t3 =
              let uu____1351 =
                let uu____1355 =
                  let uu____1357 = FStar_SMTEncoding_Util.mkApp ("ZFuel", []) in
                  [uu____1357] in
                (f, uu____1355) in
              FStar_SMTEncoding_Util.mkApp uu____1351 in
            let uu___137_1360 = env in
            {
              bindings = ((Binding_fvar (x, t1, t2, (Some t3))) ::
                (env.bindings));
              depth = (uu___137_1360.depth);
              tcenv = (uu___137_1360.tcenv);
              warn = (uu___137_1360.warn);
              cache = (uu___137_1360.cache);
              nolabels = (uu___137_1360.nolabels);
              use_zfuel_name = (uu___137_1360.use_zfuel_name);
              encode_non_total_function_typ =
                (uu___137_1360.encode_non_total_function_typ);
              current_module_name = (uu___137_1360.current_module_name)
            }
let try_lookup_free_var:
  env_t -> FStar_Ident.lident -> FStar_SMTEncoding_Term.term Prims.option =
  fun env  ->
    fun l  ->
      let uu____1370 = try_lookup_lid env l in
      match uu____1370 with
      | None  -> None
      | Some (name,sym,zf_opt) ->
          (match zf_opt with
           | Some f when env.use_zfuel_name -> Some f
           | uu____1397 ->
               (match sym with
                | Some t ->
                    (match t.FStar_SMTEncoding_Term.tm with
                     | FStar_SMTEncoding_Term.App (uu____1402,fuel::[]) ->
                         let uu____1405 =
                           let uu____1406 =
                             let uu____1407 =
                               FStar_SMTEncoding_Term.fv_of_term fuel in
                             FStar_All.pipe_right uu____1407 Prims.fst in
                           FStar_Util.starts_with uu____1406 "fuel" in
                         if uu____1405
                         then
                           let uu____1409 =
                             let uu____1410 =
                               FStar_SMTEncoding_Util.mkFreeV
                                 (name, FStar_SMTEncoding_Term.Term_sort) in
                             FStar_SMTEncoding_Term.mk_ApplyTF uu____1410
                               fuel in
                           FStar_All.pipe_left (fun _0_30  -> Some _0_30)
                             uu____1409
                         else Some t
                     | uu____1413 -> Some t)
                | uu____1414 -> None))
let lookup_free_var env a =
  let uu____1432 = try_lookup_free_var env a.FStar_Syntax_Syntax.v in
  match uu____1432 with
  | Some t -> t
  | None  ->
      let uu____1435 =
        let uu____1436 =
          FStar_Syntax_Print.lid_to_string a.FStar_Syntax_Syntax.v in
        FStar_Util.format1 "Name not found: %s" uu____1436 in
      failwith uu____1435
let lookup_free_var_name env a =
  let uu____1453 = lookup_lid env a.FStar_Syntax_Syntax.v in
  match uu____1453 with | (x,uu____1460,uu____1461) -> x
let lookup_free_var_sym env a =
  let uu____1485 = lookup_lid env a.FStar_Syntax_Syntax.v in
  match uu____1485 with
  | (name,sym,zf_opt) ->
      (match zf_opt with
       | Some
           { FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.App (g,zf);
             FStar_SMTEncoding_Term.freevars = uu____1506;
             FStar_SMTEncoding_Term.rng = uu____1507;_}
           when env.use_zfuel_name -> (g, zf)
       | uu____1515 ->
           (match sym with
            | None  -> ((FStar_SMTEncoding_Term.Var name), [])
            | Some sym1 ->
                (match sym1.FStar_SMTEncoding_Term.tm with
                 | FStar_SMTEncoding_Term.App (g,fuel::[]) -> (g, [fuel])
                 | uu____1529 -> ((FStar_SMTEncoding_Term.Var name), []))))
let tok_of_name:
  env_t -> Prims.string -> FStar_SMTEncoding_Term.term Prims.option =
  fun env  ->
    fun nm  ->
      FStar_Util.find_map env.bindings
        (fun uu___110_1538  ->
           match uu___110_1538 with
           | Binding_fvar (uu____1540,nm',tok,uu____1543) when nm = nm' ->
               tok
           | uu____1548 -> None)
let mkForall_fuel' n1 uu____1565 =
  match uu____1565 with
  | (pats,vars,body) ->
      let fallback uu____1581 =
        FStar_SMTEncoding_Util.mkForall (pats, vars, body) in
      let uu____1584 = FStar_Options.unthrottle_inductives () in
      if uu____1584
      then fallback ()
      else
        (let uu____1586 = fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort in
         match uu____1586 with
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
                       | uu____1605 -> p)) in
             let pats1 = FStar_List.map add_fuel1 pats in
             let body1 =
               match body.FStar_SMTEncoding_Term.tm with
               | FStar_SMTEncoding_Term.App
                   (FStar_SMTEncoding_Term.Imp ,guard::body'::[]) ->
                   let guard1 =
                     match guard.FStar_SMTEncoding_Term.tm with
                     | FStar_SMTEncoding_Term.App
                         (FStar_SMTEncoding_Term.And ,guards) ->
                         let uu____1619 = add_fuel1 guards in
                         FStar_SMTEncoding_Util.mk_and_l uu____1619
                     | uu____1621 ->
                         let uu____1622 = add_fuel1 [guard] in
                         FStar_All.pipe_right uu____1622 FStar_List.hd in
                   FStar_SMTEncoding_Util.mkImp (guard1, body')
               | uu____1625 -> body in
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
      | FStar_Syntax_Syntax.Tm_arrow _
        |FStar_Syntax_Syntax.Tm_refine _
         |FStar_Syntax_Syntax.Tm_bvar _
          |FStar_Syntax_Syntax.Tm_uvar _
           |FStar_Syntax_Syntax.Tm_abs _|FStar_Syntax_Syntax.Tm_constant _
          -> true
      | FStar_Syntax_Syntax.Tm_fvar fv|FStar_Syntax_Syntax.Tm_app
        ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
           FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _;
           FStar_Syntax_Syntax.vars = _;_},_)
          ->
          let uu____1669 =
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Eager_unfolding_only] env.tcenv
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          FStar_All.pipe_right uu____1669 FStar_Option.isNone
      | uu____1682 -> false
let head_redex: env_t -> FStar_Syntax_Syntax.term -> Prims.bool =
  fun env  ->
    fun t  ->
      let uu____1689 =
        let uu____1690 = FStar_Syntax_Util.un_uinst t in
        uu____1690.FStar_Syntax_Syntax.n in
      match uu____1689 with
      | FStar_Syntax_Syntax.Tm_abs
          (uu____1693,uu____1694,Some (FStar_Util.Inr (l,flags))) ->
          ((FStar_Ident.lid_equals l FStar_Syntax_Const.effect_Tot_lid) ||
             (FStar_Ident.lid_equals l FStar_Syntax_Const.effect_GTot_lid))
            ||
            (FStar_List.existsb
               (fun uu___111_1723  ->
                  match uu___111_1723 with
                  | FStar_Syntax_Syntax.TOTAL  -> true
                  | uu____1724 -> false) flags)
      | FStar_Syntax_Syntax.Tm_abs
          (uu____1725,uu____1726,Some (FStar_Util.Inl lc)) ->
          FStar_Syntax_Util.is_tot_or_gtot_lcomp lc
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____1753 =
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Eager_unfolding_only] env.tcenv
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          FStar_All.pipe_right uu____1753 FStar_Option.isSome
      | uu____1766 -> false
let whnf: env_t -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term =
  fun env  ->
    fun t  ->
      let uu____1773 = head_normal env t in
      if uu____1773
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
    let uu____1784 =
      let uu____1785 = FStar_Syntax_Syntax.null_binder t in [uu____1785] in
    let uu____1786 =
      FStar_Syntax_Syntax.fvar FStar_Syntax_Const.true_lid
        FStar_Syntax_Syntax.Delta_constant None in
    FStar_Syntax_Util.abs uu____1784 uu____1786 None
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
                match Prims.snd var with
                | FStar_SMTEncoding_Term.Fuel_sort  ->
                    let uu____1813 = FStar_SMTEncoding_Util.mkFreeV var in
                    FStar_SMTEncoding_Term.mk_ApplyTF out uu____1813
                | s ->
                    let uu____1816 = FStar_SMTEncoding_Util.mkFreeV var in
                    FStar_SMTEncoding_Util.mk_ApplyTT out uu____1816) e)
let mk_Apply_args:
  FStar_SMTEncoding_Term.term ->
    FStar_SMTEncoding_Term.term Prims.list -> FStar_SMTEncoding_Term.term
  =
  fun e  ->
    fun args  ->
      FStar_All.pipe_right args
        (FStar_List.fold_left FStar_SMTEncoding_Util.mk_ApplyTT e)
let is_app: FStar_SMTEncoding_Term.op -> Prims.bool =
  fun uu___112_1828  ->
    match uu___112_1828 with
    | FStar_SMTEncoding_Term.Var "ApplyTT"|FStar_SMTEncoding_Term.Var
      "ApplyTF" -> true
    | uu____1829 -> false
let is_an_eta_expansion:
  env_t ->
    FStar_SMTEncoding_Term.fv Prims.list ->
      FStar_SMTEncoding_Term.term -> FStar_SMTEncoding_Term.term Prims.option
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
                       FStar_SMTEncoding_Term.freevars = uu____1857;
                       FStar_SMTEncoding_Term.rng = uu____1858;_}::[]),x::xs1)
              when (is_app app) && (FStar_SMTEncoding_Term.fv_eq x y) ->
              check_partial_applications f xs1
          | (FStar_SMTEncoding_Term.App
             (FStar_SMTEncoding_Term.Var f,args),uu____1872) ->
              let uu____1877 =
                ((FStar_List.length args) = (FStar_List.length xs)) &&
                  (FStar_List.forall2
                     (fun a  ->
                        fun v1  ->
                          match a.FStar_SMTEncoding_Term.tm with
                          | FStar_SMTEncoding_Term.FreeV fv ->
                              FStar_SMTEncoding_Term.fv_eq fv v1
                          | uu____1887 -> false) args (FStar_List.rev xs)) in
              if uu____1877 then tok_of_name env f else None
          | (uu____1890,[]) ->
              let fvs = FStar_SMTEncoding_Term.free_variables t in
              let uu____1893 =
                FStar_All.pipe_right fvs
                  (FStar_List.for_all
                     (fun fv  ->
                        let uu____1895 =
                          FStar_Util.for_some
                            (FStar_SMTEncoding_Term.fv_eq fv) vars in
                        Prims.op_Negation uu____1895)) in
              if uu____1893 then Some t else None
          | uu____1898 -> None in
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
    | uu____1982 -> false
let encode_const: FStar_Const.sconst -> FStar_SMTEncoding_Term.term =
  fun uu___113_1985  ->
    match uu___113_1985 with
    | FStar_Const.Const_unit  -> FStar_SMTEncoding_Term.mk_Term_unit
    | FStar_Const.Const_bool (true ) ->
        FStar_SMTEncoding_Term.boxBool FStar_SMTEncoding_Util.mkTrue
    | FStar_Const.Const_bool (false ) ->
        FStar_SMTEncoding_Term.boxBool FStar_SMTEncoding_Util.mkFalse
    | FStar_Const.Const_char c ->
        let uu____1987 =
          let uu____1991 =
            let uu____1993 =
              let uu____1994 =
                FStar_SMTEncoding_Util.mkInteger' (FStar_Util.int_of_char c) in
              FStar_SMTEncoding_Term.boxInt uu____1994 in
            [uu____1993] in
          ("FStar.Char.Char", uu____1991) in
        FStar_SMTEncoding_Util.mkApp uu____1987
    | FStar_Const.Const_int (i,None ) ->
        let uu____2002 = FStar_SMTEncoding_Util.mkInteger i in
        FStar_SMTEncoding_Term.boxInt uu____2002
    | FStar_Const.Const_int (i,Some uu____2004) ->
        failwith "Machine integers should be desugared"
    | FStar_Const.Const_string (bytes,uu____2013) ->
        let uu____2016 = FStar_All.pipe_left FStar_Util.string_of_bytes bytes in
        varops.string_const uu____2016
    | FStar_Const.Const_range r -> FStar_SMTEncoding_Term.mk_Range_const
    | FStar_Const.Const_effect  -> FStar_SMTEncoding_Term.mk_Term_type
    | c ->
        let uu____2020 =
          let uu____2021 = FStar_Syntax_Print.const_to_string c in
          FStar_Util.format1 "Unhandled constant: %s" uu____2021 in
        failwith uu____2020
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
        | FStar_Syntax_Syntax.Tm_arrow uu____2040 -> t1
        | FStar_Syntax_Syntax.Tm_refine uu____2048 ->
            let uu____2053 = FStar_Syntax_Util.unrefine t1 in
            aux true uu____2053
        | uu____2054 ->
            if norm1
            then let uu____2055 = whnf env t1 in aux false uu____2055
            else
              (let uu____2057 =
                 let uu____2058 =
                   FStar_Range.string_of_range t0.FStar_Syntax_Syntax.pos in
                 let uu____2059 = FStar_Syntax_Print.term_to_string t0 in
                 FStar_Util.format2 "(%s) Expected a function typ; got %s"
                   uu____2058 uu____2059 in
               failwith uu____2057) in
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
    | uu____2080 ->
        let uu____2081 = FStar_Syntax_Syntax.mk_Total k1 in ([], uu____2081)
let rec encode_binders:
  FStar_SMTEncoding_Term.term Prims.option ->
    FStar_Syntax_Syntax.binders ->
      env_t ->
        (FStar_SMTEncoding_Term.fv Prims.list* FStar_SMTEncoding_Term.term
          Prims.list* env_t* FStar_SMTEncoding_Term.decls_t*
          FStar_Syntax_Syntax.bv Prims.list)
  =
  fun fuel_opt  ->
    fun bs  ->
      fun env  ->
        (let uu____2224 =
           FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low in
         if uu____2224
         then
           let uu____2225 = FStar_Syntax_Print.binders_to_string ", " bs in
           FStar_Util.print1 "Encoding binders %s\n" uu____2225
         else ());
        (let uu____2227 =
           FStar_All.pipe_right bs
             (FStar_List.fold_left
                (fun uu____2263  ->
                   fun b  ->
                     match uu____2263 with
                     | (vars,guards,env1,decls,names1) ->
                         let uu____2306 =
                           let x = unmangle (Prims.fst b) in
                           let uu____2315 = gen_term_var env1 x in
                           match uu____2315 with
                           | (xxsym,xx,env') ->
                               let uu____2329 =
                                 let uu____2332 =
                                   norm env1 x.FStar_Syntax_Syntax.sort in
                                 encode_term_pred fuel_opt uu____2332 env1 xx in
                               (match uu____2329 with
                                | (guard_x_t,decls') ->
                                    ((xxsym,
                                       FStar_SMTEncoding_Term.Term_sort),
                                      guard_x_t, env', decls', x)) in
                         (match uu____2306 with
                          | (v1,g,env2,decls',n1) ->
                              ((v1 :: vars), (g :: guards), env2,
                                (FStar_List.append decls decls'), (n1 ::
                                names1)))) ([], [], env, [], [])) in
         match uu____2227 with
         | (vars,guards,env1,decls,names1) ->
             ((FStar_List.rev vars), (FStar_List.rev guards), env1, decls,
               (FStar_List.rev names1)))
and encode_term_pred:
  FStar_SMTEncoding_Term.term Prims.option ->
    FStar_Syntax_Syntax.typ ->
      env_t ->
        FStar_SMTEncoding_Term.term ->
          (FStar_SMTEncoding_Term.term* FStar_SMTEncoding_Term.decls_t)
  =
  fun fuel_opt  ->
    fun t  ->
      fun env  ->
        fun e  ->
          let uu____2420 = encode_term t env in
          match uu____2420 with
          | (t1,decls) ->
              let uu____2427 =
                FStar_SMTEncoding_Term.mk_HasTypeWithFuel fuel_opt e t1 in
              (uu____2427, decls)
and encode_term_pred':
  FStar_SMTEncoding_Term.term Prims.option ->
    FStar_Syntax_Syntax.typ ->
      env_t ->
        FStar_SMTEncoding_Term.term ->
          (FStar_SMTEncoding_Term.term* FStar_SMTEncoding_Term.decls_t)
  =
  fun fuel_opt  ->
    fun t  ->
      fun env  ->
        fun e  ->
          let uu____2435 = encode_term t env in
          match uu____2435 with
          | (t1,decls) ->
              (match fuel_opt with
               | None  ->
                   let uu____2444 = FStar_SMTEncoding_Term.mk_HasTypeZ e t1 in
                   (uu____2444, decls)
               | Some f ->
                   let uu____2446 =
                     FStar_SMTEncoding_Term.mk_HasTypeFuel f e t1 in
                   (uu____2446, decls))
and encode_term:
  FStar_Syntax_Syntax.typ ->
    env_t -> (FStar_SMTEncoding_Term.term* FStar_SMTEncoding_Term.decls_t)
  =
  fun t  ->
    fun env  ->
      let t0 = FStar_Syntax_Subst.compress t in
      (let uu____2453 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv)
           (FStar_Options.Other "SMTEncoding") in
       if uu____2453
       then
         let uu____2454 = FStar_Syntax_Print.tag_of_term t in
         let uu____2455 = FStar_Syntax_Print.tag_of_term t0 in
         let uu____2456 = FStar_Syntax_Print.term_to_string t0 in
         FStar_Util.print3 "(%s) (%s)   %s\n" uu____2454 uu____2455
           uu____2456
       else ());
      (match t0.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Tm_delayed _|FStar_Syntax_Syntax.Tm_unknown  ->
           let uu____2461 =
             let uu____2462 =
               FStar_All.pipe_left FStar_Range.string_of_range
                 t.FStar_Syntax_Syntax.pos in
             let uu____2463 = FStar_Syntax_Print.tag_of_term t0 in
             let uu____2464 = FStar_Syntax_Print.term_to_string t0 in
             let uu____2465 = FStar_Syntax_Print.term_to_string t in
             FStar_Util.format4 "(%s) Impossible: %s\n%s\n%s\n" uu____2462
               uu____2463 uu____2464 uu____2465 in
           failwith uu____2461
       | FStar_Syntax_Syntax.Tm_bvar x ->
           let uu____2469 =
             let uu____2470 = FStar_Syntax_Print.bv_to_string x in
             FStar_Util.format1 "Impossible: locally nameless; got %s"
               uu____2470 in
           failwith uu____2469
       | FStar_Syntax_Syntax.Tm_ascribed (t1,k,uu____2475) ->
           encode_term t1 env
       | FStar_Syntax_Syntax.Tm_meta (t1,uu____2505) -> encode_term t1 env
       | FStar_Syntax_Syntax.Tm_name x ->
           let t1 = lookup_term_var env x in (t1, [])
       | FStar_Syntax_Syntax.Tm_fvar v1 ->
           let uu____2514 =
             lookup_free_var env v1.FStar_Syntax_Syntax.fv_name in
           (uu____2514, [])
       | FStar_Syntax_Syntax.Tm_type uu____2520 ->
           (FStar_SMTEncoding_Term.mk_Term_type, [])
       | FStar_Syntax_Syntax.Tm_uinst (t1,uu____2523) -> encode_term t1 env
       | FStar_Syntax_Syntax.Tm_constant c ->
           let uu____2529 = encode_const c in (uu____2529, [])
       | FStar_Syntax_Syntax.Tm_arrow (binders,c) ->
           let module_name = env.current_module_name in
           let uu____2544 = FStar_Syntax_Subst.open_comp binders c in
           (match uu____2544 with
            | (binders1,res) ->
                let uu____2551 =
                  (env.encode_non_total_function_typ &&
                     (FStar_Syntax_Util.is_pure_or_ghost_comp res))
                    || (FStar_Syntax_Util.is_tot_or_gtot_comp res) in
                if uu____2551
                then
                  let uu____2554 = encode_binders None binders1 env in
                  (match uu____2554 with
                   | (vars,guards,env',decls,uu____2569) ->
                       let fsym =
                         let uu____2579 = varops.fresh "f" in
                         (uu____2579, FStar_SMTEncoding_Term.Term_sort) in
                       let f = FStar_SMTEncoding_Util.mkFreeV fsym in
                       let app = mk_Apply f vars in
                       let uu____2582 =
                         FStar_TypeChecker_Util.pure_or_ghost_pre_and_post
                           (let uu___138_2586 = env.tcenv in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___138_2586.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___138_2586.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___138_2586.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___138_2586.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___138_2586.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___138_2586.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                (uu___138_2586.FStar_TypeChecker_Env.expected_typ);
                              FStar_TypeChecker_Env.sigtab =
                                (uu___138_2586.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.is_pattern =
                                (uu___138_2586.FStar_TypeChecker_Env.is_pattern);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___138_2586.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___138_2586.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___138_2586.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___138_2586.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___138_2586.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___138_2586.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___138_2586.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___138_2586.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___138_2586.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___138_2586.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.type_of =
                                (uu___138_2586.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___138_2586.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.use_bv_sorts =
                                (uu___138_2586.FStar_TypeChecker_Env.use_bv_sorts);
                              FStar_TypeChecker_Env.qname_and_index =
                                (uu___138_2586.FStar_TypeChecker_Env.qname_and_index)
                            }) res in
                       (match uu____2582 with
                        | (pre_opt,res_t) ->
                            let uu____2593 =
                              encode_term_pred None res_t env' app in
                            (match uu____2593 with
                             | (res_pred,decls') ->
                                 let uu____2600 =
                                   match pre_opt with
                                   | None  ->
                                       let uu____2607 =
                                         FStar_SMTEncoding_Util.mk_and_l
                                           guards in
                                       (uu____2607, [])
                                   | Some pre ->
                                       let uu____2610 =
                                         encode_formula pre env' in
                                       (match uu____2610 with
                                        | (guard,decls0) ->
                                            let uu____2618 =
                                              FStar_SMTEncoding_Util.mk_and_l
                                                (guard :: guards) in
                                            (uu____2618, decls0)) in
                                 (match uu____2600 with
                                  | (guards1,guard_decls) ->
                                      let t_interp =
                                        let uu____2626 =
                                          let uu____2632 =
                                            FStar_SMTEncoding_Util.mkImp
                                              (guards1, res_pred) in
                                          ([[app]], vars, uu____2632) in
                                        FStar_SMTEncoding_Util.mkForall
                                          uu____2626 in
                                      let cvars =
                                        let uu____2642 =
                                          FStar_SMTEncoding_Term.free_variables
                                            t_interp in
                                        FStar_All.pipe_right uu____2642
                                          (FStar_List.filter
                                             (fun uu____2648  ->
                                                match uu____2648 with
                                                | (x,uu____2652) ->
                                                    x <> (Prims.fst fsym))) in
                                      let tkey =
                                        FStar_SMTEncoding_Util.mkForall
                                          ([], (fsym :: cvars), t_interp) in
                                      let tkey_hash =
                                        FStar_SMTEncoding_Term.hash_of_term
                                          tkey in
                                      let uu____2663 =
                                        FStar_Util.smap_try_find env.cache
                                          tkey_hash in
                                      (match uu____2663 with
                                       | Some cache_entry ->
                                           let uu____2668 =
                                             let uu____2669 =
                                               let uu____2673 =
                                                 FStar_All.pipe_right cvars
                                                   (FStar_List.map
                                                      FStar_SMTEncoding_Util.mkFreeV) in
                                               ((cache_entry.cache_symbol_name),
                                                 uu____2673) in
                                             FStar_SMTEncoding_Util.mkApp
                                               uu____2669 in
                                           (uu____2668,
                                             (use_cache_entry cache_entry))
                                       | None  ->
                                           let tsym =
                                             let uu____2684 =
                                               let uu____2685 =
                                                 FStar_Util.digest_of_string
                                                   tkey_hash in
                                               Prims.strcat "Tm_arrow_"
                                                 uu____2685 in
                                             varops.mk_unique uu____2684 in
                                           let cvar_sorts =
                                             FStar_List.map Prims.snd cvars in
                                           let caption =
                                             let uu____2692 =
                                               FStar_Options.log_queries () in
                                             if uu____2692
                                             then
                                               let uu____2694 =
                                                 FStar_TypeChecker_Normalize.term_to_string
                                                   env.tcenv t0 in
                                               Some uu____2694
                                             else None in
                                           let tdecl =
                                             FStar_SMTEncoding_Term.DeclFun
                                               (tsym, cvar_sorts,
                                                 FStar_SMTEncoding_Term.Term_sort,
                                                 caption) in
                                           let t1 =
                                             let uu____2700 =
                                               let uu____2704 =
                                                 FStar_List.map
                                                   FStar_SMTEncoding_Util.mkFreeV
                                                   cvars in
                                               (tsym, uu____2704) in
                                             FStar_SMTEncoding_Util.mkApp
                                               uu____2700 in
                                           let t_has_kind =
                                             FStar_SMTEncoding_Term.mk_HasType
                                               t1
                                               FStar_SMTEncoding_Term.mk_Term_type in
                                           let k_assumption =
                                             let a_name =
                                               Prims.strcat "kinding_" tsym in
                                             let uu____2712 =
                                               let uu____2716 =
                                                 FStar_SMTEncoding_Util.mkForall
                                                   ([[t_has_kind]], cvars,
                                                     t_has_kind) in
                                               (uu____2716, (Some a_name),
                                                 a_name) in
                                             FStar_SMTEncoding_Util.mkAssume
                                               uu____2712 in
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
                                             let uu____2729 =
                                               let uu____2733 =
                                                 let uu____2734 =
                                                   let uu____2740 =
                                                     let uu____2741 =
                                                       let uu____2744 =
                                                         let uu____2745 =
                                                           FStar_SMTEncoding_Term.mk_PreType
                                                             f in
                                                         FStar_SMTEncoding_Term.mk_tester
                                                           "Tm_arrow"
                                                           uu____2745 in
                                                       (f_has_t, uu____2744) in
                                                     FStar_SMTEncoding_Util.mkImp
                                                       uu____2741 in
                                                   ([[f_has_t]], (fsym ::
                                                     cvars), uu____2740) in
                                                 mkForall_fuel uu____2734 in
                                               (uu____2733,
                                                 (Some
                                                    "pre-typing for functions"),
                                                 (Prims.strcat module_name
                                                    (Prims.strcat "_" a_name))) in
                                             FStar_SMTEncoding_Util.mkAssume
                                               uu____2729 in
                                           let t_interp1 =
                                             let a_name =
                                               Prims.strcat "interpretation_"
                                                 tsym in
                                             let uu____2758 =
                                               let uu____2762 =
                                                 let uu____2763 =
                                                   let uu____2769 =
                                                     FStar_SMTEncoding_Util.mkIff
                                                       (f_has_t_z, t_interp) in
                                                   ([[f_has_t_z]], (fsym ::
                                                     cvars), uu____2769) in
                                                 FStar_SMTEncoding_Util.mkForall
                                                   uu____2763 in
                                               (uu____2762, (Some a_name),
                                                 (Prims.strcat module_name
                                                    (Prims.strcat "_" a_name))) in
                                             FStar_SMTEncoding_Util.mkAssume
                                               uu____2758 in
                                           let t_decls =
                                             FStar_List.append (tdecl ::
                                               decls)
                                               (FStar_List.append decls'
                                                  (FStar_List.append
                                                     guard_decls
                                                     [k_assumption;
                                                     pre_typing;
                                                     t_interp1])) in
                                           ((let uu____2783 =
                                               mk_cache_entry env tsym
                                                 cvar_sorts t_decls in
                                             FStar_Util.smap_add env.cache
                                               tkey_hash uu____2783);
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
                     let uu____2794 =
                       let uu____2798 =
                         FStar_SMTEncoding_Term.mk_HasType t1
                           FStar_SMTEncoding_Term.mk_Term_type in
                       (uu____2798, (Some "Typing for non-total arrows"),
                         (Prims.strcat module_name (Prims.strcat "_" a_name))) in
                     FStar_SMTEncoding_Util.mkAssume uu____2794 in
                   let fsym = ("f", FStar_SMTEncoding_Term.Term_sort) in
                   let f = FStar_SMTEncoding_Util.mkFreeV fsym in
                   let f_has_t = FStar_SMTEncoding_Term.mk_HasType f t1 in
                   let t_interp =
                     let a_name = Prims.strcat "pre_typing_" tsym in
                     let uu____2807 =
                       let uu____2811 =
                         let uu____2812 =
                           let uu____2818 =
                             let uu____2819 =
                               let uu____2822 =
                                 let uu____2823 =
                                   FStar_SMTEncoding_Term.mk_PreType f in
                                 FStar_SMTEncoding_Term.mk_tester "Tm_arrow"
                                   uu____2823 in
                               (f_has_t, uu____2822) in
                             FStar_SMTEncoding_Util.mkImp uu____2819 in
                           ([[f_has_t]], [fsym], uu____2818) in
                         mkForall_fuel uu____2812 in
                       (uu____2811, (Some a_name),
                         (Prims.strcat module_name (Prims.strcat "_" a_name))) in
                     FStar_SMTEncoding_Util.mkAssume uu____2807 in
                   (t1, [tdecl; t_kinding; t_interp])))
       | FStar_Syntax_Syntax.Tm_refine uu____2837 ->
           let uu____2842 =
             let uu____2845 =
               FStar_TypeChecker_Normalize.normalize_refinement
                 [FStar_TypeChecker_Normalize.WHNF;
                 FStar_TypeChecker_Normalize.EraseUniverses] env.tcenv t0 in
             match uu____2845 with
             | { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_refine (x,f);
                 FStar_Syntax_Syntax.tk = uu____2850;
                 FStar_Syntax_Syntax.pos = uu____2851;
                 FStar_Syntax_Syntax.vars = uu____2852;_} ->
                 let uu____2859 = FStar_Syntax_Subst.open_term [(x, None)] f in
                 (match uu____2859 with
                  | (b,f1) ->
                      let uu____2873 =
                        let uu____2874 = FStar_List.hd b in
                        Prims.fst uu____2874 in
                      (uu____2873, f1))
             | uu____2879 -> failwith "impossible" in
           (match uu____2842 with
            | (x,f) ->
                let uu____2886 = encode_term x.FStar_Syntax_Syntax.sort env in
                (match uu____2886 with
                 | (base_t,decls) ->
                     let uu____2893 = gen_term_var env x in
                     (match uu____2893 with
                      | (x1,xtm,env') ->
                          let uu____2902 = encode_formula f env' in
                          (match uu____2902 with
                           | (refinement,decls') ->
                               let uu____2909 =
                                 fresh_fvar "f"
                                   FStar_SMTEncoding_Term.Fuel_sort in
                               (match uu____2909 with
                                | (fsym,fterm) ->
                                    let tm_has_type_with_fuel =
                                      FStar_SMTEncoding_Term.mk_HasTypeWithFuel
                                        (Some fterm) xtm base_t in
                                    let encoding =
                                      FStar_SMTEncoding_Util.mkAnd
                                        (tm_has_type_with_fuel, refinement) in
                                    let cvars =
                                      let uu____2920 =
                                        let uu____2922 =
                                          FStar_SMTEncoding_Term.free_variables
                                            refinement in
                                        let uu____2926 =
                                          FStar_SMTEncoding_Term.free_variables
                                            tm_has_type_with_fuel in
                                        FStar_List.append uu____2922
                                          uu____2926 in
                                      FStar_Util.remove_dups
                                        FStar_SMTEncoding_Term.fv_eq
                                        uu____2920 in
                                    let cvars1 =
                                      FStar_All.pipe_right cvars
                                        (FStar_List.filter
                                           (fun uu____2942  ->
                                              match uu____2942 with
                                              | (y,uu____2946) ->
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
                                    let uu____2965 =
                                      FStar_Util.smap_try_find env.cache
                                        tkey_hash in
                                    (match uu____2965 with
                                     | Some cache_entry ->
                                         let uu____2970 =
                                           let uu____2971 =
                                             let uu____2975 =
                                               FStar_All.pipe_right cvars1
                                                 (FStar_List.map
                                                    FStar_SMTEncoding_Util.mkFreeV) in
                                             ((cache_entry.cache_symbol_name),
                                               uu____2975) in
                                           FStar_SMTEncoding_Util.mkApp
                                             uu____2971 in
                                         (uu____2970,
                                           (FStar_List.append decls
                                              (FStar_List.append decls'
                                                 (use_cache_entry cache_entry))))
                                     | None  ->
                                         let module_name =
                                           env.current_module_name in
                                         let tsym =
                                           let uu____2987 =
                                             let uu____2988 =
                                               let uu____2989 =
                                                 FStar_Util.digest_of_string
                                                   tkey_hash in
                                               Prims.strcat "_Tm_refine_"
                                                 uu____2989 in
                                             Prims.strcat module_name
                                               uu____2988 in
                                           varops.mk_unique uu____2987 in
                                         let cvar_sorts =
                                           FStar_List.map Prims.snd cvars1 in
                                         let tdecl =
                                           FStar_SMTEncoding_Term.DeclFun
                                             (tsym, cvar_sorts,
                                               FStar_SMTEncoding_Term.Term_sort,
                                               None) in
                                         let t1 =
                                           let uu____2998 =
                                             let uu____3002 =
                                               FStar_List.map
                                                 FStar_SMTEncoding_Util.mkFreeV
                                                 cvars1 in
                                             (tsym, uu____3002) in
                                           FStar_SMTEncoding_Util.mkApp
                                             uu____2998 in
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
                                           let uu____3012 =
                                             let uu____3016 =
                                               let uu____3017 =
                                                 let uu____3023 =
                                                   FStar_SMTEncoding_Util.mkIff
                                                     (t_haseq_ref,
                                                       t_haseq_base) in
                                                 ([[t_haseq_ref]], cvars1,
                                                   uu____3023) in
                                               FStar_SMTEncoding_Util.mkForall
                                                 uu____3017 in
                                             (uu____3016,
                                               (Some
                                                  (Prims.strcat "haseq for "
                                                     tsym)),
                                               (Prims.strcat "haseq" tsym)) in
                                           FStar_SMTEncoding_Util.mkAssume
                                             uu____3012 in
                                         let t_kinding =
                                           let uu____3033 =
                                             let uu____3037 =
                                               FStar_SMTEncoding_Util.mkForall
                                                 ([[t_has_kind]], cvars1,
                                                   t_has_kind) in
                                             (uu____3037,
                                               (Some "refinement kinding"),
                                               (Prims.strcat
                                                  "refinement_kinding_" tsym)) in
                                           FStar_SMTEncoding_Util.mkAssume
                                             uu____3033 in
                                         let t_interp =
                                           let uu____3047 =
                                             let uu____3051 =
                                               let uu____3052 =
                                                 let uu____3058 =
                                                   FStar_SMTEncoding_Util.mkIff
                                                     (x_has_t, encoding) in
                                                 ([[x_has_t]], (ffv :: xfv ::
                                                   cvars1), uu____3058) in
                                               FStar_SMTEncoding_Util.mkForall
                                                 uu____3052 in
                                             let uu____3070 =
                                               let uu____3072 =
                                                 FStar_Syntax_Print.term_to_string
                                                   t0 in
                                               Some uu____3072 in
                                             (uu____3051, uu____3070,
                                               (Prims.strcat
                                                  "refinement_interpretation_"
                                                  tsym)) in
                                           FStar_SMTEncoding_Util.mkAssume
                                             uu____3047 in
                                         let t_decls =
                                           FStar_List.append decls
                                             (FStar_List.append decls'
                                                [tdecl;
                                                t_kinding;
                                                t_interp;
                                                t_haseq1]) in
                                         ((let uu____3077 =
                                             mk_cache_entry env tsym
                                               cvar_sorts t_decls in
                                           FStar_Util.smap_add env.cache
                                             tkey_hash uu____3077);
                                          (t1, t_decls))))))))
       | FStar_Syntax_Syntax.Tm_uvar (uv,k) ->
           let ttm =
             let uu____3094 = FStar_Unionfind.uvar_id uv in
             FStar_SMTEncoding_Util.mk_Term_uvar uu____3094 in
           let uu____3098 = encode_term_pred None k env ttm in
           (match uu____3098 with
            | (t_has_k,decls) ->
                let d =
                  let uu____3106 =
                    let uu____3110 =
                      let uu____3111 =
                        let uu____3112 =
                          let uu____3113 = FStar_Unionfind.uvar_id uv in
                          FStar_All.pipe_left FStar_Util.string_of_int
                            uu____3113 in
                        FStar_Util.format1 "uvar_typing_%s" uu____3112 in
                      varops.mk_unique uu____3111 in
                    (t_has_k, (Some "Uvar typing"), uu____3110) in
                  FStar_SMTEncoding_Util.mkAssume uu____3106 in
                (ttm, (FStar_List.append decls [d])))
       | FStar_Syntax_Syntax.Tm_app uu____3119 ->
           let uu____3129 = FStar_Syntax_Util.head_and_args t0 in
           (match uu____3129 with
            | (head1,args_e) ->
                let uu____3157 =
                  let uu____3165 =
                    let uu____3166 = FStar_Syntax_Subst.compress head1 in
                    uu____3166.FStar_Syntax_Syntax.n in
                  (uu____3165, args_e) in
                (match uu____3157 with
                 | (uu____3176,uu____3177) when head_redex env head1 ->
                     let uu____3188 = whnf env t in
                     encode_term uu____3188 env
                 | (FStar_Syntax_Syntax.Tm_uinst
                    ({
                       FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                       FStar_Syntax_Syntax.tk = _;
                       FStar_Syntax_Syntax.pos = _;
                       FStar_Syntax_Syntax.vars = _;_},_),_::(v1,_)::
                    (v2,_)::[])
                   |(FStar_Syntax_Syntax.Tm_fvar fv,_::(v1,_)::(v2,_)::[])
                     when
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Syntax_Const.lexcons_lid
                     ->
                     let uu____3262 = encode_term v1 env in
                     (match uu____3262 with
                      | (v11,decls1) ->
                          let uu____3269 = encode_term v2 env in
                          (match uu____3269 with
                           | (v21,decls2) ->
                               let uu____3276 =
                                 FStar_SMTEncoding_Util.mk_LexCons v11 v21 in
                               (uu____3276,
                                 (FStar_List.append decls1 decls2))))
                 | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify
                    ),uu____3278) ->
                     let e0 =
                       let uu____3290 = FStar_List.hd args_e in
                       FStar_TypeChecker_Util.reify_body_with_arg env.tcenv
                         head1 uu____3290 in
                     ((let uu____3296 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug env.tcenv)
                           (FStar_Options.Other "SMTEncodingReify") in
                       if uu____3296
                       then
                         let uu____3297 =
                           FStar_Syntax_Print.term_to_string e0 in
                         FStar_Util.print1 "Result of normalization %s\n"
                           uu____3297
                       else ());
                      (let e =
                         let uu____3302 =
                           let uu____3303 =
                             FStar_TypeChecker_Util.remove_reify e0 in
                           let uu____3304 = FStar_List.tl args_e in
                           FStar_Syntax_Syntax.mk_Tm_app uu____3303
                             uu____3304 in
                         uu____3302 None t0.FStar_Syntax_Syntax.pos in
                       encode_term e env))
                 | (FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_reflect
                    uu____3313),(arg,uu____3315)::[]) -> encode_term arg env
                 | uu____3333 ->
                     let uu____3341 = encode_args args_e env in
                     (match uu____3341 with
                      | (args,decls) ->
                          let encode_partial_app ht_opt =
                            let uu____3374 = encode_term head1 env in
                            match uu____3374 with
                            | (head2,decls') ->
                                let app_tm = mk_Apply_args head2 args in
                                (match ht_opt with
                                 | None  ->
                                     (app_tm,
                                       (FStar_List.append decls decls'))
                                 | Some (formals,c) ->
                                     let uu____3413 =
                                       FStar_Util.first_N
                                         (FStar_List.length args_e) formals in
                                     (match uu____3413 with
                                      | (formals1,rest) ->
                                          let subst1 =
                                            FStar_List.map2
                                              (fun uu____3455  ->
                                                 fun uu____3456  ->
                                                   match (uu____3455,
                                                           uu____3456)
                                                   with
                                                   | ((bv,uu____3470),
                                                      (a,uu____3472)) ->
                                                       FStar_Syntax_Syntax.NT
                                                         (bv, a)) formals1
                                              args_e in
                                          let ty =
                                            let uu____3486 =
                                              FStar_Syntax_Util.arrow rest c in
                                            FStar_All.pipe_right uu____3486
                                              (FStar_Syntax_Subst.subst
                                                 subst1) in
                                          let uu____3491 =
                                            encode_term_pred None ty env
                                              app_tm in
                                          (match uu____3491 with
                                           | (has_type,decls'') ->
                                               let cvars =
                                                 FStar_SMTEncoding_Term.free_variables
                                                   has_type in
                                               let e_typing =
                                                 let uu____3501 =
                                                   let uu____3505 =
                                                     FStar_SMTEncoding_Util.mkForall
                                                       ([[has_type]], cvars,
                                                         has_type) in
                                                   let uu____3510 =
                                                     let uu____3511 =
                                                       let uu____3512 =
                                                         let uu____3513 =
                                                           FStar_SMTEncoding_Term.hash_of_term
                                                             app_tm in
                                                         FStar_Util.digest_of_string
                                                           uu____3513 in
                                                       Prims.strcat
                                                         "partial_app_typing_"
                                                         uu____3512 in
                                                     varops.mk_unique
                                                       uu____3511 in
                                                   (uu____3505,
                                                     (Some
                                                        "Partial app typing"),
                                                     uu____3510) in
                                                 FStar_SMTEncoding_Util.mkAssume
                                                   uu____3501 in
                                               (app_tm,
                                                 (FStar_List.append decls
                                                    (FStar_List.append decls'
                                                       (FStar_List.append
                                                          decls'' [e_typing]))))))) in
                          let encode_full_app fv =
                            let uu____3530 = lookup_free_var_sym env fv in
                            match uu____3530 with
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
                                 FStar_Syntax_Syntax.tk = _;
                                 FStar_Syntax_Syntax.pos = _;
                                 FStar_Syntax_Syntax.vars = _;_},_)
                              |FStar_Syntax_Syntax.Tm_name x ->
                                Some (x.FStar_Syntax_Syntax.sort)
                            | FStar_Syntax_Syntax.Tm_uinst
                              ({
                                 FStar_Syntax_Syntax.n =
                                   FStar_Syntax_Syntax.Tm_fvar fv;
                                 FStar_Syntax_Syntax.tk = _;
                                 FStar_Syntax_Syntax.pos = _;
                                 FStar_Syntax_Syntax.vars = _;_},_)
                              |FStar_Syntax_Syntax.Tm_fvar fv ->
                                let uu____3568 =
                                  let uu____3569 =
                                    let uu____3572 =
                                      FStar_TypeChecker_Env.lookup_lid
                                        env.tcenv
                                        (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                                    FStar_All.pipe_right uu____3572 Prims.fst in
                                  FStar_All.pipe_right uu____3569 Prims.snd in
                                Some uu____3568
                            | FStar_Syntax_Syntax.Tm_ascribed
                                (uu____3591,(FStar_Util.Inl t1,uu____3593),uu____3594)
                                -> Some t1
                            | FStar_Syntax_Syntax.Tm_ascribed
                                (uu____3632,(FStar_Util.Inr c,uu____3634),uu____3635)
                                -> Some (FStar_Syntax_Util.comp_result c)
                            | uu____3673 -> None in
                          (match head_type with
                           | None  -> encode_partial_app None
                           | Some head_type1 ->
                               let head_type2 =
                                 let uu____3693 =
                                   FStar_TypeChecker_Normalize.normalize_refinement
                                     [FStar_TypeChecker_Normalize.WHNF;
                                     FStar_TypeChecker_Normalize.EraseUniverses]
                                     env.tcenv head_type1 in
                                 FStar_All.pipe_left
                                   FStar_Syntax_Util.unrefine uu____3693 in
                               let uu____3694 =
                                 curried_arrow_formals_comp head_type2 in
                               (match uu____3694 with
                                | (formals,c) ->
                                    (match head2.FStar_Syntax_Syntax.n with
                                     | FStar_Syntax_Syntax.Tm_uinst
                                       ({
                                          FStar_Syntax_Syntax.n =
                                            FStar_Syntax_Syntax.Tm_fvar fv;
                                          FStar_Syntax_Syntax.tk = _;
                                          FStar_Syntax_Syntax.pos = _;
                                          FStar_Syntax_Syntax.vars = _;_},_)
                                       |FStar_Syntax_Syntax.Tm_fvar fv when
                                         (FStar_List.length formals) =
                                           (FStar_List.length args)
                                         ->
                                         encode_full_app
                                           fv.FStar_Syntax_Syntax.fv_name
                                     | uu____3719 ->
                                         if
                                           (FStar_List.length formals) >
                                             (FStar_List.length args)
                                         then
                                           encode_partial_app
                                             (Some (formals, c))
                                         else encode_partial_app None))))))
       | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
           let uu____3764 = FStar_Syntax_Subst.open_term' bs body in
           (match uu____3764 with
            | (bs1,body1,opening) ->
                let fallback uu____3779 =
                  let f = varops.fresh "Tm_abs" in
                  let decl =
                    FStar_SMTEncoding_Term.DeclFun
                      (f, [], FStar_SMTEncoding_Term.Term_sort,
                        (Some "Imprecise function encoding")) in
                  let uu____3784 =
                    FStar_SMTEncoding_Util.mkFreeV
                      (f, FStar_SMTEncoding_Term.Term_sort) in
                  (uu____3784, [decl]) in
                let is_impure lc =
                  match lc with
                  | FStar_Util.Inl lc1 ->
                      let uu____3795 =
                        FStar_Syntax_Util.is_pure_or_ghost_lcomp lc1 in
                      Prims.op_Negation uu____3795
                  | FStar_Util.Inr (eff,uu____3797) ->
                      let uu____3803 =
                        FStar_TypeChecker_Util.is_pure_or_ghost_effect
                          env.tcenv eff in
                      FStar_All.pipe_right uu____3803 Prims.op_Negation in
                let reify_comp_and_body env1 c body2 =
                  let reified_body =
                    FStar_TypeChecker_Util.reify_body env1.tcenv body2 in
                  let c1 =
                    match c with
                    | FStar_Util.Inl lc ->
                        let typ =
                          let uu____3848 = lc.FStar_Syntax_Syntax.comp () in
                          FStar_TypeChecker_Env.reify_comp
                            (let uu___139_3849 = env1.tcenv in
                             {
                               FStar_TypeChecker_Env.solver =
                                 (uu___139_3849.FStar_TypeChecker_Env.solver);
                               FStar_TypeChecker_Env.range =
                                 (uu___139_3849.FStar_TypeChecker_Env.range);
                               FStar_TypeChecker_Env.curmodule =
                                 (uu___139_3849.FStar_TypeChecker_Env.curmodule);
                               FStar_TypeChecker_Env.gamma =
                                 (uu___139_3849.FStar_TypeChecker_Env.gamma);
                               FStar_TypeChecker_Env.gamma_cache =
                                 (uu___139_3849.FStar_TypeChecker_Env.gamma_cache);
                               FStar_TypeChecker_Env.modules =
                                 (uu___139_3849.FStar_TypeChecker_Env.modules);
                               FStar_TypeChecker_Env.expected_typ =
                                 (uu___139_3849.FStar_TypeChecker_Env.expected_typ);
                               FStar_TypeChecker_Env.sigtab =
                                 (uu___139_3849.FStar_TypeChecker_Env.sigtab);
                               FStar_TypeChecker_Env.is_pattern =
                                 (uu___139_3849.FStar_TypeChecker_Env.is_pattern);
                               FStar_TypeChecker_Env.instantiate_imp =
                                 (uu___139_3849.FStar_TypeChecker_Env.instantiate_imp);
                               FStar_TypeChecker_Env.effects =
                                 (uu___139_3849.FStar_TypeChecker_Env.effects);
                               FStar_TypeChecker_Env.generalize =
                                 (uu___139_3849.FStar_TypeChecker_Env.generalize);
                               FStar_TypeChecker_Env.letrecs =
                                 (uu___139_3849.FStar_TypeChecker_Env.letrecs);
                               FStar_TypeChecker_Env.top_level =
                                 (uu___139_3849.FStar_TypeChecker_Env.top_level);
                               FStar_TypeChecker_Env.check_uvars =
                                 (uu___139_3849.FStar_TypeChecker_Env.check_uvars);
                               FStar_TypeChecker_Env.use_eq =
                                 (uu___139_3849.FStar_TypeChecker_Env.use_eq);
                               FStar_TypeChecker_Env.is_iface =
                                 (uu___139_3849.FStar_TypeChecker_Env.is_iface);
                               FStar_TypeChecker_Env.admit =
                                 (uu___139_3849.FStar_TypeChecker_Env.admit);
                               FStar_TypeChecker_Env.lax = true;
                               FStar_TypeChecker_Env.lax_universes =
                                 (uu___139_3849.FStar_TypeChecker_Env.lax_universes);
                               FStar_TypeChecker_Env.type_of =
                                 (uu___139_3849.FStar_TypeChecker_Env.type_of);
                               FStar_TypeChecker_Env.universe_of =
                                 (uu___139_3849.FStar_TypeChecker_Env.universe_of);
                               FStar_TypeChecker_Env.use_bv_sorts =
                                 (uu___139_3849.FStar_TypeChecker_Env.use_bv_sorts);
                               FStar_TypeChecker_Env.qname_and_index =
                                 (uu___139_3849.FStar_TypeChecker_Env.qname_and_index)
                             }) uu____3848 FStar_Syntax_Syntax.U_unknown in
                        let uu____3850 =
                          let uu____3851 = FStar_Syntax_Syntax.mk_Total typ in
                          FStar_Syntax_Util.lcomp_of_comp uu____3851 in
                        FStar_Util.Inl uu____3850
                    | FStar_Util.Inr (eff_name,uu____3858) -> c in
                  (c1, reified_body) in
                let codomain_eff lc =
                  match lc with
                  | FStar_Util.Inl lc1 ->
                      let uu____3889 =
                        let uu____3890 = lc1.FStar_Syntax_Syntax.comp () in
                        FStar_Syntax_Subst.subst_comp opening uu____3890 in
                      FStar_All.pipe_right uu____3889
                        (fun _0_31  -> Some _0_31)
                  | FStar_Util.Inr (eff,flags) ->
                      let new_uvar1 uu____3902 =
                        let uu____3903 =
                          FStar_TypeChecker_Rel.new_uvar
                            FStar_Range.dummyRange []
                            FStar_Syntax_Util.ktype0 in
                        FStar_All.pipe_right uu____3903 Prims.fst in
                      if
                        FStar_Ident.lid_equals eff
                          FStar_Syntax_Const.effect_Tot_lid
                      then
                        let uu____3911 =
                          let uu____3912 = new_uvar1 () in
                          FStar_Syntax_Syntax.mk_Total uu____3912 in
                        FStar_All.pipe_right uu____3911
                          (fun _0_32  -> Some _0_32)
                      else
                        if
                          FStar_Ident.lid_equals eff
                            FStar_Syntax_Const.effect_GTot_lid
                        then
                          (let uu____3916 =
                             let uu____3917 = new_uvar1 () in
                             FStar_Syntax_Syntax.mk_GTotal uu____3917 in
                           FStar_All.pipe_right uu____3916
                             (fun _0_33  -> Some _0_33))
                        else None in
                (match lopt with
                 | None  ->
                     ((let uu____3928 =
                         let uu____3929 =
                           FStar_Syntax_Print.term_to_string t0 in
                         FStar_Util.format1
                           "Losing precision when encoding a function literal: %s\n(Unnannotated abstraction in the compiler ?)"
                           uu____3929 in
                       FStar_Errors.warn t0.FStar_Syntax_Syntax.pos
                         uu____3928);
                      fallback ())
                 | Some lc ->
                     let lc1 = lc in
                     let uu____3944 =
                       (is_impure lc1) &&
                         (let uu____3945 =
                            FStar_TypeChecker_Env.is_reifiable env.tcenv lc1 in
                          Prims.op_Negation uu____3945) in
                     if uu____3944
                     then fallback ()
                     else
                       (let cache_size = FStar_Util.smap_size env.cache in
                        let uu____3950 = encode_binders None bs1 env in
                        match uu____3950 with
                        | (vars,guards,envbody,decls,uu____3965) ->
                            let uu____3972 =
                              let uu____3980 =
                                FStar_TypeChecker_Env.is_reifiable env.tcenv
                                  lc1 in
                              if uu____3980
                              then reify_comp_and_body envbody lc1 body1
                              else (lc1, body1) in
                            (match uu____3972 with
                             | (lc2,body2) ->
                                 let uu____4005 = encode_term body2 envbody in
                                 (match uu____4005 with
                                  | (body3,decls') ->
                                      let uu____4012 =
                                        let uu____4017 = codomain_eff lc2 in
                                        match uu____4017 with
                                        | None  -> (None, [])
                                        | Some c ->
                                            let tfun =
                                              FStar_Syntax_Util.arrow bs1 c in
                                            let uu____4029 =
                                              encode_term tfun env in
                                            (match uu____4029 with
                                             | (t1,decls1) ->
                                                 ((Some t1), decls1)) in
                                      (match uu____4012 with
                                       | (arrow_t_opt,decls'') ->
                                           let key_body =
                                             let uu____4048 =
                                               let uu____4054 =
                                                 let uu____4055 =
                                                   let uu____4058 =
                                                     FStar_SMTEncoding_Util.mk_and_l
                                                       guards in
                                                   (uu____4058, body3) in
                                                 FStar_SMTEncoding_Util.mkImp
                                                   uu____4055 in
                                               ([], vars, uu____4054) in
                                             FStar_SMTEncoding_Util.mkForall
                                               uu____4048 in
                                           let cvars =
                                             FStar_SMTEncoding_Term.free_variables
                                               key_body in
                                           let cvars1 =
                                             match arrow_t_opt with
                                             | None  -> cvars
                                             | Some t1 ->
                                                 let uu____4066 =
                                                   let uu____4068 =
                                                     FStar_SMTEncoding_Term.free_variables
                                                       t1 in
                                                   FStar_List.append
                                                     uu____4068 cvars in
                                                 FStar_Util.remove_dups
                                                   FStar_SMTEncoding_Term.fv_eq
                                                   uu____4066 in
                                           let tkey =
                                             FStar_SMTEncoding_Util.mkForall
                                               ([], cvars1, key_body) in
                                           let tkey_hash =
                                             FStar_SMTEncoding_Term.hash_of_term
                                               tkey in
                                           let uu____4079 =
                                             FStar_Util.smap_try_find
                                               env.cache tkey_hash in
                                           (match uu____4079 with
                                            | Some cache_entry ->
                                                let uu____4084 =
                                                  let uu____4085 =
                                                    let uu____4089 =
                                                      FStar_List.map
                                                        FStar_SMTEncoding_Util.mkFreeV
                                                        cvars1 in
                                                    ((cache_entry.cache_symbol_name),
                                                      uu____4089) in
                                                  FStar_SMTEncoding_Util.mkApp
                                                    uu____4085 in
                                                (uu____4084,
                                                  (use_cache_entry
                                                     cache_entry))
                                            | None  ->
                                                let uu____4095 =
                                                  is_an_eta_expansion env
                                                    vars body3 in
                                                (match uu____4095 with
                                                 | Some t1 ->
                                                     let decls1 =
                                                       let uu____4102 =
                                                         let uu____4103 =
                                                           FStar_Util.smap_size
                                                             env.cache in
                                                         uu____4103 =
                                                           cache_size in
                                                       if uu____4102
                                                       then []
                                                       else
                                                         FStar_List.append
                                                           decls decls' in
                                                     (t1, decls1)
                                                 | None  ->
                                                     let cvar_sorts =
                                                       FStar_List.map
                                                         Prims.snd cvars1 in
                                                     let fsym =
                                                       let module_name =
                                                         env.current_module_name in
                                                       let fsym =
                                                         let uu____4114 =
                                                           let uu____4115 =
                                                             FStar_Util.digest_of_string
                                                               tkey_hash in
                                                           Prims.strcat
                                                             "Tm_abs_"
                                                             uu____4115 in
                                                         varops.mk_unique
                                                           uu____4114 in
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
                                                       let uu____4120 =
                                                         let uu____4124 =
                                                           FStar_List.map
                                                             FStar_SMTEncoding_Util.mkFreeV
                                                             cvars1 in
                                                         (fsym, uu____4124) in
                                                       FStar_SMTEncoding_Util.mkApp
                                                         uu____4120 in
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
                                                           let uu____4136 =
                                                             let uu____4137 =
                                                               let uu____4141
                                                                 =
                                                                 FStar_SMTEncoding_Util.mkForall
                                                                   ([[f]],
                                                                    cvars1,
                                                                    f_has_t) in
                                                               (uu____4141,
                                                                 (Some a_name),
                                                                 a_name) in
                                                             FStar_SMTEncoding_Util.mkAssume
                                                               uu____4137 in
                                                           [uu____4136] in
                                                     let interp_f =
                                                       let a_name =
                                                         Prims.strcat
                                                           "interpretation_"
                                                           fsym in
                                                       let uu____4149 =
                                                         let uu____4153 =
                                                           let uu____4154 =
                                                             let uu____4160 =
                                                               FStar_SMTEncoding_Util.mkEq
                                                                 (app, body3) in
                                                             ([[app]],
                                                               (FStar_List.append
                                                                  vars cvars1),
                                                               uu____4160) in
                                                           FStar_SMTEncoding_Util.mkForall
                                                             uu____4154 in
                                                         (uu____4153,
                                                           (Some a_name),
                                                           a_name) in
                                                       FStar_SMTEncoding_Util.mkAssume
                                                         uu____4149 in
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
                                                     ((let uu____4170 =
                                                         mk_cache_entry env
                                                           fsym cvar_sorts
                                                           f_decls in
                                                       FStar_Util.smap_add
                                                         env.cache tkey_hash
                                                         uu____4170);
                                                      (f, f_decls))))))))))
       | FStar_Syntax_Syntax.Tm_let
           ((uu____4172,{
                          FStar_Syntax_Syntax.lbname = FStar_Util.Inr
                            uu____4173;
                          FStar_Syntax_Syntax.lbunivs = uu____4174;
                          FStar_Syntax_Syntax.lbtyp = uu____4175;
                          FStar_Syntax_Syntax.lbeff = uu____4176;
                          FStar_Syntax_Syntax.lbdef = uu____4177;_}::uu____4178),uu____4179)
           -> failwith "Impossible: already handled by encoding of Sig_let"
       | FStar_Syntax_Syntax.Tm_let
           ((false
             ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inl x;
                FStar_Syntax_Syntax.lbunivs = uu____4197;
                FStar_Syntax_Syntax.lbtyp = t1;
                FStar_Syntax_Syntax.lbeff = uu____4199;
                FStar_Syntax_Syntax.lbdef = e1;_}::[]),e2)
           -> encode_let x t1 e1 e2 env encode_term
       | FStar_Syntax_Syntax.Tm_let uu____4215 ->
           (FStar_Errors.diag t0.FStar_Syntax_Syntax.pos
              "Non-top-level recursive functions are not yet fully encoded to the SMT solver; you may not be able to prove some facts";
            (let e = varops.fresh "let-rec" in
             let decl_e =
               FStar_SMTEncoding_Term.DeclFun
                 (e, [], FStar_SMTEncoding_Term.Term_sort, None) in
             let uu____4228 =
               FStar_SMTEncoding_Util.mkFreeV
                 (e, FStar_SMTEncoding_Term.Term_sort) in
             (uu____4228, [decl_e])))
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
              let uu____4270 = encode_term e1 env in
              match uu____4270 with
              | (ee1,decls1) ->
                  let uu____4277 =
                    FStar_Syntax_Subst.open_term [(x, None)] e2 in
                  (match uu____4277 with
                   | (xs,e21) ->
                       let uu____4291 = FStar_List.hd xs in
                       (match uu____4291 with
                        | (x1,uu____4299) ->
                            let env' = push_term_var env x1 ee1 in
                            let uu____4301 = encode_body e21 env' in
                            (match uu____4301 with
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
            let uu____4323 =
              let uu____4327 =
                let uu____4328 =
                  (FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown)
                    None FStar_Range.dummyRange in
                FStar_Syntax_Syntax.null_bv uu____4328 in
              gen_term_var env uu____4327 in
            match uu____4323 with
            | (scrsym,scr',env1) ->
                let uu____4342 = encode_term e env1 in
                (match uu____4342 with
                 | (scr,decls) ->
                     let uu____4349 =
                       let encode_branch b uu____4365 =
                         match uu____4365 with
                         | (else_case,decls1) ->
                             let uu____4376 =
                               FStar_Syntax_Subst.open_branch b in
                             (match uu____4376 with
                              | (p,w,br) ->
                                  let patterns = encode_pat env1 p in
                                  FStar_List.fold_right
                                    (fun uu____4406  ->
                                       fun uu____4407  ->
                                         match (uu____4406, uu____4407) with
                                         | ((env0,pattern),(else_case1,decls2))
                                             ->
                                             let guard = pattern.guard scr' in
                                             let projections =
                                               pattern.projections scr' in
                                             let env2 =
                                               FStar_All.pipe_right
                                                 projections
                                                 (FStar_List.fold_left
                                                    (fun env2  ->
                                                       fun uu____4444  ->
                                                         match uu____4444
                                                         with
                                                         | (x,t) ->
                                                             push_term_var
                                                               env2 x t) env1) in
                                             let uu____4449 =
                                               match w with
                                               | None  -> (guard, [])
                                               | Some w1 ->
                                                   let uu____4464 =
                                                     encode_term w1 env2 in
                                                   (match uu____4464 with
                                                    | (w2,decls21) ->
                                                        let uu____4472 =
                                                          let uu____4473 =
                                                            let uu____4476 =
                                                              let uu____4477
                                                                =
                                                                let uu____4480
                                                                  =
                                                                  FStar_SMTEncoding_Term.boxBool
                                                                    FStar_SMTEncoding_Util.mkTrue in
                                                                (w2,
                                                                  uu____4480) in
                                                              FStar_SMTEncoding_Util.mkEq
                                                                uu____4477 in
                                                            (guard,
                                                              uu____4476) in
                                                          FStar_SMTEncoding_Util.mkAnd
                                                            uu____4473 in
                                                        (uu____4472, decls21)) in
                                             (match uu____4449 with
                                              | (guard1,decls21) ->
                                                  let uu____4488 =
                                                    encode_br br env2 in
                                                  (match uu____4488 with
                                                   | (br1,decls3) ->
                                                       let uu____4496 =
                                                         FStar_SMTEncoding_Util.mkITE
                                                           (guard1, br1,
                                                             else_case1) in
                                                       (uu____4496,
                                                         (FStar_List.append
                                                            decls2
                                                            (FStar_List.append
                                                               decls21 decls3))))))
                                    patterns (else_case, decls1)) in
                       FStar_List.fold_right encode_branch pats
                         (default_case, decls) in
                     (match uu____4349 with
                      | (match_tm,decls1) ->
                          let uu____4508 =
                            FStar_SMTEncoding_Term.mkLet'
                              ([((scrsym, FStar_SMTEncoding_Term.Term_sort),
                                  scr)], match_tm) FStar_Range.dummyRange in
                          (uu____4508, decls1)))
and encode_pat:
  env_t -> FStar_Syntax_Syntax.pat -> (env_t* pattern) Prims.list =
  fun env  ->
    fun pat  ->
      match pat.FStar_Syntax_Syntax.v with
      | FStar_Syntax_Syntax.Pat_disj ps ->
          FStar_List.map (encode_one_pat env) ps
      | uu____4539 -> let uu____4540 = encode_one_pat env pat in [uu____4540]
and encode_one_pat: env_t -> FStar_Syntax_Syntax.pat -> (env_t* pattern) =
  fun env  ->
    fun pat  ->
      (let uu____4552 =
         FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low in
       if uu____4552
       then
         let uu____4553 = FStar_Syntax_Print.pat_to_string pat in
         FStar_Util.print1 "Encoding pattern %s\n" uu____4553
       else ());
      (let uu____4555 = FStar_TypeChecker_Util.decorated_pattern_as_term pat in
       match uu____4555 with
       | (vars,pat_term) ->
           let uu____4565 =
             FStar_All.pipe_right vars
               (FStar_List.fold_left
                  (fun uu____4588  ->
                     fun v1  ->
                       match uu____4588 with
                       | (env1,vars1) ->
                           let uu____4616 = gen_term_var env1 v1 in
                           (match uu____4616 with
                            | (xx,uu____4628,env2) ->
                                (env2,
                                  ((v1,
                                     (xx, FStar_SMTEncoding_Term.Term_sort))
                                  :: vars1)))) (env, [])) in
           (match uu____4565 with
            | (env1,vars1) ->
                let rec mk_guard pat1 scrutinee =
                  match pat1.FStar_Syntax_Syntax.v with
                  | FStar_Syntax_Syntax.Pat_disj uu____4675 ->
                      failwith "Impossible"
                  | FStar_Syntax_Syntax.Pat_var _
                    |FStar_Syntax_Syntax.Pat_wild _
                     |FStar_Syntax_Syntax.Pat_dot_term _ ->
                      FStar_SMTEncoding_Util.mkTrue
                  | FStar_Syntax_Syntax.Pat_constant c ->
                      let uu____4683 =
                        let uu____4686 = encode_const c in
                        (scrutinee, uu____4686) in
                      FStar_SMTEncoding_Util.mkEq uu____4683
                  | FStar_Syntax_Syntax.Pat_cons (f,args) ->
                      let is_f =
                        let tc_name =
                          FStar_TypeChecker_Env.typ_of_datacon env1.tcenv
                            (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                        let uu____4705 =
                          FStar_TypeChecker_Env.datacons_of_typ env1.tcenv
                            tc_name in
                        match uu____4705 with
                        | (uu____4709,uu____4710::[]) ->
                            FStar_SMTEncoding_Util.mkTrue
                        | uu____4712 ->
                            mk_data_tester env1
                              (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                              scrutinee in
                      let sub_term_guards =
                        FStar_All.pipe_right args
                          (FStar_List.mapi
                             (fun i  ->
                                fun uu____4733  ->
                                  match uu____4733 with
                                  | (arg,uu____4739) ->
                                      let proj =
                                        primitive_projector_by_pos env1.tcenv
                                          (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                          i in
                                      let uu____4749 =
                                        FStar_SMTEncoding_Util.mkApp
                                          (proj, [scrutinee]) in
                                      mk_guard arg uu____4749)) in
                      FStar_SMTEncoding_Util.mk_and_l (is_f ::
                        sub_term_guards) in
                let rec mk_projections pat1 scrutinee =
                  match pat1.FStar_Syntax_Syntax.v with
                  | FStar_Syntax_Syntax.Pat_disj uu____4768 ->
                      failwith "Impossible"
                  | FStar_Syntax_Syntax.Pat_dot_term (x,_)
                    |FStar_Syntax_Syntax.Pat_var x
                     |FStar_Syntax_Syntax.Pat_wild x -> [(x, scrutinee)]
                  | FStar_Syntax_Syntax.Pat_constant uu____4783 -> []
                  | FStar_Syntax_Syntax.Pat_cons (f,args) ->
                      let uu____4798 =
                        FStar_All.pipe_right args
                          (FStar_List.mapi
                             (fun i  ->
                                fun uu____4820  ->
                                  match uu____4820 with
                                  | (arg,uu____4829) ->
                                      let proj =
                                        primitive_projector_by_pos env1.tcenv
                                          (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                          i in
                                      let uu____4839 =
                                        FStar_SMTEncoding_Util.mkApp
                                          (proj, [scrutinee]) in
                                      mk_projections arg uu____4839)) in
                      FStar_All.pipe_right uu____4798 FStar_List.flatten in
                let pat_term1 uu____4855 = encode_term pat_term env1 in
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
      let uu____4862 =
        FStar_All.pipe_right l
          (FStar_List.fold_left
             (fun uu____4877  ->
                fun uu____4878  ->
                  match (uu____4877, uu____4878) with
                  | ((tms,decls),(t,uu____4898)) ->
                      let uu____4909 = encode_term t env in
                      (match uu____4909 with
                       | (t1,decls') ->
                           ((t1 :: tms), (FStar_List.append decls decls'))))
             ([], [])) in
      match uu____4862 with | (l1,decls) -> ((FStar_List.rev l1), decls)
and encode_function_type_as_formula:
  FStar_SMTEncoding_Term.term Prims.option ->
    FStar_Syntax_Syntax.term Prims.option ->
      FStar_Syntax_Syntax.typ ->
        env_t ->
          (FStar_SMTEncoding_Term.term* FStar_SMTEncoding_Term.decls_t)
  =
  fun induction_on  ->
    fun new_pats  ->
      fun t  ->
        fun env  ->
          let list_elements1 e =
            let uu____4947 = FStar_Syntax_Util.list_elements e in
            match uu____4947 with
            | Some l -> l
            | None  ->
                (FStar_Errors.warn e.FStar_Syntax_Syntax.pos
                   "SMT pattern is not a list literal; ignoring the pattern";
                 []) in
          let one_pat p =
            let uu____4965 =
              let uu____4975 = FStar_Syntax_Util.unmeta p in
              FStar_All.pipe_right uu____4975 FStar_Syntax_Util.head_and_args in
            match uu____4965 with
            | (head1,args) ->
                let uu____5006 =
                  let uu____5014 =
                    let uu____5015 = FStar_Syntax_Util.un_uinst head1 in
                    uu____5015.FStar_Syntax_Syntax.n in
                  (uu____5014, args) in
                (match uu____5006 with
                 | (FStar_Syntax_Syntax.Tm_fvar
                    fv,(uu____5029,uu____5030)::(e,uu____5032)::[]) when
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Syntax_Const.smtpat_lid
                     -> (e, None)
                 | uu____5061 -> failwith "Unexpected pattern term") in
          let lemma_pats p =
            let elts = list_elements1 p in
            let smt_pat_or t1 =
              let uu____5094 =
                let uu____5104 = FStar_Syntax_Util.unmeta t1 in
                FStar_All.pipe_right uu____5104
                  FStar_Syntax_Util.head_and_args in
              match uu____5094 with
              | (head1,args) ->
                  let uu____5133 =
                    let uu____5141 =
                      let uu____5142 = FStar_Syntax_Util.un_uinst head1 in
                      uu____5142.FStar_Syntax_Syntax.n in
                    (uu____5141, args) in
                  (match uu____5133 with
                   | (FStar_Syntax_Syntax.Tm_fvar fv,(e,uu____5155)::[]) when
                       FStar_Syntax_Syntax.fv_eq_lid fv
                         FStar_Syntax_Const.smtpatOr_lid
                       -> Some e
                   | uu____5175 -> None) in
            match elts with
            | t1::[] ->
                let uu____5193 = smt_pat_or t1 in
                (match uu____5193 with
                 | Some e ->
                     let uu____5209 = list_elements1 e in
                     FStar_All.pipe_right uu____5209
                       (FStar_List.map
                          (fun branch1  ->
                             let uu____5226 = list_elements1 branch1 in
                             FStar_All.pipe_right uu____5226
                               (FStar_List.map one_pat)))
                 | uu____5240 ->
                     let uu____5244 =
                       FStar_All.pipe_right elts (FStar_List.map one_pat) in
                     [uu____5244])
            | uu____5275 ->
                let uu____5277 =
                  FStar_All.pipe_right elts (FStar_List.map one_pat) in
                [uu____5277] in
          let uu____5308 =
            let uu____5324 =
              let uu____5325 = FStar_Syntax_Subst.compress t in
              uu____5325.FStar_Syntax_Syntax.n in
            match uu____5324 with
            | FStar_Syntax_Syntax.Tm_arrow (binders,c) ->
                let uu____5355 = FStar_Syntax_Subst.open_comp binders c in
                (match uu____5355 with
                 | (binders1,c1) ->
                     (match c1.FStar_Syntax_Syntax.n with
                      | FStar_Syntax_Syntax.Comp
                          { FStar_Syntax_Syntax.comp_univs = uu____5390;
                            FStar_Syntax_Syntax.effect_name = uu____5391;
                            FStar_Syntax_Syntax.result_typ = uu____5392;
                            FStar_Syntax_Syntax.effect_args =
                              (pre,uu____5394)::(post,uu____5396)::(pats,uu____5398)::[];
                            FStar_Syntax_Syntax.flags = uu____5399;_}
                          ->
                          let pats' =
                            match new_pats with
                            | Some new_pats' -> new_pats'
                            | None  -> pats in
                          let uu____5433 = lemma_pats pats' in
                          (binders1, pre, post, uu____5433)
                      | uu____5452 -> failwith "impos"))
            | uu____5468 -> failwith "Impos" in
          match uu____5308 with
          | (binders,pre,post,patterns) ->
              let uu____5512 = encode_binders None binders env in
              (match uu____5512 with
               | (vars,guards,env1,decls,uu____5527) ->
                   let uu____5534 =
                     let uu____5541 =
                       FStar_All.pipe_right patterns
                         (FStar_List.map
                            (fun branch1  ->
                               let uu____5572 =
                                 let uu____5577 =
                                   FStar_All.pipe_right branch1
                                     (FStar_List.map
                                        (fun uu____5593  ->
                                           match uu____5593 with
                                           | (t1,uu____5600) ->
                                               encode_term t1
                                                 (let uu___140_5603 = env1 in
                                                  {
                                                    bindings =
                                                      (uu___140_5603.bindings);
                                                    depth =
                                                      (uu___140_5603.depth);
                                                    tcenv =
                                                      (uu___140_5603.tcenv);
                                                    warn =
                                                      (uu___140_5603.warn);
                                                    cache =
                                                      (uu___140_5603.cache);
                                                    nolabels =
                                                      (uu___140_5603.nolabels);
                                                    use_zfuel_name = true;
                                                    encode_non_total_function_typ
                                                      =
                                                      (uu___140_5603.encode_non_total_function_typ);
                                                    current_module_name =
                                                      (uu___140_5603.current_module_name)
                                                  }))) in
                                 FStar_All.pipe_right uu____5577
                                   FStar_List.unzip in
                               match uu____5572 with
                               | (pats,decls1) -> (pats, decls1))) in
                     FStar_All.pipe_right uu____5541 FStar_List.unzip in
                   (match uu____5534 with
                    | (pats,decls') ->
                        let decls'1 = FStar_List.flatten decls' in
                        let pats1 =
                          match induction_on with
                          | None  -> pats
                          | Some e ->
                              (match vars with
                               | [] -> pats
                               | l::[] ->
                                   FStar_All.pipe_right pats
                                     (FStar_List.map
                                        (fun p  ->
                                           let uu____5667 =
                                             let uu____5668 =
                                               FStar_SMTEncoding_Util.mkFreeV
                                                 l in
                                             FStar_SMTEncoding_Util.mk_Precedes
                                               uu____5668 e in
                                           uu____5667 :: p))
                               | uu____5669 ->
                                   let rec aux tl1 vars1 =
                                     match vars1 with
                                     | [] ->
                                         FStar_All.pipe_right pats
                                           (FStar_List.map
                                              (fun p  ->
                                                 let uu____5698 =
                                                   FStar_SMTEncoding_Util.mk_Precedes
                                                     tl1 e in
                                                 uu____5698 :: p))
                                     | (x,FStar_SMTEncoding_Term.Term_sort )::vars2
                                         ->
                                         let uu____5706 =
                                           let uu____5707 =
                                             FStar_SMTEncoding_Util.mkFreeV
                                               (x,
                                                 FStar_SMTEncoding_Term.Term_sort) in
                                           FStar_SMTEncoding_Util.mk_LexCons
                                             uu____5707 tl1 in
                                         aux uu____5706 vars2
                                     | uu____5708 -> pats in
                                   let uu____5712 =
                                     FStar_SMTEncoding_Util.mkFreeV
                                       ("Prims.LexTop",
                                         FStar_SMTEncoding_Term.Term_sort) in
                                   aux uu____5712 vars) in
                        let env2 =
                          let uu___141_5714 = env1 in
                          {
                            bindings = (uu___141_5714.bindings);
                            depth = (uu___141_5714.depth);
                            tcenv = (uu___141_5714.tcenv);
                            warn = (uu___141_5714.warn);
                            cache = (uu___141_5714.cache);
                            nolabels = true;
                            use_zfuel_name = (uu___141_5714.use_zfuel_name);
                            encode_non_total_function_typ =
                              (uu___141_5714.encode_non_total_function_typ);
                            current_module_name =
                              (uu___141_5714.current_module_name)
                          } in
                        let uu____5715 =
                          let uu____5718 = FStar_Syntax_Util.unmeta pre in
                          encode_formula uu____5718 env2 in
                        (match uu____5715 with
                         | (pre1,decls'') ->
                             let uu____5723 =
                               let uu____5726 = FStar_Syntax_Util.unmeta post in
                               encode_formula uu____5726 env2 in
                             (match uu____5723 with
                              | (post1,decls''') ->
                                  let decls1 =
                                    FStar_List.append decls
                                      (FStar_List.append
                                         (FStar_List.flatten decls'1)
                                         (FStar_List.append decls'' decls''')) in
                                  let uu____5733 =
                                    let uu____5734 =
                                      let uu____5740 =
                                        let uu____5741 =
                                          let uu____5744 =
                                            FStar_SMTEncoding_Util.mk_and_l
                                              (pre1 :: guards) in
                                          (uu____5744, post1) in
                                        FStar_SMTEncoding_Util.mkImp
                                          uu____5741 in
                                      (pats1, vars, uu____5740) in
                                    FStar_SMTEncoding_Util.mkForall
                                      uu____5734 in
                                  (uu____5733, decls1)))))
and encode_formula:
  FStar_Syntax_Syntax.typ ->
    env_t -> (FStar_SMTEncoding_Term.term* FStar_SMTEncoding_Term.decls_t)
  =
  fun phi  ->
    fun env  ->
      let debug1 phi1 =
        let uu____5757 =
          FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv)
            (FStar_Options.Other "SMTEncoding") in
        if uu____5757
        then
          let uu____5758 = FStar_Syntax_Print.tag_of_term phi1 in
          let uu____5759 = FStar_Syntax_Print.term_to_string phi1 in
          FStar_Util.print2 "Formula (%s)  %s\n" uu____5758 uu____5759
        else () in
      let enc f r l =
        let uu____5786 =
          FStar_Util.fold_map
            (fun decls  ->
               fun x  ->
                 let uu____5799 = encode_term (Prims.fst x) env in
                 match uu____5799 with
                 | (t,decls') -> ((FStar_List.append decls decls'), t)) [] l in
        match uu____5786 with
        | (decls,args) ->
            let uu____5816 =
              let uu___142_5817 = f args in
              {
                FStar_SMTEncoding_Term.tm =
                  (uu___142_5817.FStar_SMTEncoding_Term.tm);
                FStar_SMTEncoding_Term.freevars =
                  (uu___142_5817.FStar_SMTEncoding_Term.freevars);
                FStar_SMTEncoding_Term.rng = r
              } in
            (uu____5816, decls) in
      let const_op f r uu____5836 = let uu____5839 = f r in (uu____5839, []) in
      let un_op f l =
        let uu____5855 = FStar_List.hd l in FStar_All.pipe_left f uu____5855 in
      let bin_op f uu___114_5868 =
        match uu___114_5868 with
        | t1::t2::[] -> f (t1, t2)
        | uu____5876 -> failwith "Impossible" in
      let enc_prop_c f r l =
        let uu____5903 =
          FStar_Util.fold_map
            (fun decls  ->
               fun uu____5912  ->
                 match uu____5912 with
                 | (t,uu____5920) ->
                     let uu____5921 = encode_formula t env in
                     (match uu____5921 with
                      | (phi1,decls') ->
                          ((FStar_List.append decls decls'), phi1))) [] l in
        match uu____5903 with
        | (decls,phis) ->
            let uu____5938 =
              let uu___143_5939 = f phis in
              {
                FStar_SMTEncoding_Term.tm =
                  (uu___143_5939.FStar_SMTEncoding_Term.tm);
                FStar_SMTEncoding_Term.freevars =
                  (uu___143_5939.FStar_SMTEncoding_Term.freevars);
                FStar_SMTEncoding_Term.rng = r
              } in
            (uu____5938, decls) in
      let eq_op r uu___115_5955 =
        match uu___115_5955 with
        | _::e1::e2::[]|_::_::e1::e2::[] ->
            let uu____6015 = enc (bin_op FStar_SMTEncoding_Util.mkEq) in
            uu____6015 r [e1; e2]
        | l ->
            let uu____6035 = enc (bin_op FStar_SMTEncoding_Util.mkEq) in
            uu____6035 r l in
      let mk_imp1 r uu___116_6054 =
        match uu___116_6054 with
        | (lhs,uu____6058)::(rhs,uu____6060)::[] ->
            let uu____6081 = encode_formula rhs env in
            (match uu____6081 with
             | (l1,decls1) ->
                 (match l1.FStar_SMTEncoding_Term.tm with
                  | FStar_SMTEncoding_Term.App
                      (FStar_SMTEncoding_Term.TrueOp ,uu____6090) ->
                      (l1, decls1)
                  | uu____6093 ->
                      let uu____6094 = encode_formula lhs env in
                      (match uu____6094 with
                       | (l2,decls2) ->
                           let uu____6101 =
                             FStar_SMTEncoding_Term.mkImp (l2, l1) r in
                           (uu____6101, (FStar_List.append decls1 decls2)))))
        | uu____6103 -> failwith "impossible" in
      let mk_ite r uu___117_6118 =
        match uu___117_6118 with
        | (guard,uu____6122)::(_then,uu____6124)::(_else,uu____6126)::[] ->
            let uu____6155 = encode_formula guard env in
            (match uu____6155 with
             | (g,decls1) ->
                 let uu____6162 = encode_formula _then env in
                 (match uu____6162 with
                  | (t,decls2) ->
                      let uu____6169 = encode_formula _else env in
                      (match uu____6169 with
                       | (e,decls3) ->
                           let res = FStar_SMTEncoding_Term.mkITE (g, t, e) r in
                           (res,
                             (FStar_List.append decls1
                                (FStar_List.append decls2 decls3))))))
        | uu____6178 -> failwith "impossible" in
      let unboxInt_l f l =
        let uu____6197 = FStar_List.map FStar_SMTEncoding_Term.unboxInt l in
        f uu____6197 in
      let connectives =
        let uu____6209 =
          let uu____6218 = enc_prop_c (bin_op FStar_SMTEncoding_Util.mkAnd) in
          (FStar_Syntax_Const.and_lid, uu____6218) in
        let uu____6231 =
          let uu____6241 =
            let uu____6250 = enc_prop_c (bin_op FStar_SMTEncoding_Util.mkOr) in
            (FStar_Syntax_Const.or_lid, uu____6250) in
          let uu____6263 =
            let uu____6273 =
              let uu____6283 =
                let uu____6292 =
                  enc_prop_c (bin_op FStar_SMTEncoding_Util.mkIff) in
                (FStar_Syntax_Const.iff_lid, uu____6292) in
              let uu____6305 =
                let uu____6315 =
                  let uu____6325 =
                    let uu____6334 =
                      enc_prop_c (un_op FStar_SMTEncoding_Util.mkNot) in
                    (FStar_Syntax_Const.not_lid, uu____6334) in
                  [uu____6325;
                  (FStar_Syntax_Const.eq2_lid, eq_op);
                  (FStar_Syntax_Const.eq3_lid, eq_op);
                  (FStar_Syntax_Const.true_lid,
                    (const_op FStar_SMTEncoding_Term.mkTrue));
                  (FStar_Syntax_Const.false_lid,
                    (const_op FStar_SMTEncoding_Term.mkFalse))] in
                (FStar_Syntax_Const.ite_lid, mk_ite) :: uu____6315 in
              uu____6283 :: uu____6305 in
            (FStar_Syntax_Const.imp_lid, mk_imp1) :: uu____6273 in
          uu____6241 :: uu____6263 in
        uu____6209 :: uu____6231 in
      let rec fallback phi1 =
        match phi1.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_meta
            (phi',FStar_Syntax_Syntax.Meta_labeled (msg,r,b)) ->
            let uu____6496 = encode_formula phi' env in
            (match uu____6496 with
             | (phi2,decls) ->
                 let uu____6503 =
                   FStar_SMTEncoding_Term.mk
                     (FStar_SMTEncoding_Term.Labeled (phi2, msg, r)) r in
                 (uu____6503, decls))
        | FStar_Syntax_Syntax.Tm_meta uu____6504 ->
            let uu____6509 = FStar_Syntax_Util.unmeta phi1 in
            encode_formula uu____6509 env
        | FStar_Syntax_Syntax.Tm_match (e,pats) ->
            let uu____6538 =
              encode_match e pats FStar_SMTEncoding_Util.mkFalse env
                encode_formula in
            (match uu____6538 with | (t,decls) -> (t, decls))
        | FStar_Syntax_Syntax.Tm_let
            ((false
              ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inl x;
                 FStar_Syntax_Syntax.lbunivs = uu____6546;
                 FStar_Syntax_Syntax.lbtyp = t1;
                 FStar_Syntax_Syntax.lbeff = uu____6548;
                 FStar_Syntax_Syntax.lbdef = e1;_}::[]),e2)
            ->
            let uu____6564 = encode_let x t1 e1 e2 env encode_formula in
            (match uu____6564 with | (t,decls) -> (t, decls))
        | FStar_Syntax_Syntax.Tm_app (head1,args) ->
            let head2 = FStar_Syntax_Util.un_uinst head1 in
            (match ((head2.FStar_Syntax_Syntax.n), args) with
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,uu____6596::(x,uu____6598)::(t,uu____6600)::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Syntax_Const.has_type_lid
                 ->
                 let uu____6634 = encode_term x env in
                 (match uu____6634 with
                  | (x1,decls) ->
                      let uu____6641 = encode_term t env in
                      (match uu____6641 with
                       | (t1,decls') ->
                           let uu____6648 =
                             FStar_SMTEncoding_Term.mk_HasType x1 t1 in
                           (uu____6648, (FStar_List.append decls decls'))))
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(r,uu____6652)::(msg,uu____6654)::(phi2,uu____6656)::[])
                 when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Syntax_Const.labeled_lid
                 ->
                 let uu____6690 =
                   let uu____6693 =
                     let uu____6694 = FStar_Syntax_Subst.compress r in
                     uu____6694.FStar_Syntax_Syntax.n in
                   let uu____6697 =
                     let uu____6698 = FStar_Syntax_Subst.compress msg in
                     uu____6698.FStar_Syntax_Syntax.n in
                   (uu____6693, uu____6697) in
                 (match uu____6690 with
                  | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range
                     r1),FStar_Syntax_Syntax.Tm_constant
                     (FStar_Const.Const_string (s,uu____6705))) ->
                      let phi3 =
                        (FStar_Syntax_Syntax.mk
                           (FStar_Syntax_Syntax.Tm_meta
                              (phi2,
                                (FStar_Syntax_Syntax.Meta_labeled
                                   ((FStar_Util.string_of_unicode s), r1,
                                     false))))) None r1 in
                      fallback phi3
                  | uu____6721 -> fallback phi2)
             | uu____6724 when head_redex env head2 ->
                 let uu____6732 = whnf env phi1 in
                 encode_formula uu____6732 env
             | uu____6733 ->
                 let uu____6741 = encode_term phi1 env in
                 (match uu____6741 with
                  | (tt,decls) ->
                      let uu____6748 =
                        FStar_SMTEncoding_Term.mk_Valid
                          (let uu___144_6749 = tt in
                           {
                             FStar_SMTEncoding_Term.tm =
                               (uu___144_6749.FStar_SMTEncoding_Term.tm);
                             FStar_SMTEncoding_Term.freevars =
                               (uu___144_6749.FStar_SMTEncoding_Term.freevars);
                             FStar_SMTEncoding_Term.rng =
                               (phi1.FStar_Syntax_Syntax.pos)
                           }) in
                      (uu____6748, decls)))
        | uu____6752 ->
            let uu____6753 = encode_term phi1 env in
            (match uu____6753 with
             | (tt,decls) ->
                 let uu____6760 =
                   FStar_SMTEncoding_Term.mk_Valid
                     (let uu___145_6761 = tt in
                      {
                        FStar_SMTEncoding_Term.tm =
                          (uu___145_6761.FStar_SMTEncoding_Term.tm);
                        FStar_SMTEncoding_Term.freevars =
                          (uu___145_6761.FStar_SMTEncoding_Term.freevars);
                        FStar_SMTEncoding_Term.rng =
                          (phi1.FStar_Syntax_Syntax.pos)
                      }) in
                 (uu____6760, decls)) in
      let encode_q_body env1 bs ps body =
        let uu____6788 = encode_binders None bs env1 in
        match uu____6788 with
        | (vars,guards,env2,decls,uu____6810) ->
            let uu____6817 =
              let uu____6824 =
                FStar_All.pipe_right ps
                  (FStar_List.map
                     (fun p  ->
                        let uu____6847 =
                          let uu____6852 =
                            FStar_All.pipe_right p
                              (FStar_List.map
                                 (fun uu____6866  ->
                                    match uu____6866 with
                                    | (t,uu____6872) ->
                                        encode_term t
                                          (let uu___146_6873 = env2 in
                                           {
                                             bindings =
                                               (uu___146_6873.bindings);
                                             depth = (uu___146_6873.depth);
                                             tcenv = (uu___146_6873.tcenv);
                                             warn = (uu___146_6873.warn);
                                             cache = (uu___146_6873.cache);
                                             nolabels =
                                               (uu___146_6873.nolabels);
                                             use_zfuel_name = true;
                                             encode_non_total_function_typ =
                                               (uu___146_6873.encode_non_total_function_typ);
                                             current_module_name =
                                               (uu___146_6873.current_module_name)
                                           }))) in
                          FStar_All.pipe_right uu____6852 FStar_List.unzip in
                        match uu____6847 with
                        | (p1,decls1) -> (p1, (FStar_List.flatten decls1)))) in
              FStar_All.pipe_right uu____6824 FStar_List.unzip in
            (match uu____6817 with
             | (pats,decls') ->
                 let uu____6925 = encode_formula body env2 in
                 (match uu____6925 with
                  | (body1,decls'') ->
                      let guards1 =
                        match pats with
                        | ({
                             FStar_SMTEncoding_Term.tm =
                               FStar_SMTEncoding_Term.App
                               (FStar_SMTEncoding_Term.Var gf,p::[]);
                             FStar_SMTEncoding_Term.freevars = uu____6944;
                             FStar_SMTEncoding_Term.rng = uu____6945;_}::[])::[]
                            when
                            (FStar_Ident.text_of_lid
                               FStar_Syntax_Const.guard_free)
                              = gf
                            -> []
                        | uu____6953 -> guards in
                      let uu____6956 =
                        FStar_SMTEncoding_Util.mk_and_l guards1 in
                      (vars, pats, uu____6956, body1,
                        (FStar_List.append decls
                           (FStar_List.append (FStar_List.flatten decls')
                              decls''))))) in
      debug1 phi;
      (let phi1 = FStar_Syntax_Util.unascribe phi in
       let check_pattern_vars vars pats =
         let pats1 =
           FStar_All.pipe_right pats
             (FStar_List.map
                (fun uu____6990  ->
                   match uu____6990 with
                   | (x,uu____6994) ->
                       FStar_TypeChecker_Normalize.normalize
                         [FStar_TypeChecker_Normalize.Beta;
                         FStar_TypeChecker_Normalize.AllowUnboundUniverses;
                         FStar_TypeChecker_Normalize.EraseUniverses]
                         env.tcenv x)) in
         match pats1 with
         | [] -> ()
         | hd1::tl1 ->
             let pat_vars =
               let uu____7000 = FStar_Syntax_Free.names hd1 in
               FStar_List.fold_left
                 (fun out  ->
                    fun x  ->
                      let uu____7006 = FStar_Syntax_Free.names x in
                      FStar_Util.set_union out uu____7006) uu____7000 tl1 in
             let uu____7008 =
               FStar_All.pipe_right vars
                 (FStar_Util.find_opt
                    (fun uu____7020  ->
                       match uu____7020 with
                       | (b,uu____7024) ->
                           let uu____7025 = FStar_Util.set_mem b pat_vars in
                           Prims.op_Negation uu____7025)) in
             (match uu____7008 with
              | None  -> ()
              | Some (x,uu____7029) ->
                  let pos =
                    FStar_List.fold_left
                      (fun out  ->
                         fun t  ->
                           FStar_Range.union_ranges out
                             t.FStar_Syntax_Syntax.pos)
                      hd1.FStar_Syntax_Syntax.pos tl1 in
                  let uu____7039 =
                    let uu____7040 = FStar_Syntax_Print.bv_to_string x in
                    FStar_Util.format1
                      "SMT pattern misses at least one bound variable: %s"
                      uu____7040 in
                  FStar_Errors.warn pos uu____7039) in
       let uu____7041 = FStar_Syntax_Util.destruct_typ_as_formula phi1 in
       match uu____7041 with
       | None  -> fallback phi1
       | Some (FStar_Syntax_Util.BaseConn (op,arms)) ->
           let uu____7047 =
             FStar_All.pipe_right connectives
               (FStar_List.tryFind
                  (fun uu____7083  ->
                     match uu____7083 with
                     | (l,uu____7093) -> FStar_Ident.lid_equals op l)) in
           (match uu____7047 with
            | None  -> fallback phi1
            | Some (uu____7116,f) -> f phi1.FStar_Syntax_Syntax.pos arms)
       | Some (FStar_Syntax_Util.QAll (vars,pats,body)) ->
           (FStar_All.pipe_right pats
              (FStar_List.iter (check_pattern_vars vars));
            (let uu____7145 = encode_q_body env vars pats body in
             match uu____7145 with
             | (vars1,pats1,guard,body1,decls) ->
                 let tm =
                   let uu____7171 =
                     let uu____7177 =
                       FStar_SMTEncoding_Util.mkImp (guard, body1) in
                     (pats1, vars1, uu____7177) in
                   FStar_SMTEncoding_Term.mkForall uu____7171
                     phi1.FStar_Syntax_Syntax.pos in
                 (tm, decls)))
       | Some (FStar_Syntax_Util.QEx (vars,pats,body)) ->
           (FStar_All.pipe_right pats
              (FStar_List.iter (check_pattern_vars vars));
            (let uu____7189 = encode_q_body env vars pats body in
             match uu____7189 with
             | (vars1,pats1,guard,body1,decls) ->
                 let uu____7214 =
                   let uu____7215 =
                     let uu____7221 =
                       FStar_SMTEncoding_Util.mkAnd (guard, body1) in
                     (pats1, vars1, uu____7221) in
                   FStar_SMTEncoding_Term.mkExists uu____7215
                     phi1.FStar_Syntax_Syntax.pos in
                 (uu____7214, decls))))
type prims_t =
  {
  mk:
    FStar_Ident.lident ->
      Prims.string ->
        (FStar_SMTEncoding_Term.term* FStar_SMTEncoding_Term.decl Prims.list);
  is: FStar_Ident.lident -> Prims.bool;}
let prims: prims_t =
  let uu____7270 = fresh_fvar "a" FStar_SMTEncoding_Term.Term_sort in
  match uu____7270 with
  | (asym,a) ->
      let uu____7275 = fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort in
      (match uu____7275 with
       | (xsym,x) ->
           let uu____7280 = fresh_fvar "y" FStar_SMTEncoding_Term.Term_sort in
           (match uu____7280 with
            | (ysym,y) ->
                let quant vars body x1 =
                  let xname_decl =
                    let uu____7310 =
                      let uu____7316 =
                        FStar_All.pipe_right vars (FStar_List.map Prims.snd) in
                      (x1, uu____7316, FStar_SMTEncoding_Term.Term_sort,
                        None) in
                    FStar_SMTEncoding_Term.DeclFun uu____7310 in
                  let xtok = Prims.strcat x1 "@tok" in
                  let xtok_decl =
                    FStar_SMTEncoding_Term.DeclFun
                      (xtok, [], FStar_SMTEncoding_Term.Term_sort, None) in
                  let xapp =
                    let uu____7331 =
                      let uu____7335 =
                        FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars in
                      (x1, uu____7335) in
                    FStar_SMTEncoding_Util.mkApp uu____7331 in
                  let xtok1 = FStar_SMTEncoding_Util.mkApp (xtok, []) in
                  let xtok_app = mk_Apply xtok1 vars in
                  let uu____7343 =
                    let uu____7345 =
                      let uu____7347 =
                        let uu____7349 =
                          let uu____7350 =
                            let uu____7354 =
                              let uu____7355 =
                                let uu____7361 =
                                  FStar_SMTEncoding_Util.mkEq (xapp, body) in
                                ([[xapp]], vars, uu____7361) in
                              FStar_SMTEncoding_Util.mkForall uu____7355 in
                            (uu____7354, None,
                              (Prims.strcat "primitive_" x1)) in
                          FStar_SMTEncoding_Util.mkAssume uu____7350 in
                        let uu____7370 =
                          let uu____7372 =
                            let uu____7373 =
                              let uu____7377 =
                                let uu____7378 =
                                  let uu____7384 =
                                    FStar_SMTEncoding_Util.mkEq
                                      (xtok_app, xapp) in
                                  ([[xtok_app]], vars, uu____7384) in
                                FStar_SMTEncoding_Util.mkForall uu____7378 in
                              (uu____7377,
                                (Some "Name-token correspondence"),
                                (Prims.strcat "token_correspondence_" x1)) in
                            FStar_SMTEncoding_Util.mkAssume uu____7373 in
                          [uu____7372] in
                        uu____7349 :: uu____7370 in
                      xtok_decl :: uu____7347 in
                    xname_decl :: uu____7345 in
                  (xtok1, uu____7343) in
                let axy =
                  [(asym, FStar_SMTEncoding_Term.Term_sort);
                  (xsym, FStar_SMTEncoding_Term.Term_sort);
                  (ysym, FStar_SMTEncoding_Term.Term_sort)] in
                let xy =
                  [(xsym, FStar_SMTEncoding_Term.Term_sort);
                  (ysym, FStar_SMTEncoding_Term.Term_sort)] in
                let qx = [(xsym, FStar_SMTEncoding_Term.Term_sort)] in
                let prims1 =
                  let uu____7433 =
                    let uu____7441 =
                      let uu____7447 =
                        let uu____7448 = FStar_SMTEncoding_Util.mkEq (x, y) in
                        FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool
                          uu____7448 in
                      quant axy uu____7447 in
                    (FStar_Syntax_Const.op_Eq, uu____7441) in
                  let uu____7454 =
                    let uu____7463 =
                      let uu____7471 =
                        let uu____7477 =
                          let uu____7478 =
                            let uu____7479 =
                              FStar_SMTEncoding_Util.mkEq (x, y) in
                            FStar_SMTEncoding_Util.mkNot uu____7479 in
                          FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool
                            uu____7478 in
                        quant axy uu____7477 in
                      (FStar_Syntax_Const.op_notEq, uu____7471) in
                    let uu____7485 =
                      let uu____7494 =
                        let uu____7502 =
                          let uu____7508 =
                            let uu____7509 =
                              let uu____7510 =
                                let uu____7513 =
                                  FStar_SMTEncoding_Term.unboxInt x in
                                let uu____7514 =
                                  FStar_SMTEncoding_Term.unboxInt y in
                                (uu____7513, uu____7514) in
                              FStar_SMTEncoding_Util.mkLT uu____7510 in
                            FStar_All.pipe_left
                              FStar_SMTEncoding_Term.boxBool uu____7509 in
                          quant xy uu____7508 in
                        (FStar_Syntax_Const.op_LT, uu____7502) in
                      let uu____7520 =
                        let uu____7529 =
                          let uu____7537 =
                            let uu____7543 =
                              let uu____7544 =
                                let uu____7545 =
                                  let uu____7548 =
                                    FStar_SMTEncoding_Term.unboxInt x in
                                  let uu____7549 =
                                    FStar_SMTEncoding_Term.unboxInt y in
                                  (uu____7548, uu____7549) in
                                FStar_SMTEncoding_Util.mkLTE uu____7545 in
                              FStar_All.pipe_left
                                FStar_SMTEncoding_Term.boxBool uu____7544 in
                            quant xy uu____7543 in
                          (FStar_Syntax_Const.op_LTE, uu____7537) in
                        let uu____7555 =
                          let uu____7564 =
                            let uu____7572 =
                              let uu____7578 =
                                let uu____7579 =
                                  let uu____7580 =
                                    let uu____7583 =
                                      FStar_SMTEncoding_Term.unboxInt x in
                                    let uu____7584 =
                                      FStar_SMTEncoding_Term.unboxInt y in
                                    (uu____7583, uu____7584) in
                                  FStar_SMTEncoding_Util.mkGT uu____7580 in
                                FStar_All.pipe_left
                                  FStar_SMTEncoding_Term.boxBool uu____7579 in
                              quant xy uu____7578 in
                            (FStar_Syntax_Const.op_GT, uu____7572) in
                          let uu____7590 =
                            let uu____7599 =
                              let uu____7607 =
                                let uu____7613 =
                                  let uu____7614 =
                                    let uu____7615 =
                                      let uu____7618 =
                                        FStar_SMTEncoding_Term.unboxInt x in
                                      let uu____7619 =
                                        FStar_SMTEncoding_Term.unboxInt y in
                                      (uu____7618, uu____7619) in
                                    FStar_SMTEncoding_Util.mkGTE uu____7615 in
                                  FStar_All.pipe_left
                                    FStar_SMTEncoding_Term.boxBool uu____7614 in
                                quant xy uu____7613 in
                              (FStar_Syntax_Const.op_GTE, uu____7607) in
                            let uu____7625 =
                              let uu____7634 =
                                let uu____7642 =
                                  let uu____7648 =
                                    let uu____7649 =
                                      let uu____7650 =
                                        let uu____7653 =
                                          FStar_SMTEncoding_Term.unboxInt x in
                                        let uu____7654 =
                                          FStar_SMTEncoding_Term.unboxInt y in
                                        (uu____7653, uu____7654) in
                                      FStar_SMTEncoding_Util.mkSub uu____7650 in
                                    FStar_All.pipe_left
                                      FStar_SMTEncoding_Term.boxInt
                                      uu____7649 in
                                  quant xy uu____7648 in
                                (FStar_Syntax_Const.op_Subtraction,
                                  uu____7642) in
                              let uu____7660 =
                                let uu____7669 =
                                  let uu____7677 =
                                    let uu____7683 =
                                      let uu____7684 =
                                        let uu____7685 =
                                          FStar_SMTEncoding_Term.unboxInt x in
                                        FStar_SMTEncoding_Util.mkMinus
                                          uu____7685 in
                                      FStar_All.pipe_left
                                        FStar_SMTEncoding_Term.boxInt
                                        uu____7684 in
                                    quant qx uu____7683 in
                                  (FStar_Syntax_Const.op_Minus, uu____7677) in
                                let uu____7691 =
                                  let uu____7700 =
                                    let uu____7708 =
                                      let uu____7714 =
                                        let uu____7715 =
                                          let uu____7716 =
                                            let uu____7719 =
                                              FStar_SMTEncoding_Term.unboxInt
                                                x in
                                            let uu____7720 =
                                              FStar_SMTEncoding_Term.unboxInt
                                                y in
                                            (uu____7719, uu____7720) in
                                          FStar_SMTEncoding_Util.mkAdd
                                            uu____7716 in
                                        FStar_All.pipe_left
                                          FStar_SMTEncoding_Term.boxInt
                                          uu____7715 in
                                      quant xy uu____7714 in
                                    (FStar_Syntax_Const.op_Addition,
                                      uu____7708) in
                                  let uu____7726 =
                                    let uu____7735 =
                                      let uu____7743 =
                                        let uu____7749 =
                                          let uu____7750 =
                                            let uu____7751 =
                                              let uu____7754 =
                                                FStar_SMTEncoding_Term.unboxInt
                                                  x in
                                              let uu____7755 =
                                                FStar_SMTEncoding_Term.unboxInt
                                                  y in
                                              (uu____7754, uu____7755) in
                                            FStar_SMTEncoding_Util.mkMul
                                              uu____7751 in
                                          FStar_All.pipe_left
                                            FStar_SMTEncoding_Term.boxInt
                                            uu____7750 in
                                        quant xy uu____7749 in
                                      (FStar_Syntax_Const.op_Multiply,
                                        uu____7743) in
                                    let uu____7761 =
                                      let uu____7770 =
                                        let uu____7778 =
                                          let uu____7784 =
                                            let uu____7785 =
                                              let uu____7786 =
                                                let uu____7789 =
                                                  FStar_SMTEncoding_Term.unboxInt
                                                    x in
                                                let uu____7790 =
                                                  FStar_SMTEncoding_Term.unboxInt
                                                    y in
                                                (uu____7789, uu____7790) in
                                              FStar_SMTEncoding_Util.mkDiv
                                                uu____7786 in
                                            FStar_All.pipe_left
                                              FStar_SMTEncoding_Term.boxInt
                                              uu____7785 in
                                          quant xy uu____7784 in
                                        (FStar_Syntax_Const.op_Division,
                                          uu____7778) in
                                      let uu____7796 =
                                        let uu____7805 =
                                          let uu____7813 =
                                            let uu____7819 =
                                              let uu____7820 =
                                                let uu____7821 =
                                                  let uu____7824 =
                                                    FStar_SMTEncoding_Term.unboxInt
                                                      x in
                                                  let uu____7825 =
                                                    FStar_SMTEncoding_Term.unboxInt
                                                      y in
                                                  (uu____7824, uu____7825) in
                                                FStar_SMTEncoding_Util.mkMod
                                                  uu____7821 in
                                              FStar_All.pipe_left
                                                FStar_SMTEncoding_Term.boxInt
                                                uu____7820 in
                                            quant xy uu____7819 in
                                          (FStar_Syntax_Const.op_Modulus,
                                            uu____7813) in
                                        let uu____7831 =
                                          let uu____7840 =
                                            let uu____7848 =
                                              let uu____7854 =
                                                let uu____7855 =
                                                  let uu____7856 =
                                                    let uu____7859 =
                                                      FStar_SMTEncoding_Term.unboxBool
                                                        x in
                                                    let uu____7860 =
                                                      FStar_SMTEncoding_Term.unboxBool
                                                        y in
                                                    (uu____7859, uu____7860) in
                                                  FStar_SMTEncoding_Util.mkAnd
                                                    uu____7856 in
                                                FStar_All.pipe_left
                                                  FStar_SMTEncoding_Term.boxBool
                                                  uu____7855 in
                                              quant xy uu____7854 in
                                            (FStar_Syntax_Const.op_And,
                                              uu____7848) in
                                          let uu____7866 =
                                            let uu____7875 =
                                              let uu____7883 =
                                                let uu____7889 =
                                                  let uu____7890 =
                                                    let uu____7891 =
                                                      let uu____7894 =
                                                        FStar_SMTEncoding_Term.unboxBool
                                                          x in
                                                      let uu____7895 =
                                                        FStar_SMTEncoding_Term.unboxBool
                                                          y in
                                                      (uu____7894,
                                                        uu____7895) in
                                                    FStar_SMTEncoding_Util.mkOr
                                                      uu____7891 in
                                                  FStar_All.pipe_left
                                                    FStar_SMTEncoding_Term.boxBool
                                                    uu____7890 in
                                                quant xy uu____7889 in
                                              (FStar_Syntax_Const.op_Or,
                                                uu____7883) in
                                            let uu____7901 =
                                              let uu____7910 =
                                                let uu____7918 =
                                                  let uu____7924 =
                                                    let uu____7925 =
                                                      let uu____7926 =
                                                        FStar_SMTEncoding_Term.unboxBool
                                                          x in
                                                      FStar_SMTEncoding_Util.mkNot
                                                        uu____7926 in
                                                    FStar_All.pipe_left
                                                      FStar_SMTEncoding_Term.boxBool
                                                      uu____7925 in
                                                  quant qx uu____7924 in
                                                (FStar_Syntax_Const.op_Negation,
                                                  uu____7918) in
                                              [uu____7910] in
                                            uu____7875 :: uu____7901 in
                                          uu____7840 :: uu____7866 in
                                        uu____7805 :: uu____7831 in
                                      uu____7770 :: uu____7796 in
                                    uu____7735 :: uu____7761 in
                                  uu____7700 :: uu____7726 in
                                uu____7669 :: uu____7691 in
                              uu____7634 :: uu____7660 in
                            uu____7599 :: uu____7625 in
                          uu____7564 :: uu____7590 in
                        uu____7529 :: uu____7555 in
                      uu____7494 :: uu____7520 in
                    uu____7463 :: uu____7485 in
                  uu____7433 :: uu____7454 in
                let mk1 l v1 =
                  let uu____8054 =
                    let uu____8059 =
                      FStar_All.pipe_right prims1
                        (FStar_List.find
                           (fun uu____8091  ->
                              match uu____8091 with
                              | (l',uu____8100) ->
                                  FStar_Ident.lid_equals l l')) in
                    FStar_All.pipe_right uu____8059
                      (FStar_Option.map
                         (fun uu____8133  ->
                            match uu____8133 with | (uu____8144,b) -> b v1)) in
                  FStar_All.pipe_right uu____8054 FStar_Option.get in
                let is l =
                  FStar_All.pipe_right prims1
                    (FStar_Util.for_some
                       (fun uu____8185  ->
                          match uu____8185 with
                          | (l',uu____8194) -> FStar_Ident.lid_equals l l')) in
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
        let uu____8220 = fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort in
        match uu____8220 with
        | (xxsym,xx) ->
            let uu____8225 = fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort in
            (match uu____8225 with
             | (ffsym,ff) ->
                 let xx_has_type =
                   FStar_SMTEncoding_Term.mk_HasTypeFuel ff xx tapp in
                 let tapp_hash = FStar_SMTEncoding_Term.hash_of_term tapp in
                 let module_name = env.current_module_name in
                 let uu____8233 =
                   let uu____8237 =
                     let uu____8238 =
                       let uu____8244 =
                         let uu____8245 =
                           let uu____8248 =
                             let uu____8249 =
                               let uu____8252 =
                                 FStar_SMTEncoding_Util.mkApp
                                   ("PreType", [xx]) in
                               (tapp, uu____8252) in
                             FStar_SMTEncoding_Util.mkEq uu____8249 in
                           (xx_has_type, uu____8248) in
                         FStar_SMTEncoding_Util.mkImp uu____8245 in
                       ([[xx_has_type]],
                         ((xxsym, FStar_SMTEncoding_Term.Term_sort) ::
                         (ffsym, FStar_SMTEncoding_Term.Fuel_sort) :: vars),
                         uu____8244) in
                     FStar_SMTEncoding_Util.mkForall uu____8238 in
                   let uu____8265 =
                     let uu____8266 =
                       let uu____8267 =
                         let uu____8268 =
                           FStar_Util.digest_of_string tapp_hash in
                         Prims.strcat "_pretyping_" uu____8268 in
                       Prims.strcat module_name uu____8267 in
                     varops.mk_unique uu____8266 in
                   (uu____8237, (Some "pretyping"), uu____8265) in
                 FStar_SMTEncoding_Util.mkAssume uu____8233)
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
    let uu____8298 =
      let uu____8299 =
        let uu____8303 =
          FStar_SMTEncoding_Term.mk_HasType
            FStar_SMTEncoding_Term.mk_Term_unit tt in
        (uu____8303, (Some "unit typing"), "unit_typing") in
      FStar_SMTEncoding_Util.mkAssume uu____8299 in
    let uu____8305 =
      let uu____8307 =
        let uu____8308 =
          let uu____8312 =
            let uu____8313 =
              let uu____8319 =
                let uu____8320 =
                  let uu____8323 =
                    FStar_SMTEncoding_Util.mkEq
                      (x, FStar_SMTEncoding_Term.mk_Term_unit) in
                  (typing_pred, uu____8323) in
                FStar_SMTEncoding_Util.mkImp uu____8320 in
              ([[typing_pred]], [xx], uu____8319) in
            mkForall_fuel uu____8313 in
          (uu____8312, (Some "unit inversion"), "unit_inversion") in
        FStar_SMTEncoding_Util.mkAssume uu____8308 in
      [uu____8307] in
    uu____8298 :: uu____8305 in
  let mk_bool env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt in
    let bb = ("b", FStar_SMTEncoding_Term.Bool_sort) in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let uu____8351 =
      let uu____8352 =
        let uu____8356 =
          let uu____8357 =
            let uu____8363 =
              let uu____8366 =
                let uu____8368 = FStar_SMTEncoding_Term.boxBool b in
                [uu____8368] in
              [uu____8366] in
            let uu____8371 =
              let uu____8372 = FStar_SMTEncoding_Term.boxBool b in
              FStar_SMTEncoding_Term.mk_HasType uu____8372 tt in
            (uu____8363, [bb], uu____8371) in
          FStar_SMTEncoding_Util.mkForall uu____8357 in
        (uu____8356, (Some "bool typing"), "bool_typing") in
      FStar_SMTEncoding_Util.mkAssume uu____8352 in
    let uu____8383 =
      let uu____8385 =
        let uu____8386 =
          let uu____8390 =
            let uu____8391 =
              let uu____8397 =
                let uu____8398 =
                  let uu____8401 =
                    FStar_SMTEncoding_Term.mk_tester "BoxBool" x in
                  (typing_pred, uu____8401) in
                FStar_SMTEncoding_Util.mkImp uu____8398 in
              ([[typing_pred]], [xx], uu____8397) in
            mkForall_fuel uu____8391 in
          (uu____8390, (Some "bool inversion"), "bool_inversion") in
        FStar_SMTEncoding_Util.mkAssume uu____8386 in
      [uu____8385] in
    uu____8351 :: uu____8383 in
  let mk_int env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt in
    let typing_pred_y = FStar_SMTEncoding_Term.mk_HasType y tt in
    let aa = ("a", FStar_SMTEncoding_Term.Int_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let bb = ("b", FStar_SMTEncoding_Term.Int_sort) in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let precedes =
      let uu____8435 =
        let uu____8436 =
          let uu____8440 =
            let uu____8442 =
              let uu____8444 =
                let uu____8446 = FStar_SMTEncoding_Term.boxInt a in
                let uu____8447 =
                  let uu____8449 = FStar_SMTEncoding_Term.boxInt b in
                  [uu____8449] in
                uu____8446 :: uu____8447 in
              tt :: uu____8444 in
            tt :: uu____8442 in
          ("Prims.Precedes", uu____8440) in
        FStar_SMTEncoding_Util.mkApp uu____8436 in
      FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid uu____8435 in
    let precedes_y_x =
      let uu____8452 = FStar_SMTEncoding_Util.mkApp ("Precedes", [y; x]) in
      FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid uu____8452 in
    let uu____8454 =
      let uu____8455 =
        let uu____8459 =
          let uu____8460 =
            let uu____8466 =
              let uu____8469 =
                let uu____8471 = FStar_SMTEncoding_Term.boxInt b in
                [uu____8471] in
              [uu____8469] in
            let uu____8474 =
              let uu____8475 = FStar_SMTEncoding_Term.boxInt b in
              FStar_SMTEncoding_Term.mk_HasType uu____8475 tt in
            (uu____8466, [bb], uu____8474) in
          FStar_SMTEncoding_Util.mkForall uu____8460 in
        (uu____8459, (Some "int typing"), "int_typing") in
      FStar_SMTEncoding_Util.mkAssume uu____8455 in
    let uu____8486 =
      let uu____8488 =
        let uu____8489 =
          let uu____8493 =
            let uu____8494 =
              let uu____8500 =
                let uu____8501 =
                  let uu____8504 =
                    FStar_SMTEncoding_Term.mk_tester "BoxInt" x in
                  (typing_pred, uu____8504) in
                FStar_SMTEncoding_Util.mkImp uu____8501 in
              ([[typing_pred]], [xx], uu____8500) in
            mkForall_fuel uu____8494 in
          (uu____8493, (Some "int inversion"), "int_inversion") in
        FStar_SMTEncoding_Util.mkAssume uu____8489 in
      let uu____8517 =
        let uu____8519 =
          let uu____8520 =
            let uu____8524 =
              let uu____8525 =
                let uu____8531 =
                  let uu____8532 =
                    let uu____8535 =
                      let uu____8536 =
                        let uu____8538 =
                          let uu____8540 =
                            let uu____8542 =
                              let uu____8543 =
                                let uu____8546 =
                                  FStar_SMTEncoding_Term.unboxInt x in
                                let uu____8547 =
                                  FStar_SMTEncoding_Util.mkInteger'
                                    (Prims.parse_int "0") in
                                (uu____8546, uu____8547) in
                              FStar_SMTEncoding_Util.mkGT uu____8543 in
                            let uu____8548 =
                              let uu____8550 =
                                let uu____8551 =
                                  let uu____8554 =
                                    FStar_SMTEncoding_Term.unboxInt y in
                                  let uu____8555 =
                                    FStar_SMTEncoding_Util.mkInteger'
                                      (Prims.parse_int "0") in
                                  (uu____8554, uu____8555) in
                                FStar_SMTEncoding_Util.mkGTE uu____8551 in
                              let uu____8556 =
                                let uu____8558 =
                                  let uu____8559 =
                                    let uu____8562 =
                                      FStar_SMTEncoding_Term.unboxInt y in
                                    let uu____8563 =
                                      FStar_SMTEncoding_Term.unboxInt x in
                                    (uu____8562, uu____8563) in
                                  FStar_SMTEncoding_Util.mkLT uu____8559 in
                                [uu____8558] in
                              uu____8550 :: uu____8556 in
                            uu____8542 :: uu____8548 in
                          typing_pred_y :: uu____8540 in
                        typing_pred :: uu____8538 in
                      FStar_SMTEncoding_Util.mk_and_l uu____8536 in
                    (uu____8535, precedes_y_x) in
                  FStar_SMTEncoding_Util.mkImp uu____8532 in
                ([[typing_pred; typing_pred_y; precedes_y_x]], [xx; yy],
                  uu____8531) in
              mkForall_fuel uu____8525 in
            (uu____8524, (Some "well-founded ordering on nat (alt)"),
              "well-founded-ordering-on-nat") in
          FStar_SMTEncoding_Util.mkAssume uu____8520 in
        [uu____8519] in
      uu____8488 :: uu____8517 in
    uu____8454 :: uu____8486 in
  let mk_str env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt in
    let bb = ("b", FStar_SMTEncoding_Term.String_sort) in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let uu____8593 =
      let uu____8594 =
        let uu____8598 =
          let uu____8599 =
            let uu____8605 =
              let uu____8608 =
                let uu____8610 = FStar_SMTEncoding_Term.boxString b in
                [uu____8610] in
              [uu____8608] in
            let uu____8613 =
              let uu____8614 = FStar_SMTEncoding_Term.boxString b in
              FStar_SMTEncoding_Term.mk_HasType uu____8614 tt in
            (uu____8605, [bb], uu____8613) in
          FStar_SMTEncoding_Util.mkForall uu____8599 in
        (uu____8598, (Some "string typing"), "string_typing") in
      FStar_SMTEncoding_Util.mkAssume uu____8594 in
    let uu____8625 =
      let uu____8627 =
        let uu____8628 =
          let uu____8632 =
            let uu____8633 =
              let uu____8639 =
                let uu____8640 =
                  let uu____8643 =
                    FStar_SMTEncoding_Term.mk_tester "BoxString" x in
                  (typing_pred, uu____8643) in
                FStar_SMTEncoding_Util.mkImp uu____8640 in
              ([[typing_pred]], [xx], uu____8639) in
            mkForall_fuel uu____8633 in
          (uu____8632, (Some "string inversion"), "string_inversion") in
        FStar_SMTEncoding_Util.mkAssume uu____8628 in
      [uu____8627] in
    uu____8593 :: uu____8625 in
  let mk_ref1 env reft_name uu____8665 =
    let r = ("r", FStar_SMTEncoding_Term.Ref_sort) in
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let refa =
      let uu____8676 =
        let uu____8680 =
          let uu____8682 = FStar_SMTEncoding_Util.mkFreeV aa in [uu____8682] in
        (reft_name, uu____8680) in
      FStar_SMTEncoding_Util.mkApp uu____8676 in
    let refb =
      let uu____8685 =
        let uu____8689 =
          let uu____8691 = FStar_SMTEncoding_Util.mkFreeV bb in [uu____8691] in
        (reft_name, uu____8689) in
      FStar_SMTEncoding_Util.mkApp uu____8685 in
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x refa in
    let typing_pred_b = FStar_SMTEncoding_Term.mk_HasType x refb in
    let uu____8695 =
      let uu____8696 =
        let uu____8700 =
          let uu____8701 =
            let uu____8707 =
              let uu____8708 =
                let uu____8711 = FStar_SMTEncoding_Term.mk_tester "BoxRef" x in
                (typing_pred, uu____8711) in
              FStar_SMTEncoding_Util.mkImp uu____8708 in
            ([[typing_pred]], [xx; aa], uu____8707) in
          mkForall_fuel uu____8701 in
        (uu____8700, (Some "ref inversion"), "ref_inversion") in
      FStar_SMTEncoding_Util.mkAssume uu____8696 in
    [uu____8695] in
  let mk_true_interp env nm true_tm =
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [true_tm]) in
    [FStar_SMTEncoding_Util.mkAssume
       (valid, (Some "True interpretation"), "true_interp")] in
  let mk_false_interp env nm false_tm =
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [false_tm]) in
    let uu____8751 =
      let uu____8752 =
        let uu____8756 =
          FStar_SMTEncoding_Util.mkIff
            (FStar_SMTEncoding_Util.mkFalse, valid) in
        (uu____8756, (Some "False interpretation"), "false_interp") in
      FStar_SMTEncoding_Util.mkAssume uu____8752 in
    [uu____8751] in
  let mk_and_interp env conj uu____8767 =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let l_and_a_b = FStar_SMTEncoding_Util.mkApp (conj, [a; b]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_and_a_b]) in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b]) in
    let uu____8784 =
      let uu____8785 =
        let uu____8789 =
          let uu____8790 =
            let uu____8796 =
              let uu____8797 =
                let uu____8800 =
                  FStar_SMTEncoding_Util.mkAnd (valid_a, valid_b) in
                (uu____8800, valid) in
              FStar_SMTEncoding_Util.mkIff uu____8797 in
            ([[l_and_a_b]], [aa; bb], uu____8796) in
          FStar_SMTEncoding_Util.mkForall uu____8790 in
        (uu____8789, (Some "/\\ interpretation"), "l_and-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____8785 in
    [uu____8784] in
  let mk_or_interp env disj uu____8824 =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let l_or_a_b = FStar_SMTEncoding_Util.mkApp (disj, [a; b]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_or_a_b]) in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b]) in
    let uu____8841 =
      let uu____8842 =
        let uu____8846 =
          let uu____8847 =
            let uu____8853 =
              let uu____8854 =
                let uu____8857 =
                  FStar_SMTEncoding_Util.mkOr (valid_a, valid_b) in
                (uu____8857, valid) in
              FStar_SMTEncoding_Util.mkIff uu____8854 in
            ([[l_or_a_b]], [aa; bb], uu____8853) in
          FStar_SMTEncoding_Util.mkForall uu____8847 in
        (uu____8846, (Some "\\/ interpretation"), "l_or-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____8842 in
    [uu____8841] in
  let mk_eq2_interp env eq2 tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let xx1 = ("x", FStar_SMTEncoding_Term.Term_sort) in
    let yy1 = ("y", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let x1 = FStar_SMTEncoding_Util.mkFreeV xx1 in
    let y1 = FStar_SMTEncoding_Util.mkFreeV yy1 in
    let eq2_x_y = FStar_SMTEncoding_Util.mkApp (eq2, [a; x1; y1]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [eq2_x_y]) in
    let uu____8898 =
      let uu____8899 =
        let uu____8903 =
          let uu____8904 =
            let uu____8910 =
              let uu____8911 =
                let uu____8914 = FStar_SMTEncoding_Util.mkEq (x1, y1) in
                (uu____8914, valid) in
              FStar_SMTEncoding_Util.mkIff uu____8911 in
            ([[eq2_x_y]], [aa; xx1; yy1], uu____8910) in
          FStar_SMTEncoding_Util.mkForall uu____8904 in
        (uu____8903, (Some "Eq2 interpretation"), "eq2-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____8899 in
    [uu____8898] in
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
    let uu____8961 =
      let uu____8962 =
        let uu____8966 =
          let uu____8967 =
            let uu____8973 =
              let uu____8974 =
                let uu____8977 = FStar_SMTEncoding_Util.mkEq (x1, y1) in
                (uu____8977, valid) in
              FStar_SMTEncoding_Util.mkIff uu____8974 in
            ([[eq3_x_y]], [aa; bb; xx1; yy1], uu____8973) in
          FStar_SMTEncoding_Util.mkForall uu____8967 in
        (uu____8966, (Some "Eq3 interpretation"), "eq3-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____8962 in
    [uu____8961] in
  let mk_imp_interp env imp tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let l_imp_a_b = FStar_SMTEncoding_Util.mkApp (imp, [a; b]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_imp_a_b]) in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b]) in
    let uu____9022 =
      let uu____9023 =
        let uu____9027 =
          let uu____9028 =
            let uu____9034 =
              let uu____9035 =
                let uu____9038 =
                  FStar_SMTEncoding_Util.mkImp (valid_a, valid_b) in
                (uu____9038, valid) in
              FStar_SMTEncoding_Util.mkIff uu____9035 in
            ([[l_imp_a_b]], [aa; bb], uu____9034) in
          FStar_SMTEncoding_Util.mkForall uu____9028 in
        (uu____9027, (Some "==> interpretation"), "l_imp-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____9023 in
    [uu____9022] in
  let mk_iff_interp env iff tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let l_iff_a_b = FStar_SMTEncoding_Util.mkApp (iff, [a; b]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_iff_a_b]) in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b]) in
    let uu____9079 =
      let uu____9080 =
        let uu____9084 =
          let uu____9085 =
            let uu____9091 =
              let uu____9092 =
                let uu____9095 =
                  FStar_SMTEncoding_Util.mkIff (valid_a, valid_b) in
                (uu____9095, valid) in
              FStar_SMTEncoding_Util.mkIff uu____9092 in
            ([[l_iff_a_b]], [aa; bb], uu____9091) in
          FStar_SMTEncoding_Util.mkForall uu____9085 in
        (uu____9084, (Some "<==> interpretation"), "l_iff-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____9080 in
    [uu____9079] in
  let mk_not_interp env l_not tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let l_not_a = FStar_SMTEncoding_Util.mkApp (l_not, [a]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_not_a]) in
    let not_valid_a =
      let uu____9129 = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
      FStar_All.pipe_left FStar_SMTEncoding_Util.mkNot uu____9129 in
    let uu____9131 =
      let uu____9132 =
        let uu____9136 =
          let uu____9137 =
            let uu____9143 =
              FStar_SMTEncoding_Util.mkIff (not_valid_a, valid) in
            ([[l_not_a]], [aa], uu____9143) in
          FStar_SMTEncoding_Util.mkForall uu____9137 in
        (uu____9136, (Some "not interpretation"), "l_not-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____9132 in
    [uu____9131] in
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
      let uu____9183 =
        let uu____9187 =
          let uu____9189 = FStar_SMTEncoding_Util.mk_ApplyTT b x1 in
          [uu____9189] in
        ("Valid", uu____9187) in
      FStar_SMTEncoding_Util.mkApp uu____9183 in
    let uu____9191 =
      let uu____9192 =
        let uu____9196 =
          let uu____9197 =
            let uu____9203 =
              let uu____9204 =
                let uu____9207 =
                  let uu____9208 =
                    let uu____9214 =
                      let uu____9217 =
                        let uu____9219 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a in
                        [uu____9219] in
                      [uu____9217] in
                    let uu____9222 =
                      let uu____9223 =
                        let uu____9226 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a in
                        (uu____9226, valid_b_x) in
                      FStar_SMTEncoding_Util.mkImp uu____9223 in
                    (uu____9214, [xx1], uu____9222) in
                  FStar_SMTEncoding_Util.mkForall uu____9208 in
                (uu____9207, valid) in
              FStar_SMTEncoding_Util.mkIff uu____9204 in
            ([[l_forall_a_b]], [aa; bb], uu____9203) in
          FStar_SMTEncoding_Util.mkForall uu____9197 in
        (uu____9196, (Some "forall interpretation"), "forall-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____9192 in
    [uu____9191] in
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
      let uu____9277 =
        let uu____9281 =
          let uu____9283 = FStar_SMTEncoding_Util.mk_ApplyTT b x1 in
          [uu____9283] in
        ("Valid", uu____9281) in
      FStar_SMTEncoding_Util.mkApp uu____9277 in
    let uu____9285 =
      let uu____9286 =
        let uu____9290 =
          let uu____9291 =
            let uu____9297 =
              let uu____9298 =
                let uu____9301 =
                  let uu____9302 =
                    let uu____9308 =
                      let uu____9311 =
                        let uu____9313 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a in
                        [uu____9313] in
                      [uu____9311] in
                    let uu____9316 =
                      let uu____9317 =
                        let uu____9320 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a in
                        (uu____9320, valid_b_x) in
                      FStar_SMTEncoding_Util.mkImp uu____9317 in
                    (uu____9308, [xx1], uu____9316) in
                  FStar_SMTEncoding_Util.mkExists uu____9302 in
                (uu____9301, valid) in
              FStar_SMTEncoding_Util.mkIff uu____9298 in
            ([[l_exists_a_b]], [aa; bb], uu____9297) in
          FStar_SMTEncoding_Util.mkForall uu____9291 in
        (uu____9290, (Some "exists interpretation"), "exists-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____9286 in
    [uu____9285] in
  let mk_range_interp env range tt =
    let range_ty = FStar_SMTEncoding_Util.mkApp (range, []) in
    let uu____9356 =
      let uu____9357 =
        let uu____9361 =
          FStar_SMTEncoding_Term.mk_HasTypeZ
            FStar_SMTEncoding_Term.mk_Range_const range_ty in
        let uu____9362 = varops.mk_unique "typing_range_const" in
        (uu____9361, (Some "Range_const typing"), uu____9362) in
      FStar_SMTEncoding_Util.mkAssume uu____9357 in
    [uu____9356] in
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
          let uu____9624 =
            FStar_Util.find_opt
              (fun uu____9642  ->
                 match uu____9642 with
                 | (l,uu____9652) -> FStar_Ident.lid_equals l t) prims1 in
          match uu____9624 with
          | None  -> []
          | Some (uu____9674,f) -> f env s tt
let encode_smt_lemma:
  env_t ->
    FStar_Syntax_Syntax.fv ->
      FStar_Syntax_Syntax.typ -> FStar_SMTEncoding_Term.decl Prims.list
  =
  fun env  ->
    fun fv  ->
      fun t  ->
        let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
        let uu____9711 = encode_function_type_as_formula None None t env in
        match uu____9711 with
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
            let uu____9743 =
              (let uu____9744 =
                 (FStar_Syntax_Util.is_pure_or_ghost_function t_norm) ||
                   (FStar_TypeChecker_Env.is_reifiable_function env.tcenv
                      t_norm) in
               FStar_All.pipe_left Prims.op_Negation uu____9744) ||
                (FStar_Syntax_Util.is_lemma t_norm) in
            if uu____9743
            then
              let uu____9748 = new_term_constant_and_tok_from_lid env lid in
              match uu____9748 with
              | (vname,vtok,env1) ->
                  let arg_sorts =
                    let uu____9760 =
                      let uu____9761 = FStar_Syntax_Subst.compress t_norm in
                      uu____9761.FStar_Syntax_Syntax.n in
                    match uu____9760 with
                    | FStar_Syntax_Syntax.Tm_arrow (binders,uu____9766) ->
                        FStar_All.pipe_right binders
                          (FStar_List.map
                             (fun uu____9783  ->
                                FStar_SMTEncoding_Term.Term_sort))
                    | uu____9786 -> [] in
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
              (let uu____9795 = prims.is lid in
               if uu____9795
               then
                 let vname = varops.new_fvar lid in
                 let uu____9800 = prims.mk lid vname in
                 match uu____9800 with
                 | (tok,definition) ->
                     let env1 = push_free_var env lid vname (Some tok) in
                     (definition, env1)
               else
                 (let encode_non_total_function_typ =
                    lid.FStar_Ident.nsstr <> "Prims" in
                  let uu____9815 =
                    let uu____9821 = curried_arrow_formals_comp t_norm in
                    match uu____9821 with
                    | (args,comp) ->
                        let comp1 =
                          let uu____9832 =
                            FStar_TypeChecker_Env.is_reifiable_comp env.tcenv
                              comp in
                          if uu____9832
                          then
                            let uu____9833 =
                              FStar_TypeChecker_Env.reify_comp
                                (let uu___147_9834 = env.tcenv in
                                 {
                                   FStar_TypeChecker_Env.solver =
                                     (uu___147_9834.FStar_TypeChecker_Env.solver);
                                   FStar_TypeChecker_Env.range =
                                     (uu___147_9834.FStar_TypeChecker_Env.range);
                                   FStar_TypeChecker_Env.curmodule =
                                     (uu___147_9834.FStar_TypeChecker_Env.curmodule);
                                   FStar_TypeChecker_Env.gamma =
                                     (uu___147_9834.FStar_TypeChecker_Env.gamma);
                                   FStar_TypeChecker_Env.gamma_cache =
                                     (uu___147_9834.FStar_TypeChecker_Env.gamma_cache);
                                   FStar_TypeChecker_Env.modules =
                                     (uu___147_9834.FStar_TypeChecker_Env.modules);
                                   FStar_TypeChecker_Env.expected_typ =
                                     (uu___147_9834.FStar_TypeChecker_Env.expected_typ);
                                   FStar_TypeChecker_Env.sigtab =
                                     (uu___147_9834.FStar_TypeChecker_Env.sigtab);
                                   FStar_TypeChecker_Env.is_pattern =
                                     (uu___147_9834.FStar_TypeChecker_Env.is_pattern);
                                   FStar_TypeChecker_Env.instantiate_imp =
                                     (uu___147_9834.FStar_TypeChecker_Env.instantiate_imp);
                                   FStar_TypeChecker_Env.effects =
                                     (uu___147_9834.FStar_TypeChecker_Env.effects);
                                   FStar_TypeChecker_Env.generalize =
                                     (uu___147_9834.FStar_TypeChecker_Env.generalize);
                                   FStar_TypeChecker_Env.letrecs =
                                     (uu___147_9834.FStar_TypeChecker_Env.letrecs);
                                   FStar_TypeChecker_Env.top_level =
                                     (uu___147_9834.FStar_TypeChecker_Env.top_level);
                                   FStar_TypeChecker_Env.check_uvars =
                                     (uu___147_9834.FStar_TypeChecker_Env.check_uvars);
                                   FStar_TypeChecker_Env.use_eq =
                                     (uu___147_9834.FStar_TypeChecker_Env.use_eq);
                                   FStar_TypeChecker_Env.is_iface =
                                     (uu___147_9834.FStar_TypeChecker_Env.is_iface);
                                   FStar_TypeChecker_Env.admit =
                                     (uu___147_9834.FStar_TypeChecker_Env.admit);
                                   FStar_TypeChecker_Env.lax = true;
                                   FStar_TypeChecker_Env.lax_universes =
                                     (uu___147_9834.FStar_TypeChecker_Env.lax_universes);
                                   FStar_TypeChecker_Env.type_of =
                                     (uu___147_9834.FStar_TypeChecker_Env.type_of);
                                   FStar_TypeChecker_Env.universe_of =
                                     (uu___147_9834.FStar_TypeChecker_Env.universe_of);
                                   FStar_TypeChecker_Env.use_bv_sorts =
                                     (uu___147_9834.FStar_TypeChecker_Env.use_bv_sorts);
                                   FStar_TypeChecker_Env.qname_and_index =
                                     (uu___147_9834.FStar_TypeChecker_Env.qname_and_index)
                                 }) comp FStar_Syntax_Syntax.U_unknown in
                            FStar_Syntax_Syntax.mk_Total uu____9833
                          else comp in
                        if encode_non_total_function_typ
                        then
                          let uu____9841 =
                            FStar_TypeChecker_Util.pure_or_ghost_pre_and_post
                              env.tcenv comp1 in
                          (args, uu____9841)
                        else
                          (args,
                            (None, (FStar_Syntax_Util.comp_result comp1))) in
                  match uu____9815 with
                  | (formals,(pre_opt,res_t)) ->
                      let uu____9868 =
                        new_term_constant_and_tok_from_lid env lid in
                      (match uu____9868 with
                       | (vname,vtok,env1) ->
                           let vtok_tm =
                             match formals with
                             | [] ->
                                 FStar_SMTEncoding_Util.mkFreeV
                                   (vname, FStar_SMTEncoding_Term.Term_sort)
                             | uu____9881 ->
                                 FStar_SMTEncoding_Util.mkApp (vtok, []) in
                           let mk_disc_proj_axioms guard encoded_res_t vapp
                             vars =
                             FStar_All.pipe_right quals
                               (FStar_List.collect
                                  (fun uu___118_9905  ->
                                     match uu___118_9905 with
                                     | FStar_Syntax_Syntax.Discriminator d ->
                                         let uu____9908 =
                                           FStar_Util.prefix vars in
                                         (match uu____9908 with
                                          | (uu____9919,(xxsym,uu____9921))
                                              ->
                                              let xx =
                                                FStar_SMTEncoding_Util.mkFreeV
                                                  (xxsym,
                                                    FStar_SMTEncoding_Term.Term_sort) in
                                              let uu____9931 =
                                                let uu____9932 =
                                                  let uu____9936 =
                                                    let uu____9937 =
                                                      let uu____9943 =
                                                        let uu____9944 =
                                                          let uu____9947 =
                                                            let uu____9948 =
                                                              FStar_SMTEncoding_Term.mk_tester
                                                                (escape
                                                                   d.FStar_Ident.str)
                                                                xx in
                                                            FStar_All.pipe_left
                                                              FStar_SMTEncoding_Term.boxBool
                                                              uu____9948 in
                                                          (vapp, uu____9947) in
                                                        FStar_SMTEncoding_Util.mkEq
                                                          uu____9944 in
                                                      ([[vapp]], vars,
                                                        uu____9943) in
                                                    FStar_SMTEncoding_Util.mkForall
                                                      uu____9937 in
                                                  (uu____9936,
                                                    (Some
                                                       "Discriminator equation"),
                                                    (Prims.strcat
                                                       "disc_equation_"
                                                       (escape
                                                          d.FStar_Ident.str))) in
                                                FStar_SMTEncoding_Util.mkAssume
                                                  uu____9932 in
                                              [uu____9931])
                                     | FStar_Syntax_Syntax.Projector 
                                         (d,f) ->
                                         let uu____9959 =
                                           FStar_Util.prefix vars in
                                         (match uu____9959 with
                                          | (uu____9970,(xxsym,uu____9972))
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
                                              let uu____9986 =
                                                let uu____9987 =
                                                  let uu____9991 =
                                                    let uu____9992 =
                                                      let uu____9998 =
                                                        FStar_SMTEncoding_Util.mkEq
                                                          (vapp, prim_app) in
                                                      ([[vapp]], vars,
                                                        uu____9998) in
                                                    FStar_SMTEncoding_Util.mkForall
                                                      uu____9992 in
                                                  (uu____9991,
                                                    (Some
                                                       "Projector equation"),
                                                    (Prims.strcat
                                                       "proj_equation_"
                                                       tp_name)) in
                                                FStar_SMTEncoding_Util.mkAssume
                                                  uu____9987 in
                                              [uu____9986])
                                     | uu____10007 -> [])) in
                           let uu____10008 = encode_binders None formals env1 in
                           (match uu____10008 with
                            | (vars,guards,env',decls1,uu____10024) ->
                                let uu____10031 =
                                  match pre_opt with
                                  | None  ->
                                      let uu____10036 =
                                        FStar_SMTEncoding_Util.mk_and_l
                                          guards in
                                      (uu____10036, decls1)
                                  | Some p ->
                                      let uu____10038 = encode_formula p env' in
                                      (match uu____10038 with
                                       | (g,ds) ->
                                           let uu____10045 =
                                             FStar_SMTEncoding_Util.mk_and_l
                                               (g :: guards) in
                                           (uu____10045,
                                             (FStar_List.append decls1 ds))) in
                                (match uu____10031 with
                                 | (guard,decls11) ->
                                     let vtok_app = mk_Apply vtok_tm vars in
                                     let vapp =
                                       let uu____10054 =
                                         let uu____10058 =
                                           FStar_List.map
                                             FStar_SMTEncoding_Util.mkFreeV
                                             vars in
                                         (vname, uu____10058) in
                                       FStar_SMTEncoding_Util.mkApp
                                         uu____10054 in
                                     let uu____10063 =
                                       let vname_decl =
                                         let uu____10068 =
                                           let uu____10074 =
                                             FStar_All.pipe_right formals
                                               (FStar_List.map
                                                  (fun uu____10079  ->
                                                     FStar_SMTEncoding_Term.Term_sort)) in
                                           (vname, uu____10074,
                                             FStar_SMTEncoding_Term.Term_sort,
                                             None) in
                                         FStar_SMTEncoding_Term.DeclFun
                                           uu____10068 in
                                       let uu____10084 =
                                         let env2 =
                                           let uu___148_10088 = env1 in
                                           {
                                             bindings =
                                               (uu___148_10088.bindings);
                                             depth = (uu___148_10088.depth);
                                             tcenv = (uu___148_10088.tcenv);
                                             warn = (uu___148_10088.warn);
                                             cache = (uu___148_10088.cache);
                                             nolabels =
                                               (uu___148_10088.nolabels);
                                             use_zfuel_name =
                                               (uu___148_10088.use_zfuel_name);
                                             encode_non_total_function_typ;
                                             current_module_name =
                                               (uu___148_10088.current_module_name)
                                           } in
                                         let uu____10089 =
                                           let uu____10090 =
                                             head_normal env2 tt in
                                           Prims.op_Negation uu____10090 in
                                         if uu____10089
                                         then
                                           encode_term_pred None tt env2
                                             vtok_tm
                                         else
                                           encode_term_pred None t_norm env2
                                             vtok_tm in
                                       match uu____10084 with
                                       | (tok_typing,decls2) ->
                                           let tok_typing1 =
                                             match formals with
                                             | uu____10100::uu____10101 ->
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
                                                   let uu____10124 =
                                                     let uu____10130 =
                                                       FStar_SMTEncoding_Term.mk_NoHoist
                                                         f tok_typing in
                                                     ([[vtok_app_l];
                                                      [vtok_app_r]], 
                                                       [ff], uu____10130) in
                                                   FStar_SMTEncoding_Util.mkForall
                                                     uu____10124 in
                                                 FStar_SMTEncoding_Util.mkAssume
                                                   (guarded_tok_typing,
                                                     (Some
                                                        "function token typing"),
                                                     (Prims.strcat
                                                        "function_token_typing_"
                                                        vname))
                                             | uu____10144 ->
                                                 FStar_SMTEncoding_Util.mkAssume
                                                   (tok_typing,
                                                     (Some
                                                        "function token typing"),
                                                     (Prims.strcat
                                                        "function_token_typing_"
                                                        vname)) in
                                           let uu____10146 =
                                             match formals with
                                             | [] ->
                                                 let uu____10155 =
                                                   let uu____10156 =
                                                     let uu____10158 =
                                                       FStar_SMTEncoding_Util.mkFreeV
                                                         (vname,
                                                           FStar_SMTEncoding_Term.Term_sort) in
                                                     FStar_All.pipe_left
                                                       (fun _0_34  ->
                                                          Some _0_34)
                                                       uu____10158 in
                                                   push_free_var env1 lid
                                                     vname uu____10156 in
                                                 ((FStar_List.append decls2
                                                     [tok_typing1]),
                                                   uu____10155)
                                             | uu____10161 ->
                                                 let vtok_decl =
                                                   FStar_SMTEncoding_Term.DeclFun
                                                     (vtok, [],
                                                       FStar_SMTEncoding_Term.Term_sort,
                                                       None) in
                                                 let vtok_fresh =
                                                   let uu____10166 =
                                                     varops.next_id () in
                                                   FStar_SMTEncoding_Term.fresh_token
                                                     (vtok,
                                                       FStar_SMTEncoding_Term.Term_sort)
                                                     uu____10166 in
                                                 let name_tok_corr =
                                                   let uu____10168 =
                                                     let uu____10172 =
                                                       let uu____10173 =
                                                         let uu____10179 =
                                                           FStar_SMTEncoding_Util.mkEq
                                                             (vtok_app, vapp) in
                                                         ([[vtok_app];
                                                          [vapp]], vars,
                                                           uu____10179) in
                                                       FStar_SMTEncoding_Util.mkForall
                                                         uu____10173 in
                                                     (uu____10172,
                                                       (Some
                                                          "Name-token correspondence"),
                                                       (Prims.strcat
                                                          "token_correspondence_"
                                                          vname)) in
                                                   FStar_SMTEncoding_Util.mkAssume
                                                     uu____10168 in
                                                 ((FStar_List.append decls2
                                                     [vtok_decl;
                                                     vtok_fresh;
                                                     name_tok_corr;
                                                     tok_typing1]), env1) in
                                           (match uu____10146 with
                                            | (tok_decl,env2) ->
                                                ((vname_decl :: tok_decl),
                                                  env2)) in
                                     (match uu____10063 with
                                      | (decls2,env2) ->
                                          let uu____10203 =
                                            let res_t1 =
                                              FStar_Syntax_Subst.compress
                                                res_t in
                                            let uu____10208 =
                                              encode_term res_t1 env' in
                                            match uu____10208 with
                                            | (encoded_res_t,decls) ->
                                                let uu____10216 =
                                                  FStar_SMTEncoding_Term.mk_HasType
                                                    vapp encoded_res_t in
                                                (encoded_res_t, uu____10216,
                                                  decls) in
                                          (match uu____10203 with
                                           | (encoded_res_t,ty_pred,decls3)
                                               ->
                                               let typingAx =
                                                 let uu____10224 =
                                                   let uu____10228 =
                                                     let uu____10229 =
                                                       let uu____10235 =
                                                         FStar_SMTEncoding_Util.mkImp
                                                           (guard, ty_pred) in
                                                       ([[vapp]], vars,
                                                         uu____10235) in
                                                     FStar_SMTEncoding_Util.mkForall
                                                       uu____10229 in
                                                   (uu____10228,
                                                     (Some "free var typing"),
                                                     (Prims.strcat "typing_"
                                                        vname)) in
                                                 FStar_SMTEncoding_Util.mkAssume
                                                   uu____10224 in
                                               let freshness =
                                                 let uu____10244 =
                                                   FStar_All.pipe_right quals
                                                     (FStar_List.contains
                                                        FStar_Syntax_Syntax.New) in
                                                 if uu____10244
                                                 then
                                                   let uu____10247 =
                                                     let uu____10248 =
                                                       let uu____10254 =
                                                         FStar_All.pipe_right
                                                           vars
                                                           (FStar_List.map
                                                              Prims.snd) in
                                                       let uu____10260 =
                                                         varops.next_id () in
                                                       (vname, uu____10254,
                                                         FStar_SMTEncoding_Term.Term_sort,
                                                         uu____10260) in
                                                     FStar_SMTEncoding_Term.fresh_constructor
                                                       uu____10248 in
                                                   let uu____10262 =
                                                     let uu____10264 =
                                                       pretype_axiom env2
                                                         vapp vars in
                                                     [uu____10264] in
                                                   uu____10247 :: uu____10262
                                                 else [] in
                                               let g =
                                                 let uu____10268 =
                                                   let uu____10270 =
                                                     let uu____10272 =
                                                       let uu____10274 =
                                                         let uu____10276 =
                                                           mk_disc_proj_axioms
                                                             guard
                                                             encoded_res_t
                                                             vapp vars in
                                                         typingAx ::
                                                           uu____10276 in
                                                       FStar_List.append
                                                         freshness
                                                         uu____10274 in
                                                     FStar_List.append decls3
                                                       uu____10272 in
                                                   FStar_List.append decls2
                                                     uu____10270 in
                                                 FStar_List.append decls11
                                                   uu____10268 in
                                               (g, env2))))))))
let declare_top_level_let:
  env_t ->
    FStar_Syntax_Syntax.fv ->
      FStar_Syntax_Syntax.term ->
        FStar_Syntax_Syntax.term ->
          ((Prims.string* FStar_SMTEncoding_Term.term Prims.option)*
            FStar_SMTEncoding_Term.decl Prims.list* env_t)
  =
  fun env  ->
    fun x  ->
      fun t  ->
        fun t_norm  ->
          let uu____10298 =
            try_lookup_lid env
              (x.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          match uu____10298 with
          | None  ->
              let uu____10321 = encode_free_var env x t t_norm [] in
              (match uu____10321 with
               | (decls,env1) ->
                   let uu____10336 =
                     lookup_lid env1
                       (x.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                   (match uu____10336 with
                    | (n1,x',uu____10355) -> ((n1, x'), decls, env1)))
          | Some (n1,x1,uu____10367) -> ((n1, x1), [], env)
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
          let uu____10400 = encode_free_var env lid t tt quals in
          match uu____10400 with
          | (decls,env1) ->
              let uu____10411 = FStar_Syntax_Util.is_smt_lemma t in
              if uu____10411
              then
                let uu____10415 =
                  let uu____10417 = encode_smt_lemma env1 lid tt in
                  FStar_List.append decls uu____10417 in
                (uu____10415, env1)
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
             (fun uu____10445  ->
                fun lb  ->
                  match uu____10445 with
                  | (decls,env1) ->
                      let uu____10457 =
                        let uu____10461 =
                          FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
                        encode_top_level_val env1 uu____10461
                          lb.FStar_Syntax_Syntax.lbtyp quals in
                      (match uu____10457 with
                       | (decls',env2) ->
                           ((FStar_List.append decls decls'), env2)))
             ([], env))
let is_tactic: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let fstar_tactics_tactic_lid =
      FStar_Syntax_Const.p2l ["FStar"; "Tactics"; "tactic"] in
    let uu____10475 = FStar_Syntax_Util.head_and_args t in
    match uu____10475 with
    | (hd1,args) ->
        let uu____10501 =
          let uu____10502 = FStar_Syntax_Util.un_uinst hd1 in
          uu____10502.FStar_Syntax_Syntax.n in
        (match uu____10501 with
         | FStar_Syntax_Syntax.Tm_fvar fv when
             FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_tactic_lid ->
             true
         | FStar_Syntax_Syntax.Tm_arrow (uu____10506,c) ->
             let effect_name = FStar_Syntax_Util.comp_effect_name c in
             FStar_Util.starts_with "FStar.Tactics"
               effect_name.FStar_Ident.str
         | uu____10519 -> false)
let encode_top_level_let:
  env_t ->
    (Prims.bool* FStar_Syntax_Syntax.letbinding Prims.list) ->
      FStar_Syntax_Syntax.qualifier Prims.list ->
        (FStar_SMTEncoding_Term.decl Prims.list* env_t)
  =
  fun env  ->
    fun uu____10534  ->
      fun quals  ->
        match uu____10534 with
        | (is_rec,bindings) ->
            let eta_expand1 binders formals body t =
              let nbinders = FStar_List.length binders in
              let uu____10583 = FStar_Util.first_N nbinders formals in
              match uu____10583 with
              | (formals1,extra_formals) ->
                  let subst1 =
                    FStar_List.map2
                      (fun uu____10623  ->
                         fun uu____10624  ->
                           match (uu____10623, uu____10624) with
                           | ((formal,uu____10634),(binder,uu____10636)) ->
                               let uu____10641 =
                                 let uu____10646 =
                                   FStar_Syntax_Syntax.bv_to_name binder in
                                 (formal, uu____10646) in
                               FStar_Syntax_Syntax.NT uu____10641) formals1
                      binders in
                  let extra_formals1 =
                    let uu____10651 =
                      FStar_All.pipe_right extra_formals
                        (FStar_List.map
                           (fun uu____10665  ->
                              match uu____10665 with
                              | (x,i) ->
                                  let uu____10672 =
                                    let uu___149_10673 = x in
                                    let uu____10674 =
                                      FStar_Syntax_Subst.subst subst1
                                        x.FStar_Syntax_Syntax.sort in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___149_10673.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___149_10673.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = uu____10674
                                    } in
                                  (uu____10672, i))) in
                    FStar_All.pipe_right uu____10651
                      FStar_Syntax_Util.name_binders in
                  let body1 =
                    let uu____10686 =
                      let uu____10688 =
                        let uu____10689 = FStar_Syntax_Subst.subst subst1 t in
                        uu____10689.FStar_Syntax_Syntax.n in
                      FStar_All.pipe_left (fun _0_35  -> Some _0_35)
                        uu____10688 in
                    let uu____10693 =
                      let uu____10694 = FStar_Syntax_Subst.compress body in
                      let uu____10695 =
                        let uu____10696 =
                          FStar_Syntax_Util.args_of_binders extra_formals1 in
                        FStar_All.pipe_left Prims.snd uu____10696 in
                      FStar_Syntax_Syntax.extend_app_n uu____10694
                        uu____10695 in
                    uu____10693 uu____10686 body.FStar_Syntax_Syntax.pos in
                  ((FStar_List.append binders extra_formals1), body1) in
            let destruct_bound_function flid t_norm e =
              let get_result_type c =
                let uu____10738 =
                  FStar_TypeChecker_Env.is_reifiable_comp env.tcenv c in
                if uu____10738
                then
                  FStar_TypeChecker_Env.reify_comp
                    (let uu___150_10739 = env.tcenv in
                     {
                       FStar_TypeChecker_Env.solver =
                         (uu___150_10739.FStar_TypeChecker_Env.solver);
                       FStar_TypeChecker_Env.range =
                         (uu___150_10739.FStar_TypeChecker_Env.range);
                       FStar_TypeChecker_Env.curmodule =
                         (uu___150_10739.FStar_TypeChecker_Env.curmodule);
                       FStar_TypeChecker_Env.gamma =
                         (uu___150_10739.FStar_TypeChecker_Env.gamma);
                       FStar_TypeChecker_Env.gamma_cache =
                         (uu___150_10739.FStar_TypeChecker_Env.gamma_cache);
                       FStar_TypeChecker_Env.modules =
                         (uu___150_10739.FStar_TypeChecker_Env.modules);
                       FStar_TypeChecker_Env.expected_typ =
                         (uu___150_10739.FStar_TypeChecker_Env.expected_typ);
                       FStar_TypeChecker_Env.sigtab =
                         (uu___150_10739.FStar_TypeChecker_Env.sigtab);
                       FStar_TypeChecker_Env.is_pattern =
                         (uu___150_10739.FStar_TypeChecker_Env.is_pattern);
                       FStar_TypeChecker_Env.instantiate_imp =
                         (uu___150_10739.FStar_TypeChecker_Env.instantiate_imp);
                       FStar_TypeChecker_Env.effects =
                         (uu___150_10739.FStar_TypeChecker_Env.effects);
                       FStar_TypeChecker_Env.generalize =
                         (uu___150_10739.FStar_TypeChecker_Env.generalize);
                       FStar_TypeChecker_Env.letrecs =
                         (uu___150_10739.FStar_TypeChecker_Env.letrecs);
                       FStar_TypeChecker_Env.top_level =
                         (uu___150_10739.FStar_TypeChecker_Env.top_level);
                       FStar_TypeChecker_Env.check_uvars =
                         (uu___150_10739.FStar_TypeChecker_Env.check_uvars);
                       FStar_TypeChecker_Env.use_eq =
                         (uu___150_10739.FStar_TypeChecker_Env.use_eq);
                       FStar_TypeChecker_Env.is_iface =
                         (uu___150_10739.FStar_TypeChecker_Env.is_iface);
                       FStar_TypeChecker_Env.admit =
                         (uu___150_10739.FStar_TypeChecker_Env.admit);
                       FStar_TypeChecker_Env.lax = true;
                       FStar_TypeChecker_Env.lax_universes =
                         (uu___150_10739.FStar_TypeChecker_Env.lax_universes);
                       FStar_TypeChecker_Env.type_of =
                         (uu___150_10739.FStar_TypeChecker_Env.type_of);
                       FStar_TypeChecker_Env.universe_of =
                         (uu___150_10739.FStar_TypeChecker_Env.universe_of);
                       FStar_TypeChecker_Env.use_bv_sorts =
                         (uu___150_10739.FStar_TypeChecker_Env.use_bv_sorts);
                       FStar_TypeChecker_Env.qname_and_index =
                         (uu___150_10739.FStar_TypeChecker_Env.qname_and_index)
                     }) c FStar_Syntax_Syntax.U_unknown
                else FStar_Syntax_Util.comp_result c in
              let rec aux norm1 t_norm1 =
                let uu____10760 = FStar_Syntax_Util.abs_formals e in
                match uu____10760 with
                | (binders,body,lopt) ->
                    (match binders with
                     | uu____10809::uu____10810 ->
                         let uu____10818 =
                           let uu____10819 =
                             FStar_Syntax_Subst.compress t_norm1 in
                           uu____10819.FStar_Syntax_Syntax.n in
                         (match uu____10818 with
                          | FStar_Syntax_Syntax.Tm_arrow (formals,c) ->
                              let uu____10846 =
                                FStar_Syntax_Subst.open_comp formals c in
                              (match uu____10846 with
                               | (formals1,c1) ->
                                   let nformals = FStar_List.length formals1 in
                                   let nbinders = FStar_List.length binders in
                                   let tres = get_result_type c1 in
                                   let uu____10872 =
                                     (nformals < nbinders) &&
                                       (FStar_Syntax_Util.is_total_comp c1) in
                                   if uu____10872
                                   then
                                     let uu____10890 =
                                       FStar_Util.first_N nformals binders in
                                     (match uu____10890 with
                                      | (bs0,rest) ->
                                          let c2 =
                                            let subst1 =
                                              FStar_List.map2
                                                (fun uu____10936  ->
                                                   fun uu____10937  ->
                                                     match (uu____10936,
                                                             uu____10937)
                                                     with
                                                     | ((x,uu____10947),
                                                        (b,uu____10949)) ->
                                                         let uu____10954 =
                                                           let uu____10959 =
                                                             FStar_Syntax_Syntax.bv_to_name
                                                               b in
                                                           (x, uu____10959) in
                                                         FStar_Syntax_Syntax.NT
                                                           uu____10954)
                                                formals1 bs0 in
                                            FStar_Syntax_Subst.subst_comp
                                              subst1 c1 in
                                          let body1 =
                                            FStar_Syntax_Util.abs rest body
                                              lopt in
                                          let uu____10961 =
                                            let uu____10972 =
                                              get_result_type c2 in
                                            (bs0, body1, bs0, uu____10972) in
                                          (uu____10961, false))
                                   else
                                     if nformals > nbinders
                                     then
                                       (let uu____11007 =
                                          eta_expand1 binders formals1 body
                                            tres in
                                        match uu____11007 with
                                        | (binders1,body1) ->
                                            ((binders1, body1, formals1,
                                               tres), false))
                                     else
                                       ((binders, body, formals1, tres),
                                         false))
                          | FStar_Syntax_Syntax.Tm_refine (x,uu____11059) ->
                              let uu____11064 =
                                let uu____11075 =
                                  aux norm1 x.FStar_Syntax_Syntax.sort in
                                Prims.fst uu____11075 in
                              (uu____11064, true)
                          | uu____11108 when Prims.op_Negation norm1 ->
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
                          | uu____11110 ->
                              let uu____11111 =
                                let uu____11112 =
                                  FStar_Syntax_Print.term_to_string e in
                                let uu____11113 =
                                  FStar_Syntax_Print.term_to_string t_norm1 in
                                FStar_Util.format3
                                  "Impossible! let-bound lambda %s = %s has a type that's not a function: %s\n"
                                  flid.FStar_Ident.str uu____11112
                                  uu____11113 in
                              failwith uu____11111)
                     | uu____11126 ->
                         let uu____11127 =
                           let uu____11128 =
                             FStar_Syntax_Subst.compress t_norm1 in
                           uu____11128.FStar_Syntax_Syntax.n in
                         (match uu____11127 with
                          | FStar_Syntax_Syntax.Tm_arrow (formals,c) ->
                              let uu____11155 =
                                FStar_Syntax_Subst.open_comp formals c in
                              (match uu____11155 with
                               | (formals1,c1) ->
                                   let tres = get_result_type c1 in
                                   let uu____11173 =
                                     eta_expand1 [] formals1 e tres in
                                   (match uu____11173 with
                                    | (binders1,body1) ->
                                        ((binders1, body1, formals1, tres),
                                          false)))
                          | uu____11221 -> (([], e, [], t_norm1), false))) in
              aux false t_norm in
            (try
               let uu____11249 =
                 FStar_All.pipe_right bindings
                   (FStar_Util.for_all
                      (fun lb  ->
                         (FStar_Syntax_Util.is_lemma
                            lb.FStar_Syntax_Syntax.lbtyp)
                           || (is_tactic lb.FStar_Syntax_Syntax.lbtyp))) in
               if uu____11249
               then encode_top_level_vals env bindings quals
               else
                 (let uu____11256 =
                    FStar_All.pipe_right bindings
                      (FStar_List.fold_left
                         (fun uu____11297  ->
                            fun lb  ->
                              match uu____11297 with
                              | (toks,typs,decls,env1) ->
                                  ((let uu____11348 =
                                      FStar_Syntax_Util.is_lemma
                                        lb.FStar_Syntax_Syntax.lbtyp in
                                    if uu____11348
                                    then Prims.raise Let_rec_unencodeable
                                    else ());
                                   (let t_norm =
                                      whnf env1 lb.FStar_Syntax_Syntax.lbtyp in
                                    let uu____11351 =
                                      let uu____11359 =
                                        FStar_Util.right
                                          lb.FStar_Syntax_Syntax.lbname in
                                      declare_top_level_let env1 uu____11359
                                        lb.FStar_Syntax_Syntax.lbtyp t_norm in
                                    match uu____11351 with
                                    | (tok,decl,env2) ->
                                        let uu____11384 =
                                          let uu____11391 =
                                            let uu____11397 =
                                              FStar_Util.right
                                                lb.FStar_Syntax_Syntax.lbname in
                                            (uu____11397, tok) in
                                          uu____11391 :: toks in
                                        (uu____11384, (t_norm :: typs), (decl
                                          :: decls), env2))))
                         ([], [], [], env)) in
                  match uu____11256 with
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
                        | uu____11499 ->
                            if curry
                            then
                              (match ftok with
                               | Some ftok1 -> mk_Apply ftok1 vars
                               | None  ->
                                   let uu____11504 =
                                     FStar_SMTEncoding_Util.mkFreeV
                                       (f, FStar_SMTEncoding_Term.Term_sort) in
                                   mk_Apply uu____11504 vars)
                            else
                              (let uu____11506 =
                                 let uu____11510 =
                                   FStar_List.map
                                     FStar_SMTEncoding_Util.mkFreeV vars in
                                 (f, uu____11510) in
                               FStar_SMTEncoding_Util.mkApp uu____11506) in
                      let uu____11515 =
                        (FStar_All.pipe_right quals
                           (FStar_Util.for_some
                              (fun uu___119_11517  ->
                                 match uu___119_11517 with
                                 | FStar_Syntax_Syntax.HasMaskedEffect  ->
                                     true
                                 | uu____11518 -> false)))
                          ||
                          (FStar_All.pipe_right typs1
                             (FStar_Util.for_some
                                (fun t  ->
                                   let uu____11521 =
                                     (FStar_Syntax_Util.is_pure_or_ghost_function
                                        t)
                                       ||
                                       (FStar_TypeChecker_Env.is_reifiable_function
                                          env1.tcenv t) in
                                   FStar_All.pipe_left Prims.op_Negation
                                     uu____11521))) in
                      if uu____11515
                      then (decls1, env1)
                      else
                        if Prims.op_Negation is_rec
                        then
                          (match (bindings, typs1, toks1) with
                           | ({ FStar_Syntax_Syntax.lbname = uu____11541;
                                FStar_Syntax_Syntax.lbunivs = uvs;
                                FStar_Syntax_Syntax.lbtyp = uu____11543;
                                FStar_Syntax_Syntax.lbeff = uu____11544;
                                FStar_Syntax_Syntax.lbdef = e;_}::[],t_norm::[],
                              (flid_fv,(f,ftok))::[]) ->
                               let flid =
                                 (flid_fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                               let uu____11585 =
                                 let uu____11589 =
                                   FStar_TypeChecker_Env.open_universes_in
                                     env1.tcenv uvs [e; t_norm] in
                                 match uu____11589 with
                                 | (tcenv',uu____11600,e_t) ->
                                     let uu____11604 =
                                       match e_t with
                                       | e1::t_norm1::[] -> (e1, t_norm1)
                                       | uu____11611 -> failwith "Impossible" in
                                     (match uu____11604 with
                                      | (e1,t_norm1) ->
                                          ((let uu___153_11620 = env1 in
                                            {
                                              bindings =
                                                (uu___153_11620.bindings);
                                              depth = (uu___153_11620.depth);
                                              tcenv = tcenv';
                                              warn = (uu___153_11620.warn);
                                              cache = (uu___153_11620.cache);
                                              nolabels =
                                                (uu___153_11620.nolabels);
                                              use_zfuel_name =
                                                (uu___153_11620.use_zfuel_name);
                                              encode_non_total_function_typ =
                                                (uu___153_11620.encode_non_total_function_typ);
                                              current_module_name =
                                                (uu___153_11620.current_module_name)
                                            }), e1, t_norm1)) in
                               (match uu____11585 with
                                | (env',e1,t_norm1) ->
                                    let uu____11627 =
                                      destruct_bound_function flid t_norm1 e1 in
                                    (match uu____11627 with
                                     | ((binders,body,uu____11639,uu____11640),curry)
                                         ->
                                         ((let uu____11647 =
                                             FStar_All.pipe_left
                                               (FStar_TypeChecker_Env.debug
                                                  env1.tcenv)
                                               (FStar_Options.Other
                                                  "SMTEncoding") in
                                           if uu____11647
                                           then
                                             let uu____11648 =
                                               FStar_Syntax_Print.binders_to_string
                                                 ", " binders in
                                             let uu____11649 =
                                               FStar_Syntax_Print.term_to_string
                                                 body in
                                             FStar_Util.print2
                                               "Encoding let : binders=[%s], body=%s\n"
                                               uu____11648 uu____11649
                                           else ());
                                          (let uu____11651 =
                                             encode_binders None binders env' in
                                           match uu____11651 with
                                           | (vars,guards,env'1,binder_decls,uu____11667)
                                               ->
                                               let body1 =
                                                 let uu____11675 =
                                                   FStar_TypeChecker_Env.is_reifiable_function
                                                     env'1.tcenv t_norm1 in
                                                 if uu____11675
                                                 then
                                                   FStar_TypeChecker_Util.reify_body
                                                     env'1.tcenv body
                                                 else body in
                                               let app =
                                                 mk_app1 curry f ftok vars in
                                               let uu____11678 =
                                                 let uu____11683 =
                                                   FStar_All.pipe_right quals
                                                     (FStar_List.contains
                                                        FStar_Syntax_Syntax.Logic) in
                                                 if uu____11683
                                                 then
                                                   let uu____11689 =
                                                     FStar_SMTEncoding_Term.mk_Valid
                                                       app in
                                                   let uu____11690 =
                                                     encode_formula body1
                                                       env'1 in
                                                   (uu____11689, uu____11690)
                                                 else
                                                   (let uu____11696 =
                                                      encode_term body1 env'1 in
                                                    (app, uu____11696)) in
                                               (match uu____11678 with
                                                | (app1,(body2,decls2)) ->
                                                    let eqn =
                                                      let uu____11710 =
                                                        let uu____11714 =
                                                          let uu____11715 =
                                                            let uu____11721 =
                                                              FStar_SMTEncoding_Util.mkEq
                                                                (app1, body2) in
                                                            ([[app1]], vars,
                                                              uu____11721) in
                                                          FStar_SMTEncoding_Util.mkForall
                                                            uu____11715 in
                                                        let uu____11727 =
                                                          let uu____11729 =
                                                            FStar_Util.format1
                                                              "Equation for %s"
                                                              flid.FStar_Ident.str in
                                                          Some uu____11729 in
                                                        (uu____11714,
                                                          uu____11727,
                                                          (Prims.strcat
                                                             "equation_" f)) in
                                                      FStar_SMTEncoding_Util.mkAssume
                                                        uu____11710 in
                                                    let uu____11731 =
                                                      let uu____11733 =
                                                        let uu____11735 =
                                                          let uu____11737 =
                                                            let uu____11739 =
                                                              primitive_type_axioms
                                                                env1.tcenv
                                                                flid f app1 in
                                                            FStar_List.append
                                                              [eqn]
                                                              uu____11739 in
                                                          FStar_List.append
                                                            decls2
                                                            uu____11737 in
                                                        FStar_List.append
                                                          binder_decls
                                                          uu____11735 in
                                                      FStar_List.append
                                                        decls1 uu____11733 in
                                                    (uu____11731, env1))))))
                           | uu____11742 -> failwith "Impossible")
                        else
                          (let fuel =
                             let uu____11761 = varops.fresh "fuel" in
                             (uu____11761, FStar_SMTEncoding_Term.Fuel_sort) in
                           let fuel_tm = FStar_SMTEncoding_Util.mkFreeV fuel in
                           let env0 = env1 in
                           let uu____11764 =
                             FStar_All.pipe_right toks1
                               (FStar_List.fold_left
                                  (fun uu____11803  ->
                                     fun uu____11804  ->
                                       match (uu____11803, uu____11804) with
                                       | ((gtoks,env2),(flid_fv,(f,ftok))) ->
                                           let flid =
                                             (flid_fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                                           let g =
                                             let uu____11886 =
                                               FStar_Ident.lid_add_suffix
                                                 flid "fuel_instrumented" in
                                             varops.new_fvar uu____11886 in
                                           let gtok =
                                             let uu____11888 =
                                               FStar_Ident.lid_add_suffix
                                                 flid
                                                 "fuel_instrumented_token" in
                                             varops.new_fvar uu____11888 in
                                           let env3 =
                                             let uu____11890 =
                                               let uu____11892 =
                                                 FStar_SMTEncoding_Util.mkApp
                                                   (g, [fuel_tm]) in
                                               FStar_All.pipe_left
                                                 (fun _0_36  -> Some _0_36)
                                                 uu____11892 in
                                             push_free_var env2 flid gtok
                                               uu____11890 in
                                           (((flid, f, ftok, g, gtok) ::
                                             gtoks), env3)) ([], env1)) in
                           match uu____11764 with
                           | (gtoks,env2) ->
                               let gtoks1 = FStar_List.rev gtoks in
                               let encode_one_binding env01 uu____11978
                                 t_norm uu____11980 =
                                 match (uu____11978, uu____11980) with
                                 | ((flid,f,ftok,g,gtok),{
                                                           FStar_Syntax_Syntax.lbname
                                                             = lbn;
                                                           FStar_Syntax_Syntax.lbunivs
                                                             = uvs;
                                                           FStar_Syntax_Syntax.lbtyp
                                                             = uu____12007;
                                                           FStar_Syntax_Syntax.lbeff
                                                             = uu____12008;
                                                           FStar_Syntax_Syntax.lbdef
                                                             = e;_})
                                     ->
                                     let uu____12025 =
                                       let uu____12029 =
                                         FStar_TypeChecker_Env.open_universes_in
                                           env2.tcenv uvs [e; t_norm] in
                                       match uu____12029 with
                                       | (tcenv',uu____12044,e_t) ->
                                           let uu____12048 =
                                             match e_t with
                                             | e1::t_norm1::[] ->
                                                 (e1, t_norm1)
                                             | uu____12055 ->
                                                 failwith "Impossible" in
                                           (match uu____12048 with
                                            | (e1,t_norm1) ->
                                                ((let uu___154_12064 = env2 in
                                                  {
                                                    bindings =
                                                      (uu___154_12064.bindings);
                                                    depth =
                                                      (uu___154_12064.depth);
                                                    tcenv = tcenv';
                                                    warn =
                                                      (uu___154_12064.warn);
                                                    cache =
                                                      (uu___154_12064.cache);
                                                    nolabels =
                                                      (uu___154_12064.nolabels);
                                                    use_zfuel_name =
                                                      (uu___154_12064.use_zfuel_name);
                                                    encode_non_total_function_typ
                                                      =
                                                      (uu___154_12064.encode_non_total_function_typ);
                                                    current_module_name =
                                                      (uu___154_12064.current_module_name)
                                                  }), e1, t_norm1)) in
                                     (match uu____12025 with
                                      | (env',e1,t_norm1) ->
                                          ((let uu____12074 =
                                              FStar_All.pipe_left
                                                (FStar_TypeChecker_Env.debug
                                                   env01.tcenv)
                                                (FStar_Options.Other
                                                   "SMTEncoding") in
                                            if uu____12074
                                            then
                                              let uu____12075 =
                                                FStar_Syntax_Print.lbname_to_string
                                                  lbn in
                                              let uu____12076 =
                                                FStar_Syntax_Print.term_to_string
                                                  t_norm1 in
                                              let uu____12077 =
                                                FStar_Syntax_Print.term_to_string
                                                  e1 in
                                              FStar_Util.print3
                                                "Encoding let rec %s : %s = %s\n"
                                                uu____12075 uu____12076
                                                uu____12077
                                            else ());
                                           (let uu____12079 =
                                              destruct_bound_function flid
                                                t_norm1 e1 in
                                            match uu____12079 with
                                            | ((binders,body,formals,tres),curry)
                                                ->
                                                ((let uu____12101 =
                                                    FStar_All.pipe_left
                                                      (FStar_TypeChecker_Env.debug
                                                         env01.tcenv)
                                                      (FStar_Options.Other
                                                         "SMTEncoding") in
                                                  if uu____12101
                                                  then
                                                    let uu____12102 =
                                                      FStar_Syntax_Print.binders_to_string
                                                        ", " binders in
                                                    let uu____12103 =
                                                      FStar_Syntax_Print.term_to_string
                                                        body in
                                                    let uu____12104 =
                                                      FStar_Syntax_Print.binders_to_string
                                                        ", " formals in
                                                    let uu____12105 =
                                                      FStar_Syntax_Print.term_to_string
                                                        tres in
                                                    FStar_Util.print4
                                                      "Encoding let rec: binders=[%s], body=%s, formals=[%s], tres=%s\n"
                                                      uu____12102 uu____12103
                                                      uu____12104 uu____12105
                                                  else ());
                                                 if curry
                                                 then
                                                   failwith
                                                     "Unexpected type of let rec in SMT Encoding; expected it to be annotated with an arrow type"
                                                 else ();
                                                 (let uu____12109 =
                                                    encode_binders None
                                                      binders env' in
                                                  match uu____12109 with
                                                  | (vars,guards,env'1,binder_decls,uu____12127)
                                                      ->
                                                      let decl_g =
                                                        let uu____12135 =
                                                          let uu____12141 =
                                                            let uu____12143 =
                                                              FStar_List.map
                                                                Prims.snd
                                                                vars in
                                                            FStar_SMTEncoding_Term.Fuel_sort
                                                              :: uu____12143 in
                                                          (g, uu____12141,
                                                            FStar_SMTEncoding_Term.Term_sort,
                                                            (Some
                                                               "Fuel-instrumented function name")) in
                                                        FStar_SMTEncoding_Term.DeclFun
                                                          uu____12135 in
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
                                                        let uu____12158 =
                                                          let uu____12162 =
                                                            FStar_List.map
                                                              FStar_SMTEncoding_Util.mkFreeV
                                                              vars in
                                                          (f, uu____12162) in
                                                        FStar_SMTEncoding_Util.mkApp
                                                          uu____12158 in
                                                      let gsapp =
                                                        let uu____12168 =
                                                          let uu____12172 =
                                                            let uu____12174 =
                                                              FStar_SMTEncoding_Util.mkApp
                                                                ("SFuel",
                                                                  [fuel_tm]) in
                                                            uu____12174 ::
                                                              vars_tm in
                                                          (g, uu____12172) in
                                                        FStar_SMTEncoding_Util.mkApp
                                                          uu____12168 in
                                                      let gmax =
                                                        let uu____12178 =
                                                          let uu____12182 =
                                                            let uu____12184 =
                                                              FStar_SMTEncoding_Util.mkApp
                                                                ("MaxFuel",
                                                                  []) in
                                                            uu____12184 ::
                                                              vars_tm in
                                                          (g, uu____12182) in
                                                        FStar_SMTEncoding_Util.mkApp
                                                          uu____12178 in
                                                      let body1 =
                                                        let uu____12188 =
                                                          FStar_TypeChecker_Env.is_reifiable_function
                                                            env'1.tcenv
                                                            t_norm1 in
                                                        if uu____12188
                                                        then
                                                          FStar_TypeChecker_Util.reify_body
                                                            env'1.tcenv body
                                                        else body in
                                                      let uu____12190 =
                                                        encode_term body1
                                                          env'1 in
                                                      (match uu____12190 with
                                                       | (body_tm,decls2) ->
                                                           let eqn_g =
                                                             let uu____12201
                                                               =
                                                               let uu____12205
                                                                 =
                                                                 let uu____12206
                                                                   =
                                                                   let uu____12214
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
                                                                    uu____12214) in
                                                                 FStar_SMTEncoding_Util.mkForall'
                                                                   uu____12206 in
                                                               let uu____12225
                                                                 =
                                                                 let uu____12227
                                                                   =
                                                                   FStar_Util.format1
                                                                    "Equation for fuel-instrumented recursive function: %s"
                                                                    flid.FStar_Ident.str in
                                                                 Some
                                                                   uu____12227 in
                                                               (uu____12205,
                                                                 uu____12225,
                                                                 (Prims.strcat
                                                                    "equation_with_fuel_"
                                                                    g)) in
                                                             FStar_SMTEncoding_Util.mkAssume
                                                               uu____12201 in
                                                           let eqn_f =
                                                             let uu____12230
                                                               =
                                                               let uu____12234
                                                                 =
                                                                 let uu____12235
                                                                   =
                                                                   let uu____12241
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (app,
                                                                    gmax) in
                                                                   ([[app]],
                                                                    vars,
                                                                    uu____12241) in
                                                                 FStar_SMTEncoding_Util.mkForall
                                                                   uu____12235 in
                                                               (uu____12234,
                                                                 (Some
                                                                    "Correspondence of recursive function to instrumented version"),
                                                                 (Prims.strcat
                                                                    "@fuel_correspondence_"
                                                                    g)) in
                                                             FStar_SMTEncoding_Util.mkAssume
                                                               uu____12230 in
                                                           let eqn_g' =
                                                             let uu____12249
                                                               =
                                                               let uu____12253
                                                                 =
                                                                 let uu____12254
                                                                   =
                                                                   let uu____12260
                                                                    =
                                                                    let uu____12261
                                                                    =
                                                                    let uu____12264
                                                                    =
                                                                    let uu____12265
                                                                    =
                                                                    let uu____12269
                                                                    =
                                                                    let uu____12271
                                                                    =
                                                                    FStar_SMTEncoding_Term.n_fuel
                                                                    (Prims.parse_int
                                                                    "0") in
                                                                    uu____12271
                                                                    ::
                                                                    vars_tm in
                                                                    (g,
                                                                    uu____12269) in
                                                                    FStar_SMTEncoding_Util.mkApp
                                                                    uu____12265 in
                                                                    (gsapp,
                                                                    uu____12264) in
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    uu____12261 in
                                                                   ([[gsapp]],
                                                                    (fuel ::
                                                                    vars),
                                                                    uu____12260) in
                                                                 FStar_SMTEncoding_Util.mkForall
                                                                   uu____12254 in
                                                               (uu____12253,
                                                                 (Some
                                                                    "Fuel irrelevance"),
                                                                 (Prims.strcat
                                                                    "@fuel_irrelevance_"
                                                                    g)) in
                                                             FStar_SMTEncoding_Util.mkAssume
                                                               uu____12249 in
                                                           let uu____12283 =
                                                             let uu____12288
                                                               =
                                                               encode_binders
                                                                 None formals
                                                                 env02 in
                                                             match uu____12288
                                                             with
                                                             | (vars1,v_guards,env3,binder_decls1,uu____12305)
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
                                                                    let uu____12320
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    (gtok,
                                                                    FStar_SMTEncoding_Term.Term_sort) in
                                                                    mk_Apply
                                                                    uu____12320
                                                                    (fuel ::
                                                                    vars1) in
                                                                   let uu____12323
                                                                    =
                                                                    let uu____12327
                                                                    =
                                                                    let uu____12328
                                                                    =
                                                                    let uu____12334
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (tok_app,
                                                                    gapp) in
                                                                    ([
                                                                    [tok_app]],
                                                                    (fuel ::
                                                                    vars1),
                                                                    uu____12334) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____12328 in
                                                                    (uu____12327,
                                                                    (Some
                                                                    "Fuel token correspondence"),
                                                                    (Prims.strcat
                                                                    "fuel_token_correspondence_"
                                                                    gtok)) in
                                                                   FStar_SMTEncoding_Util.mkAssume
                                                                    uu____12323 in
                                                                 let uu____12345
                                                                   =
                                                                   let uu____12349
                                                                    =
                                                                    encode_term_pred
                                                                    None tres
                                                                    env3 gapp in
                                                                   match uu____12349
                                                                   with
                                                                   | 
                                                                   (g_typing,d3)
                                                                    ->
                                                                    let uu____12357
                                                                    =
                                                                    let uu____12359
                                                                    =
                                                                    let uu____12360
                                                                    =
                                                                    let uu____12364
                                                                    =
                                                                    let uu____12365
                                                                    =
                                                                    let uu____12371
                                                                    =
                                                                    let uu____12372
                                                                    =
                                                                    let uu____12375
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    v_guards in
                                                                    (uu____12375,
                                                                    g_typing) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____12372 in
                                                                    ([[gapp]],
                                                                    (fuel ::
                                                                    vars1),
                                                                    uu____12371) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____12365 in
                                                                    (uu____12364,
                                                                    (Some
                                                                    "Typing correspondence of token to term"),
                                                                    (Prims.strcat
                                                                    "token_correspondence_"
                                                                    g)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____12360 in
                                                                    [uu____12359] in
                                                                    (d3,
                                                                    uu____12357) in
                                                                 (match uu____12345
                                                                  with
                                                                  | (aux_decls,typing_corr)
                                                                    ->
                                                                    ((FStar_List.append
                                                                    binder_decls1
                                                                    aux_decls),
                                                                    (FStar_List.append
                                                                    typing_corr
                                                                    [tok_corr]))) in
                                                           (match uu____12283
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
                               let uu____12410 =
                                 let uu____12417 =
                                   FStar_List.zip3 gtoks1 typs1 bindings in
                                 FStar_List.fold_left
                                   (fun uu____12453  ->
                                      fun uu____12454  ->
                                        match (uu____12453, uu____12454) with
                                        | ((decls2,eqns,env01),(gtok,ty,lb))
                                            ->
                                            let uu____12540 =
                                              encode_one_binding env01 gtok
                                                ty lb in
                                            (match uu____12540 with
                                             | (decls',eqns',env02) ->
                                                 ((decls' :: decls2),
                                                   (FStar_List.append eqns'
                                                      eqns), env02)))
                                   ([decls1], [], env0) uu____12417 in
                               (match uu____12410 with
                                | (decls2,eqns,env01) ->
                                    let uu____12580 =
                                      let isDeclFun uu___120_12588 =
                                        match uu___120_12588 with
                                        | FStar_SMTEncoding_Term.DeclFun
                                            uu____12589 -> true
                                        | uu____12595 -> false in
                                      let uu____12596 =
                                        FStar_All.pipe_right decls2
                                          FStar_List.flatten in
                                      FStar_All.pipe_right uu____12596
                                        (FStar_List.partition isDeclFun) in
                                    (match uu____12580 with
                                     | (prefix_decls,rest) ->
                                         let eqns1 = FStar_List.rev eqns in
                                         ((FStar_List.append prefix_decls
                                             (FStar_List.append rest eqns1)),
                                           env01)))))
             with
             | Let_rec_unencodeable  ->
                 let msg =
                   let uu____12623 =
                     FStar_All.pipe_right bindings
                       (FStar_List.map
                          (fun lb  ->
                             FStar_Syntax_Print.lbname_to_string
                               lb.FStar_Syntax_Syntax.lbname)) in
                   FStar_All.pipe_right uu____12623
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
        let uu____12656 = FStar_Syntax_Util.lid_of_sigelt se in
        match uu____12656 with | None  -> "" | Some l -> l.FStar_Ident.str in
      let uu____12659 = encode_sigelt' env se in
      match uu____12659 with
      | (g,env1) ->
          let g1 =
            match g with
            | [] ->
                let uu____12669 =
                  let uu____12670 = FStar_Util.format1 "<Skipped %s/>" nm in
                  FStar_SMTEncoding_Term.Caption uu____12670 in
                [uu____12669]
            | uu____12671 ->
                let uu____12672 =
                  let uu____12674 =
                    let uu____12675 =
                      FStar_Util.format1 "<Start encoding %s>" nm in
                    FStar_SMTEncoding_Term.Caption uu____12675 in
                  uu____12674 :: g in
                let uu____12676 =
                  let uu____12678 =
                    let uu____12679 =
                      FStar_Util.format1 "</end encoding %s>" nm in
                    FStar_SMTEncoding_Term.Caption uu____12679 in
                  [uu____12678] in
                FStar_List.append uu____12672 uu____12676 in
          (g1, env1)
and encode_sigelt':
  env_t ->
    FStar_Syntax_Syntax.sigelt -> (FStar_SMTEncoding_Term.decls_t* env_t)
  =
  fun env  ->
    fun se  ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____12687 ->
          failwith "impossible -- removed by tc.fs"
      | FStar_Syntax_Syntax.Sig_pragma _
        |FStar_Syntax_Syntax.Sig_main _
         |FStar_Syntax_Syntax.Sig_effect_abbrev _
          |FStar_Syntax_Syntax.Sig_sub_effect _ -> ([], env)
      | FStar_Syntax_Syntax.Sig_new_effect ed ->
          let uu____12696 =
            let uu____12697 =
              FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                (FStar_List.contains FStar_Syntax_Syntax.Reifiable) in
            FStar_All.pipe_right uu____12697 Prims.op_Negation in
          if uu____12696
          then ([], env)
          else
            (let close_effect_params tm =
               match ed.FStar_Syntax_Syntax.binders with
               | [] -> tm
               | uu____12717 ->
                   let uu____12718 =
                     let uu____12721 =
                       let uu____12722 =
                         let uu____12737 =
                           FStar_All.pipe_left (fun _0_37  -> Some _0_37)
                             (FStar_Util.Inr
                                (FStar_Syntax_Const.effect_Tot_lid,
                                  [FStar_Syntax_Syntax.TOTAL])) in
                         ((ed.FStar_Syntax_Syntax.binders), tm, uu____12737) in
                       FStar_Syntax_Syntax.Tm_abs uu____12722 in
                     FStar_Syntax_Syntax.mk uu____12721 in
                   uu____12718 None tm.FStar_Syntax_Syntax.pos in
             let encode_action env1 a =
               let uu____12790 =
                 new_term_constant_and_tok_from_lid env1
                   a.FStar_Syntax_Syntax.action_name in
               match uu____12790 with
               | (aname,atok,env2) ->
                   let uu____12800 =
                     FStar_Syntax_Util.arrow_formals_comp
                       a.FStar_Syntax_Syntax.action_typ in
                   (match uu____12800 with
                    | (formals,uu____12810) ->
                        let uu____12817 =
                          let uu____12820 =
                            close_effect_params
                              a.FStar_Syntax_Syntax.action_defn in
                          encode_term uu____12820 env2 in
                        (match uu____12817 with
                         | (tm,decls) ->
                             let a_decls =
                               let uu____12828 =
                                 let uu____12829 =
                                   let uu____12835 =
                                     FStar_All.pipe_right formals
                                       (FStar_List.map
                                          (fun uu____12843  ->
                                             FStar_SMTEncoding_Term.Term_sort)) in
                                   (aname, uu____12835,
                                     FStar_SMTEncoding_Term.Term_sort,
                                     (Some "Action")) in
                                 FStar_SMTEncoding_Term.DeclFun uu____12829 in
                               [uu____12828;
                               FStar_SMTEncoding_Term.DeclFun
                                 (atok, [], FStar_SMTEncoding_Term.Term_sort,
                                   (Some "Action token"))] in
                             let uu____12850 =
                               let aux uu____12879 uu____12880 =
                                 match (uu____12879, uu____12880) with
                                 | ((bv,uu____12907),(env3,acc_sorts,acc)) ->
                                     let uu____12928 = gen_term_var env3 bv in
                                     (match uu____12928 with
                                      | (xxsym,xx,env4) ->
                                          (env4,
                                            ((xxsym,
                                               FStar_SMTEncoding_Term.Term_sort)
                                            :: acc_sorts), (xx :: acc))) in
                               FStar_List.fold_right aux formals
                                 (env2, [], []) in
                             (match uu____12850 with
                              | (uu____12966,xs_sorts,xs) ->
                                  let app =
                                    FStar_SMTEncoding_Util.mkApp (aname, xs) in
                                  let a_eq =
                                    let uu____12980 =
                                      let uu____12984 =
                                        let uu____12985 =
                                          let uu____12991 =
                                            let uu____12992 =
                                              let uu____12995 =
                                                mk_Apply tm xs_sorts in
                                              (app, uu____12995) in
                                            FStar_SMTEncoding_Util.mkEq
                                              uu____12992 in
                                          ([[app]], xs_sorts, uu____12991) in
                                        FStar_SMTEncoding_Util.mkForall
                                          uu____12985 in
                                      (uu____12984, (Some "Action equality"),
                                        (Prims.strcat aname "_equality")) in
                                    FStar_SMTEncoding_Util.mkAssume
                                      uu____12980 in
                                  let tok_correspondence =
                                    let tok_term =
                                      FStar_SMTEncoding_Util.mkFreeV
                                        (atok,
                                          FStar_SMTEncoding_Term.Term_sort) in
                                    let tok_app = mk_Apply tok_term xs_sorts in
                                    let uu____13007 =
                                      let uu____13011 =
                                        let uu____13012 =
                                          let uu____13018 =
                                            FStar_SMTEncoding_Util.mkEq
                                              (tok_app, app) in
                                          ([[tok_app]], xs_sorts,
                                            uu____13018) in
                                        FStar_SMTEncoding_Util.mkForall
                                          uu____13012 in
                                      (uu____13011,
                                        (Some "Action token correspondence"),
                                        (Prims.strcat aname
                                           "_token_correspondence")) in
                                    FStar_SMTEncoding_Util.mkAssume
                                      uu____13007 in
                                  (env2,
                                    (FStar_List.append decls
                                       (FStar_List.append a_decls
                                          [a_eq; tok_correspondence])))))) in
             let uu____13028 =
               FStar_Util.fold_map encode_action env
                 ed.FStar_Syntax_Syntax.actions in
             match uu____13028 with
             | (env1,decls2) -> ((FStar_List.flatten decls2), env1))
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____13044,uu____13045)
          when FStar_Ident.lid_equals lid FStar_Syntax_Const.precedes_lid ->
          let uu____13046 = new_term_constant_and_tok_from_lid env lid in
          (match uu____13046 with | (tname,ttok,env1) -> ([], env1))
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____13057,t) ->
          let quals = se.FStar_Syntax_Syntax.sigquals in
          let will_encode_definition =
            let uu____13062 =
              FStar_All.pipe_right quals
                (FStar_Util.for_some
                   (fun uu___121_13064  ->
                      match uu___121_13064 with
                      | FStar_Syntax_Syntax.Assumption 
                        |FStar_Syntax_Syntax.Projector _
                         |FStar_Syntax_Syntax.Discriminator _
                          |FStar_Syntax_Syntax.Irreducible  -> true
                      | uu____13067 -> false)) in
            Prims.op_Negation uu____13062 in
          if will_encode_definition
          then ([], env)
          else
            (let fv =
               FStar_Syntax_Syntax.lid_as_fv lid
                 FStar_Syntax_Syntax.Delta_constant None in
             let uu____13073 = encode_top_level_val env fv t quals in
             match uu____13073 with
             | (decls,env1) ->
                 let tname = lid.FStar_Ident.str in
                 let tsym =
                   FStar_SMTEncoding_Util.mkFreeV
                     (tname, FStar_SMTEncoding_Term.Term_sort) in
                 let uu____13085 =
                   let uu____13087 =
                     primitive_type_axioms env1.tcenv lid tname tsym in
                   FStar_List.append decls uu____13087 in
                 (uu____13085, env1))
      | FStar_Syntax_Syntax.Sig_assume (l,f) ->
          let uu____13092 = encode_formula f env in
          (match uu____13092 with
           | (f1,decls) ->
               let g =
                 let uu____13101 =
                   let uu____13102 =
                     let uu____13106 =
                       let uu____13108 =
                         let uu____13109 = FStar_Syntax_Print.lid_to_string l in
                         FStar_Util.format1 "Assumption: %s" uu____13109 in
                       Some uu____13108 in
                     let uu____13110 =
                       varops.mk_unique
                         (Prims.strcat "assumption_" l.FStar_Ident.str) in
                     (f1, uu____13106, uu____13110) in
                   FStar_SMTEncoding_Util.mkAssume uu____13102 in
                 [uu____13101] in
               ((FStar_List.append decls g), env))
      | FStar_Syntax_Syntax.Sig_let (lbs,uu____13114,uu____13115) when
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_List.contains FStar_Syntax_Syntax.Irreducible)
          ->
          let uu____13121 =
            FStar_Util.fold_map
              (fun env1  ->
                 fun lb  ->
                   let lid =
                     let uu____13128 =
                       let uu____13133 =
                         FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
                       uu____13133.FStar_Syntax_Syntax.fv_name in
                     uu____13128.FStar_Syntax_Syntax.v in
                   let uu____13137 =
                     let uu____13138 =
                       FStar_TypeChecker_Env.try_lookup_val_decl env1.tcenv
                         lid in
                     FStar_All.pipe_left FStar_Option.isNone uu____13138 in
                   if uu____13137
                   then
                     let val_decl =
                       let uu___155_13153 = se in
                       {
                         FStar_Syntax_Syntax.sigel =
                           (FStar_Syntax_Syntax.Sig_declare_typ
                              (lid, (lb.FStar_Syntax_Syntax.lbunivs),
                                (lb.FStar_Syntax_Syntax.lbtyp)));
                         FStar_Syntax_Syntax.sigrng =
                           (uu___155_13153.FStar_Syntax_Syntax.sigrng);
                         FStar_Syntax_Syntax.sigquals =
                           (uu___155_13153.FStar_Syntax_Syntax.sigquals);
                         FStar_Syntax_Syntax.sigmeta =
                           (uu___155_13153.FStar_Syntax_Syntax.sigmeta)
                       } in
                     let uu____13157 = encode_sigelt' env1 val_decl in
                     match uu____13157 with | (decls,env2) -> (env2, decls)
                   else (env1, [])) env (Prims.snd lbs) in
          (match uu____13121 with
           | (env1,decls) -> ((FStar_List.flatten decls), env1))
      | FStar_Syntax_Syntax.Sig_let
          ((uu____13174,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inr b2t1;
                          FStar_Syntax_Syntax.lbunivs = uu____13176;
                          FStar_Syntax_Syntax.lbtyp = uu____13177;
                          FStar_Syntax_Syntax.lbeff = uu____13178;
                          FStar_Syntax_Syntax.lbdef = uu____13179;_}::[]),uu____13180,uu____13181)
          when FStar_Syntax_Syntax.fv_eq_lid b2t1 FStar_Syntax_Const.b2t_lid
          ->
          let uu____13195 =
            new_term_constant_and_tok_from_lid env
              (b2t1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          (match uu____13195 with
           | (tname,ttok,env1) ->
               let xx = ("x", FStar_SMTEncoding_Term.Term_sort) in
               let x = FStar_SMTEncoding_Util.mkFreeV xx in
               let b2t_x = FStar_SMTEncoding_Util.mkApp ("Prims.b2t", [x]) in
               let valid_b2t_x =
                 FStar_SMTEncoding_Util.mkApp ("Valid", [b2t_x]) in
               let decls =
                 let uu____13218 =
                   let uu____13220 =
                     let uu____13221 =
                       let uu____13225 =
                         let uu____13226 =
                           let uu____13232 =
                             let uu____13233 =
                               let uu____13236 =
                                 FStar_SMTEncoding_Util.mkApp
                                   ("BoxBool_proj_0", [x]) in
                               (valid_b2t_x, uu____13236) in
                             FStar_SMTEncoding_Util.mkEq uu____13233 in
                           ([[b2t_x]], [xx], uu____13232) in
                         FStar_SMTEncoding_Util.mkForall uu____13226 in
                       (uu____13225, (Some "b2t def"), "b2t_def") in
                     FStar_SMTEncoding_Util.mkAssume uu____13221 in
                   [uu____13220] in
                 (FStar_SMTEncoding_Term.DeclFun
                    (tname, [FStar_SMTEncoding_Term.Term_sort],
                      FStar_SMTEncoding_Term.Term_sort, None))
                   :: uu____13218 in
               (decls, env1))
      | FStar_Syntax_Syntax.Sig_let (uu____13253,uu____13254,uu____13255)
          when
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some
               (fun uu___122_13261  ->
                  match uu___122_13261 with
                  | FStar_Syntax_Syntax.Discriminator uu____13262 -> true
                  | uu____13263 -> false))
          -> ([], env)
      | FStar_Syntax_Syntax.Sig_let (uu____13265,lids,uu____13267) when
          (FStar_All.pipe_right lids
             (FStar_Util.for_some
                (fun l  ->
                   let uu____13274 =
                     let uu____13275 = FStar_List.hd l.FStar_Ident.ns in
                     uu____13275.FStar_Ident.idText in
                   uu____13274 = "Prims")))
            &&
            (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
               (FStar_Util.for_some
                  (fun uu___123_13277  ->
                     match uu___123_13277 with
                     | FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen 
                         -> true
                     | uu____13278 -> false)))
          -> ([], env)
      | FStar_Syntax_Syntax.Sig_let ((false ,lb::[]),uu____13281,uu____13282)
          when
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some
               (fun uu___124_13292  ->
                  match uu___124_13292 with
                  | FStar_Syntax_Syntax.Projector uu____13293 -> true
                  | uu____13296 -> false))
          ->
          let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
          let l = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          let uu____13303 = try_lookup_free_var env l in
          (match uu____13303 with
           | Some uu____13307 -> ([], env)
           | None  ->
               let se1 =
                 let uu___156_13310 = se in
                 {
                   FStar_Syntax_Syntax.sigel =
                     (FStar_Syntax_Syntax.Sig_declare_typ
                        (l, (lb.FStar_Syntax_Syntax.lbunivs),
                          (lb.FStar_Syntax_Syntax.lbtyp)));
                   FStar_Syntax_Syntax.sigrng = (FStar_Ident.range_of_lid l);
                   FStar_Syntax_Syntax.sigquals =
                     (uu___156_13310.FStar_Syntax_Syntax.sigquals);
                   FStar_Syntax_Syntax.sigmeta =
                     (uu___156_13310.FStar_Syntax_Syntax.sigmeta)
                 } in
               encode_sigelt env se1)
      | FStar_Syntax_Syntax.Sig_let
          ((is_rec,bindings),uu____13316,uu____13317) ->
          encode_top_level_let env (is_rec, bindings)
            se.FStar_Syntax_Syntax.sigquals
      | FStar_Syntax_Syntax.Sig_bundle (ses,uu____13329) ->
          let uu____13334 = encode_sigelts env ses in
          (match uu____13334 with
           | (g,env1) ->
               let uu____13344 =
                 FStar_All.pipe_right g
                   (FStar_List.partition
                      (fun uu___125_13354  ->
                         match uu___125_13354 with
                         | FStar_SMTEncoding_Term.Assume
                             {
                               FStar_SMTEncoding_Term.assumption_term =
                                 uu____13355;
                               FStar_SMTEncoding_Term.assumption_caption =
                                 Some "inversion axiom";
                               FStar_SMTEncoding_Term.assumption_name =
                                 uu____13356;
                               FStar_SMTEncoding_Term.assumption_fact_ids =
                                 uu____13357;_}
                             -> false
                         | uu____13359 -> true)) in
               (match uu____13344 with
                | (g',inversions) ->
                    let uu____13368 =
                      FStar_All.pipe_right g'
                        (FStar_List.partition
                           (fun uu___126_13378  ->
                              match uu___126_13378 with
                              | FStar_SMTEncoding_Term.DeclFun uu____13379 ->
                                  true
                              | uu____13385 -> false)) in
                    (match uu____13368 with
                     | (decls,rest) ->
                         ((FStar_List.append decls
                             (FStar_List.append rest inversions)), env1))))
      | FStar_Syntax_Syntax.Sig_inductive_typ
          (t,uu____13396,tps,k,uu____13399,datas) ->
          let quals = se.FStar_Syntax_Syntax.sigquals in
          let is_logical =
            FStar_All.pipe_right quals
              (FStar_Util.for_some
                 (fun uu___127_13409  ->
                    match uu___127_13409 with
                    | FStar_Syntax_Syntax.Logic 
                      |FStar_Syntax_Syntax.Assumption  -> true
                    | uu____13410 -> false)) in
          let constructor_or_logic_type_decl c =
            if is_logical
            then
              let uu____13417 = c in
              match uu____13417 with
              | (name,args,uu____13421,uu____13422,uu____13423) ->
                  let uu____13426 =
                    let uu____13427 =
                      let uu____13433 =
                        FStar_All.pipe_right args
                          (FStar_List.map
                             (fun uu____13440  ->
                                match uu____13440 with
                                | (uu____13444,sort,uu____13446) -> sort)) in
                      (name, uu____13433, FStar_SMTEncoding_Term.Term_sort,
                        None) in
                    FStar_SMTEncoding_Term.DeclFun uu____13427 in
                  [uu____13426]
            else FStar_SMTEncoding_Term.constructor_to_decl c in
          let inversion_axioms tapp vars =
            let uu____13464 =
              FStar_All.pipe_right datas
                (FStar_Util.for_some
                   (fun l  ->
                      let uu____13467 =
                        FStar_TypeChecker_Env.try_lookup_lid env.tcenv l in
                      FStar_All.pipe_right uu____13467 FStar_Option.isNone)) in
            if uu____13464
            then []
            else
              (let uu____13484 =
                 fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort in
               match uu____13484 with
               | (xxsym,xx) ->
                   let uu____13490 =
                     FStar_All.pipe_right datas
                       (FStar_List.fold_left
                          (fun uu____13501  ->
                             fun l  ->
                               match uu____13501 with
                               | (out,decls) ->
                                   let uu____13513 =
                                     FStar_TypeChecker_Env.lookup_datacon
                                       env.tcenv l in
                                   (match uu____13513 with
                                    | (uu____13519,data_t) ->
                                        let uu____13521 =
                                          FStar_Syntax_Util.arrow_formals
                                            data_t in
                                        (match uu____13521 with
                                         | (args,res) ->
                                             let indices =
                                               let uu____13550 =
                                                 let uu____13551 =
                                                   FStar_Syntax_Subst.compress
                                                     res in
                                                 uu____13551.FStar_Syntax_Syntax.n in
                                               match uu____13550 with
                                               | FStar_Syntax_Syntax.Tm_app
                                                   (uu____13559,indices) ->
                                                   indices
                                               | uu____13575 -> [] in
                                             let env1 =
                                               FStar_All.pipe_right args
                                                 (FStar_List.fold_left
                                                    (fun env1  ->
                                                       fun uu____13587  ->
                                                         match uu____13587
                                                         with
                                                         | (x,uu____13591) ->
                                                             let uu____13592
                                                               =
                                                               let uu____13593
                                                                 =
                                                                 let uu____13597
                                                                   =
                                                                   mk_term_projector_name
                                                                    l x in
                                                                 (uu____13597,
                                                                   [xx]) in
                                                               FStar_SMTEncoding_Util.mkApp
                                                                 uu____13593 in
                                                             push_term_var
                                                               env1 x
                                                               uu____13592)
                                                    env) in
                                             let uu____13599 =
                                               encode_args indices env1 in
                                             (match uu____13599 with
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
                                                      let uu____13619 =
                                                        FStar_List.map2
                                                          (fun v1  ->
                                                             fun a  ->
                                                               let uu____13627
                                                                 =
                                                                 let uu____13630
                                                                   =
                                                                   FStar_SMTEncoding_Util.mkFreeV
                                                                    v1 in
                                                                 (uu____13630,
                                                                   a) in
                                                               FStar_SMTEncoding_Util.mkEq
                                                                 uu____13627)
                                                          vars indices1 in
                                                      FStar_All.pipe_right
                                                        uu____13619
                                                        FStar_SMTEncoding_Util.mk_and_l in
                                                    let uu____13632 =
                                                      let uu____13633 =
                                                        let uu____13636 =
                                                          let uu____13637 =
                                                            let uu____13640 =
                                                              mk_data_tester
                                                                env1 l xx in
                                                            (uu____13640,
                                                              eqs) in
                                                          FStar_SMTEncoding_Util.mkAnd
                                                            uu____13637 in
                                                        (out, uu____13636) in
                                                      FStar_SMTEncoding_Util.mkOr
                                                        uu____13633 in
                                                    (uu____13632,
                                                      (FStar_List.append
                                                         decls decls'))))))))
                          (FStar_SMTEncoding_Util.mkFalse, [])) in
                   (match uu____13490 with
                    | (data_ax,decls) ->
                        let uu____13648 =
                          fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort in
                        (match uu____13648 with
                         | (ffsym,ff) ->
                             let fuel_guarded_inversion =
                               let xx_has_type_sfuel =
                                 if
                                   (FStar_List.length datas) >
                                     (Prims.parse_int "1")
                                 then
                                   let uu____13659 =
                                     FStar_SMTEncoding_Util.mkApp
                                       ("SFuel", [ff]) in
                                   FStar_SMTEncoding_Term.mk_HasTypeFuel
                                     uu____13659 xx tapp
                                 else
                                   FStar_SMTEncoding_Term.mk_HasTypeFuel ff
                                     xx tapp in
                               let uu____13662 =
                                 let uu____13666 =
                                   let uu____13667 =
                                     let uu____13673 =
                                       add_fuel
                                         (ffsym,
                                           FStar_SMTEncoding_Term.Fuel_sort)
                                         ((xxsym,
                                            FStar_SMTEncoding_Term.Term_sort)
                                         :: vars) in
                                     let uu____13681 =
                                       FStar_SMTEncoding_Util.mkImp
                                         (xx_has_type_sfuel, data_ax) in
                                     ([[xx_has_type_sfuel]], uu____13673,
                                       uu____13681) in
                                   FStar_SMTEncoding_Util.mkForall
                                     uu____13667 in
                                 let uu____13689 =
                                   varops.mk_unique
                                     (Prims.strcat "fuel_guarded_inversion_"
                                        t.FStar_Ident.str) in
                                 (uu____13666, (Some "inversion axiom"),
                                   uu____13689) in
                               FStar_SMTEncoding_Util.mkAssume uu____13662 in
                             let pattern_guarded_inversion =
                               let uu____13693 =
                                 (contains_name env "Prims.inversion") &&
                                   ((FStar_List.length datas) >
                                      (Prims.parse_int "1")) in
                               if uu____13693
                               then
                                 let xx_has_type_fuel =
                                   FStar_SMTEncoding_Term.mk_HasTypeFuel ff
                                     xx tapp in
                                 let pattern_guard =
                                   FStar_SMTEncoding_Util.mkApp
                                     ("Prims.inversion", [tapp]) in
                                 let uu____13701 =
                                   let uu____13702 =
                                     let uu____13706 =
                                       let uu____13707 =
                                         let uu____13713 =
                                           add_fuel
                                             (ffsym,
                                               FStar_SMTEncoding_Term.Fuel_sort)
                                             ((xxsym,
                                                FStar_SMTEncoding_Term.Term_sort)
                                             :: vars) in
                                         let uu____13721 =
                                           FStar_SMTEncoding_Util.mkImp
                                             (xx_has_type_fuel, data_ax) in
                                         ([[xx_has_type_fuel; pattern_guard]],
                                           uu____13713, uu____13721) in
                                       FStar_SMTEncoding_Util.mkForall
                                         uu____13707 in
                                     let uu____13729 =
                                       varops.mk_unique
                                         (Prims.strcat
                                            "pattern_guarded_inversion_"
                                            t.FStar_Ident.str) in
                                     (uu____13706, (Some "inversion axiom"),
                                       uu____13729) in
                                   FStar_SMTEncoding_Util.mkAssume
                                     uu____13702 in
                                 [uu____13701]
                               else [] in
                             FStar_List.append decls
                               (FStar_List.append [fuel_guarded_inversion]
                                  pattern_guarded_inversion)))) in
          let uu____13732 =
            let uu____13740 =
              let uu____13741 = FStar_Syntax_Subst.compress k in
              uu____13741.FStar_Syntax_Syntax.n in
            match uu____13740 with
            | FStar_Syntax_Syntax.Tm_arrow (formals,kres) ->
                ((FStar_List.append tps formals),
                  (FStar_Syntax_Util.comp_result kres))
            | uu____13770 -> (tps, k) in
          (match uu____13732 with
           | (formals,res) ->
               let uu____13785 = FStar_Syntax_Subst.open_term formals res in
               (match uu____13785 with
                | (formals1,res1) ->
                    let uu____13792 = encode_binders None formals1 env in
                    (match uu____13792 with
                     | (vars,guards,env',binder_decls,uu____13807) ->
                         let uu____13814 =
                           new_term_constant_and_tok_from_lid env t in
                         (match uu____13814 with
                          | (tname,ttok,env1) ->
                              let ttok_tm =
                                FStar_SMTEncoding_Util.mkApp (ttok, []) in
                              let guard =
                                FStar_SMTEncoding_Util.mk_and_l guards in
                              let tapp =
                                let uu____13827 =
                                  let uu____13831 =
                                    FStar_List.map
                                      FStar_SMTEncoding_Util.mkFreeV vars in
                                  (tname, uu____13831) in
                                FStar_SMTEncoding_Util.mkApp uu____13827 in
                              let uu____13836 =
                                let tname_decl =
                                  let uu____13842 =
                                    let uu____13843 =
                                      FStar_All.pipe_right vars
                                        (FStar_List.map
                                           (fun uu____13858  ->
                                              match uu____13858 with
                                              | (n1,s) ->
                                                  ((Prims.strcat tname n1),
                                                    s, false))) in
                                    let uu____13866 = varops.next_id () in
                                    (tname, uu____13843,
                                      FStar_SMTEncoding_Term.Term_sort,
                                      uu____13866, false) in
                                  constructor_or_logic_type_decl uu____13842 in
                                let uu____13871 =
                                  match vars with
                                  | [] ->
                                      let uu____13878 =
                                        let uu____13879 =
                                          let uu____13881 =
                                            FStar_SMTEncoding_Util.mkApp
                                              (tname, []) in
                                          FStar_All.pipe_left
                                            (fun _0_38  -> Some _0_38)
                                            uu____13881 in
                                        push_free_var env1 t tname
                                          uu____13879 in
                                      ([], uu____13878)
                                  | uu____13885 ->
                                      let ttok_decl =
                                        FStar_SMTEncoding_Term.DeclFun
                                          (ttok, [],
                                            FStar_SMTEncoding_Term.Term_sort,
                                            (Some "token")) in
                                      let ttok_fresh =
                                        let uu____13891 = varops.next_id () in
                                        FStar_SMTEncoding_Term.fresh_token
                                          (ttok,
                                            FStar_SMTEncoding_Term.Term_sort)
                                          uu____13891 in
                                      let ttok_app = mk_Apply ttok_tm vars in
                                      let pats = [[ttok_app]; [tapp]] in
                                      let name_tok_corr =
                                        let uu____13900 =
                                          let uu____13904 =
                                            let uu____13905 =
                                              let uu____13913 =
                                                FStar_SMTEncoding_Util.mkEq
                                                  (ttok_app, tapp) in
                                              (pats, None, vars, uu____13913) in
                                            FStar_SMTEncoding_Util.mkForall'
                                              uu____13905 in
                                          (uu____13904,
                                            (Some "name-token correspondence"),
                                            (Prims.strcat
                                               "token_correspondence_" ttok)) in
                                        FStar_SMTEncoding_Util.mkAssume
                                          uu____13900 in
                                      ([ttok_decl; ttok_fresh; name_tok_corr],
                                        env1) in
                                match uu____13871 with
                                | (tok_decls,env2) ->
                                    ((FStar_List.append tname_decl tok_decls),
                                      env2) in
                              (match uu____13836 with
                               | (decls,env2) ->
                                   let kindingAx =
                                     let uu____13936 =
                                       encode_term_pred None res1 env' tapp in
                                     match uu____13936 with
                                     | (k1,decls1) ->
                                         let karr =
                                           if
                                             (FStar_List.length formals1) >
                                               (Prims.parse_int "0")
                                           then
                                             let uu____13950 =
                                               let uu____13951 =
                                                 let uu____13955 =
                                                   let uu____13956 =
                                                     FStar_SMTEncoding_Term.mk_PreType
                                                       ttok_tm in
                                                   FStar_SMTEncoding_Term.mk_tester
                                                     "Tm_arrow" uu____13956 in
                                                 (uu____13955,
                                                   (Some "kinding"),
                                                   (Prims.strcat
                                                      "pre_kinding_" ttok)) in
                                               FStar_SMTEncoding_Util.mkAssume
                                                 uu____13951 in
                                             [uu____13950]
                                           else [] in
                                         let uu____13959 =
                                           let uu____13961 =
                                             let uu____13963 =
                                               let uu____13964 =
                                                 let uu____13968 =
                                                   let uu____13969 =
                                                     let uu____13975 =
                                                       FStar_SMTEncoding_Util.mkImp
                                                         (guard, k1) in
                                                     ([[tapp]], vars,
                                                       uu____13975) in
                                                   FStar_SMTEncoding_Util.mkForall
                                                     uu____13969 in
                                                 (uu____13968, None,
                                                   (Prims.strcat "kinding_"
                                                      ttok)) in
                                               FStar_SMTEncoding_Util.mkAssume
                                                 uu____13964 in
                                             [uu____13963] in
                                           FStar_List.append karr uu____13961 in
                                         FStar_List.append decls1 uu____13959 in
                                   let aux =
                                     let uu____13984 =
                                       let uu____13986 =
                                         inversion_axioms tapp vars in
                                       let uu____13988 =
                                         let uu____13990 =
                                           pretype_axiom env2 tapp vars in
                                         [uu____13990] in
                                       FStar_List.append uu____13986
                                         uu____13988 in
                                     FStar_List.append kindingAx uu____13984 in
                                   let g =
                                     FStar_List.append decls
                                       (FStar_List.append binder_decls aux) in
                                   (g, env2))))))
      | FStar_Syntax_Syntax.Sig_datacon
          (d,uu____13995,uu____13996,uu____13997,uu____13998,uu____13999)
          when FStar_Ident.lid_equals d FStar_Syntax_Const.lexcons_lid ->
          ([], env)
      | FStar_Syntax_Syntax.Sig_datacon
          (d,uu____14004,t,uu____14006,n_tps,uu____14008) ->
          let quals = se.FStar_Syntax_Syntax.sigquals in
          let uu____14013 = new_term_constant_and_tok_from_lid env d in
          (match uu____14013 with
           | (ddconstrsym,ddtok,env1) ->
               let ddtok_tm = FStar_SMTEncoding_Util.mkApp (ddtok, []) in
               let uu____14024 = FStar_Syntax_Util.arrow_formals t in
               (match uu____14024 with
                | (formals,t_res) ->
                    let uu____14046 =
                      fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort in
                    (match uu____14046 with
                     | (fuel_var,fuel_tm) ->
                         let s_fuel_tm =
                           FStar_SMTEncoding_Util.mkApp ("SFuel", [fuel_tm]) in
                         let uu____14055 =
                           encode_binders (Some fuel_tm) formals env1 in
                         (match uu____14055 with
                          | (vars,guards,env',binder_decls,names1) ->
                              let fields =
                                FStar_All.pipe_right names1
                                  (FStar_List.mapi
                                     (fun n1  ->
                                        fun x  ->
                                          let projectible = true in
                                          let uu____14093 =
                                            mk_term_projector_name d x in
                                          (uu____14093,
                                            FStar_SMTEncoding_Term.Term_sort,
                                            projectible))) in
                              let datacons =
                                let uu____14095 =
                                  let uu____14105 = varops.next_id () in
                                  (ddconstrsym, fields,
                                    FStar_SMTEncoding_Term.Term_sort,
                                    uu____14105, true) in
                                FStar_All.pipe_right uu____14095
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
                              let uu____14127 =
                                encode_term_pred None t env1 ddtok_tm in
                              (match uu____14127 with
                               | (tok_typing,decls3) ->
                                   let tok_typing1 =
                                     match fields with
                                     | uu____14135::uu____14136 ->
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
                                         let uu____14161 =
                                           let uu____14167 =
                                             FStar_SMTEncoding_Term.mk_NoHoist
                                               f tok_typing in
                                           ([[vtok_app_l]; [vtok_app_r]],
                                             [ff], uu____14167) in
                                         FStar_SMTEncoding_Util.mkForall
                                           uu____14161
                                     | uu____14180 -> tok_typing in
                                   let uu____14185 =
                                     encode_binders (Some fuel_tm) formals
                                       env1 in
                                   (match uu____14185 with
                                    | (vars',guards',env'',decls_formals,uu____14200)
                                        ->
                                        let uu____14207 =
                                          let xvars1 =
                                            FStar_List.map
                                              FStar_SMTEncoding_Util.mkFreeV
                                              vars' in
                                          let dapp1 =
                                            FStar_SMTEncoding_Util.mkApp
                                              (ddconstrsym, xvars1) in
                                          encode_term_pred (Some fuel_tm)
                                            t_res env'' dapp1 in
                                        (match uu____14207 with
                                         | (ty_pred',decls_pred) ->
                                             let guard' =
                                               FStar_SMTEncoding_Util.mk_and_l
                                                 guards' in
                                             let proxy_fresh =
                                               match formals with
                                               | [] -> []
                                               | uu____14226 ->
                                                   let uu____14230 =
                                                     let uu____14231 =
                                                       varops.next_id () in
                                                     FStar_SMTEncoding_Term.fresh_token
                                                       (ddtok,
                                                         FStar_SMTEncoding_Term.Term_sort)
                                                       uu____14231 in
                                                   [uu____14230] in
                                             let encode_elim uu____14238 =
                                               let uu____14239 =
                                                 FStar_Syntax_Util.head_and_args
                                                   t_res in
                                               match uu____14239 with
                                               | (head1,args) ->
                                                   let uu____14268 =
                                                     let uu____14269 =
                                                       FStar_Syntax_Subst.compress
                                                         head1 in
                                                     uu____14269.FStar_Syntax_Syntax.n in
                                                   (match uu____14268 with
                                                    | FStar_Syntax_Syntax.Tm_uinst
                                                      ({
                                                         FStar_Syntax_Syntax.n
                                                           =
                                                           FStar_Syntax_Syntax.Tm_fvar
                                                           fv;
                                                         FStar_Syntax_Syntax.tk
                                                           = _;
                                                         FStar_Syntax_Syntax.pos
                                                           = _;
                                                         FStar_Syntax_Syntax.vars
                                                           = _;_},_)
                                                      |FStar_Syntax_Syntax.Tm_fvar
                                                      fv ->
                                                        let encoded_head =
                                                          lookup_free_var_name
                                                            env'
                                                            fv.FStar_Syntax_Syntax.fv_name in
                                                        let uu____14287 =
                                                          encode_args args
                                                            env' in
                                                        (match uu____14287
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
                                                                 | uu____14313
                                                                    ->
                                                                    failwith
                                                                    "Impossible: parameter must be a variable" in
                                                               let guards1 =
                                                                 FStar_All.pipe_right
                                                                   guards
                                                                   (FStar_List.collect
                                                                    (fun g 
                                                                    ->
                                                                    let uu____14321
                                                                    =
                                                                    let uu____14322
                                                                    =
                                                                    FStar_SMTEncoding_Term.free_variables
                                                                    g in
                                                                    FStar_List.contains
                                                                    fv1
                                                                    uu____14322 in
                                                                    if
                                                                    uu____14321
                                                                    then
                                                                    let uu____14329
                                                                    =
                                                                    FStar_SMTEncoding_Term.subst
                                                                    g fv1 xv in
                                                                    [uu____14329]
                                                                    else [])) in
                                                               FStar_SMTEncoding_Util.mk_and_l
                                                                 guards1 in
                                                             let uu____14331
                                                               =
                                                               FStar_List.fold_left
                                                                 (fun
                                                                    uu____14344
                                                                     ->
                                                                    fun arg 
                                                                    ->
                                                                    match uu____14344
                                                                    with
                                                                    | 
                                                                    (env2,arg_vars,eqns_or_guards,i)
                                                                    ->
                                                                    let uu____14366
                                                                    =
                                                                    let uu____14370
                                                                    =
                                                                    FStar_Syntax_Syntax.new_bv
                                                                    None
                                                                    FStar_Syntax_Syntax.tun in
                                                                    gen_term_var
                                                                    env2
                                                                    uu____14370 in
                                                                    (match uu____14366
                                                                    with
                                                                    | 
                                                                    (uu____14377,xv,env3)
                                                                    ->
                                                                    let eqns
                                                                    =
                                                                    if
                                                                    i < n_tps
                                                                    then
                                                                    let uu____14383
                                                                    =
                                                                    guards_for_parameter
                                                                    arg xv in
                                                                    uu____14383
                                                                    ::
                                                                    eqns_or_guards
                                                                    else
                                                                    (let uu____14385
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (arg, xv) in
                                                                    uu____14385
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
                                                             (match uu____14331
                                                              with
                                                              | (uu____14393,arg_vars,elim_eqns_or_guards,uu____14396)
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
                                                                    let uu____14415
                                                                    =
                                                                    let uu____14419
                                                                    =
                                                                    let uu____14420
                                                                    =
                                                                    let uu____14426
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders) in
                                                                    let uu____14432
                                                                    =
                                                                    let uu____14433
                                                                    =
                                                                    let uu____14436
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    (FStar_List.append
                                                                    elim_eqns_or_guards
                                                                    guards) in
                                                                    (ty_pred,
                                                                    uu____14436) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____14433 in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____14426,
                                                                    uu____14432) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____14420 in
                                                                    (uu____14419,
                                                                    (Some
                                                                    "data constructor typing elim"),
                                                                    (Prims.strcat
                                                                    "data_elim_"
                                                                    ddconstrsym)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____14415 in
                                                                  let subterm_ordering
                                                                    =
                                                                    if
                                                                    FStar_Ident.lid_equals
                                                                    d
                                                                    FStar_Syntax_Const.lextop_lid
                                                                    then
                                                                    let x =
                                                                    let uu____14449
                                                                    =
                                                                    varops.fresh
                                                                    "x" in
                                                                    (uu____14449,
                                                                    FStar_SMTEncoding_Term.Term_sort) in
                                                                    let xtm =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    x in
                                                                    let uu____14451
                                                                    =
                                                                    let uu____14455
                                                                    =
                                                                    let uu____14456
                                                                    =
                                                                    let uu____14462
                                                                    =
                                                                    let uu____14465
                                                                    =
                                                                    let uu____14467
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp1 in
                                                                    [uu____14467] in
                                                                    [uu____14465] in
                                                                    let uu____14470
                                                                    =
                                                                    let uu____14471
                                                                    =
                                                                    let uu____14474
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_tester
                                                                    "LexCons"
                                                                    xtm in
                                                                    let uu____14475
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp1 in
                                                                    (uu____14474,
                                                                    uu____14475) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____14471 in
                                                                    (uu____14462,
                                                                    [x],
                                                                    uu____14470) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____14456 in
                                                                    let uu____14485
                                                                    =
                                                                    varops.mk_unique
                                                                    "lextop" in
                                                                    (uu____14455,
                                                                    (Some
                                                                    "lextop is top"),
                                                                    uu____14485) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____14451
                                                                    else
                                                                    (let prec
                                                                    =
                                                                    let uu____14490
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
                                                                    (let uu____14505
                                                                    =
                                                                    let uu____14506
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    v1 in
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    uu____14506
                                                                    dapp1 in
                                                                    [uu____14505]))) in
                                                                    FStar_All.pipe_right
                                                                    uu____14490
                                                                    FStar_List.flatten in
                                                                    let uu____14510
                                                                    =
                                                                    let uu____14514
                                                                    =
                                                                    let uu____14515
                                                                    =
                                                                    let uu____14521
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders) in
                                                                    let uu____14527
                                                                    =
                                                                    let uu____14528
                                                                    =
                                                                    let uu____14531
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    prec in
                                                                    (ty_pred,
                                                                    uu____14531) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____14528 in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____14521,
                                                                    uu____14527) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____14515 in
                                                                    (uu____14514,
                                                                    (Some
                                                                    "subterm ordering"),
                                                                    (Prims.strcat
                                                                    "subterm_ordering_"
                                                                    ddconstrsym)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____14510) in
                                                                  (arg_decls,
                                                                    [typing_inversion;
                                                                    subterm_ordering])))
                                                    | uu____14541 ->
                                                        ((let uu____14543 =
                                                            let uu____14544 =
                                                              FStar_Syntax_Print.lid_to_string
                                                                d in
                                                            let uu____14545 =
                                                              FStar_Syntax_Print.term_to_string
                                                                head1 in
                                                            FStar_Util.format2
                                                              "Constructor %s builds an unexpected type %s\n"
                                                              uu____14544
                                                              uu____14545 in
                                                          FStar_Errors.warn
                                                            se.FStar_Syntax_Syntax.sigrng
                                                            uu____14543);
                                                         ([], []))) in
                                             let uu____14548 = encode_elim () in
                                             (match uu____14548 with
                                              | (decls2,elim) ->
                                                  let g =
                                                    let uu____14560 =
                                                      let uu____14562 =
                                                        let uu____14564 =
                                                          let uu____14566 =
                                                            let uu____14568 =
                                                              let uu____14569
                                                                =
                                                                let uu____14575
                                                                  =
                                                                  let uu____14577
                                                                    =
                                                                    let uu____14578
                                                                    =
                                                                    FStar_Syntax_Print.lid_to_string
                                                                    d in
                                                                    FStar_Util.format1
                                                                    "data constructor proxy: %s"
                                                                    uu____14578 in
                                                                  Some
                                                                    uu____14577 in
                                                                (ddtok, [],
                                                                  FStar_SMTEncoding_Term.Term_sort,
                                                                  uu____14575) in
                                                              FStar_SMTEncoding_Term.DeclFun
                                                                uu____14569 in
                                                            [uu____14568] in
                                                          let uu____14581 =
                                                            let uu____14583 =
                                                              let uu____14585
                                                                =
                                                                let uu____14587
                                                                  =
                                                                  let uu____14589
                                                                    =
                                                                    let uu____14591
                                                                    =
                                                                    let uu____14593
                                                                    =
                                                                    let uu____14594
                                                                    =
                                                                    let uu____14598
                                                                    =
                                                                    let uu____14599
                                                                    =
                                                                    let uu____14605
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (app,
                                                                    dapp) in
                                                                    ([[app]],
                                                                    vars,
                                                                    uu____14605) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____14599 in
                                                                    (uu____14598,
                                                                    (Some
                                                                    "equality for proxy"),
                                                                    (Prims.strcat
                                                                    "equality_tok_"
                                                                    ddtok)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____14594 in
                                                                    let uu____14612
                                                                    =
                                                                    let uu____14614
                                                                    =
                                                                    let uu____14615
                                                                    =
                                                                    let uu____14619
                                                                    =
                                                                    let uu____14620
                                                                    =
                                                                    let uu____14626
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    vars' in
                                                                    let uu____14632
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    (guard',
                                                                    ty_pred') in
                                                                    ([
                                                                    [ty_pred']],
                                                                    uu____14626,
                                                                    uu____14632) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____14620 in
                                                                    (uu____14619,
                                                                    (Some
                                                                    "data constructor typing intro"),
                                                                    (Prims.strcat
                                                                    "data_typing_intro_"
                                                                    ddtok)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____14615 in
                                                                    [uu____14614] in
                                                                    uu____14593
                                                                    ::
                                                                    uu____14612 in
                                                                    (FStar_SMTEncoding_Util.mkAssume
                                                                    (tok_typing1,
                                                                    (Some
                                                                    "typing for data constructor proxy"),
                                                                    (Prims.strcat
                                                                    "typing_tok_"
                                                                    ddtok)))
                                                                    ::
                                                                    uu____14591 in
                                                                  FStar_List.append
                                                                    uu____14589
                                                                    elim in
                                                                FStar_List.append
                                                                  decls_pred
                                                                  uu____14587 in
                                                              FStar_List.append
                                                                decls_formals
                                                                uu____14585 in
                                                            FStar_List.append
                                                              proxy_fresh
                                                              uu____14583 in
                                                          FStar_List.append
                                                            uu____14566
                                                            uu____14581 in
                                                        FStar_List.append
                                                          decls3 uu____14564 in
                                                      FStar_List.append
                                                        decls2 uu____14562 in
                                                    FStar_List.append
                                                      binder_decls
                                                      uu____14560 in
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
           (fun uu____14653  ->
              fun se  ->
                match uu____14653 with
                | (g,env1) ->
                    let uu____14665 = encode_sigelt env1 se in
                    (match uu____14665 with
                     | (g',env2) -> ((FStar_List.append g g'), env2)))
           ([], env))
let encode_env_bindings:
  env_t ->
    FStar_TypeChecker_Env.binding Prims.list ->
      (FStar_SMTEncoding_Term.decls_t* env_t)
  =
  fun env  ->
    fun bindings  ->
      let encode_binding b uu____14701 =
        match uu____14701 with
        | (i,decls,env1) ->
            (match b with
             | FStar_TypeChecker_Env.Binding_univ uu____14719 ->
                 ((i + (Prims.parse_int "1")), [], env1)
             | FStar_TypeChecker_Env.Binding_var x ->
                 let t1 =
                   FStar_TypeChecker_Normalize.normalize
                     [FStar_TypeChecker_Normalize.Beta;
                     FStar_TypeChecker_Normalize.Eager_unfolding;
                     FStar_TypeChecker_Normalize.Simplify;
                     FStar_TypeChecker_Normalize.EraseUniverses] env1.tcenv
                     x.FStar_Syntax_Syntax.sort in
                 ((let uu____14724 =
                     FStar_All.pipe_left
                       (FStar_TypeChecker_Env.debug env1.tcenv)
                       (FStar_Options.Other "SMTEncoding") in
                   if uu____14724
                   then
                     let uu____14725 = FStar_Syntax_Print.bv_to_string x in
                     let uu____14726 =
                       FStar_Syntax_Print.term_to_string
                         x.FStar_Syntax_Syntax.sort in
                     let uu____14727 = FStar_Syntax_Print.term_to_string t1 in
                     FStar_Util.print3 "Normalized %s : %s to %s\n"
                       uu____14725 uu____14726 uu____14727
                   else ());
                  (let uu____14729 = encode_term t1 env1 in
                   match uu____14729 with
                   | (t,decls') ->
                       let t_hash = FStar_SMTEncoding_Term.hash_of_term t in
                       let uu____14739 =
                         let uu____14743 =
                           let uu____14744 =
                             let uu____14745 =
                               FStar_Util.digest_of_string t_hash in
                             Prims.strcat uu____14745
                               (Prims.strcat "_" (Prims.string_of_int i)) in
                           Prims.strcat "x_" uu____14744 in
                         new_term_constant_from_string env1 x uu____14743 in
                       (match uu____14739 with
                        | (xxsym,xx,env') ->
                            let t2 =
                              FStar_SMTEncoding_Term.mk_HasTypeWithFuel None
                                xx t in
                            let caption =
                              let uu____14756 = FStar_Options.log_queries () in
                              if uu____14756
                              then
                                let uu____14758 =
                                  let uu____14759 =
                                    FStar_Syntax_Print.bv_to_string x in
                                  let uu____14760 =
                                    FStar_Syntax_Print.term_to_string
                                      x.FStar_Syntax_Syntax.sort in
                                  let uu____14761 =
                                    FStar_Syntax_Print.term_to_string t1 in
                                  FStar_Util.format3 "%s : %s (%s)"
                                    uu____14759 uu____14760 uu____14761 in
                                Some uu____14758
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
             | FStar_TypeChecker_Env.Binding_lid (x,(uu____14772,t)) ->
                 let t_norm = whnf env1 t in
                 let fv =
                   FStar_Syntax_Syntax.lid_as_fv x
                     FStar_Syntax_Syntax.Delta_constant None in
                 let uu____14781 = encode_free_var env1 fv t t_norm [] in
                 (match uu____14781 with
                  | (g,env') ->
                      ((i + (Prims.parse_int "1")),
                        (FStar_List.append decls g), env'))
             | FStar_TypeChecker_Env.Binding_sig_inst (_,se,_)
               |FStar_TypeChecker_Env.Binding_sig (_,se) ->
                 let uu____14800 = encode_sigelt env1 se in
                 (match uu____14800 with
                  | (g,env') ->
                      ((i + (Prims.parse_int "1")),
                        (FStar_List.append decls g), env'))) in
      let uu____14810 =
        FStar_List.fold_right encode_binding bindings
          ((Prims.parse_int "0"), [], env) in
      match uu____14810 with | (uu____14822,decls,env1) -> (decls, env1)
let encode_labels labs =
  let prefix1 =
    FStar_All.pipe_right labs
      (FStar_List.map
         (fun uu____14867  ->
            match uu____14867 with
            | (l,uu____14874,uu____14875) ->
                FStar_SMTEncoding_Term.DeclFun
                  ((Prims.fst l), [], FStar_SMTEncoding_Term.Bool_sort, None))) in
  let suffix =
    FStar_All.pipe_right labs
      (FStar_List.collect
         (fun uu____14896  ->
            match uu____14896 with
            | (l,uu____14904,uu____14905) ->
                let uu____14910 =
                  FStar_All.pipe_left
                    (fun _0_39  -> FStar_SMTEncoding_Term.Echo _0_39)
                    (Prims.fst l) in
                let uu____14911 =
                  let uu____14913 =
                    let uu____14914 = FStar_SMTEncoding_Util.mkFreeV l in
                    FStar_SMTEncoding_Term.Eval uu____14914 in
                  [uu____14913] in
                uu____14910 :: uu____14911)) in
  (prefix1, suffix)
let last_env: env_t Prims.list FStar_ST.ref = FStar_Util.mk_ref []
let init_env: FStar_TypeChecker_Env.env -> Prims.unit =
  fun tcenv  ->
    let uu____14925 =
      let uu____14927 =
        let uu____14928 = FStar_Util.smap_create (Prims.parse_int "100") in
        let uu____14930 =
          let uu____14931 = FStar_TypeChecker_Env.current_module tcenv in
          FStar_All.pipe_right uu____14931 FStar_Ident.string_of_lid in
        {
          bindings = [];
          depth = (Prims.parse_int "0");
          tcenv;
          warn = true;
          cache = uu____14928;
          nolabels = false;
          use_zfuel_name = false;
          encode_non_total_function_typ = true;
          current_module_name = uu____14930
        } in
      [uu____14927] in
    FStar_ST.write last_env uu____14925
let get_env: FStar_Ident.lident -> FStar_TypeChecker_Env.env -> env_t =
  fun cmn  ->
    fun tcenv  ->
      let uu____14941 = FStar_ST.read last_env in
      match uu____14941 with
      | [] -> failwith "No env; call init first!"
      | e::uu____14947 ->
          let uu___157_14949 = e in
          let uu____14950 = FStar_Ident.string_of_lid cmn in
          {
            bindings = (uu___157_14949.bindings);
            depth = (uu___157_14949.depth);
            tcenv;
            warn = (uu___157_14949.warn);
            cache = (uu___157_14949.cache);
            nolabels = (uu___157_14949.nolabels);
            use_zfuel_name = (uu___157_14949.use_zfuel_name);
            encode_non_total_function_typ =
              (uu___157_14949.encode_non_total_function_typ);
            current_module_name = uu____14950
          }
let set_env: env_t -> Prims.unit =
  fun env  ->
    let uu____14954 = FStar_ST.read last_env in
    match uu____14954 with
    | [] -> failwith "Empty env stack"
    | uu____14959::tl1 -> FStar_ST.write last_env (env :: tl1)
let push_env: Prims.unit -> Prims.unit =
  fun uu____14967  ->
    let uu____14968 = FStar_ST.read last_env in
    match uu____14968 with
    | [] -> failwith "Empty env stack"
    | hd1::tl1 ->
        let refs = FStar_Util.smap_copy hd1.cache in
        let top =
          let uu___158_14979 = hd1 in
          {
            bindings = (uu___158_14979.bindings);
            depth = (uu___158_14979.depth);
            tcenv = (uu___158_14979.tcenv);
            warn = (uu___158_14979.warn);
            cache = refs;
            nolabels = (uu___158_14979.nolabels);
            use_zfuel_name = (uu___158_14979.use_zfuel_name);
            encode_non_total_function_typ =
              (uu___158_14979.encode_non_total_function_typ);
            current_module_name = (uu___158_14979.current_module_name)
          } in
        FStar_ST.write last_env (top :: hd1 :: tl1)
let pop_env: Prims.unit -> Prims.unit =
  fun uu____14985  ->
    let uu____14986 = FStar_ST.read last_env in
    match uu____14986 with
    | [] -> failwith "Popping an empty stack"
    | uu____14991::tl1 -> FStar_ST.write last_env tl1
let mark_env: Prims.unit -> Prims.unit = fun uu____14999  -> push_env ()
let reset_mark_env: Prims.unit -> Prims.unit = fun uu____15002  -> pop_env ()
let commit_mark_env: Prims.unit -> Prims.unit =
  fun uu____15005  ->
    let uu____15006 = FStar_ST.read last_env in
    match uu____15006 with
    | hd1::uu____15012::tl1 -> FStar_ST.write last_env (hd1 :: tl1)
    | uu____15018 -> failwith "Impossible"
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
        | (uu____15067::uu____15068,FStar_SMTEncoding_Term.Assume a) ->
            FStar_SMTEncoding_Term.Assume
              (let uu___159_15072 = a in
               {
                 FStar_SMTEncoding_Term.assumption_term =
                   (uu___159_15072.FStar_SMTEncoding_Term.assumption_term);
                 FStar_SMTEncoding_Term.assumption_caption =
                   (uu___159_15072.FStar_SMTEncoding_Term.assumption_caption);
                 FStar_SMTEncoding_Term.assumption_name =
                   (uu___159_15072.FStar_SMTEncoding_Term.assumption_name);
                 FStar_SMTEncoding_Term.assumption_fact_ids = fact_db_ids
               })
        | uu____15073 -> d
let fact_dbs_for_lid:
  env_t -> FStar_Ident.lid -> FStar_SMTEncoding_Term.fact_db_id Prims.list =
  fun env  ->
    fun lid  ->
      let uu____15084 =
        let uu____15086 =
          let uu____15087 = FStar_Ident.lid_of_ids lid.FStar_Ident.ns in
          FStar_SMTEncoding_Term.Namespace uu____15087 in
        let uu____15088 = open_fact_db_tags env in uu____15086 :: uu____15088 in
      (FStar_SMTEncoding_Term.Name lid) :: uu____15084
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
      let uu____15103 = encode_sigelt env se in
      match uu____15103 with
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
        let uu____15128 = FStar_Options.log_queries () in
        if uu____15128
        then
          let uu____15130 =
            let uu____15131 =
              let uu____15132 =
                let uu____15133 =
                  FStar_All.pipe_right (FStar_Syntax_Util.lids_of_sigelt se)
                    (FStar_List.map FStar_Syntax_Print.lid_to_string) in
                FStar_All.pipe_right uu____15133 (FStar_String.concat ", ") in
              Prims.strcat "encoding sigelt " uu____15132 in
            FStar_SMTEncoding_Term.Caption uu____15131 in
          uu____15130 :: decls
        else decls in
      let env =
        let uu____15140 = FStar_TypeChecker_Env.current_module tcenv in
        get_env uu____15140 tcenv in
      let uu____15141 = encode_top_level_facts env se in
      match uu____15141 with
      | (decls,env1) ->
          (set_env env1;
           (let uu____15150 = caption decls in
            FStar_SMTEncoding_Z3.giveZ3 uu____15150))
let encode_modul:
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.modul -> Prims.unit =
  fun tcenv  ->
    fun modul  ->
      let name =
        FStar_Util.format2 "%s %s"
          (if modul.FStar_Syntax_Syntax.is_interface
           then "interface"
           else "module") (modul.FStar_Syntax_Syntax.name).FStar_Ident.str in
      (let uu____15161 = FStar_TypeChecker_Env.debug tcenv FStar_Options.Low in
       if uu____15161
       then
         let uu____15162 =
           FStar_All.pipe_right
             (FStar_List.length modul.FStar_Syntax_Syntax.exports)
             Prims.string_of_int in
         FStar_Util.print2
           "+++++++++++Encoding externals for %s ... %s exports\n" name
           uu____15162
       else ());
      (let env = get_env modul.FStar_Syntax_Syntax.name tcenv in
       let encode_signature env1 ses =
         FStar_All.pipe_right ses
           (FStar_List.fold_left
              (fun uu____15183  ->
                 fun se  ->
                   match uu____15183 with
                   | (g,env2) ->
                       let uu____15195 = encode_top_level_facts env2 se in
                       (match uu____15195 with
                        | (g',env3) -> ((FStar_List.append g g'), env3)))
              ([], env1)) in
       let uu____15208 =
         encode_signature
           (let uu___160_15212 = env in
            {
              bindings = (uu___160_15212.bindings);
              depth = (uu___160_15212.depth);
              tcenv = (uu___160_15212.tcenv);
              warn = false;
              cache = (uu___160_15212.cache);
              nolabels = (uu___160_15212.nolabels);
              use_zfuel_name = (uu___160_15212.use_zfuel_name);
              encode_non_total_function_typ =
                (uu___160_15212.encode_non_total_function_typ);
              current_module_name = (uu___160_15212.current_module_name)
            }) modul.FStar_Syntax_Syntax.exports in
       match uu____15208 with
       | (decls,env1) ->
           let caption decls1 =
             let uu____15224 = FStar_Options.log_queries () in
             if uu____15224
             then
               let msg = Prims.strcat "Externals for " name in
               FStar_List.append ((FStar_SMTEncoding_Term.Caption msg) ::
                 decls1)
                 [FStar_SMTEncoding_Term.Caption (Prims.strcat "End " msg)]
             else decls1 in
           (set_env
              (let uu___161_15229 = env1 in
               {
                 bindings = (uu___161_15229.bindings);
                 depth = (uu___161_15229.depth);
                 tcenv = (uu___161_15229.tcenv);
                 warn = true;
                 cache = (uu___161_15229.cache);
                 nolabels = (uu___161_15229.nolabels);
                 use_zfuel_name = (uu___161_15229.use_zfuel_name);
                 encode_non_total_function_typ =
                   (uu___161_15229.encode_non_total_function_typ);
                 current_module_name = (uu___161_15229.current_module_name)
               });
            (let uu____15231 =
               FStar_TypeChecker_Env.debug tcenv FStar_Options.Low in
             if uu____15231
             then FStar_Util.print1 "Done encoding externals for %s\n" name
             else ());
            (let decls1 = caption decls in FStar_SMTEncoding_Z3.giveZ3 decls1)))
let encode_query:
  (Prims.unit -> Prims.string) Prims.option ->
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
        (let uu____15266 =
           let uu____15267 = FStar_TypeChecker_Env.current_module tcenv in
           uu____15267.FStar_Ident.str in
         FStar_SMTEncoding_Z3.query_logging.FStar_SMTEncoding_Z3.set_module_name
           uu____15266);
        (let env =
           let uu____15269 = FStar_TypeChecker_Env.current_module tcenv in
           get_env uu____15269 tcenv in
         let bindings =
           FStar_TypeChecker_Env.fold_env tcenv
             (fun bs  -> fun b  -> b :: bs) [] in
         let uu____15276 =
           let rec aux bindings1 =
             match bindings1 with
             | (FStar_TypeChecker_Env.Binding_var x)::rest ->
                 let uu____15297 = aux rest in
                 (match uu____15297 with
                  | (out,rest1) ->
                      let t =
                        let uu____15315 =
                          FStar_Syntax_Util.destruct_typ_as_formula
                            x.FStar_Syntax_Syntax.sort in
                        match uu____15315 with
                        | Some uu____15319 ->
                            let uu____15320 =
                              FStar_Syntax_Syntax.new_bv None
                                FStar_TypeChecker_Common.t_unit in
                            FStar_Syntax_Util.refine uu____15320
                              x.FStar_Syntax_Syntax.sort
                        | uu____15321 -> x.FStar_Syntax_Syntax.sort in
                      let t1 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Normalize.Eager_unfolding;
                          FStar_TypeChecker_Normalize.Beta;
                          FStar_TypeChecker_Normalize.Simplify;
                          FStar_TypeChecker_Normalize.EraseUniverses]
                          env.tcenv t in
                      let uu____15324 =
                        let uu____15326 =
                          FStar_Syntax_Syntax.mk_binder
                            (let uu___162_15327 = x in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___162_15327.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___162_15327.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = t1
                             }) in
                        uu____15326 :: out in
                      (uu____15324, rest1))
             | uu____15330 -> ([], bindings1) in
           let uu____15334 = aux bindings in
           match uu____15334 with
           | (closing,bindings1) ->
               let uu____15348 =
                 FStar_Syntax_Util.close_forall_no_univs
                   (FStar_List.rev closing) q in
               (uu____15348, bindings1) in
         match uu____15276 with
         | (q1,bindings1) ->
             let uu____15361 =
               let uu____15364 =
                 FStar_List.filter
                   (fun uu___128_15366  ->
                      match uu___128_15366 with
                      | FStar_TypeChecker_Env.Binding_sig uu____15367 ->
                          false
                      | uu____15371 -> true) bindings1 in
               encode_env_bindings env uu____15364 in
             (match uu____15361 with
              | (env_decls,env1) ->
                  ((let uu____15382 =
                      ((FStar_TypeChecker_Env.debug tcenv FStar_Options.Low)
                         ||
                         (FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug tcenv)
                            (FStar_Options.Other "SMTEncoding")))
                        ||
                        (FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug tcenv)
                           (FStar_Options.Other "SMTQuery")) in
                    if uu____15382
                    then
                      let uu____15383 = FStar_Syntax_Print.term_to_string q1 in
                      FStar_Util.print1 "Encoding query formula: %s\n"
                        uu____15383
                    else ());
                   (let uu____15385 = encode_formula q1 env1 in
                    match uu____15385 with
                    | (phi,qdecls) ->
                        let uu____15397 =
                          let uu____15400 =
                            FStar_TypeChecker_Env.get_range tcenv in
                          FStar_SMTEncoding_ErrorReporting.label_goals
                            use_env_msg uu____15400 phi in
                        (match uu____15397 with
                         | (labels,phi1) ->
                             let uu____15410 = encode_labels labels in
                             (match uu____15410 with
                              | (label_prefix,label_suffix) ->
                                  let query_prelude =
                                    FStar_List.append env_decls
                                      (FStar_List.append label_prefix qdecls) in
                                  let qry =
                                    let uu____15431 =
                                      let uu____15435 =
                                        FStar_SMTEncoding_Util.mkNot phi1 in
                                      let uu____15436 =
                                        varops.mk_unique "@query" in
                                      (uu____15435, (Some "query"),
                                        uu____15436) in
                                    FStar_SMTEncoding_Util.mkAssume
                                      uu____15431 in
                                  let suffix =
                                    FStar_List.append label_suffix
                                      [FStar_SMTEncoding_Term.Echo "Done!"] in
                                  (query_prelude, labels, qry, suffix)))))))
let is_trivial:
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.typ -> Prims.bool =
  fun tcenv  ->
    fun q  ->
      let env =
        let uu____15449 = FStar_TypeChecker_Env.current_module tcenv in
        get_env uu____15449 tcenv in
      FStar_SMTEncoding_Z3.push "query";
      (let uu____15451 = encode_formula q env in
       match uu____15451 with
       | (f,uu____15455) ->
           (FStar_SMTEncoding_Z3.pop "query";
            (match f.FStar_SMTEncoding_Term.tm with
             | FStar_SMTEncoding_Term.App
                 (FStar_SMTEncoding_Term.TrueOp ,uu____15457) -> true
             | uu____15460 -> false)))