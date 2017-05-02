open Prims
let add_fuel x tl1 =
  let uu____16 = FStar_Options.unthrottle_inductives () in
  if uu____16 then tl1 else x :: tl1
let withenv c uu____39 = match uu____39 with | (a,b) -> (a, b, c)
let vargs args =
  FStar_List.filter
    (fun uu___117_74  ->
       match uu___117_74 with
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
        let uu___141_140 = a in
        let uu____141 =
          FStar_Syntax_Util.unmangle_field_name a.FStar_Syntax_Syntax.ppname in
        {
          FStar_Syntax_Syntax.ppname = uu____141;
          FStar_Syntax_Syntax.index =
            (uu___141_140.FStar_Syntax_Syntax.index);
          FStar_Syntax_Syntax.sort = (uu___141_140.FStar_Syntax_Syntax.sort)
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
    let uu___142_780 = x in
    let uu____781 =
      FStar_Syntax_Util.unmangle_field_name x.FStar_Syntax_Syntax.ppname in
    {
      FStar_Syntax_Syntax.ppname = uu____781;
      FStar_Syntax_Syntax.index = (uu___142_780.FStar_Syntax_Syntax.index);
      FStar_Syntax_Syntax.sort = (uu___142_780.FStar_Syntax_Syntax.sort)
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
type env_t =
  {
  bindings: binding Prims.list;
  depth: Prims.int;
  tcenv: FStar_TypeChecker_Env.env;
  warn: Prims.bool;
  cache:
    (Prims.string* FStar_SMTEncoding_Term.sort Prims.list*
      FStar_SMTEncoding_Term.decl Prims.list) FStar_Util.smap;
  nolabels: Prims.bool;
  use_zfuel_name: Prims.bool;
  encode_non_total_function_typ: Prims.bool;
  current_module_name: Prims.string;}
let print_env: env_t -> Prims.string =
  fun e  ->
    let uu____952 =
      FStar_All.pipe_right e.bindings
        (FStar_List.map
           (fun uu___118_956  ->
              match uu___118_956 with
              | Binding_var (x,uu____958) ->
                  FStar_Syntax_Print.bv_to_string x
              | Binding_fvar (l,uu____960,uu____961,uu____962) ->
                  FStar_Syntax_Print.lid_to_string l)) in
    FStar_All.pipe_right uu____952 (FStar_String.concat ", ")
let lookup_binding env f = FStar_Util.find_map env.bindings f
let caption_t: env_t -> FStar_Syntax_Syntax.term -> Prims.string Prims.option
  =
  fun env  ->
    fun t  ->
      let uu____995 = FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low in
      if uu____995
      then
        let uu____997 = FStar_Syntax_Print.term_to_string t in Some uu____997
      else None
let fresh_fvar:
  Prims.string ->
    FStar_SMTEncoding_Term.sort ->
      (Prims.string* FStar_SMTEncoding_Term.term)
  =
  fun x  ->
    fun s  ->
      let xsym = varops.fresh x in
      let uu____1008 = FStar_SMTEncoding_Util.mkFreeV (xsym, s) in
      (xsym, uu____1008)
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
        (let uu___143_1020 = env in
         {
           bindings = ((Binding_var (x, y)) :: (env.bindings));
           depth = (env.depth + (Prims.parse_int "1"));
           tcenv = (uu___143_1020.tcenv);
           warn = (uu___143_1020.warn);
           cache = (uu___143_1020.cache);
           nolabels = (uu___143_1020.nolabels);
           use_zfuel_name = (uu___143_1020.use_zfuel_name);
           encode_non_total_function_typ =
             (uu___143_1020.encode_non_total_function_typ);
           current_module_name = (uu___143_1020.current_module_name)
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
        (let uu___144_1033 = env in
         {
           bindings = ((Binding_var (x, y)) :: (env.bindings));
           depth = (uu___144_1033.depth);
           tcenv = (uu___144_1033.tcenv);
           warn = (uu___144_1033.warn);
           cache = (uu___144_1033.cache);
           nolabels = (uu___144_1033.nolabels);
           use_zfuel_name = (uu___144_1033.use_zfuel_name);
           encode_non_total_function_typ =
             (uu___144_1033.encode_non_total_function_typ);
           current_module_name = (uu___144_1033.current_module_name)
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
          (let uu___145_1049 = env in
           {
             bindings = ((Binding_var (x, y)) :: (env.bindings));
             depth = (uu___145_1049.depth);
             tcenv = (uu___145_1049.tcenv);
             warn = (uu___145_1049.warn);
             cache = (uu___145_1049.cache);
             nolabels = (uu___145_1049.nolabels);
             use_zfuel_name = (uu___145_1049.use_zfuel_name);
             encode_non_total_function_typ =
               (uu___145_1049.encode_non_total_function_typ);
             current_module_name = (uu___145_1049.current_module_name)
           }))
let push_term_var:
  env_t -> FStar_Syntax_Syntax.bv -> FStar_SMTEncoding_Term.term -> env_t =
  fun env  ->
    fun x  ->
      fun t  ->
        let uu___146_1059 = env in
        {
          bindings = ((Binding_var (x, t)) :: (env.bindings));
          depth = (uu___146_1059.depth);
          tcenv = (uu___146_1059.tcenv);
          warn = (uu___146_1059.warn);
          cache = (uu___146_1059.cache);
          nolabels = (uu___146_1059.nolabels);
          use_zfuel_name = (uu___146_1059.use_zfuel_name);
          encode_non_total_function_typ =
            (uu___146_1059.encode_non_total_function_typ);
          current_module_name = (uu___146_1059.current_module_name)
        }
let lookup_term_var:
  env_t -> FStar_Syntax_Syntax.bv -> FStar_SMTEncoding_Term.term =
  fun env  ->
    fun a  ->
      let aux a' =
        lookup_binding env
          (fun uu___119_1075  ->
             match uu___119_1075 with
             | Binding_var (b,t) when FStar_Syntax_Syntax.bv_eq b a' ->
                 Some (b, t)
             | uu____1083 -> None) in
      let uu____1086 = aux a in
      match uu____1086 with
      | None  ->
          let a2 = unmangle a in
          let uu____1093 = aux a2 in
          (match uu____1093 with
           | None  ->
               let uu____1099 =
                 let uu____1100 = FStar_Syntax_Print.bv_to_string a2 in
                 let uu____1101 = print_env env in
                 FStar_Util.format2
                   "Bound term variable not found (after unmangling): %s in environment: %s"
                   uu____1100 uu____1101 in
               failwith uu____1099
           | Some (b,t) -> t)
      | Some (b,t) -> t
let new_term_constant_and_tok_from_lid:
  env_t -> FStar_Ident.lident -> (Prims.string* Prims.string* env_t) =
  fun env  ->
    fun x  ->
      let fname = varops.new_fvar x in
      let ftok = Prims.strcat fname "@tok" in
      let uu____1121 =
        let uu___147_1122 = env in
        let uu____1123 =
          let uu____1125 =
            let uu____1126 =
              let uu____1133 =
                let uu____1135 = FStar_SMTEncoding_Util.mkApp (ftok, []) in
                FStar_All.pipe_left (fun _0_29  -> Some _0_29) uu____1135 in
              (x, fname, uu____1133, None) in
            Binding_fvar uu____1126 in
          uu____1125 :: (env.bindings) in
        {
          bindings = uu____1123;
          depth = (uu___147_1122.depth);
          tcenv = (uu___147_1122.tcenv);
          warn = (uu___147_1122.warn);
          cache = (uu___147_1122.cache);
          nolabels = (uu___147_1122.nolabels);
          use_zfuel_name = (uu___147_1122.use_zfuel_name);
          encode_non_total_function_typ =
            (uu___147_1122.encode_non_total_function_typ);
          current_module_name = (uu___147_1122.current_module_name)
        } in
      (fname, ftok, uu____1121)
let try_lookup_lid:
  env_t ->
    FStar_Ident.lident ->
      (Prims.string* FStar_SMTEncoding_Term.term Prims.option*
        FStar_SMTEncoding_Term.term Prims.option) Prims.option
  =
  fun env  ->
    fun a  ->
      lookup_binding env
        (fun uu___120_1157  ->
           match uu___120_1157 with
           | Binding_fvar (b,t1,t2,t3) when FStar_Ident.lid_equals b a ->
               Some (t1, t2, t3)
           | uu____1179 -> None)
let contains_name: env_t -> Prims.string -> Prims.bool =
  fun env  ->
    fun s  ->
      let uu____1191 =
        lookup_binding env
          (fun uu___121_1193  ->
             match uu___121_1193 with
             | Binding_fvar (b,t1,t2,t3) when b.FStar_Ident.str = s ->
                 Some ()
             | uu____1203 -> None) in
      FStar_All.pipe_right uu____1191 FStar_Option.isSome
let lookup_lid:
  env_t ->
    FStar_Ident.lident ->
      (Prims.string* FStar_SMTEncoding_Term.term Prims.option*
        FStar_SMTEncoding_Term.term Prims.option)
  =
  fun env  ->
    fun a  ->
      let uu____1216 = try_lookup_lid env a in
      match uu____1216 with
      | None  ->
          let uu____1233 =
            let uu____1234 = FStar_Syntax_Print.lid_to_string a in
            FStar_Util.format1 "Name not found: %s" uu____1234 in
          failwith uu____1233
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
          let uu___148_1265 = env in
          {
            bindings = ((Binding_fvar (x, fname, ftok, None)) ::
              (env.bindings));
            depth = (uu___148_1265.depth);
            tcenv = (uu___148_1265.tcenv);
            warn = (uu___148_1265.warn);
            cache = (uu___148_1265.cache);
            nolabels = (uu___148_1265.nolabels);
            use_zfuel_name = (uu___148_1265.use_zfuel_name);
            encode_non_total_function_typ =
              (uu___148_1265.encode_non_total_function_typ);
            current_module_name = (uu___148_1265.current_module_name)
          }
let push_zfuel_name: env_t -> FStar_Ident.lident -> Prims.string -> env_t =
  fun env  ->
    fun x  ->
      fun f  ->
        let uu____1277 = lookup_lid env x in
        match uu____1277 with
        | (t1,t2,uu____1285) ->
            let t3 =
              let uu____1291 =
                let uu____1295 =
                  let uu____1297 = FStar_SMTEncoding_Util.mkApp ("ZFuel", []) in
                  [uu____1297] in
                (f, uu____1295) in
              FStar_SMTEncoding_Util.mkApp uu____1291 in
            let uu___149_1300 = env in
            {
              bindings = ((Binding_fvar (x, t1, t2, (Some t3))) ::
                (env.bindings));
              depth = (uu___149_1300.depth);
              tcenv = (uu___149_1300.tcenv);
              warn = (uu___149_1300.warn);
              cache = (uu___149_1300.cache);
              nolabels = (uu___149_1300.nolabels);
              use_zfuel_name = (uu___149_1300.use_zfuel_name);
              encode_non_total_function_typ =
                (uu___149_1300.encode_non_total_function_typ);
              current_module_name = (uu___149_1300.current_module_name)
            }
let try_lookup_free_var:
  env_t -> FStar_Ident.lident -> FStar_SMTEncoding_Term.term Prims.option =
  fun env  ->
    fun l  ->
      let uu____1310 = try_lookup_lid env l in
      match uu____1310 with
      | None  -> None
      | Some (name,sym,zf_opt) ->
          (match zf_opt with
           | Some f when env.use_zfuel_name -> Some f
           | uu____1337 ->
               (match sym with
                | Some t ->
                    (match t.FStar_SMTEncoding_Term.tm with
                     | FStar_SMTEncoding_Term.App (uu____1342,fuel::[]) ->
                         let uu____1345 =
                           let uu____1346 =
                             let uu____1347 =
                               FStar_SMTEncoding_Term.fv_of_term fuel in
                             FStar_All.pipe_right uu____1347 Prims.fst in
                           FStar_Util.starts_with uu____1346 "fuel" in
                         if uu____1345
                         then
                           let uu____1349 =
                             let uu____1350 =
                               FStar_SMTEncoding_Util.mkFreeV
                                 (name, FStar_SMTEncoding_Term.Term_sort) in
                             FStar_SMTEncoding_Term.mk_ApplyTF uu____1350
                               fuel in
                           FStar_All.pipe_left (fun _0_30  -> Some _0_30)
                             uu____1349
                         else Some t
                     | uu____1353 -> Some t)
                | uu____1354 -> None))
let lookup_free_var env a =
  let uu____1372 = try_lookup_free_var env a.FStar_Syntax_Syntax.v in
  match uu____1372 with
  | Some t -> t
  | None  ->
      let uu____1375 =
        let uu____1376 =
          FStar_Syntax_Print.lid_to_string a.FStar_Syntax_Syntax.v in
        FStar_Util.format1 "Name not found: %s" uu____1376 in
      failwith uu____1375
let lookup_free_var_name env a =
  let uu____1393 = lookup_lid env a.FStar_Syntax_Syntax.v in
  match uu____1393 with | (x,uu____1400,uu____1401) -> x
let lookup_free_var_sym env a =
  let uu____1425 = lookup_lid env a.FStar_Syntax_Syntax.v in
  match uu____1425 with
  | (name,sym,zf_opt) ->
      (match zf_opt with
       | Some
           { FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.App (g,zf);
             FStar_SMTEncoding_Term.freevars = uu____1446;
             FStar_SMTEncoding_Term.rng = uu____1447;_}
           when env.use_zfuel_name -> (g, zf)
       | uu____1455 ->
           (match sym with
            | None  -> ((FStar_SMTEncoding_Term.Var name), [])
            | Some sym1 ->
                (match sym1.FStar_SMTEncoding_Term.tm with
                 | FStar_SMTEncoding_Term.App (g,fuel::[]) -> (g, [fuel])
                 | uu____1469 -> ((FStar_SMTEncoding_Term.Var name), []))))
let tok_of_name:
  env_t -> Prims.string -> FStar_SMTEncoding_Term.term Prims.option =
  fun env  ->
    fun nm  ->
      FStar_Util.find_map env.bindings
        (fun uu___122_1478  ->
           match uu___122_1478 with
           | Binding_fvar (uu____1480,nm',tok,uu____1483) when nm = nm' ->
               tok
           | uu____1488 -> None)
let mkForall_fuel' n1 uu____1505 =
  match uu____1505 with
  | (pats,vars,body) ->
      let fallback uu____1521 =
        FStar_SMTEncoding_Util.mkForall (pats, vars, body) in
      let uu____1524 = FStar_Options.unthrottle_inductives () in
      if uu____1524
      then fallback ()
      else
        (let uu____1526 = fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort in
         match uu____1526 with
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
                       | uu____1545 -> p)) in
             let pats1 = FStar_List.map add_fuel1 pats in
             let body1 =
               match body.FStar_SMTEncoding_Term.tm with
               | FStar_SMTEncoding_Term.App
                   (FStar_SMTEncoding_Term.Imp ,guard::body'::[]) ->
                   let guard1 =
                     match guard.FStar_SMTEncoding_Term.tm with
                     | FStar_SMTEncoding_Term.App
                         (FStar_SMTEncoding_Term.And ,guards) ->
                         let uu____1559 = add_fuel1 guards in
                         FStar_SMTEncoding_Util.mk_and_l uu____1559
                     | uu____1561 ->
                         let uu____1562 = add_fuel1 [guard] in
                         FStar_All.pipe_right uu____1562 FStar_List.hd in
                   FStar_SMTEncoding_Util.mkImp (guard1, body')
               | uu____1565 -> body in
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
          let uu____1609 =
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Eager_unfolding_only] env.tcenv
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          FStar_All.pipe_right uu____1609 FStar_Option.isNone
      | uu____1622 -> false
let head_redex: env_t -> FStar_Syntax_Syntax.term -> Prims.bool =
  fun env  ->
    fun t  ->
      let uu____1629 =
        let uu____1630 = FStar_Syntax_Util.un_uinst t in
        uu____1630.FStar_Syntax_Syntax.n in
      match uu____1629 with
      | FStar_Syntax_Syntax.Tm_abs
          (uu____1633,uu____1634,Some (FStar_Util.Inr (l,flags))) ->
          ((FStar_Ident.lid_equals l FStar_Syntax_Const.effect_Tot_lid) ||
             (FStar_Ident.lid_equals l FStar_Syntax_Const.effect_GTot_lid))
            ||
            (FStar_List.existsb
               (fun uu___123_1663  ->
                  match uu___123_1663 with
                  | FStar_Syntax_Syntax.TOTAL  -> true
                  | uu____1664 -> false) flags)
      | FStar_Syntax_Syntax.Tm_abs
          (uu____1665,uu____1666,Some (FStar_Util.Inl lc)) ->
          FStar_Syntax_Util.is_tot_or_gtot_lcomp lc
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____1693 =
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Eager_unfolding_only] env.tcenv
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          FStar_All.pipe_right uu____1693 FStar_Option.isSome
      | uu____1706 -> false
let whnf: env_t -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term =
  fun env  ->
    fun t  ->
      let uu____1713 = head_normal env t in
      if uu____1713
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
    let uu____1724 =
      let uu____1725 = FStar_Syntax_Syntax.null_binder t in [uu____1725] in
    let uu____1726 =
      FStar_Syntax_Syntax.fvar FStar_Syntax_Const.true_lid
        FStar_Syntax_Syntax.Delta_constant None in
    FStar_Syntax_Util.abs uu____1724 uu____1726 None
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
                    let uu____1753 = FStar_SMTEncoding_Util.mkFreeV var in
                    FStar_SMTEncoding_Term.mk_ApplyTF out uu____1753
                | s ->
                    let uu____1756 = FStar_SMTEncoding_Util.mkFreeV var in
                    FStar_SMTEncoding_Util.mk_ApplyTT out uu____1756) e)
let mk_Apply_args:
  FStar_SMTEncoding_Term.term ->
    FStar_SMTEncoding_Term.term Prims.list -> FStar_SMTEncoding_Term.term
  =
  fun e  ->
    fun args  ->
      FStar_All.pipe_right args
        (FStar_List.fold_left FStar_SMTEncoding_Util.mk_ApplyTT e)
let is_app: FStar_SMTEncoding_Term.op -> Prims.bool =
  fun uu___124_1768  ->
    match uu___124_1768 with
    | FStar_SMTEncoding_Term.Var "ApplyTT"|FStar_SMTEncoding_Term.Var
      "ApplyTF" -> true
    | uu____1769 -> false
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
                       FStar_SMTEncoding_Term.freevars = uu____1797;
                       FStar_SMTEncoding_Term.rng = uu____1798;_}::[]),x::xs1)
              when (is_app app) && (FStar_SMTEncoding_Term.fv_eq x y) ->
              check_partial_applications f xs1
          | (FStar_SMTEncoding_Term.App
             (FStar_SMTEncoding_Term.Var f,args),uu____1812) ->
              let uu____1817 =
                ((FStar_List.length args) = (FStar_List.length xs)) &&
                  (FStar_List.forall2
                     (fun a  ->
                        fun v1  ->
                          match a.FStar_SMTEncoding_Term.tm with
                          | FStar_SMTEncoding_Term.FreeV fv ->
                              FStar_SMTEncoding_Term.fv_eq fv v1
                          | uu____1827 -> false) args (FStar_List.rev xs)) in
              if uu____1817 then tok_of_name env f else None
          | (uu____1830,[]) ->
              let fvs = FStar_SMTEncoding_Term.free_variables t in
              let uu____1833 =
                FStar_All.pipe_right fvs
                  (FStar_List.for_all
                     (fun fv  ->
                        let uu____1835 =
                          FStar_Util.for_some
                            (FStar_SMTEncoding_Term.fv_eq fv) vars in
                        Prims.op_Negation uu____1835)) in
              if uu____1833 then Some t else None
          | uu____1838 -> None in
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
    | uu____1922 -> false
let encode_const: FStar_Const.sconst -> FStar_SMTEncoding_Term.term =
  fun uu___125_1925  ->
    match uu___125_1925 with
    | FStar_Const.Const_unit  -> FStar_SMTEncoding_Term.mk_Term_unit
    | FStar_Const.Const_bool (true ) ->
        FStar_SMTEncoding_Term.boxBool FStar_SMTEncoding_Util.mkTrue
    | FStar_Const.Const_bool (false ) ->
        FStar_SMTEncoding_Term.boxBool FStar_SMTEncoding_Util.mkFalse
    | FStar_Const.Const_char c ->
        let uu____1927 =
          let uu____1931 =
            let uu____1933 =
              let uu____1934 =
                FStar_SMTEncoding_Util.mkInteger' (FStar_Util.int_of_char c) in
              FStar_SMTEncoding_Term.boxInt uu____1934 in
            [uu____1933] in
          ("FStar.Char.Char", uu____1931) in
        FStar_SMTEncoding_Util.mkApp uu____1927
    | FStar_Const.Const_int (i,None ) ->
        let uu____1942 = FStar_SMTEncoding_Util.mkInteger i in
        FStar_SMTEncoding_Term.boxInt uu____1942
    | FStar_Const.Const_int (i,Some uu____1944) ->
        failwith "Machine integers should be desugared"
    | FStar_Const.Const_string (bytes,uu____1953) ->
        let uu____1956 = FStar_All.pipe_left FStar_Util.string_of_bytes bytes in
        varops.string_const uu____1956
    | FStar_Const.Const_range r -> FStar_SMTEncoding_Term.mk_Range_const
    | FStar_Const.Const_effect  -> FStar_SMTEncoding_Term.mk_Term_type
    | c ->
        let uu____1960 =
          let uu____1961 = FStar_Syntax_Print.const_to_string c in
          FStar_Util.format1 "Unhandled constant: %s" uu____1961 in
        failwith uu____1960
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
        | FStar_Syntax_Syntax.Tm_arrow uu____1980 -> t1
        | FStar_Syntax_Syntax.Tm_refine uu____1988 ->
            let uu____1993 = FStar_Syntax_Util.unrefine t1 in
            aux true uu____1993
        | uu____1994 ->
            if norm1
            then let uu____1995 = whnf env t1 in aux false uu____1995
            else
              (let uu____1997 =
                 let uu____1998 =
                   FStar_Range.string_of_range t0.FStar_Syntax_Syntax.pos in
                 let uu____1999 = FStar_Syntax_Print.term_to_string t0 in
                 FStar_Util.format2 "(%s) Expected a function typ; got %s"
                   uu____1998 uu____1999 in
               failwith uu____1997) in
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
    | uu____2020 ->
        let uu____2021 = FStar_Syntax_Syntax.mk_Total k1 in ([], uu____2021)
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
        (let uu____2164 =
           FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low in
         if uu____2164
         then
           let uu____2165 = FStar_Syntax_Print.binders_to_string ", " bs in
           FStar_Util.print1 "Encoding binders %s\n" uu____2165
         else ());
        (let uu____2167 =
           FStar_All.pipe_right bs
             (FStar_List.fold_left
                (fun uu____2203  ->
                   fun b  ->
                     match uu____2203 with
                     | (vars,guards,env1,decls,names1) ->
                         let uu____2246 =
                           let x = unmangle (Prims.fst b) in
                           let uu____2255 = gen_term_var env1 x in
                           match uu____2255 with
                           | (xxsym,xx,env') ->
                               let uu____2269 =
                                 let uu____2272 =
                                   norm env1 x.FStar_Syntax_Syntax.sort in
                                 encode_term_pred fuel_opt uu____2272 env1 xx in
                               (match uu____2269 with
                                | (guard_x_t,decls') ->
                                    ((xxsym,
                                       FStar_SMTEncoding_Term.Term_sort),
                                      guard_x_t, env', decls', x)) in
                         (match uu____2246 with
                          | (v1,g,env2,decls',n1) ->
                              ((v1 :: vars), (g :: guards), env2,
                                (FStar_List.append decls decls'), (n1 ::
                                names1)))) ([], [], env, [], [])) in
         match uu____2167 with
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
          let uu____2360 = encode_term t env in
          match uu____2360 with
          | (t1,decls) ->
              let uu____2367 =
                FStar_SMTEncoding_Term.mk_HasTypeWithFuel fuel_opt e t1 in
              (uu____2367, decls)
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
          let uu____2375 = encode_term t env in
          match uu____2375 with
          | (t1,decls) ->
              (match fuel_opt with
               | None  ->
                   let uu____2384 = FStar_SMTEncoding_Term.mk_HasTypeZ e t1 in
                   (uu____2384, decls)
               | Some f ->
                   let uu____2386 =
                     FStar_SMTEncoding_Term.mk_HasTypeFuel f e t1 in
                   (uu____2386, decls))
and encode_term:
  FStar_Syntax_Syntax.typ ->
    env_t -> (FStar_SMTEncoding_Term.term* FStar_SMTEncoding_Term.decls_t)
  =
  fun t  ->
    fun env  ->
      let t0 = FStar_Syntax_Subst.compress t in
      (let uu____2393 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv)
           (FStar_Options.Other "SMTEncoding") in
       if uu____2393
       then
         let uu____2394 = FStar_Syntax_Print.tag_of_term t in
         let uu____2395 = FStar_Syntax_Print.tag_of_term t0 in
         let uu____2396 = FStar_Syntax_Print.term_to_string t0 in
         FStar_Util.print3 "(%s) (%s)   %s\n" uu____2394 uu____2395
           uu____2396
       else ());
      (match t0.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Tm_delayed _|FStar_Syntax_Syntax.Tm_unknown  ->
           let uu____2401 =
             let uu____2402 =
               FStar_All.pipe_left FStar_Range.string_of_range
                 t.FStar_Syntax_Syntax.pos in
             let uu____2403 = FStar_Syntax_Print.tag_of_term t0 in
             let uu____2404 = FStar_Syntax_Print.term_to_string t0 in
             let uu____2405 = FStar_Syntax_Print.term_to_string t in
             FStar_Util.format4 "(%s) Impossible: %s\n%s\n%s\n" uu____2402
               uu____2403 uu____2404 uu____2405 in
           failwith uu____2401
       | FStar_Syntax_Syntax.Tm_bvar x ->
           let uu____2409 =
             let uu____2410 = FStar_Syntax_Print.bv_to_string x in
             FStar_Util.format1 "Impossible: locally nameless; got %s"
               uu____2410 in
           failwith uu____2409
       | FStar_Syntax_Syntax.Tm_ascribed (t1,k,uu____2415) ->
           encode_term t1 env
       | FStar_Syntax_Syntax.Tm_meta (t1,uu____2445) -> encode_term t1 env
       | FStar_Syntax_Syntax.Tm_name x ->
           let t1 = lookup_term_var env x in (t1, [])
       | FStar_Syntax_Syntax.Tm_fvar v1 ->
           let uu____2454 =
             lookup_free_var env v1.FStar_Syntax_Syntax.fv_name in
           (uu____2454, [])
       | FStar_Syntax_Syntax.Tm_type uu____2460 ->
           (FStar_SMTEncoding_Term.mk_Term_type, [])
       | FStar_Syntax_Syntax.Tm_uinst (t1,uu____2463) -> encode_term t1 env
       | FStar_Syntax_Syntax.Tm_constant c ->
           let uu____2469 = encode_const c in (uu____2469, [])
       | FStar_Syntax_Syntax.Tm_arrow (binders,c) ->
           let module_name = env.current_module_name in
           let uu____2484 = FStar_Syntax_Subst.open_comp binders c in
           (match uu____2484 with
            | (binders1,res) ->
                let uu____2491 =
                  (env.encode_non_total_function_typ &&
                     (FStar_Syntax_Util.is_pure_or_ghost_comp res))
                    || (FStar_Syntax_Util.is_tot_or_gtot_comp res) in
                if uu____2491
                then
                  let uu____2494 = encode_binders None binders1 env in
                  (match uu____2494 with
                   | (vars,guards,env',decls,uu____2509) ->
                       let fsym =
                         let uu____2519 = varops.fresh "f" in
                         (uu____2519, FStar_SMTEncoding_Term.Term_sort) in
                       let f = FStar_SMTEncoding_Util.mkFreeV fsym in
                       let app = mk_Apply f vars in
                       let uu____2522 =
                         FStar_TypeChecker_Util.pure_or_ghost_pre_and_post
                           (let uu___150_2526 = env.tcenv in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___150_2526.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___150_2526.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___150_2526.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___150_2526.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___150_2526.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___150_2526.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                (uu___150_2526.FStar_TypeChecker_Env.expected_typ);
                              FStar_TypeChecker_Env.sigtab =
                                (uu___150_2526.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.is_pattern =
                                (uu___150_2526.FStar_TypeChecker_Env.is_pattern);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___150_2526.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___150_2526.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___150_2526.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___150_2526.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___150_2526.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___150_2526.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___150_2526.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___150_2526.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___150_2526.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___150_2526.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.type_of =
                                (uu___150_2526.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___150_2526.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.use_bv_sorts =
                                (uu___150_2526.FStar_TypeChecker_Env.use_bv_sorts);
                              FStar_TypeChecker_Env.qname_and_index =
                                (uu___150_2526.FStar_TypeChecker_Env.qname_and_index)
                            }) res in
                       (match uu____2522 with
                        | (pre_opt,res_t) ->
                            let uu____2533 =
                              encode_term_pred None res_t env' app in
                            (match uu____2533 with
                             | (res_pred,decls') ->
                                 let uu____2540 =
                                   match pre_opt with
                                   | None  ->
                                       let uu____2547 =
                                         FStar_SMTEncoding_Util.mk_and_l
                                           guards in
                                       (uu____2547, [])
                                   | Some pre ->
                                       let uu____2550 =
                                         encode_formula pre env' in
                                       (match uu____2550 with
                                        | (guard,decls0) ->
                                            let uu____2558 =
                                              FStar_SMTEncoding_Util.mk_and_l
                                                (guard :: guards) in
                                            (uu____2558, decls0)) in
                                 (match uu____2540 with
                                  | (guards1,guard_decls) ->
                                      let t_interp =
                                        let uu____2566 =
                                          let uu____2572 =
                                            FStar_SMTEncoding_Util.mkImp
                                              (guards1, res_pred) in
                                          ([[app]], vars, uu____2572) in
                                        FStar_SMTEncoding_Util.mkForall
                                          uu____2566 in
                                      let cvars =
                                        let uu____2582 =
                                          FStar_SMTEncoding_Term.free_variables
                                            t_interp in
                                        FStar_All.pipe_right uu____2582
                                          (FStar_List.filter
                                             (fun uu____2588  ->
                                                match uu____2588 with
                                                | (x,uu____2592) ->
                                                    x <> (Prims.fst fsym))) in
                                      let tkey =
                                        FStar_SMTEncoding_Util.mkForall
                                          ([], (fsym :: cvars), t_interp) in
                                      let tkey_hash =
                                        FStar_SMTEncoding_Term.hash_of_term
                                          tkey in
                                      let uu____2603 =
                                        FStar_Util.smap_try_find env.cache
                                          tkey_hash in
                                      (match uu____2603 with
                                       | Some (t',sorts,uu____2619) ->
                                           let uu____2629 =
                                             let uu____2630 =
                                               let uu____2634 =
                                                 FStar_All.pipe_right cvars
                                                   (FStar_List.map
                                                      FStar_SMTEncoding_Util.mkFreeV) in
                                               (t', uu____2634) in
                                             FStar_SMTEncoding_Util.mkApp
                                               uu____2630 in
                                           (uu____2629, [])
                                       | None  ->
                                           let tsym =
                                             let uu____2650 =
                                               let uu____2651 =
                                                 FStar_Util.digest_of_string
                                                   tkey_hash in
                                               Prims.strcat "Tm_arrow_"
                                                 uu____2651 in
                                             varops.mk_unique uu____2650 in
                                           let cvar_sorts =
                                             FStar_List.map Prims.snd cvars in
                                           let caption =
                                             let uu____2658 =
                                               FStar_Options.log_queries () in
                                             if uu____2658
                                             then
                                               let uu____2660 =
                                                 FStar_TypeChecker_Normalize.term_to_string
                                                   env.tcenv t0 in
                                               Some uu____2660
                                             else None in
                                           let tdecl =
                                             FStar_SMTEncoding_Term.DeclFun
                                               (tsym, cvar_sorts,
                                                 FStar_SMTEncoding_Term.Term_sort,
                                                 caption) in
                                           let t1 =
                                             let uu____2666 =
                                               let uu____2670 =
                                                 FStar_List.map
                                                   FStar_SMTEncoding_Util.mkFreeV
                                                   cvars in
                                               (tsym, uu____2670) in
                                             FStar_SMTEncoding_Util.mkApp
                                               uu____2666 in
                                           let t_has_kind =
                                             FStar_SMTEncoding_Term.mk_HasType
                                               t1
                                               FStar_SMTEncoding_Term.mk_Term_type in
                                           let k_assumption =
                                             let a_name =
                                               Prims.strcat "kinding_" tsym in
                                             let uu____2678 =
                                               let uu____2682 =
                                                 FStar_SMTEncoding_Util.mkForall
                                                   ([[t_has_kind]], cvars,
                                                     t_has_kind) in
                                               (uu____2682, (Some a_name),
                                                 a_name) in
                                             FStar_SMTEncoding_Term.Assume
                                               uu____2678 in
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
                                             let uu____2695 =
                                               let uu____2699 =
                                                 let uu____2700 =
                                                   let uu____2706 =
                                                     let uu____2707 =
                                                       let uu____2710 =
                                                         let uu____2711 =
                                                           FStar_SMTEncoding_Term.mk_PreType
                                                             f in
                                                         FStar_SMTEncoding_Term.mk_tester
                                                           "Tm_arrow"
                                                           uu____2711 in
                                                       (f_has_t, uu____2710) in
                                                     FStar_SMTEncoding_Util.mkImp
                                                       uu____2707 in
                                                   ([[f_has_t]], (fsym ::
                                                     cvars), uu____2706) in
                                                 mkForall_fuel uu____2700 in
                                               (uu____2699,
                                                 (Some
                                                    "pre-typing for functions"),
                                                 (Prims.strcat module_name
                                                    (Prims.strcat "_" a_name))) in
                                             FStar_SMTEncoding_Term.Assume
                                               uu____2695 in
                                           let t_interp1 =
                                             let a_name =
                                               Prims.strcat "interpretation_"
                                                 tsym in
                                             let uu____2724 =
                                               let uu____2728 =
                                                 let uu____2729 =
                                                   let uu____2735 =
                                                     FStar_SMTEncoding_Util.mkIff
                                                       (f_has_t_z, t_interp) in
                                                   ([[f_has_t_z]], (fsym ::
                                                     cvars), uu____2735) in
                                                 FStar_SMTEncoding_Util.mkForall
                                                   uu____2729 in
                                               (uu____2728, (Some a_name),
                                                 (Prims.strcat module_name
                                                    (Prims.strcat "_" a_name))) in
                                             FStar_SMTEncoding_Term.Assume
                                               uu____2724 in
                                           let t_decls =
                                             FStar_List.append (tdecl ::
                                               decls)
                                               (FStar_List.append decls'
                                                  (FStar_List.append
                                                     guard_decls
                                                     [k_assumption;
                                                     pre_typing;
                                                     t_interp1])) in
                                           (FStar_Util.smap_add env.cache
                                              tkey_hash
                                              (tsym, cvar_sorts, t_decls);
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
                     let uu____2766 =
                       let uu____2770 =
                         FStar_SMTEncoding_Term.mk_HasType t1
                           FStar_SMTEncoding_Term.mk_Term_type in
                       (uu____2770, (Some "Typing for non-total arrows"),
                         (Prims.strcat module_name (Prims.strcat "_" a_name))) in
                     FStar_SMTEncoding_Term.Assume uu____2766 in
                   let fsym = ("f", FStar_SMTEncoding_Term.Term_sort) in
                   let f = FStar_SMTEncoding_Util.mkFreeV fsym in
                   let f_has_t = FStar_SMTEncoding_Term.mk_HasType f t1 in
                   let t_interp =
                     let a_name = Prims.strcat "pre_typing_" tsym in
                     let uu____2779 =
                       let uu____2783 =
                         let uu____2784 =
                           let uu____2790 =
                             let uu____2791 =
                               let uu____2794 =
                                 let uu____2795 =
                                   FStar_SMTEncoding_Term.mk_PreType f in
                                 FStar_SMTEncoding_Term.mk_tester "Tm_arrow"
                                   uu____2795 in
                               (f_has_t, uu____2794) in
                             FStar_SMTEncoding_Util.mkImp uu____2791 in
                           ([[f_has_t]], [fsym], uu____2790) in
                         mkForall_fuel uu____2784 in
                       (uu____2783, (Some a_name),
                         (Prims.strcat module_name (Prims.strcat "_" a_name))) in
                     FStar_SMTEncoding_Term.Assume uu____2779 in
                   (t1, [tdecl; t_kinding; t_interp])))
       | FStar_Syntax_Syntax.Tm_refine uu____2809 ->
           let uu____2814 =
             let uu____2817 =
               FStar_TypeChecker_Normalize.normalize_refinement
                 [FStar_TypeChecker_Normalize.WHNF;
                 FStar_TypeChecker_Normalize.EraseUniverses] env.tcenv t0 in
             match uu____2817 with
             | { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_refine (x,f);
                 FStar_Syntax_Syntax.tk = uu____2822;
                 FStar_Syntax_Syntax.pos = uu____2823;
                 FStar_Syntax_Syntax.vars = uu____2824;_} ->
                 let uu____2831 = FStar_Syntax_Subst.open_term [(x, None)] f in
                 (match uu____2831 with
                  | (b,f1) ->
                      let uu____2845 =
                        let uu____2846 = FStar_List.hd b in
                        Prims.fst uu____2846 in
                      (uu____2845, f1))
             | uu____2851 -> failwith "impossible" in
           (match uu____2814 with
            | (x,f) ->
                let uu____2858 = encode_term x.FStar_Syntax_Syntax.sort env in
                (match uu____2858 with
                 | (base_t,decls) ->
                     let uu____2865 = gen_term_var env x in
                     (match uu____2865 with
                      | (x1,xtm,env') ->
                          let uu____2874 = encode_formula f env' in
                          (match uu____2874 with
                           | (refinement,decls') ->
                               let uu____2881 =
                                 fresh_fvar "f"
                                   FStar_SMTEncoding_Term.Fuel_sort in
                               (match uu____2881 with
                                | (fsym,fterm) ->
                                    let tm_has_type_with_fuel =
                                      FStar_SMTEncoding_Term.mk_HasTypeWithFuel
                                        (Some fterm) xtm base_t in
                                    let encoding =
                                      FStar_SMTEncoding_Util.mkAnd
                                        (tm_has_type_with_fuel, refinement) in
                                    let cvars =
                                      let uu____2892 =
                                        let uu____2894 =
                                          FStar_SMTEncoding_Term.free_variables
                                            refinement in
                                        let uu____2898 =
                                          FStar_SMTEncoding_Term.free_variables
                                            tm_has_type_with_fuel in
                                        FStar_List.append uu____2894
                                          uu____2898 in
                                      FStar_Util.remove_dups
                                        FStar_SMTEncoding_Term.fv_eq
                                        uu____2892 in
                                    let cvars1 =
                                      FStar_All.pipe_right cvars
                                        (FStar_List.filter
                                           (fun uu____2914  ->
                                              match uu____2914 with
                                              | (y,uu____2918) ->
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
                                    let uu____2937 =
                                      FStar_Util.smap_try_find env.cache
                                        tkey_hash in
                                    (match uu____2937 with
                                     | Some (t1,uu____2952,uu____2953) ->
                                         let uu____2963 =
                                           let uu____2964 =
                                             let uu____2968 =
                                               FStar_All.pipe_right cvars1
                                                 (FStar_List.map
                                                    FStar_SMTEncoding_Util.mkFreeV) in
                                             (t1, uu____2968) in
                                           FStar_SMTEncoding_Util.mkApp
                                             uu____2964 in
                                         (uu____2963, [])
                                     | None  ->
                                         let module_name =
                                           env.current_module_name in
                                         let tsym =
                                           let uu____2985 =
                                             let uu____2986 =
                                               let uu____2987 =
                                                 FStar_Util.digest_of_string
                                                   tkey_hash in
                                               Prims.strcat "_Tm_refine_"
                                                 uu____2987 in
                                             Prims.strcat module_name
                                               uu____2986 in
                                           varops.mk_unique uu____2985 in
                                         let cvar_sorts =
                                           FStar_List.map Prims.snd cvars1 in
                                         let tdecl =
                                           FStar_SMTEncoding_Term.DeclFun
                                             (tsym, cvar_sorts,
                                               FStar_SMTEncoding_Term.Term_sort,
                                               None) in
                                         let t1 =
                                           let uu____2996 =
                                             let uu____3000 =
                                               FStar_List.map
                                                 FStar_SMTEncoding_Util.mkFreeV
                                                 cvars1 in
                                             (tsym, uu____3000) in
                                           FStar_SMTEncoding_Util.mkApp
                                             uu____2996 in
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
                                           let uu____3010 =
                                             let uu____3014 =
                                               let uu____3015 =
                                                 let uu____3021 =
                                                   FStar_SMTEncoding_Util.mkIff
                                                     (t_haseq_ref,
                                                       t_haseq_base) in
                                                 ([[t_haseq_ref]], cvars1,
                                                   uu____3021) in
                                               FStar_SMTEncoding_Util.mkForall
                                                 uu____3015 in
                                             (uu____3014,
                                               (Some
                                                  (Prims.strcat "haseq for "
                                                     tsym)),
                                               (Prims.strcat "haseq" tsym)) in
                                           FStar_SMTEncoding_Term.Assume
                                             uu____3010 in
                                         let t_kinding =
                                           let uu____3031 =
                                             let uu____3035 =
                                               FStar_SMTEncoding_Util.mkForall
                                                 ([[t_has_kind]], cvars1,
                                                   t_has_kind) in
                                             (uu____3035,
                                               (Some "refinement kinding"),
                                               (Prims.strcat
                                                  "refinement_kinding_" tsym)) in
                                           FStar_SMTEncoding_Term.Assume
                                             uu____3031 in
                                         let t_interp =
                                           let uu____3045 =
                                             let uu____3049 =
                                               let uu____3050 =
                                                 let uu____3056 =
                                                   FStar_SMTEncoding_Util.mkIff
                                                     (x_has_t, encoding) in
                                                 ([[x_has_t]], (ffv :: xfv ::
                                                   cvars1), uu____3056) in
                                               FStar_SMTEncoding_Util.mkForall
                                                 uu____3050 in
                                             let uu____3068 =
                                               let uu____3070 =
                                                 FStar_Syntax_Print.term_to_string
                                                   t0 in
                                               Some uu____3070 in
                                             (uu____3049, uu____3068,
                                               (Prims.strcat
                                                  "refinement_interpretation_"
                                                  tsym)) in
                                           FStar_SMTEncoding_Term.Assume
                                             uu____3045 in
                                         let t_decls =
                                           FStar_List.append decls
                                             (FStar_List.append decls'
                                                [tdecl;
                                                t_kinding;
                                                t_interp;
                                                t_haseq1]) in
                                         (FStar_Util.smap_add env.cache
                                            tkey_hash
                                            (tsym, cvar_sorts, t_decls);
                                          (t1, t_decls))))))))
       | FStar_Syntax_Syntax.Tm_uvar (uv,k) ->
           let ttm =
             let uu____3098 = FStar_Unionfind.uvar_id uv in
             FStar_SMTEncoding_Util.mk_Term_uvar uu____3098 in
           let uu____3102 = encode_term_pred None k env ttm in
           (match uu____3102 with
            | (t_has_k,decls) ->
                let d =
                  let uu____3110 =
                    let uu____3114 =
                      let uu____3115 =
                        let uu____3116 =
                          let uu____3117 = FStar_Unionfind.uvar_id uv in
                          FStar_All.pipe_left FStar_Util.string_of_int
                            uu____3117 in
                        FStar_Util.format1 "uvar_typing_%s" uu____3116 in
                      varops.mk_unique uu____3115 in
                    (t_has_k, (Some "Uvar typing"), uu____3114) in
                  FStar_SMTEncoding_Term.Assume uu____3110 in
                (ttm, (FStar_List.append decls [d])))
       | FStar_Syntax_Syntax.Tm_app uu____3123 ->
           let uu____3133 = FStar_Syntax_Util.head_and_args t0 in
           (match uu____3133 with
            | (head1,args_e) ->
                let uu____3161 =
                  let uu____3169 =
                    let uu____3170 = FStar_Syntax_Subst.compress head1 in
                    uu____3170.FStar_Syntax_Syntax.n in
                  (uu____3169, args_e) in
                (match uu____3161 with
                 | (uu____3180,uu____3181) when head_redex env head1 ->
                     let uu____3192 = whnf env t in
                     encode_term uu____3192 env
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
                     let uu____3266 = encode_term v1 env in
                     (match uu____3266 with
                      | (v11,decls1) ->
                          let uu____3273 = encode_term v2 env in
                          (match uu____3273 with
                           | (v21,decls2) ->
                               let uu____3280 =
                                 FStar_SMTEncoding_Util.mk_LexCons v11 v21 in
                               (uu____3280,
                                 (FStar_List.append decls1 decls2))))
                 | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify
                    ),uu____3282) ->
                     let e0 =
                       let uu____3294 = FStar_List.hd args_e in
                       FStar_TypeChecker_Util.reify_body_with_arg env.tcenv
                         head1 uu____3294 in
                     ((let uu____3300 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug env.tcenv)
                           (FStar_Options.Other "SMTEncodingReify") in
                       if uu____3300
                       then
                         let uu____3301 =
                           FStar_Syntax_Print.term_to_string e0 in
                         FStar_Util.print1 "Result of normalization %s\n"
                           uu____3301
                       else ());
                      (let e =
                         let uu____3306 =
                           let uu____3307 =
                             FStar_TypeChecker_Util.remove_reify e0 in
                           let uu____3308 = FStar_List.tl args_e in
                           FStar_Syntax_Syntax.mk_Tm_app uu____3307
                             uu____3308 in
                         uu____3306 None t0.FStar_Syntax_Syntax.pos in
                       encode_term e env))
                 | (FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_reflect
                    uu____3317),(arg,uu____3319)::[]) -> encode_term arg env
                 | uu____3337 ->
                     let uu____3345 = encode_args args_e env in
                     (match uu____3345 with
                      | (args,decls) ->
                          let encode_partial_app ht_opt =
                            let uu____3378 = encode_term head1 env in
                            match uu____3378 with
                            | (head2,decls') ->
                                let app_tm = mk_Apply_args head2 args in
                                (match ht_opt with
                                 | None  ->
                                     (app_tm,
                                       (FStar_List.append decls decls'))
                                 | Some (formals,c) ->
                                     let uu____3417 =
                                       FStar_Util.first_N
                                         (FStar_List.length args_e) formals in
                                     (match uu____3417 with
                                      | (formals1,rest) ->
                                          let subst1 =
                                            FStar_List.map2
                                              (fun uu____3459  ->
                                                 fun uu____3460  ->
                                                   match (uu____3459,
                                                           uu____3460)
                                                   with
                                                   | ((bv,uu____3474),
                                                      (a,uu____3476)) ->
                                                       FStar_Syntax_Syntax.NT
                                                         (bv, a)) formals1
                                              args_e in
                                          let ty =
                                            let uu____3490 =
                                              FStar_Syntax_Util.arrow rest c in
                                            FStar_All.pipe_right uu____3490
                                              (FStar_Syntax_Subst.subst
                                                 subst1) in
                                          let uu____3495 =
                                            encode_term_pred None ty env
                                              app_tm in
                                          (match uu____3495 with
                                           | (has_type,decls'') ->
                                               let cvars =
                                                 FStar_SMTEncoding_Term.free_variables
                                                   has_type in
                                               let e_typing =
                                                 let uu____3505 =
                                                   let uu____3509 =
                                                     FStar_SMTEncoding_Util.mkForall
                                                       ([[has_type]], cvars,
                                                         has_type) in
                                                   let uu____3514 =
                                                     let uu____3515 =
                                                       let uu____3516 =
                                                         let uu____3517 =
                                                           FStar_SMTEncoding_Term.hash_of_term
                                                             app_tm in
                                                         FStar_Util.digest_of_string
                                                           uu____3517 in
                                                       Prims.strcat
                                                         "partial_app_typing_"
                                                         uu____3516 in
                                                     varops.mk_unique
                                                       uu____3515 in
                                                   (uu____3509,
                                                     (Some
                                                        "Partial app typing"),
                                                     uu____3514) in
                                                 FStar_SMTEncoding_Term.Assume
                                                   uu____3505 in
                                               (app_tm,
                                                 (FStar_List.append decls
                                                    (FStar_List.append decls'
                                                       (FStar_List.append
                                                          decls'' [e_typing]))))))) in
                          let encode_full_app fv =
                            let uu____3534 = lookup_free_var_sym env fv in
                            match uu____3534 with
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
                                let uu____3572 =
                                  let uu____3573 =
                                    let uu____3576 =
                                      FStar_TypeChecker_Env.lookup_lid
                                        env.tcenv
                                        (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                                    FStar_All.pipe_right uu____3576 Prims.fst in
                                  FStar_All.pipe_right uu____3573 Prims.snd in
                                Some uu____3572
                            | FStar_Syntax_Syntax.Tm_ascribed
                                (uu____3595,(FStar_Util.Inl t1,uu____3597),uu____3598)
                                -> Some t1
                            | FStar_Syntax_Syntax.Tm_ascribed
                                (uu____3636,(FStar_Util.Inr c,uu____3638),uu____3639)
                                -> Some (FStar_Syntax_Util.comp_result c)
                            | uu____3677 -> None in
                          (match head_type with
                           | None  -> encode_partial_app None
                           | Some head_type1 ->
                               let head_type2 =
                                 let uu____3697 =
                                   FStar_TypeChecker_Normalize.normalize_refinement
                                     [FStar_TypeChecker_Normalize.WHNF;
                                     FStar_TypeChecker_Normalize.EraseUniverses]
                                     env.tcenv head_type1 in
                                 FStar_All.pipe_left
                                   FStar_Syntax_Util.unrefine uu____3697 in
                               let uu____3698 =
                                 curried_arrow_formals_comp head_type2 in
                               (match uu____3698 with
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
                                     | uu____3723 ->
                                         if
                                           (FStar_List.length formals) >
                                             (FStar_List.length args)
                                         then
                                           encode_partial_app
                                             (Some (formals, c))
                                         else encode_partial_app None))))))
       | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
           let uu____3768 = FStar_Syntax_Subst.open_term' bs body in
           (match uu____3768 with
            | (bs1,body1,opening) ->
                let fallback uu____3783 =
                  let f = varops.fresh "Tm_abs" in
                  let decl =
                    FStar_SMTEncoding_Term.DeclFun
                      (f, [], FStar_SMTEncoding_Term.Term_sort,
                        (Some "Imprecise function encoding")) in
                  let uu____3788 =
                    FStar_SMTEncoding_Util.mkFreeV
                      (f, FStar_SMTEncoding_Term.Term_sort) in
                  (uu____3788, [decl]) in
                let is_impure lc =
                  match lc with
                  | FStar_Util.Inl lc1 ->
                      let uu____3799 =
                        FStar_Syntax_Util.is_pure_or_ghost_lcomp lc1 in
                      Prims.op_Negation uu____3799
                  | FStar_Util.Inr (eff,uu____3801) ->
                      let uu____3807 =
                        FStar_TypeChecker_Util.is_pure_or_ghost_effect
                          env.tcenv eff in
                      FStar_All.pipe_right uu____3807 Prims.op_Negation in
                let reify_comp_and_body env1 c body2 =
                  let reified_body =
                    FStar_TypeChecker_Util.reify_body env1.tcenv body2 in
                  let c1 =
                    match c with
                    | FStar_Util.Inl lc ->
                        let typ =
                          let uu____3852 = lc.FStar_Syntax_Syntax.comp () in
                          FStar_TypeChecker_Env.reify_comp
                            (let uu___151_3853 = env1.tcenv in
                             {
                               FStar_TypeChecker_Env.solver =
                                 (uu___151_3853.FStar_TypeChecker_Env.solver);
                               FStar_TypeChecker_Env.range =
                                 (uu___151_3853.FStar_TypeChecker_Env.range);
                               FStar_TypeChecker_Env.curmodule =
                                 (uu___151_3853.FStar_TypeChecker_Env.curmodule);
                               FStar_TypeChecker_Env.gamma =
                                 (uu___151_3853.FStar_TypeChecker_Env.gamma);
                               FStar_TypeChecker_Env.gamma_cache =
                                 (uu___151_3853.FStar_TypeChecker_Env.gamma_cache);
                               FStar_TypeChecker_Env.modules =
                                 (uu___151_3853.FStar_TypeChecker_Env.modules);
                               FStar_TypeChecker_Env.expected_typ =
                                 (uu___151_3853.FStar_TypeChecker_Env.expected_typ);
                               FStar_TypeChecker_Env.sigtab =
                                 (uu___151_3853.FStar_TypeChecker_Env.sigtab);
                               FStar_TypeChecker_Env.is_pattern =
                                 (uu___151_3853.FStar_TypeChecker_Env.is_pattern);
                               FStar_TypeChecker_Env.instantiate_imp =
                                 (uu___151_3853.FStar_TypeChecker_Env.instantiate_imp);
                               FStar_TypeChecker_Env.effects =
                                 (uu___151_3853.FStar_TypeChecker_Env.effects);
                               FStar_TypeChecker_Env.generalize =
                                 (uu___151_3853.FStar_TypeChecker_Env.generalize);
                               FStar_TypeChecker_Env.letrecs =
                                 (uu___151_3853.FStar_TypeChecker_Env.letrecs);
                               FStar_TypeChecker_Env.top_level =
                                 (uu___151_3853.FStar_TypeChecker_Env.top_level);
                               FStar_TypeChecker_Env.check_uvars =
                                 (uu___151_3853.FStar_TypeChecker_Env.check_uvars);
                               FStar_TypeChecker_Env.use_eq =
                                 (uu___151_3853.FStar_TypeChecker_Env.use_eq);
                               FStar_TypeChecker_Env.is_iface =
                                 (uu___151_3853.FStar_TypeChecker_Env.is_iface);
                               FStar_TypeChecker_Env.admit =
                                 (uu___151_3853.FStar_TypeChecker_Env.admit);
                               FStar_TypeChecker_Env.lax = true;
                               FStar_TypeChecker_Env.lax_universes =
                                 (uu___151_3853.FStar_TypeChecker_Env.lax_universes);
                               FStar_TypeChecker_Env.type_of =
                                 (uu___151_3853.FStar_TypeChecker_Env.type_of);
                               FStar_TypeChecker_Env.universe_of =
                                 (uu___151_3853.FStar_TypeChecker_Env.universe_of);
                               FStar_TypeChecker_Env.use_bv_sorts =
                                 (uu___151_3853.FStar_TypeChecker_Env.use_bv_sorts);
                               FStar_TypeChecker_Env.qname_and_index =
                                 (uu___151_3853.FStar_TypeChecker_Env.qname_and_index)
                             }) uu____3852 FStar_Syntax_Syntax.U_unknown in
                        let uu____3854 =
                          let uu____3855 = FStar_Syntax_Syntax.mk_Total typ in
                          FStar_Syntax_Util.lcomp_of_comp uu____3855 in
                        FStar_Util.Inl uu____3854
                    | FStar_Util.Inr (eff_name,uu____3862) -> c in
                  (c1, reified_body) in
                let codomain_eff lc =
                  match lc with
                  | FStar_Util.Inl lc1 ->
                      let uu____3893 =
                        let uu____3894 = lc1.FStar_Syntax_Syntax.comp () in
                        FStar_Syntax_Subst.subst_comp opening uu____3894 in
                      FStar_All.pipe_right uu____3893
                        (fun _0_31  -> Some _0_31)
                  | FStar_Util.Inr (eff,flags) ->
                      let new_uvar1 uu____3906 =
                        let uu____3907 =
                          FStar_TypeChecker_Rel.new_uvar
                            FStar_Range.dummyRange []
                            FStar_Syntax_Util.ktype0 in
                        FStar_All.pipe_right uu____3907 Prims.fst in
                      if
                        FStar_Ident.lid_equals eff
                          FStar_Syntax_Const.effect_Tot_lid
                      then
                        let uu____3915 =
                          let uu____3916 = new_uvar1 () in
                          FStar_Syntax_Syntax.mk_Total uu____3916 in
                        FStar_All.pipe_right uu____3915
                          (fun _0_32  -> Some _0_32)
                      else
                        if
                          FStar_Ident.lid_equals eff
                            FStar_Syntax_Const.effect_GTot_lid
                        then
                          (let uu____3920 =
                             let uu____3921 = new_uvar1 () in
                             FStar_Syntax_Syntax.mk_GTotal uu____3921 in
                           FStar_All.pipe_right uu____3920
                             (fun _0_33  -> Some _0_33))
                        else None in
                (match lopt with
                 | None  ->
                     ((let uu____3932 =
                         let uu____3933 =
                           FStar_Syntax_Print.term_to_string t0 in
                         FStar_Util.format1
                           "Losing precision when encoding a function literal: %s\n(Unnannotated abstraction in the compiler ?)"
                           uu____3933 in
                       FStar_Errors.warn t0.FStar_Syntax_Syntax.pos
                         uu____3932);
                      fallback ())
                 | Some lc ->
                     let lc1 = lc in
                     let uu____3948 =
                       (is_impure lc1) &&
                         (let uu____3949 =
                            FStar_TypeChecker_Env.is_reifiable env.tcenv lc1 in
                          Prims.op_Negation uu____3949) in
                     if uu____3948
                     then fallback ()
                     else
                       (let cache_size = FStar_Util.smap_size env.cache in
                        let uu____3959 = encode_binders None bs1 env in
                        match uu____3959 with
                        | (vars,guards,envbody,decls,uu____3974) ->
                            let uu____3981 =
                              let uu____3989 =
                                FStar_TypeChecker_Env.is_reifiable env.tcenv
                                  lc1 in
                              if uu____3989
                              then reify_comp_and_body envbody lc1 body1
                              else (lc1, body1) in
                            (match uu____3981 with
                             | (lc2,body2) ->
                                 let uu____4014 = encode_term body2 envbody in
                                 (match uu____4014 with
                                  | (body3,decls') ->
                                      let uu____4021 =
                                        let uu____4026 = codomain_eff lc2 in
                                        match uu____4026 with
                                        | None  -> (None, [])
                                        | Some c ->
                                            let tfun =
                                              FStar_Syntax_Util.arrow bs1 c in
                                            let uu____4038 =
                                              encode_term tfun env in
                                            (match uu____4038 with
                                             | (t1,decls1) ->
                                                 ((Some t1), decls1)) in
                                      (match uu____4021 with
                                       | (arrow_t_opt,decls'') ->
                                           let key_body =
                                             let uu____4057 =
                                               let uu____4063 =
                                                 let uu____4064 =
                                                   let uu____4067 =
                                                     FStar_SMTEncoding_Util.mk_and_l
                                                       guards in
                                                   (uu____4067, body3) in
                                                 FStar_SMTEncoding_Util.mkImp
                                                   uu____4064 in
                                               ([], vars, uu____4063) in
                                             FStar_SMTEncoding_Util.mkForall
                                               uu____4057 in
                                           let cvars =
                                             FStar_SMTEncoding_Term.free_variables
                                               key_body in
                                           let cvars1 =
                                             match arrow_t_opt with
                                             | None  -> cvars
                                             | Some t1 ->
                                                 let uu____4075 =
                                                   let uu____4077 =
                                                     FStar_SMTEncoding_Term.free_variables
                                                       t1 in
                                                   FStar_List.append
                                                     uu____4077 cvars in
                                                 FStar_Util.remove_dups
                                                   FStar_SMTEncoding_Term.fv_eq
                                                   uu____4075 in
                                           let tkey =
                                             FStar_SMTEncoding_Util.mkForall
                                               ([], cvars1, key_body) in
                                           let tkey_hash =
                                             FStar_SMTEncoding_Term.hash_of_term
                                               tkey in
                                           let uu____4088 =
                                             FStar_Util.smap_try_find
                                               env.cache tkey_hash in
                                           (match uu____4088 with
                                            | Some (t1,uu____4103,uu____4104)
                                                ->
                                                let uu____4114 =
                                                  let uu____4115 =
                                                    let uu____4119 =
                                                      FStar_List.map
                                                        FStar_SMTEncoding_Util.mkFreeV
                                                        cvars1 in
                                                    (t1, uu____4119) in
                                                  FStar_SMTEncoding_Util.mkApp
                                                    uu____4115 in
                                                (uu____4114, [])
                                            | None  ->
                                                let uu____4130 =
                                                  is_an_eta_expansion env
                                                    vars body3 in
                                                (match uu____4130 with
                                                 | Some t1 ->
                                                     let decls1 =
                                                       let uu____4137 =
                                                         let uu____4138 =
                                                           FStar_Util.smap_size
                                                             env.cache in
                                                         uu____4138 =
                                                           cache_size in
                                                       if uu____4137
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
                                                         let uu____4154 =
                                                           let uu____4155 =
                                                             FStar_Util.digest_of_string
                                                               tkey_hash in
                                                           Prims.strcat
                                                             "Tm_abs_"
                                                             uu____4155 in
                                                         varops.mk_unique
                                                           uu____4154 in
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
                                                       let uu____4160 =
                                                         let uu____4164 =
                                                           FStar_List.map
                                                             FStar_SMTEncoding_Util.mkFreeV
                                                             cvars1 in
                                                         (fsym, uu____4164) in
                                                       FStar_SMTEncoding_Util.mkApp
                                                         uu____4160 in
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
                                                           let uu____4176 =
                                                             let uu____4177 =
                                                               let uu____4181
                                                                 =
                                                                 FStar_SMTEncoding_Util.mkForall
                                                                   ([[f]],
                                                                    cvars1,
                                                                    f_has_t) in
                                                               (uu____4181,
                                                                 (Some a_name),
                                                                 a_name) in
                                                             FStar_SMTEncoding_Term.Assume
                                                               uu____4177 in
                                                           [uu____4176] in
                                                     let interp_f =
                                                       let a_name =
                                                         Prims.strcat
                                                           "interpretation_"
                                                           fsym in
                                                       let uu____4189 =
                                                         let uu____4193 =
                                                           let uu____4194 =
                                                             let uu____4200 =
                                                               FStar_SMTEncoding_Util.mkEq
                                                                 (app, body3) in
                                                             ([[app]],
                                                               (FStar_List.append
                                                                  vars cvars1),
                                                               uu____4200) in
                                                           FStar_SMTEncoding_Util.mkForall
                                                             uu____4194 in
                                                         (uu____4193,
                                                           (Some a_name),
                                                           a_name) in
                                                       FStar_SMTEncoding_Term.Assume
                                                         uu____4189 in
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
                                                     (FStar_Util.smap_add
                                                        env.cache tkey_hash
                                                        (fsym, cvar_sorts,
                                                          f_decls);
                                                      (f, f_decls))))))))))
       | FStar_Syntax_Syntax.Tm_let
           ((uu____4218,{
                          FStar_Syntax_Syntax.lbname = FStar_Util.Inr
                            uu____4219;
                          FStar_Syntax_Syntax.lbunivs = uu____4220;
                          FStar_Syntax_Syntax.lbtyp = uu____4221;
                          FStar_Syntax_Syntax.lbeff = uu____4222;
                          FStar_Syntax_Syntax.lbdef = uu____4223;_}::uu____4224),uu____4225)
           -> failwith "Impossible: already handled by encoding of Sig_let"
       | FStar_Syntax_Syntax.Tm_let
           ((false
             ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inl x;
                FStar_Syntax_Syntax.lbunivs = uu____4243;
                FStar_Syntax_Syntax.lbtyp = t1;
                FStar_Syntax_Syntax.lbeff = uu____4245;
                FStar_Syntax_Syntax.lbdef = e1;_}::[]),e2)
           -> encode_let x t1 e1 e2 env encode_term
       | FStar_Syntax_Syntax.Tm_let uu____4261 ->
           (FStar_Errors.diag t0.FStar_Syntax_Syntax.pos
              "Non-top-level recursive functions are not yet fully encoded to the SMT solver; you may not be able to prove some facts";
            (let e = varops.fresh "let-rec" in
             let decl_e =
               FStar_SMTEncoding_Term.DeclFun
                 (e, [], FStar_SMTEncoding_Term.Term_sort, None) in
             let uu____4274 =
               FStar_SMTEncoding_Util.mkFreeV
                 (e, FStar_SMTEncoding_Term.Term_sort) in
             (uu____4274, [decl_e])))
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
              let uu____4316 = encode_term e1 env in
              match uu____4316 with
              | (ee1,decls1) ->
                  let uu____4323 =
                    FStar_Syntax_Subst.open_term [(x, None)] e2 in
                  (match uu____4323 with
                   | (xs,e21) ->
                       let uu____4337 = FStar_List.hd xs in
                       (match uu____4337 with
                        | (x1,uu____4345) ->
                            let env' = push_term_var env x1 ee1 in
                            let uu____4347 = encode_body e21 env' in
                            (match uu____4347 with
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
            let uu____4369 =
              let uu____4373 =
                let uu____4374 =
                  (FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown)
                    None FStar_Range.dummyRange in
                FStar_Syntax_Syntax.null_bv uu____4374 in
              gen_term_var env uu____4373 in
            match uu____4369 with
            | (scrsym,scr',env1) ->
                let uu____4388 = encode_term e env1 in
                (match uu____4388 with
                 | (scr,decls) ->
                     let uu____4395 =
                       let encode_branch b uu____4411 =
                         match uu____4411 with
                         | (else_case,decls1) ->
                             let uu____4422 =
                               FStar_Syntax_Subst.open_branch b in
                             (match uu____4422 with
                              | (p,w,br) ->
                                  let patterns = encode_pat env1 p in
                                  FStar_List.fold_right
                                    (fun uu____4452  ->
                                       fun uu____4453  ->
                                         match (uu____4452, uu____4453) with
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
                                                       fun uu____4490  ->
                                                         match uu____4490
                                                         with
                                                         | (x,t) ->
                                                             push_term_var
                                                               env2 x t) env1) in
                                             let uu____4495 =
                                               match w with
                                               | None  -> (guard, [])
                                               | Some w1 ->
                                                   let uu____4510 =
                                                     encode_term w1 env2 in
                                                   (match uu____4510 with
                                                    | (w2,decls21) ->
                                                        let uu____4518 =
                                                          let uu____4519 =
                                                            let uu____4522 =
                                                              let uu____4523
                                                                =
                                                                let uu____4526
                                                                  =
                                                                  FStar_SMTEncoding_Term.boxBool
                                                                    FStar_SMTEncoding_Util.mkTrue in
                                                                (w2,
                                                                  uu____4526) in
                                                              FStar_SMTEncoding_Util.mkEq
                                                                uu____4523 in
                                                            (guard,
                                                              uu____4522) in
                                                          FStar_SMTEncoding_Util.mkAnd
                                                            uu____4519 in
                                                        (uu____4518, decls21)) in
                                             (match uu____4495 with
                                              | (guard1,decls21) ->
                                                  let uu____4534 =
                                                    encode_br br env2 in
                                                  (match uu____4534 with
                                                   | (br1,decls3) ->
                                                       let uu____4542 =
                                                         FStar_SMTEncoding_Util.mkITE
                                                           (guard1, br1,
                                                             else_case1) in
                                                       (uu____4542,
                                                         (FStar_List.append
                                                            decls2
                                                            (FStar_List.append
                                                               decls21 decls3))))))
                                    patterns (else_case, decls1)) in
                       FStar_List.fold_right encode_branch pats
                         (default_case, decls) in
                     (match uu____4395 with
                      | (match_tm,decls1) ->
                          let uu____4554 =
                            FStar_SMTEncoding_Term.mkLet'
                              ([((scrsym, FStar_SMTEncoding_Term.Term_sort),
                                  scr)], match_tm) FStar_Range.dummyRange in
                          (uu____4554, decls1)))
and encode_pat:
  env_t -> FStar_Syntax_Syntax.pat -> (env_t* pattern) Prims.list =
  fun env  ->
    fun pat  ->
      match pat.FStar_Syntax_Syntax.v with
      | FStar_Syntax_Syntax.Pat_disj ps ->
          FStar_List.map (encode_one_pat env) ps
      | uu____4585 -> let uu____4586 = encode_one_pat env pat in [uu____4586]
and encode_one_pat: env_t -> FStar_Syntax_Syntax.pat -> (env_t* pattern) =
  fun env  ->
    fun pat  ->
      (let uu____4598 =
         FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low in
       if uu____4598
       then
         let uu____4599 = FStar_Syntax_Print.pat_to_string pat in
         FStar_Util.print1 "Encoding pattern %s\n" uu____4599
       else ());
      (let uu____4601 = FStar_TypeChecker_Util.decorated_pattern_as_term pat in
       match uu____4601 with
       | (vars,pat_term) ->
           let uu____4611 =
             FStar_All.pipe_right vars
               (FStar_List.fold_left
                  (fun uu____4634  ->
                     fun v1  ->
                       match uu____4634 with
                       | (env1,vars1) ->
                           let uu____4662 = gen_term_var env1 v1 in
                           (match uu____4662 with
                            | (xx,uu____4674,env2) ->
                                (env2,
                                  ((v1,
                                     (xx, FStar_SMTEncoding_Term.Term_sort))
                                  :: vars1)))) (env, [])) in
           (match uu____4611 with
            | (env1,vars1) ->
                let rec mk_guard pat1 scrutinee =
                  match pat1.FStar_Syntax_Syntax.v with
                  | FStar_Syntax_Syntax.Pat_disj uu____4721 ->
                      failwith "Impossible"
                  | FStar_Syntax_Syntax.Pat_var _
                    |FStar_Syntax_Syntax.Pat_wild _
                     |FStar_Syntax_Syntax.Pat_dot_term _ ->
                      FStar_SMTEncoding_Util.mkTrue
                  | FStar_Syntax_Syntax.Pat_constant c ->
                      let uu____4729 =
                        let uu____4732 = encode_const c in
                        (scrutinee, uu____4732) in
                      FStar_SMTEncoding_Util.mkEq uu____4729
                  | FStar_Syntax_Syntax.Pat_cons (f,args) ->
                      let is_f =
                        let tc_name =
                          FStar_TypeChecker_Env.typ_of_datacon env1.tcenv
                            (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                        let uu____4751 =
                          FStar_TypeChecker_Env.datacons_of_typ env1.tcenv
                            tc_name in
                        match uu____4751 with
                        | (uu____4755,uu____4756::[]) ->
                            FStar_SMTEncoding_Util.mkTrue
                        | uu____4758 ->
                            mk_data_tester env1
                              (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                              scrutinee in
                      let sub_term_guards =
                        FStar_All.pipe_right args
                          (FStar_List.mapi
                             (fun i  ->
                                fun uu____4779  ->
                                  match uu____4779 with
                                  | (arg,uu____4785) ->
                                      let proj =
                                        primitive_projector_by_pos env1.tcenv
                                          (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                          i in
                                      let uu____4795 =
                                        FStar_SMTEncoding_Util.mkApp
                                          (proj, [scrutinee]) in
                                      mk_guard arg uu____4795)) in
                      FStar_SMTEncoding_Util.mk_and_l (is_f ::
                        sub_term_guards) in
                let rec mk_projections pat1 scrutinee =
                  match pat1.FStar_Syntax_Syntax.v with
                  | FStar_Syntax_Syntax.Pat_disj uu____4814 ->
                      failwith "Impossible"
                  | FStar_Syntax_Syntax.Pat_dot_term (x,_)
                    |FStar_Syntax_Syntax.Pat_var x
                     |FStar_Syntax_Syntax.Pat_wild x -> [(x, scrutinee)]
                  | FStar_Syntax_Syntax.Pat_constant uu____4829 -> []
                  | FStar_Syntax_Syntax.Pat_cons (f,args) ->
                      let uu____4844 =
                        FStar_All.pipe_right args
                          (FStar_List.mapi
                             (fun i  ->
                                fun uu____4866  ->
                                  match uu____4866 with
                                  | (arg,uu____4875) ->
                                      let proj =
                                        primitive_projector_by_pos env1.tcenv
                                          (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                          i in
                                      let uu____4885 =
                                        FStar_SMTEncoding_Util.mkApp
                                          (proj, [scrutinee]) in
                                      mk_projections arg uu____4885)) in
                      FStar_All.pipe_right uu____4844 FStar_List.flatten in
                let pat_term1 uu____4901 = encode_term pat_term env1 in
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
      let uu____4908 =
        FStar_All.pipe_right l
          (FStar_List.fold_left
             (fun uu____4923  ->
                fun uu____4924  ->
                  match (uu____4923, uu____4924) with
                  | ((tms,decls),(t,uu____4944)) ->
                      let uu____4955 = encode_term t env in
                      (match uu____4955 with
                       | (t1,decls') ->
                           ((t1 :: tms), (FStar_List.append decls decls'))))
             ([], [])) in
      match uu____4908 with | (l1,decls) -> ((FStar_List.rev l1), decls)
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
            let uu____4993 = FStar_Syntax_Util.list_elements e in
            match uu____4993 with
            | Some l -> l
            | None  ->
                (FStar_Errors.warn e.FStar_Syntax_Syntax.pos
                   "SMT pattern is not a list literal; ignoring the pattern";
                 []) in
          let one_pat p =
            let uu____5011 =
              let uu____5021 = FStar_Syntax_Util.unmeta p in
              FStar_All.pipe_right uu____5021 FStar_Syntax_Util.head_and_args in
            match uu____5011 with
            | (head1,args) ->
                let uu____5052 =
                  let uu____5060 =
                    let uu____5061 = FStar_Syntax_Util.un_uinst head1 in
                    uu____5061.FStar_Syntax_Syntax.n in
                  (uu____5060, args) in
                (match uu____5052 with
                 | (FStar_Syntax_Syntax.Tm_fvar
                    fv,(uu____5075,uu____5076)::(e,uu____5078)::[]) when
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Syntax_Const.smtpat_lid
                     -> (e, None)
                 | (FStar_Syntax_Syntax.Tm_fvar fv,(e,uu____5109)::[]) when
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Syntax_Const.smtpatT_lid
                     -> (e, None)
                 | uu____5130 -> failwith "Unexpected pattern term") in
          let lemma_pats p =
            let elts = list_elements1 p in
            let smt_pat_or t1 =
              let uu____5163 =
                let uu____5173 = FStar_Syntax_Util.unmeta t1 in
                FStar_All.pipe_right uu____5173
                  FStar_Syntax_Util.head_and_args in
              match uu____5163 with
              | (head1,args) ->
                  let uu____5202 =
                    let uu____5210 =
                      let uu____5211 = FStar_Syntax_Util.un_uinst head1 in
                      uu____5211.FStar_Syntax_Syntax.n in
                    (uu____5210, args) in
                  (match uu____5202 with
                   | (FStar_Syntax_Syntax.Tm_fvar fv,(e,uu____5224)::[]) when
                       FStar_Syntax_Syntax.fv_eq_lid fv
                         FStar_Syntax_Const.smtpatOr_lid
                       -> Some e
                   | uu____5244 -> None) in
            match elts with
            | t1::[] ->
                let uu____5262 = smt_pat_or t1 in
                (match uu____5262 with
                 | Some e ->
                     let uu____5278 = list_elements1 e in
                     FStar_All.pipe_right uu____5278
                       (FStar_List.map
                          (fun branch1  ->
                             let uu____5295 = list_elements1 branch1 in
                             FStar_All.pipe_right uu____5295
                               (FStar_List.map one_pat)))
                 | uu____5309 ->
                     let uu____5313 =
                       FStar_All.pipe_right elts (FStar_List.map one_pat) in
                     [uu____5313])
            | uu____5344 ->
                let uu____5346 =
                  FStar_All.pipe_right elts (FStar_List.map one_pat) in
                [uu____5346] in
          let uu____5377 =
            let uu____5393 =
              let uu____5394 = FStar_Syntax_Subst.compress t in
              uu____5394.FStar_Syntax_Syntax.n in
            match uu____5393 with
            | FStar_Syntax_Syntax.Tm_arrow (binders,c) ->
                let uu____5424 = FStar_Syntax_Subst.open_comp binders c in
                (match uu____5424 with
                 | (binders1,c1) ->
                     (match c1.FStar_Syntax_Syntax.n with
                      | FStar_Syntax_Syntax.Comp
                          { FStar_Syntax_Syntax.comp_univs = uu____5459;
                            FStar_Syntax_Syntax.effect_name = uu____5460;
                            FStar_Syntax_Syntax.result_typ = uu____5461;
                            FStar_Syntax_Syntax.effect_args =
                              (pre,uu____5463)::(post,uu____5465)::(pats,uu____5467)::[];
                            FStar_Syntax_Syntax.flags = uu____5468;_}
                          ->
                          let pats' =
                            match new_pats with
                            | Some new_pats' -> new_pats'
                            | None  -> pats in
                          let uu____5502 = lemma_pats pats' in
                          (binders1, pre, post, uu____5502)
                      | uu____5521 -> failwith "impos"))
            | uu____5537 -> failwith "Impos" in
          match uu____5377 with
          | (binders,pre,post,patterns) ->
              let uu____5581 = encode_binders None binders env in
              (match uu____5581 with
               | (vars,guards,env1,decls,uu____5596) ->
                   let uu____5603 =
                     let uu____5610 =
                       FStar_All.pipe_right patterns
                         (FStar_List.map
                            (fun branch1  ->
                               let uu____5641 =
                                 let uu____5646 =
                                   FStar_All.pipe_right branch1
                                     (FStar_List.map
                                        (fun uu____5662  ->
                                           match uu____5662 with
                                           | (t1,uu____5669) ->
                                               encode_term t1
                                                 (let uu___152_5672 = env1 in
                                                  {
                                                    bindings =
                                                      (uu___152_5672.bindings);
                                                    depth =
                                                      (uu___152_5672.depth);
                                                    tcenv =
                                                      (uu___152_5672.tcenv);
                                                    warn =
                                                      (uu___152_5672.warn);
                                                    cache =
                                                      (uu___152_5672.cache);
                                                    nolabels =
                                                      (uu___152_5672.nolabels);
                                                    use_zfuel_name = true;
                                                    encode_non_total_function_typ
                                                      =
                                                      (uu___152_5672.encode_non_total_function_typ);
                                                    current_module_name =
                                                      (uu___152_5672.current_module_name)
                                                  }))) in
                                 FStar_All.pipe_right uu____5646
                                   FStar_List.unzip in
                               match uu____5641 with
                               | (pats,decls1) -> (pats, decls1))) in
                     FStar_All.pipe_right uu____5610 FStar_List.unzip in
                   (match uu____5603 with
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
                                           let uu____5736 =
                                             let uu____5737 =
                                               FStar_SMTEncoding_Util.mkFreeV
                                                 l in
                                             FStar_SMTEncoding_Util.mk_Precedes
                                               uu____5737 e in
                                           uu____5736 :: p))
                               | uu____5738 ->
                                   let rec aux tl1 vars1 =
                                     match vars1 with
                                     | [] ->
                                         FStar_All.pipe_right pats
                                           (FStar_List.map
                                              (fun p  ->
                                                 let uu____5767 =
                                                   FStar_SMTEncoding_Util.mk_Precedes
                                                     tl1 e in
                                                 uu____5767 :: p))
                                     | (x,FStar_SMTEncoding_Term.Term_sort )::vars2
                                         ->
                                         let uu____5775 =
                                           let uu____5776 =
                                             FStar_SMTEncoding_Util.mkFreeV
                                               (x,
                                                 FStar_SMTEncoding_Term.Term_sort) in
                                           FStar_SMTEncoding_Util.mk_LexCons
                                             uu____5776 tl1 in
                                         aux uu____5775 vars2
                                     | uu____5777 -> pats in
                                   let uu____5781 =
                                     FStar_SMTEncoding_Util.mkFreeV
                                       ("Prims.LexTop",
                                         FStar_SMTEncoding_Term.Term_sort) in
                                   aux uu____5781 vars) in
                        let env2 =
                          let uu___153_5783 = env1 in
                          {
                            bindings = (uu___153_5783.bindings);
                            depth = (uu___153_5783.depth);
                            tcenv = (uu___153_5783.tcenv);
                            warn = (uu___153_5783.warn);
                            cache = (uu___153_5783.cache);
                            nolabels = true;
                            use_zfuel_name = (uu___153_5783.use_zfuel_name);
                            encode_non_total_function_typ =
                              (uu___153_5783.encode_non_total_function_typ);
                            current_module_name =
                              (uu___153_5783.current_module_name)
                          } in
                        let uu____5784 =
                          let uu____5787 = FStar_Syntax_Util.unmeta pre in
                          encode_formula uu____5787 env2 in
                        (match uu____5784 with
                         | (pre1,decls'') ->
                             let uu____5792 =
                               let uu____5795 = FStar_Syntax_Util.unmeta post in
                               encode_formula uu____5795 env2 in
                             (match uu____5792 with
                              | (post1,decls''') ->
                                  let decls1 =
                                    FStar_List.append decls
                                      (FStar_List.append
                                         (FStar_List.flatten decls'1)
                                         (FStar_List.append decls'' decls''')) in
                                  let uu____5802 =
                                    let uu____5803 =
                                      let uu____5809 =
                                        let uu____5810 =
                                          let uu____5813 =
                                            FStar_SMTEncoding_Util.mk_and_l
                                              (pre1 :: guards) in
                                          (uu____5813, post1) in
                                        FStar_SMTEncoding_Util.mkImp
                                          uu____5810 in
                                      (pats1, vars, uu____5809) in
                                    FStar_SMTEncoding_Util.mkForall
                                      uu____5803 in
                                  (uu____5802, decls1)))))
and encode_formula:
  FStar_Syntax_Syntax.typ ->
    env_t -> (FStar_SMTEncoding_Term.term* FStar_SMTEncoding_Term.decls_t)
  =
  fun phi  ->
    fun env  ->
      let debug1 phi1 =
        let uu____5826 =
          FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv)
            (FStar_Options.Other "SMTEncoding") in
        if uu____5826
        then
          let uu____5827 = FStar_Syntax_Print.tag_of_term phi1 in
          let uu____5828 = FStar_Syntax_Print.term_to_string phi1 in
          FStar_Util.print2 "Formula (%s)  %s\n" uu____5827 uu____5828
        else () in
      let enc f r l =
        let uu____5855 =
          FStar_Util.fold_map
            (fun decls  ->
               fun x  ->
                 let uu____5868 = encode_term (Prims.fst x) env in
                 match uu____5868 with
                 | (t,decls') -> ((FStar_List.append decls decls'), t)) [] l in
        match uu____5855 with
        | (decls,args) ->
            let uu____5885 =
              let uu___154_5886 = f args in
              {
                FStar_SMTEncoding_Term.tm =
                  (uu___154_5886.FStar_SMTEncoding_Term.tm);
                FStar_SMTEncoding_Term.freevars =
                  (uu___154_5886.FStar_SMTEncoding_Term.freevars);
                FStar_SMTEncoding_Term.rng = r
              } in
            (uu____5885, decls) in
      let const_op f r uu____5905 = let uu____5908 = f r in (uu____5908, []) in
      let un_op f l =
        let uu____5924 = FStar_List.hd l in FStar_All.pipe_left f uu____5924 in
      let bin_op f uu___126_5937 =
        match uu___126_5937 with
        | t1::t2::[] -> f (t1, t2)
        | uu____5945 -> failwith "Impossible" in
      let enc_prop_c f r l =
        let uu____5972 =
          FStar_Util.fold_map
            (fun decls  ->
               fun uu____5981  ->
                 match uu____5981 with
                 | (t,uu____5989) ->
                     let uu____5990 = encode_formula t env in
                     (match uu____5990 with
                      | (phi1,decls') ->
                          ((FStar_List.append decls decls'), phi1))) [] l in
        match uu____5972 with
        | (decls,phis) ->
            let uu____6007 =
              let uu___155_6008 = f phis in
              {
                FStar_SMTEncoding_Term.tm =
                  (uu___155_6008.FStar_SMTEncoding_Term.tm);
                FStar_SMTEncoding_Term.freevars =
                  (uu___155_6008.FStar_SMTEncoding_Term.freevars);
                FStar_SMTEncoding_Term.rng = r
              } in
            (uu____6007, decls) in
      let eq_op r uu___127_6024 =
        match uu___127_6024 with
        | _::e1::e2::[]|_::_::e1::e2::[] ->
            let uu____6084 = enc (bin_op FStar_SMTEncoding_Util.mkEq) in
            uu____6084 r [e1; e2]
        | l ->
            let uu____6104 = enc (bin_op FStar_SMTEncoding_Util.mkEq) in
            uu____6104 r l in
      let mk_imp1 r uu___128_6123 =
        match uu___128_6123 with
        | (lhs,uu____6127)::(rhs,uu____6129)::[] ->
            let uu____6150 = encode_formula rhs env in
            (match uu____6150 with
             | (l1,decls1) ->
                 (match l1.FStar_SMTEncoding_Term.tm with
                  | FStar_SMTEncoding_Term.App
                      (FStar_SMTEncoding_Term.TrueOp ,uu____6159) ->
                      (l1, decls1)
                  | uu____6162 ->
                      let uu____6163 = encode_formula lhs env in
                      (match uu____6163 with
                       | (l2,decls2) ->
                           let uu____6170 =
                             FStar_SMTEncoding_Term.mkImp (l2, l1) r in
                           (uu____6170, (FStar_List.append decls1 decls2)))))
        | uu____6172 -> failwith "impossible" in
      let mk_ite r uu___129_6187 =
        match uu___129_6187 with
        | (guard,uu____6191)::(_then,uu____6193)::(_else,uu____6195)::[] ->
            let uu____6224 = encode_formula guard env in
            (match uu____6224 with
             | (g,decls1) ->
                 let uu____6231 = encode_formula _then env in
                 (match uu____6231 with
                  | (t,decls2) ->
                      let uu____6238 = encode_formula _else env in
                      (match uu____6238 with
                       | (e,decls3) ->
                           let res = FStar_SMTEncoding_Term.mkITE (g, t, e) r in
                           (res,
                             (FStar_List.append decls1
                                (FStar_List.append decls2 decls3))))))
        | uu____6247 -> failwith "impossible" in
      let unboxInt_l f l =
        let uu____6266 = FStar_List.map FStar_SMTEncoding_Term.unboxInt l in
        f uu____6266 in
      let connectives =
        let uu____6278 =
          let uu____6287 = enc_prop_c (bin_op FStar_SMTEncoding_Util.mkAnd) in
          (FStar_Syntax_Const.and_lid, uu____6287) in
        let uu____6300 =
          let uu____6310 =
            let uu____6319 = enc_prop_c (bin_op FStar_SMTEncoding_Util.mkOr) in
            (FStar_Syntax_Const.or_lid, uu____6319) in
          let uu____6332 =
            let uu____6342 =
              let uu____6352 =
                let uu____6361 =
                  enc_prop_c (bin_op FStar_SMTEncoding_Util.mkIff) in
                (FStar_Syntax_Const.iff_lid, uu____6361) in
              let uu____6374 =
                let uu____6384 =
                  let uu____6394 =
                    let uu____6403 =
                      enc_prop_c (un_op FStar_SMTEncoding_Util.mkNot) in
                    (FStar_Syntax_Const.not_lid, uu____6403) in
                  [uu____6394;
                  (FStar_Syntax_Const.eq2_lid, eq_op);
                  (FStar_Syntax_Const.eq3_lid, eq_op);
                  (FStar_Syntax_Const.true_lid,
                    (const_op FStar_SMTEncoding_Term.mkTrue));
                  (FStar_Syntax_Const.false_lid,
                    (const_op FStar_SMTEncoding_Term.mkFalse))] in
                (FStar_Syntax_Const.ite_lid, mk_ite) :: uu____6384 in
              uu____6352 :: uu____6374 in
            (FStar_Syntax_Const.imp_lid, mk_imp1) :: uu____6342 in
          uu____6310 :: uu____6332 in
        uu____6278 :: uu____6300 in
      let rec fallback phi1 =
        match phi1.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_meta
            (phi',FStar_Syntax_Syntax.Meta_labeled (msg,r,b)) ->
            let uu____6565 = encode_formula phi' env in
            (match uu____6565 with
             | (phi2,decls) ->
                 let uu____6572 =
                   FStar_SMTEncoding_Term.mk
                     (FStar_SMTEncoding_Term.Labeled (phi2, msg, r)) r in
                 (uu____6572, decls))
        | FStar_Syntax_Syntax.Tm_meta uu____6573 ->
            let uu____6578 = FStar_Syntax_Util.unmeta phi1 in
            encode_formula uu____6578 env
        | FStar_Syntax_Syntax.Tm_match (e,pats) ->
            let uu____6607 =
              encode_match e pats FStar_SMTEncoding_Util.mkFalse env
                encode_formula in
            (match uu____6607 with | (t,decls) -> (t, decls))
        | FStar_Syntax_Syntax.Tm_let
            ((false
              ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inl x;
                 FStar_Syntax_Syntax.lbunivs = uu____6615;
                 FStar_Syntax_Syntax.lbtyp = t1;
                 FStar_Syntax_Syntax.lbeff = uu____6617;
                 FStar_Syntax_Syntax.lbdef = e1;_}::[]),e2)
            ->
            let uu____6633 = encode_let x t1 e1 e2 env encode_formula in
            (match uu____6633 with | (t,decls) -> (t, decls))
        | FStar_Syntax_Syntax.Tm_app (head1,args) ->
            let head2 = FStar_Syntax_Util.un_uinst head1 in
            (match ((head2.FStar_Syntax_Syntax.n), args) with
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,uu____6665::(x,uu____6667)::(t,uu____6669)::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Syntax_Const.has_type_lid
                 ->
                 let uu____6703 = encode_term x env in
                 (match uu____6703 with
                  | (x1,decls) ->
                      let uu____6710 = encode_term t env in
                      (match uu____6710 with
                       | (t1,decls') ->
                           let uu____6717 =
                             FStar_SMTEncoding_Term.mk_HasType x1 t1 in
                           (uu____6717, (FStar_List.append decls decls'))))
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(r,uu____6721)::(msg,uu____6723)::(phi2,uu____6725)::[])
                 when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Syntax_Const.labeled_lid
                 ->
                 let uu____6759 =
                   let uu____6762 =
                     let uu____6763 = FStar_Syntax_Subst.compress r in
                     uu____6763.FStar_Syntax_Syntax.n in
                   let uu____6766 =
                     let uu____6767 = FStar_Syntax_Subst.compress msg in
                     uu____6767.FStar_Syntax_Syntax.n in
                   (uu____6762, uu____6766) in
                 (match uu____6759 with
                  | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range
                     r1),FStar_Syntax_Syntax.Tm_constant
                     (FStar_Const.Const_string (s,uu____6774))) ->
                      let phi3 =
                        (FStar_Syntax_Syntax.mk
                           (FStar_Syntax_Syntax.Tm_meta
                              (phi2,
                                (FStar_Syntax_Syntax.Meta_labeled
                                   ((FStar_Util.string_of_unicode s), r1,
                                     false))))) None r1 in
                      fallback phi3
                  | uu____6790 -> fallback phi2)
             | uu____6793 when head_redex env head2 ->
                 let uu____6801 = whnf env phi1 in
                 encode_formula uu____6801 env
             | uu____6802 ->
                 let uu____6810 = encode_term phi1 env in
                 (match uu____6810 with
                  | (tt,decls) ->
                      let uu____6817 =
                        FStar_SMTEncoding_Term.mk_Valid
                          (let uu___156_6818 = tt in
                           {
                             FStar_SMTEncoding_Term.tm =
                               (uu___156_6818.FStar_SMTEncoding_Term.tm);
                             FStar_SMTEncoding_Term.freevars =
                               (uu___156_6818.FStar_SMTEncoding_Term.freevars);
                             FStar_SMTEncoding_Term.rng =
                               (phi1.FStar_Syntax_Syntax.pos)
                           }) in
                      (uu____6817, decls)))
        | uu____6821 ->
            let uu____6822 = encode_term phi1 env in
            (match uu____6822 with
             | (tt,decls) ->
                 let uu____6829 =
                   FStar_SMTEncoding_Term.mk_Valid
                     (let uu___157_6830 = tt in
                      {
                        FStar_SMTEncoding_Term.tm =
                          (uu___157_6830.FStar_SMTEncoding_Term.tm);
                        FStar_SMTEncoding_Term.freevars =
                          (uu___157_6830.FStar_SMTEncoding_Term.freevars);
                        FStar_SMTEncoding_Term.rng =
                          (phi1.FStar_Syntax_Syntax.pos)
                      }) in
                 (uu____6829, decls)) in
      let encode_q_body env1 bs ps body =
        let uu____6857 = encode_binders None bs env1 in
        match uu____6857 with
        | (vars,guards,env2,decls,uu____6879) ->
            let uu____6886 =
              let uu____6893 =
                FStar_All.pipe_right ps
                  (FStar_List.map
                     (fun p  ->
                        let uu____6916 =
                          let uu____6921 =
                            FStar_All.pipe_right p
                              (FStar_List.map
                                 (fun uu____6935  ->
                                    match uu____6935 with
                                    | (t,uu____6941) ->
                                        encode_term t
                                          (let uu___158_6942 = env2 in
                                           {
                                             bindings =
                                               (uu___158_6942.bindings);
                                             depth = (uu___158_6942.depth);
                                             tcenv = (uu___158_6942.tcenv);
                                             warn = (uu___158_6942.warn);
                                             cache = (uu___158_6942.cache);
                                             nolabels =
                                               (uu___158_6942.nolabels);
                                             use_zfuel_name = true;
                                             encode_non_total_function_typ =
                                               (uu___158_6942.encode_non_total_function_typ);
                                             current_module_name =
                                               (uu___158_6942.current_module_name)
                                           }))) in
                          FStar_All.pipe_right uu____6921 FStar_List.unzip in
                        match uu____6916 with
                        | (p1,decls1) -> (p1, (FStar_List.flatten decls1)))) in
              FStar_All.pipe_right uu____6893 FStar_List.unzip in
            (match uu____6886 with
             | (pats,decls') ->
                 let uu____6994 = encode_formula body env2 in
                 (match uu____6994 with
                  | (body1,decls'') ->
                      let guards1 =
                        match pats with
                        | ({
                             FStar_SMTEncoding_Term.tm =
                               FStar_SMTEncoding_Term.App
                               (FStar_SMTEncoding_Term.Var gf,p::[]);
                             FStar_SMTEncoding_Term.freevars = uu____7013;
                             FStar_SMTEncoding_Term.rng = uu____7014;_}::[])::[]
                            when
                            (FStar_Ident.text_of_lid
                               FStar_Syntax_Const.guard_free)
                              = gf
                            -> []
                        | uu____7022 -> guards in
                      let uu____7025 =
                        FStar_SMTEncoding_Util.mk_and_l guards1 in
                      (vars, pats, uu____7025, body1,
                        (FStar_List.append decls
                           (FStar_List.append (FStar_List.flatten decls')
                              decls''))))) in
      debug1 phi;
      (let phi1 = FStar_Syntax_Util.unascribe phi in
       let check_pattern_vars vars pats =
         let pats1 =
           FStar_All.pipe_right pats
             (FStar_List.map
                (fun uu____7059  ->
                   match uu____7059 with
                   | (x,uu____7063) ->
                       FStar_TypeChecker_Normalize.normalize
                         [FStar_TypeChecker_Normalize.Beta;
                         FStar_TypeChecker_Normalize.AllowUnboundUniverses;
                         FStar_TypeChecker_Normalize.EraseUniverses]
                         env.tcenv x)) in
         match pats1 with
         | [] -> ()
         | hd1::tl1 ->
             let pat_vars =
               let uu____7069 = FStar_Syntax_Free.names hd1 in
               FStar_List.fold_left
                 (fun out  ->
                    fun x  ->
                      let uu____7075 = FStar_Syntax_Free.names x in
                      FStar_Util.set_union out uu____7075) uu____7069 tl1 in
             let uu____7077 =
               FStar_All.pipe_right vars
                 (FStar_Util.find_opt
                    (fun uu____7089  ->
                       match uu____7089 with
                       | (b,uu____7093) ->
                           let uu____7094 = FStar_Util.set_mem b pat_vars in
                           Prims.op_Negation uu____7094)) in
             (match uu____7077 with
              | None  -> ()
              | Some (x,uu____7098) ->
                  let pos =
                    FStar_List.fold_left
                      (fun out  ->
                         fun t  ->
                           FStar_Range.union_ranges out
                             t.FStar_Syntax_Syntax.pos)
                      hd1.FStar_Syntax_Syntax.pos tl1 in
                  let uu____7108 =
                    let uu____7109 = FStar_Syntax_Print.bv_to_string x in
                    FStar_Util.format1
                      "SMT pattern misses at least one bound variable: %s"
                      uu____7109 in
                  FStar_Errors.warn pos uu____7108) in
       let uu____7110 = FStar_Syntax_Util.destruct_typ_as_formula phi1 in
       match uu____7110 with
       | None  -> fallback phi1
       | Some (FStar_Syntax_Util.BaseConn (op,arms)) ->
           let uu____7116 =
             FStar_All.pipe_right connectives
               (FStar_List.tryFind
                  (fun uu____7152  ->
                     match uu____7152 with
                     | (l,uu____7162) -> FStar_Ident.lid_equals op l)) in
           (match uu____7116 with
            | None  -> fallback phi1
            | Some (uu____7185,f) -> f phi1.FStar_Syntax_Syntax.pos arms)
       | Some (FStar_Syntax_Util.QAll (vars,pats,body)) ->
           (FStar_All.pipe_right pats
              (FStar_List.iter (check_pattern_vars vars));
            (let uu____7214 = encode_q_body env vars pats body in
             match uu____7214 with
             | (vars1,pats1,guard,body1,decls) ->
                 let tm =
                   let uu____7240 =
                     let uu____7246 =
                       FStar_SMTEncoding_Util.mkImp (guard, body1) in
                     (pats1, vars1, uu____7246) in
                   FStar_SMTEncoding_Term.mkForall uu____7240
                     phi1.FStar_Syntax_Syntax.pos in
                 (tm, decls)))
       | Some (FStar_Syntax_Util.QEx (vars,pats,body)) ->
           (FStar_All.pipe_right pats
              (FStar_List.iter (check_pattern_vars vars));
            (let uu____7258 = encode_q_body env vars pats body in
             match uu____7258 with
             | (vars1,pats1,guard,body1,decls) ->
                 let uu____7283 =
                   let uu____7284 =
                     let uu____7290 =
                       FStar_SMTEncoding_Util.mkAnd (guard, body1) in
                     (pats1, vars1, uu____7290) in
                   FStar_SMTEncoding_Term.mkExists uu____7284
                     phi1.FStar_Syntax_Syntax.pos in
                 (uu____7283, decls))))
type prims_t =
  {
  mk:
    FStar_Ident.lident ->
      Prims.string ->
        (FStar_SMTEncoding_Term.term* FStar_SMTEncoding_Term.decl Prims.list);
  is: FStar_Ident.lident -> Prims.bool;}
let prims: prims_t =
  let uu____7339 = fresh_fvar "a" FStar_SMTEncoding_Term.Term_sort in
  match uu____7339 with
  | (asym,a) ->
      let uu____7344 = fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort in
      (match uu____7344 with
       | (xsym,x) ->
           let uu____7349 = fresh_fvar "y" FStar_SMTEncoding_Term.Term_sort in
           (match uu____7349 with
            | (ysym,y) ->
                let quant vars body x1 =
                  let xname_decl =
                    let uu____7379 =
                      let uu____7385 =
                        FStar_All.pipe_right vars (FStar_List.map Prims.snd) in
                      (x1, uu____7385, FStar_SMTEncoding_Term.Term_sort,
                        None) in
                    FStar_SMTEncoding_Term.DeclFun uu____7379 in
                  let xtok = Prims.strcat x1 "@tok" in
                  let xtok_decl =
                    FStar_SMTEncoding_Term.DeclFun
                      (xtok, [], FStar_SMTEncoding_Term.Term_sort, None) in
                  let xapp =
                    let uu____7400 =
                      let uu____7404 =
                        FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars in
                      (x1, uu____7404) in
                    FStar_SMTEncoding_Util.mkApp uu____7400 in
                  let xtok1 = FStar_SMTEncoding_Util.mkApp (xtok, []) in
                  let xtok_app = mk_Apply xtok1 vars in
                  let uu____7412 =
                    let uu____7414 =
                      let uu____7416 =
                        let uu____7418 =
                          let uu____7419 =
                            let uu____7423 =
                              let uu____7424 =
                                let uu____7430 =
                                  FStar_SMTEncoding_Util.mkEq (xapp, body) in
                                ([[xapp]], vars, uu____7430) in
                              FStar_SMTEncoding_Util.mkForall uu____7424 in
                            (uu____7423, None,
                              (Prims.strcat "primitive_" x1)) in
                          FStar_SMTEncoding_Term.Assume uu____7419 in
                        let uu____7439 =
                          let uu____7441 =
                            let uu____7442 =
                              let uu____7446 =
                                let uu____7447 =
                                  let uu____7453 =
                                    FStar_SMTEncoding_Util.mkEq
                                      (xtok_app, xapp) in
                                  ([[xtok_app]], vars, uu____7453) in
                                FStar_SMTEncoding_Util.mkForall uu____7447 in
                              (uu____7446,
                                (Some "Name-token correspondence"),
                                (Prims.strcat "token_correspondence_" x1)) in
                            FStar_SMTEncoding_Term.Assume uu____7442 in
                          [uu____7441] in
                        uu____7418 :: uu____7439 in
                      xtok_decl :: uu____7416 in
                    xname_decl :: uu____7414 in
                  (xtok1, uu____7412) in
                let axy =
                  [(asym, FStar_SMTEncoding_Term.Term_sort);
                  (xsym, FStar_SMTEncoding_Term.Term_sort);
                  (ysym, FStar_SMTEncoding_Term.Term_sort)] in
                let xy =
                  [(xsym, FStar_SMTEncoding_Term.Term_sort);
                  (ysym, FStar_SMTEncoding_Term.Term_sort)] in
                let qx = [(xsym, FStar_SMTEncoding_Term.Term_sort)] in
                let prims1 =
                  let uu____7502 =
                    let uu____7510 =
                      let uu____7516 =
                        let uu____7517 = FStar_SMTEncoding_Util.mkEq (x, y) in
                        FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool
                          uu____7517 in
                      quant axy uu____7516 in
                    (FStar_Syntax_Const.op_Eq, uu____7510) in
                  let uu____7523 =
                    let uu____7532 =
                      let uu____7540 =
                        let uu____7546 =
                          let uu____7547 =
                            let uu____7548 =
                              FStar_SMTEncoding_Util.mkEq (x, y) in
                            FStar_SMTEncoding_Util.mkNot uu____7548 in
                          FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool
                            uu____7547 in
                        quant axy uu____7546 in
                      (FStar_Syntax_Const.op_notEq, uu____7540) in
                    let uu____7554 =
                      let uu____7563 =
                        let uu____7571 =
                          let uu____7577 =
                            let uu____7578 =
                              let uu____7579 =
                                let uu____7582 =
                                  FStar_SMTEncoding_Term.unboxInt x in
                                let uu____7583 =
                                  FStar_SMTEncoding_Term.unboxInt y in
                                (uu____7582, uu____7583) in
                              FStar_SMTEncoding_Util.mkLT uu____7579 in
                            FStar_All.pipe_left
                              FStar_SMTEncoding_Term.boxBool uu____7578 in
                          quant xy uu____7577 in
                        (FStar_Syntax_Const.op_LT, uu____7571) in
                      let uu____7589 =
                        let uu____7598 =
                          let uu____7606 =
                            let uu____7612 =
                              let uu____7613 =
                                let uu____7614 =
                                  let uu____7617 =
                                    FStar_SMTEncoding_Term.unboxInt x in
                                  let uu____7618 =
                                    FStar_SMTEncoding_Term.unboxInt y in
                                  (uu____7617, uu____7618) in
                                FStar_SMTEncoding_Util.mkLTE uu____7614 in
                              FStar_All.pipe_left
                                FStar_SMTEncoding_Term.boxBool uu____7613 in
                            quant xy uu____7612 in
                          (FStar_Syntax_Const.op_LTE, uu____7606) in
                        let uu____7624 =
                          let uu____7633 =
                            let uu____7641 =
                              let uu____7647 =
                                let uu____7648 =
                                  let uu____7649 =
                                    let uu____7652 =
                                      FStar_SMTEncoding_Term.unboxInt x in
                                    let uu____7653 =
                                      FStar_SMTEncoding_Term.unboxInt y in
                                    (uu____7652, uu____7653) in
                                  FStar_SMTEncoding_Util.mkGT uu____7649 in
                                FStar_All.pipe_left
                                  FStar_SMTEncoding_Term.boxBool uu____7648 in
                              quant xy uu____7647 in
                            (FStar_Syntax_Const.op_GT, uu____7641) in
                          let uu____7659 =
                            let uu____7668 =
                              let uu____7676 =
                                let uu____7682 =
                                  let uu____7683 =
                                    let uu____7684 =
                                      let uu____7687 =
                                        FStar_SMTEncoding_Term.unboxInt x in
                                      let uu____7688 =
                                        FStar_SMTEncoding_Term.unboxInt y in
                                      (uu____7687, uu____7688) in
                                    FStar_SMTEncoding_Util.mkGTE uu____7684 in
                                  FStar_All.pipe_left
                                    FStar_SMTEncoding_Term.boxBool uu____7683 in
                                quant xy uu____7682 in
                              (FStar_Syntax_Const.op_GTE, uu____7676) in
                            let uu____7694 =
                              let uu____7703 =
                                let uu____7711 =
                                  let uu____7717 =
                                    let uu____7718 =
                                      let uu____7719 =
                                        let uu____7722 =
                                          FStar_SMTEncoding_Term.unboxInt x in
                                        let uu____7723 =
                                          FStar_SMTEncoding_Term.unboxInt y in
                                        (uu____7722, uu____7723) in
                                      FStar_SMTEncoding_Util.mkSub uu____7719 in
                                    FStar_All.pipe_left
                                      FStar_SMTEncoding_Term.boxInt
                                      uu____7718 in
                                  quant xy uu____7717 in
                                (FStar_Syntax_Const.op_Subtraction,
                                  uu____7711) in
                              let uu____7729 =
                                let uu____7738 =
                                  let uu____7746 =
                                    let uu____7752 =
                                      let uu____7753 =
                                        let uu____7754 =
                                          FStar_SMTEncoding_Term.unboxInt x in
                                        FStar_SMTEncoding_Util.mkMinus
                                          uu____7754 in
                                      FStar_All.pipe_left
                                        FStar_SMTEncoding_Term.boxInt
                                        uu____7753 in
                                    quant qx uu____7752 in
                                  (FStar_Syntax_Const.op_Minus, uu____7746) in
                                let uu____7760 =
                                  let uu____7769 =
                                    let uu____7777 =
                                      let uu____7783 =
                                        let uu____7784 =
                                          let uu____7785 =
                                            let uu____7788 =
                                              FStar_SMTEncoding_Term.unboxInt
                                                x in
                                            let uu____7789 =
                                              FStar_SMTEncoding_Term.unboxInt
                                                y in
                                            (uu____7788, uu____7789) in
                                          FStar_SMTEncoding_Util.mkAdd
                                            uu____7785 in
                                        FStar_All.pipe_left
                                          FStar_SMTEncoding_Term.boxInt
                                          uu____7784 in
                                      quant xy uu____7783 in
                                    (FStar_Syntax_Const.op_Addition,
                                      uu____7777) in
                                  let uu____7795 =
                                    let uu____7804 =
                                      let uu____7812 =
                                        let uu____7818 =
                                          let uu____7819 =
                                            let uu____7820 =
                                              let uu____7823 =
                                                FStar_SMTEncoding_Term.unboxInt
                                                  x in
                                              let uu____7824 =
                                                FStar_SMTEncoding_Term.unboxInt
                                                  y in
                                              (uu____7823, uu____7824) in
                                            FStar_SMTEncoding_Util.mkMul
                                              uu____7820 in
                                          FStar_All.pipe_left
                                            FStar_SMTEncoding_Term.boxInt
                                            uu____7819 in
                                        quant xy uu____7818 in
                                      (FStar_Syntax_Const.op_Multiply,
                                        uu____7812) in
                                    let uu____7830 =
                                      let uu____7839 =
                                        let uu____7847 =
                                          let uu____7853 =
                                            let uu____7854 =
                                              let uu____7855 =
                                                let uu____7858 =
                                                  FStar_SMTEncoding_Term.unboxInt
                                                    x in
                                                let uu____7859 =
                                                  FStar_SMTEncoding_Term.unboxInt
                                                    y in
                                                (uu____7858, uu____7859) in
                                              FStar_SMTEncoding_Util.mkDiv
                                                uu____7855 in
                                            FStar_All.pipe_left
                                              FStar_SMTEncoding_Term.boxInt
                                              uu____7854 in
                                          quant xy uu____7853 in
                                        (FStar_Syntax_Const.op_Division,
                                          uu____7847) in
                                      let uu____7865 =
                                        let uu____7874 =
                                          let uu____7882 =
                                            let uu____7888 =
                                              let uu____7889 =
                                                let uu____7890 =
                                                  let uu____7893 =
                                                    FStar_SMTEncoding_Term.unboxInt
                                                      x in
                                                  let uu____7894 =
                                                    FStar_SMTEncoding_Term.unboxInt
                                                      y in
                                                  (uu____7893, uu____7894) in
                                                FStar_SMTEncoding_Util.mkMod
                                                  uu____7890 in
                                              FStar_All.pipe_left
                                                FStar_SMTEncoding_Term.boxInt
                                                uu____7889 in
                                            quant xy uu____7888 in
                                          (FStar_Syntax_Const.op_Modulus,
                                            uu____7882) in
                                        let uu____7900 =
                                          let uu____7909 =
                                            let uu____7917 =
                                              let uu____7923 =
                                                let uu____7924 =
                                                  let uu____7925 =
                                                    let uu____7928 =
                                                      FStar_SMTEncoding_Term.unboxBool
                                                        x in
                                                    let uu____7929 =
                                                      FStar_SMTEncoding_Term.unboxBool
                                                        y in
                                                    (uu____7928, uu____7929) in
                                                  FStar_SMTEncoding_Util.mkAnd
                                                    uu____7925 in
                                                FStar_All.pipe_left
                                                  FStar_SMTEncoding_Term.boxBool
                                                  uu____7924 in
                                              quant xy uu____7923 in
                                            (FStar_Syntax_Const.op_And,
                                              uu____7917) in
                                          let uu____7935 =
                                            let uu____7944 =
                                              let uu____7952 =
                                                let uu____7958 =
                                                  let uu____7959 =
                                                    let uu____7960 =
                                                      let uu____7963 =
                                                        FStar_SMTEncoding_Term.unboxBool
                                                          x in
                                                      let uu____7964 =
                                                        FStar_SMTEncoding_Term.unboxBool
                                                          y in
                                                      (uu____7963,
                                                        uu____7964) in
                                                    FStar_SMTEncoding_Util.mkOr
                                                      uu____7960 in
                                                  FStar_All.pipe_left
                                                    FStar_SMTEncoding_Term.boxBool
                                                    uu____7959 in
                                                quant xy uu____7958 in
                                              (FStar_Syntax_Const.op_Or,
                                                uu____7952) in
                                            let uu____7970 =
                                              let uu____7979 =
                                                let uu____7987 =
                                                  let uu____7993 =
                                                    let uu____7994 =
                                                      let uu____7995 =
                                                        FStar_SMTEncoding_Term.unboxBool
                                                          x in
                                                      FStar_SMTEncoding_Util.mkNot
                                                        uu____7995 in
                                                    FStar_All.pipe_left
                                                      FStar_SMTEncoding_Term.boxBool
                                                      uu____7994 in
                                                  quant qx uu____7993 in
                                                (FStar_Syntax_Const.op_Negation,
                                                  uu____7987) in
                                              [uu____7979] in
                                            uu____7944 :: uu____7970 in
                                          uu____7909 :: uu____7935 in
                                        uu____7874 :: uu____7900 in
                                      uu____7839 :: uu____7865 in
                                    uu____7804 :: uu____7830 in
                                  uu____7769 :: uu____7795 in
                                uu____7738 :: uu____7760 in
                              uu____7703 :: uu____7729 in
                            uu____7668 :: uu____7694 in
                          uu____7633 :: uu____7659 in
                        uu____7598 :: uu____7624 in
                      uu____7563 :: uu____7589 in
                    uu____7532 :: uu____7554 in
                  uu____7502 :: uu____7523 in
                let mk1 l v1 =
                  let uu____8123 =
                    let uu____8128 =
                      FStar_All.pipe_right prims1
                        (FStar_List.find
                           (fun uu____8160  ->
                              match uu____8160 with
                              | (l',uu____8169) ->
                                  FStar_Ident.lid_equals l l')) in
                    FStar_All.pipe_right uu____8128
                      (FStar_Option.map
                         (fun uu____8202  ->
                            match uu____8202 with | (uu____8213,b) -> b v1)) in
                  FStar_All.pipe_right uu____8123 FStar_Option.get in
                let is l =
                  FStar_All.pipe_right prims1
                    (FStar_Util.for_some
                       (fun uu____8254  ->
                          match uu____8254 with
                          | (l',uu____8263) -> FStar_Ident.lid_equals l l')) in
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
        let uu____8289 = fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort in
        match uu____8289 with
        | (xxsym,xx) ->
            let uu____8294 = fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort in
            (match uu____8294 with
             | (ffsym,ff) ->
                 let xx_has_type =
                   FStar_SMTEncoding_Term.mk_HasTypeFuel ff xx tapp in
                 let tapp_hash = FStar_SMTEncoding_Term.hash_of_term tapp in
                 let module_name = env.current_module_name in
                 let uu____8302 =
                   let uu____8306 =
                     let uu____8307 =
                       let uu____8313 =
                         let uu____8314 =
                           let uu____8317 =
                             let uu____8318 =
                               let uu____8321 =
                                 FStar_SMTEncoding_Util.mkApp
                                   ("PreType", [xx]) in
                               (tapp, uu____8321) in
                             FStar_SMTEncoding_Util.mkEq uu____8318 in
                           (xx_has_type, uu____8317) in
                         FStar_SMTEncoding_Util.mkImp uu____8314 in
                       ([[xx_has_type]],
                         ((xxsym, FStar_SMTEncoding_Term.Term_sort) ::
                         (ffsym, FStar_SMTEncoding_Term.Fuel_sort) :: vars),
                         uu____8313) in
                     FStar_SMTEncoding_Util.mkForall uu____8307 in
                   let uu____8334 =
                     let uu____8335 =
                       let uu____8336 =
                         let uu____8337 =
                           FStar_Util.digest_of_string tapp_hash in
                         Prims.strcat "_pretyping_" uu____8337 in
                       Prims.strcat module_name uu____8336 in
                     varops.mk_unique uu____8335 in
                   (uu____8306, (Some "pretyping"), uu____8334) in
                 FStar_SMTEncoding_Term.Assume uu____8302)
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
    let uu____8367 =
      let uu____8368 =
        let uu____8372 =
          FStar_SMTEncoding_Term.mk_HasType
            FStar_SMTEncoding_Term.mk_Term_unit tt in
        (uu____8372, (Some "unit typing"), "unit_typing") in
      FStar_SMTEncoding_Term.Assume uu____8368 in
    let uu____8374 =
      let uu____8376 =
        let uu____8377 =
          let uu____8381 =
            let uu____8382 =
              let uu____8388 =
                let uu____8389 =
                  let uu____8392 =
                    FStar_SMTEncoding_Util.mkEq
                      (x, FStar_SMTEncoding_Term.mk_Term_unit) in
                  (typing_pred, uu____8392) in
                FStar_SMTEncoding_Util.mkImp uu____8389 in
              ([[typing_pred]], [xx], uu____8388) in
            mkForall_fuel uu____8382 in
          (uu____8381, (Some "unit inversion"), "unit_inversion") in
        FStar_SMTEncoding_Term.Assume uu____8377 in
      [uu____8376] in
    uu____8367 :: uu____8374 in
  let mk_bool env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt in
    let bb = ("b", FStar_SMTEncoding_Term.Bool_sort) in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let uu____8420 =
      let uu____8421 =
        let uu____8425 =
          let uu____8426 =
            let uu____8432 =
              let uu____8435 =
                let uu____8437 = FStar_SMTEncoding_Term.boxBool b in
                [uu____8437] in
              [uu____8435] in
            let uu____8440 =
              let uu____8441 = FStar_SMTEncoding_Term.boxBool b in
              FStar_SMTEncoding_Term.mk_HasType uu____8441 tt in
            (uu____8432, [bb], uu____8440) in
          FStar_SMTEncoding_Util.mkForall uu____8426 in
        (uu____8425, (Some "bool typing"), "bool_typing") in
      FStar_SMTEncoding_Term.Assume uu____8421 in
    let uu____8452 =
      let uu____8454 =
        let uu____8455 =
          let uu____8459 =
            let uu____8460 =
              let uu____8466 =
                let uu____8467 =
                  let uu____8470 =
                    FStar_SMTEncoding_Term.mk_tester "BoxBool" x in
                  (typing_pred, uu____8470) in
                FStar_SMTEncoding_Util.mkImp uu____8467 in
              ([[typing_pred]], [xx], uu____8466) in
            mkForall_fuel uu____8460 in
          (uu____8459, (Some "bool inversion"), "bool_inversion") in
        FStar_SMTEncoding_Term.Assume uu____8455 in
      [uu____8454] in
    uu____8420 :: uu____8452 in
  let mk_int env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt in
    let typing_pred_y = FStar_SMTEncoding_Term.mk_HasType y tt in
    let aa = ("a", FStar_SMTEncoding_Term.Int_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let bb = ("b", FStar_SMTEncoding_Term.Int_sort) in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let precedes =
      let uu____8504 =
        let uu____8505 =
          let uu____8509 =
            let uu____8511 =
              let uu____8513 =
                let uu____8515 = FStar_SMTEncoding_Term.boxInt a in
                let uu____8516 =
                  let uu____8518 = FStar_SMTEncoding_Term.boxInt b in
                  [uu____8518] in
                uu____8515 :: uu____8516 in
              tt :: uu____8513 in
            tt :: uu____8511 in
          ("Prims.Precedes", uu____8509) in
        FStar_SMTEncoding_Util.mkApp uu____8505 in
      FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid uu____8504 in
    let precedes_y_x =
      let uu____8521 = FStar_SMTEncoding_Util.mkApp ("Precedes", [y; x]) in
      FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid uu____8521 in
    let uu____8523 =
      let uu____8524 =
        let uu____8528 =
          let uu____8529 =
            let uu____8535 =
              let uu____8538 =
                let uu____8540 = FStar_SMTEncoding_Term.boxInt b in
                [uu____8540] in
              [uu____8538] in
            let uu____8543 =
              let uu____8544 = FStar_SMTEncoding_Term.boxInt b in
              FStar_SMTEncoding_Term.mk_HasType uu____8544 tt in
            (uu____8535, [bb], uu____8543) in
          FStar_SMTEncoding_Util.mkForall uu____8529 in
        (uu____8528, (Some "int typing"), "int_typing") in
      FStar_SMTEncoding_Term.Assume uu____8524 in
    let uu____8555 =
      let uu____8557 =
        let uu____8558 =
          let uu____8562 =
            let uu____8563 =
              let uu____8569 =
                let uu____8570 =
                  let uu____8573 =
                    FStar_SMTEncoding_Term.mk_tester "BoxInt" x in
                  (typing_pred, uu____8573) in
                FStar_SMTEncoding_Util.mkImp uu____8570 in
              ([[typing_pred]], [xx], uu____8569) in
            mkForall_fuel uu____8563 in
          (uu____8562, (Some "int inversion"), "int_inversion") in
        FStar_SMTEncoding_Term.Assume uu____8558 in
      let uu____8586 =
        let uu____8588 =
          let uu____8589 =
            let uu____8593 =
              let uu____8594 =
                let uu____8600 =
                  let uu____8601 =
                    let uu____8604 =
                      let uu____8605 =
                        let uu____8607 =
                          let uu____8609 =
                            let uu____8611 =
                              let uu____8612 =
                                let uu____8615 =
                                  FStar_SMTEncoding_Term.unboxInt x in
                                let uu____8616 =
                                  FStar_SMTEncoding_Util.mkInteger'
                                    (Prims.parse_int "0") in
                                (uu____8615, uu____8616) in
                              FStar_SMTEncoding_Util.mkGT uu____8612 in
                            let uu____8617 =
                              let uu____8619 =
                                let uu____8620 =
                                  let uu____8623 =
                                    FStar_SMTEncoding_Term.unboxInt y in
                                  let uu____8624 =
                                    FStar_SMTEncoding_Util.mkInteger'
                                      (Prims.parse_int "0") in
                                  (uu____8623, uu____8624) in
                                FStar_SMTEncoding_Util.mkGTE uu____8620 in
                              let uu____8625 =
                                let uu____8627 =
                                  let uu____8628 =
                                    let uu____8631 =
                                      FStar_SMTEncoding_Term.unboxInt y in
                                    let uu____8632 =
                                      FStar_SMTEncoding_Term.unboxInt x in
                                    (uu____8631, uu____8632) in
                                  FStar_SMTEncoding_Util.mkLT uu____8628 in
                                [uu____8627] in
                              uu____8619 :: uu____8625 in
                            uu____8611 :: uu____8617 in
                          typing_pred_y :: uu____8609 in
                        typing_pred :: uu____8607 in
                      FStar_SMTEncoding_Util.mk_and_l uu____8605 in
                    (uu____8604, precedes_y_x) in
                  FStar_SMTEncoding_Util.mkImp uu____8601 in
                ([[typing_pred; typing_pred_y; precedes_y_x]], [xx; yy],
                  uu____8600) in
              mkForall_fuel uu____8594 in
            (uu____8593, (Some "well-founded ordering on nat (alt)"),
              "well-founded-ordering-on-nat") in
          FStar_SMTEncoding_Term.Assume uu____8589 in
        [uu____8588] in
      uu____8557 :: uu____8586 in
    uu____8523 :: uu____8555 in
  let mk_str env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt in
    let bb = ("b", FStar_SMTEncoding_Term.String_sort) in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let uu____8662 =
      let uu____8663 =
        let uu____8667 =
          let uu____8668 =
            let uu____8674 =
              let uu____8677 =
                let uu____8679 = FStar_SMTEncoding_Term.boxString b in
                [uu____8679] in
              [uu____8677] in
            let uu____8682 =
              let uu____8683 = FStar_SMTEncoding_Term.boxString b in
              FStar_SMTEncoding_Term.mk_HasType uu____8683 tt in
            (uu____8674, [bb], uu____8682) in
          FStar_SMTEncoding_Util.mkForall uu____8668 in
        (uu____8667, (Some "string typing"), "string_typing") in
      FStar_SMTEncoding_Term.Assume uu____8663 in
    let uu____8694 =
      let uu____8696 =
        let uu____8697 =
          let uu____8701 =
            let uu____8702 =
              let uu____8708 =
                let uu____8709 =
                  let uu____8712 =
                    FStar_SMTEncoding_Term.mk_tester "BoxString" x in
                  (typing_pred, uu____8712) in
                FStar_SMTEncoding_Util.mkImp uu____8709 in
              ([[typing_pred]], [xx], uu____8708) in
            mkForall_fuel uu____8702 in
          (uu____8701, (Some "string inversion"), "string_inversion") in
        FStar_SMTEncoding_Term.Assume uu____8697 in
      [uu____8696] in
    uu____8662 :: uu____8694 in
  let mk_ref1 env reft_name uu____8734 =
    let r = ("r", FStar_SMTEncoding_Term.Ref_sort) in
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let refa =
      let uu____8745 =
        let uu____8749 =
          let uu____8751 = FStar_SMTEncoding_Util.mkFreeV aa in [uu____8751] in
        (reft_name, uu____8749) in
      FStar_SMTEncoding_Util.mkApp uu____8745 in
    let refb =
      let uu____8754 =
        let uu____8758 =
          let uu____8760 = FStar_SMTEncoding_Util.mkFreeV bb in [uu____8760] in
        (reft_name, uu____8758) in
      FStar_SMTEncoding_Util.mkApp uu____8754 in
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x refa in
    let typing_pred_b = FStar_SMTEncoding_Term.mk_HasType x refb in
    let uu____8764 =
      let uu____8765 =
        let uu____8769 =
          let uu____8770 =
            let uu____8776 =
              let uu____8777 =
                let uu____8780 = FStar_SMTEncoding_Term.mk_tester "BoxRef" x in
                (typing_pred, uu____8780) in
              FStar_SMTEncoding_Util.mkImp uu____8777 in
            ([[typing_pred]], [xx; aa], uu____8776) in
          mkForall_fuel uu____8770 in
        (uu____8769, (Some "ref inversion"), "ref_inversion") in
      FStar_SMTEncoding_Term.Assume uu____8765 in
    [uu____8764] in
  let mk_true_interp env nm true_tm =
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [true_tm]) in
    [FStar_SMTEncoding_Term.Assume
       (valid, (Some "True interpretation"), "true_interp")] in
  let mk_false_interp env nm false_tm =
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [false_tm]) in
    let uu____8820 =
      let uu____8821 =
        let uu____8825 =
          FStar_SMTEncoding_Util.mkIff
            (FStar_SMTEncoding_Util.mkFalse, valid) in
        (uu____8825, (Some "False interpretation"), "false_interp") in
      FStar_SMTEncoding_Term.Assume uu____8821 in
    [uu____8820] in
  let mk_and_interp env conj uu____8836 =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let l_and_a_b = FStar_SMTEncoding_Util.mkApp (conj, [a; b]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_and_a_b]) in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b]) in
    let uu____8853 =
      let uu____8854 =
        let uu____8858 =
          let uu____8859 =
            let uu____8865 =
              let uu____8866 =
                let uu____8869 =
                  FStar_SMTEncoding_Util.mkAnd (valid_a, valid_b) in
                (uu____8869, valid) in
              FStar_SMTEncoding_Util.mkIff uu____8866 in
            ([[l_and_a_b]], [aa; bb], uu____8865) in
          FStar_SMTEncoding_Util.mkForall uu____8859 in
        (uu____8858, (Some "/\\ interpretation"), "l_and-interp") in
      FStar_SMTEncoding_Term.Assume uu____8854 in
    [uu____8853] in
  let mk_or_interp env disj uu____8893 =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let l_or_a_b = FStar_SMTEncoding_Util.mkApp (disj, [a; b]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_or_a_b]) in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b]) in
    let uu____8910 =
      let uu____8911 =
        let uu____8915 =
          let uu____8916 =
            let uu____8922 =
              let uu____8923 =
                let uu____8926 =
                  FStar_SMTEncoding_Util.mkOr (valid_a, valid_b) in
                (uu____8926, valid) in
              FStar_SMTEncoding_Util.mkIff uu____8923 in
            ([[l_or_a_b]], [aa; bb], uu____8922) in
          FStar_SMTEncoding_Util.mkForall uu____8916 in
        (uu____8915, (Some "\\/ interpretation"), "l_or-interp") in
      FStar_SMTEncoding_Term.Assume uu____8911 in
    [uu____8910] in
  let mk_eq2_interp env eq2 tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let xx1 = ("x", FStar_SMTEncoding_Term.Term_sort) in
    let yy1 = ("y", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let x1 = FStar_SMTEncoding_Util.mkFreeV xx1 in
    let y1 = FStar_SMTEncoding_Util.mkFreeV yy1 in
    let eq2_x_y = FStar_SMTEncoding_Util.mkApp (eq2, [a; x1; y1]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [eq2_x_y]) in
    let uu____8967 =
      let uu____8968 =
        let uu____8972 =
          let uu____8973 =
            let uu____8979 =
              let uu____8980 =
                let uu____8983 = FStar_SMTEncoding_Util.mkEq (x1, y1) in
                (uu____8983, valid) in
              FStar_SMTEncoding_Util.mkIff uu____8980 in
            ([[eq2_x_y]], [aa; xx1; yy1], uu____8979) in
          FStar_SMTEncoding_Util.mkForall uu____8973 in
        (uu____8972, (Some "Eq2 interpretation"), "eq2-interp") in
      FStar_SMTEncoding_Term.Assume uu____8968 in
    [uu____8967] in
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
    let uu____9030 =
      let uu____9031 =
        let uu____9035 =
          let uu____9036 =
            let uu____9042 =
              let uu____9043 =
                let uu____9046 = FStar_SMTEncoding_Util.mkEq (x1, y1) in
                (uu____9046, valid) in
              FStar_SMTEncoding_Util.mkIff uu____9043 in
            ([[eq3_x_y]], [aa; bb; xx1; yy1], uu____9042) in
          FStar_SMTEncoding_Util.mkForall uu____9036 in
        (uu____9035, (Some "Eq3 interpretation"), "eq3-interp") in
      FStar_SMTEncoding_Term.Assume uu____9031 in
    [uu____9030] in
  let mk_imp_interp env imp tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let l_imp_a_b = FStar_SMTEncoding_Util.mkApp (imp, [a; b]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_imp_a_b]) in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b]) in
    let uu____9091 =
      let uu____9092 =
        let uu____9096 =
          let uu____9097 =
            let uu____9103 =
              let uu____9104 =
                let uu____9107 =
                  FStar_SMTEncoding_Util.mkImp (valid_a, valid_b) in
                (uu____9107, valid) in
              FStar_SMTEncoding_Util.mkIff uu____9104 in
            ([[l_imp_a_b]], [aa; bb], uu____9103) in
          FStar_SMTEncoding_Util.mkForall uu____9097 in
        (uu____9096, (Some "==> interpretation"), "l_imp-interp") in
      FStar_SMTEncoding_Term.Assume uu____9092 in
    [uu____9091] in
  let mk_iff_interp env iff tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let l_iff_a_b = FStar_SMTEncoding_Util.mkApp (iff, [a; b]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_iff_a_b]) in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b]) in
    let uu____9148 =
      let uu____9149 =
        let uu____9153 =
          let uu____9154 =
            let uu____9160 =
              let uu____9161 =
                let uu____9164 =
                  FStar_SMTEncoding_Util.mkIff (valid_a, valid_b) in
                (uu____9164, valid) in
              FStar_SMTEncoding_Util.mkIff uu____9161 in
            ([[l_iff_a_b]], [aa; bb], uu____9160) in
          FStar_SMTEncoding_Util.mkForall uu____9154 in
        (uu____9153, (Some "<==> interpretation"), "l_iff-interp") in
      FStar_SMTEncoding_Term.Assume uu____9149 in
    [uu____9148] in
  let mk_not_interp env l_not tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let l_not_a = FStar_SMTEncoding_Util.mkApp (l_not, [a]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_not_a]) in
    let not_valid_a =
      let uu____9198 = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
      FStar_All.pipe_left FStar_SMTEncoding_Util.mkNot uu____9198 in
    let uu____9200 =
      let uu____9201 =
        let uu____9205 =
          let uu____9206 =
            let uu____9212 =
              FStar_SMTEncoding_Util.mkIff (not_valid_a, valid) in
            ([[l_not_a]], [aa], uu____9212) in
          FStar_SMTEncoding_Util.mkForall uu____9206 in
        (uu____9205, (Some "not interpretation"), "l_not-interp") in
      FStar_SMTEncoding_Term.Assume uu____9201 in
    [uu____9200] in
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
      let uu____9252 =
        let uu____9256 =
          let uu____9258 = FStar_SMTEncoding_Util.mk_ApplyTT b x1 in
          [uu____9258] in
        ("Valid", uu____9256) in
      FStar_SMTEncoding_Util.mkApp uu____9252 in
    let uu____9260 =
      let uu____9261 =
        let uu____9265 =
          let uu____9266 =
            let uu____9272 =
              let uu____9273 =
                let uu____9276 =
                  let uu____9277 =
                    let uu____9283 =
                      let uu____9286 =
                        let uu____9288 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a in
                        [uu____9288] in
                      [uu____9286] in
                    let uu____9291 =
                      let uu____9292 =
                        let uu____9295 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a in
                        (uu____9295, valid_b_x) in
                      FStar_SMTEncoding_Util.mkImp uu____9292 in
                    (uu____9283, [xx1], uu____9291) in
                  FStar_SMTEncoding_Util.mkForall uu____9277 in
                (uu____9276, valid) in
              FStar_SMTEncoding_Util.mkIff uu____9273 in
            ([[l_forall_a_b]], [aa; bb], uu____9272) in
          FStar_SMTEncoding_Util.mkForall uu____9266 in
        (uu____9265, (Some "forall interpretation"), "forall-interp") in
      FStar_SMTEncoding_Term.Assume uu____9261 in
    [uu____9260] in
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
      let uu____9346 =
        let uu____9350 =
          let uu____9352 = FStar_SMTEncoding_Util.mk_ApplyTT b x1 in
          [uu____9352] in
        ("Valid", uu____9350) in
      FStar_SMTEncoding_Util.mkApp uu____9346 in
    let uu____9354 =
      let uu____9355 =
        let uu____9359 =
          let uu____9360 =
            let uu____9366 =
              let uu____9367 =
                let uu____9370 =
                  let uu____9371 =
                    let uu____9377 =
                      let uu____9380 =
                        let uu____9382 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a in
                        [uu____9382] in
                      [uu____9380] in
                    let uu____9385 =
                      let uu____9386 =
                        let uu____9389 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a in
                        (uu____9389, valid_b_x) in
                      FStar_SMTEncoding_Util.mkImp uu____9386 in
                    (uu____9377, [xx1], uu____9385) in
                  FStar_SMTEncoding_Util.mkExists uu____9371 in
                (uu____9370, valid) in
              FStar_SMTEncoding_Util.mkIff uu____9367 in
            ([[l_exists_a_b]], [aa; bb], uu____9366) in
          FStar_SMTEncoding_Util.mkForall uu____9360 in
        (uu____9359, (Some "exists interpretation"), "exists-interp") in
      FStar_SMTEncoding_Term.Assume uu____9355 in
    [uu____9354] in
  let mk_range_interp env range tt =
    let range_ty = FStar_SMTEncoding_Util.mkApp (range, []) in
    let uu____9425 =
      let uu____9426 =
        let uu____9430 =
          FStar_SMTEncoding_Term.mk_HasTypeZ
            FStar_SMTEncoding_Term.mk_Range_const range_ty in
        let uu____9431 = varops.mk_unique "typing_range_const" in
        (uu____9430, (Some "Range_const typing"), uu____9431) in
      FStar_SMTEncoding_Term.Assume uu____9426 in
    [uu____9425] in
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
          let uu____9693 =
            FStar_Util.find_opt
              (fun uu____9711  ->
                 match uu____9711 with
                 | (l,uu____9721) -> FStar_Ident.lid_equals l t) prims1 in
          match uu____9693 with
          | None  -> []
          | Some (uu____9743,f) -> f env s tt
let encode_smt_lemma:
  env_t ->
    FStar_Syntax_Syntax.fv ->
      FStar_Syntax_Syntax.typ -> FStar_SMTEncoding_Term.decl Prims.list
  =
  fun env  ->
    fun fv  ->
      fun t  ->
        let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
        let uu____9780 = encode_function_type_as_formula None None t env in
        match uu____9780 with
        | (form,decls) ->
            FStar_List.append decls
              [FStar_SMTEncoding_Term.Assume
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
            let uu____9812 =
              (let uu____9813 =
                 (FStar_Syntax_Util.is_pure_or_ghost_function t_norm) ||
                   (FStar_TypeChecker_Env.is_reifiable_function env.tcenv
                      t_norm) in
               FStar_All.pipe_left Prims.op_Negation uu____9813) ||
                (FStar_Syntax_Util.is_lemma t_norm) in
            if uu____9812
            then
              let uu____9817 = new_term_constant_and_tok_from_lid env lid in
              match uu____9817 with
              | (vname,vtok,env1) ->
                  let arg_sorts =
                    let uu____9829 =
                      let uu____9830 = FStar_Syntax_Subst.compress t_norm in
                      uu____9830.FStar_Syntax_Syntax.n in
                    match uu____9829 with
                    | FStar_Syntax_Syntax.Tm_arrow (binders,uu____9835) ->
                        FStar_All.pipe_right binders
                          (FStar_List.map
                             (fun uu____9852  ->
                                FStar_SMTEncoding_Term.Term_sort))
                    | uu____9855 -> [] in
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
              (let uu____9864 = prims.is lid in
               if uu____9864
               then
                 let vname = varops.new_fvar lid in
                 let uu____9869 = prims.mk lid vname in
                 match uu____9869 with
                 | (tok,definition) ->
                     let env1 = push_free_var env lid vname (Some tok) in
                     (definition, env1)
               else
                 (let encode_non_total_function_typ =
                    lid.FStar_Ident.nsstr <> "Prims" in
                  let uu____9884 =
                    let uu____9890 = curried_arrow_formals_comp t_norm in
                    match uu____9890 with
                    | (args,comp) ->
                        let comp1 =
                          let uu____9901 =
                            FStar_TypeChecker_Env.is_reifiable_comp env.tcenv
                              comp in
                          if uu____9901
                          then
                            let uu____9902 =
                              FStar_TypeChecker_Env.reify_comp
                                (let uu___159_9903 = env.tcenv in
                                 {
                                   FStar_TypeChecker_Env.solver =
                                     (uu___159_9903.FStar_TypeChecker_Env.solver);
                                   FStar_TypeChecker_Env.range =
                                     (uu___159_9903.FStar_TypeChecker_Env.range);
                                   FStar_TypeChecker_Env.curmodule =
                                     (uu___159_9903.FStar_TypeChecker_Env.curmodule);
                                   FStar_TypeChecker_Env.gamma =
                                     (uu___159_9903.FStar_TypeChecker_Env.gamma);
                                   FStar_TypeChecker_Env.gamma_cache =
                                     (uu___159_9903.FStar_TypeChecker_Env.gamma_cache);
                                   FStar_TypeChecker_Env.modules =
                                     (uu___159_9903.FStar_TypeChecker_Env.modules);
                                   FStar_TypeChecker_Env.expected_typ =
                                     (uu___159_9903.FStar_TypeChecker_Env.expected_typ);
                                   FStar_TypeChecker_Env.sigtab =
                                     (uu___159_9903.FStar_TypeChecker_Env.sigtab);
                                   FStar_TypeChecker_Env.is_pattern =
                                     (uu___159_9903.FStar_TypeChecker_Env.is_pattern);
                                   FStar_TypeChecker_Env.instantiate_imp =
                                     (uu___159_9903.FStar_TypeChecker_Env.instantiate_imp);
                                   FStar_TypeChecker_Env.effects =
                                     (uu___159_9903.FStar_TypeChecker_Env.effects);
                                   FStar_TypeChecker_Env.generalize =
                                     (uu___159_9903.FStar_TypeChecker_Env.generalize);
                                   FStar_TypeChecker_Env.letrecs =
                                     (uu___159_9903.FStar_TypeChecker_Env.letrecs);
                                   FStar_TypeChecker_Env.top_level =
                                     (uu___159_9903.FStar_TypeChecker_Env.top_level);
                                   FStar_TypeChecker_Env.check_uvars =
                                     (uu___159_9903.FStar_TypeChecker_Env.check_uvars);
                                   FStar_TypeChecker_Env.use_eq =
                                     (uu___159_9903.FStar_TypeChecker_Env.use_eq);
                                   FStar_TypeChecker_Env.is_iface =
                                     (uu___159_9903.FStar_TypeChecker_Env.is_iface);
                                   FStar_TypeChecker_Env.admit =
                                     (uu___159_9903.FStar_TypeChecker_Env.admit);
                                   FStar_TypeChecker_Env.lax = true;
                                   FStar_TypeChecker_Env.lax_universes =
                                     (uu___159_9903.FStar_TypeChecker_Env.lax_universes);
                                   FStar_TypeChecker_Env.type_of =
                                     (uu___159_9903.FStar_TypeChecker_Env.type_of);
                                   FStar_TypeChecker_Env.universe_of =
                                     (uu___159_9903.FStar_TypeChecker_Env.universe_of);
                                   FStar_TypeChecker_Env.use_bv_sorts =
                                     (uu___159_9903.FStar_TypeChecker_Env.use_bv_sorts);
                                   FStar_TypeChecker_Env.qname_and_index =
                                     (uu___159_9903.FStar_TypeChecker_Env.qname_and_index)
                                 }) comp FStar_Syntax_Syntax.U_unknown in
                            FStar_Syntax_Syntax.mk_Total uu____9902
                          else comp in
                        if encode_non_total_function_typ
                        then
                          let uu____9910 =
                            FStar_TypeChecker_Util.pure_or_ghost_pre_and_post
                              env.tcenv comp1 in
                          (args, uu____9910)
                        else
                          (args,
                            (None, (FStar_Syntax_Util.comp_result comp1))) in
                  match uu____9884 with
                  | (formals,(pre_opt,res_t)) ->
                      let uu____9937 =
                        new_term_constant_and_tok_from_lid env lid in
                      (match uu____9937 with
                       | (vname,vtok,env1) ->
                           let vtok_tm =
                             match formals with
                             | [] ->
                                 FStar_SMTEncoding_Util.mkFreeV
                                   (vname, FStar_SMTEncoding_Term.Term_sort)
                             | uu____9950 ->
                                 FStar_SMTEncoding_Util.mkApp (vtok, []) in
                           let mk_disc_proj_axioms guard encoded_res_t vapp
                             vars =
                             FStar_All.pipe_right quals
                               (FStar_List.collect
                                  (fun uu___130_9974  ->
                                     match uu___130_9974 with
                                     | FStar_Syntax_Syntax.Discriminator d ->
                                         let uu____9977 =
                                           FStar_Util.prefix vars in
                                         (match uu____9977 with
                                          | (uu____9988,(xxsym,uu____9990))
                                              ->
                                              let xx =
                                                FStar_SMTEncoding_Util.mkFreeV
                                                  (xxsym,
                                                    FStar_SMTEncoding_Term.Term_sort) in
                                              let uu____10000 =
                                                let uu____10001 =
                                                  let uu____10005 =
                                                    let uu____10006 =
                                                      let uu____10012 =
                                                        let uu____10013 =
                                                          let uu____10016 =
                                                            let uu____10017 =
                                                              FStar_SMTEncoding_Term.mk_tester
                                                                (escape
                                                                   d.FStar_Ident.str)
                                                                xx in
                                                            FStar_All.pipe_left
                                                              FStar_SMTEncoding_Term.boxBool
                                                              uu____10017 in
                                                          (vapp, uu____10016) in
                                                        FStar_SMTEncoding_Util.mkEq
                                                          uu____10013 in
                                                      ([[vapp]], vars,
                                                        uu____10012) in
                                                    FStar_SMTEncoding_Util.mkForall
                                                      uu____10006 in
                                                  (uu____10005,
                                                    (Some
                                                       "Discriminator equation"),
                                                    (Prims.strcat
                                                       "disc_equation_"
                                                       (escape
                                                          d.FStar_Ident.str))) in
                                                FStar_SMTEncoding_Term.Assume
                                                  uu____10001 in
                                              [uu____10000])
                                     | FStar_Syntax_Syntax.Projector 
                                         (d,f) ->
                                         let uu____10028 =
                                           FStar_Util.prefix vars in
                                         (match uu____10028 with
                                          | (uu____10039,(xxsym,uu____10041))
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
                                              let uu____10055 =
                                                let uu____10056 =
                                                  let uu____10060 =
                                                    let uu____10061 =
                                                      let uu____10067 =
                                                        FStar_SMTEncoding_Util.mkEq
                                                          (vapp, prim_app) in
                                                      ([[vapp]], vars,
                                                        uu____10067) in
                                                    FStar_SMTEncoding_Util.mkForall
                                                      uu____10061 in
                                                  (uu____10060,
                                                    (Some
                                                       "Projector equation"),
                                                    (Prims.strcat
                                                       "proj_equation_"
                                                       tp_name)) in
                                                FStar_SMTEncoding_Term.Assume
                                                  uu____10056 in
                                              [uu____10055])
                                     | uu____10076 -> [])) in
                           let uu____10077 = encode_binders None formals env1 in
                           (match uu____10077 with
                            | (vars,guards,env',decls1,uu____10093) ->
                                let uu____10100 =
                                  match pre_opt with
                                  | None  ->
                                      let uu____10105 =
                                        FStar_SMTEncoding_Util.mk_and_l
                                          guards in
                                      (uu____10105, decls1)
                                  | Some p ->
                                      let uu____10107 = encode_formula p env' in
                                      (match uu____10107 with
                                       | (g,ds) ->
                                           let uu____10114 =
                                             FStar_SMTEncoding_Util.mk_and_l
                                               (g :: guards) in
                                           (uu____10114,
                                             (FStar_List.append decls1 ds))) in
                                (match uu____10100 with
                                 | (guard,decls11) ->
                                     let vtok_app = mk_Apply vtok_tm vars in
                                     let vapp =
                                       let uu____10123 =
                                         let uu____10127 =
                                           FStar_List.map
                                             FStar_SMTEncoding_Util.mkFreeV
                                             vars in
                                         (vname, uu____10127) in
                                       FStar_SMTEncoding_Util.mkApp
                                         uu____10123 in
                                     let uu____10132 =
                                       let vname_decl =
                                         let uu____10137 =
                                           let uu____10143 =
                                             FStar_All.pipe_right formals
                                               (FStar_List.map
                                                  (fun uu____10148  ->
                                                     FStar_SMTEncoding_Term.Term_sort)) in
                                           (vname, uu____10143,
                                             FStar_SMTEncoding_Term.Term_sort,
                                             None) in
                                         FStar_SMTEncoding_Term.DeclFun
                                           uu____10137 in
                                       let uu____10153 =
                                         let env2 =
                                           let uu___160_10157 = env1 in
                                           {
                                             bindings =
                                               (uu___160_10157.bindings);
                                             depth = (uu___160_10157.depth);
                                             tcenv = (uu___160_10157.tcenv);
                                             warn = (uu___160_10157.warn);
                                             cache = (uu___160_10157.cache);
                                             nolabels =
                                               (uu___160_10157.nolabels);
                                             use_zfuel_name =
                                               (uu___160_10157.use_zfuel_name);
                                             encode_non_total_function_typ;
                                             current_module_name =
                                               (uu___160_10157.current_module_name)
                                           } in
                                         let uu____10158 =
                                           let uu____10159 =
                                             head_normal env2 tt in
                                           Prims.op_Negation uu____10159 in
                                         if uu____10158
                                         then
                                           encode_term_pred None tt env2
                                             vtok_tm
                                         else
                                           encode_term_pred None t_norm env2
                                             vtok_tm in
                                       match uu____10153 with
                                       | (tok_typing,decls2) ->
                                           let tok_typing1 =
                                             match formals with
                                             | uu____10169::uu____10170 ->
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
                                                   let uu____10193 =
                                                     let uu____10199 =
                                                       FStar_SMTEncoding_Term.mk_NoHoist
                                                         f tok_typing in
                                                     ([[vtok_app_l];
                                                      [vtok_app_r]], 
                                                       [ff], uu____10199) in
                                                   FStar_SMTEncoding_Util.mkForall
                                                     uu____10193 in
                                                 FStar_SMTEncoding_Term.Assume
                                                   (guarded_tok_typing,
                                                     (Some
                                                        "function token typing"),
                                                     (Prims.strcat
                                                        "function_token_typing_"
                                                        vname))
                                             | uu____10213 ->
                                                 FStar_SMTEncoding_Term.Assume
                                                   (tok_typing,
                                                     (Some
                                                        "function token typing"),
                                                     (Prims.strcat
                                                        "function_token_typing_"
                                                        vname)) in
                                           let uu____10215 =
                                             match formals with
                                             | [] ->
                                                 let uu____10224 =
                                                   let uu____10225 =
                                                     let uu____10227 =
                                                       FStar_SMTEncoding_Util.mkFreeV
                                                         (vname,
                                                           FStar_SMTEncoding_Term.Term_sort) in
                                                     FStar_All.pipe_left
                                                       (fun _0_34  ->
                                                          Some _0_34)
                                                       uu____10227 in
                                                   push_free_var env1 lid
                                                     vname uu____10225 in
                                                 ((FStar_List.append decls2
                                                     [tok_typing1]),
                                                   uu____10224)
                                             | uu____10230 ->
                                                 let vtok_decl =
                                                   FStar_SMTEncoding_Term.DeclFun
                                                     (vtok, [],
                                                       FStar_SMTEncoding_Term.Term_sort,
                                                       None) in
                                                 let vtok_fresh =
                                                   let uu____10235 =
                                                     varops.next_id () in
                                                   FStar_SMTEncoding_Term.fresh_token
                                                     (vtok,
                                                       FStar_SMTEncoding_Term.Term_sort)
                                                     uu____10235 in
                                                 let name_tok_corr =
                                                   let uu____10237 =
                                                     let uu____10241 =
                                                       let uu____10242 =
                                                         let uu____10248 =
                                                           FStar_SMTEncoding_Util.mkEq
                                                             (vtok_app, vapp) in
                                                         ([[vtok_app];
                                                          [vapp]], vars,
                                                           uu____10248) in
                                                       FStar_SMTEncoding_Util.mkForall
                                                         uu____10242 in
                                                     (uu____10241,
                                                       (Some
                                                          "Name-token correspondence"),
                                                       (Prims.strcat
                                                          "token_correspondence_"
                                                          vname)) in
                                                   FStar_SMTEncoding_Term.Assume
                                                     uu____10237 in
                                                 ((FStar_List.append decls2
                                                     [vtok_decl;
                                                     vtok_fresh;
                                                     name_tok_corr;
                                                     tok_typing1]), env1) in
                                           (match uu____10215 with
                                            | (tok_decl,env2) ->
                                                ((vname_decl :: tok_decl),
                                                  env2)) in
                                     (match uu____10132 with
                                      | (decls2,env2) ->
                                          let uu____10272 =
                                            let res_t1 =
                                              FStar_Syntax_Subst.compress
                                                res_t in
                                            let uu____10277 =
                                              encode_term res_t1 env' in
                                            match uu____10277 with
                                            | (encoded_res_t,decls) ->
                                                let uu____10285 =
                                                  FStar_SMTEncoding_Term.mk_HasType
                                                    vapp encoded_res_t in
                                                (encoded_res_t, uu____10285,
                                                  decls) in
                                          (match uu____10272 with
                                           | (encoded_res_t,ty_pred,decls3)
                                               ->
                                               let typingAx =
                                                 let uu____10293 =
                                                   let uu____10297 =
                                                     let uu____10298 =
                                                       let uu____10304 =
                                                         FStar_SMTEncoding_Util.mkImp
                                                           (guard, ty_pred) in
                                                       ([[vapp]], vars,
                                                         uu____10304) in
                                                     FStar_SMTEncoding_Util.mkForall
                                                       uu____10298 in
                                                   (uu____10297,
                                                     (Some "free var typing"),
                                                     (Prims.strcat "typing_"
                                                        vname)) in
                                                 FStar_SMTEncoding_Term.Assume
                                                   uu____10293 in
                                               let freshness =
                                                 let uu____10313 =
                                                   FStar_All.pipe_right quals
                                                     (FStar_List.contains
                                                        FStar_Syntax_Syntax.New) in
                                                 if uu____10313
                                                 then
                                                   let uu____10316 =
                                                     let uu____10317 =
                                                       let uu____10323 =
                                                         FStar_All.pipe_right
                                                           vars
                                                           (FStar_List.map
                                                              Prims.snd) in
                                                       let uu____10329 =
                                                         varops.next_id () in
                                                       (vname, uu____10323,
                                                         FStar_SMTEncoding_Term.Term_sort,
                                                         uu____10329) in
                                                     FStar_SMTEncoding_Term.fresh_constructor
                                                       uu____10317 in
                                                   let uu____10331 =
                                                     let uu____10333 =
                                                       pretype_axiom env2
                                                         vapp vars in
                                                     [uu____10333] in
                                                   uu____10316 :: uu____10331
                                                 else [] in
                                               let g =
                                                 let uu____10337 =
                                                   let uu____10339 =
                                                     let uu____10341 =
                                                       let uu____10343 =
                                                         let uu____10345 =
                                                           mk_disc_proj_axioms
                                                             guard
                                                             encoded_res_t
                                                             vapp vars in
                                                         typingAx ::
                                                           uu____10345 in
                                                       FStar_List.append
                                                         freshness
                                                         uu____10343 in
                                                     FStar_List.append decls3
                                                       uu____10341 in
                                                   FStar_List.append decls2
                                                     uu____10339 in
                                                 FStar_List.append decls11
                                                   uu____10337 in
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
          let uu____10367 =
            try_lookup_lid env
              (x.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          match uu____10367 with
          | None  ->
              let uu____10390 = encode_free_var env x t t_norm [] in
              (match uu____10390 with
               | (decls,env1) ->
                   let uu____10405 =
                     lookup_lid env1
                       (x.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                   (match uu____10405 with
                    | (n1,x',uu____10424) -> ((n1, x'), decls, env1)))
          | Some (n1,x1,uu____10436) -> ((n1, x1), [], env)
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
          let uu____10469 = encode_free_var env lid t tt quals in
          match uu____10469 with
          | (decls,env1) ->
              let uu____10480 = FStar_Syntax_Util.is_smt_lemma t in
              if uu____10480
              then
                let uu____10484 =
                  let uu____10486 = encode_smt_lemma env1 lid tt in
                  FStar_List.append decls uu____10486 in
                (uu____10484, env1)
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
             (fun uu____10514  ->
                fun lb  ->
                  match uu____10514 with
                  | (decls,env1) ->
                      let uu____10526 =
                        let uu____10530 =
                          FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
                        encode_top_level_val env1 uu____10530
                          lb.FStar_Syntax_Syntax.lbtyp quals in
                      (match uu____10526 with
                       | (decls',env2) ->
                           ((FStar_List.append decls decls'), env2)))
             ([], env))
let is_tactic: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let fstar_tactics_tactic_lid =
      FStar_Syntax_Const.p2l ["FStar"; "Tactics"; "tactic"] in
    let uu____10544 = FStar_Syntax_Util.head_and_args t in
    match uu____10544 with
    | (hd1,args) ->
        let uu____10570 =
          let uu____10571 = FStar_Syntax_Util.un_uinst hd1 in
          uu____10571.FStar_Syntax_Syntax.n in
        (match uu____10570 with
         | FStar_Syntax_Syntax.Tm_fvar fv when
             FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_tactic_lid ->
             true
         | FStar_Syntax_Syntax.Tm_arrow (uu____10575,c) ->
             let effect_name = FStar_Syntax_Util.comp_effect_name c in
             FStar_Util.starts_with "FStar.Tactics"
               effect_name.FStar_Ident.str
         | uu____10588 -> false)
let encode_top_level_let:
  env_t ->
    (Prims.bool* FStar_Syntax_Syntax.letbinding Prims.list) ->
      FStar_Syntax_Syntax.qualifier Prims.list ->
        (FStar_SMTEncoding_Term.decl Prims.list* env_t)
  =
  fun env  ->
    fun uu____10603  ->
      fun quals  ->
        match uu____10603 with
        | (is_rec,bindings) ->
            let eta_expand1 binders formals body t =
              let nbinders = FStar_List.length binders in
              let uu____10652 = FStar_Util.first_N nbinders formals in
              match uu____10652 with
              | (formals1,extra_formals) ->
                  let subst1 =
                    FStar_List.map2
                      (fun uu____10692  ->
                         fun uu____10693  ->
                           match (uu____10692, uu____10693) with
                           | ((formal,uu____10703),(binder,uu____10705)) ->
                               let uu____10710 =
                                 let uu____10715 =
                                   FStar_Syntax_Syntax.bv_to_name binder in
                                 (formal, uu____10715) in
                               FStar_Syntax_Syntax.NT uu____10710) formals1
                      binders in
                  let extra_formals1 =
                    let uu____10720 =
                      FStar_All.pipe_right extra_formals
                        (FStar_List.map
                           (fun uu____10734  ->
                              match uu____10734 with
                              | (x,i) ->
                                  let uu____10741 =
                                    let uu___161_10742 = x in
                                    let uu____10743 =
                                      FStar_Syntax_Subst.subst subst1
                                        x.FStar_Syntax_Syntax.sort in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___161_10742.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___161_10742.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = uu____10743
                                    } in
                                  (uu____10741, i))) in
                    FStar_All.pipe_right uu____10720
                      FStar_Syntax_Util.name_binders in
                  let body1 =
                    let uu____10755 =
                      let uu____10757 =
                        let uu____10758 = FStar_Syntax_Subst.subst subst1 t in
                        uu____10758.FStar_Syntax_Syntax.n in
                      FStar_All.pipe_left (fun _0_35  -> Some _0_35)
                        uu____10757 in
                    let uu____10762 =
                      let uu____10763 = FStar_Syntax_Subst.compress body in
                      let uu____10764 =
                        let uu____10765 =
                          FStar_Syntax_Util.args_of_binders extra_formals1 in
                        FStar_All.pipe_left Prims.snd uu____10765 in
                      FStar_Syntax_Syntax.extend_app_n uu____10763
                        uu____10764 in
                    uu____10762 uu____10755 body.FStar_Syntax_Syntax.pos in
                  ((FStar_List.append binders extra_formals1), body1) in
            let destruct_bound_function flid t_norm e =
              let get_result_type c =
                let uu____10807 =
                  FStar_TypeChecker_Env.is_reifiable_comp env.tcenv c in
                if uu____10807
                then
                  FStar_TypeChecker_Env.reify_comp
                    (let uu___162_10808 = env.tcenv in
                     {
                       FStar_TypeChecker_Env.solver =
                         (uu___162_10808.FStar_TypeChecker_Env.solver);
                       FStar_TypeChecker_Env.range =
                         (uu___162_10808.FStar_TypeChecker_Env.range);
                       FStar_TypeChecker_Env.curmodule =
                         (uu___162_10808.FStar_TypeChecker_Env.curmodule);
                       FStar_TypeChecker_Env.gamma =
                         (uu___162_10808.FStar_TypeChecker_Env.gamma);
                       FStar_TypeChecker_Env.gamma_cache =
                         (uu___162_10808.FStar_TypeChecker_Env.gamma_cache);
                       FStar_TypeChecker_Env.modules =
                         (uu___162_10808.FStar_TypeChecker_Env.modules);
                       FStar_TypeChecker_Env.expected_typ =
                         (uu___162_10808.FStar_TypeChecker_Env.expected_typ);
                       FStar_TypeChecker_Env.sigtab =
                         (uu___162_10808.FStar_TypeChecker_Env.sigtab);
                       FStar_TypeChecker_Env.is_pattern =
                         (uu___162_10808.FStar_TypeChecker_Env.is_pattern);
                       FStar_TypeChecker_Env.instantiate_imp =
                         (uu___162_10808.FStar_TypeChecker_Env.instantiate_imp);
                       FStar_TypeChecker_Env.effects =
                         (uu___162_10808.FStar_TypeChecker_Env.effects);
                       FStar_TypeChecker_Env.generalize =
                         (uu___162_10808.FStar_TypeChecker_Env.generalize);
                       FStar_TypeChecker_Env.letrecs =
                         (uu___162_10808.FStar_TypeChecker_Env.letrecs);
                       FStar_TypeChecker_Env.top_level =
                         (uu___162_10808.FStar_TypeChecker_Env.top_level);
                       FStar_TypeChecker_Env.check_uvars =
                         (uu___162_10808.FStar_TypeChecker_Env.check_uvars);
                       FStar_TypeChecker_Env.use_eq =
                         (uu___162_10808.FStar_TypeChecker_Env.use_eq);
                       FStar_TypeChecker_Env.is_iface =
                         (uu___162_10808.FStar_TypeChecker_Env.is_iface);
                       FStar_TypeChecker_Env.admit =
                         (uu___162_10808.FStar_TypeChecker_Env.admit);
                       FStar_TypeChecker_Env.lax = true;
                       FStar_TypeChecker_Env.lax_universes =
                         (uu___162_10808.FStar_TypeChecker_Env.lax_universes);
                       FStar_TypeChecker_Env.type_of =
                         (uu___162_10808.FStar_TypeChecker_Env.type_of);
                       FStar_TypeChecker_Env.universe_of =
                         (uu___162_10808.FStar_TypeChecker_Env.universe_of);
                       FStar_TypeChecker_Env.use_bv_sorts =
                         (uu___162_10808.FStar_TypeChecker_Env.use_bv_sorts);
                       FStar_TypeChecker_Env.qname_and_index =
                         (uu___162_10808.FStar_TypeChecker_Env.qname_and_index)
                     }) c FStar_Syntax_Syntax.U_unknown
                else FStar_Syntax_Util.comp_result c in
              let rec aux norm1 t_norm1 =
                let uu____10829 = FStar_Syntax_Util.abs_formals e in
                match uu____10829 with
                | (binders,body,lopt) ->
                    (match binders with
                     | uu____10878::uu____10879 ->
                         let uu____10887 =
                           let uu____10888 =
                             FStar_Syntax_Subst.compress t_norm1 in
                           uu____10888.FStar_Syntax_Syntax.n in
                         (match uu____10887 with
                          | FStar_Syntax_Syntax.Tm_arrow (formals,c) ->
                              let uu____10915 =
                                FStar_Syntax_Subst.open_comp formals c in
                              (match uu____10915 with
                               | (formals1,c1) ->
                                   let nformals = FStar_List.length formals1 in
                                   let nbinders = FStar_List.length binders in
                                   let tres = get_result_type c1 in
                                   let uu____10941 =
                                     (nformals < nbinders) &&
                                       (FStar_Syntax_Util.is_total_comp c1) in
                                   if uu____10941
                                   then
                                     let uu____10959 =
                                       FStar_Util.first_N nformals binders in
                                     (match uu____10959 with
                                      | (bs0,rest) ->
                                          let c2 =
                                            let subst1 =
                                              FStar_List.map2
                                                (fun uu____11005  ->
                                                   fun uu____11006  ->
                                                     match (uu____11005,
                                                             uu____11006)
                                                     with
                                                     | ((x,uu____11016),
                                                        (b,uu____11018)) ->
                                                         let uu____11023 =
                                                           let uu____11028 =
                                                             FStar_Syntax_Syntax.bv_to_name
                                                               b in
                                                           (x, uu____11028) in
                                                         FStar_Syntax_Syntax.NT
                                                           uu____11023)
                                                formals1 bs0 in
                                            FStar_Syntax_Subst.subst_comp
                                              subst1 c1 in
                                          let body1 =
                                            FStar_Syntax_Util.abs rest body
                                              lopt in
                                          let uu____11030 =
                                            let uu____11041 =
                                              get_result_type c2 in
                                            (bs0, body1, bs0, uu____11041) in
                                          (uu____11030, false))
                                   else
                                     if nformals > nbinders
                                     then
                                       (let uu____11076 =
                                          eta_expand1 binders formals1 body
                                            tres in
                                        match uu____11076 with
                                        | (binders1,body1) ->
                                            ((binders1, body1, formals1,
                                               tres), false))
                                     else
                                       ((binders, body, formals1, tres),
                                         false))
                          | FStar_Syntax_Syntax.Tm_refine (x,uu____11128) ->
                              let uu____11133 =
                                let uu____11144 =
                                  aux norm1 x.FStar_Syntax_Syntax.sort in
                                Prims.fst uu____11144 in
                              (uu____11133, true)
                          | uu____11177 when Prims.op_Negation norm1 ->
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
                          | uu____11179 ->
                              let uu____11180 =
                                let uu____11181 =
                                  FStar_Syntax_Print.term_to_string e in
                                let uu____11182 =
                                  FStar_Syntax_Print.term_to_string t_norm1 in
                                FStar_Util.format3
                                  "Impossible! let-bound lambda %s = %s has a type that's not a function: %s\n"
                                  flid.FStar_Ident.str uu____11181
                                  uu____11182 in
                              failwith uu____11180)
                     | uu____11195 ->
                         let uu____11196 =
                           let uu____11197 =
                             FStar_Syntax_Subst.compress t_norm1 in
                           uu____11197.FStar_Syntax_Syntax.n in
                         (match uu____11196 with
                          | FStar_Syntax_Syntax.Tm_arrow (formals,c) ->
                              let uu____11224 =
                                FStar_Syntax_Subst.open_comp formals c in
                              (match uu____11224 with
                               | (formals1,c1) ->
                                   let tres = get_result_type c1 in
                                   let uu____11242 =
                                     eta_expand1 [] formals1 e tres in
                                   (match uu____11242 with
                                    | (binders1,body1) ->
                                        ((binders1, body1, formals1, tres),
                                          false)))
                          | uu____11290 -> (([], e, [], t_norm1), false))) in
              aux false t_norm in
            (try
               let uu____11318 =
                 FStar_All.pipe_right bindings
                   (FStar_Util.for_all
                      (fun lb  ->
                         (FStar_Syntax_Util.is_lemma
                            lb.FStar_Syntax_Syntax.lbtyp)
                           || (is_tactic lb.FStar_Syntax_Syntax.lbtyp))) in
               if uu____11318
               then encode_top_level_vals env bindings quals
               else
                 (let uu____11325 =
                    FStar_All.pipe_right bindings
                      (FStar_List.fold_left
                         (fun uu____11366  ->
                            fun lb  ->
                              match uu____11366 with
                              | (toks,typs,decls,env1) ->
                                  ((let uu____11417 =
                                      FStar_Syntax_Util.is_lemma
                                        lb.FStar_Syntax_Syntax.lbtyp in
                                    if uu____11417
                                    then Prims.raise Let_rec_unencodeable
                                    else ());
                                   (let t_norm =
                                      whnf env1 lb.FStar_Syntax_Syntax.lbtyp in
                                    let uu____11420 =
                                      let uu____11428 =
                                        FStar_Util.right
                                          lb.FStar_Syntax_Syntax.lbname in
                                      declare_top_level_let env1 uu____11428
                                        lb.FStar_Syntax_Syntax.lbtyp t_norm in
                                    match uu____11420 with
                                    | (tok,decl,env2) ->
                                        let uu____11453 =
                                          let uu____11460 =
                                            let uu____11466 =
                                              FStar_Util.right
                                                lb.FStar_Syntax_Syntax.lbname in
                                            (uu____11466, tok) in
                                          uu____11460 :: toks in
                                        (uu____11453, (t_norm :: typs), (decl
                                          :: decls), env2))))
                         ([], [], [], env)) in
                  match uu____11325 with
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
                        | uu____11568 ->
                            if curry
                            then
                              (match ftok with
                               | Some ftok1 -> mk_Apply ftok1 vars
                               | None  ->
                                   let uu____11573 =
                                     FStar_SMTEncoding_Util.mkFreeV
                                       (f, FStar_SMTEncoding_Term.Term_sort) in
                                   mk_Apply uu____11573 vars)
                            else
                              (let uu____11575 =
                                 let uu____11579 =
                                   FStar_List.map
                                     FStar_SMTEncoding_Util.mkFreeV vars in
                                 (f, uu____11579) in
                               FStar_SMTEncoding_Util.mkApp uu____11575) in
                      let uu____11584 =
                        (FStar_All.pipe_right quals
                           (FStar_Util.for_some
                              (fun uu___131_11586  ->
                                 match uu___131_11586 with
                                 | FStar_Syntax_Syntax.HasMaskedEffect  ->
                                     true
                                 | uu____11587 -> false)))
                          ||
                          (FStar_All.pipe_right typs1
                             (FStar_Util.for_some
                                (fun t  ->
                                   let uu____11590 =
                                     (FStar_Syntax_Util.is_pure_or_ghost_function
                                        t)
                                       ||
                                       (FStar_TypeChecker_Env.is_reifiable_function
                                          env1.tcenv t) in
                                   FStar_All.pipe_left Prims.op_Negation
                                     uu____11590))) in
                      if uu____11584
                      then (decls1, env1)
                      else
                        if Prims.op_Negation is_rec
                        then
                          (match (bindings, typs1, toks1) with
                           | ({ FStar_Syntax_Syntax.lbname = uu____11610;
                                FStar_Syntax_Syntax.lbunivs = uvs;
                                FStar_Syntax_Syntax.lbtyp = uu____11612;
                                FStar_Syntax_Syntax.lbeff = uu____11613;
                                FStar_Syntax_Syntax.lbdef = e;_}::[],t_norm::[],
                              (flid_fv,(f,ftok))::[]) ->
                               let flid =
                                 (flid_fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                               let uu____11654 =
                                 let uu____11658 =
                                   FStar_TypeChecker_Env.open_universes_in
                                     env1.tcenv uvs [e; t_norm] in
                                 match uu____11658 with
                                 | (tcenv',uu____11669,e_t) ->
                                     let uu____11673 =
                                       match e_t with
                                       | e1::t_norm1::[] -> (e1, t_norm1)
                                       | uu____11680 -> failwith "Impossible" in
                                     (match uu____11673 with
                                      | (e1,t_norm1) ->
                                          ((let uu___165_11689 = env1 in
                                            {
                                              bindings =
                                                (uu___165_11689.bindings);
                                              depth = (uu___165_11689.depth);
                                              tcenv = tcenv';
                                              warn = (uu___165_11689.warn);
                                              cache = (uu___165_11689.cache);
                                              nolabels =
                                                (uu___165_11689.nolabels);
                                              use_zfuel_name =
                                                (uu___165_11689.use_zfuel_name);
                                              encode_non_total_function_typ =
                                                (uu___165_11689.encode_non_total_function_typ);
                                              current_module_name =
                                                (uu___165_11689.current_module_name)
                                            }), e1, t_norm1)) in
                               (match uu____11654 with
                                | (env',e1,t_norm1) ->
                                    let uu____11696 =
                                      destruct_bound_function flid t_norm1 e1 in
                                    (match uu____11696 with
                                     | ((binders,body,uu____11708,uu____11709),curry)
                                         ->
                                         ((let uu____11716 =
                                             FStar_All.pipe_left
                                               (FStar_TypeChecker_Env.debug
                                                  env1.tcenv)
                                               (FStar_Options.Other
                                                  "SMTEncoding") in
                                           if uu____11716
                                           then
                                             let uu____11717 =
                                               FStar_Syntax_Print.binders_to_string
                                                 ", " binders in
                                             let uu____11718 =
                                               FStar_Syntax_Print.term_to_string
                                                 body in
                                             FStar_Util.print2
                                               "Encoding let : binders=[%s], body=%s\n"
                                               uu____11717 uu____11718
                                           else ());
                                          (let uu____11720 =
                                             encode_binders None binders env' in
                                           match uu____11720 with
                                           | (vars,guards,env'1,binder_decls,uu____11736)
                                               ->
                                               let body1 =
                                                 let uu____11744 =
                                                   FStar_TypeChecker_Env.is_reifiable_function
                                                     env'1.tcenv t_norm1 in
                                                 if uu____11744
                                                 then
                                                   FStar_TypeChecker_Util.reify_body
                                                     env'1.tcenv body
                                                 else body in
                                               let app =
                                                 mk_app1 curry f ftok vars in
                                               let uu____11747 =
                                                 let uu____11752 =
                                                   FStar_All.pipe_right quals
                                                     (FStar_List.contains
                                                        FStar_Syntax_Syntax.Logic) in
                                                 if uu____11752
                                                 then
                                                   let uu____11758 =
                                                     FStar_SMTEncoding_Term.mk_Valid
                                                       app in
                                                   let uu____11759 =
                                                     encode_formula body1
                                                       env'1 in
                                                   (uu____11758, uu____11759)
                                                 else
                                                   (let uu____11765 =
                                                      encode_term body1 env'1 in
                                                    (app, uu____11765)) in
                                               (match uu____11747 with
                                                | (app1,(body2,decls2)) ->
                                                    let eqn =
                                                      let uu____11779 =
                                                        let uu____11783 =
                                                          let uu____11784 =
                                                            let uu____11790 =
                                                              FStar_SMTEncoding_Util.mkEq
                                                                (app1, body2) in
                                                            ([[app1]], vars,
                                                              uu____11790) in
                                                          FStar_SMTEncoding_Util.mkForall
                                                            uu____11784 in
                                                        let uu____11796 =
                                                          let uu____11798 =
                                                            FStar_Util.format1
                                                              "Equation for %s"
                                                              flid.FStar_Ident.str in
                                                          Some uu____11798 in
                                                        (uu____11783,
                                                          uu____11796,
                                                          (Prims.strcat
                                                             "equation_" f)) in
                                                      FStar_SMTEncoding_Term.Assume
                                                        uu____11779 in
                                                    let uu____11800 =
                                                      let uu____11802 =
                                                        let uu____11804 =
                                                          let uu____11806 =
                                                            let uu____11808 =
                                                              primitive_type_axioms
                                                                env1.tcenv
                                                                flid f app1 in
                                                            FStar_List.append
                                                              [eqn]
                                                              uu____11808 in
                                                          FStar_List.append
                                                            decls2
                                                            uu____11806 in
                                                        FStar_List.append
                                                          binder_decls
                                                          uu____11804 in
                                                      FStar_List.append
                                                        decls1 uu____11802 in
                                                    (uu____11800, env1))))))
                           | uu____11811 -> failwith "Impossible")
                        else
                          (let fuel =
                             let uu____11830 = varops.fresh "fuel" in
                             (uu____11830, FStar_SMTEncoding_Term.Fuel_sort) in
                           let fuel_tm = FStar_SMTEncoding_Util.mkFreeV fuel in
                           let env0 = env1 in
                           let uu____11833 =
                             FStar_All.pipe_right toks1
                               (FStar_List.fold_left
                                  (fun uu____11872  ->
                                     fun uu____11873  ->
                                       match (uu____11872, uu____11873) with
                                       | ((gtoks,env2),(flid_fv,(f,ftok))) ->
                                           let flid =
                                             (flid_fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                                           let g =
                                             let uu____11955 =
                                               FStar_Ident.lid_add_suffix
                                                 flid "fuel_instrumented" in
                                             varops.new_fvar uu____11955 in
                                           let gtok =
                                             let uu____11957 =
                                               FStar_Ident.lid_add_suffix
                                                 flid
                                                 "fuel_instrumented_token" in
                                             varops.new_fvar uu____11957 in
                                           let env3 =
                                             let uu____11959 =
                                               let uu____11961 =
                                                 FStar_SMTEncoding_Util.mkApp
                                                   (g, [fuel_tm]) in
                                               FStar_All.pipe_left
                                                 (fun _0_36  -> Some _0_36)
                                                 uu____11961 in
                                             push_free_var env2 flid gtok
                                               uu____11959 in
                                           (((flid, f, ftok, g, gtok) ::
                                             gtoks), env3)) ([], env1)) in
                           match uu____11833 with
                           | (gtoks,env2) ->
                               let gtoks1 = FStar_List.rev gtoks in
                               let encode_one_binding env01 uu____12047
                                 t_norm uu____12049 =
                                 match (uu____12047, uu____12049) with
                                 | ((flid,f,ftok,g,gtok),{
                                                           FStar_Syntax_Syntax.lbname
                                                             = lbn;
                                                           FStar_Syntax_Syntax.lbunivs
                                                             = uvs;
                                                           FStar_Syntax_Syntax.lbtyp
                                                             = uu____12076;
                                                           FStar_Syntax_Syntax.lbeff
                                                             = uu____12077;
                                                           FStar_Syntax_Syntax.lbdef
                                                             = e;_})
                                     ->
                                     let uu____12094 =
                                       let uu____12098 =
                                         FStar_TypeChecker_Env.open_universes_in
                                           env2.tcenv uvs [e; t_norm] in
                                       match uu____12098 with
                                       | (tcenv',uu____12113,e_t) ->
                                           let uu____12117 =
                                             match e_t with
                                             | e1::t_norm1::[] ->
                                                 (e1, t_norm1)
                                             | uu____12124 ->
                                                 failwith "Impossible" in
                                           (match uu____12117 with
                                            | (e1,t_norm1) ->
                                                ((let uu___166_12133 = env2 in
                                                  {
                                                    bindings =
                                                      (uu___166_12133.bindings);
                                                    depth =
                                                      (uu___166_12133.depth);
                                                    tcenv = tcenv';
                                                    warn =
                                                      (uu___166_12133.warn);
                                                    cache =
                                                      (uu___166_12133.cache);
                                                    nolabels =
                                                      (uu___166_12133.nolabels);
                                                    use_zfuel_name =
                                                      (uu___166_12133.use_zfuel_name);
                                                    encode_non_total_function_typ
                                                      =
                                                      (uu___166_12133.encode_non_total_function_typ);
                                                    current_module_name =
                                                      (uu___166_12133.current_module_name)
                                                  }), e1, t_norm1)) in
                                     (match uu____12094 with
                                      | (env',e1,t_norm1) ->
                                          ((let uu____12143 =
                                              FStar_All.pipe_left
                                                (FStar_TypeChecker_Env.debug
                                                   env01.tcenv)
                                                (FStar_Options.Other
                                                   "SMTEncoding") in
                                            if uu____12143
                                            then
                                              let uu____12144 =
                                                FStar_Syntax_Print.lbname_to_string
                                                  lbn in
                                              let uu____12145 =
                                                FStar_Syntax_Print.term_to_string
                                                  t_norm1 in
                                              let uu____12146 =
                                                FStar_Syntax_Print.term_to_string
                                                  e1 in
                                              FStar_Util.print3
                                                "Encoding let rec %s : %s = %s\n"
                                                uu____12144 uu____12145
                                                uu____12146
                                            else ());
                                           (let uu____12148 =
                                              destruct_bound_function flid
                                                t_norm1 e1 in
                                            match uu____12148 with
                                            | ((binders,body,formals,tres),curry)
                                                ->
                                                ((let uu____12170 =
                                                    FStar_All.pipe_left
                                                      (FStar_TypeChecker_Env.debug
                                                         env01.tcenv)
                                                      (FStar_Options.Other
                                                         "SMTEncoding") in
                                                  if uu____12170
                                                  then
                                                    let uu____12171 =
                                                      FStar_Syntax_Print.binders_to_string
                                                        ", " binders in
                                                    let uu____12172 =
                                                      FStar_Syntax_Print.term_to_string
                                                        body in
                                                    let uu____12173 =
                                                      FStar_Syntax_Print.binders_to_string
                                                        ", " formals in
                                                    let uu____12174 =
                                                      FStar_Syntax_Print.term_to_string
                                                        tres in
                                                    FStar_Util.print4
                                                      "Encoding let rec: binders=[%s], body=%s, formals=[%s], tres=%s\n"
                                                      uu____12171 uu____12172
                                                      uu____12173 uu____12174
                                                  else ());
                                                 if curry
                                                 then
                                                   failwith
                                                     "Unexpected type of let rec in SMT Encoding; expected it to be annotated with an arrow type"
                                                 else ();
                                                 (let uu____12178 =
                                                    encode_binders None
                                                      binders env' in
                                                  match uu____12178 with
                                                  | (vars,guards,env'1,binder_decls,uu____12196)
                                                      ->
                                                      let decl_g =
                                                        let uu____12204 =
                                                          let uu____12210 =
                                                            let uu____12212 =
                                                              FStar_List.map
                                                                Prims.snd
                                                                vars in
                                                            FStar_SMTEncoding_Term.Fuel_sort
                                                              :: uu____12212 in
                                                          (g, uu____12210,
                                                            FStar_SMTEncoding_Term.Term_sort,
                                                            (Some
                                                               "Fuel-instrumented function name")) in
                                                        FStar_SMTEncoding_Term.DeclFun
                                                          uu____12204 in
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
                                                        let uu____12227 =
                                                          let uu____12231 =
                                                            FStar_List.map
                                                              FStar_SMTEncoding_Util.mkFreeV
                                                              vars in
                                                          (f, uu____12231) in
                                                        FStar_SMTEncoding_Util.mkApp
                                                          uu____12227 in
                                                      let gsapp =
                                                        let uu____12237 =
                                                          let uu____12241 =
                                                            let uu____12243 =
                                                              FStar_SMTEncoding_Util.mkApp
                                                                ("SFuel",
                                                                  [fuel_tm]) in
                                                            uu____12243 ::
                                                              vars_tm in
                                                          (g, uu____12241) in
                                                        FStar_SMTEncoding_Util.mkApp
                                                          uu____12237 in
                                                      let gmax =
                                                        let uu____12247 =
                                                          let uu____12251 =
                                                            let uu____12253 =
                                                              FStar_SMTEncoding_Util.mkApp
                                                                ("MaxFuel",
                                                                  []) in
                                                            uu____12253 ::
                                                              vars_tm in
                                                          (g, uu____12251) in
                                                        FStar_SMTEncoding_Util.mkApp
                                                          uu____12247 in
                                                      let body1 =
                                                        let uu____12257 =
                                                          FStar_TypeChecker_Env.is_reifiable_function
                                                            env'1.tcenv
                                                            t_norm1 in
                                                        if uu____12257
                                                        then
                                                          FStar_TypeChecker_Util.reify_body
                                                            env'1.tcenv body
                                                        else body in
                                                      let uu____12259 =
                                                        encode_term body1
                                                          env'1 in
                                                      (match uu____12259 with
                                                       | (body_tm,decls2) ->
                                                           let eqn_g =
                                                             let uu____12270
                                                               =
                                                               let uu____12274
                                                                 =
                                                                 let uu____12275
                                                                   =
                                                                   let uu____12283
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
                                                                    uu____12283) in
                                                                 FStar_SMTEncoding_Util.mkForall'
                                                                   uu____12275 in
                                                               let uu____12294
                                                                 =
                                                                 let uu____12296
                                                                   =
                                                                   FStar_Util.format1
                                                                    "Equation for fuel-instrumented recursive function: %s"
                                                                    flid.FStar_Ident.str in
                                                                 Some
                                                                   uu____12296 in
                                                               (uu____12274,
                                                                 uu____12294,
                                                                 (Prims.strcat
                                                                    "equation_with_fuel_"
                                                                    g)) in
                                                             FStar_SMTEncoding_Term.Assume
                                                               uu____12270 in
                                                           let eqn_f =
                                                             let uu____12299
                                                               =
                                                               let uu____12303
                                                                 =
                                                                 let uu____12304
                                                                   =
                                                                   let uu____12310
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (app,
                                                                    gmax) in
                                                                   ([[app]],
                                                                    vars,
                                                                    uu____12310) in
                                                                 FStar_SMTEncoding_Util.mkForall
                                                                   uu____12304 in
                                                               (uu____12303,
                                                                 (Some
                                                                    "Correspondence of recursive function to instrumented version"),
                                                                 (Prims.strcat
                                                                    "@fuel_correspondence_"
                                                                    g)) in
                                                             FStar_SMTEncoding_Term.Assume
                                                               uu____12299 in
                                                           let eqn_g' =
                                                             let uu____12318
                                                               =
                                                               let uu____12322
                                                                 =
                                                                 let uu____12323
                                                                   =
                                                                   let uu____12329
                                                                    =
                                                                    let uu____12330
                                                                    =
                                                                    let uu____12333
                                                                    =
                                                                    let uu____12334
                                                                    =
                                                                    let uu____12338
                                                                    =
                                                                    let uu____12340
                                                                    =
                                                                    FStar_SMTEncoding_Term.n_fuel
                                                                    (Prims.parse_int
                                                                    "0") in
                                                                    uu____12340
                                                                    ::
                                                                    vars_tm in
                                                                    (g,
                                                                    uu____12338) in
                                                                    FStar_SMTEncoding_Util.mkApp
                                                                    uu____12334 in
                                                                    (gsapp,
                                                                    uu____12333) in
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    uu____12330 in
                                                                   ([[gsapp]],
                                                                    (fuel ::
                                                                    vars),
                                                                    uu____12329) in
                                                                 FStar_SMTEncoding_Util.mkForall
                                                                   uu____12323 in
                                                               (uu____12322,
                                                                 (Some
                                                                    "Fuel irrelevance"),
                                                                 (Prims.strcat
                                                                    "@fuel_irrelevance_"
                                                                    g)) in
                                                             FStar_SMTEncoding_Term.Assume
                                                               uu____12318 in
                                                           let uu____12352 =
                                                             let uu____12357
                                                               =
                                                               encode_binders
                                                                 None formals
                                                                 env02 in
                                                             match uu____12357
                                                             with
                                                             | (vars1,v_guards,env3,binder_decls1,uu____12374)
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
                                                                    let uu____12389
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    (gtok,
                                                                    FStar_SMTEncoding_Term.Term_sort) in
                                                                    mk_Apply
                                                                    uu____12389
                                                                    (fuel ::
                                                                    vars1) in
                                                                   let uu____12392
                                                                    =
                                                                    let uu____12396
                                                                    =
                                                                    let uu____12397
                                                                    =
                                                                    let uu____12403
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (tok_app,
                                                                    gapp) in
                                                                    ([
                                                                    [tok_app]],
                                                                    (fuel ::
                                                                    vars1),
                                                                    uu____12403) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____12397 in
                                                                    (uu____12396,
                                                                    (Some
                                                                    "Fuel token correspondence"),
                                                                    (Prims.strcat
                                                                    "fuel_token_correspondence_"
                                                                    gtok)) in
                                                                   FStar_SMTEncoding_Term.Assume
                                                                    uu____12392 in
                                                                 let uu____12414
                                                                   =
                                                                   let uu____12418
                                                                    =
                                                                    encode_term_pred
                                                                    None tres
                                                                    env3 gapp in
                                                                   match uu____12418
                                                                   with
                                                                   | 
                                                                   (g_typing,d3)
                                                                    ->
                                                                    let uu____12426
                                                                    =
                                                                    let uu____12428
                                                                    =
                                                                    let uu____12429
                                                                    =
                                                                    let uu____12433
                                                                    =
                                                                    let uu____12434
                                                                    =
                                                                    let uu____12440
                                                                    =
                                                                    let uu____12441
                                                                    =
                                                                    let uu____12444
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    v_guards in
                                                                    (uu____12444,
                                                                    g_typing) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____12441 in
                                                                    ([[gapp]],
                                                                    (fuel ::
                                                                    vars1),
                                                                    uu____12440) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____12434 in
                                                                    (uu____12433,
                                                                    (Some
                                                                    "Typing correspondence of token to term"),
                                                                    (Prims.strcat
                                                                    "token_correspondence_"
                                                                    g)) in
                                                                    FStar_SMTEncoding_Term.Assume
                                                                    uu____12429 in
                                                                    [uu____12428] in
                                                                    (d3,
                                                                    uu____12426) in
                                                                 (match uu____12414
                                                                  with
                                                                  | (aux_decls,typing_corr)
                                                                    ->
                                                                    ((FStar_List.append
                                                                    binder_decls1
                                                                    aux_decls),
                                                                    (FStar_List.append
                                                                    typing_corr
                                                                    [tok_corr]))) in
                                                           (match uu____12352
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
                               let uu____12479 =
                                 let uu____12486 =
                                   FStar_List.zip3 gtoks1 typs1 bindings in
                                 FStar_List.fold_left
                                   (fun uu____12522  ->
                                      fun uu____12523  ->
                                        match (uu____12522, uu____12523) with
                                        | ((decls2,eqns,env01),(gtok,ty,lb))
                                            ->
                                            let uu____12609 =
                                              encode_one_binding env01 gtok
                                                ty lb in
                                            (match uu____12609 with
                                             | (decls',eqns',env02) ->
                                                 ((decls' :: decls2),
                                                   (FStar_List.append eqns'
                                                      eqns), env02)))
                                   ([decls1], [], env0) uu____12486 in
                               (match uu____12479 with
                                | (decls2,eqns,env01) ->
                                    let uu____12649 =
                                      let isDeclFun uu___132_12657 =
                                        match uu___132_12657 with
                                        | FStar_SMTEncoding_Term.DeclFun
                                            uu____12658 -> true
                                        | uu____12664 -> false in
                                      let uu____12665 =
                                        FStar_All.pipe_right decls2
                                          FStar_List.flatten in
                                      FStar_All.pipe_right uu____12665
                                        (FStar_List.partition isDeclFun) in
                                    (match uu____12649 with
                                     | (prefix_decls,rest) ->
                                         let eqns1 = FStar_List.rev eqns in
                                         ((FStar_List.append prefix_decls
                                             (FStar_List.append rest eqns1)),
                                           env01)))))
             with
             | Let_rec_unencodeable  ->
                 let msg =
                   let uu____12692 =
                     FStar_All.pipe_right bindings
                       (FStar_List.map
                          (fun lb  ->
                             FStar_Syntax_Print.lbname_to_string
                               lb.FStar_Syntax_Syntax.lbname)) in
                   FStar_All.pipe_right uu____12692
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
      (let uu____12725 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv)
           (FStar_Options.Other "SMTEncoding") in
       if uu____12725
       then
         let uu____12726 = FStar_Syntax_Print.sigelt_to_string se in
         FStar_All.pipe_left (FStar_Util.print1 ">>>>Encoding [%s]\n")
           uu____12726
       else ());
      (let nm =
         let uu____12729 = FStar_Syntax_Util.lid_of_sigelt se in
         match uu____12729 with | None  -> "" | Some l -> l.FStar_Ident.str in
       let uu____12732 = encode_sigelt' env se in
       match uu____12732 with
       | (g,e) ->
           (match g with
            | [] ->
                let uu____12741 =
                  let uu____12743 =
                    let uu____12744 = FStar_Util.format1 "<Skipped %s/>" nm in
                    FStar_SMTEncoding_Term.Caption uu____12744 in
                  [uu____12743] in
                (uu____12741, e)
            | uu____12746 ->
                let uu____12747 =
                  let uu____12749 =
                    let uu____12751 =
                      let uu____12752 =
                        FStar_Util.format1 "<Start encoding %s>" nm in
                      FStar_SMTEncoding_Term.Caption uu____12752 in
                    uu____12751 :: g in
                  let uu____12753 =
                    let uu____12755 =
                      let uu____12756 =
                        FStar_Util.format1 "</end encoding %s>" nm in
                      FStar_SMTEncoding_Term.Caption uu____12756 in
                    [uu____12755] in
                  FStar_List.append uu____12749 uu____12753 in
                (uu____12747, e)))
and encode_sigelt':
  env_t ->
    FStar_Syntax_Syntax.sigelt -> (FStar_SMTEncoding_Term.decls_t* env_t)
  =
  fun env  ->
    fun se  ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____12764 ->
          failwith "impossible -- removed by tc.fs"
      | FStar_Syntax_Syntax.Sig_pragma _
        |FStar_Syntax_Syntax.Sig_main _
         |FStar_Syntax_Syntax.Sig_effect_abbrev _
          |FStar_Syntax_Syntax.Sig_sub_effect _ -> ([], env)
      | FStar_Syntax_Syntax.Sig_new_effect ed ->
          let uu____12773 =
            let uu____12774 =
              FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                (FStar_List.contains FStar_Syntax_Syntax.Reifiable) in
            FStar_All.pipe_right uu____12774 Prims.op_Negation in
          if uu____12773
          then ([], env)
          else
            (let close_effect_params tm =
               match ed.FStar_Syntax_Syntax.binders with
               | [] -> tm
               | uu____12794 ->
                   let uu____12795 =
                     let uu____12798 =
                       let uu____12799 =
                         let uu____12814 =
                           FStar_All.pipe_left (fun _0_37  -> Some _0_37)
                             (FStar_Util.Inr
                                (FStar_Syntax_Const.effect_Tot_lid,
                                  [FStar_Syntax_Syntax.TOTAL])) in
                         ((ed.FStar_Syntax_Syntax.binders), tm, uu____12814) in
                       FStar_Syntax_Syntax.Tm_abs uu____12799 in
                     FStar_Syntax_Syntax.mk uu____12798 in
                   uu____12795 None tm.FStar_Syntax_Syntax.pos in
             let encode_action env1 a =
               let uu____12867 =
                 new_term_constant_and_tok_from_lid env1
                   a.FStar_Syntax_Syntax.action_name in
               match uu____12867 with
               | (aname,atok,env2) ->
                   let uu____12877 =
                     FStar_Syntax_Util.arrow_formals_comp
                       a.FStar_Syntax_Syntax.action_typ in
                   (match uu____12877 with
                    | (formals,uu____12887) ->
                        let uu____12894 =
                          let uu____12897 =
                            close_effect_params
                              a.FStar_Syntax_Syntax.action_defn in
                          encode_term uu____12897 env2 in
                        (match uu____12894 with
                         | (tm,decls) ->
                             let a_decls =
                               let uu____12905 =
                                 let uu____12906 =
                                   let uu____12912 =
                                     FStar_All.pipe_right formals
                                       (FStar_List.map
                                          (fun uu____12920  ->
                                             FStar_SMTEncoding_Term.Term_sort)) in
                                   (aname, uu____12912,
                                     FStar_SMTEncoding_Term.Term_sort,
                                     (Some "Action")) in
                                 FStar_SMTEncoding_Term.DeclFun uu____12906 in
                               [uu____12905;
                               FStar_SMTEncoding_Term.DeclFun
                                 (atok, [], FStar_SMTEncoding_Term.Term_sort,
                                   (Some "Action token"))] in
                             let uu____12927 =
                               let aux uu____12956 uu____12957 =
                                 match (uu____12956, uu____12957) with
                                 | ((bv,uu____12984),(env3,acc_sorts,acc)) ->
                                     let uu____13005 = gen_term_var env3 bv in
                                     (match uu____13005 with
                                      | (xxsym,xx,env4) ->
                                          (env4,
                                            ((xxsym,
                                               FStar_SMTEncoding_Term.Term_sort)
                                            :: acc_sorts), (xx :: acc))) in
                               FStar_List.fold_right aux formals
                                 (env2, [], []) in
                             (match uu____12927 with
                              | (uu____13043,xs_sorts,xs) ->
                                  let app =
                                    FStar_SMTEncoding_Util.mkApp (aname, xs) in
                                  let a_eq =
                                    let uu____13057 =
                                      let uu____13061 =
                                        let uu____13062 =
                                          let uu____13068 =
                                            let uu____13069 =
                                              let uu____13072 =
                                                mk_Apply tm xs_sorts in
                                              (app, uu____13072) in
                                            FStar_SMTEncoding_Util.mkEq
                                              uu____13069 in
                                          ([[app]], xs_sorts, uu____13068) in
                                        FStar_SMTEncoding_Util.mkForall
                                          uu____13062 in
                                      (uu____13061, (Some "Action equality"),
                                        (Prims.strcat aname "_equality")) in
                                    FStar_SMTEncoding_Term.Assume uu____13057 in
                                  let tok_correspondence =
                                    let tok_term =
                                      FStar_SMTEncoding_Util.mkFreeV
                                        (atok,
                                          FStar_SMTEncoding_Term.Term_sort) in
                                    let tok_app = mk_Apply tok_term xs_sorts in
                                    let uu____13084 =
                                      let uu____13088 =
                                        let uu____13089 =
                                          let uu____13095 =
                                            FStar_SMTEncoding_Util.mkEq
                                              (tok_app, app) in
                                          ([[tok_app]], xs_sorts,
                                            uu____13095) in
                                        FStar_SMTEncoding_Util.mkForall
                                          uu____13089 in
                                      (uu____13088,
                                        (Some "Action token correspondence"),
                                        (Prims.strcat aname
                                           "_token_correspondence")) in
                                    FStar_SMTEncoding_Term.Assume uu____13084 in
                                  (env2,
                                    (FStar_List.append decls
                                       (FStar_List.append a_decls
                                          [a_eq; tok_correspondence])))))) in
             let uu____13105 =
               FStar_Util.fold_map encode_action env
                 ed.FStar_Syntax_Syntax.actions in
             match uu____13105 with
             | (env1,decls2) -> ((FStar_List.flatten decls2), env1))
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____13121,uu____13122)
          when FStar_Ident.lid_equals lid FStar_Syntax_Const.precedes_lid ->
          let uu____13123 = new_term_constant_and_tok_from_lid env lid in
          (match uu____13123 with | (tname,ttok,env1) -> ([], env1))
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____13134,t) ->
          let quals = se.FStar_Syntax_Syntax.sigquals in
          let will_encode_definition =
            let uu____13139 =
              FStar_All.pipe_right quals
                (FStar_Util.for_some
                   (fun uu___133_13141  ->
                      match uu___133_13141 with
                      | FStar_Syntax_Syntax.Assumption 
                        |FStar_Syntax_Syntax.Projector _
                         |FStar_Syntax_Syntax.Discriminator _
                          |FStar_Syntax_Syntax.Irreducible  -> true
                      | uu____13144 -> false)) in
            Prims.op_Negation uu____13139 in
          if will_encode_definition
          then ([], env)
          else
            (let fv =
               FStar_Syntax_Syntax.lid_as_fv lid
                 FStar_Syntax_Syntax.Delta_constant None in
             let uu____13150 = encode_top_level_val env fv t quals in
             match uu____13150 with
             | (decls,env1) ->
                 let tname = lid.FStar_Ident.str in
                 let tsym =
                   FStar_SMTEncoding_Util.mkFreeV
                     (tname, FStar_SMTEncoding_Term.Term_sort) in
                 let uu____13162 =
                   let uu____13164 =
                     primitive_type_axioms env1.tcenv lid tname tsym in
                   FStar_List.append decls uu____13164 in
                 (uu____13162, env1))
      | FStar_Syntax_Syntax.Sig_assume (l,f) ->
          let uu____13169 = encode_formula f env in
          (match uu____13169 with
           | (f1,decls) ->
               let g =
                 let uu____13178 =
                   let uu____13179 =
                     let uu____13183 =
                       let uu____13185 =
                         let uu____13186 = FStar_Syntax_Print.lid_to_string l in
                         FStar_Util.format1 "Assumption: %s" uu____13186 in
                       Some uu____13185 in
                     let uu____13187 =
                       varops.mk_unique
                         (Prims.strcat "assumption_" l.FStar_Ident.str) in
                     (f1, uu____13183, uu____13187) in
                   FStar_SMTEncoding_Term.Assume uu____13179 in
                 [uu____13178] in
               ((FStar_List.append decls g), env))
      | FStar_Syntax_Syntax.Sig_let (lbs,uu____13191,uu____13192) when
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_List.contains FStar_Syntax_Syntax.Irreducible)
          ->
          let uu____13198 =
            FStar_Util.fold_map
              (fun env1  ->
                 fun lb  ->
                   let lid =
                     let uu____13205 =
                       let uu____13210 =
                         FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
                       uu____13210.FStar_Syntax_Syntax.fv_name in
                     uu____13205.FStar_Syntax_Syntax.v in
                   let uu____13214 =
                     let uu____13215 =
                       FStar_TypeChecker_Env.try_lookup_val_decl env1.tcenv
                         lid in
                     FStar_All.pipe_left FStar_Option.isNone uu____13215 in
                   if uu____13214
                   then
                     let val_decl =
                       let uu___167_13230 = se in
                       {
                         FStar_Syntax_Syntax.sigel =
                           (FStar_Syntax_Syntax.Sig_declare_typ
                              (lid, (lb.FStar_Syntax_Syntax.lbunivs),
                                (lb.FStar_Syntax_Syntax.lbtyp)));
                         FStar_Syntax_Syntax.sigrng =
                           (uu___167_13230.FStar_Syntax_Syntax.sigrng);
                         FStar_Syntax_Syntax.sigquals =
                           (uu___167_13230.FStar_Syntax_Syntax.sigquals);
                         FStar_Syntax_Syntax.sigmeta =
                           (uu___167_13230.FStar_Syntax_Syntax.sigmeta)
                       } in
                     let uu____13234 = encode_sigelt' env1 val_decl in
                     match uu____13234 with | (decls,env2) -> (env2, decls)
                   else (env1, [])) env (Prims.snd lbs) in
          (match uu____13198 with
           | (env1,decls) -> ((FStar_List.flatten decls), env1))
      | FStar_Syntax_Syntax.Sig_let
          ((uu____13251,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inr b2t1;
                          FStar_Syntax_Syntax.lbunivs = uu____13253;
                          FStar_Syntax_Syntax.lbtyp = uu____13254;
                          FStar_Syntax_Syntax.lbeff = uu____13255;
                          FStar_Syntax_Syntax.lbdef = uu____13256;_}::[]),uu____13257,uu____13258)
          when FStar_Syntax_Syntax.fv_eq_lid b2t1 FStar_Syntax_Const.b2t_lid
          ->
          let uu____13272 =
            new_term_constant_and_tok_from_lid env
              (b2t1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          (match uu____13272 with
           | (tname,ttok,env1) ->
               let xx = ("x", FStar_SMTEncoding_Term.Term_sort) in
               let x = FStar_SMTEncoding_Util.mkFreeV xx in
               let b2t_x = FStar_SMTEncoding_Util.mkApp ("Prims.b2t", [x]) in
               let valid_b2t_x =
                 FStar_SMTEncoding_Util.mkApp ("Valid", [b2t_x]) in
               let decls =
                 let uu____13295 =
                   let uu____13297 =
                     let uu____13298 =
                       let uu____13302 =
                         let uu____13303 =
                           let uu____13309 =
                             let uu____13310 =
                               let uu____13313 =
                                 FStar_SMTEncoding_Util.mkApp
                                   ("BoxBool_proj_0", [x]) in
                               (valid_b2t_x, uu____13313) in
                             FStar_SMTEncoding_Util.mkEq uu____13310 in
                           ([[b2t_x]], [xx], uu____13309) in
                         FStar_SMTEncoding_Util.mkForall uu____13303 in
                       (uu____13302, (Some "b2t def"), "b2t_def") in
                     FStar_SMTEncoding_Term.Assume uu____13298 in
                   [uu____13297] in
                 (FStar_SMTEncoding_Term.DeclFun
                    (tname, [FStar_SMTEncoding_Term.Term_sort],
                      FStar_SMTEncoding_Term.Term_sort, None))
                   :: uu____13295 in
               (decls, env1))
      | FStar_Syntax_Syntax.Sig_let (uu____13330,uu____13331,uu____13332)
          when
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some
               (fun uu___134_13338  ->
                  match uu___134_13338 with
                  | FStar_Syntax_Syntax.Discriminator uu____13339 -> true
                  | uu____13340 -> false))
          -> ([], env)
      | FStar_Syntax_Syntax.Sig_let (uu____13342,lids,uu____13344) when
          (FStar_All.pipe_right lids
             (FStar_Util.for_some
                (fun l  ->
                   let uu____13351 =
                     let uu____13352 = FStar_List.hd l.FStar_Ident.ns in
                     uu____13352.FStar_Ident.idText in
                   uu____13351 = "Prims")))
            &&
            (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
               (FStar_Util.for_some
                  (fun uu___135_13354  ->
                     match uu___135_13354 with
                     | FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen 
                         -> true
                     | uu____13355 -> false)))
          -> ([], env)
      | FStar_Syntax_Syntax.Sig_let ((false ,lb::[]),uu____13358,uu____13359)
          when
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some
               (fun uu___136_13369  ->
                  match uu___136_13369 with
                  | FStar_Syntax_Syntax.Projector uu____13370 -> true
                  | uu____13373 -> false))
          ->
          let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
          let l = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          let uu____13380 = try_lookup_free_var env l in
          (match uu____13380 with
           | Some uu____13384 -> ([], env)
           | None  ->
               let se1 =
                 let uu___168_13387 = se in
                 {
                   FStar_Syntax_Syntax.sigel =
                     (FStar_Syntax_Syntax.Sig_declare_typ
                        (l, (lb.FStar_Syntax_Syntax.lbunivs),
                          (lb.FStar_Syntax_Syntax.lbtyp)));
                   FStar_Syntax_Syntax.sigrng = (FStar_Ident.range_of_lid l);
                   FStar_Syntax_Syntax.sigquals =
                     (uu___168_13387.FStar_Syntax_Syntax.sigquals);
                   FStar_Syntax_Syntax.sigmeta =
                     (uu___168_13387.FStar_Syntax_Syntax.sigmeta)
                 } in
               encode_sigelt env se1)
      | FStar_Syntax_Syntax.Sig_let
          ((is_rec,bindings),uu____13393,uu____13394) ->
          encode_top_level_let env (is_rec, bindings)
            se.FStar_Syntax_Syntax.sigquals
      | FStar_Syntax_Syntax.Sig_bundle (ses,uu____13406) ->
          let uu____13411 = encode_signature env ses in
          (match uu____13411 with
           | (g,env1) ->
               let uu____13421 =
                 FStar_All.pipe_right g
                   (FStar_List.partition
                      (fun uu___137_13431  ->
                         match uu___137_13431 with
                         | FStar_SMTEncoding_Term.Assume
                             (uu____13432,Some "inversion axiom",uu____13433)
                             -> false
                         | uu____13435 -> true)) in
               (match uu____13421 with
                | (g',inversions) ->
                    let uu____13444 =
                      FStar_All.pipe_right g'
                        (FStar_List.partition
                           (fun uu___138_13454  ->
                              match uu___138_13454 with
                              | FStar_SMTEncoding_Term.DeclFun uu____13455 ->
                                  true
                              | uu____13461 -> false)) in
                    (match uu____13444 with
                     | (decls,rest) ->
                         ((FStar_List.append decls
                             (FStar_List.append rest inversions)), env1))))
      | FStar_Syntax_Syntax.Sig_inductive_typ
          (t,uu____13472,tps,k,uu____13475,datas) ->
          let quals = se.FStar_Syntax_Syntax.sigquals in
          let is_logical =
            FStar_All.pipe_right quals
              (FStar_Util.for_some
                 (fun uu___139_13485  ->
                    match uu___139_13485 with
                    | FStar_Syntax_Syntax.Logic 
                      |FStar_Syntax_Syntax.Assumption  -> true
                    | uu____13486 -> false)) in
          let constructor_or_logic_type_decl c =
            if is_logical
            then
              let uu____13493 = c in
              match uu____13493 with
              | (name,args,uu____13497,uu____13498,uu____13499) ->
                  let uu____13502 =
                    let uu____13503 =
                      let uu____13509 =
                        FStar_All.pipe_right args
                          (FStar_List.map
                             (fun uu____13516  ->
                                match uu____13516 with
                                | (uu____13520,sort,uu____13522) -> sort)) in
                      (name, uu____13509, FStar_SMTEncoding_Term.Term_sort,
                        None) in
                    FStar_SMTEncoding_Term.DeclFun uu____13503 in
                  [uu____13502]
            else FStar_SMTEncoding_Term.constructor_to_decl c in
          let inversion_axioms tapp vars =
            let uu____13540 =
              FStar_All.pipe_right datas
                (FStar_Util.for_some
                   (fun l  ->
                      let uu____13543 =
                        FStar_TypeChecker_Env.try_lookup_lid env.tcenv l in
                      FStar_All.pipe_right uu____13543 FStar_Option.isNone)) in
            if uu____13540
            then []
            else
              (let uu____13560 =
                 fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort in
               match uu____13560 with
               | (xxsym,xx) ->
                   let uu____13566 =
                     FStar_All.pipe_right datas
                       (FStar_List.fold_left
                          (fun uu____13577  ->
                             fun l  ->
                               match uu____13577 with
                               | (out,decls) ->
                                   let uu____13589 =
                                     FStar_TypeChecker_Env.lookup_datacon
                                       env.tcenv l in
                                   (match uu____13589 with
                                    | (uu____13595,data_t) ->
                                        let uu____13597 =
                                          FStar_Syntax_Util.arrow_formals
                                            data_t in
                                        (match uu____13597 with
                                         | (args,res) ->
                                             let indices =
                                               let uu____13626 =
                                                 let uu____13627 =
                                                   FStar_Syntax_Subst.compress
                                                     res in
                                                 uu____13627.FStar_Syntax_Syntax.n in
                                               match uu____13626 with
                                               | FStar_Syntax_Syntax.Tm_app
                                                   (uu____13635,indices) ->
                                                   indices
                                               | uu____13651 -> [] in
                                             let env1 =
                                               FStar_All.pipe_right args
                                                 (FStar_List.fold_left
                                                    (fun env1  ->
                                                       fun uu____13663  ->
                                                         match uu____13663
                                                         with
                                                         | (x,uu____13667) ->
                                                             let uu____13668
                                                               =
                                                               let uu____13669
                                                                 =
                                                                 let uu____13673
                                                                   =
                                                                   mk_term_projector_name
                                                                    l x in
                                                                 (uu____13673,
                                                                   [xx]) in
                                                               FStar_SMTEncoding_Util.mkApp
                                                                 uu____13669 in
                                                             push_term_var
                                                               env1 x
                                                               uu____13668)
                                                    env) in
                                             let uu____13675 =
                                               encode_args indices env1 in
                                             (match uu____13675 with
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
                                                      let uu____13695 =
                                                        FStar_List.map2
                                                          (fun v1  ->
                                                             fun a  ->
                                                               let uu____13703
                                                                 =
                                                                 let uu____13706
                                                                   =
                                                                   FStar_SMTEncoding_Util.mkFreeV
                                                                    v1 in
                                                                 (uu____13706,
                                                                   a) in
                                                               FStar_SMTEncoding_Util.mkEq
                                                                 uu____13703)
                                                          vars indices1 in
                                                      FStar_All.pipe_right
                                                        uu____13695
                                                        FStar_SMTEncoding_Util.mk_and_l in
                                                    let uu____13708 =
                                                      let uu____13709 =
                                                        let uu____13712 =
                                                          let uu____13713 =
                                                            let uu____13716 =
                                                              mk_data_tester
                                                                env1 l xx in
                                                            (uu____13716,
                                                              eqs) in
                                                          FStar_SMTEncoding_Util.mkAnd
                                                            uu____13713 in
                                                        (out, uu____13712) in
                                                      FStar_SMTEncoding_Util.mkOr
                                                        uu____13709 in
                                                    (uu____13708,
                                                      (FStar_List.append
                                                         decls decls'))))))))
                          (FStar_SMTEncoding_Util.mkFalse, [])) in
                   (match uu____13566 with
                    | (data_ax,decls) ->
                        let uu____13724 =
                          fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort in
                        (match uu____13724 with
                         | (ffsym,ff) ->
                             let fuel_guarded_inversion =
                               let xx_has_type_sfuel =
                                 if
                                   (FStar_List.length datas) >
                                     (Prims.parse_int "1")
                                 then
                                   let uu____13735 =
                                     FStar_SMTEncoding_Util.mkApp
                                       ("SFuel", [ff]) in
                                   FStar_SMTEncoding_Term.mk_HasTypeFuel
                                     uu____13735 xx tapp
                                 else
                                   FStar_SMTEncoding_Term.mk_HasTypeFuel ff
                                     xx tapp in
                               let uu____13738 =
                                 let uu____13742 =
                                   let uu____13743 =
                                     let uu____13749 =
                                       add_fuel
                                         (ffsym,
                                           FStar_SMTEncoding_Term.Fuel_sort)
                                         ((xxsym,
                                            FStar_SMTEncoding_Term.Term_sort)
                                         :: vars) in
                                     let uu____13757 =
                                       FStar_SMTEncoding_Util.mkImp
                                         (xx_has_type_sfuel, data_ax) in
                                     ([[xx_has_type_sfuel]], uu____13749,
                                       uu____13757) in
                                   FStar_SMTEncoding_Util.mkForall
                                     uu____13743 in
                                 let uu____13765 =
                                   varops.mk_unique
                                     (Prims.strcat "fuel_guarded_inversion_"
                                        t.FStar_Ident.str) in
                                 (uu____13742, (Some "inversion axiom"),
                                   uu____13765) in
                               FStar_SMTEncoding_Term.Assume uu____13738 in
                             let pattern_guarded_inversion =
                               let uu____13769 =
                                 (contains_name env "Prims.inversion") &&
                                   ((FStar_List.length datas) >
                                      (Prims.parse_int "1")) in
                               if uu____13769
                               then
                                 let xx_has_type_fuel =
                                   FStar_SMTEncoding_Term.mk_HasTypeFuel ff
                                     xx tapp in
                                 let pattern_guard =
                                   FStar_SMTEncoding_Util.mkApp
                                     ("Prims.inversion", [tapp]) in
                                 let uu____13777 =
                                   let uu____13778 =
                                     let uu____13782 =
                                       let uu____13783 =
                                         let uu____13789 =
                                           add_fuel
                                             (ffsym,
                                               FStar_SMTEncoding_Term.Fuel_sort)
                                             ((xxsym,
                                                FStar_SMTEncoding_Term.Term_sort)
                                             :: vars) in
                                         let uu____13797 =
                                           FStar_SMTEncoding_Util.mkImp
                                             (xx_has_type_fuel, data_ax) in
                                         ([[xx_has_type_fuel; pattern_guard]],
                                           uu____13789, uu____13797) in
                                       FStar_SMTEncoding_Util.mkForall
                                         uu____13783 in
                                     let uu____13805 =
                                       varops.mk_unique
                                         (Prims.strcat
                                            "pattern_guarded_inversion_"
                                            t.FStar_Ident.str) in
                                     (uu____13782, (Some "inversion axiom"),
                                       uu____13805) in
                                   FStar_SMTEncoding_Term.Assume uu____13778 in
                                 [uu____13777]
                               else [] in
                             FStar_List.append decls
                               (FStar_List.append [fuel_guarded_inversion]
                                  pattern_guarded_inversion)))) in
          let uu____13808 =
            let uu____13816 =
              let uu____13817 = FStar_Syntax_Subst.compress k in
              uu____13817.FStar_Syntax_Syntax.n in
            match uu____13816 with
            | FStar_Syntax_Syntax.Tm_arrow (formals,kres) ->
                ((FStar_List.append tps formals),
                  (FStar_Syntax_Util.comp_result kres))
            | uu____13846 -> (tps, k) in
          (match uu____13808 with
           | (formals,res) ->
               let uu____13861 = FStar_Syntax_Subst.open_term formals res in
               (match uu____13861 with
                | (formals1,res1) ->
                    let uu____13868 = encode_binders None formals1 env in
                    (match uu____13868 with
                     | (vars,guards,env',binder_decls,uu____13883) ->
                         let uu____13890 =
                           new_term_constant_and_tok_from_lid env t in
                         (match uu____13890 with
                          | (tname,ttok,env1) ->
                              let ttok_tm =
                                FStar_SMTEncoding_Util.mkApp (ttok, []) in
                              let guard =
                                FStar_SMTEncoding_Util.mk_and_l guards in
                              let tapp =
                                let uu____13903 =
                                  let uu____13907 =
                                    FStar_List.map
                                      FStar_SMTEncoding_Util.mkFreeV vars in
                                  (tname, uu____13907) in
                                FStar_SMTEncoding_Util.mkApp uu____13903 in
                              let uu____13912 =
                                let tname_decl =
                                  let uu____13918 =
                                    let uu____13919 =
                                      FStar_All.pipe_right vars
                                        (FStar_List.map
                                           (fun uu____13934  ->
                                              match uu____13934 with
                                              | (n1,s) ->
                                                  ((Prims.strcat tname n1),
                                                    s, false))) in
                                    let uu____13942 = varops.next_id () in
                                    (tname, uu____13919,
                                      FStar_SMTEncoding_Term.Term_sort,
                                      uu____13942, false) in
                                  constructor_or_logic_type_decl uu____13918 in
                                let uu____13947 =
                                  match vars with
                                  | [] ->
                                      let uu____13954 =
                                        let uu____13955 =
                                          let uu____13957 =
                                            FStar_SMTEncoding_Util.mkApp
                                              (tname, []) in
                                          FStar_All.pipe_left
                                            (fun _0_38  -> Some _0_38)
                                            uu____13957 in
                                        push_free_var env1 t tname
                                          uu____13955 in
                                      ([], uu____13954)
                                  | uu____13961 ->
                                      let ttok_decl =
                                        FStar_SMTEncoding_Term.DeclFun
                                          (ttok, [],
                                            FStar_SMTEncoding_Term.Term_sort,
                                            (Some "token")) in
                                      let ttok_fresh =
                                        let uu____13967 = varops.next_id () in
                                        FStar_SMTEncoding_Term.fresh_token
                                          (ttok,
                                            FStar_SMTEncoding_Term.Term_sort)
                                          uu____13967 in
                                      let ttok_app = mk_Apply ttok_tm vars in
                                      let pats = [[ttok_app]; [tapp]] in
                                      let name_tok_corr =
                                        let uu____13976 =
                                          let uu____13980 =
                                            let uu____13981 =
                                              let uu____13989 =
                                                FStar_SMTEncoding_Util.mkEq
                                                  (ttok_app, tapp) in
                                              (pats, None, vars, uu____13989) in
                                            FStar_SMTEncoding_Util.mkForall'
                                              uu____13981 in
                                          (uu____13980,
                                            (Some "name-token correspondence"),
                                            (Prims.strcat
                                               "token_correspondence_" ttok)) in
                                        FStar_SMTEncoding_Term.Assume
                                          uu____13976 in
                                      ([ttok_decl; ttok_fresh; name_tok_corr],
                                        env1) in
                                match uu____13947 with
                                | (tok_decls,env2) ->
                                    ((FStar_List.append tname_decl tok_decls),
                                      env2) in
                              (match uu____13912 with
                               | (decls,env2) ->
                                   let kindingAx =
                                     let uu____14012 =
                                       encode_term_pred None res1 env' tapp in
                                     match uu____14012 with
                                     | (k1,decls1) ->
                                         let karr =
                                           if
                                             (FStar_List.length formals1) >
                                               (Prims.parse_int "0")
                                           then
                                             let uu____14026 =
                                               let uu____14027 =
                                                 let uu____14031 =
                                                   let uu____14032 =
                                                     FStar_SMTEncoding_Term.mk_PreType
                                                       ttok_tm in
                                                   FStar_SMTEncoding_Term.mk_tester
                                                     "Tm_arrow" uu____14032 in
                                                 (uu____14031,
                                                   (Some "kinding"),
                                                   (Prims.strcat
                                                      "pre_kinding_" ttok)) in
                                               FStar_SMTEncoding_Term.Assume
                                                 uu____14027 in
                                             [uu____14026]
                                           else [] in
                                         let uu____14035 =
                                           let uu____14037 =
                                             let uu____14039 =
                                               let uu____14040 =
                                                 let uu____14044 =
                                                   let uu____14045 =
                                                     let uu____14051 =
                                                       FStar_SMTEncoding_Util.mkImp
                                                         (guard, k1) in
                                                     ([[tapp]], vars,
                                                       uu____14051) in
                                                   FStar_SMTEncoding_Util.mkForall
                                                     uu____14045 in
                                                 (uu____14044, None,
                                                   (Prims.strcat "kinding_"
                                                      ttok)) in
                                               FStar_SMTEncoding_Term.Assume
                                                 uu____14040 in
                                             [uu____14039] in
                                           FStar_List.append karr uu____14037 in
                                         FStar_List.append decls1 uu____14035 in
                                   let aux =
                                     let uu____14060 =
                                       let uu____14062 =
                                         inversion_axioms tapp vars in
                                       let uu____14064 =
                                         let uu____14066 =
                                           pretype_axiom env2 tapp vars in
                                         [uu____14066] in
                                       FStar_List.append uu____14062
                                         uu____14064 in
                                     FStar_List.append kindingAx uu____14060 in
                                   let g =
                                     FStar_List.append decls
                                       (FStar_List.append binder_decls aux) in
                                   (g, env2))))))
      | FStar_Syntax_Syntax.Sig_datacon
          (d,uu____14071,uu____14072,uu____14073,uu____14074,uu____14075)
          when FStar_Ident.lid_equals d FStar_Syntax_Const.lexcons_lid ->
          ([], env)
      | FStar_Syntax_Syntax.Sig_datacon
          (d,uu____14080,t,uu____14082,n_tps,uu____14084) ->
          let quals = se.FStar_Syntax_Syntax.sigquals in
          let uu____14089 = new_term_constant_and_tok_from_lid env d in
          (match uu____14089 with
           | (ddconstrsym,ddtok,env1) ->
               let ddtok_tm = FStar_SMTEncoding_Util.mkApp (ddtok, []) in
               let uu____14100 = FStar_Syntax_Util.arrow_formals t in
               (match uu____14100 with
                | (formals,t_res) ->
                    let uu____14122 =
                      fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort in
                    (match uu____14122 with
                     | (fuel_var,fuel_tm) ->
                         let s_fuel_tm =
                           FStar_SMTEncoding_Util.mkApp ("SFuel", [fuel_tm]) in
                         let uu____14131 =
                           encode_binders (Some fuel_tm) formals env1 in
                         (match uu____14131 with
                          | (vars,guards,env',binder_decls,names1) ->
                              let fields =
                                FStar_All.pipe_right names1
                                  (FStar_List.mapi
                                     (fun n1  ->
                                        fun x  ->
                                          let projectible = true in
                                          let uu____14169 =
                                            mk_term_projector_name d x in
                                          (uu____14169,
                                            FStar_SMTEncoding_Term.Term_sort,
                                            projectible))) in
                              let datacons =
                                let uu____14171 =
                                  let uu____14181 = varops.next_id () in
                                  (ddconstrsym, fields,
                                    FStar_SMTEncoding_Term.Term_sort,
                                    uu____14181, true) in
                                FStar_All.pipe_right uu____14171
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
                              let uu____14203 =
                                encode_term_pred None t env1 ddtok_tm in
                              (match uu____14203 with
                               | (tok_typing,decls3) ->
                                   let tok_typing1 =
                                     match fields with
                                     | uu____14211::uu____14212 ->
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
                                         let uu____14237 =
                                           let uu____14243 =
                                             FStar_SMTEncoding_Term.mk_NoHoist
                                               f tok_typing in
                                           ([[vtok_app_l]; [vtok_app_r]],
                                             [ff], uu____14243) in
                                         FStar_SMTEncoding_Util.mkForall
                                           uu____14237
                                     | uu____14256 -> tok_typing in
                                   let uu____14261 =
                                     encode_binders (Some fuel_tm) formals
                                       env1 in
                                   (match uu____14261 with
                                    | (vars',guards',env'',decls_formals,uu____14276)
                                        ->
                                        let uu____14283 =
                                          let xvars1 =
                                            FStar_List.map
                                              FStar_SMTEncoding_Util.mkFreeV
                                              vars' in
                                          let dapp1 =
                                            FStar_SMTEncoding_Util.mkApp
                                              (ddconstrsym, xvars1) in
                                          encode_term_pred (Some fuel_tm)
                                            t_res env'' dapp1 in
                                        (match uu____14283 with
                                         | (ty_pred',decls_pred) ->
                                             let guard' =
                                               FStar_SMTEncoding_Util.mk_and_l
                                                 guards' in
                                             let proxy_fresh =
                                               match formals with
                                               | [] -> []
                                               | uu____14302 ->
                                                   let uu____14306 =
                                                     let uu____14307 =
                                                       varops.next_id () in
                                                     FStar_SMTEncoding_Term.fresh_token
                                                       (ddtok,
                                                         FStar_SMTEncoding_Term.Term_sort)
                                                       uu____14307 in
                                                   [uu____14306] in
                                             let encode_elim uu____14314 =
                                               let uu____14315 =
                                                 FStar_Syntax_Util.head_and_args
                                                   t_res in
                                               match uu____14315 with
                                               | (head1,args) ->
                                                   let uu____14344 =
                                                     let uu____14345 =
                                                       FStar_Syntax_Subst.compress
                                                         head1 in
                                                     uu____14345.FStar_Syntax_Syntax.n in
                                                   (match uu____14344 with
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
                                                        let uu____14363 =
                                                          encode_args args
                                                            env' in
                                                        (match uu____14363
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
                                                                 | uu____14389
                                                                    ->
                                                                    failwith
                                                                    "Impossible: parameter must be a variable" in
                                                               let guards1 =
                                                                 FStar_All.pipe_right
                                                                   guards
                                                                   (FStar_List.collect
                                                                    (fun g 
                                                                    ->
                                                                    let uu____14397
                                                                    =
                                                                    let uu____14398
                                                                    =
                                                                    FStar_SMTEncoding_Term.free_variables
                                                                    g in
                                                                    FStar_List.contains
                                                                    fv1
                                                                    uu____14398 in
                                                                    if
                                                                    uu____14397
                                                                    then
                                                                    let uu____14405
                                                                    =
                                                                    FStar_SMTEncoding_Term.subst
                                                                    g fv1 xv in
                                                                    [uu____14405]
                                                                    else [])) in
                                                               FStar_SMTEncoding_Util.mk_and_l
                                                                 guards1 in
                                                             let uu____14407
                                                               =
                                                               FStar_List.fold_left
                                                                 (fun
                                                                    uu____14420
                                                                     ->
                                                                    fun arg 
                                                                    ->
                                                                    match uu____14420
                                                                    with
                                                                    | 
                                                                    (env2,arg_vars,eqns_or_guards,i)
                                                                    ->
                                                                    let uu____14442
                                                                    =
                                                                    let uu____14446
                                                                    =
                                                                    FStar_Syntax_Syntax.new_bv
                                                                    None
                                                                    FStar_Syntax_Syntax.tun in
                                                                    gen_term_var
                                                                    env2
                                                                    uu____14446 in
                                                                    (match uu____14442
                                                                    with
                                                                    | 
                                                                    (uu____14453,xv,env3)
                                                                    ->
                                                                    let eqns
                                                                    =
                                                                    if
                                                                    i < n_tps
                                                                    then
                                                                    let uu____14459
                                                                    =
                                                                    guards_for_parameter
                                                                    arg xv in
                                                                    uu____14459
                                                                    ::
                                                                    eqns_or_guards
                                                                    else
                                                                    (let uu____14461
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (arg, xv) in
                                                                    uu____14461
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
                                                             (match uu____14407
                                                              with
                                                              | (uu____14469,arg_vars,elim_eqns_or_guards,uu____14472)
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
                                                                    let uu____14491
                                                                    =
                                                                    let uu____14495
                                                                    =
                                                                    let uu____14496
                                                                    =
                                                                    let uu____14502
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders) in
                                                                    let uu____14508
                                                                    =
                                                                    let uu____14509
                                                                    =
                                                                    let uu____14512
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    (FStar_List.append
                                                                    elim_eqns_or_guards
                                                                    guards) in
                                                                    (ty_pred,
                                                                    uu____14512) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____14509 in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____14502,
                                                                    uu____14508) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____14496 in
                                                                    (uu____14495,
                                                                    (Some
                                                                    "data constructor typing elim"),
                                                                    (Prims.strcat
                                                                    "data_elim_"
                                                                    ddconstrsym)) in
                                                                    FStar_SMTEncoding_Term.Assume
                                                                    uu____14491 in
                                                                  let subterm_ordering
                                                                    =
                                                                    if
                                                                    FStar_Ident.lid_equals
                                                                    d
                                                                    FStar_Syntax_Const.lextop_lid
                                                                    then
                                                                    let x =
                                                                    let uu____14525
                                                                    =
                                                                    varops.fresh
                                                                    "x" in
                                                                    (uu____14525,
                                                                    FStar_SMTEncoding_Term.Term_sort) in
                                                                    let xtm =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    x in
                                                                    let uu____14527
                                                                    =
                                                                    let uu____14531
                                                                    =
                                                                    let uu____14532
                                                                    =
                                                                    let uu____14538
                                                                    =
                                                                    let uu____14541
                                                                    =
                                                                    let uu____14543
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp1 in
                                                                    [uu____14543] in
                                                                    [uu____14541] in
                                                                    let uu____14546
                                                                    =
                                                                    let uu____14547
                                                                    =
                                                                    let uu____14550
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_tester
                                                                    "LexCons"
                                                                    xtm in
                                                                    let uu____14551
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp1 in
                                                                    (uu____14550,
                                                                    uu____14551) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____14547 in
                                                                    (uu____14538,
                                                                    [x],
                                                                    uu____14546) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____14532 in
                                                                    let uu____14561
                                                                    =
                                                                    varops.mk_unique
                                                                    "lextop" in
                                                                    (uu____14531,
                                                                    (Some
                                                                    "lextop is top"),
                                                                    uu____14561) in
                                                                    FStar_SMTEncoding_Term.Assume
                                                                    uu____14527
                                                                    else
                                                                    (let prec
                                                                    =
                                                                    let uu____14566
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
                                                                    (let uu____14581
                                                                    =
                                                                    let uu____14582
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    v1 in
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    uu____14582
                                                                    dapp1 in
                                                                    [uu____14581]))) in
                                                                    FStar_All.pipe_right
                                                                    uu____14566
                                                                    FStar_List.flatten in
                                                                    let uu____14586
                                                                    =
                                                                    let uu____14590
                                                                    =
                                                                    let uu____14591
                                                                    =
                                                                    let uu____14597
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders) in
                                                                    let uu____14603
                                                                    =
                                                                    let uu____14604
                                                                    =
                                                                    let uu____14607
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    prec in
                                                                    (ty_pred,
                                                                    uu____14607) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____14604 in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____14597,
                                                                    uu____14603) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____14591 in
                                                                    (uu____14590,
                                                                    (Some
                                                                    "subterm ordering"),
                                                                    (Prims.strcat
                                                                    "subterm_ordering_"
                                                                    ddconstrsym)) in
                                                                    FStar_SMTEncoding_Term.Assume
                                                                    uu____14586) in
                                                                  (arg_decls,
                                                                    [typing_inversion;
                                                                    subterm_ordering])))
                                                    | uu____14617 ->
                                                        ((let uu____14619 =
                                                            let uu____14620 =
                                                              FStar_Syntax_Print.lid_to_string
                                                                d in
                                                            let uu____14621 =
                                                              FStar_Syntax_Print.term_to_string
                                                                head1 in
                                                            FStar_Util.format2
                                                              "Constructor %s builds an unexpected type %s\n"
                                                              uu____14620
                                                              uu____14621 in
                                                          FStar_Errors.warn
                                                            se.FStar_Syntax_Syntax.sigrng
                                                            uu____14619);
                                                         ([], []))) in
                                             let uu____14624 = encode_elim () in
                                             (match uu____14624 with
                                              | (decls2,elim) ->
                                                  let g =
                                                    let uu____14636 =
                                                      let uu____14638 =
                                                        let uu____14640 =
                                                          let uu____14642 =
                                                            let uu____14644 =
                                                              let uu____14645
                                                                =
                                                                let uu____14651
                                                                  =
                                                                  let uu____14653
                                                                    =
                                                                    let uu____14654
                                                                    =
                                                                    FStar_Syntax_Print.lid_to_string
                                                                    d in
                                                                    FStar_Util.format1
                                                                    "data constructor proxy: %s"
                                                                    uu____14654 in
                                                                  Some
                                                                    uu____14653 in
                                                                (ddtok, [],
                                                                  FStar_SMTEncoding_Term.Term_sort,
                                                                  uu____14651) in
                                                              FStar_SMTEncoding_Term.DeclFun
                                                                uu____14645 in
                                                            [uu____14644] in
                                                          let uu____14657 =
                                                            let uu____14659 =
                                                              let uu____14661
                                                                =
                                                                let uu____14663
                                                                  =
                                                                  let uu____14665
                                                                    =
                                                                    let uu____14667
                                                                    =
                                                                    let uu____14669
                                                                    =
                                                                    let uu____14670
                                                                    =
                                                                    let uu____14674
                                                                    =
                                                                    let uu____14675
                                                                    =
                                                                    let uu____14681
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (app,
                                                                    dapp) in
                                                                    ([[app]],
                                                                    vars,
                                                                    uu____14681) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____14675 in
                                                                    (uu____14674,
                                                                    (Some
                                                                    "equality for proxy"),
                                                                    (Prims.strcat
                                                                    "equality_tok_"
                                                                    ddtok)) in
                                                                    FStar_SMTEncoding_Term.Assume
                                                                    uu____14670 in
                                                                    let uu____14688
                                                                    =
                                                                    let uu____14690
                                                                    =
                                                                    let uu____14691
                                                                    =
                                                                    let uu____14695
                                                                    =
                                                                    let uu____14696
                                                                    =
                                                                    let uu____14702
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    vars' in
                                                                    let uu____14708
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    (guard',
                                                                    ty_pred') in
                                                                    ([
                                                                    [ty_pred']],
                                                                    uu____14702,
                                                                    uu____14708) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____14696 in
                                                                    (uu____14695,
                                                                    (Some
                                                                    "data constructor typing intro"),
                                                                    (Prims.strcat
                                                                    "data_typing_intro_"
                                                                    ddtok)) in
                                                                    FStar_SMTEncoding_Term.Assume
                                                                    uu____14691 in
                                                                    [uu____14690] in
                                                                    uu____14669
                                                                    ::
                                                                    uu____14688 in
                                                                    (FStar_SMTEncoding_Term.Assume
                                                                    (tok_typing1,
                                                                    (Some
                                                                    "typing for data constructor proxy"),
                                                                    (Prims.strcat
                                                                    "typing_tok_"
                                                                    ddtok)))
                                                                    ::
                                                                    uu____14667 in
                                                                  FStar_List.append
                                                                    uu____14665
                                                                    elim in
                                                                FStar_List.append
                                                                  decls_pred
                                                                  uu____14663 in
                                                              FStar_List.append
                                                                decls_formals
                                                                uu____14661 in
                                                            FStar_List.append
                                                              proxy_fresh
                                                              uu____14659 in
                                                          FStar_List.append
                                                            uu____14642
                                                            uu____14657 in
                                                        FStar_List.append
                                                          decls3 uu____14640 in
                                                      FStar_List.append
                                                        decls2 uu____14638 in
                                                    FStar_List.append
                                                      binder_decls
                                                      uu____14636 in
                                                  ((FStar_List.append
                                                      datacons g), env1)))))))))
and encode_signature:
  env_t ->
    FStar_Syntax_Syntax.sigelt Prims.list ->
      (FStar_SMTEncoding_Term.decl Prims.list* env_t)
  =
  fun env  ->
    fun ses  ->
      FStar_All.pipe_right ses
        (FStar_List.fold_left
           (fun uu____14729  ->
              fun se  ->
                match uu____14729 with
                | (g,env1) ->
                    let uu____14741 = encode_sigelt env1 se in
                    (match uu____14741 with
                     | (g',env2) -> ((FStar_List.append g g'), env2)))
           ([], env))
let encode_env_bindings:
  env_t ->
    FStar_TypeChecker_Env.binding Prims.list ->
      (FStar_SMTEncoding_Term.decls_t* env_t)
  =
  fun env  ->
    fun bindings  ->
      let encode_binding b uu____14777 =
        match uu____14777 with
        | (i,decls,env1) ->
            (match b with
             | FStar_TypeChecker_Env.Binding_univ uu____14795 ->
                 ((i + (Prims.parse_int "1")), [], env1)
             | FStar_TypeChecker_Env.Binding_var x ->
                 let t1 =
                   FStar_TypeChecker_Normalize.normalize
                     [FStar_TypeChecker_Normalize.Beta;
                     FStar_TypeChecker_Normalize.Eager_unfolding;
                     FStar_TypeChecker_Normalize.Simplify;
                     FStar_TypeChecker_Normalize.EraseUniverses] env1.tcenv
                     x.FStar_Syntax_Syntax.sort in
                 ((let uu____14800 =
                     FStar_All.pipe_left
                       (FStar_TypeChecker_Env.debug env1.tcenv)
                       (FStar_Options.Other "SMTEncoding") in
                   if uu____14800
                   then
                     let uu____14801 = FStar_Syntax_Print.bv_to_string x in
                     let uu____14802 =
                       FStar_Syntax_Print.term_to_string
                         x.FStar_Syntax_Syntax.sort in
                     let uu____14803 = FStar_Syntax_Print.term_to_string t1 in
                     FStar_Util.print3 "Normalized %s : %s to %s\n"
                       uu____14801 uu____14802 uu____14803
                   else ());
                  (let uu____14805 = encode_term t1 env1 in
                   match uu____14805 with
                   | (t,decls') ->
                       let t_hash = FStar_SMTEncoding_Term.hash_of_term t in
                       let uu____14815 =
                         let uu____14819 =
                           let uu____14820 =
                             let uu____14821 =
                               FStar_Util.digest_of_string t_hash in
                             Prims.strcat uu____14821
                               (Prims.strcat "_" (Prims.string_of_int i)) in
                           Prims.strcat "x_" uu____14820 in
                         new_term_constant_from_string env1 x uu____14819 in
                       (match uu____14815 with
                        | (xxsym,xx,env') ->
                            let t2 =
                              FStar_SMTEncoding_Term.mk_HasTypeWithFuel None
                                xx t in
                            let caption =
                              let uu____14832 = FStar_Options.log_queries () in
                              if uu____14832
                              then
                                let uu____14834 =
                                  let uu____14835 =
                                    FStar_Syntax_Print.bv_to_string x in
                                  let uu____14836 =
                                    FStar_Syntax_Print.term_to_string
                                      x.FStar_Syntax_Syntax.sort in
                                  let uu____14837 =
                                    FStar_Syntax_Print.term_to_string t1 in
                                  FStar_Util.format3 "%s : %s (%s)"
                                    uu____14835 uu____14836 uu____14837 in
                                Some uu____14834
                              else None in
                            let ax =
                              let a_name = Prims.strcat "binder_" xxsym in
                              FStar_SMTEncoding_Term.Assume
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
             | FStar_TypeChecker_Env.Binding_lid (x,(uu____14848,t)) ->
                 let t_norm = whnf env1 t in
                 let fv =
                   FStar_Syntax_Syntax.lid_as_fv x
                     FStar_Syntax_Syntax.Delta_constant None in
                 let uu____14857 = encode_free_var env1 fv t t_norm [] in
                 (match uu____14857 with
                  | (g,env') ->
                      ((i + (Prims.parse_int "1")),
                        (FStar_List.append decls g), env'))
             | FStar_TypeChecker_Env.Binding_sig_inst (_,se,_)
               |FStar_TypeChecker_Env.Binding_sig (_,se) ->
                 let uu____14876 = encode_sigelt env1 se in
                 (match uu____14876 with
                  | (g,env') ->
                      ((i + (Prims.parse_int "1")),
                        (FStar_List.append decls g), env'))) in
      let uu____14886 =
        FStar_List.fold_right encode_binding bindings
          ((Prims.parse_int "0"), [], env) in
      match uu____14886 with | (uu____14898,decls,env1) -> (decls, env1)
let encode_labels labs =
  let prefix1 =
    FStar_All.pipe_right labs
      (FStar_List.map
         (fun uu____14943  ->
            match uu____14943 with
            | (l,uu____14950,uu____14951) ->
                FStar_SMTEncoding_Term.DeclFun
                  ((Prims.fst l), [], FStar_SMTEncoding_Term.Bool_sort, None))) in
  let suffix =
    FStar_All.pipe_right labs
      (FStar_List.collect
         (fun uu____14972  ->
            match uu____14972 with
            | (l,uu____14980,uu____14981) ->
                let uu____14986 =
                  FStar_All.pipe_left
                    (fun _0_39  -> FStar_SMTEncoding_Term.Echo _0_39)
                    (Prims.fst l) in
                let uu____14987 =
                  let uu____14989 =
                    let uu____14990 = FStar_SMTEncoding_Util.mkFreeV l in
                    FStar_SMTEncoding_Term.Eval uu____14990 in
                  [uu____14989] in
                uu____14986 :: uu____14987)) in
  (prefix1, suffix)
let last_env: env_t Prims.list FStar_ST.ref = FStar_Util.mk_ref []
let init_env: FStar_TypeChecker_Env.env -> Prims.unit =
  fun tcenv  ->
    let uu____15001 =
      let uu____15003 =
        let uu____15004 = FStar_Util.smap_create (Prims.parse_int "100") in
        let uu____15016 =
          let uu____15017 = FStar_TypeChecker_Env.current_module tcenv in
          FStar_All.pipe_right uu____15017 FStar_Ident.string_of_lid in
        {
          bindings = [];
          depth = (Prims.parse_int "0");
          tcenv;
          warn = true;
          cache = uu____15004;
          nolabels = false;
          use_zfuel_name = false;
          encode_non_total_function_typ = true;
          current_module_name = uu____15016
        } in
      [uu____15003] in
    FStar_ST.write last_env uu____15001
let get_env: FStar_Ident.lident -> FStar_TypeChecker_Env.env -> env_t =
  fun cmn  ->
    fun tcenv  ->
      let uu____15027 = FStar_ST.read last_env in
      match uu____15027 with
      | [] -> failwith "No env; call init first!"
      | e::uu____15033 ->
          let uu___169_15035 = e in
          let uu____15036 = FStar_Ident.string_of_lid cmn in
          {
            bindings = (uu___169_15035.bindings);
            depth = (uu___169_15035.depth);
            tcenv;
            warn = (uu___169_15035.warn);
            cache = (uu___169_15035.cache);
            nolabels = (uu___169_15035.nolabels);
            use_zfuel_name = (uu___169_15035.use_zfuel_name);
            encode_non_total_function_typ =
              (uu___169_15035.encode_non_total_function_typ);
            current_module_name = uu____15036
          }
let set_env: env_t -> Prims.unit =
  fun env  ->
    let uu____15040 = FStar_ST.read last_env in
    match uu____15040 with
    | [] -> failwith "Empty env stack"
    | uu____15045::tl1 -> FStar_ST.write last_env (env :: tl1)
let push_env: Prims.unit -> Prims.unit =
  fun uu____15053  ->
    let uu____15054 = FStar_ST.read last_env in
    match uu____15054 with
    | [] -> failwith "Empty env stack"
    | hd1::tl1 ->
        let refs = FStar_Util.smap_copy hd1.cache in
        let top =
          let uu___170_15075 = hd1 in
          {
            bindings = (uu___170_15075.bindings);
            depth = (uu___170_15075.depth);
            tcenv = (uu___170_15075.tcenv);
            warn = (uu___170_15075.warn);
            cache = refs;
            nolabels = (uu___170_15075.nolabels);
            use_zfuel_name = (uu___170_15075.use_zfuel_name);
            encode_non_total_function_typ =
              (uu___170_15075.encode_non_total_function_typ);
            current_module_name = (uu___170_15075.current_module_name)
          } in
        FStar_ST.write last_env (top :: hd1 :: tl1)
let pop_env: Prims.unit -> Prims.unit =
  fun uu____15081  ->
    let uu____15082 = FStar_ST.read last_env in
    match uu____15082 with
    | [] -> failwith "Popping an empty stack"
    | uu____15087::tl1 -> FStar_ST.write last_env tl1
let mark_env: Prims.unit -> Prims.unit = fun uu____15095  -> push_env ()
let reset_mark_env: Prims.unit -> Prims.unit = fun uu____15098  -> pop_env ()
let commit_mark_env: Prims.unit -> Prims.unit =
  fun uu____15101  ->
    let uu____15102 = FStar_ST.read last_env in
    match uu____15102 with
    | hd1::uu____15108::tl1 -> FStar_ST.write last_env (hd1 :: tl1)
    | uu____15114 -> failwith "Impossible"
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
let encode_sig:
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.sigelt -> Prims.unit =
  fun tcenv  ->
    fun se  ->
      let caption decls =
        let uu____15159 = FStar_Options.log_queries () in
        if uu____15159
        then
          let uu____15161 =
            let uu____15162 =
              let uu____15163 =
                let uu____15164 =
                  FStar_All.pipe_right (FStar_Syntax_Util.lids_of_sigelt se)
                    (FStar_List.map FStar_Syntax_Print.lid_to_string) in
                FStar_All.pipe_right uu____15164 (FStar_String.concat ", ") in
              Prims.strcat "encoding sigelt " uu____15163 in
            FStar_SMTEncoding_Term.Caption uu____15162 in
          uu____15161 :: decls
        else decls in
      let env =
        let uu____15171 = FStar_TypeChecker_Env.current_module tcenv in
        get_env uu____15171 tcenv in
      let uu____15172 = encode_sigelt env se in
      match uu____15172 with
      | (decls,env1) ->
          (set_env env1;
           (let uu____15178 = caption decls in
            FStar_SMTEncoding_Z3.giveZ3 uu____15178))
let encode_modul:
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.modul -> Prims.unit =
  fun tcenv  ->
    fun modul  ->
      let name =
        FStar_Util.format2 "%s %s"
          (if modul.FStar_Syntax_Syntax.is_interface
           then "interface"
           else "module") (modul.FStar_Syntax_Syntax.name).FStar_Ident.str in
      (let uu____15189 = FStar_TypeChecker_Env.debug tcenv FStar_Options.Low in
       if uu____15189
       then
         let uu____15190 =
           FStar_All.pipe_right
             (FStar_List.length modul.FStar_Syntax_Syntax.exports)
             Prims.string_of_int in
         FStar_Util.print2
           "+++++++++++Encoding externals for %s ... %s exports\n" name
           uu____15190
       else ());
      (let env = get_env modul.FStar_Syntax_Syntax.name tcenv in
       let uu____15195 =
         encode_signature
           (let uu___171_15199 = env in
            {
              bindings = (uu___171_15199.bindings);
              depth = (uu___171_15199.depth);
              tcenv = (uu___171_15199.tcenv);
              warn = false;
              cache = (uu___171_15199.cache);
              nolabels = (uu___171_15199.nolabels);
              use_zfuel_name = (uu___171_15199.use_zfuel_name);
              encode_non_total_function_typ =
                (uu___171_15199.encode_non_total_function_typ);
              current_module_name = (uu___171_15199.current_module_name)
            }) modul.FStar_Syntax_Syntax.exports in
       match uu____15195 with
       | (decls,env1) ->
           let caption decls1 =
             let uu____15211 = FStar_Options.log_queries () in
             if uu____15211
             then
               let msg = Prims.strcat "Externals for " name in
               FStar_List.append ((FStar_SMTEncoding_Term.Caption msg) ::
                 decls1)
                 [FStar_SMTEncoding_Term.Caption (Prims.strcat "End " msg)]
             else decls1 in
           (set_env
              (let uu___172_15216 = env1 in
               {
                 bindings = (uu___172_15216.bindings);
                 depth = (uu___172_15216.depth);
                 tcenv = (uu___172_15216.tcenv);
                 warn = true;
                 cache = (uu___172_15216.cache);
                 nolabels = (uu___172_15216.nolabels);
                 use_zfuel_name = (uu___172_15216.use_zfuel_name);
                 encode_non_total_function_typ =
                   (uu___172_15216.encode_non_total_function_typ);
                 current_module_name = (uu___172_15216.current_module_name)
               });
            (let uu____15218 =
               FStar_TypeChecker_Env.debug tcenv FStar_Options.Low in
             if uu____15218
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
        (let uu____15253 =
           let uu____15254 = FStar_TypeChecker_Env.current_module tcenv in
           uu____15254.FStar_Ident.str in
         FStar_SMTEncoding_Z3.query_logging.FStar_SMTEncoding_Z3.set_module_name
           uu____15253);
        (let env =
           let uu____15256 = FStar_TypeChecker_Env.current_module tcenv in
           get_env uu____15256 tcenv in
         let bindings =
           FStar_TypeChecker_Env.fold_env tcenv
             (fun bs  -> fun b  -> b :: bs) [] in
         let uu____15263 =
           let rec aux bindings1 =
             match bindings1 with
             | (FStar_TypeChecker_Env.Binding_var x)::rest ->
                 let uu____15284 = aux rest in
                 (match uu____15284 with
                  | (out,rest1) ->
                      let t =
                        let uu____15302 =
                          FStar_Syntax_Util.destruct_typ_as_formula
                            x.FStar_Syntax_Syntax.sort in
                        match uu____15302 with
                        | Some uu____15306 ->
                            let uu____15307 =
                              FStar_Syntax_Syntax.new_bv None
                                FStar_TypeChecker_Common.t_unit in
                            FStar_Syntax_Util.refine uu____15307
                              x.FStar_Syntax_Syntax.sort
                        | uu____15308 -> x.FStar_Syntax_Syntax.sort in
                      let t1 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Normalize.Eager_unfolding;
                          FStar_TypeChecker_Normalize.Beta;
                          FStar_TypeChecker_Normalize.Simplify;
                          FStar_TypeChecker_Normalize.EraseUniverses]
                          env.tcenv t in
                      let uu____15311 =
                        let uu____15313 =
                          FStar_Syntax_Syntax.mk_binder
                            (let uu___173_15314 = x in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___173_15314.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___173_15314.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = t1
                             }) in
                        uu____15313 :: out in
                      (uu____15311, rest1))
             | uu____15317 -> ([], bindings1) in
           let uu____15321 = aux bindings in
           match uu____15321 with
           | (closing,bindings1) ->
               let uu____15335 =
                 FStar_Syntax_Util.close_forall_no_univs
                   (FStar_List.rev closing) q in
               (uu____15335, bindings1) in
         match uu____15263 with
         | (q1,bindings1) ->
             let uu____15348 =
               let uu____15351 =
                 FStar_List.filter
                   (fun uu___140_15353  ->
                      match uu___140_15353 with
                      | FStar_TypeChecker_Env.Binding_sig uu____15354 ->
                          false
                      | uu____15358 -> true) bindings1 in
               encode_env_bindings env uu____15351 in
             (match uu____15348 with
              | (env_decls,env1) ->
                  ((let uu____15369 =
                      ((FStar_TypeChecker_Env.debug tcenv FStar_Options.Low)
                         ||
                         (FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug tcenv)
                            (FStar_Options.Other "SMTEncoding")))
                        ||
                        (FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug tcenv)
                           (FStar_Options.Other "SMTQuery")) in
                    if uu____15369
                    then
                      let uu____15370 = FStar_Syntax_Print.term_to_string q1 in
                      FStar_Util.print1 "Encoding query formula: %s\n"
                        uu____15370
                    else ());
                   (let uu____15372 = encode_formula q1 env1 in
                    match uu____15372 with
                    | (phi,qdecls) ->
                        let uu____15384 =
                          let uu____15387 =
                            FStar_TypeChecker_Env.get_range tcenv in
                          FStar_SMTEncoding_ErrorReporting.label_goals
                            use_env_msg uu____15387 phi in
                        (match uu____15384 with
                         | (labels,phi1) ->
                             let uu____15397 = encode_labels labels in
                             (match uu____15397 with
                              | (label_prefix,label_suffix) ->
                                  let query_prelude =
                                    FStar_List.append env_decls
                                      (FStar_List.append label_prefix qdecls) in
                                  let qry =
                                    let uu____15418 =
                                      let uu____15422 =
                                        FStar_SMTEncoding_Util.mkNot phi1 in
                                      let uu____15423 =
                                        varops.mk_unique "@query" in
                                      (uu____15422, (Some "query"),
                                        uu____15423) in
                                    FStar_SMTEncoding_Term.Assume uu____15418 in
                                  let suffix =
                                    FStar_List.append label_suffix
                                      [FStar_SMTEncoding_Term.Echo "Done!"] in
                                  (query_prelude, labels, qry, suffix)))))))
let is_trivial:
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.typ -> Prims.bool =
  fun tcenv  ->
    fun q  ->
      let env =
        let uu____15436 = FStar_TypeChecker_Env.current_module tcenv in
        get_env uu____15436 tcenv in
      FStar_SMTEncoding_Z3.push "query";
      (let uu____15438 = encode_formula q env in
       match uu____15438 with
       | (f,uu____15442) ->
           (FStar_SMTEncoding_Z3.pop "query";
            (match f.FStar_SMTEncoding_Term.tm with
             | FStar_SMTEncoding_Term.App
                 (FStar_SMTEncoding_Term.TrueOp ,uu____15444) -> true
             | uu____15447 -> false)))