
open Prims

type ('env, 'modul) interactive_tc =
{pop : 'env  ->  Prims.string  ->  Prims.unit; push : 'env  ->  Prims.bool  ->  Prims.bool  ->  Prims.string  ->  'env; mark : 'env  ->  'env; reset_mark : 'env  ->  'env; commit_mark : 'env  ->  'env; check_frag : 'env  ->  'modul  ->  FStar_Parser_ParseIt.input_frag  ->  ('modul * 'env * Prims.int) Prims.option; report_fail : Prims.unit  ->  Prims.unit; tc_prims : Prims.unit  ->  'env; tc_one_file : Prims.string Prims.list  ->  'env  ->  ((Prims.string Prims.option * Prims.string) * 'env * 'modul * Prims.string Prims.list); cleanup : 'env  ->  Prims.unit}


let is_Mkinteractive_tc = (Obj.magic ((fun _ -> (failwith "Not yet implemented:is_Mkinteractive_tc"))))


type input_chunks =
| Push of (Prims.bool * Prims.int * Prims.int)
| Pop of Prims.string
| Code of (Prims.string * (Prims.string * Prims.string))


let is_Push = (fun _discr_ -> (match (_discr_) with
| Push (_) -> begin
true
end
| _ -> begin
false
end))


let is_Pop = (fun _discr_ -> (match (_discr_) with
| Pop (_) -> begin
true
end
| _ -> begin
false
end))


let is_Code = (fun _discr_ -> (match (_discr_) with
| Code (_) -> begin
true
end
| _ -> begin
false
end))


let ___Push____0 = (fun projectee -> (match (projectee) with
| Push (_96_16) -> begin
_96_16
end))


let ___Pop____0 = (fun projectee -> (match (projectee) with
| Pop (_96_19) -> begin
_96_19
end))


let ___Code____0 = (fun projectee -> (match (projectee) with
| Code (_96_22) -> begin
_96_22
end))


type ('env, 'modul) stack =
('env * 'modul) Prims.list


type interactive_state =
{chunk : FStar_Util.string_builder; stdin : FStar_Util.stream_reader Prims.option FStar_ST.ref; buffer : input_chunks Prims.list FStar_ST.ref; log : FStar_Util.file_handle Prims.option FStar_ST.ref}


let is_Mkinteractive_state : interactive_state  ->  Prims.bool = (Obj.magic ((fun _ -> (failwith "Not yet implemented:is_Mkinteractive_state"))))


let the_interactive_state : interactive_state = (let _197_194 = (FStar_Util.new_string_builder ())
in (let _197_193 = (FStar_ST.alloc None)
in (let _197_192 = (FStar_ST.alloc [])
in (let _197_191 = (FStar_ST.alloc None)
in {chunk = _197_194; stdin = _197_193; buffer = _197_192; log = _197_191}))))


let rec read_chunk : Prims.unit  ->  input_chunks = (fun _96_30 -> (match (()) with
| () -> begin
(

let s = the_interactive_state
in (

let log = if (FStar_Options.debug_any ()) then begin
(

let transcript = (match ((FStar_ST.read s.log)) with
| Some (transcript) -> begin
transcript
end
| None -> begin
(

let transcript = (FStar_Util.open_file_for_writing "transcript")
in (

let _96_36 = (FStar_ST.op_Colon_Equals s.log (Some (transcript)))
in transcript))
end)
in (fun line -> (

let _96_40 = (FStar_Util.append_to_file transcript line)
in (FStar_Util.flush_file transcript))))
end else begin
(fun _96_42 -> ())
end
in (

let stdin = (match ((FStar_ST.read s.stdin)) with
| Some (i) -> begin
i
end
| None -> begin
(

let i = (FStar_Util.open_stdin ())
in (

let _96_49 = (FStar_ST.op_Colon_Equals s.stdin (Some (i)))
in i))
end)
in (

let line = (match ((FStar_Util.read_line stdin)) with
| None -> begin
(FStar_All.exit (Prims.parse_int "0"))
end
| Some (l) -> begin
l
end)
in (

let _96_56 = (log line)
in (

let l = (FStar_Util.trim_string line)
in if (FStar_Util.starts_with l "#end") then begin
(

let responses = (match ((FStar_Util.split l " ")) with
| (_96_62)::(ok)::(fail)::[] -> begin
((ok), (fail))
end
| _96_65 -> begin
(("ok"), ("fail"))
end)
in (

let str = (FStar_Util.string_of_string_builder s.chunk)
in (

let _96_68 = (FStar_Util.clear_string_builder s.chunk)
in Code (((str), (responses))))))
end else begin
if (FStar_Util.starts_with l "#pop") then begin
(

let _96_70 = (FStar_Util.clear_string_builder s.chunk)
in Pop (l))
end else begin
if (FStar_Util.starts_with l "#push") then begin
(

let _96_72 = (FStar_Util.clear_string_builder s.chunk)
in (

let lc_lax = (let _197_202 = (FStar_Util.substring_from l (FStar_String.length "#push"))
in (FStar_Util.trim_string _197_202))
in (

let lc = (match ((FStar_Util.split lc_lax " ")) with
| (l)::(c)::("#lax")::[] -> begin
(let _197_204 = (FStar_Util.int_of_string l)
in (let _197_203 = (FStar_Util.int_of_string c)
in ((true), (_197_204), (_197_203))))
end
| (l)::(c)::[] -> begin
(let _197_206 = (FStar_Util.int_of_string l)
in (let _197_205 = (FStar_Util.int_of_string c)
in ((false), (_197_206), (_197_205))))
end
| _96_83 -> begin
(

let _96_84 = (FStar_Util.print_warning (Prims.strcat "Error locations may be wrong, unrecognized string after #push: " lc_lax))
in ((false), ((Prims.parse_int "1")), ((Prims.parse_int "0"))))
end)
in Push (lc))))
end else begin
if (l = "#finish") then begin
(FStar_All.exit (Prims.parse_int "0"))
end else begin
(

let _96_87 = (FStar_Util.string_builder_append s.chunk line)
in (

let _96_89 = (FStar_Util.string_builder_append s.chunk "\n")
in (read_chunk ())))
end
end
end
end))))))
end))


let shift_chunk : Prims.unit  ->  input_chunks = (fun _96_91 -> (match (()) with
| () -> begin
(

let s = the_interactive_state
in (match ((FStar_ST.read s.buffer)) with
| [] -> begin
(read_chunk ())
end
| (chunk)::chunks -> begin
(

let _96_97 = (FStar_ST.op_Colon_Equals s.buffer chunks)
in chunk)
end))
end))


let fill_buffer : Prims.unit  ->  Prims.unit = (fun _96_99 -> (match (()) with
| () -> begin
(

let s = the_interactive_state
in (let _197_214 = (let _197_213 = (FStar_ST.read s.buffer)
in (let _197_212 = (let _197_211 = (read_chunk ())
in (_197_211)::[])
in (FStar_List.append _197_213 _197_212)))
in (FStar_ST.op_Colon_Equals s.buffer _197_214)))
end))


let deps_of_our_file : Prims.string  ->  Prims.string Prims.list = (fun filename -> (

let deps = (FStar_Dependencies.find_deps_if_needed FStar_Parser_Dep.VerifyFigureItOut ((filename)::[]))
in (FStar_List.filter (fun x -> ((FStar_Parser_Dep.lowercase_module_name x) <> (FStar_Parser_Dep.lowercase_module_name filename))) deps)))


type m_timestamps =
(Prims.string Prims.option * Prims.string * FStar_Util.time Prims.option * FStar_Util.time) Prims.list


let interactive_mode = (fun filename initial_mod tc -> (

let _96_109 = if (let _197_221 = (FStar_Options.codegen ())
in (FStar_Option.isSome _197_221)) then begin
(FStar_Util.print_warning "code-generation is not supported in interactive mode, ignoring the codegen flag")
end else begin
()
end
in (

let rec tc_deps = (fun m stack env remaining ts -> (match (remaining) with
| [] -> begin
((stack), (env), (ts))
end
| _96_119 -> begin
(

let stack = (((env), (m)))::stack
in (

let env = (let _197_232 = (FStar_Options.lax ())
in (tc.push env _197_232 true "typecheck_modul"))
in (

let _96_128 = (tc.tc_one_file remaining env)
in (match (_96_128) with
| ((intf, impl), env, modl, remaining) -> begin
(

let _96_136 = (

let intf_t = (match (intf) with
| Some (intf) -> begin
(let _197_233 = (FStar_Util.get_file_last_modification_time intf)
in Some (_197_233))
end
| None -> begin
None
end)
in (

let impl_t = (FStar_Util.get_file_last_modification_time impl)
in ((intf_t), (impl_t))))
in (match (_96_136) with
| (intf_t, impl_t) -> begin
(tc_deps m stack env remaining ((((intf), (impl), (intf_t), (impl_t)))::ts))
end))
end))))
end))
in (

let update_deps = (fun m stk env ts -> (

let is_stale = (fun intf impl intf_t impl_t -> (

let impl_mt = (FStar_Util.get_file_last_modification_time impl)
in ((FStar_Util.is_before impl_t impl_mt) || (match (((intf), (intf_t))) with
| (Some (intf), Some (intf_t)) -> begin
(

let intf_mt = (FStar_Util.get_file_last_modification_time intf)
in (FStar_Util.is_before intf_t intf_mt))
end
| (None, None) -> begin
false
end
| (_96_158, _96_160) -> begin
(failwith "Impossible, if the interface is None, the timestamp entry should also be None")
end))))
in (

let rec iterate = (fun depnames st env' ts good_stack good_ts -> (

let match_dep = (fun depnames intf impl -> (match (intf) with
| None -> begin
(match (depnames) with
| (dep)::depnames' -> begin
if (dep = impl) then begin
((true), (depnames'))
end else begin
((false), (depnames))
end
end
| _96_178 -> begin
((false), (depnames))
end)
end
| Some (intf) -> begin
(match (depnames) with
| (depintf)::(dep)::depnames' -> begin
if ((depintf = intf) && (dep = impl)) then begin
((true), (depnames'))
end else begin
((false), (depnames))
end
end
| _96_187 -> begin
((false), (depnames))
end)
end))
in (

let rec pop_tc_and_stack = (fun env stack ts -> (match (ts) with
| [] -> begin
env
end
| (_96_195)::ts -> begin
(

let _96_197 = (tc.pop env "")
in (

let _96_204 = (let _197_275 = (FStar_List.hd stack)
in (let _197_274 = (FStar_List.tl stack)
in ((_197_275), (_197_274))))
in (match (_96_204) with
| ((env, _96_201), stack) -> begin
(pop_tc_and_stack env stack ts)
end)))
end))
in (match (ts) with
| (ts_elt)::ts' -> begin
(

let _96_212 = ts_elt
in (match (_96_212) with
| (intf, impl, intf_t, impl_t) -> begin
(

let _96_215 = (match_dep depnames intf impl)
in (match (_96_215) with
| (b, depnames') -> begin
if ((not (b)) || (is_stale intf impl intf_t impl_t)) then begin
(

let env = (pop_tc_and_stack env' (FStar_List.rev_append st []) ts)
in (tc_deps m good_stack env depnames good_ts))
end else begin
(

let _96_219 = (let _197_277 = (FStar_List.hd st)
in (let _197_276 = (FStar_List.tl st)
in ((_197_277), (_197_276))))
in (match (_96_219) with
| (stack_elt, st') -> begin
(iterate depnames' st' env' ts' ((stack_elt)::good_stack) ((ts_elt)::good_ts))
end))
end
end))
end))
end
| [] -> begin
(tc_deps m good_stack env' depnames good_ts)
end))))
in (

let filenames = (deps_of_our_file filename)
in (iterate filenames (FStar_List.rev_append stk []) env (FStar_List.rev_append ts []) [] [])))))
in (

let rec go = (fun line_col stack curmod env ts -> (match ((shift_chunk ())) with
| Pop (msg) -> begin
(

let _96_230 = (tc.pop env msg)
in (

let _96_242 = (match (stack) with
| [] -> begin
(

let _96_233 = (FStar_Util.print_error "too many pops")
in (FStar_All.exit (Prims.parse_int "1")))
end
| (hd)::tl -> begin
((hd), (tl))
end)
in (match (_96_242) with
| ((env, curmod), stack) -> begin
(

let _96_243 = if ((FStar_List.length stack) = (FStar_List.length ts)) then begin
(tc.cleanup env)
end else begin
()
end
in (go line_col stack curmod env ts))
end)))
end
| Push (lax, l, c) -> begin
(

let _96_255 = if ((FStar_List.length stack) = (FStar_List.length ts)) then begin
(let _197_288 = (update_deps curmod stack env ts)
in ((true), (_197_288)))
end else begin
((false), (((stack), (env), (ts))))
end
in (match (_96_255) with
| (restore_cmd_line_options, (stack, env, ts)) -> begin
(

let stack = (((env), (curmod)))::stack
in (

let env = (tc.push env lax restore_cmd_line_options "#push")
in (go ((l), (c)) stack curmod env ts)))
end))
end
| Code (text, (ok, fail)) -> begin
(

let fail = (fun curmod env_mark -> (

let _96_267 = (tc.report_fail ())
in (

let _96_269 = (FStar_Util.print1 "%s\n" fail)
in (

let env = (tc.reset_mark env_mark)
in (go line_col stack curmod env ts)))))
in (

let env_mark = (tc.mark env)
in (

let frag = {FStar_Parser_ParseIt.frag_text = text; FStar_Parser_ParseIt.frag_line = (Prims.fst line_col); FStar_Parser_ParseIt.frag_col = (Prims.snd line_col)}
in (

let res = (tc.check_frag env_mark curmod frag)
in (match (res) with
| Some (curmod, env, n_errs) -> begin
if (n_errs = (Prims.parse_int "0")) then begin
(

let _96_280 = (FStar_Util.print1 "\n%s\n" ok)
in (

let env = (tc.commit_mark env)
in (go line_col stack curmod env ts)))
end else begin
(fail curmod env_mark)
end
end
| _96_284 -> begin
(fail curmod env_mark)
end)))))
end))
in (

let filenames = (deps_of_our_file filename)
in (

let env = (tc.tc_prims ())
in (

let _96_290 = (tc_deps initial_mod [] env filenames [])
in (match (_96_290) with
| (stack, env, ts) -> begin
if ((FStar_Options.universes ()) && ((FStar_Options.record_hints ()) || (FStar_Options.use_hints ()))) then begin
(let _197_295 = (let _197_293 = (FStar_Options.file_list ())
in (FStar_List.hd _197_293))
in (FStar_SMTEncoding_Solver.with_hints_db _197_295 (fun _96_291 -> (match (()) with
| () -> begin
(go (((Prims.parse_int "1")), ((Prims.parse_int "0"))) stack initial_mod env ts)
end))))
end else begin
(go (((Prims.parse_int "1")), ((Prims.parse_int "0"))) stack initial_mod env ts)
end
end)))))))))




