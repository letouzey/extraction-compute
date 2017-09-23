
(** From Lambda code to Native code *)

(** Dynlink an OCaml's lambda term and run it *)
(** Many parts borrowed from opttoploop.ml *)

type res = Ok of Obj.t | Err of string
type evaluation_outcome = Result of Obj.t | Exception of exn

external ndl_run_toplevel: string -> string -> res
  = "caml_natdynlink_run_toplevel"
external ndl_loadsym: string -> Obj.t = "caml_natdynlink_loadsym"

let dll_run dll entry =
  match (try Result (Obj.magic (ndl_run_toplevel dll entry))
    with exn -> Exception exn)
  with
  | Exception _ as r -> r
  | Result r ->
        match Obj.magic r with
        | Ok x -> Result x
        | Err s -> failwith ("Opttoploop.dll_run " ^ s)

let ext_dll = ".so"
let ext_obj = ".o"

let phrase_name = "TOP"

let need_symbol sym =
  try ignore (ndl_loadsym sym); false
  with _ -> true

let eval_lambda ?(debug=false) lam =
  (* We build code that normally do not call other libs.
     Only exception : CamlinternalLazy referred in match
     compilation of lazyness. Hence we need a bit of load_path. *)
  Config.load_path := [Config.standard_library];
  Clflags.native_code := true;
  Compilenv.reset ?packname:None phrase_name;
  let size = 1 in (* TODO !! *)
  let ppf = Format.std_formatter in
  let slam = Simplif.simplify_lambda lam in
  if debug then Printlambda.lambda ppf slam;
  let dll = Filename.temp_file ("caml" ^ phrase_name) ext_dll in
  let fn = Filename.chop_extension dll in
  Asmgen.compile_implementation ~toplevel:need_symbol fn ppf (size, slam);
  Asmlink.call_linker_shared [fn ^ ext_obj] dll;
  Sys.remove (fn ^ ext_obj);
  let dll =
    if Filename.is_implicit dll
    then Filename.concat (Sys.getcwd ()) dll
    else dll in
  let res = dll_run dll phrase_name in
  (try Sys.remove dll with Sys_error _ -> ());
  (* note: under windows, cannot remove a loaded dll
     (should remember the handles, close them in at_exit, and then remove
     files) *)
  match res with
  | Result o -> o
  | Exception e -> raise e

open Extraction_plugin

let direct_eval ?(debug=false) (s:Miniml.ml_decl list) ot =
  eval_lambda ~debug (Olambda.lambda_for_eval s ot)

(* API sucks: *)
let all_no_fail_flags = Pretyping.({
  use_typeclasses = true;
  solve_unification_constraints = true;
  use_hook = None;
  fail_evar = false;
  expand_evars = true })

let compute_constr env sigma c =
  try
    let ty = Retyping.get_type_of env sigma c in
    let s,mlt,mlty = Extract_env.structure_for_compute (EConstr.Unsafe.to_constr c) in
    let gterm = Olambda.reconstruct mlty (direct_eval s (Some mlt)) in
    Pretyping.understand
      ~flags:all_no_fail_flags
      ~expected_type:(Pretyping.OfType ty)
      env sigma gterm
  with Olambda.CannotReconstruct r ->
    CErrors.user_err (Pp.str ("Cannot reconstruct a Coq value : " ^
                  Olambda.cannot_reconstruct_msg r))

let compute_constr_expr cexpr =
  let sigma,env = Pfedit.get_current_context () in
  let c,_ = Constrintern.interp_constr env sigma cexpr in
  let res,_ = compute_constr env sigma (EConstr.of_constr c) in
  Feedback.msg_notice (Printer.pr_lconstr_env env sigma res)
