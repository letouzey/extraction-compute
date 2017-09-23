(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2012     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Extraction_plugin

(** From Lambda code to Bytecode *)

let reset_compiler () =
  Translobj.reset_labels ();
  Translmod.primitive_declarations := [];
  Env.reset_cache ()

(** Compile a standalone lambda expression to a cmo.
    This lambda must be a block with all the toplevel definitions.
    Code borrowed from drivers/compile.ml *)

let compile_lambda ?(debug=false) modulename lam =
  let mod_id = Ident.create_persistent modulename in
  let lambda = Lambda.Lprim (Lambda.Psetglobal mod_id,[lam]) in
  if debug then Printlambda.lambda Format.std_formatter lambda;
  if debug then Printf.printf "=======\n%!";
  let lambda' = Simplif.simplify_lambda lambda in
  if debug then Printlambda.lambda Format.std_formatter lambda';
  let bytecode = Bytegen.compile_implementation modulename lambda' in
  if debug then Printinstr.instrlist Format.std_formatter bytecode;
  let path = modulename^".cmo" in
  let oc = open_out_bin (modulename^".cmo") in
  let () = Emitcode.to_file oc modulename path bytecode in
  close_out oc


(** Compile, link and execute a lambda phrase.
    Code borrowed from toplevel/toploop.ml *)

let eval_lambda ?(debug=false) lam =
  let ppf = Format.std_formatter in
  if debug then Format.fprintf ppf "\n====== RAW LAMBDA ======\n\n";
  if debug then Printlambda.lambda ppf lam;
  if debug then Format.fprintf ppf "\n\n====== SIMPLIFIED LAMBDA ======\n";
  let slam = Simplif.simplify_lambda lam in
  if debug then Printlambda.lambda ppf slam;
  let (init_code, fun_code) = Bytegen.compile_phrase slam in
  if debug then Format.fprintf ppf "\n\n====== BYTECODE ======\n";
  if debug then Printinstr.instrlist ppf fun_code;
  if debug then Format.fprintf ppf "\n====== RESULT ======\n\n";
  let (code, code_size, reloc) = Emitcode.to_memory init_code fun_code in
  let can_free = (fun_code = []) in
  let initial_symtable = Symtable.current_state() in
  Symtable.patch_object code reloc;
  Symtable.check_global_initialized reloc;
  Symtable.update_global_table();
  try
    let retval = (Meta.reify_bytecode code code_size) () in
    if can_free then begin
      Meta.static_release_bytecode code code_size;
      Meta.static_free code;
    end;
    retval
  with x ->
    if can_free then begin
      Meta.static_release_bytecode code code_size;
      Meta.static_free code;
    end;
    Symtable.restore_state initial_symtable;
    raise x


let make_cmo ?(debug=false) modulename (structure:Miniml.ml_decl list) =
  reset_compiler ();
  compile_lambda ~debug modulename
    (Olambda.lambda_for_compunit structure)

let direct_eval ?(debug=false) (s:Miniml.ml_decl list) ot =
  eval_lambda ~debug (Olambda.lambda_for_eval s ot)

(* API sucks *)

let all_no_fail_flags = Pretyping.({
  use_typeclasses = true;
  solve_unification_constraints = true;
  use_hook = None;
  fail_evar = false;
  expand_evars = true })

let compute_constr ?(debug=false) env sigma c =
  try
    let ty = Retyping.get_type_of env sigma c in
    let s,mlt,mlty = Extract_env.structure_for_compute (EConstr.Unsafe.to_constr c) in
    let gterm = Olambda.reconstruct mlty (direct_eval ~debug s (Some mlt))
    in
    Pretyping.understand
      ~flags:all_no_fail_flags
      ~expected_type:(Pretyping.OfType ty)
      env sigma gterm
  with Olambda.CannotReconstruct r ->
    CErrors.user_err (Pp.str ("Cannot reconstruct a Coq value : " ^
                  Olambda.cannot_reconstruct_msg r))

let compute_constr_expr ?(debug=false) cexpr =
  let sigma,env = Pfedit.get_current_context () in
  let c,_ = Constrintern.interp_constr env sigma cexpr in
  let res,_ = compute_constr ~debug env sigma (EConstr.of_constr c) in
  Feedback.msg_notice (Printer.pr_lconstr_env env sigma res)
