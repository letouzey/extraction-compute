(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2012     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

let debug_compute = ref false

let _ = Goptions.declare_bool_option
  {Goptions.optdepr = false;
   Goptions.optname = "Verbose Extraction Compute";
   Goptions.optkey = ["Verbose";"Extraction";"Compute"];
   Goptions.optread = (fun () -> !debug_compute);
   Goptions.optwrite = ((:=) debug_compute) }

open Stdarg

VERNAC COMMAND EXTEND ExtractionCompute CLASSIFIED AS QUERY
| [ "Extraction" "Compute" constr(c) ]
  -> [ Olambda_byte.compute_constr_expr ~debug:(!debug_compute) c ]
END
