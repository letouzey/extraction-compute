/* Borrowed from OCaml's byterun/terminfo.c, and specialized to the NATIVE_CODE case */

#include "caml/mlvalues.h"
#include "caml/fail.h"

#define Bad_term (Val_int(1))

CAMLexport value caml_terminfo_setup (value vchan)
{
  return Bad_term;
}

CAMLexport value caml_terminfo_backup (value lines)
{
  caml_invalid_argument("Terminfo.backup");
  return Val_unit;
}

CAMLexport value caml_terminfo_standout (value start)
{
  caml_invalid_argument("Terminfo.standout");
  return Val_unit;
}

CAMLexport value caml_terminfo_resume (value lines)
{
  caml_invalid_argument("Terminfo.resume");
  return Val_unit;
}
