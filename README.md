Extraction Compute
==================

Pierre Letouzey, Oct 2017

### What ?

A reduction machinary for Coq terms done by going through the extraction
infrastructure, then running the obtained OCaml code (either native or
bytecode) and reimporting the result back to an Coq term, at least in
favorable situations (such as results in nat, bool or list of basic types).

### Status

Clearly, very experimental. See Caveats below.

### Caveats

Of course, this only concerns terms that are relevant for extraction,
for instance it won't work on a term of sort Prop, or on a type. Moreover
proof parts are discarded, so if the final result is supposed to still
contain a proof part it will be replaced by an hole (evar).

Another limitation: for the moment, the term reconstruction after reduction
is done by following the ML type generated by the extraction. So when
the Coq type is too complex and has no ML counterpart and become `Obj.t`
at extraction, the term reconstruction done by Extraction Compute will fail.

By the way, this reconstruction is done by rebuilding a `glob_constr`, then
leting Coq process it up to a `constr`. In particular, this allows to re-infer
type annotations (for instance in lists). But the type-checking time might
be non-negligible.

### Requirements

OCaml 4.02.* with compiler-libs. TODO: test and adapt for more recent OCaml

### How to build ?

First, compile a recent Coq:
 - at least 6cb18298 (2017-10-06) for the master branch of extraction-compute
 - at least 8.7+beta2 for the v8.7 branch of extraction-compute

Then:

```
export COQBIN=...
cd native && make
cd bytecode && make byte
```

### How to install ?

TODO

### How to use ?

```
Require ExtractionCompute.
Extraction Compute (1+1).
```

### Technical Remarks

Note that we build a native/compilerlibs.cmxs containing
ocamlcommon.cmxa and ocamloptcomp.cmxa. Since ocamlcommon.cma and
ocamlbytecomp.cma and ocamltoplevel.cma are already linked inside
coqtop.byte, we build an empty bytecode/compilerlibs.cma, just for
having the same `Declare ML Module` in ExtractionCompute.v.

For successful dynlink of this compilerlibs.cmxs, we had to provide
a dummy terminfo.o file (normally provided by libasmrun.a), see fake_terminfo.c

Other possible solutions (for the record):

  - Add ̀`-cclib -lasmrun_pic` to the compile line (this embed a correct terminfo.c)

  - Build a fat binary with coqkmtop :

```
coqmktop -opt -I +compiler-libs -thread ocamlcommon.cmxa ocamloptcomp.cmxa -o /tmp/bigcoq -coqlib ...
```
