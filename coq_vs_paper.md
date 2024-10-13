# Overview
- The definition of what is a logical effect handler (with concurrency) is found in `handler.v`
  under the name `iHandler`.
- `wpi` (with concurrency and masks) and associated generic proof rules are defined in `wpi.v`.
  * Many lemmata are proven by first establishing a maskless version with postfix `_emp_mask` and
    then lifting them to a masked version, which is the lemma statement we expose outwards.
  * `WpiSubsume` is `wpi_inH` and the `⊆` relation is controlled by the `inH` typeclass defined in
    `handler.v`.
- Every effect has a corresponding library in a file with corresponding name (except for `fail` and
  `threadpool`; see below) in the `src/` directory. Assuming the effect had name `effect`, we use the
  following naming conventions:
  * Its event type is called `eventE`.
  * Its logical effect handler is called `effectH`.
  * Its interpretation relation is called `effect_irel`.
  * Its interpretation function is called `effect_ifn`.
  * Its (interpretational) adequacy theorem is called `effect_adequacy` (or `effect_adequacy_empty`
    if the adeuqacy theorem is restricted to the empty mask).
- The effect "Fail" in the paper is called `ub` in our Coq formalization. See `ub.v`.
- The effect "Conc" in the paper is called `threadpool` in our Coq formalization.
  * The threadpool event and handler are found in `threadpool/handler.v`.
  * The concurrency adequacy theorem `ConcAdequate` is proven and thoroughly explained in
    `threadpool/interleaving.v` (theorem name: `threadpool_adequacy`).
- The infrastructure for state machine adequacy is in `exec.v`:
  * The multi-step relation is called `exec`. Note that this relation and other definitions in this
    file are more complex than described in the paper to support concurrency.
  * The single step relation is called `seHandler` (this is a simplified version of the more complex
    `eHandler` that supports concurrency).
  * `sound(H, I)` is called `seHandlerAdequate` (or `eHandlerAdequate` for concurrent handlers). The
    invariant `I` is called `sehandler_inv` (resp. `ehandler_inv`).
  * The theorem `StateMachineAdeqate` corresponds to `wpi_adequate`.

# ExampleLang
All the files pertaining to our ExampleLang example are in the `src/examplelang/` directory.

- The language definition of ExampleLang is in `lang.v`.
- The denotation of ExampleLang is `compile_expr` in `lang.v`.
- The rules of Figure 2 and Figure 4, and `WpPickInt` in Figure 6 are stated and proven in
  `program_logic.v`.

# HeapLang
All the files pertaining to our HeapLang case study are in the `src/heaplang/` directory.

- We use a hard copy of HeapLang given in `definition.v` in order to remove the upstream support for
  prophecy variables.
- The denotation of HeapLang is `compile_expr` in `lang.v`. As already hinted at in the text,
  we actually only have one denotation, the one with step events. Whether or not these step events
  do anything (and thus whether or not we do total or partial verification) is controlled by the
  parameter `m : later_modality` (see `../step.v`) which is passed to `stepH`, `heaplangH`, and the
  `WP` notation.
- The semantic bind lemma (Lemma 4.1) is `compile_expr_bind` in `lang.v`.
- The rules governing the program logic for HeapLang are found in `heaplang/program_logic.v`
- The definition of the interpretation relation for HeapLang programs and the adequacy theorems for
  the weakest preconditions are found in `adequacy.v`.
- The theorem relating the interpretational adequacy to operational adequacy is
  `partially_adequate_opsem_adequate` in `opsem_adequacy.v`.
  * "Interpretationally adequate" corresponds to `partially_adequate` defined in `adequacy.v`.
  * "Operationally adequate" corresponds to `adequate` which is defined in upstream Iris:
    `iris/program_logic/adequacy.v`.
  * The mentioned "trace lemmata" are spread out in the various effect files and all end in the
    postfix `_trace`. Traces and associated theory are established in `../trace.v` and
    `../threadpool/ctrace.v`.
- The interpreter `heaplang_interpreter` and various soundness results can be found in
  `interpreter.v`.

# Islaris

All files pertaining to the Islaris case study can be found in the `islaris/` folder.
The files not ending in `_itree.v` are the original files from Islaris, while we added the files
ending in `_itree.v`. 

**All author names in these files belong to the original authors of Islaris. We did not change them
for this work.**

- `spec_itree.v` defines the `SpecE` event and the corresponding handlers.
- The definition of `IslarisE` (called `islaE`) together with our ITree semantics of Islaris is in
  `opsem_itree.v`.
- `lifting_itree.v` contains our definition of `wp_asm` and the reproved program logic.
- `isla_adequacy` in `adequacy_itree.v` reproves the original adequacy statement from Islaris using
  our program logic (adapted for the fact that there is no concurrency).
