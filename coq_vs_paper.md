# Overview of effect libraries
Every effect has a corresponding library in a file with corresponding name (except for "Fail" and
"Conc"; see below) in the `src/` directory. Assuming the effect had name `effect` (lower case), we
use the following naming conventions:

- Its event type is called `eventE`.
- Its logical effect handler is called `effectH`.
- Its interpretation relation is called `effect_irel`.
- Its interpretation function is called `effect_ifn`.
- Its interpretational adequacy theorem is called `effect_adequacy` (or `effect_adequacy_empty`
  if the adequacy theorem is restricted to the empty mask).

The effect "Fail" in the paper is called `ub` in our Coq formalization. See `ub.v`.
The effect "Conc" in the paper is called `threadpool` in our Coq formalization, and all its related
files are found in `src/threadpool/`.

# Section 2: Key Ideas
Instead of formalizing the language in stages, we formalize the biggest extension $\lambda_{\mathbb{Z},!,\text{pick},\text{spawn}}$ from section 4.1 (with the exceptions noted below). We shall henceforth call this language ExampleLang.

Section 2.1:
- The definition of expressions and values (including the extensions from the later sections) is `expr` resp. `val` in `src/examplelang/lang.v`.
- `FailE` is `ubE` in `src/ub.v`. `fail` is `ub` in `src/ub.v`
- `LangE` (including the extensions from the later sections) is `exampleE` in `src/examplelang/lang.v`.
- Fig. 1:
  * The denotation of ExampleLang expressions `[[e]]` is `compile_expr` in `src/examplelang/lang.v`.
  * `to_int` and `to_lam` are `val_to_int` resp. `val_to_LamV` in `src/examplelang/lang.v`. Note
    that the Coq definitions return an option and the `None` case is turned into fail using the
    `some_or_ub` function with notation `?` (from `src/ub.v`).
  * Recursion is handled by means of the `rec` combinator from the ITree library
- `wp` (but with masks) is `wp_example` in `src/examplelang/program_logic.v`
- Fig. 2: (all rules are found in `src/examplelang/program_logic.v`)
  * `WpConsequence` is `wp_wand`
  * `WpFrame` is `wp_frame`
  * `WpVal` is `wp_val`
  * `WpBindPlusL` is `wp_bind_plus_l`
  * `WpBindPlusR` is `wp_bind_plus_R`
  * `WpPlus` is `wp_plus`
  * `WpApp` is `wp_app`
  * `WpIfTrue` is `wp_if_true`
  * `WpIfFalse` is `wp_if_false`
- Fig. 3: (all rules are found in `src/wpi.v`)
  * `WpiConsequence` is `wpi_wand`
  * `WpiFrame` is `wpi_frame_l`
  * `WpiEutt` is `wpi_proper` (written as a `Proper` instance such
    that it can be used with `setoid_rewrite`)
  * `WpiBind` is `wpi_bind`
  * `WpiRet` is `wpi_ret`

Section 2.2:
- `HeapE` (respectively `HeapH`) is `heapE` (respectively `heapH`) in `src/heap.v`
- `unwrap` is the `some_or_ub` function with notation `?` in `src/ub.v`
- `to_loc` is `val_to_loc` in `src/examplelang/lang.v` except that it returns an option and gives
  `none` instead of exhibition `ub` when failing.
- `alloc`, `load` and `store` are `alloc`, `load` and `store` in `src/heap.v`
- Fig. 4: (all in `src/examplelang/program_logic.v`, the rules in the
  paper ignore a side-condition on masks)
  * `WpRef` is `wp_ref`
  * `WpLoad` is `wp_load`
  * `WpStore` is `wp_store`
- Fig. 5: (all in `src/heap.v`, the rules in the paper ignore a
  side-condition on masks)
  * `WpiAlloc` is `wpi_alloc`
  * `WpiLoad` is `wpi_load`
  * `WpiStore` is `wpi_store`

Section 2.3:
- `DemonicE`, `choice`, and `DemonicH` are `demonicE`, `demonic_choice`, and `demonicH` in `src/choice.v`
- Fig. 6:
  * `WpiDemonic` is `wpi_demonic` in `src/choice.v`
  * `WpPickInt` is `wp_pick_int` in `src/examplelang/program_logic.v`

Section 2.4
- Fig. 7: (all in `src/threadpool/choice.v`)
    * $\downarrow_\DemonicE$ is `demonic_irel`.
    * `DemonicIrelChoice` corresponds to the variant `demonic_EDemonic` of `demonic_irelF`
    * `DemonicIrelRet` corresponds to the variant `demonic_Ret` of `demonic_irelF`
    * `DemonicIrelTau` corresponds to the variant `demonic_Tau` of `demonic_irelF`
    * `DemonicIrelVis` corresponds to the variant `demonic_Vis` of `demonic_irelF`
- Fig. 8:
  * `FailAdequate` is `ub_adequacy` in `src/ub.v`, with one difference: we use `R + ub_crash` in
    place of `option R` where `ub_crash` is a custom unit type.
  * `DemonicAdequate` is `demonic_adequacy` in `src/choice.v`
  * `HeapAdequate` is `heap_adequacy` in `src/heap.v`, with a technical difference: `heap_adequacy`
    allows one to choose the initial heap `σ`, taking the corresponding authoritative ghost state as
    an input and giving back this ghost state in the postcondition. In particular, the
    interpretation relation `heap_irel` has a slightly different signature than $\downarrow_\HeapE$
    to account for the initial and final heap of the program.
  * `EmptyAdequate` is `void_adequacy` in `src/void.v` (mask changing updates were excised in the
    paper)
  * `LangAdequate` is not formalized; deferred to `LangAdequate'` in Section 4.4.
- The interpreter for demonic choice is `demonic_ifn` in
  `src/choice.v`. We only build the composed interpreter for the
  HeapLang case study (see `src/heaplang/interpreter.v`), not for
  ExampleLang.

# Section 3: Weakest Preconditions for ITrees and Logical Effect Handlers

Section 3.1:
- The definition of `wpi` without concurrency is not given anywhere in the formalization. It is a
  special case of `wpi` in `src/wpi.v`. See Section 4 for full definition.
- The definition of what is a logical effect handler (extended with concurrency; see Section 3.5) is
  found in `src/handler.v` under the name `iHandler`. In particular, `HandlerMono` is
  `ihandler_mono`.

Section 3.2:
- `FailH` is `ubH` in `src/ub.v`
- `DemonicH` is `demonicH` in `src/choice.v`
- The composition operator `⊕` is notation defined in `src/handler.v`
- `WpiSubsume` is `wpi_inH` in `src/wpi.v` and the `⊆` relation is controlled by the `inH` typeclass
  defined in `src/handler.v`.

Section 3.3:
- `StateE` (respectively `StateH`) is `stateE` (respectively `stateH`) in `src/state.v`
- `HeapE` (respectively `HeapH`) is `heapE` (respectively `heapH`) in `src/heap.v`

# Section 4: Extension: Concurrency

Section 4.1:
- `ConcE`, `spawn`, and `yield` are `threadpoolE`, `spawn`, and `yield` in
  `src/threadpool/handler.v`
- Fig. 9: (all in `src/examplelang/lang.v`)
    * `yield_if_not_val` is `yield_if_not_val`
    * $[[e]]$ is `compile_expr`
    * $[[e]]_\yield$ is `compile_expr_yield` defined in the `let` binding in `compile_expr'`
- The CAS example is not formalized as a part of ExampleLang. However, it exists in
  the HeapLang formalization. Consult Section 6.

Section 4.2:
- Fig. 10: (all in `src/threadpool/handler.v`)
  * `WpiSpawn` is `wpi_spawn`
  * `WpiYield` is `wpi_yield`
- Fig. 11: (all rules are found in `src/examplelang/program_logic.v`)
  * `WpSpawn` is `wp_spawn`
  * `WpInvOpen` follows from `wp_atomic`
  * Bind rules such as `WpBindStoreL` and `WpBindStoreR` are not all formalized but follow from
    `wpi_bind`. For an example, consult the proof of `wp_bind_plus_l`.
- `WpiInvOpen` corresponds to either `wpi_open_invariant` or
  `wpi_open_invariant_timeless` depending on which of the two
  technical side-conditions of footnote 3 is preferred.
- $\LangH_{\mathbb{Z},!,\text{pick},\text{spawn}}$ is `exampleH` in
  `src/examplelang/program_logic.v`.

Section 4.3:
- As stated above, the full definition of what is a logical effect handler is found in `handler.v`
  under the name `iHandler`.
- The definition of `wpi` without masks is `wpi` in `src/wpi.v`
- The definition of `wpi` with masks is `wpi_mask` in `src/wpi.v`
  * This definition is further given notation `WPi` in `src/wpi.v`, which is what is used outwards

Section 4.4:
- The concurrency adequacy theorem `ConcAdequate` is `threadpool_adequacy` in
  `threadpool/interleaving.v`, with one difference: $t'$ has return type `R + last_thread_killed`
  instead of `R` to account for footnote 5. In the post-condition, `last_thread_killed` is handled
  by `True`, reflecting that `endthread` means safely terminating the thread.
- `LangAdequate'` corresponds to `wp_adequacy_irel` in `src/examplelang/adequacy.v` (modulo various
  simplifications made in the paper).
- Fig. 12: (all in `src/threadpool/interleaving.v`)
  * $\downarrow_\ConcE^i$ is `interleaves i`
  * $\downarrow_\ConcE$ is `threadpool_irel`. Specifically, `ConcIrel` corresponds to the
    definition `threadpool_irel`.
  * `ConcIrelRet` corresponds to the variant `Return` of `interleavesF`
  * `ConcIrelTau` corresponds to the variant `Step` of `interleavesF`
  * `ConcIrelVis` corresponds to the variant `Emit` of `interleavesF`
  * `ConcIrelYield` corresponds to the variant `Yield` of `interleavesF`
  * `ConcIrelEndthread` corresponds to the variant `KillThread` of `interleavesF`
  * `ConcIrelFork` corresponds to the variant `Fork` of `interleavesF`
  * The variant `KillLastThread` of `interleavesF` is not discussed in the paper, in accordance
    to footnote 9.
- $f_\ConcE$ is `threadpool_ifn` in `src/threadpool/scheduler.v`

# Section 5: Extension: Angelic Choice and State Machine Adequacy

- `AngelicE` and `AngelicH` are `angelicE` and `angelicH` in `src/angelic_choice.v`
- `WpiAngelic` is `wpi_angelic` (slightly reworded) in `src/angelic_choice.v`
- The infrastructure for state machine adequacy is in `src/exec.v`:
  * The multi-step relation is called `exec`. Note that this relation and other definitions in this file are more complex than described in the paper to support concurrency.
  * The single step relation is called `seHandler` (this is a simplified version of the more complex `eHandler` that supports concurrency).
  * `sound(H, I)` is called `seHandlerAdequate` (or `eHandlerAdequate` for concurrent handlers). The invariant `I` is called `sehandler_inv` (resp. `ehandler_inv`).
  * The theorem `StateMachineAdeqate` corresponds to `wpi_adequate`.

# Section 6: Case Study: HeapLang
The files pertaining to our HeapLang case study are in the `src/heaplang/` directory.
We refer to files relative to this directory.

Section 6.0:
- In `src/heaplang/definition.v`, we give a hard copy of the definition of HeapLang in order to
  remove the upstream support for prophecy variables.
- `HeapLangE` (respectively `HeapLangH`) is `heaplangE` (respectively `heaplangH`)
- The denotation of HeapLang expressions `[[e]]` is `compile_expr` in `src/heaplang/lang.v`.
    * As already hinted at in the text, we actually only have one denotation, the one with step
      events (see below). Whether or not these step events do anything (and thus whether or not we
      do total or partial verification) is controlled by the parameter `m : later_modality` (see
      `../step.v`) which is passed to `stepH`, `heaplangH`, and the `WP` notation.
    * Recursion is handled by means of the `rec` combinator from the ITree library
- The semantic bind lemma (Lemma 6.1) is `compile_expr_bind` in `src/heaplang/lang.v`
- The program logic rules are all found in `src/heaplang/program_logic.v` modulo small differences.
  First, the rules in Coq are generally written in a continuation passing style. Second, the rules
  are generic over the modality; for now take `m = Identity`. The rules that are mentioned in the
  paper are called as follows:
    * `HlWpBind` is `wp_bind`
    * `HlWpCasSuc` is `wp_CmpXchg_suc` and `HlWpCasFail` is `wp_CmpXchg_fail`. These have
      restrictions on what values can actually be compared, e.g., it is not safe to compare
      closures.

Section 6.1:
- `StepE` (respectively `StepH`) is `stepE` (respectively `stepH`) in `src/step.v`
    * There is one important difference between `stepH` in Coq and `StepH` in the paper. In Coq, our
      `stepH` takes a modality `m : later_modality` which determines whether a `step` event is
      handled using the later modality `▷` (when `m = Later`) or using no modality (when `m =
      Identity`).
- Fig. 13: (all in `src/step.v`)
    * $\downarrow_\StepE^n$ is `step_irel (Some n)`.
    * In our formalization, as opposed to the paper, `step_irel` is not defined as a coinductive
      relation but instead by way of a corecursive function `step_ifn` (the interpretation
      function).
    * `StepAdequate` is `step_adequacy_empty` (after taking `m = Later`).

Section 6.2:
- The interpreter `heaplang_interpreter` and various soundness results can be found in
  `src/heaplang/interpreter.v`.

Section 6.3:
- "Interpretationally adequate" (Definition 4.2) corresponds to `partially_adequate` defined in
  `src/heaplang/adequacy.v`, modulo the following differences:
    * `partially_adequate` takes as an argument the initial heap `σ` instead of universally
      quantifying over all heaps.
    * `partially_adequate` is stronger than Definition 4.2 (in fact, they are equivalent, but this
      converse implication is not important). A technical explanation: Unlike Definition 4.2,
      `wp_partial_soundness` doesn't quantify over $r$ and $t'$ (called `te` in Coq) such that
      $[[e]]^\later \downarrow^{\sigma; n}_{\HeapLangE^\later} t' \approx \Ret(r)$, but instead just
      quantifies over $t'$ (`te`) such that $[[e]]^\later \downarrow^{\sigma; n}_{\HeapLangE^\later}
      t'$, giving $t' \approx \Ret(r)$ for some $r$ as a guarantee rather than taking it as an
      assumption. (This difference is necessary for the case `n = None`, which is not discussed in
      the paper. We used Definition 4.3 instead of a definition more 1-to-1 with the Coq
      formalization because the former is a bit easier to understand.)
- "Operationally adequate" (Definition 4.3) corresponds to `adequate NotStuck` which is defined in
  upstream Iris: `iris/program_logic/adequacy.v`.
- The theorem relating the program logic to interpretation adequacy (first implication) is
  `wp_partial_soundness`:
- The theorem relating the interpretational adequacy to operational adequacy (second implication) is
  `partially_adequate_opsem_adequate` in `src/heaplang/opsem_adequacy.v`.
  * The mentioned "trace lemmata" are spread out in the various effect files and all end in the
    postfix `_trace`. Traces and associated theory are established in `../trace.v` and
    `../threadpool/ctrace.v`.

# Section 7: Case Study Islaris
All files pertaining to the Islaris case study can be found in the `islaris/` folder.
The files not ending in `_itree.v` are the original files from Islaris, while we added the files
ending in `_itree.v`.

- `HaltE` (respectively `HaltH`) is `haltE` (respectively `haltH`) in `src/halt.v`.
- `spec_itree.v` defines the `SpecE` event and the corresponding handlers.
- The definition of `IslarisE` (called `islaE`) together with our ITree semantics of Islaris is in
  `opsem_itree.v`.
- `lifting_itree.v` contains our definition of `wp_asm` and the reproved program logic.
- `isla_adequacy` in `adequacy_itree.v` reproves the original adequacy statement from Islaris using
  our program logic (adapted for the fact that there is no concurrency).
