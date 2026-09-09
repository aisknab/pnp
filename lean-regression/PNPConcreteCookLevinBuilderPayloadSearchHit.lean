/-
Copyright (c) 2026 PNP Labs.

Hit-branch execution, exact frame restoration, canonical output, bounded growth
and end-to-end linkage from the physical source-width comparison.
-/
import PNP.Concrete.CookLevinBuilderPayloadSearchHit

namespace PNP.Concrete.CookLevin.BuilderPayloadSearchHitRegression

open PipelineTape BuilderUnaryPolynomial
open BuilderDividerOperands (endTape)
open BuilderPayloadLiteralTokenSelector (Kind Source Context)
open PipelineStateNamespace (renameConfiguration)
open BuilderPayloadSearchHit

example {width : Nat} (source : Source width) (context : Context source.ordinal) :
    (scratch source context).length = 14 :=
  BuilderPayloadSearchHit.scratch_length source context

example {width : Nat} (source : Source width) (context : Context source.ordinal) (older : List Nat) :
    initialValues source context older = BuilderPayloadLiteralTokenSelector.initialValues source context older ++ scratch source context :=
  BuilderPayloadSearchHit.input_layout source context older

example {width : Nat} (source : Source width) (context : Context source.ordinal)
    (older : List Nat) (inside outside : List WorkSymbol) :
    workRunExact? (BuilderRegisterErase.machine 14) (BuilderRegisterErase.workSteps (scratch source context))
      (workStartConfiguration (BuilderRegisterErase.machine 14) (endTape (initialValues source context older) inside outside)) =
      some {state := (BuilderRegisterErase.machine 14).acceptState, tape := endTape (BuilderPayloadLiteralTokenSelector.initialValues source context older) inside (restoredOutside source context outside)} :=
  BuilderPayloadSearchHit.restore_workRunExact source context older inside outside

example {width : Nat} (source : Source width) (context : Context source.ordinal)
    (older : List Nat) (outside : List WorkSymbol) :
    (registerWord (BuilderPayloadLiteralTokenSelector.initialValues source context older)).length +
      (restoredOutside source context outside).length =
    (registerWord (initialValues source context older)).length + outside.length :=
  BuilderPayloadSearchHit.restored_span_eq source context older outside

example {width : Nat} (source : Source width) (context : Context source.ordinal)
    (older : List Nat) (inside outside : List WorkSymbol) :
    workRunExact? (BuilderPayloadSearchHit.machine source.kind) (workSteps source context) (initialConfiguration source context older inside outside) =
      some (finalConfiguration source context older inside outside) :=
  BuilderPayloadSearchHit.workRunExact source context older inside outside

example {width : Nat} (source : Source width) (context : Context source.ordinal)
    (older : List Nat) (inside outside : List WorkSymbol) :
    run (compileWorkMachine (BuilderPayloadSearchHit.machine source.kind)) (6 * workSteps source context)
      (encodeWorkConfiguration (initialConfiguration source context older inside outside)) =
      encodeWorkConfiguration (finalConfiguration source context older inside outside) :=
  BuilderPayloadSearchHit.run_compile_exact source context older inside outside

example (configuration : WorkConfiguration) :
    observe (renameConfiguration WorkMachineChain.secondState configuration) =
      BuilderPayloadLiteralTokenSelector.observe configuration :=
  BuilderPayloadSearchHit.observe_renamed configuration

example {width : Nat} (source : Source width) (context : Context source.ordinal)
    (older : List Nat) (inside outside : List WorkSymbol) :
    observe (finalConfiguration source context older inside outside) =
      DirectToken.literalSlot source.selectedLiteral.emit context.position :=
  BuilderPayloadSearchHit.canonical_result source context older inside outside

example {width : Nat} (source : Source width) (context : Context source.ordinal)
    (older : List Nat) (inside outside : List WorkSymbol) :
    observe (workRun (BuilderPayloadSearchHit.machine source.kind) (workSteps source context) (initialConfiguration source context older inside outside)) =
      DirectToken.literalSlot source.selectedLiteral.emit context.position :=
  BuilderPayloadSearchHit.workRun_observes_literal source context older inside outside

example {width : Nat} (source : Source width) (context : Context source.ordinal)
    (older : List Nat) (inside outside : List WorkSymbol) :
    (finalConfiguration source context older inside outside).tape =
      endTape (finalValues source context older) inside (finalOutside source context outside) :=
  BuilderPayloadSearchHit.final_tape source context older inside outside

example {width : Nat} (source : Source width) (context : Context source.ordinal) (older : List Nat) :
    ∃ remainingScratch, finalValues source context older =
      BuilderPayloadLiteralTokenSelector.initialValues source context older ++ remainingScratch :=
  BuilderPayloadSearchHit.original_frame_preserved source context older

example (kind : Kind) :
    (BuilderPayloadSearchHit.machine kind).rules.Pairwise WorkMachineChain.QueryDistinct :=
  BuilderPayloadSearchHit.rules_pairwise_query_distinct kind

example (kind : Kind) : WorkMachineChain.NoRuleAtAccept (BuilderPayloadSearchHit.machine kind) :=
  BuilderPayloadSearchHit.noRuleAtAccept kind

example (kind : Kind) : WorkMachineProgramGraph.NoRuleAt (BuilderPayloadSearchHit.machine kind) (BuilderPayloadSearchHit.machine kind).rejectState :=
  BuilderPayloadSearchHit.noRuleAtReject kind

example (kind : Kind) : (BuilderPayloadSearchHit.machine kind).acceptState ≠ (BuilderPayloadSearchHit.machine kind).rejectState :=
  BuilderPayloadSearchHit.acceptState_ne_rejectState kind

example (kind : Kind) : WorkMachineProgramGraph.NoRuleAt (BuilderPayloadSearchHit.machine kind)
    (WorkMachineChain.secondState (WorkMachineChain.secondState 2)) :=
  BuilderPayloadSearchHit.noRuleAtPadding kind

example {width : Nat} (source : Source width) (context : Context source.ordinal)
    (older : List Nat) (outside : List WorkSymbol) (bound : NatPolynomial) (input : Nat)
    (hSpan : (registerWord (initialValues source context older)).length + outside.length ≤ bound.eval input) :
    (registerWord (finalValues source context older)).length + (finalOutside source context outside).length ≤
      (spanPolynomial source.kind bound).eval input ∧
    6 * workSteps source context ≤ (rawTimePolynomial source.kind bound).eval input :=
  BuilderPayloadSearchHit.source_polynomial_bounds source context older outside bound input hSpan

example {width : Nat} (source : Source width) (context : Context source.ordinal)
    (older : List Nat) (inside outside : List WorkSymbol)
    (hHit : context.position < source.originalLiteral.index.val + 2) :
    workRunExact? (WorkMachineChain.machine (BuilderPayloadSearchComparison.machine source.kind) (BuilderPayloadSearchHit.machine source.kind))
      (BuilderPayloadSearchComparison.workSteps source context + 1 + workSteps source context)
      (workStartConfiguration (WorkMachineChain.machine (BuilderPayloadSearchComparison.machine source.kind) (BuilderPayloadSearchHit.machine source.kind))
        (endTape (BuilderPayloadSearchComparison.initialValues source context older) inside outside)) =
      some (renameConfiguration WorkMachineChain.secondState
        (finalConfiguration source context older inside (BuilderPayloadSearchComparison.finalOutside source context outside))) :=
  BuilderPayloadSearchHit.comparison_hit_workRunExact source context older inside outside hHit

-- Distinct outcomes survive both nested state renamings.
example (tape : WorkTape) :
    observe {state := WorkMachineChain.secondState (WorkMachineChain.secondState 0), tape := tape} = some .t := rfl
example (tape : WorkTape) :
    observe {state := WorkMachineChain.secondState (WorkMachineChain.secondState 1), tape := tape} = some .f := rfl
example (tape : WorkTape) :
    observe {state := WorkMachineChain.secondState (WorkMachineChain.secondState 2), tape := tape} = none := rfl

-- Erasure does not shrink the physical span: cleared cells become blank exterior.
example {width : Nat} (source : Source width) (context : Context source.ordinal) (outside : List WorkSymbol) :
    (restoredOutside source context outside).length =
      (registerWord (scratch source context)).length + outside.length := by
  simp only [restoredOutside, BuilderRegisterErase.clearedSpan, List.length_append, List.length_replicate]

example {width : Nat} (source : Source width) (context : Context source.ordinal) (outside : List WorkSymbol) :
    outside.length ≤ (restoredOutside source context outside).length := by
  simp only [restoredOutside, List.length_append, List.length_replicate]
  omega

-- The cleanup count is fixed even for arbitrarily large values and source lists.
example {width : Nat} (source : Source width) (context : Context source.ordinal) :
    BuilderRegisterErase.workSteps (scratch source context) =
      (registerWord (scratch source context)).length + 28 := by
  simp only [BuilderRegisterErase.workSteps, BuilderRegisterErase.clearedSpan, BuilderPayloadSearchHit.scratch_length]

end PNP.Concrete.CookLevin.BuilderPayloadSearchHitRegression
