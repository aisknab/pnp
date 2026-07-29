/-
Copyright (c) 2026 PNP Labs.

Exact pure semantics of the four-gate locked-NAND target-emitter final block.
-/

import PNP.Concrete.LockedNANDTargetEmitterSemanticOutput
import PNP.Concrete.LockedNANDTargetEmitterSemanticPrefix

namespace PNP.Concrete.LockedNAND.TargetEmitterSemanticFinal

open PNP.Concrete

abbrev Runtime := TargetEmitterProgramSemantics.Runtime

private theorem getD_three_zero
    {α : Type} (first second third fallback : α) :
    [first, second, third].getD 0 fallback = first := by
  rfl

private theorem getD_three_one
    {α : Type} (first second third fallback : α) :
    [first, second, third].getD 1 fallback = second := by
  rfl

private theorem getD_three_two
    {α : Type} (first second third fallback : α) :
    [first, second, third].getD 2 fallback = third := by
  rfl

/-- Evaluating the closed positive final plan is exactly the independent raw
four-gate template appended at the supplied prefix boundary. -/
theorem finalPositivePlan_evaluated
    (runtime : Runtime)
    (prefixGates : List RawGate) (prefixOutput : RawSource)
    (outputTrace : TargetEmitterPlan.NatExpression)
    (finalLockCoordinate outputTraceCoordinate : Nat)
    (base :
      runtime.registers.outputIndex + 1 =
        prefixGates.length)
    (prefixOutputEq :
      prefixOutput =
        .gate runtime.registers.outputIndex)
    (finalLock :
      TargetEmitterPlan.finalLock.evaluate runtime.registers
          runtime.captured 0 =
        finalLockCoordinate)
    (trace :
      outputTrace.evaluate runtime.registers
          runtime.captured 0 =
        outputTraceCoordinate) :
    prefixGates ++
        TargetEmitterProgramSemantics.evaluatedGates runtime
          (TargetEmitterPlan.finalPositivePlan outputTrace) =
      RawBuilder.appendTemplate prefixGates
        (RawBuilder.rawBinding3
          (.input finalLockCoordinate)
          prefixOutput
          (.input outputTraceCoordinate))
        RawBuilder.finalTemplate := by
  simp only [TargetEmitterProgramSemantics.evaluatedGates,
    TargetEmitterPlan.finalPositivePlan,
    TargetEmitterPlan.instantiateTemplateAt,
    TargetEmitterPlan.finalBindings,
    TargetEmitterPlan.finalTemplate,
    TargetEmitterPlan.TemplateGate.instantiateAt,
    TargetEmitterPlan.TemplateSource.instantiateAt,
    TargetEmitterPlan.PlannedGate.evaluate,
    TargetEmitterPlan.PlannedSource.evaluate,
    TargetEmitterPlan.NatExpression.evaluate_addOffset,
    TargetEmitterPlan.outputIndex,
    TargetEmitterPlan.NatExpression.evaluate_counter,
    TargetEmitterPlan.NatExpression.evaluateCounter,
    List.map_cons, List.map_nil]
  simp only [getD_three_zero, getD_three_one, getD_three_two,
    TargetEmitterPlan.NatExpression.evaluate_counter,
    TargetEmitterPlan.NatExpression.evaluateCounter]
  rw [finalLock, trace, prefixOutputEq]
  simp [RawBuilder.appendTemplate, base,
    RawBuilder.finalTemplate,
    DirectWire.finalConjunctionDirectProgram,
    rawProgramGates, RawGate.ofGate, RawSource.ofSource,
    RawBuilder.instantiateGate,
    RawBuilder.instantiateSource, RawBuilder.rawBinding3]

/-- The zero-check branch is the same raw final template with an explicit
false prefix source and the source-captured raw trace coordinate. -/
theorem finalZeroPlan_evaluated
    (runtime : Runtime)
    (prefixGates : List RawGate)
    (finalLockCoordinate outputTraceCoordinate : Nat)
    (base :
      runtime.registers.outputIndex =
        prefixGates.length)
    (finalLock :
      TargetEmitterPlan.finalLock.evaluate runtime.registers
          runtime.captured 0 =
        finalLockCoordinate)
    (trace :
      TargetEmitterPlan.rawGateTrace.evaluate runtime.registers
          runtime.captured 0 =
        outputTraceCoordinate) :
    prefixGates ++
        TargetEmitterProgramSemantics.evaluatedGates runtime
          TargetEmitterPlan.finalZeroPlan =
      RawBuilder.appendTemplate prefixGates
        (RawBuilder.rawBinding3
          (.input finalLockCoordinate)
          (.constant false)
          (.input outputTraceCoordinate))
        RawBuilder.finalTemplate := by
  simp only [TargetEmitterProgramSemantics.evaluatedGates,
    TargetEmitterPlan.finalZeroPlan,
    TargetEmitterPlan.instantiateTemplateAt,
    TargetEmitterPlan.finalBindings,
    TargetEmitterPlan.finalTemplate,
    TargetEmitterPlan.TemplateGate.instantiateAt,
    TargetEmitterPlan.TemplateSource.instantiateAt,
    TargetEmitterPlan.PlannedGate.evaluate,
    TargetEmitterPlan.PlannedSource.evaluate,
    TargetEmitterPlan.NatExpression.evaluate_addOffset,
    TargetEmitterPlan.outputIndex,
    TargetEmitterPlan.NatExpression.evaluate_counter,
    TargetEmitterPlan.NatExpression.evaluateCounter,
    List.map_cons, List.map_nil]
  simp only [getD_three_zero, getD_three_one, getD_three_two]
  rw [finalLock, trace]
  simp [RawBuilder.appendTemplate, base,
    RawBuilder.finalTemplate,
    DirectWire.finalConjunctionDirectProgram,
    rawProgramGates, RawGate.ofGate, RawSource.ofSource,
    RawBuilder.instantiateGate,
    RawBuilder.instantiateSource, RawBuilder.rawBinding3]

private theorem encodeGateListTokens_append
    (first second : List RawGate) :
    encodeGateListTokens (first ++ second) =
      encodeGateListTokens first ++
        encodeGateListTokens second := by
  induction first with
  | nil =>
      rfl
  | cons gate rest inductionHypothesis =>
      simp [encodeGateListTokens,
        inductionHypothesis, List.append_assoc]

/-- Exact token consequence of the positive final-template equality. -/
theorem finalPositiveResult_targetTokens
    (runtime : Runtime)
    (prefixGates : List RawGate) (prefixOutput : RawSource)
    (outputTrace : TargetEmitterPlan.NatExpression)
    (finalLockCoordinate outputTraceCoordinate : Nat)
    (tokenPrefix : List Token)
    (targetTokens :
      runtime.targetTokens =
        tokenPrefix ++ encodeGateListTokens prefixGates)
    (base :
      runtime.registers.outputIndex + 1 =
        prefixGates.length)
    (prefixOutputEq :
      prefixOutput =
        .gate runtime.registers.outputIndex)
    (finalLock :
      TargetEmitterPlan.finalLock.evaluate runtime.registers
          runtime.captured 0 =
        finalLockCoordinate)
    (trace :
      outputTrace.evaluate runtime.registers
          runtime.captured 0 =
        outputTraceCoordinate) :
    (TargetEmitterProgramSemantics.finalResult runtime
      (TargetEmitterPlan.finalPositivePlan
        outputTrace)).targetTokens =
      tokenPrefix ++
        encodeGateListTokens
          (RawBuilder.appendTemplate prefixGates
            (RawBuilder.rawBinding3
              (.input finalLockCoordinate)
              prefixOutput
              (.input outputTraceCoordinate))
            RawBuilder.finalTemplate) := by
  rw [TargetEmitterProgramSemantics.finalResult_targetTokens,
    targetTokens]
  change
    (tokenPrefix ++ encodeGateListTokens prefixGates) ++
        encodeGateListTokens
          (TargetEmitterProgramSemantics.evaluatedGates runtime
            (TargetEmitterPlan.finalPositivePlan outputTrace)) =
      _
  rw [List.append_assoc]
  rw [← encodeGateListTokens_append]
  exact congrArg (fun tokens => tokenPrefix ++ tokens)
    (congrArg encodeGateListTokens
      (finalPositivePlan_evaluated runtime prefixGates
        prefixOutput outputTrace finalLockCoordinate
        outputTraceCoordinate base prefixOutputEq finalLock trace))

/-- Exact token consequence of the zero-check final-template equality. -/
theorem finalZeroResult_targetTokens
    (runtime : Runtime)
    (prefixGates : List RawGate)
    (finalLockCoordinate outputTraceCoordinate : Nat)
    (tokenPrefix : List Token)
    (targetTokens :
      runtime.targetTokens =
        tokenPrefix ++ encodeGateListTokens prefixGates)
    (base :
      runtime.registers.outputIndex =
        prefixGates.length)
    (finalLock :
      TargetEmitterPlan.finalLock.evaluate runtime.registers
          runtime.captured 0 =
        finalLockCoordinate)
    (trace :
      TargetEmitterPlan.rawGateTrace.evaluate runtime.registers
          runtime.captured 0 =
        outputTraceCoordinate) :
    (TargetEmitterProgramSemantics.finalResult runtime
      TargetEmitterPlan.finalZeroPlan).targetTokens =
      tokenPrefix ++
        encodeGateListTokens
          (RawBuilder.appendTemplate prefixGates
            (RawBuilder.rawBinding3
              (.input finalLockCoordinate)
              (.constant false)
              (.input outputTraceCoordinate))
            RawBuilder.finalTemplate) := by
  rw [TargetEmitterProgramSemantics.finalResult_targetTokens,
    targetTokens]
  change
    (tokenPrefix ++ encodeGateListTokens prefixGates) ++
        encodeGateListTokens
          (TargetEmitterProgramSemantics.evaluatedGates runtime
            TargetEmitterPlan.finalZeroPlan) =
      _
  rw [List.append_assoc]
  rw [← encodeGateListTokens_append]
  exact congrArg (fun tokens => tokenPrefix ++ tokens)
    (congrArg encodeGateListTokens
      (finalZeroPlan_evaluated runtime prefixGates
        finalLockCoordinate outputTraceCoordinate base finalLock trace))

end PNP.Concrete.LockedNAND.TargetEmitterSemanticFinal
