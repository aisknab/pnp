/-
Copyright (c) 2026 PNP Labs.

Derive arbitrary-label wiring bounds through actual descendant programs.
These structural bounds justify an outer literal splice; Boolean equivalence
alone is not used as acyclicity authority. Supports and programs remain inputs.
This is not full manuscript Package E, global ZeroSlack or polynomial PCCMin.
-/

import PNP.NANDWireDescendantGain

namespace PNP.DirectWire.WireHistoryArbitrarySupport

open WireObligationHistory

variable {inputs gates outputs profileWidth : Nat}
variable (candidate : Candidate inputs gates outputs)
variable (records : List (TerminalPrimitiveRecord inputs gates outputs profileWidth))
variable {raw : List (RawEvent (terminalInterfacePorts candidate records).length)}

theorem closedHistory_dependencyInterfaceBound
    (history : ClosedHistory (extractedCarrier candidate records) raw)
    (labels : Fin inputs → Nat) :
    ArbitrarySupportSplice.DependencyInterfaceBound candidate records
      (fieldCandidate history.state.current) labels := by
  intro field
  calc
    CausalBound.outputLevel (fieldCandidate history.state.current)
        (ArbitrarySupportSplice.dependencyBoundaryLabels candidate records labels) field =
        history.state.current.fieldLevel
          (ArbitrarySupportSplice.dependencyBoundaryLabels candidate records labels) field :=
      fieldCandidate_outputLevel _ _ _
    _ ≤ (extractedCarrier candidate records).fieldLevel
        (ArbitrarySupportSplice.dependencyBoundaryLabels candidate records labels) field :=
      history.field_causal_bound _ field
    _ = terminalExtractedInterfaceCausalLevel candidate records labels
        (CausalBound.levels candidate.program labels) field := rfl
    _ ≤ CausalBound.levels candidate.program labels
        ((terminalInterfacePorts candidate records).get field) :=
      extractTerminalSupport_causal_levels candidate records labels field

end PNP.DirectWire.WireHistoryArbitrarySupport

namespace PNP.DirectWire.WireDescendantHistory

variable {inputs outputs : Nat}
variable {source : Implementation inputs outputs} {stage : RawStage}

theorem StageCompilation.output_dependency_bound
    (compiled : StageCompilation source stage)
    (labels : Fin inputs → Nat) (output : Fin outputs) :
    CausalBound.outputLevel compiled.result.candidate labels output ≤
      CausalBound.outputLevel source.candidate labels output := by
  exact ArbitrarySupportSplice.result_output_dependency_bound
    source.candidate compiled.records
    (WireHistoryArbitrarySupport.fieldCandidate compiled.owned.history.state.current)
    labels
    (WireHistoryArbitrarySupport.closedHistory_dependencyInterfaceBound
      source.candidate compiled.records compiled.owned.history labels)
    compiled.owned.compiled compiled.owned.compiledAt output

theorem CompiledRun.output_dependency_bound
    {stages : List RawStage} (run : CompiledRun source stages)
    (labels : Fin inputs → Nat) (output : Fin outputs) :
    CausalBound.outputLevel run.result.candidate labels output ≤
      CausalBound.outputLevel source.candidate labels output := by
  induction run with
  | nil source => exact Nat.le_refl _
  | cons first rest ih =>
      exact Nat.le_trans ih (first.output_dependency_bound labels output)

variable {gates profileWidth : Nat}
variable (candidate : Candidate inputs gates outputs)
variable (records : List (TerminalPrimitiveRecord inputs gates outputs profileWidth))
variable {stages : List RawStage}

theorem CompiledRun.extracted_causalInterfaceBound
    (run : CompiledRun
      (extractTerminalSupport candidate records).extractedCandidate.toImplementation stages) :
    ArbitrarySupportSplice.CausalInterfaceBound candidate records run.result.candidate := by
  intro output
  calc
    CausalBound.outputLevel run.result.candidate
        (ArbitrarySupportSplice.causalBoundaryLabels candidate records) output ≤
        CausalBound.outputLevel
          (extractTerminalSupport candidate records).extractedCandidate.toImplementation.candidate
          (ArbitrarySupportSplice.causalBoundaryLabels candidate records) output :=
      run.output_dependency_bound _ output
    _ = terminalExtractedInterfaceCausalLevel candidate records
        (fun _ => 0) (fun index => index.val + 1) output := rfl
    _ ≤ ((terminalInterfacePorts candidate records).get output).val + 1 :=
      extractTerminalSupport_causal_index candidate records output

theorem CompiledRun.extracted_compiles
    (run : CompiledRun
      (extractTerminalSupport candidate records).extractedCandidate.toImplementation stages) :
    ∃ compiled, ArbitrarySupportSplice.compile candidate records run.result.candidate =
      some compiled :=
  ArbitrarySupportSplice.compile_of_causalInterfaceBound candidate records _
    (run.extracted_causalInterfaceBound candidate records)

end PNP.DirectWire.WireDescendantHistory
