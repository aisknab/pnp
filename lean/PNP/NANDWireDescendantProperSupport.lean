/-
Copyright (c) 2026 PNP Labs.

Execute an arbitrary descendant program inside an extracted computational
support, then construct the actual one-copy outer splice. Its wiring bound is
derived from execution. All ordinary outputs and literal fields are preserved,
and actual cumulative charges/removals remain visible after embedding.

This is an offered-program verifier component, not a global successful strategy,
full manuscript profiles, complete Package E or a polynomial-time bound.
-/

import PNP.NANDWireDescendantCausalBounds

namespace PNP.DirectWire.WireDescendantProperSupport

open WireDescendantHistory

variable {inputs outputs fields : Nat}
variable (carrier : WireCarrier inputs outputs fields)
variable (records : List (TerminalPrimitiveRecord inputs
  carrier.implementation.gateCount (outputs + fields) 0))

/-- The source of the local program includes the complete extracted interface. -/
def localSource :=
  (extractTerminalSupport carrier.exposed.candidate records).extractedCandidate.toImplementation

/-- Actual complete execution and actual compiler receipt, produced internally. -/
structure SplicedRun (stages : List RawStage) where
  run : CompiledRun (localSource carrier records) stages
  runAt : WireDescendantHistory.compile (localSource carrier records) stages = some run
  compiled : CompiledRawNandGraph
    (ArbitrarySupportSplice.graph carrier.exposed.candidate records run.result.candidate)
  compiledAt : ArbitrarySupportSplice.compile carrier.exposed.candidate records
    run.result.candidate = some compiled

/-- Positive retained exterior is exactly proper physical support. -/
theorem proper_iff_exterior_positive :
    (extractTerminalSupport carrier.exposed.candidate records).gateCount <
        carrier.implementation.gateCount ↔
      0 < (ArbitrarySupportSplice.exterior records).length := by
  have partition :
      (extractTerminalSupport carrier.exposed.candidate records).gateCount +
        (ArbitrarySupportSplice.exterior records).length = carrier.implementation.gateCount :=
    ArbitrarySupportSplice.exterior_accounting carrier.exposed.candidate records
  constructor <;> intro inequality <;> omega

namespace SplicedRun

variable {carrier records} {stages : List RawStage}

/-- Recover ordinary outputs and actual field sources from the compiled word. -/
def result (executed : SplicedRun carrier records stages) : WireCarrier inputs outputs fields :=
  carrier.spliceResult records executed.run.result.candidate executed.compiled

theorem open_equivalent (executed : SplicedRun carrier records stages) :
    executed.run.result.candidate.semantics =
      (extractTerminalSupport carrier.exposed.candidate records).extractedCandidate.semantics := by
  funext valuation output
  exact executed.run.semantics valuation output

theorem output (executed : SplicedRun carrier records stages)
    (valuation : Valuation inputs) (index : Fin outputs) :
    executed.result.implementation.candidate.semantics valuation index =
      carrier.implementation.candidate.semantics valuation index :=
  carrier.splice_output records executed.run.result.candidate executed.open_equivalent
    executed.compiled valuation index

theorem field (executed : SplicedRun carrier records stages)
    (valuation : Valuation inputs) (index : Fin fields) :
    executed.result.fieldValue valuation index = carrier.fieldValue valuation index :=
  carrier.splice_field records executed.run.result.candidate executed.open_equivalent
    executed.compiled valuation index

/-- Every exterior gate occurs once; every final local physical gate is counted. -/
theorem gateCount (executed : SplicedRun carrier records stages) :
    executed.result.implementation.gateCount =
      (ArbitrarySupportSplice.exterior records).length + executed.run.result.gateCount :=
  ArbitrarySupportSplice.result_gateCount carrier.exposed.candidate records
    executed.run.result.candidate executed.compiled

/-- Embedding preserves all historical execution costs, including later deletions. -/
theorem charge_accounting (executed : SplicedRun carrier records stages) :
    executed.result.implementation.gateCount + executed.run.removedCount =
      carrier.implementation.gateCount + executed.run.chargedCount := by
  have localBalance := executed.run.gate_balance
  change executed.run.result.gateCount + executed.run.removedCount =
    (extractTerminalSupport carrier.exposed.candidate records).gateCount +
      executed.run.chargedCount at localBalance
  have partition :
      (extractTerminalSupport carrier.exposed.candidate records).gateCount +
        (ArbitrarySupportSplice.exterior records).length = carrier.implementation.gateCount :=
    ArbitrarySupportSplice.exterior_accounting carrier.exposed.candidate records
  have finalCount := executed.gateCount
  omega

theorem gain_iff_local_gain (executed : SplicedRun carrier records stages) :
    executed.result.implementation.gateCount < carrier.implementation.gateCount ↔
      executed.run.result.gateCount <
        (extractTerminalSupport carrier.exposed.candidate records).gateCount := by
  have partition :
      (extractTerminalSupport carrier.exposed.candidate records).gateCount +
        (ArbitrarySupportSplice.exterior records).length = carrier.implementation.gateCount :=
    ArbitrarySupportSplice.exterior_accounting carrier.exposed.candidate records
  have finalCount := executed.gateCount
  constructor <;> intro inequality <;> omega

theorem gain_iff_net_charges (executed : SplicedRun carrier records stages) :
    executed.result.implementation.gateCount < carrier.implementation.gateCount ↔
      executed.run.chargedCount < executed.run.removedCount := by
  have accounting := executed.charge_accounting
  constructor <;> intro inequality <;> omega

theorem strictGain (executed : SplicedRun carrier records stages)
    (smaller : executed.run.result.gateCount <
      (extractTerminalSupport carrier.exposed.candidate records).gateCount) :
    StrictEquivalentGain carrier.implementation executed.result.implementation :=
  ⟨executed.gain_iff_local_gain.mpr smaller, executed.output⟩

theorem strictResidualDescent (executed : SplicedRun carrier records stages)
    (smaller : executed.run.result.gateCount <
      (extractTerminalSupport carrier.exposed.candidate records).gateCount) :
    residualSlack executed.result.implementation < residualSlack carrier.implementation :=
  (executed.strictGain smaller).strictResidualDescent

end SplicedRun

/-- Compile the whole offered program and then the actual literal outer graph. -/
def compile (stages : List RawStage) : Option (SplicedRun carrier records stages) :=
  match runAt : WireDescendantHistory.compile (localSource carrier records) stages with
  | none => none
  | some run =>
      match compiledAt : ArbitrarySupportSplice.compile carrier.exposed.candidate records
          run.result.candidate with
      | none => none
      | some compiled => some ⟨run, runAt, compiled, compiledAt⟩

/-- No extra order, rank or acyclicity premise is required for a successful run. -/
theorem compile_complete (stages : List RawStage)
    (run : CompiledRun (localSource carrier records) stages)
    (runAt : WireDescendantHistory.compile (localSource carrier records) stages = some run) :
    ∃ executed, compile carrier records stages = some executed ∧ executed.run = run := by
  unfold compile
  split
  · rename_i rejected
    have impossible := rejected.symm.trans runAt
    cases impossible
  · rename_i actual actualAt
    have same : actual = run := Option.some.inj (actualAt.symm.trans runAt)
    cases same
    obtain ⟨compiled, compiledAt⟩ :=
      run.extracted_compiles carrier.exposed.candidate records
    split
    · rename_i rejected
      have impossible := rejected.symm.trans compiledAt
      cases impossible
    · exact ⟨_, rfl, rfl⟩

/-- Total outer compilation is equivalent to successful complete local execution. -/
theorem compile_exists_iff (stages : List RawStage) :
    (∃ executed, compile carrier records stages = some executed) ↔
      ∃ run, WireDescendantHistory.compile (localSource carrier records) stages = some run := by
  constructor
  · rintro ⟨executed, _accepted⟩
    exact ⟨executed.run, executed.runAt⟩
  · rintro ⟨run, runAt⟩
    obtain ⟨executed, accepted, _same⟩ := compile_complete carrier records stages run runAt
    exact ⟨executed, accepted⟩

theorem compile_none_iff (stages : List RawStage) :
    compile carrier records stages = none ↔
      WireDescendantHistory.compile (localSource carrier records) stages = none := by
  constructor
  · intro rejected
    cases runAt : WireDescendantHistory.compile (localSource carrier records) stages with
    | none => rfl
    | some run =>
        obtain ⟨executed, accepted, _same⟩ :=
          compile_complete carrier records stages run runAt
        have impossible := rejected.symm.trans accepted
        cases impossible
  · intro rejected
    unfold compile
    split
    · rfl
    · rename_i run runAt
      have impossible := runAt.symm.trans rejected
      cases impossible

end PNP.DirectWire.WireDescendantProperSupport
