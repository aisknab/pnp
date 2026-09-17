/-
Copyright (c) 2026 PNP Labs.

Run a complete mixed program over the computational fields of an extracted
support, allowing obligations to remain open across actual descendant splices.
Final closure recovers the full interface; execution-derived causal bounds
construct the literal one-copy outer splice without a supplied wiring witness.

This is verification of an offered finite program, not certificate discovery,
full manuscript profiles or rule coverage, ZeroSlack or polynomial execution.
-/

import PNP.NANDWireOpenProgramOwnership

namespace PNP.DirectWire.WireOpenProperSupport

open WireOpenProgram (RawEvent CompiledProgram)
open WireHistoryArbitrarySupport (extractedCarrier fieldCandidate)

variable {inputs outputs fields : Nat}
variable (carrier : WireCarrier inputs outputs fields)
variable (records : List (TerminalPrimitiveRecord inputs
  carrier.implementation.gateCount (outputs + fields) 0))

/-- The extracted interface is represented by actual fields, with no protected
duplicate outputs that would prevent temporary forgetting and restoration. -/
def localSource := extractedCarrier carrier.exposed.candidate records

variable {raw : List RawEvent}

/-- Final closure restores every extracted observation, not merely ordinary outputs. -/
theorem program_equivalent (program : CompiledProgram (localSource carrier records) raw) :
    (fieldCandidate program.result).semantics =
      (extractTerminalSupport carrier.exposed.candidate records).extractedCandidate.semantics := by
  funext valuation field
  exact (WireHistoryArbitrarySupport.fieldCandidate_semantics program.result valuation field).trans
    ((program.full_field valuation field).trans
      (WireHistoryArbitrarySupport.extractedCarrier_fieldValue
        carrier.exposed.candidate records valuation field))

/-- All input-label dependencies come from the actual complete execution. -/
theorem program_causalInterfaceBound (program : CompiledProgram (localSource carrier records) raw) :
    ArbitrarySupportSplice.CausalInterfaceBound carrier.exposed.candidate records
      (fieldCandidate program.result) := by
  intro field
  calc
    CausalBound.outputLevel (fieldCandidate program.result)
        (ArbitrarySupportSplice.causalBoundaryLabels carrier.exposed.candidate records) field =
        program.result.fieldLevel
          (ArbitrarySupportSplice.causalBoundaryLabels carrier.exposed.candidate records) field :=
      WireHistoryArbitrarySupport.fieldCandidate_outputLevel _ _ _
    _ ≤ (localSource carrier records).fieldLevel
        (ArbitrarySupportSplice.causalBoundaryLabels carrier.exposed.candidate records) field :=
      program.field_causal_bound _ field
    _ = terminalExtractedInterfaceCausalLevel carrier.exposed.candidate records
        (fun _ => 0) (fun index => index.val + 1) field := rfl
    _ ≤ ((terminalInterfacePorts carrier.exposed.candidate records).get field).val + 1 :=
      extractTerminalSupport_causal_index carrier.exposed.candidate records field

theorem program_compiles (program : CompiledProgram (localSource carrier records) raw) :
    ∃ compiled, ArbitrarySupportSplice.compile carrier.exposed.candidate records
      (fieldCandidate program.result) = some compiled :=
  ArbitrarySupportSplice.compile_of_causalInterfaceBound carrier.exposed.candidate records _
    (program_causalInterfaceBound carrier records program)

/-- Both complete computations are retained; neither receipt is a raw input. -/
structure SplicedProgram (raw : List RawEvent) where
  program : CompiledProgram (localSource carrier records) raw
  programAt : WireOpenProgram.compile (localSource carrier records) raw = some program
  compiled : CompiledRawNandGraph
    (ArbitrarySupportSplice.graph carrier.exposed.candidate records (fieldCandidate program.result))
  compiledAt : ArbitrarySupportSplice.compile carrier.exposed.candidate records
    (fieldCandidate program.result) = some compiled

namespace SplicedProgram

variable {carrier records}

/-- Rebind ordinary outputs and fields from the actual literal compiler result. -/
def result (executed : SplicedProgram carrier records raw) : WireCarrier inputs outputs fields :=
  carrier.spliceResult records (fieldCandidate executed.program.result) executed.compiled

theorem output (executed : SplicedProgram carrier records raw)
    (valuation : Valuation inputs) (index : Fin outputs) :
    executed.result.implementation.candidate.semantics valuation index =
      carrier.implementation.candidate.semantics valuation index :=
  carrier.splice_output records (fieldCandidate executed.program.result)
    (program_equivalent carrier records executed.program) executed.compiled valuation index

theorem field (executed : SplicedProgram carrier records raw)
    (valuation : Valuation inputs) (index : Fin fields) :
    executed.result.fieldValue valuation index = carrier.fieldValue valuation index :=
  carrier.splice_field records (fieldCandidate executed.program.result)
    (program_equivalent carrier records executed.program) executed.compiled valuation index

/-- Exactly one unchanged exterior and the actual final local physical circuit. -/
theorem gateCount (executed : SplicedProgram carrier records raw) :
    executed.result.implementation.gateCount =
      (ArbitrarySupportSplice.exterior records).length +
        executed.program.result.implementation.gateCount :=
  ArbitrarySupportSplice.result_gateCount carrier.exposed.candidate records
    (fieldCandidate executed.program.result) executed.compiled

theorem charge_accounting (executed : SplicedProgram carrier records raw) :
    executed.result.implementation.gateCount + executed.program.execution.removed =
      carrier.implementation.gateCount + executed.program.execution.charged := by
  have localBalance := executed.program.gate_balance
  change executed.program.result.implementation.gateCount + executed.program.execution.removed =
    (extractTerminalSupport carrier.exposed.candidate records).gateCount +
      executed.program.execution.charged at localBalance
  have partition :
      (extractTerminalSupport carrier.exposed.candidate records).gateCount +
        (ArbitrarySupportSplice.exterior records).length = carrier.implementation.gateCount :=
    ArbitrarySupportSplice.exterior_accounting carrier.exposed.candidate records
  have finalCount := executed.gateCount
  omega

theorem gain_iff_local_gain (executed : SplicedProgram carrier records raw) :
    executed.result.implementation.gateCount < carrier.implementation.gateCount ↔
      executed.program.result.implementation.gateCount <
        (extractTerminalSupport carrier.exposed.candidate records).gateCount := by
  have partition :
      (extractTerminalSupport carrier.exposed.candidate records).gateCount +
        (ArbitrarySupportSplice.exterior records).length = carrier.implementation.gateCount :=
    ArbitrarySupportSplice.exterior_accounting carrier.exposed.candidate records
  have finalCount := executed.gateCount
  constructor <;> intro inequality <;> omega

theorem gain_iff_net_charges (executed : SplicedProgram carrier records raw) :
    executed.result.implementation.gateCount < carrier.implementation.gateCount ↔
      executed.program.execution.charged < executed.program.execution.removed := by
  have accounting := executed.charge_accounting
  constructor <;> intro inequality <;> omega

theorem strictGain (executed : SplicedProgram carrier records raw)
    (smaller : executed.program.result.implementation.gateCount <
      (extractTerminalSupport carrier.exposed.candidate records).gateCount) :
    StrictEquivalentGain carrier.implementation executed.result.implementation :=
  ⟨executed.gain_iff_local_gain.mpr smaller, executed.output⟩

theorem strictResidualDescent (executed : SplicedProgram carrier records raw)
    (smaller : executed.program.result.implementation.gateCount <
      (extractTerminalSupport carrier.exposed.candidate records).gateCount) :
    residualSlack executed.result.implementation < residualSlack carrier.implementation :=
  (executed.strictGain smaller).strictResidualDescent

end SplicedProgram

/-- The outer compiler consumes the complete source-derived, finally closed run. -/
def compile (raw : List RawEvent) : Option (SplicedProgram carrier records raw) :=
  match programAt : WireOpenProgram.compile (localSource carrier records) raw with
  | none => none
  | some program =>
      match compiledAt : ArbitrarySupportSplice.compile carrier.exposed.candidate records
          (fieldCandidate program.result) with
      | none => none
      | some compiled => some ⟨program, programAt, compiled, compiledAt⟩

theorem compile_complete (raw : List RawEvent)
    (program : CompiledProgram (localSource carrier records) raw)
    (programAt : WireOpenProgram.compile (localSource carrier records) raw = some program) :
    ∃ executed, compile carrier records raw = some executed ∧ executed.program = program := by
  unfold compile
  split
  · rename_i rejected
    have impossible := rejected.symm.trans programAt
    cases impossible
  · rename_i actual actualAt
    have same : actual = program := Option.some.inj (actualAt.symm.trans programAt)
    cases same
    obtain ⟨compiled, compiledAt⟩ := program_compiles carrier records program
    split
    · rename_i rejected
      have impossible := rejected.symm.trans compiledAt
      cases impossible
    · exact ⟨_, rfl, rfl⟩

/-- No extra rank, owner map, order or acyclicity premise is needed for embedding. -/
theorem compile_exists_iff (raw : List RawEvent) :
    (∃ executed, compile carrier records raw = some executed) ↔
      ∃ program, WireOpenProgram.compile (localSource carrier records) raw = some program := by
  constructor
  · rintro ⟨executed, _accepted⟩
    exact ⟨executed.program, executed.programAt⟩
  · rintro ⟨program, programAt⟩
    obtain ⟨executed, accepted, _same⟩ := compile_complete carrier records raw program programAt
    exact ⟨executed, accepted⟩

theorem compile_none_iff (raw : List RawEvent) :
    compile carrier records raw = none ↔
      WireOpenProgram.compile (localSource carrier records) raw = none := by
  constructor
  · intro rejected
    cases programAt : WireOpenProgram.compile (localSource carrier records) raw with
    | none => rfl
    | some program =>
        obtain ⟨executed, accepted, _same⟩ := compile_complete carrier records raw program programAt
        have impossible := rejected.symm.trans accepted
        cases impossible
  · intro rejected
    unfold compile
    split
    · rfl
    · rename_i program programAt
      have impossible := programAt.symm.trans rejected
      cases impossible

end PNP.DirectWire.WireOpenProperSupport
