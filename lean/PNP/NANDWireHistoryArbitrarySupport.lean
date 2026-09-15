/-
Copyright (c) 2026 PNP Labs.

One-copy literal arbitrary-support replacement after actual closed R5/R6/R8
histories. Extraction supplies computational fields, not protected duplicate
outputs. The history and physical normalizer derive causal bounds; the existing
literal compiler then computes an order without an acyclicity certificate.

This covers the existing history language and three-pass physical normalizer,
not all manuscript rules, full-profile compatibility, complete Package E,
global ZeroSlack or polynomial PCCMin.
-/

import PNP.NANDWireHistoryCausalBounds

namespace PNP.DirectWire.WireHistoryArbitrarySupport

open WireObligationHistory

/-- Expose exactly the computational fields as the replacement's interface word. -/
def fieldCandidate {inputs fields : Nat} (carrier : WireCarrier inputs 0 fields) :
    Candidate inputs carrier.implementation.gateCount fields :=
  Candidate.ofDirectWireWord carrier.implementation.candidate.program ⟨carrier.source⟩

theorem fieldCandidate_semantics {inputs fields : Nat}
    (carrier : WireCarrier inputs 0 fields) (valuation : Valuation inputs)
    (field : Fin fields) :
    (fieldCandidate carrier).semantics valuation field = carrier.fieldValue valuation field := by
  unfold fieldCandidate
  rw [Candidate.ofDirectWireWord_semantics]
  rfl

theorem fieldCandidate_outputLevel {inputs fields : Nat}
    (carrier : WireCarrier inputs 0 fields) (labels : Fin inputs → Nat)
    (field : Fin fields) :
    CausalBound.outputLevel (fieldCandidate carrier) labels field =
      carrier.fieldLevel labels field := by
  unfold fieldCandidate CausalBound.outputLevel
  rw [Candidate.ofDirectWireWord_pointwise]
  rfl

variable {inputs gates outputs profileWidth : Nat}
variable (candidate : Candidate inputs gates outputs)
variable (records : List (TerminalPrimitiveRecord inputs gates outputs profileWidth))

/-- All extracted observations are actual fields. There are no duplicate ordinary
outputs to protect a forgotten field from the existing physical normalizer. -/
def extractedCarrier :
    WireCarrier (terminalBoundaryPorts candidate.program records).length 0
      (terminalInterfacePorts candidate records).length :=
  let extracted := (extractTerminalSupport candidate records).extractedCandidate
  { implementation :=
      (Candidate.ofDirectWireWord extracted.program ⟨Fin.elim0⟩).toImplementation
    source := extracted.directWireWord.source }

theorem extractedCarrier_gateCount :
    (extractedCarrier candidate records).implementation.gateCount =
      (extractTerminalSupport candidate records).gateCount := rfl

theorem extractedCarrier_fieldValue
    (valuation : Valuation (terminalBoundaryPorts candidate.program records).length)
    (field : Fin (terminalInterfacePorts candidate records).length) :
    (extractedCarrier candidate records).fieldValue valuation field =
      (extractTerminalSupport candidate records).extractedCandidate.semantics valuation field := rfl

variable {raw : List (RawEvent (terminalInterfacePorts candidate records).length)}

/-- Every final field retains the extracted source's complete Boolean meaning. -/
theorem closedHistory_equivalent
    (history : ClosedHistory (extractedCarrier candidate records) raw) :
    (fieldCandidate history.state.current).semantics =
      (extractTerminalSupport candidate records).extractedCandidate.semantics := by
  funext valuation field
  exact (fieldCandidate_semantics history.state.current valuation field).trans
    ((history.full_field valuation field).trans
      (extractedCarrier_fieldValue candidate records valuation field))

/-- Causality is derived from the actual extracted program and actual execution.
Neither equivalence nor a supplied rank stands in for this proof. -/
theorem closedHistory_causalInterfaceBound
    (history : ClosedHistory (extractedCarrier candidate records) raw) :
    ArbitrarySupportSplice.CausalInterfaceBound candidate records
      (fieldCandidate history.state.current) := by
  intro field
  calc
    CausalBound.outputLevel (fieldCandidate history.state.current)
        (ArbitrarySupportSplice.causalBoundaryLabels candidate records) field =
        history.state.current.fieldLevel
          (ArbitrarySupportSplice.causalBoundaryLabels candidate records) field :=
      fieldCandidate_outputLevel _ _ _
    _ ≤ (extractedCarrier candidate records).fieldLevel
        (ArbitrarySupportSplice.causalBoundaryLabels candidate records) field :=
      history.field_causal_bound _ field
    _ = terminalExtractedInterfaceCausalLevel candidate records
        (fun _ => 0) (fun index => index.val + 1) field := rfl
    _ ≤ ((terminalInterfacePorts candidate records).get field).val + 1 :=
      extractTerminalSupport_causal_index candidate records field

/-- Every closed executed history admits the literal one-copy splice. -/
theorem closedHistory_compiles
    (history : ClosedHistory (extractedCarrier candidate records) raw) :
    ∃ compiled, ArbitrarySupportSplice.compile candidate records
      (fieldCandidate history.state.current) = some compiled :=
  ArbitrarySupportSplice.compile_of_causalInterfaceBound candidate records _
    (closedHistory_causalInterfaceBound candidate records history)

theorem closedHistory_result_semantics
    (history : ClosedHistory (extractedCarrier candidate records) raw)
    (compiled : CompiledRawNandGraph
      (ArbitrarySupportSplice.graph candidate records (fieldCandidate history.state.current)))
    (valuation : Valuation inputs) (output : Fin outputs) :
    (ArbitrarySupportSplice.result candidate records
      (fieldCandidate history.state.current) compiled).semantics valuation output =
        candidate.semantics valuation output :=
  ArbitrarySupportSplice.result_semantics candidate records _
    (closedHistory_equivalent candidate records history) compiled valuation output

/-- All restored materializers are charged; the retained exterior occurs only once. -/
theorem closedHistory_result_exact_accounting
    (history : ClosedHistory (extractedCarrier candidate records) raw)
    (compiled : CompiledRawNandGraph
      (ArbitrarySupportSplice.graph candidate records (fieldCandidate history.state.current))) :
    (ArbitrarySupportSplice.result candidate records
      (fieldCandidate history.state.current) compiled).toImplementation.gateCount +
        history.execution.removed = gates + history.execution.charged := by
  have spliceCount := ArbitrarySupportSplice.result_exact_accounting candidate records
    (fieldCandidate history.state.current) compiled
  have historyCount := history.gate_balance
  rw [extractedCarrier_gateCount] at historyCount
  omega

theorem closedHistory_result_strict_gain
    (history : ClosedHistory (extractedCarrier candidate records) raw)
    (gain : history.execution.charged < history.execution.removed)
    (compiled : CompiledRawNandGraph
      (ArbitrarySupportSplice.graph candidate records (fieldCandidate history.state.current))) :
    (ArbitrarySupportSplice.result candidate records
      (fieldCandidate history.state.current) compiled).toImplementation.gateCount < gates := by
  have counted := closedHistory_result_exact_accounting candidate records history compiled
  omega

/-- Execute the raw history, then compute a literal physical splice. No proof,
replacement candidate, graph, topological order or rank is a constructor input. -/
def compile (raw : List (RawEvent (terminalInterfacePorts candidate records).length)) :
    Option (Implementation inputs outputs) :=
  match compileHistory (extractedCarrier candidate records) raw with
  | none => none
  | some history =>
      (ArbitrarySupportSplice.compile candidate records
        (fieldCandidate history.state.current)).map fun compiled =>
          (ArbitrarySupportSplice.result candidate records
            (fieldCandidate history.state.current) compiled).toImplementation

theorem compile_complete
    (history : ClosedHistory (extractedCarrier candidate records) raw)
    (executed : compileHistory (extractedCarrier candidate records) raw = some history) :
    ∃ result, compile candidate records raw = some result := by
  obtain ⟨compiled, compiledAt⟩ := closedHistory_compiles candidate records history
  unfold compile
  rw [executed]
  dsimp only
  rw [compiledAt]
  exact ⟨_, rfl⟩

/-- A successful constructor preserves all original outputs and the full physical
charge/removal balance of its own computed history. -/
theorem compile_sound
    (result : Implementation inputs outputs)
    (accepted : compile candidate records raw = some result) :
    ∃ history : ClosedHistory (extractedCarrier candidate records) raw,
      compileHistory (extractedCarrier candidate records) raw = some history ∧
      result.gateCount + history.execution.removed = gates + history.execution.charged ∧
      (∀ valuation output, result.candidate.semantics valuation output =
        candidate.semantics valuation output) := by
  cases executed : compileHistory (extractedCarrier candidate records) raw with
  | none =>
      unfold compile at accepted
      rw [executed] at accepted
      cases accepted
  | some history =>
      obtain ⟨compiled, compiledAt⟩ := closedHistory_compiles candidate records history
      unfold compile at accepted
      rw [executed] at accepted
      dsimp only at accepted
      rw [compiledAt] at accepted
      have same : (ArbitrarySupportSplice.result candidate records
          (fieldCandidate history.state.current) compiled).toImplementation = result :=
        Option.some.inj accepted
      subst result
      exact ⟨history, rfl,
        closedHistory_result_exact_accounting candidate records history compiled,
        closedHistory_result_semantics candidate records history compiled⟩

/-- The second compilation stage adds no rejection of a valid closed history. -/
theorem compile_none_iff :
    compile candidate records raw = none ↔
      compileHistory (extractedCarrier candidate records) raw = none := by
  constructor
  · intro failed
    cases executed : compileHistory (extractedCarrier candidate records) raw with
    | none => rfl
    | some history =>
        obtain ⟨result, found⟩ := compile_complete candidate records history executed
        rw [failed] at found
        cases found
  · intro failed
    unfold compile
    rw [failed]

end PNP.DirectWire.WireHistoryArbitrarySupport
