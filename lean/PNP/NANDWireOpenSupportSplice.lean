/-
Copyright (c) 2026 PNP Labs.

Transport an actual ambient open-obligation state through a source-derived
support splice. Pending creations keep their exact captured carriers and full
values; the splice itself neither creates nor discharges them. Charges and
removals come from the complete actual local program.

This internal bridge is not the complete mixed-program compiler, full manuscript
profiles, complete Package E, global ZeroSlack or polynomial PCCMin.
-/

import PNP.NANDWireDescendantCertificate

namespace PNP.DirectWire.WireOpenSupportSplice

open WireObligationHistory WireDescendantProperSupport

variable {inputs outputs fields : Nat}
variable {source : WireCarrier inputs outputs fields}
variable (before : State source)
variable (records : List (TerminalPrimitiveRecord inputs
  before.current.implementation.gateCount (outputs + fields) 0))
variable {stages : List WireDescendantHistory.RawStage}

/-- The pending function is retained literally, including every actual snapshot. -/
def transfer (executed : SplicedRun before.current records stages) : State source where
  current := executed.result
  pending := before.pending
  charged := before.charged + executed.run.chargedCount
  removed := before.removed + executed.run.removedCount
  output := fun valuation output =>
    (executed.output valuation output).trans (before.output valuation output)
  available := fun valuation field closed =>
    (executed.field valuation field).trans (before.available valuation field closed)
  balance := by
    have ambient := executed.charge_accounting
    have prior := before.balance
    omega

theorem transfer_pending (executed : SplicedRun before.current records stages) :
    (transfer before records executed).pending = before.pending := rfl

theorem transfer_keep (executed : SplicedRun before.current records stages) :
    (transfer before records executed).keep = before.keep := rfl

theorem transfer_snapshot (executed : SplicedRun before.current records stages)
    (field : Fin fields) (snapshot : Snapshot source field) :
    (transfer before records executed).pending field = some snapshot ↔
      before.pending field = some snapshot := Iff.rfl

theorem transfer_charge (executed : SplicedRun before.current records stages) :
    (transfer before records executed).charged =
      before.charged + executed.run.chargedCount := rfl

theorem transfer_removal (executed : SplicedRun before.current records stages) :
    (transfer before records executed).removed =
      before.removed + executed.run.removedCount := rfl

theorem transfer_output (executed : SplicedRun before.current records stages)
    (valuation : Valuation inputs) (output : Fin outputs) :
    (transfer before records executed).current.implementation.candidate.semantics
        valuation output = source.implementation.candidate.semantics valuation output :=
  (transfer before records executed).output valuation output

theorem transfer_available (executed : SplicedRun before.current records stages)
    (valuation : Valuation inputs) (field : Fin fields)
    (available : before.pending field = none) :
    (transfer before records executed).current.fieldValue valuation field =
      source.fieldValue valuation field :=
  (transfer before records executed).available valuation field available

theorem transfer_balance (executed : SplicedRun before.current records stages) :
    (transfer before records executed).current.implementation.gateCount +
        (transfer before records executed).removed =
      source.implementation.gateCount + (transfer before records executed).charged :=
  (transfer before records executed).balance

/-- Arbitrary input labels are transported through the actual complete local run. -/
theorem replacement_dependency_bound
    (executed : SplicedRun before.current records stages) (labels : Fin inputs → Nat) :
    ArbitrarySupportSplice.DependencyInterfaceBound before.current.exposed.candidate records
      executed.run.result.candidate labels := by
  intro observation
  calc
    CausalBound.outputLevel executed.run.result.candidate
        (ArbitrarySupportSplice.dependencyBoundaryLabels
          before.current.exposed.candidate records labels) observation ≤
        CausalBound.outputLevel (localSource before.current records).candidate
          (ArbitrarySupportSplice.dependencyBoundaryLabels
            before.current.exposed.candidate records labels) observation :=
      executed.run.output_dependency_bound _ observation
    _ = terminalExtractedInterfaceCausalLevel before.current.exposed.candidate records labels
        (CausalBound.levels before.current.exposed.candidate.program labels) observation := rfl
    _ ≤ CausalBound.levels before.current.exposed.candidate.program labels
        ((terminalInterfacePorts before.current.exposed.candidate records).get observation) :=
      extractTerminalSupport_causal_levels before.current.exposed.candidate records labels observation

/-- The bound concerns the actual one-copy compiled word, not an equivalent surrogate. -/
theorem result_exposed_dependency_bound
    (executed : SplicedRun before.current records stages) (labels : Fin inputs → Nat)
    (observation : Fin (outputs + fields)) :
    CausalBound.outputLevel executed.result.exposed.candidate labels observation ≤
      CausalBound.outputLevel before.current.exposed.candidate labels observation := by
  unfold WireDescendantProperSupport.SplicedRun.result WireCarrier.spliceResult
  rw [WireCarrier.exposed_unpack]
  exact ArbitrarySupportSplice.result_output_dependency_bound
    before.current.exposed.candidate records executed.run.result.candidate labels
    (replacement_dependency_bound before records executed labels)
    executed.compiled executed.compiledAt observation

theorem result_causal_bounds
    (executed : SplicedRun before.current records stages) (labels : Fin inputs → Nat) :
    SourceCausalBounds before.current executed.result labels := by
  constructor
  · intro output
    simpa only [WireCarrier.exposed_output_level] using
      result_exposed_dependency_bound before records executed labels (Fin.castAdd fields output)
  · intro field
    simpa only [WireCarrier.exposed_field_level] using
      result_exposed_dependency_bound before records executed labels (Fin.natAdd outputs field)

/-- Current bounds compose; every pending snapshot is literally the same object. -/
theorem transfer_causal_invariant
    (executed : SplicedRun before.current records stages) (labels : Fin inputs → Nat)
    (bounded : before.CausalInvariant labels) :
    (transfer before records executed).CausalInvariant labels := by
  have localBounds := result_causal_bounds before records executed labels
  exact ⟨⟨fun output => Nat.le_trans (localBounds.1 output) (bounded.1.1 output),
    fun field => Nat.le_trans (localBounds.2 field) (bounded.1.2 field)⟩, bounded.2⟩

variable (raw : WireDescendantCertificate.RawCertificate)

/-- Decode and compiler receipts retain the complete raw support/program input. -/
structure Receipt where
  records : List (TerminalPrimitiveRecord inputs
    before.current.implementation.gateCount (outputs + fields) 0)
  recordsAt : WireDescendantHistory.decodeRecords inputs before.current.implementation.gateCount
    (outputs + fields) 0 raw.records = some records
  executed : SplicedRun before.current records raw.stages
  executedAt : WireDescendantProperSupport.compile before.current records raw.stages = some executed

namespace Receipt

variable {before raw}

def next (receipt : Receipt before raw) : State source :=
  transfer before receipt.records receipt.executed

theorem pending (receipt : Receipt before raw) : receipt.next.pending = before.pending := rfl

theorem records_source (receipt : Receipt before raw) :
    receipt.records.map WireDescendantHistory.encodeRecord = raw.records :=
  WireDescendantHistory.decodeRecords_source inputs before.current.implementation.gateCount
    (outputs + fields) 0 raw.records receipt.records receipt.recordsAt

end Receipt

/-- Splice execution does not require or pretend that the ambient ledger is closed. -/
def execute : Option (Receipt before raw) :=
  match recordsAt : WireDescendantHistory.decodeRecords inputs
      before.current.implementation.gateCount (outputs + fields) 0 raw.records with
  | none => none
  | some records =>
      match executedAt : WireDescendantProperSupport.compile before.current records raw.stages with
      | none => none
      | some executed => some ⟨records, recordsAt, executed, executedAt⟩

theorem execute_of_compiled
    (records : List (TerminalPrimitiveRecord inputs
      before.current.implementation.gateCount (outputs + fields) 0))
    (recordsAt : WireDescendantHistory.decodeRecords inputs
      before.current.implementation.gateCount (outputs + fields) 0 raw.records = some records)
    (executed : SplicedRun before.current records raw.stages)
    (executedAt : WireDescendantProperSupport.compile before.current records raw.stages = some executed) :
    ∃ receipt, execute before raw = some receipt := by
  unfold execute
  split
  · rename_i rejected
    have impossible := rejected.symm.trans recordsAt
    cases impossible
  · rename_i actual actualAt
    have sameRecords : actual = records := Option.some.inj (actualAt.symm.trans recordsAt)
    cases sameRecords
    split
    · rename_i rejected
      have impossible := rejected.symm.trans executedAt
      cases impossible
    · exact ⟨_, rfl⟩

/-- Successful complete local execution derives the outer splice; no extra
correctness or acyclicity certificate is supplied. -/
theorem execute_exists_iff :
    (∃ receipt, execute before raw = some receipt) ↔
      ∃ records, WireDescendantHistory.decodeRecords inputs
        before.current.implementation.gateCount (outputs + fields) 0 raw.records = some records ∧
        ∃ run, WireDescendantHistory.compile (localSource before.current records) raw.stages =
          some run := by
  constructor
  · rintro ⟨receipt, _accepted⟩
    exact ⟨receipt.records, receipt.recordsAt, receipt.executed.run, receipt.executed.runAt⟩
  · rintro ⟨records, recordsAt, run, runAt⟩
    obtain ⟨executed, executedAt, _sameRun⟩ :=
      WireDescendantProperSupport.compile_complete before.current records raw.stages run runAt
    exact execute_of_compiled before raw records recordsAt executed executedAt

end PNP.DirectWire.WireOpenSupportSplice
