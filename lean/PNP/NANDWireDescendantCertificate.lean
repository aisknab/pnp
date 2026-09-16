/-
Copyright (c) 2026 PNP Labs.

Source-only proper-support certificates for arbitrary descendant programs.
Decode the complete offered support, execute the complete local program, derive
the literal outer splice, and check proper physical support and strict final
saving. Intermediate stages may grow. All receipts are constructed internally.

This verifier does not find a successful certificate for every nonminimal input.
It does not supply full manuscript profiles, all rule families, global routing,
unconditional ZeroSlack or polynomial runtime/certificate-size bounds.
-/

import PNP.NANDWireDescendantProperSupport

namespace PNP.DirectWire.WireDescendantCertificate

open WireDescendantHistory WireDescendantProperSupport

/-- Only finite raw coordinates and actions are supplied, never correctness,
intermediate implementations, charge totals, owner maps or a wiring order. -/
structure RawCertificate where
  records : List RawRecord
  stages : List RawStage
  deriving Repr, DecidableEq

variable {inputs outputs fields : Nat}
variable (carrier : WireCarrier inputs outputs fields) (raw : RawCertificate)

/-- A receipt built by the verifier from the actual source and complete input. -/
structure CheckedCertificate where
  records : List (TerminalPrimitiveRecord inputs
    carrier.implementation.gateCount (outputs + fields) 0)
  recordsAt : decodeRecords inputs carrier.implementation.gateCount
    (outputs + fields) 0 raw.records = some records
  executed : SplicedRun carrier records raw.stages
  executedAt : WireDescendantProperSupport.compile carrier records raw.stages = some executed
  proper : 0 < (ArbitrarySupportSplice.exterior records).length
  smaller : executed.run.result.gateCount <
    (extractTerminalSupport carrier.exposed.candidate records).gateCount

namespace CheckedCertificate

variable {carrier raw}

/-- The actual compiled and rebound carrier, not a separately supplied result. -/
def result (checked : CheckedCertificate carrier raw) : WireCarrier inputs outputs fields :=
  checked.executed.result

theorem records_source (checked : CheckedCertificate carrier raw) :
    checked.records.map encodeRecord = raw.records :=
  decodeRecords_source inputs carrier.implementation.gateCount
    (outputs + fields) 0 raw.records checked.records checked.recordsAt

theorem proper_support (checked : CheckedCertificate carrier raw) :
    (extractTerminalSupport carrier.exposed.candidate checked.records).gateCount <
      carrier.implementation.gateCount :=
  (proper_iff_exterior_positive carrier checked.records).mpr checked.proper

theorem output (checked : CheckedCertificate carrier raw)
    (valuation : Valuation inputs) (index : Fin outputs) :
    checked.result.implementation.candidate.semantics valuation index =
      carrier.implementation.candidate.semantics valuation index :=
  checked.executed.output valuation index

theorem field (checked : CheckedCertificate carrier raw)
    (valuation : Valuation inputs) (index : Fin fields) :
    checked.result.fieldValue valuation index = carrier.fieldValue valuation index :=
  checked.executed.field valuation index

theorem gateCount (checked : CheckedCertificate carrier raw) :
    checked.result.implementation.gateCount =
      (ArbitrarySupportSplice.exterior checked.records).length +
        checked.executed.run.result.gateCount :=
  checked.executed.gateCount

theorem charge_accounting (checked : CheckedCertificate carrier raw) :
    checked.result.implementation.gateCount + checked.executed.run.removedCount =
      carrier.implementation.gateCount + checked.executed.run.chargedCount :=
  checked.executed.charge_accounting

theorem strictGain (checked : CheckedCertificate carrier raw) :
    StrictEquivalentGain carrier.implementation checked.result.implementation :=
  checked.executed.strictGain checked.smaller

theorem strictResidualDescent (checked : CheckedCertificate carrier raw) :
    residualSlack checked.result.implementation < residualSlack carrier.implementation :=
  checked.strictGain.strictResidualDescent

end CheckedCertificate

/-- Fail closed on any invalid coordinate, failed complete program, whole
physical support or final nondecrease. Outer compilation is source-derived. -/
def verify : Option (CheckedCertificate carrier raw) :=
  match recordsAt : decodeRecords inputs carrier.implementation.gateCount
      (outputs + fields) 0 raw.records with
  | none => none
  | some records =>
      match executedAt : WireDescendantProperSupport.compile carrier records raw.stages with
      | none => none
      | some executed =>
          if proper : 0 < (ArbitrarySupportSplice.exterior records).length then
            if smaller : executed.run.result.gateCount <
                (extractTerminalSupport carrier.exposed.candidate records).gateCount then
              some ⟨records, recordsAt, executed, executedAt, proper, smaller⟩
            else none
          else none

private theorem verify_of_executed
    (records : List (TerminalPrimitiveRecord inputs
      carrier.implementation.gateCount (outputs + fields) 0))
    (recordsAt : decodeRecords inputs carrier.implementation.gateCount
      (outputs + fields) 0 raw.records = some records)
    (executed : SplicedRun carrier records raw.stages)
    (executedAt : WireDescendantProperSupport.compile carrier records raw.stages = some executed)
    (proper : 0 < (ArbitrarySupportSplice.exterior records).length)
    (smaller : executed.run.result.gateCount <
      (extractTerminalSupport carrier.exposed.candidate records).gateCount) :
    ∃ checked, verify carrier raw = some checked := by
  unfold verify
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
    · rename_i actual actualAt
      have sameExecuted : actual = executed := Option.some.inj (actualAt.symm.trans executedAt)
      cases sameExecuted
      rw [dif_pos proper, dif_pos smaller]
      exact ⟨_, rfl⟩

/-- Complete acceptance needs only decoding, actual program execution,
properness and final saving. No extra successful-splice certificate is supplied. -/
theorem verify_complete
    (records : List (TerminalPrimitiveRecord inputs
      carrier.implementation.gateCount (outputs + fields) 0))
    (recordsAt : decodeRecords inputs carrier.implementation.gateCount
      (outputs + fields) 0 raw.records = some records)
    (run : CompiledRun (localSource carrier records) raw.stages)
    (runAt : WireDescendantHistory.compile (localSource carrier records) raw.stages = some run)
    (proper : 0 < (ArbitrarySupportSplice.exterior records).length)
    (smaller : run.result.gateCount <
      (extractTerminalSupport carrier.exposed.candidate records).gateCount) :
    ∃ checked, verify carrier raw = some checked := by
  obtain ⟨executed, executedAt, sameRun⟩ :=
    WireDescendantProperSupport.compile_complete carrier records raw.stages run runAt
  have finalSaving : executed.run.result.gateCount <
      (extractTerminalSupport carrier.exposed.candidate records).gateCount := by
    rw [sameRun]
    exact smaller
  exact verify_of_executed carrier raw records recordsAt executed executedAt proper finalSaving

/-- Exact source-only acceptance boundary for arbitrary dimensions and programs. -/
theorem verify_exists_iff :
    (∃ checked, verify carrier raw = some checked) ↔
      ∃ records, decodeRecords inputs carrier.implementation.gateCount
        (outputs + fields) 0 raw.records = some records ∧
        ∃ run : CompiledRun (localSource carrier records) raw.stages,
          WireDescendantHistory.compile (localSource carrier records) raw.stages = some run ∧
          0 < (ArbitrarySupportSplice.exterior records).length ∧
          run.result.gateCount <
            (extractTerminalSupport carrier.exposed.candidate records).gateCount := by
  constructor
  · rintro ⟨checked, _accepted⟩
    exact ⟨checked.records, checked.recordsAt, checked.executed.run,
      checked.executed.runAt, checked.proper, checked.smaller⟩
  · rintro ⟨records, recordsAt, run, runAt, proper, smaller⟩
    exact verify_complete carrier raw records recordsAt run runAt proper smaller

/-- The returned witness preserves both observation classes and all historical
costs, and proves a genuine gain on a proper physical support. -/
theorem verify_sound (checked : CheckedCertificate carrier raw)
    (_accepted : verify carrier raw = some checked) :
    checked.records.map encodeRecord = raw.records ∧
      (extractTerminalSupport carrier.exposed.candidate checked.records).gateCount <
        carrier.implementation.gateCount ∧
      StrictEquivalentGain carrier.implementation checked.result.implementation ∧
      (∀ valuation field, checked.result.fieldValue valuation field =
        carrier.fieldValue valuation field) ∧
      checked.result.implementation.gateCount + checked.executed.run.removedCount =
        carrier.implementation.gateCount + checked.executed.run.chargedCount :=
  ⟨checked.records_source, checked.proper_support, checked.strictGain,
    checked.field, checked.charge_accounting⟩

theorem verify_decode_none
    (rejected : decodeRecords inputs carrier.implementation.gateCount
      (outputs + fields) 0 raw.records = none) :
    verify carrier raw = none := by
  unfold verify
  split
  · rfl
  · rename_i records recordsAt
    have impossible := recordsAt.symm.trans rejected
    cases impossible

theorem verify_run_none
    (records : List (TerminalPrimitiveRecord inputs
      carrier.implementation.gateCount (outputs + fields) 0))
    (recordsAt : decodeRecords inputs carrier.implementation.gateCount
      (outputs + fields) 0 raw.records = some records)
    (rejected : WireDescendantHistory.compile (localSource carrier records) raw.stages = none) :
    verify carrier raw = none := by
  cases accepted : verify carrier raw with
  | none => rfl
  | some checked =>
      have sameRecords : checked.records = records :=
        Option.some.inj (checked.recordsAt.symm.trans recordsAt)
      cases sameRecords
      have impossible := checked.executed.runAt.symm.trans rejected
      cases impossible

theorem verify_not_proper
    (records : List (TerminalPrimitiveRecord inputs
      carrier.implementation.gateCount (outputs + fields) 0))
    (recordsAt : decodeRecords inputs carrier.implementation.gateCount
      (outputs + fields) 0 raw.records = some records)
    (notProper : ¬ 0 < (ArbitrarySupportSplice.exterior records).length) :
    verify carrier raw = none := by
  cases accepted : verify carrier raw with
  | none => rfl
  | some checked =>
      have sameRecords : checked.records = records :=
        Option.some.inj (checked.recordsAt.symm.trans recordsAt)
      cases sameRecords
      exact (notProper checked.proper).elim

theorem verify_no_gain
    (records : List (TerminalPrimitiveRecord inputs
      carrier.implementation.gateCount (outputs + fields) 0))
    (recordsAt : decodeRecords inputs carrier.implementation.gateCount
      (outputs + fields) 0 raw.records = some records)
    (run : CompiledRun (localSource carrier records) raw.stages)
    (runAt : WireDescendantHistory.compile (localSource carrier records) raw.stages = some run)
    (notSmaller : ¬ run.result.gateCount <
      (extractTerminalSupport carrier.exposed.candidate records).gateCount) :
    verify carrier raw = none := by
  cases accepted : verify carrier raw with
  | none => rfl
  | some checked =>
      have sameRecords : checked.records = records :=
        Option.some.inj (checked.recordsAt.symm.trans recordsAt)
      cases sameRecords
      have sameRun : checked.executed.run = run :=
        Option.some.inj (checked.executed.runAt.symm.trans runAt)
      have smaller := checked.smaller
      rw [sameRun] at smaller
      exact (notSmaller smaller).elim

end PNP.DirectWire.WireDescendantCertificate
