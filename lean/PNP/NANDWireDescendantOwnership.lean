/-
Copyright (c) 2026 PNP Labs.

Derive persistent physical ownership for every complete accepted raw-stage
program. The fold starts with the original physical coordinates and advances
the actual compiler-position map at each computed stage index. Historical
charges and removals are retained across every descendant.

This is ownership for the existing closed computational-history language,
not full carrier compatibility, open-obligation transport, global routing,
unconditional ZeroSlack or polynomial PCCMin.
-/

import PNP.NANDWireDescendantRun
import PNP.NANDWireDescendantLedger

namespace PNP.DirectWire.WireDescendantHistory.CompiledRun

variable {inputs outputs initialGates : Nat}
variable {source : Implementation inputs outputs} {stage : RawStage} {stages : List RawStage}

/-- Internal fold interface. The public ledger below always supplies the
computed initial ledger and starts the traversal position at zero. -/
def carry {initialGates : Nat} {source : Implementation inputs outputs} {stages : List RawStage}
    (run : CompiledRun source stages) (position : Nat)
    (ledger : PersistentOwnership initialGates source.gateCount) :
    PersistentOwnership initialGates run.result.gateCount :=
  match run with
  | .nil _ => ledger
  | .cons first rest => rest.carry (position + 1) (ledger.advance position first)

theorem carry_nil (source : Implementation inputs outputs) (position : Nat)
    (ledger : PersistentOwnership initialGates source.gateCount) :
    (CompiledRun.nil source).carry position ledger = ledger := rfl

/-- Each fold step follows the preceding stage's actual computed map; it does
not restart ownership at the descendant's gate coordinates. -/
theorem carry_cons (first : StageCompilation source stage)
    (rest : CompiledRun first.result stages) (position : Nat)
    (ledger : PersistentOwnership initialGates source.gateCount) :
    (CompiledRun.cons first rest).carry position ledger =
      rest.carry (position + 1) (ledger.advance position first) := rfl

theorem carry_wellFormed (run : CompiledRun source stages) :
    ∀ (position : Nat) (ledger : PersistentOwnership initialGates source.gateCount),
      PersistentOwnership.WellFormed ledger position →
      PersistentOwnership.WellFormed (run.carry position ledger) (position + stages.length) := by
  induction run with
  | nil source =>
      intro position ledger checked
      simpa only [carry, result, List.length_nil, Nat.add_zero] using checked
  | @cons source stage stages first rest ih =>
      intro position ledger checked
      have reached := ih (position + 1) (ledger.advance position first)
        (ledger.advance_wellFormed position first checked)
      have sameBound : position + 1 + stages.length = position + (stage :: stages).length := by
        simp only [List.length_cons]
        omega
      rw [sameBound] at reached
      exact reached

theorem carry_charged_length (run : CompiledRun source stages) :
    ∀ (position : Nat) (ledger : PersistentOwnership initialGates source.gateCount),
      (run.carry position ledger).charged.length =
        ledger.charged.length + run.chargedCount := by
  induction run with
  | nil source => intro position ledger; rfl
  | cons first rest ih =>
      intro position ledger
      change (rest.carry (position + 1) (ledger.advance position first)).charged.length =
        ledger.charged.length + (first.chargedCount + rest.chargedCount)
      rw [ih, ledger.advance_charged_length position first]
      exact Nat.add_assoc _ _ _

theorem carry_removed_length (run : CompiledRun source stages) :
    ∀ (position : Nat) (ledger : PersistentOwnership initialGates source.gateCount),
      (run.carry position ledger).removed.length =
        ledger.removed.length + run.removedCount := by
  induction run with
  | nil source => intro position ledger; rfl
  | cons first rest ih =>
      intro position ledger
      change (rest.carry (position + 1) (ledger.advance position first)).removed.length =
        ledger.removed.length + (first.removedCount + rest.removedCount)
      rw [ih, ledger.advance_removed_length position first]
      exact Nat.add_assoc _ _ _

/-- A charge remains historical even when later stages remove its live gate. -/
theorem carry_charge_survives (run : CompiledRun source stages) :
    ∀ (position : Nat) (ledger : PersistentOwnership initialGates source.gateCount)
      (origin : DescendantOrigin initialGates), origin ∈ ledger.charged →
      origin ∈ (run.carry position ledger).charged := by
  induction run with
  | nil source => intro position ledger origin member; exact member
  | cons first rest ih =>
      intro position ledger origin member
      exact ih (position + 1) (ledger.advance position first) origin
        (List.mem_append_left _ member)

/-- Public source-derived ownership: no caller supplies the initial map,
stage counter, charges, removals or invariant. -/
def ledger (run : CompiledRun source stages) :
    PersistentOwnership source.gateCount run.result.gateCount :=
  run.carry 0 (PersistentOwnership.initial source.gateCount)

theorem ledger_nil (source : Implementation inputs outputs) :
    (CompiledRun.nil source).ledger = PersistentOwnership.initial source.gateCount := rfl

theorem ledger_wellFormed (run : CompiledRun source stages) :
    PersistentOwnership.WellFormed run.ledger stages.length := by
  simpa only [ledger, Nat.zero_add] using
    run.carry_wellFormed 0 (PersistentOwnership.initial source.gateCount)
      (PersistentOwnership.initial_wellFormed source.gateCount)

/-- Complete physical identity conservation for arbitrary source dimensions
and arbitrary finite accepted stage lists. Counts are the sums of the actual
existing stage executions, not definitions from these new ledger lengths. -/
theorem physical_ownership (run : CompiledRun source stages) :
    run.ledger.live.length = run.result.gateCount ∧
      run.ledger.charged.length = run.chargedCount ∧
      run.ledger.removed.length = run.removedCount ∧
      (run.ledger.live ++ run.ledger.removed).Nodup ∧
      (run.ledger.live ++ run.ledger.removed).Perm
        (originalOrigins source.gateCount ++ run.ledger.charged) := by
  have checked := run.ledger_wellFormed
  refine ⟨List.length_ofFn, ?_, ?_, checked.distinct, checked.conserved⟩
  · change (run.carry 0 (PersistentOwnership.initial source.gateCount)).charged.length = _
    rw [run.carry_charged_length]
    exact Nat.zero_add _
  · change (run.carry 0 (PersistentOwnership.initial source.gateCount)).removed.length = _
    rw [run.carry_removed_length]
    exact Nat.zero_add _

theorem ledger_origin_injective (run : CompiledRun source stages) :
    Function.Injective run.ledger.origin :=
  run.ledger.origin_injective stages.length run.ledger_wellFormed

theorem ledger_charged_before (run : CompiledRun source stages)
    (origin : DescendantOrigin source.gateCount) (member : origin ∈ run.ledger.charged) :
    createdBefore stages.length origin :=
  run.ledger_wellFormed.chargedBefore origin member

end PNP.DirectWire.WireDescendantHistory.CompiledRun
