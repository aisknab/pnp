/-
Copyright (c) 2026 PNP Labs.

Dispatch on the computed option-presence bit before stripping its payload.
The no-failure branch retains the entire checked state for later model
recovery; it is not asserted to be the final serialized output.
-/
import PNP.Concrete.NormalizerSourceAssemblyMigration

namespace PNP.Concrete.NormalizerBlocks.SourceAssembly
open BitRegister Occurrence

def failureBlock : Block 38 := .seq migrate.block SystemAssembly.block
def failureResult (r : State) : State := SystemAssembly.result (migrated r)
def failureSteps (r : State) : Nat := 7+SystemAssembly.fuel (migrated r)
def failureBound : NatPolynomial :=
  .add (.constant 7) (SystemAssembly.bound.substitute (.linear 1 7))
theorem failure_exec (r : State) :
    Exec failureBlock r.store (failureSteps r) (failureResult r).store :=
  Exec.seq (migrate_exec r) (SystemAssembly.block_exec (migrated r))
theorem failureSteps_bound (r : State) (n : Nat) (bounded : r.store.Bounded n) :
    failureSteps r ≤ failureBound.eval n := by
  have work := SystemAssembly.fuel_bound (migrated r) (n+7) (migrated_bounded r n bounded)
  change 7+SystemAssembly.fuel (migrated r) ≤ 7+(SystemAssembly.bound.substitute (.linear 1 7)).eval n
  rw [NatPolynomial.eval_substitute]
  change 7+SystemAssembly.fuel (migrated r) ≤ 7+SystemAssembly.bound.eval (1*n+7)
  rw [Nat.one_mul]
  exact Nat.add_le_add_left work 7
theorem failure_recovery (r : State) : (failureResult r).recovery = r.recovery :=
  (SystemAssembly.result_recovery (migrated r)).trans (migrated_frame r).2.1

def hasFailure (r : State) : Bool := r.registers.output.headD false
def dispatch : Block 38 := .branch 8 .skip .skip failureBlock
def dispatched (r : State) : State := if hasFailure r then failureResult r else r
def dispatchSteps (r : State) : Nat := 1+if hasFailure r then failureSteps r else 1
def dispatchBound : NatPolynomial := .add failureBound (.constant 2)
theorem dispatch_exec (r : State) :
    Exec dispatch r.store (dispatchSteps r) (dispatched r).store := by
  have checked := EdgeKinds.branch_head (8 : Fin 38) r.store .skip failureBlock
    1 (failureSteps r) r.store (failureResult r).store (Exec.skip r.store) (failure_exec r)
  change Exec dispatch r.store (1+if hasFailure r then failureSteps r else 1)
    (if hasFailure r then (failureResult r).store else r.store) at checked
  cases h : hasFailure r <;>
    simpa only [dispatched,dispatchSteps,h,Bool.false_eq_true,ite_false,ite_true] using checked
theorem dispatchSteps_bound (r : State) (n : Nat) (bounded : r.store.Bounded n) :
    dispatchSteps r ≤ dispatchBound.eval n := by
  have work := failureSteps_bound r n bounded
  change 1+(if hasFailure r then failureSteps r else 1) ≤ failureBound.eval n+2
  cases hasFailure r <;> simp only [Bool.false_eq_true,ite_false,ite_true] <;> omega
theorem dispatched_bounded (r : State) (n : Nat) (bounded : r.store.Bounded n) :
    (dispatched r).store.Bounded (n+dispatchBound.eval n) :=
  Store.bounded_mono ((dispatch_exec r).bounded n bounded)
    (Nat.add_le_add_left (dispatchSteps_bound r n bounded) n)
theorem dispatched_recovery (r : State) : (dispatched r).recovery = r.recovery := by
  unfold dispatched
  split
  · exact failure_recovery r
  · rfl
theorem answer_presence (value : Option Nat) :
    (TableOwner.answer value).headD false = value.isSome := by cases value <;> rfl
theorem dispatched_none (r : State) (output : r.registers.output = TableOwner.answer none) :
    dispatched r = r := by
  unfold dispatched hasFailure
  rw [output,answer_presence]
  rfl
theorem dispatched_some (r : State) (index : Nat)
    (output : r.registers.output = TableOwner.answer (some index)) :
    dispatched r = failureResult r := by
  unfold dispatched hasFailure
  rw [output,answer_presence]
  rfl

end PNP.Concrete.NormalizerBlocks.SourceAssembly
