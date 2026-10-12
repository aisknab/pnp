/-
Copyright (c) 2026 PNP Labs.

The complete A-row iteration emits both labelled entries at the actual
runtime ordinal. Its cost excludes the previously accumulated output.
-/
import PNP.Concrete.NormalizerSystemRowsLoop

namespace PNP.Concrete.NormalizerBlocks.SystemRows
open BitRegister Occurrence
attribute [local irreducible] Coefficient.entry

def advance : Block 29 := .seq (.action (.pop 25)) (.action (.push 26 true))
def advanced (r : State) : State :=
  {r with remaining := r.remaining.tail,counter := true::r.counter}
theorem advance_exec (r : State) : Exec advance r.store 2 (advanced r).store :=
  Exec.seq (.action _ _) (.action _ _)
theorem advanced_shared (r : State) : (advanced r).shared = r.shared := rfl

def emitBound (routine : Coefficient.Routine) : NatPolynomial :=
  .add (.linear 4 24) (.mul (.constant 5) routine.bound)
theorem emit_bound (routine : Coefficient.Routine) (r : State) (n : Nat)
    (fixed : r.shared.Bounded n) (index : r.counter.length ≤ n) :
    emitFuel routine r ≤ (emitBound routine).eval n := by
  have cost := emitFuel_bound routine r n fixed index
  change emitFuel routine r ≤ (4*n+24)+5*routine.bound.eval n
  omega

def aBlock : Block 29 :=
  .seq (emit (Coefficient.entry false)) (.seq (emit (Coefficient.entry true)) advance)
def aResult (r : State) : State :=
  advanced (emitted (Coefficient.entry true) (emitted (Coefficient.entry false) r))
def aFuel (r : State) : Nat :=
  emitFuel (Coefficient.entry false) r +
    (emitFuel (Coefficient.entry true) (emitted (Coefficient.entry false) r) + 2)
def aBound : NatPolynomial :=
  .add (emitBound (Coefficient.entry false))
    (.add (emitBound (Coefficient.entry true)) (.constant 2))
theorem a_exec (r : State) : Exec aBlock r.store (aFuel r) (aResult r).store :=
  Exec.seq (emit_exec _ r) (Exec.seq (emit_exec _ _) (advance_exec _))
theorem a_shared (r : State) : (aResult r).shared = r.shared :=
  (emitted_shared _ (Coefficient.entry_data true) _).trans
    (emitted_shared _ (Coefficient.entry_data false) r)
theorem a_frame (r : State) :
    (aResult r).rows = r.rows ∧ (aResult r).remaining = r.remaining.tail ∧
    (aResult r).counter = true::r.counter := ⟨rfl,rfl,rfl⟩
theorem a_fuel_bound (r : State) (n : Nat)
    (fixed : r.shared.Bounded n) (index : r.counter.length ≤ n) :
    aFuel r ≤ aBound.eval n := by
  have first := emit_bound (Coefficient.entry false) r n fixed index
  have nextFixed : (emitted (Coefficient.entry false) r).shared.Bounded n := by
    rw [emitted_shared _ (Coefficient.entry_data false)]
    exact fixed
  have second := emit_bound (Coefficient.entry true) (emitted (Coefficient.entry false) r) n nextFixed index
  change emitFuel (Coefficient.entry false) r +
    (emitFuel (Coefficient.entry true) (emitted (Coefficient.entry false) r) + 2) ≤
      (emitBound (Coefficient.entry false)).eval n + ((emitBound (Coefficient.entry true)).eval n+2)
  omega
def aIteration : Iteration where
  block := aBlock
  result := aResult
  fuel := aFuel
  bound := aBound
  exec := a_exec
  shared := a_shared
  rows r := (a_frame r).1
  remaining r := (a_frame r).2.1
  counter r := (a_frame r).2.2
  cost := a_fuel_bound

theorem a_whole_exec (r : State) :
    Exec (loop aIteration) r.store (whole aIteration r).fuel (whole aIteration r).state.store :=
  whole_exec aIteration r
theorem a_scan_bound (word : BitString) (r : State) (n : Nat)
    (fixed : r.shared.Bounded n) (budget : r.counter.length + word.length ≤ n) :
    (scan aIteration word r).fuel ≤ word.length*(1+aBound.eval n)+1 :=
  scan_fuel_bound aIteration word r n fixed budget

end PNP.Concrete.NormalizerBlocks.SystemRows
