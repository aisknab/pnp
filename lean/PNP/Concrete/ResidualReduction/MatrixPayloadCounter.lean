import PNP.Concrete.ResidualReduction.MatrixCountedPayload

/-! Literal construction of the payload countdown from the two unary headers.
Its size is the product of row width and row count, not a decoded coefficient
value. Both factors are bounded by encoded input length at the loader boundary,
so constructing this counter has an explicit quadratic, not hidden exponential,
cost. All other data registers are preserved. -/

namespace PNP.Concrete.ResidualReduction.MatrixPayloadCounter
open PNP.Concrete PNP.Concrete.BitRegister
open PNP.Concrete.NormalizerBlocks PNP.Concrete.NormalizerBlocks.Occurrence
open PNP.Concrete.ResidualReduction.MatrixReconstruction
open PNP.Concrete.ResidualReduction.MatrixStrictHeader

def addBody : Block 9 := .seq (.action (.push 2 true)) (.action (.pop 6))
def addLoop : Block 9 := .loop 6 addBody

theorem addLoop_exec (width : Nat) (r : Registers) :
    Exec addLoop ({r with active := List.replicate width true}).store (3 * width + 1)
      ({r with active := [], remaining := List.replicate width true ++ r.remaining}).store := by
  induction width generalizing r with
  | zero => exact Exec.loopStop rfl
  | succ width ih =>
    have step : Exec addBody ({r with active := List.replicate (width + 1) true}).store 2
        ({r with active := List.replicate width true, remaining := true :: r.remaining}).store :=
      Exec.seq (.action _ _) (.action _ _)
    have checked := Exec.loopStep (source := (6 : Fin 9)) rfl step
      (ih {r with remaining := true :: r.remaining})
    have cost : 3 * (width + 1) + 1 = 1 + (2 + (3 * width + 1)) := by omega
    rw [cost]
    simpa only [addLoop, replicate_push] using checked

def counted (width rows accumulated : Nat) (r : State) : State :=
  {r with core := {r.core with target := List.replicate width true, remaining := List.replicate accumulated true, active := []}, pending := List.replicate rows true}

def body : Block 12 :=
  .seq (.action (.copy 6 1)) (.seq (lift addLoop) (.action (.pop 11)))
def loop : Block 12 := .loop 11 body

theorem body_exec (width rows accumulated : Nat) (r : State) :
    Exec body (counted width (rows + 1) accumulated r).store (3 * width + 3)
      (counted width rows (width + accumulated) r).store := by
  let before := counted width (rows + 1) accumulated r
  let loaded := {before with core := {before.core with active := List.replicate width true}}
  let added := counted width (rows + 1) (width + accumulated) r
  have first : Exec (.action (.copy (6 : Fin 12) 1)) before.store 1 loaded.store := .action _ _
  have core : Exec addLoop loaded.core.store (3 * width + 1) added.core.store := by
    simpa only [loaded, before, added, counted, replicate_add] using
      addLoop_exec width before.core
  have second : Exec (lift addLoop) loaded.store (3 * width + 1) added.store :=
    lift_exec addLoop loaded _ added.core core
  have third : Exec (.action (.pop (11 : Fin 12))) added.store 1
      (counted width rows (width + accumulated) r).store := .action _ _
  have checked := Exec.seq first (Exec.seq second third)
  have cost : 3 * width + 3 = 1 + ((3 * width + 1) + 1) := by omega
  simpa only [body, before, cost] using checked

theorem loop_exec (width rows accumulated : Nat) (r : State) :
    Exec loop (counted width rows accumulated r).store ((3 * width + 4) * rows + 1)
      (counted width 0 (width * rows + accumulated) r).store := by
  induction rows generalizing accumulated with
  | zero => simpa only [loop, Nat.mul_zero, Nat.zero_add] using
      (Exec.loopStop (body := body) (show (counted width 0 accumulated r).store.get 11 = [] from rfl))
  | succ rows ih =>
    have step := body_exec width rows accumulated r
    have checked := Exec.loopStep (source := (11 : Fin 12)) rfl step (ih (width + accumulated))
    have amount : width * rows + (width + accumulated) = width * (rows + 1) + accumulated := by
      rw [Nat.mul_succ]
      omega
    rw [amount] at checked
    have cost : (3 * width + 4) * (rows + 1) + 1 =
        1 + ((3 * width + 3) + ((3 * width + 4) * rows + 1)) := by
      rw [Nat.mul_succ]
      omega
    rw [cost]
    exact checked

theorem counter_input_bound (n rows inputLength : Nat)
    (dimension : n ≤ inputLength) (count : rows ≤ inputLength) :
    (n + 1) * rows ≤ (inputLength + 1) * inputLength :=
  Nat.mul_le_mul (Nat.succ_le_succ dimension) count

theorem counterFuel_input_bound (n rows inputLength : Nat)
    (dimension : n ≤ inputLength) (count : rows ≤ inputLength) :
    (3 * (n + 1) + 4) * rows + 1 ≤ (3 * (inputLength + 1) + 4) * inputLength + 1 := by
  exact Nat.add_le_add_right
    (Nat.mul_le_mul (by omega) count) 1

end PNP.Concrete.ResidualReduction.MatrixPayloadCounter
