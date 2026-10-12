/-
Copyright (c) 2026 PNP Labs.

Concrete output serialization for path reconstruction. The reverse
accumulator is restored using finite bit operations; failure emits only
the absent marker and never exposes a partial path as successful.
-/
import PNP.Concrete.NormalizerPathCanonical

namespace PNP.Concrete.NormalizerBlocks.TracePath
open BitRegister

def preparePath : Block 23 := .seq (.action (.copy 3 21)) (.action (.clear 8))
def pathPrepared (r : State) : State := r.withRegisters {r.registers with excess := r.buffer, output := []}
theorem preparePath_exec (r : State) : Exec preparePath r.store 2 (pathPrepared r).store :=
  Exec.seq (.action _ _) (.action _ _)

def reversePath : Block 23 := liftCore ClauseQuery.reverseLoop
def pathReversed (r : State) : State := r.withRegisters {r.registers with excess := [], output := r.registers.excess.reverse ++ r.registers.output}
theorem reversePath_exec (r : State) :
    Exec reversePath r.store (4 * r.registers.excess.length + 1) (pathReversed r).store :=
  liftCore_exec _ r _ _ (ClauseQuery.reverse_exec r.registers r.registers.excess)

def successTag : Block 23 := .action (.push 8 true)
def successTagged (r : State) : State := r.withRegisters {r.registers with output := true :: r.registers.output}
theorem successTag_exec (r : State) : Exec successTag r.store 1 (successTagged r).store := .action _ _

def packSuccess : Block 23 := .seq preparePath (.seq reversePath successTag)
def successPacked (r : State) : State := successTagged (pathReversed (pathPrepared r))
theorem packSuccess_exec (r : State) :
    Exec packSuccess r.store (4 * r.buffer.length + 4) (successPacked r).store := by
  have checked := Exec.seq (preparePath_exec r) (Exec.seq (reversePath_exec (pathPrepared r)) (successTag_exec (pathReversed (pathPrepared r))))
  change Exec packSuccess r.store (2 + ((4 * r.buffer.length + 1) + 1)) (successPacked r).store at checked
  have cost : 2 + ((4 * r.buffer.length + 1) + 1) = 4 * r.buffer.length + 4 := by omega
  rw [cost] at checked
  exact checked

def packFailure : Block 23 := .seq (.action (.clear 8)) (.action (.push 8 false))
def failurePacked (r : State) : State := r.withRegisters {r.registers with output := [false]}
theorem packFailure_exec (r : State) : Exec packFailure r.store 2 (failurePacked r).store :=
  Exec.seq (.action _ _) (.action _ _)

def finish : Block 23 := .branch 19 packFailure packFailure packSuccess
def finished (r : State) : State := if ForwardEdge.present r.core.output then successPacked r else failurePacked r
def finishFuel (r : State) : Nat := 1 + if ForwardEdge.present r.core.output then 4 * r.buffer.length + 4 else 2
theorem finish_exec (r : State) : Exec finish r.store (finishFuel r) (finished r).store := by
  have checked := EdgeKinds.branch_head (19 : Fin 23) r.store packFailure packSuccess 2 (4 * r.buffer.length + 4)
    (failurePacked r).store (successPacked r).store (packFailure_exec r) (packSuccess_exec r)
  change Exec finish r.store (finishFuel r)
    (if ForwardEdge.present r.core.output then (successPacked r).store else (failurePacked r).store) at checked
  cases tag : ForwardEdge.present r.core.output <;>
    simpa only [finished, tag, Bool.false_eq_true, ite_false, ite_true] using checked

theorem finishFuel_bound (r : State) : finishFuel r ≤ 4 * r.buffer.length + 5 := by
  cases tag : ForwardEdge.present r.core.output <;>
    simp only [finishFuel, tag, Bool.false_eq_true, ite_false, ite_true] <;> omega

theorem finished_output (r : State) : (finished r).registers.output = observation r := by
  cases tag : ForwardEdge.present r.core.output <;>
    simp only [finished, observation, tag, Bool.false_eq_true, ite_false, ite_true]
  · rfl
  · change true :: (r.buffer.reverse ++ []) = true :: r.buffer.reverse
    rw [List.append_nil]

theorem finished_preserves (r : State) :
    (finished r).core.graph.core.formula = r.core.graph.core.formula ∧
      (finished r).core.graph.core.matching = r.core.graph.core.matching := by
  cases tag : ForwardEdge.present r.core.output <;>
    simp only [finished, tag, Bool.false_eq_true, ite_false, ite_true] <;> exact ⟨rfl, rfl⟩

end PNP.Concrete.NormalizerBlocks.TracePath
