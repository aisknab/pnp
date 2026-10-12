/-
Copyright (c) 2026 PNP Labs.

Concrete serialization helpers for extraction. A byte reversal restores
the skipped prefix before the untouched suffix. The optional predecessor
is emitted from the computed parent answer, not from supplied metadata.
-/

import PNP.Concrete.NormalizerExtractSemantics

namespace PNP.Concrete.NormalizerBlocks.Extraction
open BitRegister

def prepareRemaining : Block 27 := .seq (.action (.copy 3 23)) (.action (.copy 8 22))
def remainingPrepared (r : State) : State :=
  r.withRegisters {r.registers with excess := r.skipped, output := r.pending}
theorem prepareRemaining_exec (r : State) : Exec prepareRemaining r.store 2 (remainingPrepared r).store :=
  Exec.seq (.action _ _) (.action _ _)

def reverseRemaining : Block 27 := liftCore ClauseQuery.reverseLoop
def remainingReversed (r : State) : State :=
  r.withRegisters {r.registers with excess := [], output := r.registers.excess.reverse ++ r.registers.output}
theorem reverseRemaining_exec (r : State) :
    Exec reverseRemaining r.store (4 * r.registers.excess.length + 1) (remainingReversed r).store :=
  liftCore_exec _ r _ _ (ClauseQuery.reverse_exec r.registers r.registers.excess)

def copyOutputInput : Block 27 := .action (.copy 0 8)
def outputCopied (r : State) : State := r.withRegisters {r.registers with input := r.registers.output}
theorem copyOutputInput_exec (r : State) : Exec copyOutputInput r.store 1 (outputCopied r).store := .action _ _

def packRemaining : Block 27 := .seq prepareRemaining (.seq reverseRemaining copyOutputInput)
def remainingPacked (r : State) : State := outputCopied (remainingReversed (remainingPrepared r))
theorem packRemaining_exec (r : State) :
    Exec packRemaining r.store (4 * r.skipped.length + 4) (remainingPacked r).store := by
  have checked := Exec.seq (prepareRemaining_exec r)
    (Exec.seq (reverseRemaining_exec (remainingPrepared r)) (copyOutputInput_exec (remainingReversed (remainingPrepared r))))
  change Exec packRemaining r.store (2 + ((4 * r.skipped.length + 1) + 1)) (remainingPacked r).store at checked
  have cost : 2 + ((4 * r.skipped.length + 1) + 1) = 4 * r.skipped.length + 4 := by omega
  rw [cost] at checked
  exact checked

theorem remainingPacked_input (r : State) :
    (remainingPacked r).registers.input = r.skipped.reverse ++ r.pending := rfl

def pushFalse : Block 27 := .action (.push 0 false)
def falsePushed (r : State) : State := r.withRegisters {r.registers with input := false :: r.registers.input}
theorem pushFalse_exec (r : State) : Exec pushFalse r.store 1 (falsePushed r).store := .action _ _
def pushTrue : Block 27 := .action (.push 0 true)
def truePushed (r : State) : State := r.withRegisters {r.registers with input := true :: r.registers.input}
theorem pushTrue_exec (r : State) : Exec pushTrue r.store 1 (truePushed r).store := .action _ _

def pushSign : Block 27 := .branch 4 pushFalse pushFalse pushTrue
def signPushed (r : State) : State :=
  r.withRegisters {r.registers with input := ForwardEdge.present r.registers.sign :: r.registers.input}
theorem pushSign_exec (r : State) : Exec pushSign r.store 2 (signPushed r).store := by
  have checked := EdgeKinds.branch_head (4 : Fin 27) r.store pushFalse pushTrue 1 1
    (falsePushed r).store (truePushed r).store (pushFalse_exec r) (pushTrue_exec r)
  change Exec pushSign r.store (1 + if ForwardEdge.present r.registers.sign then 1 else 1)
    (if ForwardEdge.present r.registers.sign then (truePushed r).store else (falsePushed r).store) at checked
  cases tag : ForwardEdge.present r.registers.sign <;>
    simpa only [signPushed, falsePushed, truePushed, tag, Bool.false_eq_true, ite_false, ite_true] using checked

def prepend : Block 27 := liftCore ParentQuery.prependLoop
def prepended (r : State) : State :=
  r.withRegisters (ParentQuery.prepended r.registers.remaining r.registers)
def prependFuel (r : State) : Nat := 3 * r.registers.remaining.length + 1
theorem prepend_exec (r : State) : Exec prepend r.store (prependFuel r) (prepended r).store :=
  liftCore_exec _ r _ _ (ParentQuery.prepend_exec r.registers.remaining r.registers)

def copySignCounter : Block 27 := .action (.copy 2 4)
def signCounterCopied (r : State) : State := r.withRegisters {r.registers with remaining := r.registers.sign}
theorem copySignCounter_exec (r : State) : Exec copySignCounter r.store 1 (signCounterCopied r).store := .action _ _
def popCounter2 : Block 27 := .seq (.action (.pop 2)) (.action (.pop 2))
def counterPopped2 (r : State) : State := r.withRegisters {r.registers with remaining := r.registers.remaining.tail.tail}
theorem popCounter2_exec (r : State) : Exec popCounter2 r.store 2 (counterPopped2 r).store :=
  Exec.seq (.action _ _) (.action _ _)
def parentCounter : Block 27 := .seq copySignCounter popCounter2
def parentCounted (r : State) : State := counterPopped2 (signCounterCopied r)
theorem parentCounter_exec (r : State) : Exec parentCounter r.store 3 (parentCounted r).store :=
  Exec.seq (copySignCounter_exec r) (popCounter2_exec (signCounterCopied r))

def popSign : Block 27 := .action (.pop 4)
def signPopped (r : State) : State := r.withRegisters {r.registers with sign := r.registers.sign.tail}
theorem popSign_exec (r : State) : Exec popSign r.store 1 (signPopped r).store := .action _ _

def parentSome : Block 27 :=
  .seq pushFalse (.seq parentCounter (.seq prepend (.seq popSign (.seq pushSign pushTrue))))
def parentSomeResult (r : State) : State :=
  truePushed (signPushed (signPopped (prepended (parentCounted (falsePushed r)))))
def parentSomeFuel (r : State) : Nat := 3 * r.registers.sign.tail.tail.length + 9
theorem parentSome_exec (r : State) : Exec parentSome r.store (parentSomeFuel r) (parentSomeResult r).store := by
  have checked := Exec.seq (pushFalse_exec r) <| Exec.seq (parentCounter_exec (falsePushed r)) <|
    Exec.seq (prepend_exec (parentCounted (falsePushed r))) <|
      Exec.seq (popSign_exec (prepended (parentCounted (falsePushed r)))) <|
        Exec.seq (pushSign_exec (signPopped (prepended (parentCounted (falsePushed r)))))
          (pushTrue_exec (signPushed (signPopped (prepended (parentCounted (falsePushed r))))))
  change Exec parentSome r.store
    (1 + (3 + ((3 * r.registers.sign.tail.tail.length + 1) + (1 + (2 + 1))))) (parentSomeResult r).store at checked
  have cost : 1 + (3 + ((3 * r.registers.sign.tail.tail.length + 1) + (1 + (2 + 1)))) = parentSomeFuel r := by
    unfold parentSomeFuel
    omega
  rw [cost] at checked
  exact checked

def chooseParent : Block 27 := .branch 4 pushFalse pushFalse parentSome
def parentChosen (r : State) : State :=
  if ForwardEdge.present r.registers.sign then parentSomeResult r else falsePushed r
def chooseParentFuel (r : State) : Nat :=
  1 + if ForwardEdge.present r.registers.sign then parentSomeFuel r else 1
theorem chooseParent_exec (r : State) :
    Exec chooseParent r.store (chooseParentFuel r) (parentChosen r).store := by
  have checked := EdgeKinds.branch_head (4 : Fin 27) r.store pushFalse parentSome 1 (parentSomeFuel r)
    (falsePushed r).store (parentSomeResult r).store (pushFalse_exec r) (parentSome_exec r)
  change Exec chooseParent r.store (chooseParentFuel r)
    (if ForwardEdge.present r.registers.sign then (parentSomeResult r).store else (falsePushed r).store) at checked
  cases tag : ForwardEdge.present r.registers.sign <;>
    simpa only [parentChosen, tag, Bool.false_eq_true, ite_false, ite_true] using checked

def copyParentSign : Block 27 := .action (.copy 4 19)
def parentSignCopied (r : State) : State := r.withRegisters {r.registers with sign := r.parent.output}
theorem copyParentSign_exec (r : State) : Exec copyParentSign r.store 1 (parentSignCopied r).store := .action _ _
def beginParent : Block 27 := .seq copyParentSign popSign
def parentBegun (r : State) : State := signPopped (parentSignCopied r)
theorem beginParent_exec (r : State) : Exec beginParent r.store 2 (parentBegun r).store :=
  Exec.seq (copyParentSign_exec r) (popSign_exec (parentSignCopied r))

def packParent : Block 27 := .seq beginParent chooseParent
def parentPacked (r : State) : State := parentChosen (parentBegun r)
def packParentFuel (r : State) : Nat := 2 + chooseParentFuel (parentBegun r)
theorem packParent_exec (r : State) : Exec packParent r.store (packParentFuel r) (parentPacked r).store :=
  Exec.seq (beginParent_exec r) (chooseParent_exec (parentBegun r))

theorem parentPacked_input (r : State) :
    (parentPacked r).registers.input = parentBytes r.parent.output r.registers.input := by
  have head : ForwardEdge.present (parentBegun r).registers.sign = ForwardEdge.present r.parent.output.tail := rfl
  unfold parentPacked parentChosen
  rw [head]
  unfold parentBytes
  cases tag : ForwardEdge.present r.parent.output.tail <;>
    simp only [Bool.false_eq_true, ite_false, ite_true] <;> rfl

theorem parentPacked_fields (r : State) :
    (parentPacked r).parent.targetIndex = r.parent.targetIndex ∧
      (parentPacked r).parent.targetTag = r.parent.targetTag ∧
        (parentPacked r).parent.output = r.parent.output := by
  cases tag : ForwardEdge.present (parentBegun r).registers.sign <;>
    simp only [parentPacked, parentChosen, tag, Bool.false_eq_true, ite_false, ite_true] <;>
    exact ⟨rfl, rfl, rfl⟩

theorem packParentFuel_bound (r : State) : packParentFuel r ≤ 3 * r.parent.output.length + 12 := by
  have tail : r.parent.output.tail.tail.tail.length ≤ r.parent.output.length :=
    Nat.le_trans (ParentQuery.input_tail_bound r.parent.output.tail.tail) (EdgeKinds.tail_length_le r.parent.output)
  change 2 + (1 + if ForwardEdge.present r.parent.output.tail
    then 3 * r.parent.output.tail.tail.tail.length + 9 else 1) ≤ _
  cases tag : ForwardEdge.present r.parent.output.tail <;>
    simp only [Bool.false_eq_true, ite_false, ite_true] <;> omega

end PNP.Concrete.NormalizerBlocks.Extraction
