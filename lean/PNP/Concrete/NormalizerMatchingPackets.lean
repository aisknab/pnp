/-
Copyright (c) 2026 PNP Labs.

Literal packet assembly used between matching rounds. These blocks prepend
an internally available word or its unary length to an existing suffix;
they do not receive a preassembled search or augmentation request.
-/
import PNP.Concrete.NormalizerMatchingCalls

namespace PNP.Concrete.NormalizerBlocks.MatchingPacket
open BitRegister Occurrence

def prepareCount : Block 9 := .seq (.action (.copy 0 8)) (.action (.push 0 false))
def countPrepared (r : Registers) : Registers := {r with input := false :: r.output}
theorem prepareCount_exec (r : Registers) : Exec prepareCount r.store 2 (countPrepared r).store :=
  Exec.seq (.action _ _) (.action _ _)
def finishCount : Block 9 := .action (.copy 8 0)
def countFinished (r : Registers) : Registers := {r with output := r.input}
theorem finishCount_exec (r : Registers) : Exec finishCount r.store 1 (countFinished r).store := .action _ _
def prependCount : Block 9 := .seq prepareCount (.seq ParentQuery.prependLoop finishCount)
def countPrepended (r : Registers) : Registers :=
  countFinished (ParentQuery.prepended r.remaining (countPrepared r))
def countFuel (r : Registers) : Nat := 3 * r.remaining.length + 4
theorem prependCount_exec (r : Registers) : Exec prependCount r.store (countFuel r) (countPrepended r).store := by
  have checked := Exec.seq (prepareCount_exec r)
    (Exec.seq (ParentQuery.prepend_exec r.remaining (countPrepared r))
      (finishCount_exec (ParentQuery.prepended r.remaining (countPrepared r))))
  have cost : countFuel r = 2 + ((3 * r.remaining.length + 1) + 1) := by unfold countFuel; omega
  rw [cost]
  exact checked
theorem countPrepended_output (r : Registers) :
    (countPrepended r).output = TableInit.encodeCount r.remaining.length r.output := rfl

def prepareBits : Block 9 :=
  .seq (.action (.copy 7 8)) (.seq (.action (.copy 3 0)) (.action (.clear 8)))
def bitsPrepared (r : Registers) : Registers := {r with reserved := r.output, excess := r.input, output := []}
theorem prepareBits_exec (r : Registers) : Exec prepareBits r.store 3 (bitsPrepared r).store :=
  Exec.seq (.action _ _) (Exec.seq (.action _ _) (.action _ _))
def reverseFirst : Block 9 := .seq prepareBits ClauseQuery.reverseLoop
def firstReversed (r : Registers) : Registers := {r with reserved := r.output, excess := [], output := r.input.reverse}
theorem reverseFirst_exec (r : Registers) :
    Exec reverseFirst r.store (4 * r.input.length + 4) (firstReversed r).store := by
  have reversed := ClauseQuery.reverse_exec (bitsPrepared r) r.input
  have checked := Exec.seq (prepareBits_exec r) reversed
  have cost : 4 * r.input.length + 4 = 3 + (4 * r.input.length + 1) := by omega
  rw [cost]
  simpa only [reverseFirst, bitsPrepared, firstReversed, List.append_nil] using checked

def restoreSuffix : Block 9 := .seq (.action (.copy 3 8)) (.action (.copy 8 7))
def suffixRestored (r : Registers) : Registers := {r with excess := r.output, output := r.reserved}
theorem restoreSuffix_exec (r : Registers) : Exec restoreSuffix r.store 2 (suffixRestored r).store :=
  Exec.seq (.action _ _) (.action _ _)
def prependBits : Block 9 := .seq reverseFirst (.seq restoreSuffix ClauseQuery.reverseLoop)
def bitsPrepended (r : Registers) : Registers := {r with reserved := r.output, excess := [], output := r.input ++ r.output}
def bitsFuel (r : Registers) : Nat := 8 * r.input.length + 7
theorem prependBits_exec (r : Registers) : Exec prependBits r.store (bitsFuel r) (bitsPrepended r).store := by
  have checked := Exec.seq (reverseFirst_exec r)
    (Exec.seq (restoreSuffix_exec (firstReversed r))
      (ClauseQuery.reverse_exec (suffixRestored (firstReversed r)) r.input.reverse))
  have cost : bitsFuel r = (4 * r.input.length + 4) + (2 + (4 * r.input.reverse.length + 1)) := by
    rw [List.length_reverse]
    unfold bitsFuel
    omega
  rw [cost]
  simpa only [prependBits, firstReversed, suffixRestored, bitsPrepended, List.reverse_reverse] using checked
theorem bitsPrepended_output (r : Registers) : (bitsPrepended r).output = r.input ++ r.output := rfl

end PNP.Concrete.NormalizerBlocks.MatchingPacket
