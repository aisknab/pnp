import PNP.Concrete.ResidualReduction.MatrixRowInstructions

/-! Construct an arbitrary unit direction by literal counted instructions.
The two unary counters determine every emitted bit. The output is accumulated
in reverse order so that a later common reversal can serialize a weight/direction
pair without assuming an append or a semantic point constructor is primitive. -/

namespace PNP.Concrete.ResidualReduction.SourceUnitDirectionInstructions
open PNP.Concrete PNP.Concrete.BitRegister
open PNP.Concrete.NormalizerBlocks PNP.Concrete.NormalizerBlocks.Occurrence
open PNP.Concrete.ResidualReduction.FactoredContraction
open PNP.Concrete.ResidualReduction.BinaryLinear
open PNP.Concrete.ResidualReduction.ConstrainedBilinear

def word (n j : Nat) : BitString :=
  List.replicate j false ++ true :: List.replicate (n - j - 1) false

theorem zero_bytes (n : Nat) : (SourceEncoding.pointCodec n).encode (zeroPoint n) = List.replicate n false := by
  induction n with
  | zero => rfl
  | succ n ih => exact congrArg (List.cons false) ih

theorem unit_bytes (n : Nat) (j : Fin n) :
    (SourceEncoding.pointCodec n).encode (unitPoint n j) = word n j.val := by
  induction n with
  | zero => exact Fin.elim0 j
  | succ n ih =>
    refine Fin.cases ?_ (fun i => ?_) j
    · change true :: (SourceEncoding.pointCodec n).encode (zeroPoint n) = true :: List.replicate n false
      rw [zero_bytes]
    · change false :: (SourceEncoding.pointCodec n).encode (unitPoint n i) =
        word (n + 1) (i.val + 1)
      simpa only [word, Nat.add_sub_add_right, List.replicate_succ, List.cons_append] using congrArg (List.cons false) (ih i)

private theorem replicate_snoc (count : Nat) (output : BitString) :
    List.replicate count false ++ false :: output = List.replicate (count + 1) false ++ output := by
  induction count with
  | zero => rfl
  | succ count ih =>
    simpa only [List.replicate_succ, List.cons_append] using congrArg (List.cons false) ih

def prefixStep : Block 9 := .seq (.action (.push 8 false))
  (.seq (.action (.pop 1)) (.action (.pop 2)))
def prefixLoop : Block 9 := .loop 1 prefixStep

theorem prefix_exec (r : Registers) (count rest : Nat) :
    Exec prefixLoop
      ({r with target := List.replicate count true, remaining := List.replicate (count + rest) true}).store
      (4 * count + 1)
      ({r with target := [], remaining := List.replicate rest true, output := List.replicate count false ++ r.output}).store := by
  induction count generalizing r with
  | zero =>
    simp only [Nat.zero_add, Nat.mul_zero, List.replicate_zero, List.nil_append]
    exact Exec.loopStop rfl
  | succ count ih =>
    have step : Exec prefixStep
        ({r with target := List.replicate (count + 1) true, remaining := List.replicate (count + 1 + rest) true}).store 3
        ({r with target := List.replicate count true, remaining := List.replicate (count + rest) true, output := false :: r.output}).store := by
      have same : count + 1 + rest = (count + rest) + 1 := by omega
      rw [same]
      exact Exec.seq (.action _ _) (Exec.seq (.action _ _) (.action _ _))
    have checked := Exec.loopStep (source := (1 : Fin 9)) rfl step (ih {r with output := false :: r.output})
    have cost : 4 * (count + 1) + 1 = 1 + (3 + (4 * count + 1)) := by omega
    simpa only [prefixLoop, cost, replicate_snoc] using checked

def suffixStep : Block 9 := .seq (.action (.push 8 false)) (.action (.pop 2))
def suffixLoop : Block 9 := .loop 2 suffixStep

theorem suffix_exec (r : Registers) (count : Nat) :
    Exec suffixLoop ({r with remaining := List.replicate count true}).store (3 * count + 1)
      ({r with remaining := [], output := List.replicate count false ++ r.output}).store := by
  induction count generalizing r with
  | zero => exact Exec.loopStop rfl
  | succ count ih =>
    have step : Exec suffixStep ({r with remaining := List.replicate (count + 1) true}).store 2
        ({r with remaining := List.replicate count true, output := false :: r.output}).store :=
      Exec.seq (.action _ _) (.action _ _)
    have checked := Exec.loopStep (source := (2 : Fin 9)) rfl step (ih {r with output := false :: r.output})
    have cost : 3 * (count + 1) + 1 = 1 + (2 + (3 * count + 1)) := by omega
    simpa only [suffixLoop, cost, replicate_snoc] using checked

def middle : Block 9 := .seq (.action (.push 8 true)) (.action (.pop 2))
def block : Block 9 := .seq prefixLoop (.seq middle suffixLoop)
def fuel (n j : Nat) : Nat := 4 * j + 3 * (n - j - 1) + 4

theorem block_exec (r : Registers) (n : Nat) (j : Fin n) :
    Exec block ({r with target := List.replicate j.val true, remaining := List.replicate n true}).store
      (fuel n j.val)
      ({r with target := [], remaining := [], output := ((SourceEncoding.pointCodec n).encode (unitPoint n j)).reverse ++ r.output}).store := by
  let tail := n - j.val - 1
  have partition : j.val + (tail + 1) = n := by dsimp only [tail]; omega
  have first := prefix_exec r j.val (tail + 1)
  rw [partition] at first
  let afterPrefix : Registers := {r with target := [], remaining := List.replicate (tail + 1) true, output := List.replicate j.val false ++ r.output}
  let afterMiddle : Registers := {r with target := [], remaining := List.replicate tail true, output := true :: (List.replicate j.val false ++ r.output)}
  have center : Exec middle afterPrefix.store 2 afterMiddle.store := Exec.seq (.action _ _) (.action _ _)
  have last := suffix_exec afterMiddle tail
  have checked := Exec.seq first (Exec.seq center last)
  have cost : fuel n j.val = (4 * j.val + 1) + (2 + (3 * tail + 1)) := by unfold fuel tail; omega
  simpa only [block, cost, afterPrefix, afterMiddle, unit_bytes, word, List.reverse_append,
    List.reverse_cons, List.reverse_replicate, List.append_assoc, List.cons_append, List.nil_append, tail] using checked

theorem fuel_bound (n : Nat) (j : Fin n) : fuel n j.val ≤ 4 * n := by
  unfold fuel
  have bound := j.isLt
  omega

end PNP.Concrete.ResidualReduction.SourceUnitDirectionInstructions
