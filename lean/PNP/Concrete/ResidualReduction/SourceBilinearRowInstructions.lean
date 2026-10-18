import PNP.Concrete.ResidualReduction.SourceBilinearFamily

/-! Literal conversion of one coefficient row into the source-row format.
The source bits are copied; constants and padding are emitted by counted
instructions. No affine row, completed family or witness is supplied. -/

namespace PNP.Concrete.ResidualReduction.SourceBilinearRowInstructions
open PNP.Concrete PNP.Concrete.BitRegister
open PNP.Concrete.NormalizerBlocks PNP.Concrete.NormalizerBlocks.Occurrence
open PNP.Concrete.ResidualReduction.FactoredContraction
open PNP.Concrete.ResidualReduction.SourceMatrixEncoding
open PNP.Concrete.ResidualReduction.MatrixInstructions

private theorem replicate_snoc (count : Nat) (saved : BitString) :
    List.replicate count false ++ false :: saved = List.replicate (count + 1) false ++ saved := by
  induction count with
  | zero => rfl
  | succ count ih =>
    simpa only [List.replicate_succ, List.cons_append] using congrArg (List.cons false) ih

def zeroStep : Block 9 := .seq (.action (.push 3 false)) (.action (.pop 2))
def zeroLoop : Block 9 := .loop 2 zeroStep

theorem zero_exec (r : Registers) (count : Nat) :
    Exec zeroLoop ({r with remaining := List.replicate count true}).store (3 * count + 1)
      ({r with remaining := [], excess := List.replicate count false ++ r.excess}).store := by
  induction count generalizing r with
  | zero => exact Exec.loopStop rfl
  | succ count ih =>
    have step : Exec zeroStep ({r with remaining := List.replicate (count + 1) true}).store 2
        ({r with remaining := List.replicate count true, excess := false :: r.excess}).store :=
      Exec.seq (.action _ _) (.action _ _)
    have checked := Exec.loopStep (source := (2 : Fin 9)) rfl step (ih {r with excess := false :: r.excess})
    have cost : 3 * (count + 1) + 1 = 1 + (2 + (3 * count + 1)) := by omega
    simpa only [zeroLoop, cost, replicate_snoc] using checked

def packed (word : BitString) : BitString :=
  false :: (word ++ false :: (List.replicate word.length false ++ [true]))

def copyPrefix : Block 9 := .seq (.action (.push 3 false)) <|
  .seq (.action (.copy 2 1)) copyLoop
def suffix : Block 9 := .seq (.action (.push 3 false)) <|
  .seq (.action (.copy 2 1)) <| .seq zeroLoop (.action (.push 3 true))
def row : Block 9 := .seq copyPrefix suffix

theorem prefix_exec (r : Registers) (word rest : BitString) :
    Exec copyPrefix ({r with input := word ++ rest, target := List.replicate word.length true, remaining := []}).store
      (5 * word.length + 3)
      ({r with input := rest, target := List.replicate word.length true, remaining := [], excess := word.reverse ++ false :: r.excess}).store := by
  let before := {r with input := word ++ rest, target := List.replicate word.length true, remaining := []}
  let tagged := {before with excess := false :: r.excess}
  let ready := {tagged with remaining := List.replicate word.length true}
  have tag : Exec (.action (.push (3 : Fin 9) false)) before.store 1 tagged.store := .action _ _
  have seed : Exec (.action (.copy (2 : Fin 9) 1)) tagged.store 1 ready.store := .action _ _
  have copied := copy_exec {r with target := List.replicate word.length true, excess := false :: r.excess} word rest
  have cost : 5 * word.length + 3 = 1 + (1 + (5 * word.length + 1)) := by omega
  simpa only [copyPrefix, cost, before, tagged, ready] using Exec.seq tag (Exec.seq seed copied)

theorem suffix_exec (r : Registers) (n : Nat) :
    Exec suffix ({r with target := List.replicate n true, remaining := []}).store (3 * n + 4)
      ({r with target := List.replicate n true, remaining := [], excess := true :: (List.replicate n false ++ false :: r.excess)}).store := by
  let before := {r with target := List.replicate n true, remaining := []}
  let tagged := {before with excess := false :: r.excess}
  let ready := {tagged with remaining := List.replicate n true}
  let padded := {before with excess := List.replicate n false ++ false :: r.excess}
  have tag : Exec (.action (.push (3 : Fin 9) false)) before.store 1 tagged.store := .action _ _
  have seed : Exec (.action (.copy (2 : Fin 9) 1)) tagged.store 1 ready.store := .action _ _
  have zeros : Exec zeroLoop ready.store (3 * n + 1) padded.store := zero_exec tagged n
  have last : Exec (.action (.push (3 : Fin 9) true)) padded.store 1
      ({r with target := List.replicate n true, remaining := [], excess := true :: (List.replicate n false ++ false :: r.excess)}).store := .action _ _
  have cost : 3 * n + 4 = 1 + (1 + ((3 * n + 1) + 1)) := by omega
  simpa only [suffix, cost] using Exec.seq tag (Exec.seq seed (Exec.seq zeros last))

theorem row_exec (r : Registers) (word rest : BitString) :
    Exec row ({r with input := word ++ rest, target := List.replicate word.length true, remaining := []}).store
      (8 * word.length + 7)
      ({r with input := rest, target := List.replicate word.length true, remaining := [], excess := (packed word).reverse ++ r.excess}).store := by
  have checked := Exec.seq (prefix_exec r word rest)
    (suffix_exec {r with input := rest, excess := word.reverse ++ false :: r.excess} word.length)
  have cost : 8 * word.length + 7 = (5 * word.length + 3) + (3 * word.length + 4) := by omega
  simpa only [row, cost, packed, List.reverse_cons, List.reverse_append, List.reverse_replicate,
    List.reverse_nil, List.append_assoc, List.cons_append, List.nil_append] using checked

theorem coefficient_row_exec (r : Registers) {n : Nat} (f : Fin n → Bool) (rest : BitString) :
    Exec row ({r with input := (List.finRange n).map f ++ rest, target := List.replicate n true, remaining := []}).store
      (8 * n + 7)
      ({r with input := rest, target := List.replicate n true, remaining := [], excess := (rowWord (SourceBilinearFamily.row f)).reverse ++ r.excess}).store := by
  simpa only [List.length_map, List.length_finRange, SourceBilinearFamily.row_word, packed] using
    row_exec r ((List.finRange n).map f) rest

end PNP.Concrete.ResidualReduction.SourceBilinearRowInstructions
