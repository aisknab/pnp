import PNP.Concrete.ResidualReduction.SourceLineMatrixRows

/-! Augment the original source bytes by every required unit-covector row.
The complete family is materialized and reordered by literal instructions.
The original family count and input normal are retained separately. -/

namespace PNP.Concrete.ResidualReduction.SourceLineMatrixAugmentation
open PNP.Concrete PNP.Concrete.BitRegister
open PNP.Concrete.NormalizerBlocks
open PNP.Concrete.ResidualReduction.FactoredContraction
open PNP.Concrete.ResidualReduction.MatrixInstructions
open PNP.Concrete.ResidualReduction.SourceMatrixEncoding (familyBits)
open PNP.Concrete.ResidualReduction.SourceLineMatrix
open PNP.Concrete.ResidualReduction.SourceLineMatrixRows (ready loop loopFuel loop_exec)
open PNP.Concrete.ResidualReduction.SourcePlaneMatrixAugmentation
  (State registers setRegisters lift9 lift9_exec)

def loaded {n : Nat} (rows : Nat) (alpha : Affine n) (word : BitString) : State :=
  ⟨⟨⟨SourcePolarInstructions.working n 0 0 [] word [] [], [], [], []⟩,
    List.replicate rows true⟩, affineWord alpha⟩
def start {n : Nat} (F : Family n) (alpha : Affine n) : State :=
  loaded F.length alpha (familyBits F)
def augmentedInput {n : Nat} (F : Family n) (alpha : Affine n) : State :=
  loaded F.length alpha (familyBits (augmented F alpha))

def seedPrepare : Block 17 := .seq (.action (.copy 3 0)) (.action (.clear 0))
def seed : Block 17 := .seq seedPrepare <|
  .seq (lift9 ClauseQuery.reverseLoop) (.action (.copy 13 9))
theorem seed_exec {n : Nat} (rows : Nat) (alpha : Affine n) (word : BitString) :
    Exec seed (loaded rows alpha word).store (4 * word.length + 4)
      (ready rows alpha 0 n word.reverse).store := by
  let before := loaded rows alpha word
  let staged := setRegisters before {base 0 [] with excess := word}
  let reversed := setRegisters before {base 0 [] with output := word.reverse}
  have prepared : Exec seedPrepare before.store 2 staged.store :=
    Exec.seq (.action _ _) (.action _ _)
  have core : Exec ClauseQuery.reverseLoop (registers staged).store
      (4 * word.length + 1) (registers reversed).store := by
    simpa only [staged, reversed, registers, setRegisters, SourceMatrixPacket.setCore,
      base, List.append_nil] using ClauseQuery.reverse_exec (base 0 []) word
  have copied : Exec (.action (.copy (13 : Fin 17) 9)) reversed.store 1
      (ready rows alpha 0 n word.reverse).store := .action _ _
  have cost : 4 * word.length + 4 = 2 + ((4 * word.length + 1) + 1) := by omega
  simpa only [seed, cost, before] using Exec.seq prepared
    (Exec.seq (lift9_exec _ staged _ (registers reversed) core) copied)

def reorderPrepare : Block 17 := .seq (.action (.copy 3 8)) (.action (.clear 8))
def restore : Block 17 := .seq (.action (.copy 0 8)) <|
  .seq (.action (.clear 8)) (.action (.clear 10))
def reorder : Block 17 := .seq reorderPrepare (.seq (lift9 ClauseQuery.reverseLoop) restore)
theorem reorder_exec {n : Nat} (rows : Nat) (alpha : Affine n) (word : BitString) :
    Exec reorder (ready rows alpha n 0 word.reverse).store (4 * word.length + 6)
      (loaded rows alpha word).store := by
  let before := ready rows alpha n 0 word.reverse
  let staged := setRegisters before {base 0 [] with excess := word.reverse}
  let ordered := ready rows alpha n 0 word
  have prepared : Exec reorderPrepare before.store 2 staged.store :=
    Exec.seq (.action _ _) (.action _ _)
  have core : Exec ClauseQuery.reverseLoop (registers staged).store
      (4 * word.length + 1) (registers ordered).store := by
    simpa only [staged, ordered, ready, registers, setRegisters, SourceMatrixPacket.setCore,
      SourceMatrixConstruction.ready, SourcePolarInstructions.working, base,
      List.length_reverse, List.reverse_reverse, List.append_nil] using
      ClauseQuery.reverse_exec (base 0 []) word.reverse
  have restored : Exec restore ordered.store 3 (loaded rows alpha word).store :=
    Exec.seq (.action _ _) (Exec.seq (.action _ _) (.action _ _))
  have cost : 4 * word.length + 6 = 2 + ((4 * word.length + 1) + 3) := by omega
  simpa only [reorder, cost, before] using Exec.seq prepared
    (Exec.seq (lift9_exec _ staged _ (registers ordered) core) restored)

def block : Block 17 := .seq seed (.seq loop reorder)
def fuel {n : Nat} (F : Family n) (alpha : Affine n) : Nat :=
  (4 * (familyBits F).length + 4) +
    (loopFuel n 0 n + (4 * (familyBits (augmented F alpha)).length + 6))
theorem block_exec {n : Nat} (F : Family n) (alpha : Affine n) :
    Exec block (start F alpha).store (fuel F alpha) (augmentedInput F alpha).store := by
  have generated : Exec loop (ready F.length alpha 0 n (familyBits F).reverse).store
      (loopFuel n 0 n)
      (ready F.length alpha n 0 (familyBits (augmented F alpha)).reverse).store := by
    simpa only [Nat.zero_add, augmented_bits, List.reverse_append] using
      loop_exec F.length alpha n 0 (familyBits F).reverse (by omega)
  exact Exec.seq (seed_exec F.length alpha (familyBits F))
    (Exec.seq generated (reorder_exec F.length alpha (familyBits (augmented F alpha))))
theorem input_bytes {n : Nat} (F : Family n) (alpha : Affine n) :
    (augmentedInput F alpha).store.get 0 = familyBits (augmented F alpha) := rfl
theorem retained_count {n : Nat} (F : Family n) (alpha : Affine n) :
    (augmentedInput F alpha).store.get 15 = List.replicate F.length true := rfl
theorem retained_normal {n : Nat} (F : Family n) (alpha : Affine n) :
    (augmentedInput F alpha).store.get 16 = affineWord alpha := rfl

end PNP.Concrete.ResidualReduction.SourceLineMatrixAugmentation
