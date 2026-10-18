import PNP.Concrete.ResidualReduction.SourceFamilyTailLoad

/-! Canonical packet loader for the complete reduction pass. Dimension and
row count are parsed from unary headers; every tail coefficient is read by the
tail loader. The raw initial state contains only the input stream. -/

namespace PNP.Concrete.ResidualReduction.SourceFamilyReductionLoad
open PNP.Concrete PNP.Concrete.BitRegister PNP.Concrete.NormalizerBlocks
open PNP.Concrete.NormalizerBlocks.Occurrence
open PNP.Concrete.NativeNormalization.NativeBitCodec
open PNP.Concrete.ResidualReduction.FactoredContraction
open PNP.Concrete.ResidualReduction.SourceMatrixEncoding (familyBits)
open PNP.Concrete.ResidualReduction.SourceRowReductionState (work parameters emptyData)
open PNP.Concrete.ResidualReduction.SourceFamilyReductionState
open PNP.Concrete.ResidualReduction.SourceFamilyTailLoad (noParameters noData blank)
open PNP.Concrete.ResidualReduction.SourceFamilyReductionEncoding (packet packet_bytes)

def rawCore (input : BitString) : Registers := ⟨input,[],[],[],[],[],[],[],[]⟩
def initial (input : BitString) : Store 23 :=
  full (SourceRowReductionState.full (rawCore input) noParameters noData) emptySaved

theorem headerFuel (count : Nat) (suffix : BitString) :
    MatrixStrictHeader.blockFuel (natural count ++ suffix) = 4 * count + 9 := by
  induction count with
  | zero => rfl
  | succ count ih =>
    unfold MatrixStrictHeader.blockFuel at ih ⊢
    change 3 + (4 + MatrixStrictHeader.fuel (natural count ++ suffix)) = 4 * (count + 1) + 9
    omega

def finishDimension : Block 23 := .seq (.action (.push 1 true)) (.action (.clear 4))
def dimension : Block 23 := .seq (core MatrixStrictHeader.block) finishDimension

theorem dimension_exec (n : Nat) (suffix : BitString) :
    Exec dimension (initial (natural n ++ suffix)) (4 * n + 11)
      (full (blank n suffix) emptySaved) := by
  let before := rawCore (natural n ++ suffix)
  let counted : Registers := ⟨suffix,List.replicate n true,[],[],[true],[],[],[],[]⟩
  have scan : Exec MatrixStrictHeader.block before.store (4 * n + 9) counted.store := by
    simpa only [headerFuel,MatrixStrictHeader.result,MatrixStrictHeader.scan_canonical,if_true,
      before,counted,rawCore,List.append_nil] using
      MatrixStrictHeader.block_exec (natural n ++ suffix) before
  have finish : Exec finishDimension
      (full (SourceRowReductionState.full counted noParameters noData) emptySaved) 2
      (full (blank n suffix) emptySaved) := Exec.seq (.action _ _) (.action _ _)
  have cost : 4 * n + 11 = (4 * n + 9) + 2 := by omega
  simpa only [dimension,cost,initial,before] using
    Exec.seq (core_exec scan noParameters noData emptySaved) finish

def prepareCount : Block 23 := .seq (.action (.copy 2 1)) (.action (.clear 1))
def saveCount : Block 23 := .seq (.action (.copy 19 1)) (.action (.copy 22 1))
def restoreWidth : Block 23 := .seq (.action (.copy 1 2)) <|
  .seq (.action (.clear 2)) <| .seq (.action (.clear 4)) (.action (.push 21 true))
def count : Block 23 := .seq prepareCount <| .seq (core MatrixStrictHeader.block) <|
  .seq saveCount restoreWidth

theorem count_exec {n : Nat} (t : TailForm n) (m : Nat) (suffix : BitString) :
    Exec count (full (base t (natural m ++ suffix)) emptySaved) (4 * m + 17)
      (state t suffix (List.replicate m true) [] true (List.replicate m true)) := by
  let before := work n (natural m ++ suffix)
  let ready := {before with target := [],remaining := List.replicate (n + 1) true}
  let counted := {work n suffix with target := List.replicate m true,remaining := List.replicate (n + 1) true,sign := [true]}
  let d := emptyData t []
  let saved : Saved := ⟨List.replicate m true,[],[],List.replicate m true⟩
  have prepare : Exec prepareCount (full (base t (natural m ++ suffix)) emptySaved) 2
      (full (SourceRowReductionState.full ready (parameters t) d) emptySaved) :=
    Exec.seq (.action _ _) (.action _ _)
  have scan : Exec MatrixStrictHeader.block ready.store (4 * m + 9) counted.store := by
    simpa only [headerFuel,MatrixStrictHeader.result,MatrixStrictHeader.scan_canonical,if_true,
      ready,before,counted,work,List.append_nil] using
      MatrixStrictHeader.block_exec (natural m ++ suffix) ready
  have save : Exec saveCount (full (SourceRowReductionState.full counted (parameters t) d) emptySaved) 2
      (full (SourceRowReductionState.full counted (parameters t) d) saved) :=
    Exec.seq (.action _ _) (.action _ _)
  have restore : Exec restoreWidth (full (SourceRowReductionState.full counted (parameters t) d) saved) 4
      (state t suffix (List.replicate m true) [] true (List.replicate m true)) :=
    Exec.seq (.action _ _) (Exec.seq (.action _ _) (Exec.seq (.action _ _) (.action _ _)))
  have cost : 4 * m + 17 = 2 + ((4 * m + 9) + (2 + 4)) := by omega
  simpa only [count,cost] using
    Exec.seq prepare (Exec.seq (core_exec scan (parameters t) d emptySaved) (Exec.seq save restore))

def block : Block 23 := .seq dimension (.seq SourceFamilyTailLoad.block count)
def fuel {n : Nat} (t : TailForm n) (F : Family (n + 1)) : Nat :=
  (4 * n + 11) + (SourceFamilyTailLoad.fuel t + (4 * F.length + 17))

theorem block_exec {n : Nat} (t : TailForm n) (F : Family (n + 1)) (suffix : BitString) :
    Exec block (initial (packet t F ++ suffix)) (fuel t F)
      (SourceFamilyReductionState.initial t F suffix) := by
  have dim := dimension_exec n ((SourceComputedTailEncoding.codec n).encode t ++
    (natural F.length ++ (familyBits F ++ suffix)))
  have tail := SourceFamilyTailLoad.block_exec t
    (natural F.length ++ (familyBits F ++ suffix)) emptySaved
  have rows := count_exec t F.length (familyBits F ++ suffix)
  simpa only [block,fuel,packet_bytes,List.append_assoc,SourceFamilyReductionState.initial,loopState] using
    Exec.seq dim (Exec.seq tail rows)

theorem fuel_bound {n : Nat} (t : TailForm n) (F : Family (n + 1)) :
    fuel t F ≤ 31 * (n + 1) + 4 * F.length + 43 := by
  have tail := SourceFamilyTailLoad.fuel_bound t
  unfold fuel
  omega

end PNP.Concrete.ResidualReduction.SourceFamilyReductionLoad
