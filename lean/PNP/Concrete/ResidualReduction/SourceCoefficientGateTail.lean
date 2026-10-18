import PNP.Concrete.ResidualReduction.SourceCoefficientGateState

/-! Load the exact scalar tail, construct the encoded candidate polynomial,
and combine its full coefficient comparison with the computed head result.
Both failure cases return false; no unsatisfiability claim is produced. -/

namespace PNP.Concrete.ResidualReduction.SourceCoefficientGateTail
open PNP.Concrete PNP.Concrete.BitRegister PNP.Concrete.NormalizerBlocks
open PNP.Concrete.NormalizerBlocks.Occurrence
open PNP.Concrete.ResidualReduction.FactoredContraction
open PNP.Concrete.ResidualReduction.MatrixInstructions
open PNP.Concrete.ResidualReduction.SourceScalarState (work data zero)
open PNP.Concrete.ResidualReduction.SourceCoefficientGateState

def saveExpected : Block 18 := .seq (.action (.copy 17 8)) <|
  .seq (.action (.clear 8)) (.action (.copy 11 0))
def loadExpected : Block 18 := .seq (.action (.copy 2 14)) <|
  .seq (core copyLoop) <| .seq (core ClauseQuery.reverseLoop) saveExpected
def loadFuel (n : Nat) : Nat := 9 * quadraticBits n + 6

theorem load_exec {n : Nat} (q acc : Quadratic n) (suffix : BitString) (saved : Saved) :
    Exec loadExpected (state (SourceQuadraticEncoding.word q ++ suffix) acc saved) (loadFuel n)
      (state suffix acc {saved with expected := SourceQuadraticEncoding.word q}) := by
  let metadata := data (SourceQuadraticEncoding.word q ++ suffix) acc
  let loaded := {work (SourceQuadraticEncoding.word q ++ suffix) with remaining := List.replicate (quadraticBits n) true}
  let copied := {work suffix with excess := (SourceQuadraticEncoding.word q).reverse}
  let emitted := {work suffix with output := SourceQuadraticEncoding.word q}
  have load : Exec (.action (.copy (2 : Fin 18) 14))
      (state (SourceQuadraticEncoding.word q ++ suffix) acc saved) 1
      (full loaded SourceScalarState.emptySaved metadata saved) := .action _ _
  have copy : Exec copyLoop loaded.store (5 * quadraticBits n + 1) copied.store := by
    simpa only [loaded,copied,work,SourceQuadraticEncoding.word_length,List.append_nil] using
      copy_exec (work suffix) (SourceQuadraticEncoding.word q) suffix
  have reverse : Exec ClauseQuery.reverseLoop copied.store (4 * quadraticBits n + 1) emitted.store := by
    simpa only [copied,emitted,work,SourceQuadraticEncoding.word_length,List.length_reverse,
      List.reverse_reverse,List.append_nil] using
      ClauseQuery.reverse_exec (work suffix) (SourceQuadraticEncoding.word q).reverse
  have save : Exec saveExpected (full emitted SourceScalarState.emptySaved metadata saved) 3
      (state suffix acc {saved with expected := SourceQuadraticEncoding.word q}) :=
    Exec.seq (.action _ _) (Exec.seq (.action _ _) (.action _ _))
  have cost : loadFuel n = 1 + ((5 * quadraticBits n + 1) + ((4 * quadraticBits n + 1) + 3)) := by
    unfold loadFuel
    omega
  simpa only [loadExpected,cost] using Exec.seq load
    (Exec.seq (core_exec copy SourceScalarState.emptySaved metadata saved)
      (Exec.seq (core_exec reverse SourceScalarState.emptySaved metadata saved) save))

def prepareCompare : Block 18 := .seq (.action (.copy 0 17)) <|
  .seq (.action (.copy 5 15)) (.action (.copy 1 14))
def reject : Block 18 := .seq (.action (.clear 6)) (.action (.push 6 false))
def mask : Block 18 := .branch 16 reject reject (.seq .skip .skip)
def output : Block 18 := .seq (.action (.copy 8 6)) <|
  .seq (.action (.clear 6)) <| .seq (.action (.clear 1)) (.action (.copy 0 11))
def compare : Block 18 := .seq prepareCompare <|
  .seq (core SourceQuadraticEquality.block) <| .seq mask output
def compareFuel (n : Nat) : Nat := 12 * quadraticBits n + 15

theorem mask_exec (r : Registers) (p : SourceQuadraticProduct.Saved) (d : SourceScalarState.Data)
    (word : BitString) (head value : Bool) :
    Exec mask (full {r with active := [value]} p d ⟨[head],word⟩) 3
      (full {r with active := [head && value]} p d ⟨[head],word⟩) := by
  cases head with
  | false => exact Exec.zero rfl (Exec.seq (.action _ _) (.action _ _))
  | true => exact Exec.one rfl (Exec.seq (.skip _) (.skip _))

theorem compare_exec {n : Nat} (q candidate : Quadratic n) (suffix : BitString) (head : Bool) :
    Exec compare (state suffix candidate ⟨[head],SourceQuadraticEncoding.word q⟩) (compareFuel n)
      (full {work suffix with output := [head && qEq q candidate]} SourceScalarState.emptySaved
        (data suffix candidate) ⟨[head],SourceQuadraticEncoding.word q⟩) := by
  let metadata := data suffix candidate
  let saved : Saved := ⟨[head],SourceQuadraticEncoding.word q⟩
  let ready := SourceQuadraticEquality.ready (work []) q candidate
  let compared := SourceQuadraticEquality.finished (work []) q candidate
  let masked := {compared with active := [head && qEq q candidate]}
  have load : Exec prepareCompare (state suffix candidate saved) 3
      (full ready SourceScalarState.emptySaved metadata saved) :=
    Exec.seq (.action _ _) (Exec.seq (.action _ _) (.action _ _))
  have equal := core_exec (SourceQuadraticEquality.block_exec (work []) q candidate)
    SourceScalarState.emptySaved metadata saved
  have combine : Exec mask (full compared SourceScalarState.emptySaved metadata saved) 3
      (full masked SourceScalarState.emptySaved metadata saved) :=
    mask_exec compared SourceScalarState.emptySaved metadata (SourceQuadraticEncoding.word q)
      head (qEq q candidate)
  have finish : Exec output (full masked SourceScalarState.emptySaved metadata saved) 4
      (full {work suffix with output := [head && qEq q candidate]}
        SourceScalarState.emptySaved metadata saved) :=
    Exec.seq (.action _ _) (Exec.seq (.action _ _) (Exec.seq (.action _ _) (.action _ _)))
  have cost : compareFuel n = 3 + (SourceQuadraticEquality.fuel n + (3 + 4)) := by
    simp only [compareFuel,SourceQuadraticEquality.fuel]
    omega
  simpa only [compare,cost,ready,compared,metadata,saved] using
    Exec.seq load (Exec.seq equal (Exec.seq combine finish))

def block : Block 18 := .seq loadExpected <|
  .seq (scalar SourceTailPolynomial.block) compare
def fuel {n : Nat} (t : TailForm n) : Nat :=
  loadFuel n + (SourceTailPolynomial.fuel t + compareFuel n)

theorem block_exec {n : Nat} (h : Affine n) (q : Quadratic n) (t : TailForm n) (suffix : BitString) :
    Exec block (state (SourceQuadraticEncoding.word q ++
      ((SourceComputedTailEncoding.codec n).encode t ++ suffix))
      (zero n) ⟨[aEq h (aConst n true)],[]⟩) (fuel t) (finished h q t suffix) := by
  let saved : Saved := ⟨[aEq h (aConst n true)],SourceQuadraticEncoding.word q⟩
  have load := load_exec q (zero n) ((SourceComputedTailEncoding.codec n).encode t ++ suffix)
    ⟨[aEq h (aConst n true)],[]⟩
  have candidate := scalar_exec (SourceTailPolynomial.block_exec t suffix
    ((SourceComputedTailEncoding.codec n).encode t ++ suffix)) saved
  have check := compare_exec q t.polynomial suffix (aEq h (aConst n true))
  simpa only [block,fuel,state,SourceScalarState.state,saved,full,finished,checks] using
    Exec.seq load (Exec.seq candidate check)

theorem fuel_bound {n : Nat} (t : TailForm n) :
    fuel t ≤ 65 * quadraticBits n + 50 * n + 104 := by
  have candidate := SourceTailPolynomial.fuel_bound t
  simp only [fuel,loadFuel,compareFuel]
  omega

end PNP.Concrete.ResidualReduction.SourceCoefficientGateTail
