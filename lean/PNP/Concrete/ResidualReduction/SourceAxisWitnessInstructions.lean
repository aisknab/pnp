import PNP.Concrete.ResidualReduction.SourceAxisWitnessAlgebra

/-! Decode one selected axis and construct its exact point bytes with literal
counted unit and XOR instructions. The untouched input suffix survives even the
two-unit branch, so a second axis can follow. No vector is supplied by a caller. -/

namespace PNP.Concrete.ResidualReduction.SourceAxisWitness
open PNP.Concrete PNP.Concrete.BitRegister
open PNP.Concrete.NormalizerBlocks PNP.Concrete.NormalizerBlocks.Occurrence
open PNP.Concrete.ResidualReduction.FactoredContraction
open PNP.Concrete.ResidualReduction.ConstrainedBilinear
open PNP.Concrete.ResidualReduction.SourceCandidateChoice (Axis)
open PNP.Concrete.ResidualReduction.SourceLinePullback (transfers transfers_exec)

structure Saved where
  width : BitString
  first : BitString
  second : BitString
  work : BitString
  tail : BitString
def Saved.store (s : Saved) : Store 5 :=
  .cons s.width (.cons s.first (.cons s.second (.cons s.work (.cons s.tail .nil))))
def store (r : Registers) (s : Saved) : Store 14 := Frame.join r.store s.store
def data {n : Nat} (i k : Fin n) (work tail : BitString) : Saved :=
  ⟨List.replicate n true, List.replicate i.val true, List.replicate k.val true, work, tail⟩
def selected {n : Nat} (i k : Fin n) (second : Bool) : Fin n := if second then k else i
def clean (r : Registers) : Registers :=
  {r with target := [], remaining := [], excess := [], mode := [], output := []}
def ready (r : Registers) (s : Saved) (second : Bool) : Registers :=
  {clean r with target := if second then s.second else s.first, remaining := s.width}
def unitDone (r : Registers) {n : Nat} (j : Fin n) : Registers :=
  {clean r with output := ((SourceEncoding.pointCodec n).encode (unitPoint n j)).reverse}
def outputCore (r : Registers) {n : Nat} (z : Point n) : Registers :=
  {clean r with output := (SourceEncoding.pointCodec n).encode z}

def prepare (second : Bool) : Block 14 :=
  transfers [.copy 1 (if second then 11 else 10), .copy 2 9, .clear 3, .clear 5, .clear 8]
theorem prepare_exec (r : Registers) (s : Saved) (second : Bool) :
    Exec (prepare second) (store r s) 6 (store (ready r s second) s) := by
  cases second <;> exact transfers_exec _ _

def unitBlock (second : Bool) : Block 14 :=
  .seq (prepare second) (Frame.block 5 SourceUnitDirectionInstructions.block)
def unitFuel (n j : Nat) : Nat := 6 + SourceUnitDirectionInstructions.fuel n j
theorem unit_exec (r : Registers) {n : Nat} (i k : Fin n) (second : Bool) (work tail : BitString) :
    Exec (unitBlock second) (store r (data i k work tail))
      (unitFuel n (selected i k second).val)
      (store (unitDone r (selected i k second)) (data i k work tail)) := by
  apply Exec.seq (prepare_exec r (data i k work tail) second)
  have checked := Frame.execution
    (SourceUnitDirectionInstructions.block_exec (clean r) n (selected i k second))
    (data i k work tail).store
  cases second <;>
    simpa only [store, ready, clean, data, selected, unitDone, Bool.false_eq_true, if_false, if_true,
      List.append_nil] using checked

def single (second : Bool) : Block 14 :=
  .seq (unitBlock second) (Frame.block 5 SourceLineQueryMatrixPadding.reverseOutput)
def singleFuel (n j : Nat) : Nat := unitFuel n j + (4 * n + 3)
theorem single_exec (r : Registers) {n : Nat} (i k : Fin n) (second : Bool) (work tail : BitString) :
    Exec (single second) (store r (data i k work tail))
      (singleFuel n (selected i k second).val)
      (store (outputCore r (unitPoint n (selected i k second))) (data i k work tail)) := by
  apply Exec.seq (unit_exec r i k second work tail)
  simpa only [store, unitDone, outputCore, clean, List.length_reverse, SourceEncoding.point_length,
    List.reverse_reverse] using Frame.execution
      (SourceLineQueryMatrixPadding.reverse_output_exec (clean r)
        ((SourceEncoding.pointCodec n).encode (unitPoint n (selected i k second))).reverse)
      (data i k work tail).store

def stageXor : Block 14 :=
  transfers [.copy 13 0, .copy 0 12, .copy 5 8, .copy 2 9, .clear 3]
def finishXor : Block 14 :=
  transfers [.copy 8 3, .clear 3, .copy 0 13, .clear 12, .clear 13]
def both : Block 14 :=
  .seq (unitBlock false) <| .seq (.action (.copy 12 8)) <|
  .seq (unitBlock true) <| .seq stageXor <|
  .seq (Frame.block 5 MatrixInstructions.xorLoop) finishXor
def bothFuel (n i k : Nat) : Nat :=
  unitFuel n i + (1 + (unitFuel n k + (6 + ((7 * n + 1) + 6))))

theorem both_exec (r : Registers) {n : Nat} (i k : Fin n) :
    Exec both (store r (data i k [] [])) (bothFuel n i.val k.val)
      (store (outputCore r (pXor (unitPoint n i) (unitPoint n k))) (data i k [] [])) := by
  let u := ((SourceEncoding.pointCodec n).encode (unitPoint n i)).reverse
  let v := ((SourceEncoding.pointCodec n).encode (unitPoint n k)).reverse
  let z := (SourceEncoding.pointCodec n).encode (pXor (unitPoint n i) (unitPoint n k))
  let first := unitDone r i
  let second := unitDone r k
  let staged : Registers := {second with input := u, remaining := List.replicate n true, mode := v, excess := []}
  let xored : Registers := {second with input := [], remaining := [], mode := [], excess := z}
  have one : Exec (unitBlock false) (store r (data i k [] [])) (unitFuel n i.val)
      (store first (data i k [] [])) := unit_exec r i k false [] []
  have save : Exec (.action (.copy (12 : Fin 14) 8)) (store first (data i k [] [])) 1
      (store first (data i k u [])) := .action _ _
  have two : Exec (unitBlock true) (store first (data i k u [])) (unitFuel n k.val)
      (store second (data i k u [])) := unit_exec first i k true u []
  have stage : Exec stageXor (store second (data i k u [])) 6
      (store staged (data i k u r.input)) := transfers_exec _ _
  have lengths : u.length = v.length := by
    simp only [u, v, List.length_reverse, SourceEncoding.point_length]
  have xor : Exec (Frame.block 5 MatrixInstructions.xorLoop) (store staged (data i k u r.input))
      (7 * n + 1) (store xored (data i k u r.input)) := by
    simpa only [store, u, v, z, staged, xored, List.append_nil, List.length_reverse,
      SourceEncoding.point_length, xor_reversed_bytes] using
      Frame.execution (MatrixInstructions.xor_exec {second with excess := []} u v [] lengths)
        (data i k u r.input).store
  have finish : Exec finishXor (store xored (data i k u r.input)) 6
      (store (outputCore r (pXor (unitPoint n i) (unitPoint n k))) (data i k [] [])) :=
    transfers_exec _ _
  exact Exec.seq one (Exec.seq save (Exec.seq two (Exec.seq stage (Exec.seq xor finish))))

def read (zero one : Block 14) : Block 14 :=
  .branch 0 .skip (.seq (.action (.pop 0)) zero) (.seq (.action (.pop 0)) one)
def block : Block 14 := read (read .skip (single true)) (read (single false) both)
def bodyFuel {n : Nat} (i k : Fin n) : Axis → Nat
  | .first => singleFuel n i.val
  | .second => singleFuel n k.val
  | .both => bothFuel n i.val k.val
def fuel {n : Nat} (i k : Fin n) (a : Axis) : Nat := 4 + bodyFuel i k a
def start (r : Registers) {n : Nat} (i k : Fin n) (a : Axis) : Store 14 :=
  store {r with input := SourceCandidateChoice.axisBits a ++ r.input} (data i k [] [])
def result (r : Registers) {n : Nat} (i k : Fin n) (a : Axis) : Store 14 :=
  store (outputCore r (point i k a)) (data i k [] [])

theorem block_exec (r : Registers) {n : Nat} (i k : Fin n) (a : Axis) :
    Exec block (start r i k a) (fuel i k a) (result r i k a) := by
  cases a with
  | first =>
    have checked : Exec block (start r i k .first)
        (1 + (1 + (1 + (1 + singleFuel n i.val)))) (result r i k .first) :=
      Exec.one rfl (Exec.seq (.action _ _) (Exec.zero rfl (Exec.seq (.action _ _) (single_exec r i k false [] []))))
    simpa only [fuel, bodyFuel, ← Nat.add_assoc] using checked
  | second =>
    have checked : Exec block (start r i k .second)
        (1 + (1 + (1 + (1 + singleFuel n k.val)))) (result r i k .second) :=
      Exec.zero rfl (Exec.seq (.action _ _) (Exec.one rfl (Exec.seq (.action _ _) (single_exec r i k true [] []))))
    simpa only [fuel, bodyFuel, ← Nat.add_assoc] using checked
  | both =>
    have checked : Exec block (start r i k .both)
        (1 + (1 + (1 + (1 + bothFuel n i.val k.val)))) (result r i k .both) :=
      Exec.one rfl (Exec.seq (.action _ _) (Exec.one rfl (Exec.seq (.action _ _) (both_exec r i k))))
    simpa only [fuel, bodyFuel, ← Nat.add_assoc] using checked

theorem output_exact (r : Registers) {n : Nat} (i k : Fin n) (a : Axis) :
    (result r i k a).get 8 =
      (SourceEncoding.pointCodec n).encode (sumUnits (SourceCandidateChoice.support i k a)) := by
  rw [← point_exact]
  exact Frame.get_core _ _ (8 : Fin 9)
theorem tail_preserved (r : Registers) {n : Nat} (i k : Fin n) (a : Axis) :
    (result r i k a).get 0 = r.input := Frame.get_core _ _ (0 : Fin 9)
theorem fuel_bound {n : Nat} (i k : Fin n) (a : Axis) : fuel i k a ≤ 15 * n + 30 := by
  have first := SourceUnitDirectionInstructions.fuel_bound n i
  have second := SourceUnitDirectionInstructions.fuel_bound n k
  cases a <;> simp only [fuel, bodyFuel, singleFuel, bothFuel, unitFuel] <;> omega

def costPolynomial : NatPolynomial := .add (.mul (.constant 15) .variable) (.constant 30)
theorem bounded_exec (r : Registers) {n : Nat} (i k : Fin n) (a : Axis) (L : Nat) (h : n ≤ L) :
    ∃ used ≤ costPolynomial.eval L, Exec block (start r i k a) used (result r i k a) := by
  refine ⟨fuel i k a, ?_, block_exec r i k a⟩
  have bound := fuel_bound i k a
  change fuel i k a ≤ 15 * L + 30
  omega

def program : Program 14 := block.program 0 8
theorem program_run (r : Registers) {n : Nat} (i k : Fin n) (a : Axis) :
    BitRegister.run program (fuel i k a + 1) ⟨.running 0, start r i k a⟩ =
      ⟨.accepted, result r i k a⟩ := (block_exec r i k a).program_run 0 8

end PNP.Concrete.ResidualReduction.SourceAxisWitness
