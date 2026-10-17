import PNP.Concrete.ResidualReduction.SourceAxisWitnessInstructions

/-! Produce both parameter vectors from the exact four-bit candidate choice.
The first vector is saved while the second is constructed; the original input
suffix and both selected supports are preserved by the all-input refinement. -/

namespace PNP.Concrete.ResidualReduction.SourceWitnessPair
open PNP.Concrete PNP.Concrete.BitRegister
open PNP.Concrete.NormalizerBlocks PNP.Concrete.NormalizerBlocks.Occurrence
open PNP.Concrete.ResidualReduction.FactoredContraction
open PNP.Concrete.ResidualReduction.ConstrainedBilinear
open PNP.Concrete.ResidualReduction.SourceCandidateChoice (Choice)
open PNP.Concrete.ResidualReduction.SourceLinePullback (transfers transfers_exec)

structure Saved where
  width : BitString
  first : BitString
  second : BitString
  left : BitString
def Saved.store (s : Saved) : Store 4 :=
  .cons s.width (.cons s.first (.cons s.second (.cons s.left .nil)))
def store (core : Store 14) (s : Saved) : Store 18 := Frame.join core s.store
def data {n : Nat} (j l : Fin n) (left : BitString) : Saved :=
  ⟨List.replicate n true, List.replicate j.val true, List.replicate l.val true, left⟩
def rowInput (r : Registers) (c : Choice) : Registers :=
  {r with input := SourceCandidateChoice.axisBits c.2 ++ r.input}
def start (r : Registers) {m n : Nat} (i k : Fin m) (j l : Fin n) (c : Choice) : Store 18 :=
  store (SourceAxisWitness.start (rowInput r c) i k c.1) (data j l [])
def afterRow (r : Registers) {m n : Nat} (i k : Fin m) (j l : Fin n) (c : Choice) : Store 18 :=
  store (SourceAxisWitness.result (rowInput r c) i k c.1) (data j l [])
def rowCore (r : Registers) {m : Nat} (i k : Fin m) (c : Choice) : Registers :=
  SourceAxisWitness.outputCore r (SourceAxisWitness.point i k c.1)
def rowBytes {m : Nat} (i k : Fin m) (c : Choice) : BitString :=
  (SourceEncoding.pointCodec m).encode (SourceAxisWitness.point i k c.1)
def columnStart (r : Registers) {m n : Nat} (i k : Fin m) (j l : Fin n) (c : Choice) : Store 18 :=
  store (SourceAxisWitness.start (rowCore r i k c) j l c.2) (data j l (rowBytes i k c))
def result (r : Registers) {m n : Nat} (i k : Fin m) (j l : Fin n) (c : Choice) : Store 18 :=
  store (SourceAxisWitness.result (rowCore r i k c) j l c.2) (data j l (rowBytes i k c))

def handoff : Block 18 := transfers [.copy 17 8, .copy 9 14, .copy 10 15, .copy 11 16]
theorem handoff_exec (r : Registers) {m n : Nat} (i k : Fin m) (j l : Fin n) (c : Choice) :
    Exec handoff (afterRow r i k j l c) 5 (columnStart r i k j l c) :=
  transfers_exec _ _
def block : Block 18 := .seq (Frame.block 4 SourceAxisWitness.block) <|
  .seq handoff (Frame.block 4 SourceAxisWitness.block)
def fuel {m n : Nat} (i k : Fin m) (j l : Fin n) (c : Choice) : Nat :=
  SourceAxisWitness.fuel i k c.1 + (5 + SourceAxisWitness.fuel j l c.2)
theorem block_exec (r : Registers) {m n : Nat} (i k : Fin m) (j l : Fin n) (c : Choice) :
    Exec block (start r i k j l c) (fuel i k j l c) (result r i k j l c) :=
  Exec.seq (Frame.execution (SourceAxisWitness.block_exec (rowInput r c) i k c.1) (data j l []).store)
    (Exec.seq (handoff_exec r i k j l c)
      (Frame.execution (SourceAxisWitness.block_exec (rowCore r i k c) j l c.2)
        (data j l (rowBytes i k c)).store))

theorem left_exact (r : Registers) {m n : Nat} (i k : Fin m) (j l : Fin n) (c : Choice) :
    (result r i k j l c).get 17 =
      (SourceEncoding.pointCodec m).encode (sumUnits (SourceCandidateChoice.decode i k j l c).1) := by
  change (SourceEncoding.pointCodec m).encode (SourceAxisWitness.point i k c.1) = _
  rw [SourceAxisWitness.point_exact]
  rfl
theorem right_exact (r : Registers) {m n : Nat} (i k : Fin m) (j l : Fin n) (c : Choice) :
    (result r i k j l c).get 8 =
      (SourceEncoding.pointCodec n).encode (sumUnits (SourceCandidateChoice.decode i k j l c).2) := by
  change (SourceEncoding.pointCodec n).encode (SourceAxisWitness.point j l c.2) = _
  rw [SourceAxisWitness.point_exact]
  rfl
theorem tail_preserved (r : Registers) {m n : Nat} (i k : Fin m) (j l : Fin n) (c : Choice) :
    (result r i k j l c).get 0 = r.input := rfl
theorem fuel_bound {m n : Nat} (i k : Fin m) (j l : Fin n) (c : Choice) :
    fuel i k j l c ≤ 15 * m + 15 * n + 65 := by
  have row := SourceAxisWitness.fuel_bound i k c.1
  have column := SourceAxisWitness.fuel_bound j l c.2
  unfold fuel
  omega
def program : Program 18 := block.program 0 8
theorem program_run (r : Registers) {m n : Nat} (i k : Fin m) (j l : Fin n) (c : Choice) :
    BitRegister.run program (fuel i k j l c + 1) ⟨.running 0, start r i k j l c⟩ =
      ⟨.accepted, result r i k j l c⟩ := (block_exec r i k j l c).program_run 0 8

end PNP.Concrete.ResidualReduction.SourceWitnessPair
