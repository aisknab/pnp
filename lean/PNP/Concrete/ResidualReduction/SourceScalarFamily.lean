import PNP.Concrete.ResidualReduction.SourceScalarRow

/-! Complete selected scalar construction from the actual family coefficient
stream. The initialized accumulator, every selected product, every skipped row
and the final output copy are counted. Bounds are uniform in encoded source
size; physical register-copy compilation and the full successor remain separate. -/

namespace PNP.Concrete.ResidualReduction.SourceScalarFamily
open PNP.Concrete PNP.Concrete.BitRegister PNP.Concrete.NormalizerBlocks
open PNP.Concrete.NormalizerBlocks.Occurrence
open PNP.Concrete.NativeNormalization.NativeBitCodec
open PNP.Concrete.ResidualReduction.FactoredContraction
open PNP.Concrete.ResidualReduction.MatrixInstructions
open PNP.Concrete.ResidualReduction.SourceMatrixEncoding
open PNP.Concrete.ResidualReduction.SourceScalarState

def rowLoop : Block 16 := .loop 0 SourceScalarRow.block
def loopFuel {n : Nat} : Family n → Nat
  | [] => 1
  | r :: F => 1 + (SourceScalarRow.fuel n r.selected + loopFuel F)

theorem loop_exec {n : Nat} (F : Family n) (q : Quadratic n) :
    Exec rowLoop (state (familyBits F) q) (loopFuel F) (state [] (qAdd q (scalar F))) := by
  induction F generalizing q with
  | nil =>
    change Exec rowLoop (state [] q) 1 (state [] (qAdd q (zero n)))
    rw [add_zero_right]
    exact Exec.loopStop rfl
  | cons r F ih =>
    have first := SourceScalarRow.block_exec r q (familyBits F) (familyBits (r :: F))
    have rest := ih (SourceScalarState.step q r)
    rw [step_scalar] at rest
    have present : (state (familyBits (r :: F)) q).get 0 =
        r.selected :: (affineWord r.left ++ (affineWord r.right ++ familyBits F)) := by
      change rowWord r ++ familyBits F = _
      simp only [rowWord,List.cons_append,List.append_assoc]
    have checked := Exec.loopStep (source := (0 : Fin 16)) present first rest
    simpa only [rowLoop,loopFuel,state,familyBits] using checked

theorem loopFuel_bound {n : Nat} (F : Family n) :
    loopFuel F ≤ (SourceScalarRow.fuel n true + 1) * F.length + 1 := by
  induction F with
  | nil => simp only [loopFuel,List.length_nil,Nat.mul_zero]; omega
  | cons r F ih =>
    have row := SourceScalarRow.fuel_le_selected n r.selected
    simp only [loopFuel,List.length_cons,Nat.mul_add,Nat.mul_one]
    omega

def finish : Block 16 := .action (.copy 8 15)
def finished {n : Nat} (q : Quadratic n) : Store 16 :=
  full {work [] with output := SourceQuadraticEncoding.word q} emptySaved (data [] q)
def block : Block 16 := .seq SourceScalarInitialization.block <| .seq rowLoop finish
def fuel {n : Nat} (F : Family n) : Nat := SourceScalarInitialization.fuel n + (loopFuel F + 1)

theorem block_exec {n : Nat} (F : Family n) :
    Exec block (initial n (familyBits F)) (fuel F) (finished (scalar F)) := by
  have start := SourceScalarInitialization.block_exec n (familyBits F)
  have rows := loop_exec F (zero n)
  rw [add_zero_left] at rows
  have stop : Exec finish (state [] (scalar F)) 1 (finished (scalar F)) := .action _ _
  exact Exec.seq start (Exec.seq rows stop)

theorem output_get {n : Nat} (q : Quadratic n) :
    (finished q).get 8 = SourceQuadraticEncoding.word q := rfl
theorem output_decode {n : Nat} (F : Family n) :
    (SourceQuadraticEncoding.codec n).decode ((finished (scalar F)).get 8) = some (scalar F) :=
  SourceQuadraticEncoding.roundtrip (scalar F)
theorem output_length {n : Nat} (F : Family n) :
    ((finished (scalar F)).get 8).length = quadraticBits n :=
  SourceQuadraticEncoding.word_length (scalar F)

def rowBound (L : Nat) : Nat :=
  (7 * L + 17) * L + 15 * ((L + 1) * (L + 1)) + 18 * L + 54
def sourceBound (L : Nat) : Nat :=
  (rowBound L + 1) * L + 6 * ((L + 1) * (L + 1)) + 4 * L + 11

theorem rowFuel_bound (n : Nat) : SourceScalarRow.fuel n true ≤ rowBound n := by
  have product := SourceQuadraticProduct.forwardFuel_bound n
  have width := SourceQuadraticEncoding.word_bound (zero n)
  rw [SourceQuadraticEncoding.word_length] at width
  rw [SourceScalarRow.selected_fuel]
  unfold rowBound
  omega

theorem rowBound_mono {n m : Nat} (h : n ≤ m) : rowBound n ≤ rowBound m := by
  have product : (7 * n + 17) * n ≤ (7 * m + 17) * m :=
    Nat.mul_le_mul (Nat.add_le_add_right (Nat.mul_le_mul_left 7 h) 17) h
  have square : (n + 1) * (n + 1) ≤ (m + 1) * (m + 1) :=
    Nat.mul_le_mul (Nat.add_le_add_right h 1) (Nat.add_le_add_right h 1)
  unfold rowBound
  omega

theorem fuel_source_bound {n : Nat} (F : Family n) :
    fuel F ≤ sourceBound (SourceMatrixEncoding.codec.encode ⟨n,F⟩).length := by
  let L := (SourceMatrixEncoding.codec.encode ⟨n,F⟩).length
  have dimension : n ≤ L := SourceMatrixEncoding.dimension_bound n F
  have rows : F.length ≤ L := SourceMatrixEncoding.rowCount_bound n F
  have perRow : SourceScalarRow.fuel n true ≤ rowBound L :=
    Nat.le_trans (rowFuel_bound n) (rowBound_mono dimension)
  have allRows := loopFuel_bound F
  have product := Nat.mul_le_mul (Nat.add_le_add_right perRow 1) rows
  have square : (n + 1) * (n + 1) ≤ (L + 1) * (L + 1) :=
    Nat.mul_le_mul (Nat.add_le_add_right dimension 1) (Nat.add_le_add_right dimension 1)
  have initialization := SourceScalarInitialization.fuel_bound n
  change fuel F ≤ sourceBound L
  unfold fuel sourceBound
  omega

theorem output_source_bound {n : Nat} (F : Family n) :
    ((finished (scalar F)).get 8).length ≤
      ((SourceMatrixEncoding.codec.encode ⟨n,F⟩).length + 1) *
        ((SourceMatrixEncoding.codec.encode ⟨n,F⟩).length + 1) := by
  have dimension := SourceMatrixEncoding.dimension_bound n F
  have bound := SourceQuadraticEncoding.word_bound (scalar F)
  have square := Nat.mul_le_mul (Nat.add_le_add_right dimension 1) (Nat.add_le_add_right dimension 1)
  exact Nat.le_trans bound square

end PNP.Concrete.ResidualReduction.SourceScalarFamily
