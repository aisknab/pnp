import PNP.Concrete.ResidualReduction.SourceChartedSuccessorRaw

/-! A uniform cubic encoded-packet bound for the connected source instructions.
Every header read, packet transfer, scalar, candidate, gate and reduction call is
included. Whole-word copying still counts as one source instruction here; this
is not the physical machine or complete contraction-history runtime theorem. -/

namespace PNP.Concrete.ResidualReduction.SourceChartedSuccessorBounds
open PNP.Concrete PNP.Concrete.BitRegister PNP.Concrete.NormalizerBlocks
open PNP.Concrete.NativeNormalization.NativeBitCodec
open PNP.Concrete.ResidualReduction.FactoredContraction
open PNP.Concrete.ResidualReduction.MatrixInstructions
open PNP.Concrete.ResidualReduction.SourceChartedSuccessorState
open PNP.Concrete.ResidualReduction.SourceChartedSuccessorInput (packet)

theorem normals_length {n : Nat} (normals : Option (Affine (n + 1) × Affine (n + 1))) :
    ((normalsCodec n).encode normals).length ≤ 2 * n + 5 := by
  cases normals with
  | none =>
    rw [SourceChartedSuccessorNormals.none_bytes]
    simp only [List.length_cons,List.length_nil]
    omega
  | some p =>
    rcases p with ⟨a,b⟩
    rw [SourceChartedSuccessorNormals.some_bytes]
    simp only [List.length_cons,List.length_append,affineWord_length]
    omega

theorem candidate_fuel {n : Nat} (k : Fin (n + 1))
    (normals : Option (Affine (n + 1) × Affine (n + 1))) :
    SourceComputedTailInstructions.fuel n k.val normals.isSome ≤ 40 * quadraticBits n + 92 * n + 166 := by
  have pivot := k.isLt
  cases normals with
  | none => rw [Option.isSome,SourceComputedTailInstructions.affineFuel_exact]; omega
  | some p => rw [Option.isSome,SourceComputedTailInstructions.planeFuel_exact]; omega

theorem tail_fuel {n : Nat} (k : Fin (n + 1))
    (normals : Option (Affine (n + 1) × Affine (n + 1))) :
    SourceChartedSuccessorTail.fuel k normals ≤ 40 * quadraticBits n + 111 * n + 254 := by
  have size := normals_length normals
  have candidate := candidate_fuel k normals
  simp only [SourceChartedSuccessorTail.fuel,SourceChartedSuccessorTail.loadFuel]
  omega

theorem gate_fuel {n : Nat} (F : Family (n + 1)) (k : Fin (n + 1))
    (normals : Option (Affine (n + 1) × Affine (n + 1))) :
    SourceChartedSuccessorGate.fuel F k normals ≤ 79 * quadraticBits n + 98 * n + 200 := by
  have gate := SourceCoefficientGateRaw.fuel_bound (candidate F k normals)
  have width : quadraticBits (n + 1) = quadraticBits n + n + 1 := by
    simp only [quadraticBits,affineBits]
    omega
  simp only [SourceChartedSuccessorGate.fuel,SourceChartedSuccessorGate.prepareFuel,width]
  omega

theorem finish_fuel {n : Nat} (F : Family (n + 1)) (k : Fin (n + 1))
    (normals : Option (Affine (n + 1) × Affine (n + 1))) :
    SourceChartedSuccessorFinish.fuel F k normals ≤
      165 * ((SourceEncoding.familyCodec (n + 1)).encode F).length + 692 * n + 949 := by
  have size := SourceComputedTailEncoding.bytes_bound (candidate F k normals)
  have reduce := SourceFamilyReductionRaw.fuel_encoded_bound (candidate F k normals) F
  rw [SourceFamilyReductionRaw.packet_length] at reduce
  cases branch : SourceChartedSuccessorGate.decision F k normals <;>
    simp only [SourceChartedSuccessorFinish.fuel,branch,Bool.false_eq_true,↓reduceIte,
      SourceChartedSuccessorFinish.successFuel,SourceChartedSuccessorFinish.prepareFuel] <;> omega

theorem combined_fuel {n : Nat} (F : Family (n + 1)) (k : Fin (n + 1))
    (normals : Option (Affine (n + 1) × Affine (n + 1))) :
    SourceChartedSuccessorRaw.fuel F k normals ≤
      SourceScalarFamily.sourceBound (SourceMatrixEncoding.codec.encode ⟨n + 1,F⟩).length +
      119 * quadraticBits n + 927 * n + 4 * F.length +
      165 * ((SourceEncoding.familyCodec (n + 1)).encode F).length + 1515 := by
  have pivot := k.isLt
  have normal := SourceChartedSuccessorNormals.fuel_bound n normals.isSome
  have scalarRun := SourceScalarFamily.fuel_source_bound F
  have tail := tail_fuel k normals
  have gate := gate_fuel F k normals
  have finish := finish_fuel F k normals
  simp only [SourceChartedSuccessorRaw.fuel,SourceChartedSuccessorInput.headersFuel,
    SourceChartedSuccessorScalar.fuel,SourceChartedSuccessorScalar.loadFuel]
  omega

theorem scalar_bound_mono {n m : Nat} (h : n ≤ m) :
    SourceScalarFamily.sourceBound n ≤ SourceScalarFamily.sourceBound m := by
  have row := SourceScalarFamily.rowBound_mono h
  have product := Nat.mul_le_mul (Nat.add_le_add_right row 1) h
  have square := Nat.mul_le_mul (Nat.add_le_add_right h 1) (Nat.add_le_add_right h 1)
  unfold SourceScalarFamily.sourceBound
  omega

def bound (L : Nat) : Nat :=
  SourceScalarFamily.sourceBound L + 120 * ((L + 1) * (L + 1)) + 1100 * L + 1600

theorem source_bound {n : Nat} (F : Family (n + 1)) (k : Fin (n + 1))
    (normals : Option (Affine (n + 1) × Affine (n + 1))) :
    SourceChartedSuccessorRaw.fuel F k normals + 1 ≤ bound (packet F k normals).length := by
  let L := (packet F k normals).length
  let S := (SourceMatrixEncoding.codec.encode ⟨n + 1,F⟩).length
  have sourceLength : S = n + 2 + ((SourceEncoding.familyCodec (n + 1)).encode F).length := by
    change (natural (n + 1) ++ (SourceEncoding.familyCodec (n + 1)).encode F).length = _
    simp only [List.length_append,natural_length,Nat.add_assoc]
    omega
  have packetLength := SourceChartedSuccessorInput.packet_length F k normals
  have source : S ≤ L := by dsimp only [L]; omega
  have dimension : n ≤ L := by dsimp only [L]; omega
  have family : ((SourceEncoding.familyCodec (n + 1)).encode F).length ≤ L := by
    dsimp only [L]; omega
  have rows : F.length ≤ L :=
    Nat.le_trans (SourceMatrixEncoding.rowCount_bound (n + 1) F) source
  have scalarBound := scalar_bound_mono source
  have width := SourceQuadraticEncoding.word_bound (SourceScalarState.zero n)
  rw [SourceQuadraticEncoding.word_length] at width
  have square := Nat.mul_le_mul (Nat.add_le_add_right dimension 1) (Nat.add_le_add_right dimension 1)
  have total := combined_fuel F k normals
  change SourceChartedSuccessorRaw.fuel F k normals + 1 ≤ bound L
  unfold bound
  change SourceScalarFamily.sourceBound S ≤ SourceScalarFamily.sourceBound L at scalarBound
  change SourceChartedSuccessorRaw.fuel F k normals ≤ SourceScalarFamily.sourceBound S +
    119 * quadraticBits n + 927 * n + 4 * F.length +
    165 * ((SourceEncoding.familyCodec (n + 1)).encode F).length + 1515 at total
  omega

theorem bound_cubic (L : Nat) :
    bound L = 22 * (L * L * L) + 191 * (L * L) + 1426 * L + 1737 := by
  simp only [bound,SourceScalarFamily.sourceBound,SourceScalarFamily.rowBound,
    Nat.mul_add,Nat.add_mul,Nat.mul_assoc,Nat.mul_one,Nat.one_mul]
  omega

end PNP.Concrete.ResidualReduction.SourceChartedSuccessorBounds
