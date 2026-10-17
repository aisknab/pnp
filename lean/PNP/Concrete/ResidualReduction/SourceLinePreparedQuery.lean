import PNP.Concrete.ResidualReduction.SourceLineOutputInstructions

/-! Complete prepared execution of sourceLineQuery, including all computed
maps, ordered witness selection, original-coordinate direction lifting and
canonical optional output. Raw input parsing and concrete tape runtime remain
separate obligations; no whole-contraction runtime claim is made here. -/

namespace PNP.Concrete.ResidualReduction.SourceLinePreparedQuery
open PNP.Concrete PNP.Concrete.BitRegister
open PNP.Concrete.NormalizerBlocks PNP.Concrete.NormalizerBlocks.Occurrence
open PNP.Concrete.ResidualReduction.FactoredContraction
open PNP.Concrete.ResidualReduction.BinaryLinear
open PNP.Concrete.ResidualReduction.SourceDirections
open PNP.Concrete.ResidualReduction.MatrixSolutionEncoding
open PNP.Concrete.ResidualReduction.SourceLineWitness (Selection selection leftPoint rightPoint pickFrame)
open PNP.Concrete.ResidualReduction.SourceWitnessLift (store)

def rawPair {n : Nat} (F : Family n) (a : Affine n) (p : Selection F a) :
    Point (n + F.length) × Point (directionSpace F [a]).parameters :=
  ((SourceLinePullback.leftSpace F a).direction (leftPoint F a p),
    (SourceLinePullback.rightSpace F a).direction (rightPoint F a p))
theorem selection_raw {n : Nat} (F : Family n) (a : Affine n) :
    (selection F a).map (rawPair F a) = SourceLine.lineRawQuery F a := by
  rw [SourceLinePullback.exact_query_interface, SourceOrderedMatrixSelector.witness_exact]
  cases seeds : SourceOrderedSelectorPrelude.selectedSeeds
      (SourceLinePullback.normalPull F a) (SourceLinePullback.activityPull F a) with
  | none =>
    simp only [selection, SourceMatrixWitness.selected, seeds, Option.bind_none, Option.map_none]
  | some p =>
    rcases p with ⟨e, f⟩
    cases choice : SourceCandidateSelection.choice
        (SourceLinePullback.normalPull F a) (SourceLinePullback.activityPull F a) e.1 f.1 e.2 f.2 with
    | none =>
      simp only [selection, SourceMatrixWitness.selected, seeds, Option.bind_some, choice, Option.map_none]
    | some c =>
      simp only [selection, SourceMatrixWitness.selected, seeds, Option.bind_some, choice, Option.map_some,
        rawPair, leftPoint, rightPoint, SourceAxisWitness.point_exact, SourceCandidateChoice.decode]

def saved {n : Nat} (F : Family n) (a : Affine n) (p : Selection F a) : Store 29 :=
  SourceWitnessLift.resultData (pickFrame F a p)
    (SourceLinePullback.leftSpace F a).forms (SourceLinePullback.rightSpace F a).forms
    (leftPoint F a p) (rightPoint F a p)
theorem retained_map {n : Nat} (F : Family n) (a : Affine n) (p : Selection F a) :
    (saved F a p).get 19 = mapBits (directionSpace F [a]).forms := by
  simp only [saved, SourceWitnessLift.resultData, SourceWitnessLift.saveLeft, SourceWitnessLift.saveParameter,
    Store.get_set, show (19 : Fin 29) ≠ 11 by decide, show (19 : Fin 29) ≠ 10 by decide, if_false]
  rfl
theorem retained_width {n : Nat} (F : Family n) (a : Affine n) (p : Selection F a) :
    (saved F a p).get 20 = List.replicate (directionSpace F [a]).parameters true := by
  simp only [saved, SourceWitnessLift.resultData, SourceWitnessLift.saveLeft, SourceWitnessLift.saveParameter,
    Store.get_set, show (20 : Fin 29) ≠ 11 by decide, show (20 : Fin 29) ≠ 10 by decide, if_false]
  rfl
theorem retained_joint {n : Nat} (F : Family n) (a : Affine n) (p : Selection F a) :
    (saved F a p).get 11 = (SourceEncoding.pointCodec (n + F.length)).encode (rawPair F a p).1 :=
  Store.get_set_same _ _ _

def finished {n : Nat} (F : Family n) (a : Affine n) (p : Selection F a) : Store 38 :=
  store (SourceLineOutput.finished (rawPair F a p).1 (directionSpace F [a]).forms (rawPair F a p).2) (saved F a p)
theorem lift_exec {n : Nat} (F : Family n) (a : Affine n) (p : Selection F a) :
    Exec SourceLineOutput.success (SourceLineWitness.liftedResult F a p)
      (SourceLineOutput.successFuel (n + F.length) n (directionSpace F [a]).parameters) (finished F a p) :=
  SourceLineOutput.success_exec
    (SourceWitnessLift.resultCore (SourceLinePullback.rightSpace F a).forms (rightPoint F a p))
    (saved F a p) (rawPair F a p).1 (directionSpace F [a]).forms (rawPair F a p).2
    rfl (retained_joint F a p) (retained_map F a p) (retained_width F a p)

def finishFuel {n : Nat} (F : Family n) (a : Affine n) : Nat :=
  match selection F a with
  | none => 3
  | some _ => 1 + SourceLineOutput.successFuel (n + F.length) n (directionSpace F [a]).parameters
def result {n : Nat} (F : Family n) (a : Affine n) : Store 38 :=
  match selection F a with
  | none => SourceLineOutput.rejected (SourceLineWitness.parameterResult F a)
  | some p => finished F a p
theorem finish_exec {n : Nat} (F : Family n) (a : Affine n) :
    Exec SourceLineOutput.block (SourceLineWitness.result F a) (finishFuel F a) (result F a) := by
  cases h : selection F a with
  | none =>
    simp only [SourceLineWitness.result, finishFuel, result, h]
    exact Exec.empty (SourceLineWitness.parameter_none_flag F a h)
      (SourceLineOutput.reject_exec (SourceLineWitness.parameterResult F a))
  | some p =>
    simp only [SourceLineWitness.result, finishFuel, result, h]
    have flag : (SourceLineWitness.liftedResult F a p).get 4 = [true] :=
      SourceWitnessLift.result_present _ _ _ _ _
    exact Exec.one flag (lift_exec F a p)

def block : Block 38 := .seq SourceLineWitness.block SourceLineOutput.block
def fuel {n : Nat} (F : Family n) (a : Affine n) : Nat := SourceLineWitness.fuel F a + finishFuel F a
theorem block_exec {n : Nat} (F : Family n) (a : Affine n) :
    Exec block (SourceLinePullback.start F a) (fuel F a) (result F a) :=
  Exec.seq (SourceLineWitness.block_exec F a) (finish_exec F a)
theorem result_output {n : Nat} (F : Family n) (a : Affine n) :
    (result F a).get 8 = (SourceLineOutput.codec n F.length).encode (SourceLine.sourceLineQuery F a) := by
  rw [SourceLine.sourceLineQuery, ← selection_raw]
  cases h : selection F a with
  | none =>
    simp only [result, h, Option.map_none, SourceLineOutput.none_bytes]
    exact SourceLineOutput.rejected_output _
  | some p =>
    simp only [result, h, Option.map_some]
    rw [SourceLineOutput.lift_bytes]
    exact Frame.get_core _ _ (8 : Fin 9)

def costPolynomial : NatPolynomial := .add SourceLineWitness.costPolynomial SourceLineOutput.costPolynomial
theorem finish_original_bound {n : Nat} (F : Family n) (a : Affine n) :
    finishFuel F a ≤ SourceLineOutput.costPolynomial.eval
      (SourceDirectionEncoding.codec.encode ⟨n, [a], F⟩).length := by
  cases h : selection F a with
  | none =>
    simp only [finishFuel, h, SourceLineOutput.costPolynomial_eval, SourceLineOutput.successFuel]
    omega
  | some p =>
    have dimension := SourceDirectionEncoding.dimension_bound n F [a]
    have rows := SourceDirectionEncoding.family_bound n F [a]
    have joint : n + F.length ≤ 2 * (SourceDirectionEncoding.codec.encode ⟨n, [a], F⟩).length := by omega
    have bound := SourceLineOutput.bounded_cost (n + F.length) n (directionSpace F [a]).parameters
      (SourceDirectionEncoding.codec.encode ⟨n, [a], F⟩).length joint dimension
      (SourceLineQueryMatrices.parameter_bound F a)
    simp only [finishFuel, h]
    omega
theorem original_input_bound {n : Nat} (F : Family n) (a : Affine n) :
    fuel F a ≤ costPolynomial.eval (SourceDirectionEncoding.codec.encode ⟨n, [a], F⟩).length :=
  Nat.add_le_add (SourceLineWitness.original_input_bound F a) (finish_original_bound F a)
theorem output_original_bound {n : Nat} (F : Family n) (a : Affine n) :
    ((result F a).get 8).length ≤ 3 * (SourceDirectionEncoding.codec.encode ⟨n, [a], F⟩).length + 1 := by
  rw [result_output]
  have size := SourceLineOutput.bytes_bound (SourceLine.sourceLineQuery F a)
  have dimension := SourceDirectionEncoding.dimension_bound n F [a]
  have rows := SourceDirectionEncoding.family_bound n F [a]
  omega

def program : Program 38 := block.program 0 8
theorem program_run {n : Nat} (F : Family n) (a : Affine n) :
    BitRegister.run program (fuel F a + 1) ⟨.running 0, SourceLinePullback.start F a⟩ = ⟨.accepted, result F a⟩ :=
  (block_exec F a).program_run 0 8
theorem exact_decoded_output {n : Nat} (F : Family n) (a : Affine n) :
    ∃ steps ≤ costPolynomial.eval (SourceDirectionEncoding.codec.encode ⟨n, [a], F⟩).length + 1,
      BitRegister.run program steps ⟨.running 0, SourceLinePullback.start F a⟩ = ⟨.accepted, result F a⟩ ∧
      (SourceLineOutput.codec n F.length).decode ((result F a).get 8) = some (SourceLine.sourceLineQuery F a) := by
  refine ⟨fuel F a + 1, Nat.add_le_add_right (original_input_bound F a) 1, program_run F a, ?_⟩
  rw [result_output]
  exact SourceLineOutput.roundtrip _
theorem decoded_sound {n : Nat} (F : Family n) (a : Affine n) (w : SourceLine.LineWitness n F.length)
    (h : (SourceLineOutput.codec n F.length).decode ((result F a).get 8) = some (some w)) :
    SourceLine.LineGood F a w := by
  rw [result_output, SourceLineOutput.roundtrip] at h
  exact SourceLine.sourceLineQuery_sound F a w (Option.some.inj h)
theorem decoded_none_iff {n : Nat} (F : Family n) (a : Affine n) :
    (SourceLineOutput.codec n F.length).decode ((result F a).get 8) = some none ↔
      ¬ ∃ w, SourceLine.LineGood F a w := by
  rw [result_output, SourceLineOutput.roundtrip, Option.some.injEq]
  exact SourceLine.sourceLineQuery_none_iff F a

end PNP.Concrete.ResidualReduction.SourceLinePreparedQuery
