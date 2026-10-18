import PNP.Concrete.ResidualReduction.SourceLineWitnessLifting

/-! Original-encoded-input instruction and returned-vector bounds for the
complete source-derived lineRawQuery computation. These are source-instruction
bounds, not a claim of raw-machine or whole-contraction polynomial runtime. -/

namespace PNP.Concrete.ResidualReduction.SourceLineWitness
open PNP.Concrete PNP.Concrete.BitRegister
open PNP.Concrete.NormalizerBlocks
open PNP.Concrete.ResidualReduction.FactoredContraction
open PNP.Concrete.ResidualReduction.BinaryLinear
open PNP.Concrete.ResidualReduction.SourceDirections
open PNP.Concrete.ResidualReduction.SourceDirectionEncoding (codec)

def liftCostPolynomial : NatPolynomial :=
  .add (.constant 17) (.add
    (NatPolynomial.substitute SourceLinearMap.costPolynomial (.mul (.constant 2) .variable))
    SourceLinearMap.costPolynomial)
theorem liftCostPolynomial_eval (L : Nat) :
    liftCostPolynomial.eval L = 17 + (SourceLinearMap.fuel (2 * L) (2 * L) + SourceLinearMap.fuel L L) := by
  simp only [liftCostPolynomial, NatPolynomial.eval_add, NatPolynomial.eval_constant,
    NatPolynomial.eval_substitute, NatPolynomial.eval_mul, NatPolynomial.eval_variable,
    SourceLinearMap.costPolynomial_eval]

theorem lift_original_bound {n : Nat} (F : Family n) (alpha : Affine n) :
    1 + liftFuel F alpha ≤ liftCostPolynomial.eval (codec.encode ⟨n, [alpha], F⟩).length := by
  let L := (codec.encode ⟨n, [alpha], F⟩).length
  have dimension := SourceDirectionEncoding.dimension_bound n F [alpha]
  have family := SourceDirectionEncoding.family_bound n F [alpha]
  have leftAmbient : n + F.length ≤ 2 * L := by dsimp only [L]; omega
  have left := SourceLinearMap.fuel_mono (n + F.length)
    (SourceLinePullback.leftSpace F alpha).parameters (2 * L) (2 * L)
    leftAmbient (SourceLinePullback.left_parameter_bound F alpha)
  have right := SourceLinearMap.fuel_mono (directionSpace F [alpha]).parameters
    (SourceLinePullback.rightSpace F alpha).parameters L L
    (SourceLineQueryMatrices.parameter_bound F alpha) (SourceLinePullback.right_parameter_bound F alpha)
  rw [liftCostPolynomial_eval]
  unfold liftFuel SourceWitnessLift.fuel
  change 1 + (10 + (SourceLinearMap.fuel _ _ + (5 + (SourceLinearMap.fuel _ _ + 1)))) ≤
    17 + (SourceLinearMap.fuel (2 * L) (2 * L) + SourceLinearMap.fuel L L)
  omega

theorem finish_original_bound {n : Nat} (F : Family n) (alpha : Affine n) :
    finishFuel F alpha ≤ liftCostPolynomial.eval (codec.encode ⟨n, [alpha], F⟩).length := by
  cases h : selection F alpha with
  | none =>
    simp only [finishFuel, h, liftCostPolynomial_eval]
    omega
  | some p =>
    rw [finishFuel, h]
    exact lift_original_bound F alpha

def costPolynomial : NatPolynomial := .add parameterCostPolynomial liftCostPolynomial
theorem original_input_bound {n : Nat} (F : Family n) (alpha : Affine n) :
    fuel F alpha ≤ costPolynomial.eval (codec.encode ⟨n, [alpha], F⟩).length :=
  Nat.add_le_add (parameter_original_bound F alpha) (finish_original_bound F alpha)

theorem output_lengths {n : Nat} (F : Family n) (alpha : Affine n) (x y : BitString)
    (h : observed (result F alpha) = some (x, y)) :
    x.length = n + F.length ∧ y.length = (directionSpace F [alpha]).parameters := by
  rw [result_exact, queryBytes] at h
  cases query : SourceLine.lineRawQuery F alpha with
  | none => simp only [query, Option.map_none] at h; cases h
  | some w =>
    simp only [query, Option.map_some] at h
    have equal := Option.some.inj h
    have left := congrArg (fun p : BitString × BitString => p.1.length) equal
    have right := congrArg (fun p : BitString × BitString => p.2.length) equal
    simp only [SourceEncoding.point_length] at left right
    exact ⟨left.symm, right.symm⟩
theorem output_original_bounds {n : Nat} (F : Family n) (alpha : Affine n) (x y : BitString)
    (h : observed (result F alpha) = some (x, y)) :
    x.length ≤ 2 * (codec.encode ⟨n, [alpha], F⟩).length ∧
      y.length ≤ (codec.encode ⟨n, [alpha], F⟩).length := by
  obtain ⟨left, right⟩ := output_lengths F alpha x y h
  have dimension := SourceDirectionEncoding.dimension_bound n F [alpha]
  have family := SourceDirectionEncoding.family_bound n F [alpha]
  have parameters := SourceLineQueryMatrices.parameter_bound F alpha
  constructor <;> omega

theorem program_original_bound {n : Nat} (F : Family n) (alpha : Affine n) :
    ∃ steps ≤ costPolynomial.eval (codec.encode ⟨n, [alpha], F⟩).length + 1,
      BitRegister.run program steps ⟨.running 0, SourceLinePullback.start F alpha⟩ =
        ⟨.accepted, result F alpha⟩ :=
  ⟨fuel F alpha + 1, Nat.add_le_add_right (original_input_bound F alpha) 1, program_run F alpha⟩

end PNP.Concrete.ResidualReduction.SourceLineWitness
