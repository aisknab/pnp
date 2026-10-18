import Lean
import PNP.Concrete.ResidualReduction.SourcePolynomialDirection
import PNP.Concrete.ResidualReduction.SourceDirectionRegression

namespace PNP.Concrete.ResidualReduction.SourcePolynomialDirection.Regression
open PNP.Concrete PNP.Concrete.BitRegister
open PNP.Concrete.ResidualReduction.FactoredContraction
open PNP.Concrete.ResidualReduction.BinaryLinear
open PNP.Concrete.ResidualReduction.SourceDirections
open PNP.Concrete.ResidualReduction.SourceDirectionEncoding
open PNP.Concrete.ResidualReduction.MatrixSolutionEncoding

private def sample : Row 2 := ⟨true, (true, (false, true)), (false, (true, false))⟩
private def constrained : System 2 := [(true, (false, true))]

-- Each failure boundary is exercised independently: missing first or second
-- header, incomplete normals, missing family header, short and trailing family.
example : codec.decode [] = none := rfl
example : codec.decode [false] = none := rfl
example : codec.decode [true, false, true, false] = none := rfl
example : codec.decode [false, false] = none := rfl
example : codec.decode [false, false, true, false] = none := rfl
example : codec.decode [false, false, true, false, true, true] = none := rfl
example : codec.decode [false, false, false, false] = none := rfl
example : codec.decode [false, false, false, true] = none := rfl
example : polynomial.output [] = [false] := polynomial_malformed [] rfl
example : polynomial.output [true, false, true, false] = [false] := polynomial_malformed _ rfl
example : polynomial.output [false, false] = [false] := polynomial_malformed _ rfl
example : polynomial.output [false, false, true, false, true, true] = [false] := polynomial_malformed _ rfl
example : polynomial.output [false, false, false, true] = [false] := polynomial_malformed _ rfl

-- Direct literal execution does not use the general output theorem. The
-- first case rejects before payload work; the second reaches the third header.
set_option maxRecDepth 16384 in
example : (BitRegister.run program 20 (BitRegister.initial program [])).control = .accepted := rfl
set_option maxRecDepth 16384 in
example : (BitRegister.run program 20 (BitRegister.initial program [])).store.get 8 = [false] := rfl
set_option maxRecDepth 16384 in
example : (BitRegister.run program 45 (BitRegister.initial program [false, false])).control = .accepted := rfl
set_option maxRecDepth 16384 in
example : (BitRegister.run program 45 (BitRegister.initial program [false, false])).store.get 8 = [false] := rfl

-- Nonzero normal constants, empty data and source coefficient order all
-- retain their exact meaning. A positive-dimensional answer is allowed.
example : polynomial.output (codec.encode ⟨2, [], [sample]⟩) = [true, false, false, false] := by
  rw [polynomial_canonical]
  rfl
example : polynomial.output (codec.encode ⟨2, constrained, [sample]⟩) =
    [true, true, false, false, false, true, false] := by
  rw [polynomial_canonical]
  rfl
example : polynomial.output (codec.encode ⟨2, [], []⟩) =
    [true, true, true, false, true, false, false, false, true, false] := by
  rw [polynomial_canonical]
  rfl
example : polynomial.output (codec.encode ⟨0, [true], [⟨true, true, false⟩]⟩) = [true, false] := by
  rw [polynomial_canonical]
  rfl
example : (directionSpace (n := 1) [⟨true, (true, false), (true, false)⟩] []).parameters = 1 := rfl
example : polynomial.output (codec.encode ⟨1, [], [⟨true, (true, false), (true, false)⟩]⟩) =
    [true, true, false, true, false] := by
  rw [polynomial_canonical]
  rfl

example (input : BitString) :
    SourceDirectionInput.Valid input ↔ ∃ problem, codec.decode input = some problem :=
  SourceDirectionInput.valid_iff_decodable input
example (input : BitString) :
    (CompilerIO.sourceResult program (sourceFuel.eval input.length) input).store.get 8 =
      SourceDirectionInput.directionEncoded input := source_output input
example {n : Nat} (F : Family n) (U : System n) :
    (solutionCodec n).decode (polynomial.output (codec.encode ⟨n, U, F⟩)) =
      some (some (directionSpace F U)) := exact_decoded_direction n F U
example (input : BitString) :
    boundedDecide (CompilerIO.rawMachine program)
      ((CompilerIO.runtimePolynomial 20 sourceFuel).eval input.length) input = .accept :=
  polynomial_machine_accepts input
example (input : BitString) :
    (polynomial.output input).length ≤ (input.length + 1) * (input.length + 1) + 1 := polynomial_output_bound input
example {n : Nat} (F : Family n) (U : System n) (s : Space n)
    (returned : (solutionCodec n).decode (polynomial.output (codec.encode ⟨n, U, F⟩)) = some (some s))
    (z : Point s.parameters) : DirectionSpec F U (s.direction z) := polynomial_sound F U s returned z
example {n : Nat} (F : Family n) (U : System n) (v : Point n) (valid : DirectionSpec F U v) :
    ∃ s : Space n, (solutionCodec n).decode (polynomial.output (codec.encode ⟨n, U, F⟩)) = some (some s) ∧
      ∃ z, s.direction z = v := polynomial_complete F U v valid

run_cmd do
  for name in [``SourceDirectionInput.canonical_first, ``SourceDirectionInput.canonical_normalBytes,
    ``SourceDirectionInput.canonical_familyTail, ``SourceDirectionInput.canonical_header,
    ``SourceDirectionInput.valid_canonical, ``SourceDirectionInput.family_split,
    ``SourceDirectionInput.valid_input, ``SourceDirectionInput.valid_iff_decodable,
    ``SourceDirectionInput.decode_none_not_valid, ``SourceDirectionInput.decode_none_header,
    ``SourceDirectionInput.decode_none_normals, ``SourceDirectionInput.decode_none_family_header,
    ``SourceDirectionInput.decode_none_family_length, ``SourceDirectionInput.size_bounds,
    ``SourceDirectionInput.directionEncoded_canonical, ``SourceDirectionInput.directionEncoded_malformed,
    ``SourceDirectionLoader.loader_exec, ``SourceDirectionLoader.headers_exec,
    ``SourceDirectionLoader.normal_seed_exec, ``SourceDirectionLoader.normal_payload_exec,
    ``SourceDirectionLoader.preserve_exec, ``SourceDirectionLoader.family_header_exec,
    ``SourceDirectionLoader.readHeader_valid, ``SourceDirectionLoader.family_seed_exec,
    ``SourceDirectionLoader.family_payload_exec, ``SourceDirectionLoader.familyDone_canonical,
    ``SourceDirectionLoader.family_prepare_exec, ``SourceDirectionLoader.handoff_exec,
    ``SourceDirectionLoader.normal_prepare_exec, ``SourceDirectionLoader.finish_exec,
    ``SourceDirectionRaw.failure_exec, ``SourceDirectionRaw.failed_output,
    ``SourceDirectionRaw.complete_check, ``SourceDirectionRaw.completion_bound,
    ``SourceDirectionRaw.short_check, ``SourceDirectionRaw.extra_check,
    ``SourceDirectionRaw.family_check_exec, ``SourceDirectionRaw.family_selection_exec,
    ``SourceDirectionRaw.normal_selection_exec, ``SourceDirectionRaw.selection_exec,
    ``SourceDirectionRaw.block_exec,
    ``normalPayload_eval, ``familyPayload_eval, ``sourceFuel_eval, ``source_result,
    ``acceptsWithin, ``source_output, ``polynomial_program, ``polynomial_output,
    ``polynomial_canonical, ``polynomial_malformed, ``exact_decoded_direction,
    ``polynomial_machine_accepts, ``polynomial_output_bound, ``polynomial_sound, ``polynomial_complete] do
    let axioms ← Lean.collectAxioms name
    for axiomName in axioms do
      if axiomName != ``propext && axiomName != ``Quot.sound then
        throwError "Unexpected axiom in {name}: {axiomName}"

#print axioms PNP.Concrete.ResidualReduction.SourceDirectionInput.valid_iff_decodable
#print axioms PNP.Concrete.ResidualReduction.SourceDirectionLoader.finish_exec
#print axioms PNP.Concrete.ResidualReduction.SourceDirectionRaw.block_exec
#print axioms PNP.Concrete.ResidualReduction.SourcePolynomialDirection.polynomial_output
#print axioms PNP.Concrete.ResidualReduction.SourcePolynomialDirection.polynomial_machine_accepts
#print axioms PNP.Concrete.ResidualReduction.SourcePolynomialDirection.polynomial_sound

end PNP.Concrete.ResidualReduction.SourcePolynomialDirection.Regression
