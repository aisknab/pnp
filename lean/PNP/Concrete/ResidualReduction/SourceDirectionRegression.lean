import Lean
import PNP.Concrete.ResidualReduction.SourceDirectionBudget
import PNP.Concrete.ResidualReduction.SourcePolarFamilyRegression

namespace PNP.Concrete.ResidualReduction.SourceDirectionInstructions.Regression
open PNP.Concrete PNP.Concrete.BitRegister
open PNP.Concrete.NormalizerBlocks
open PNP.Concrete.NativeNormalization.NativeBitCodec
open PNP.Concrete.ResidualReduction.FactoredContraction
open PNP.Concrete.ResidualReduction.BinaryLinear
open PNP.Concrete.ResidualReduction.SourceDirections
open PNP.Concrete.ResidualReduction.MatrixInstructions
open PNP.Concrete.ResidualReduction.MatrixSolutionEncoding

private def sample : Row 2 := ⟨true, (true, (false, true)), (false, (true, false))⟩
private def constrained : System 2 := [(true, (false, true))]
private def inconsistent : System 2 := [(false, (false, true))]

-- The source contains only original normals and rows. Explicit dimensions
-- survive empty inputs; truncated and trailing encodings do not decode.
example : SourceDirectionEncoding.codec.encode ⟨0, [], []⟩ = [false, false, false] := rfl
example : SourceDirectionEncoding.codec.encode ⟨1, [], []⟩ = [true, false, false, false] := rfl
example : SourceDirectionEncoding.codec.decode [false, false, false] = some ⟨0, [], []⟩ := rfl
example : SourceDirectionEncoding.codec.decode [] = none := rfl
example : SourceDirectionEncoding.codec.decode [false, false] = none := rfl
example : SourceDirectionEncoding.codec.decode [false, false, false, false] = none := rfl
example {n : Nat} (F : Family n) (U : System n) :
    SourceDirectionEncoding.codec.decode (SourceDirectionEncoding.codec.encode ⟨n, U, F⟩) =
      some ⟨n, U, F⟩ := SourceDirectionEncoding.roundtrip n F U

-- The first basis and all generated constraints come from actual kernels.
-- Original normal constants are homogenised, not mistaken for consistency
-- requirements. The emitted solution is canonical and keeps coordinate order.
example : matrixBits (directionSystem [sample] ([] : System 2)) =
    [false, true, false, true, false, false] := rfl
example : matrixBits (directionSystem [sample] constrained) =
    [true, false, true, true, false, false] := rfl
example : (solutionCodec 2).encode (some (directionSpace [sample] [])) =
    [true, false, false, false] := rfl
example : (solutionCodec 2).encode (some (directionSpace [sample] constrained)) =
    [true, true, false, false, false, true, false] := rfl
example : (solutionCodec 2).encode (some (directionSpace ([] : Family 2) [])) =
    [true, true, true, false, true, false, false, false, true, false] := rfl
example : (solutionCodec 2).encode (some (directionSpace [sample] inconsistent)) =
    [true, false, false, false] := rfl
example : (solutionCodec 0).encode (some (directionSpace (n := 0) [⟨true, true, false⟩] [true])) =
    [true, false] := rfl

example : (BitRegister.run program (fuel [sample] constrained + 1)
    ⟨.running 0, (start [sample] constrained).store⟩).store.get 8 =
      [true, true, false, false, false, true, false] := by
  exact congrArg (fun c => c.store.get (8 : Fin 20)) (program_run [sample] constrained)
example : (BitRegister.run program (fuel [sample] inconsistent + 1)
    ⟨.running 0, (start [sample] inconsistent).store⟩).store.get 8 =
      [true, false, false, false] := by
  exact congrArg (fun c => c.store.get (8 : Fin 20)) (program_run [sample] inconsistent)
example : (BitRegister.run program (fuel (n := 0) [] [] + 1)
    ⟨.running 0, (start (n := 0) [] []).store⟩).store.get 8 = [true, false] := by
  exact congrArg (fun c => c.store.get (8 : Fin 20)) (program_run (n := 0) [] [])

-- Arbitrary-dimensional contracts, without a supplied map, coefficient table
-- or execution oracle. This remains the prepared phase, not raw input parsing.
example {n : Nat} (F : Family n) (U : System n) :
    Exec block (start F U).store (fuel F U) (result F U).store := block_exec F U
example {n : Nat} (F : Family n) (U : System n) :
    (solutionCodec n).decode ((result F U).store.get 8) = some (some (directionSpace F U)) := by
  rw [result_output]
  exact decode_encode (solutionCodec n) _
example {n : Nat} (F : Family n) (U : System n) (v : Point n) :
    DirectionSpec F U v ↔ ∃ z, (directionSpace F U).direction z = v := directionSpace_iff F U v
example {n : Nat} (F : Family n) (U : System n) :
    fuel F U ≤ SourceDirectionBudget.costPolynomial.eval
      (SourceDirectionEncoding.codec.encode ⟨n, U, F⟩).length := SourceDirectionBudget.original_input_bound F U
example {n : Nat} (F : Family n) (U : System n) :
    ((result F U).store.get 8).length ≤
      ((SourceDirectionEncoding.codec.encode ⟨n, U, F⟩).length + 1) *
        ((SourceDirectionEncoding.codec.encode ⟨n, U, F⟩).length + 1) + 1 := SourceDirectionBudget.output_bound F U

run_cmd do
  for name in [``SourceDirectionEncoding.codec_bits, ``SourceDirectionEncoding.codec_length,
    ``SourceDirectionEncoding.dimension_bound, ``SourceDirectionEncoding.normals_bound,
    ``SourceDirectionEncoding.family_bound, ``SourceDirectionEncoding.normals_payload_bound,
    ``SourceDirectionEncoding.family_payload_bound, ``SourceDirectionEncoding.normals_packet_bound,
    ``SourceDirectionEncoding.roundtrip, ``SourceDirectionEncoding.canonical,
    ``SourceDirectionEncoding.matrixBits_append, ``SourceDirectionEncoding.direction_count_bound,
    ``SourceDirectionEncoding.direction_packet_bound,
    ``store_core, ``solver_exec, ``family_exec, ``small_exec, ``firstKernel_exec,
    ``prepareFamily_exec, ``polar_exec, ``prepareSecond_exec, ``secondKernel_exec,
    ``block_exec, ``result_output, ``program_run,
    ``SourceDirectionBudget.kernel_bound, ``SourceDirectionBudget.family_bound,
    ``SourceDirectionBudget.fuel_bound, ``SourceDirectionBudget.rowPolynomial_eval,
    ``SourceDirectionBudget.matrixPolynomial_eval, ``SourceDirectionBudget.familyPolynomial_eval,
    ``SourceDirectionBudget.costPolynomial_eval, ``SourceDirectionBudget.original_input_bound,
    ``SourceDirectionBudget.output_bound] do
    let axioms ← Lean.collectAxioms name
    for axiomName in axioms do
      if axiomName != ``propext && axiomName != ``Quot.sound then
        throwError "Unexpected axiom in {name}: {axiomName}"

#print axioms PNP.Concrete.ResidualReduction.SourceDirectionInstructions.block_exec
#print axioms PNP.Concrete.ResidualReduction.SourceDirectionInstructions.program_run
#print axioms PNP.Concrete.ResidualReduction.SourceDirectionBudget.original_input_bound
#print axioms PNP.Concrete.ResidualReduction.SourceDirectionBudget.output_bound

end PNP.Concrete.ResidualReduction.SourceDirectionInstructions.Regression
