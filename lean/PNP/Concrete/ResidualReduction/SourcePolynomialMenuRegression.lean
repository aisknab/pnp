import PNP.Concrete.ResidualReduction.SourcePolynomialMenu
import PNP.Concrete.ResidualReduction.SourceMenuSortRegression
import Lean

/-! Canonical packet bytes, counted output headers, source-order independence,
duplicates, degenerate rows and every malformed-input boundary. All-bitstring
machine and compiler theorems are checked separately from finite examples.
This constructor does not claim contraction completeness or decide stopped cores. -/

namespace PNP.Concrete.ResidualReduction.SourcePolynomialMenu.Regression
open PNP.Concrete PNP.Concrete.BitRegister PNP.Concrete.NormalizerBlocks
open PNP.Concrete.ResidualReduction.FactoredContraction
open PNP.Concrete.ResidualReduction.MatrixInstructions
open PNP.Concrete.ResidualReduction.SourceChain

private def a : Affine 2 := (true, (false, false))
private def b : Affine 2 := (false, (true, false))
private def c : Affine 2 := (true, (true, false))
private def ac : Affine 2 := (true, (false, true))
private def bc : Affine 2 := (false, (true, true))
private def zc : Affine 2 := (false, (false, true))
private def ab : Row 2 := ⟨true, a, b⟩
private def cb : Row 2 := ⟨false, c, b⟩
private def constants : Row 2 := ⟨false, ac, bc⟩
private def repeated : Row 2 := ⟨true, a, ac⟩
private def zeroLeft : Row 2 := ⟨false, zc, b⟩
private def zeroRight : Row 2 := ⟨true, a, zc⟩
private def abc : BitString := [true, false, false, false, true, false, true, true, false]
private def packet : BitString := [true, true, false, true, true, true, false] ++ abc

example : MatrixInputEncoding.codec.encode ⟨2, [a, b, c]⟩ = packet := rfl
example : SourceMenuSerialization.fuel 2 3 = 65 := rfl
example : SourceMenuSerialization.fuel 0 0 = 11 := rfl

private def Serialized {n : Nat} (menu : List (Affine n)) (word : BitString) : Prop :=
  Exec SourceMenuSerialization.block (SourceMenuSerialization.ready menu).store
    (SourceMenuSerialization.fuel n menu.length) (SourceMenuSerialization.result menu).store ∧
    (SourceMenuSerialization.result menu).store.get 8 = word
private theorem serialized {n : Nat} (menu : List (Affine n)) (word : BitString)
    (expected : MatrixInputEncoding.codec.encode ⟨n, menu⟩ = word) : Serialized menu word :=
  ⟨SourceMenuSerialization.block_exec menu, expected⟩

example : Serialized (n := 0) [] [false, false] := serialized _ _ rfl
example : Serialized (n := 2) [] [true, true, false, false] := serialized _ _ rfl
example : Serialized [a, b, c] packet := serialized _ _ rfl
example : Serialized [b, b] [true, true, false, true, true, false, false, true, false, false, true, false] :=
  serialized _ _ rfl
example : Serialized (n := 0) [false, true] [false, true, true, false, false, true] := serialized _ _ rfl

private def Produces (input word : BitString) : Prop :=
  ∃ after : Store 16, CompilerIO.sourceResult program (sourceFuel.eval input.length) input =
    ⟨.accepted, after⟩ ∧ after.get 8 = word
private theorem produces (input word : BitString) (expected : SourceMenuInput.answer input = word) :
    Produces input word := by
  obtain ⟨after, checked, output⟩ := source_result input
  exact ⟨after, checked, output.trans expected⟩
private def FamilyProduces {n : Nat} (F : Family n) (word : BitString) : Prop :=
  Produces (SourceMatrixEncoding.codec.encode ⟨n, F⟩) word
private theorem family_produces {n : Nat} (F : Family n) (word : BitString)
    (expected : MatrixInputEncoding.codec.encode ⟨n, sourceMenu F⟩ = word) : FamilyProduces F word := by
  apply produces
  rw [SourceMenuInput.answer_canonical]
  exact expected

example : FamilyProduces ([] : Family 0) [false, false] := family_produces _ _ rfl
example : FamilyProduces ([] : Family 2) [true, true, false, false] := family_produces _ _ rfl
example : FamilyProduces (n := 0) [⟨true, false, true⟩, ⟨false, true, true⟩] [false, false] :=
  family_produces _ _ rfl
example : FamilyProduces (n := 1) [⟨true, (true, true), (true, false)⟩] [true, false, false] :=
  family_produces _ _ rfl
example : FamilyProduces [ab] packet := family_produces _ _ rfl
example : FamilyProduces [cb] packet := family_produces _ _ rfl
example : FamilyProduces [constants] packet := family_produces _ _ rfl
example : FamilyProduces [ab, ab] packet := family_produces _ _ rfl
example : FamilyProduces [ab, cb, constants] packet := family_produces _ _ rfl
example : FamilyProduces [cb, ab, repeated] packet := family_produces _ _ rfl
example : FamilyProduces [zeroLeft, zeroRight, repeated] [true, true, false, false] := family_produces _ _ rfl
example : FamilyProduces [zeroLeft, constants, repeated, zeroRight] packet := family_produces _ _ rfl

-- Missing delimiters, truncated payloads, and trailing data reject.
example : Produces [] [false] := produces _ _ rfl
example : Produces [true] [false] := produces _ _ rfl
example : Produces [true, true, true] [false] := produces _ _ rfl
example : Produces [false] [false] := produces _ _ rfl
example : Produces [false, true] [false] := produces _ _ rfl
example : Produces [false, true, true] [false] := produces _ _ rfl
example : Produces [false, true, false] [false] := produces _ _ rfl
example : Produces [false, true, false, false] [false] := produces _ _ rfl
example : Produces [false, true, false, false, false] [false] := produces _ _ rfl
example : Produces [false, true, false, false, false, false] [false, false] := produces _ _ rfl
example : Produces [false, true, false, false, false, false, true] [false] := produces _ _ rfl
example : Produces [false, false, false] [false] := produces _ _ rfl
example : Produces [false, false, true] [false] := produces _ _ rfl
example : Produces [true, true, false, true, false] [false] := produces _ _ rfl

-- These are the concrete compiler's output statements, not native evaluation.
example : polynomial.output (SourceMatrixEncoding.codec.encode ⟨2, [ab, cb, constants]⟩) = packet := by
  rw [polynomial_canonical]
  rfl
example : polynomial.output [] = [false] := polynomial_malformed [] rfl
example : polynomial.output [false, false, true] = [false] := polynomial_malformed _ rfl
example : MatrixInputEncoding.codec.decode
    (polynomial.output (SourceMatrixEncoding.codec.encode ⟨2, [ab, cb, constants]⟩)) = some ⟨2, [a, b, c]⟩ := by
  rw [exact_decoded_menu]
  rfl

example (input : BitString) :
    ∃ after : Store 16, CompilerIO.sourceResult program (sourceFuel.eval input.length) input =
      ⟨.accepted, after⟩ ∧ after.get 8 = SourceMenuInput.answer input := source_result input
example : CompilerIO.AcceptsWithin program sourceFuel := acceptsWithin
example (input : BitString) : polynomial.output input = SourceMenuInput.answer input := polynomial_output input
example (input : BitString) :
    boundedDecide (CompilerIO.rawMachine program)
      ((CompilerIO.runtimePolynomial 16 sourceFuel).eval input.length) input = .accept :=
  polynomial_machine_accepts input
example (input : BitString) : (polynomial.output input).length ≤ 7 * input.length + 2 :=
  polynomial_output_bound input
example (n : Nat) (F : Family n) :
    MatrixInputEncoding.codec.decode (polynomial.output (SourceMatrixEncoding.codec.encode ⟨n, F⟩)) =
      some ⟨n, sourceMenu F⟩ := exact_decoded_menu n F

run_cmd do
  for name in [
    ``SourceMenuSerialization.countBody_exec,
    ``SourceMenuSerialization.countLoop_exec,
    ``SourceMenuSerialization.countStart_exec,
    ``SourceMenuSerialization.countHeader_exec,
    ``SourceMenuSerialization.emitCount_exec,
    ``SourceMenuSerialization.dimensionHeader_exec,
    ``SourceMenuSerialization.emitDimension_exec,
    ``SourceMenuSerialization.finish_exec,
    ``SourceMenuSerialization.block_exec,
    ``SourceMenuSerialization.result_output,
    ``SourceMenuSerialization.costPolynomial_eval,
    ``SourceMenuSerialization.bounded_cost,
    ``SourceMenuSerialization.original_input_bound,
    ``SourceMenuRaw.headerLoop_exec,
    ``SourceMenuRaw.family_bytes,
    ``SourceMenuRaw.entered_store,
    ``SourceMenuRaw.enter_exec,
    ``SourceMenuRaw.serialize_exec,
    ``SourceMenuRaw.finished_output,
    ``SourceMenuRaw.construct_exec,
    ``SourceMenuInput.answer_canonical,
    ``SourceMenuInput.answer_malformed,
    ``SourceMenuInput.decoded_answer,
    ``SourceMenuInput.answer_length,
    ``SourceMenuRaw.complete_check,
    ``SourceMenuRaw.short_check,
    ``SourceMenuRaw.extra_check,
    ``SourceMenuRaw.valid_exec,
    ``SourceMenuRaw.failed_header,
    ``SourceMenuRaw.failed_payload,
    ``SourceMenuRaw.block_exec,
    ``SourcePolynomialMenu.sourceFuel_eval,
    ``SourcePolynomialMenu.source_result,
    ``SourcePolynomialMenu.acceptsWithin,
    ``SourcePolynomialMenu.source_output,
    ``SourcePolynomialMenu.polynomial_program,
    ``SourcePolynomialMenu.polynomial_output,
    ``SourcePolynomialMenu.polynomial_canonical,
    ``SourcePolynomialMenu.polynomial_malformed,
    ``SourcePolynomialMenu.exact_decoded_menu,
    ``SourcePolynomialMenu.polynomial_machine_accepts,
    ``SourcePolynomialMenu.polynomial_output_bound] do
    let axioms ← Lean.collectAxioms name
    for axiomName in axioms do
      if axiomName != ``propext && axiomName != ``Quot.sound then
        throwError "Unexpected axiom in {name}: {axiomName}"

#print axioms PNP.Concrete.ResidualReduction.SourceMenuSerialization.block_exec
#print axioms PNP.Concrete.ResidualReduction.SourceMenuRaw.construct_exec
#print axioms PNP.Concrete.ResidualReduction.SourceMenuRaw.block_exec
#print axioms PNP.Concrete.ResidualReduction.SourcePolynomialMenu.acceptsWithin
#print axioms PNP.Concrete.ResidualReduction.SourcePolynomialMenu.polynomial_output
#print axioms PNP.Concrete.ResidualReduction.SourcePolynomialMenu.polynomial_machine_accepts
#print axioms PNP.Concrete.ResidualReduction.SourcePolynomialMenu.polynomial_output_bound

end PNP.Concrete.ResidualReduction.SourcePolynomialMenu.Regression
