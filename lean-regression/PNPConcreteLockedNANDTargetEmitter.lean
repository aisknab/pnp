import PNP.Concrete.LockedNANDTargetEmitter

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000

namespace PNP.Concrete.LockedNANDTargetEmitterRegression

open PNP.Concrete
open LockedNAND

namespace Controller

open TargetEmitterController
open TargetEmitterControllerCompiled
open TargetEmitterControllerPolynomialBound
open TargetEmitterControllerTotalTrace

private def runsTotallyExactly (bits : BitString) : Prop :=
  ∃ steps final,
    steps ≤ allInputWorkBound bits.length ∧
    workRunExact? TargetEmitterController.machine steps
        (workStartConfiguration TargetEmitterController.machine
          (rawInputWorkTape bits)) =
      some final ∧
    TargetEmitterController.machine.isHalted final = true ∧
    (final.state = TargetEmitterController.machine.acceptState ↔
      ∃ raw, decodeCircuit bits = some raw) ∧
    (encodeWorkTape final.tape).outputBits =
      RawBuilder.targetBytes bits

private def rejectsExactly (bits : BitString) : Prop :=
  ∃ steps final,
    steps ≤ allInputWorkBound bits.length ∧
    workRunExact? TargetEmitterController.machine steps
        (workStartConfiguration TargetEmitterController.machine
          (rawInputWorkTape bits)) =
      some final ∧
    TargetEmitterController.machine.isHalted final = true ∧
    final.state = TargetEmitterController.machine.rejectState ∧
    (encodeWorkTape final.tape).outputBits = []

private def acceptsExactly (raw : RawCircuit) : Prop :=
  ∃ steps final,
    steps ≤ allInputWorkBound (encodeCircuit raw).length ∧
    workRunExact? TargetEmitterController.machine steps
        (workStartConfiguration TargetEmitterController.machine
          (rawInputWorkTape (encodeCircuit raw))) =
      some final ∧
    TargetEmitterController.machine.isHalted final = true ∧
    final.state = TargetEmitterController.machine.acceptState ∧
    (encodeWorkTape final.tape).outputBits =
      RawBuilder.targetBytes (encodeCircuit raw)

private def constantFalseCircuit : RawCircuit :=
  { inputCount := 0
    gates := []
    output := .constant false }

private def constantTrueCircuit : RawCircuit :=
  { inputCount := 0
    gates := []
    output := .constant true }

private def oneGateCircuit : RawCircuit :=
  { inputCount := 0
    gates :=
      [{ left := .constant false
         right := .constant true }]
    output := .gate 0 }

private abbrev inputOutOfRangeCircuit : RawCircuit :=
  TargetEmitterGrammarScanner.decodedInvalidReferenceCircuit

/-! The unconditional theorem covers empty, one-bit, odd, even, all-zero,
all-one, grammar-success, and grammar-failure inputs with the same bound. -/

example : runsTotallyExactly [] :=
  allInput_bounded_exact []

example : runsTotallyExactly [false] :=
  allInput_bounded_exact [false]

example : runsTotallyExactly [true] :=
  allInput_bounded_exact [true]

example : runsTotallyExactly [false, false, false] :=
  allInput_bounded_exact [false, false, false]

example : runsTotallyExactly [true, true, true, true, true] :=
  allInput_bounded_exact [true, true, true, true, true]

example : rejectsExactly [] :=
  malformed_bounded_exact [] rfl

example : rejectsExactly [false] :=
  malformed_bounded_exact [false] rfl

example : rejectsExactly [true] :=
  malformed_bounded_exact [true] rfl

example : acceptsExactly constantFalseCircuit :=
  decoded_bounded_exact
    (encodeCircuit constantFalseCircuit) constantFalseCircuit
    (decodeCircuit_encodeCircuit constantFalseCircuit)

example : acceptsExactly constantTrueCircuit :=
  decoded_bounded_exact
    (encodeCircuit constantTrueCircuit) constantTrueCircuit
    (decodeCircuit_encodeCircuit constantTrueCircuit)

example : acceptsExactly oneGateCircuit :=
  decoded_bounded_exact
    (encodeCircuit oneGateCircuit) oneGateCircuit
    (decodeCircuit_encodeCircuit oneGateCircuit)

/-! Grammar decoding deliberately accepts an intrinsically invalid reference;
the strict parser composition rejects that source and clears the result. -/

example :
    GrammarDecodableCircuit (encodeCircuit inputOutOfRangeCircuit) :=
  ⟨inputOutOfRangeCircuit,
    decodeCircuit_encodeCircuit inputOutOfRangeCircuit⟩

example :
    boundedDecide TargetEmitterControllerCompiled.compiledMachine
        (compiledRawTimePolynomial.eval
          (encodeCircuit inputOutOfRangeCircuit).length)
        (encodeCircuit inputOutOfRangeCircuit) =
      .accept :=
  (compiledBoundedDecide_accept_iff
    (encodeCircuit inputOutOfRangeCircuit)).2
      ⟨inputOutOfRangeCircuit,
        decodeCircuit_encodeCircuit inputOutOfRangeCircuit⟩

example :
    machineOutput TargetEmitterControllerCompiled.compiledMachine
        (compiledRawTimePolynomial.eval
          (encodeCircuit inputOutOfRangeCircuit).length)
        (encodeCircuit inputOutOfRangeCircuit) =
      RawBuilder.targetBytes (encodeCircuit inputOutOfRangeCircuit) :=
  compiledMachineOutput_eq_targetBytes
    (encodeCircuit inputOutOfRangeCircuit)

example :
    RawBuilder.targetBytes (encodeCircuit inputOutOfRangeCircuit) ≠ [] :=
  TargetEmitterSpec.rawTargetBytes_ne_nil_of_decoded
    (encodeCircuit inputOutOfRangeCircuit) inputOutOfRangeCircuit
    (decodeCircuit_encodeCircuit inputOutOfRangeCircuit)

example :
    strictLockedNANDPolynomialTimeFunction.output
        (encodeCircuit inputOutOfRangeCircuit) =
      [] := by
  rw [strictLockedNANDPolynomialTimeFunction_output]
  exact buildLockedNANDInstance_of_malformed
    (encodeCircuit inputOutOfRangeCircuit) (by
      unfold decodeElaboratedCircuit
      rw [decodeCircuit_encodeCircuit]
      exact
        TargetEmitterGrammarScanner.decodedInvalidReferenceCircuit_unelaboratable)

/-! Literal table, polynomial evaluation, compiled non-timeout, exact
standalone output, strict composition, and refinement witnesses. -/

example :
    TargetEmitterController.machine.rules.length =
      TargetEmitterController.ruleCount :=
  TargetEmitterController.rules_length_literal

example : TargetEmitterController.ruleCount = 1387921 :=
  rfl

example (n : Nat) :
    compiledRawTimePolynomial.eval n =
      6 * allInputWorkBound n :=
  compiledRawTimePolynomial_eval n

example (bits : BitString) :
    boundedDecide TargetEmitterControllerCompiled.compiledMachine
        (compiledRawTimePolynomial.eval bits.length) bits ≠
      .timeout :=
  compiledBoundedDecide_ne_timeout bits

example (bits : BitString) :
    rawTargetBytesPolynomialTimeFunction.output bits =
      RawBuilder.targetBytes bits :=
  rawTargetBytesPolynomialTimeFunction_output bits

example (bits : BitString) :
    strictLockedNANDPolynomialTimeFunction.output bits =
      buildLockedNANDInstance bits :=
  strictLockedNANDPolynomialTimeFunction_output bits

example :
    FunctionProgram.RawRefinement
      rawTargetBytesPolynomialTimeFunction.program :=
  rawTargetBytesRawRefinement

example :
    FunctionProgram.RawRefinement
      strictLockedNANDPolynomialTimeFunction.program :=
  strictLockedNANDRawRefinement

end Controller

end PNP.Concrete.LockedNANDTargetEmitterRegression
