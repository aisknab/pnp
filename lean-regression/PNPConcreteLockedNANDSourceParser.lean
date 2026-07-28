import PNP.Concrete.LockedNANDSourceParserCompiled

namespace PNP.Concrete.LockedNAND.SourceParserRegression

open SourceParser

/-! Four-bit framing is fail-closed and retains the exact valid-token
prefix. -/

example : TokenDecodeFailure [false] :=
  .trailingOne [] false

example : TokenDecodeFailure [true, false] :=
  .trailingTwo [] true false

example : TokenDecodeFailure [false, true, false] :=
  .trailingThree [] false true false

example : TokenDecodeFailure [true, true, false, true] :=
  .reserved [] false true []

example :
    TokenDecodeFailure
      (encodeTokens [.version0, .unit] ++
        [true, true, true, false] ++ [false]) :=
  .reserved [.version0, .unit] true false [false]

example : decodeTokens [false] = none :=
  (decodeTokens_eq_none_iff_failure [false]).mpr
    (.trailingOne [] false)

example : decodeTokens [true, false] = none :=
  (decodeTokens_eq_none_iff_failure [true, false]).mpr
    (.trailingTwo [] true false)

example : decodeTokens [false, true, false] = none :=
  (decodeTokens_eq_none_iff_failure [false, true, false]).mpr
    (.trailingThree [] false true false)

example : decodeTokens [true, true, false, true] = none :=
  (decodeTokens_eq_none_iff_failure [true, true, false, true]).mpr
    (.reserved [] false true [])

example (bits : BitString) :
    decodeTokens bits = none ↔ TokenDecodeFailure bits :=
  decodeTokens_eq_none_iff_failure bits

/-! Unterminated unary naturals and the source forms that contain them. -/

example : NatTokenFailure [] :=
  .missingEnd 0

example : NatTokenFailure [.unit, .unit, .unit] := by
  simpa using (NatTokenFailure.missingEnd 3)

example : NatTokenFailure [.unit, .programEnd, .natEnd] := by
  simpa using
    (NatTokenFailure.wrongToken 1 .programEnd [.natEnd]
      (by decide) (by decide))

example : decodeNatTokens [.unit, .unit] = none :=
  (decodeNatTokens_eq_none_iff_failure [.unit, .unit]).mpr (by
    simpa using (NatTokenFailure.missingEnd 2))

example : SourceTokenFailure [] :=
  .missing

example : SourceTokenFailure [.programEnd] :=
  .wrongHead .programEnd []
    (by decide) (by decide) (by decide) (by decide)

example : SourceTokenFailure [.input, .unit, .unit] :=
  .inputIndex (by
    simpa using (NatTokenFailure.missingEnd 2))

example : SourceTokenFailure [.gate, .unit] :=
  .gateIndex (by
    simpa using (NatTokenFailure.missingEnd 1))

example : decodeSourceTokens [.input, .unit] = none :=
  (decodeSourceTokens_eq_none_iff_failure [.input, .unit]).mpr
    (.inputIndex (by
      simpa using (NatTokenFailure.missingEnd 1)))

example (tokens : List Token) :
    decodeSourceTokens tokens = none ↔ SourceTokenFailure tokens :=
  decodeSourceTokens_eq_none_iff_failure tokens

/-! Declared gate-list failures distinguish the two source positions and the
gate terminator. -/

example : NGatesTokenFailure 1 [] :=
  .left SourceTokenFailure.missing

example :
    NGatesTokenFailure 1
      (encodeSourceTokens (.constant false)) :=
  .right 0 (.constant false) SourceTokenFailure.missing

example :
    NGatesTokenFailure 1
      (encodeSourceTokens (.constant false) ++
        encodeSourceTokens (.constant true)) :=
  .missingGateEnd 0 (.constant false) (.constant true)

example :
    NGatesTokenFailure 1
      (encodeSourceTokens (.constant false) ++
        encodeSourceTokens (.constant true) ++
        [.programEnd]) :=
  .wrongGateEnd 0 (.constant false) (.constant true)
    .programEnd [] (by decide)

example : decodeNGatesTokens 1 [] = none :=
  (decodeNGatesTokens_eq_none_iff_failure 1 []).mpr
    (.left SourceTokenFailure.missing)

example (count : Nat) (tokens : List Token) :
    decodeNGatesTokens count tokens = none ↔
      NGatesTokenFailure count tokens :=
  decodeNGatesTokens_eq_none_iff_failure count tokens

/-! The complete circuit classifier retains the exact grammar stage. -/

example : CircuitTokenFailure [] :=
  .missingVersion

example : CircuitTokenFailure [.unit] :=
  .wrongVersion .unit [] (by decide)

example : CircuitTokenFailure [.version0, .unit, .unit] :=
  .inputCount (by
    simpa using (NatTokenFailure.missingEnd 2))

example :
    CircuitTokenFailure
      (.version0 :: (encodeNatTokens 2 ++ [.unit])) :=
  .gateCount 2 (by
    simpa using (NatTokenFailure.missingEnd 1))

example :
    CircuitTokenFailure (circuitHeaderTokens 0 1) :=
  .gates 0 1 (.left SourceTokenFailure.missing)

example :
    CircuitTokenFailure (circuitGatesPrefixTokens 0 []) :=
  .missingProgramEnd 0 []

example :
    CircuitTokenFailure
      (circuitGatesPrefixTokens 0 [] ++ [.outputsEnd]) :=
  .wrongProgramEnd 0 [] .outputsEnd [] (by decide)

example :
    CircuitTokenFailure
      (circuitGatesPrefixTokens 0 [] ++ [.programEnd]) :=
  .output 0 [] SourceTokenFailure.missing

example :
    CircuitTokenFailure
      (circuitOutputPrefixTokens 0 [] (.constant false)) :=
  .missingOutputsEnd 0 [] (.constant false)

example :
    CircuitTokenFailure
      (circuitOutputPrefixTokens 0 [] (.constant false) ++
        [.programEnd]) :=
  .wrongOutputsEnd 0 [] (.constant false)
    .programEnd [] (by decide)

example :
    CircuitTokenFailure
      (circuitOutputPrefixTokens 0 [] (.constant false) ++
        [.outputsEnd]) :=
  .missingInstanceEnd 0 [] (.constant false)

example :
    CircuitTokenFailure
      (circuitOutputPrefixTokens 0 [] (.constant false) ++
        [.outputsEnd, .programEnd]) :=
  .wrongInstanceEnd 0 [] (.constant false)
    .programEnd [] (by decide)

example :
    CircuitTokenFailure
      (circuitOutputPrefixTokens 0 [] (.constant false) ++
        [.outputsEnd, .instanceEnd, .unit]) :=
  .trailingToken 0 [] (.constant false) .unit []

example : decodeCircuitTokens [] = none :=
  (decodeCircuitTokens_eq_none_iff_failure []).mpr
    CircuitTokenFailure.missingVersion

example :
    decodeCircuitTokens (circuitGatesPrefixTokens 0 []) = none :=
  (decodeCircuitTokens_eq_none_iff_failure
    (circuitGatesPrefixTokens 0 [])).mpr
      (.missingProgramEnd 0 [])

example (tokens : List Token) :
    decodeCircuitTokens tokens = none ↔ CircuitTokenFailure tokens :=
  decodeCircuitTokens_eq_none_iff_failure tokens

/-! Representative exact operational and compiled regressions. -/

private def rejectsExactly (bits : BitString) : Prop :=
  ∃ steps final,
    steps ≤ validWorkBound bits.length ∧
    workRunExact? machine steps
        (workStartConfiguration machine (rawInputWorkTape bits)) =
      some final ∧
    machine.isHalted final = true ∧
    final.state = State.reject ∧
    (encodeWorkTape final.tape).outputBits = []

private def acceptsCanonicalExactly (raw : RawCircuit) : Prop :=
  ∃ steps,
    steps ≤ validWorkBound (encodeCircuit raw).length ∧
    workRunExact? machine steps
        (workStartConfiguration machine
          (rawInputWorkTape (encodeCircuit raw))) =
      some (validFinalConfiguration raw)

private def runsTotallyExactly (bits : BitString) : Prop :=
  ∃ steps final,
    steps ≤ validWorkBound bits.length ∧
    workRunExact? machine steps
        (workStartConfiguration machine (rawInputWorkTape bits)) =
      some final ∧
    machine.isHalted final = true ∧
    (final.state = State.accept ↔ ValidEncodedCircuit bits) ∧
    (encodeWorkTape final.tape).outputBits = validatedSourceBytes bits

/-! Empty input and every incomplete one-, two-, or three-bit token tail
reach the rejecting halt and clear their output. -/

example : rejectsExactly [] :=
  malformed_exact [] rfl

example : rejectsExactly [false] :=
  malformed_exact [false] rfl

example : rejectsExactly [true] :=
  malformed_exact [true] rfl

example : rejectsExactly [false, true] :=
  malformed_exact [false, true] rfl

example : rejectsExactly [true, false, true] :=
  malformed_exact [true, false, true] rfl

/-! Reserved framing and a token-aligned grammar failure follow the same
machine-level fail-closed path. -/

example : rejectsExactly [true, true, false, true] :=
  malformed_exact [true, true, false, true] rfl

private def missingProgramBits : BitString :=
  encodeTokens (circuitGatesPrefixTokens 0 [])

private theorem missingProgramBits_decode_none :
    decodeCircuit missingProgramBits = none := by
  unfold missingProgramBits decodeCircuit
  rw [decodeTokens_encodeTokens]
  exact
    (decodeCircuitTokens_eq_none_iff_failure
      (circuitGatesPrefixTokens 0 [])).mpr
        (.missingProgramEnd 0 [])

example : rejectsExactly missingProgramBits :=
  malformed_exact missingProgramBits missingProgramBits_decode_none

/-! Canonical prefixes followed by incomplete raw tokens exercise the
machine-level malformed-tail path at parser continuations, rather than only at
the initial input boundary.  The two gate-start work symbols are each checked
both while a gate remains and after the declared gate count is exhausted. -/

private theorem decodeCircuit_encodeTokens_append_trailingOne_none
    (tokens : List Token) (bit : Bool) :
    decodeCircuit (encodeTokens tokens ++ [bit]) = none := by
  unfold decodeCircuit
  rw [decodeTokens_encodeTokens_append]
  rfl

private theorem decodeCircuit_encodeTokens_append_trailingTwo_none
    (tokens : List Token) (first second : Bool) :
    decodeCircuit (encodeTokens tokens ++ [first, second]) = none := by
  unfold decodeCircuit
  rw [decodeTokens_encodeTokens_append]
  rfl

private def gateStartPositiveZeroZeroBits : BitString :=
  encodeTokens (circuitHeaderTokens 0 1) ++ [false, false]

example : rejectsExactly gateStartPositiveZeroZeroBits :=
  malformed_exact gateStartPositiveZeroZeroBits (by
    unfold gateStartPositiveZeroZeroBits
    exact decodeCircuit_encodeTokens_append_trailingTwo_none
      (circuitHeaderTokens 0 1) false false)

private def gateStartPositiveZeroOneBits : BitString :=
  encodeTokens (circuitHeaderTokens 0 1) ++ [false, true]

example : rejectsExactly gateStartPositiveZeroOneBits :=
  malformed_exact gateStartPositiveZeroOneBits (by
    unfold gateStartPositiveZeroOneBits
    exact decodeCircuit_encodeTokens_append_trailingTwo_none
      (circuitHeaderTokens 0 1) false true)

private def gateStartExhaustedZeroZeroBits : BitString :=
  encodeTokens (circuitHeaderTokens 0 0) ++ [false, false]

example : rejectsExactly gateStartExhaustedZeroZeroBits :=
  malformed_exact gateStartExhaustedZeroZeroBits (by
    unfold gateStartExhaustedZeroZeroBits
    exact decodeCircuit_encodeTokens_append_trailingTwo_none
      (circuitHeaderTokens 0 0) false false)

private def gateStartExhaustedZeroOneBits : BitString :=
  encodeTokens (circuitHeaderTokens 0 0) ++ [false, true]

example : rejectsExactly gateStartExhaustedZeroOneBits :=
  malformed_exact gateStartExhaustedZeroOneBits (by
    unfold gateStartExhaustedZeroOneBits
    exact decodeCircuit_encodeTokens_append_trailingTwo_none
      (circuitHeaderTokens 0 0) false true)

/-! Source and unary-index continuations are checked on both sides of a gate,
followed by the gate terminator itself. -/

private def gateLeftInputIndexTailBits : BitString :=
  encodeTokens (circuitHeaderTokens 1 1 ++ [.input]) ++ [false]

example : rejectsExactly gateLeftInputIndexTailBits :=
  malformed_exact gateLeftInputIndexTailBits (by
    unfold gateLeftInputIndexTailBits
    exact decodeCircuit_encodeTokens_append_trailingOne_none
      (circuitHeaderTokens 1 1 ++ [.input]) false)

private def gateRightSourceTailBits : BitString :=
  encodeTokens
      (circuitHeaderTokens 0 1 ++
        encodeSourceTokens (.constant false)) ++
    [true]

example : rejectsExactly gateRightSourceTailBits :=
  malformed_exact gateRightSourceTailBits (by
    unfold gateRightSourceTailBits
    exact decodeCircuit_encodeTokens_append_trailingOne_none
      (circuitHeaderTokens 0 1 ++
        encodeSourceTokens (.constant false)) true)

private def gateRightGateIndexTailBits : BitString :=
  encodeTokens
      (circuitHeaderTokens 0 1 ++
        encodeSourceTokens (.constant false) ++ [.gate]) ++
    [false]

example : rejectsExactly gateRightGateIndexTailBits :=
  malformed_exact gateRightGateIndexTailBits (by
    unfold gateRightGateIndexTailBits
    exact decodeCircuit_encodeTokens_append_trailingOne_none
      (circuitHeaderTokens 0 1 ++
        encodeSourceTokens (.constant false) ++ [.gate]) false)

private def gateEndTailBits : BitString :=
  encodeTokens
      (circuitHeaderTokens 0 1 ++
        encodeSourceTokens (.constant false) ++
        encodeSourceTokens (.constant true)) ++
    [true]

example : rejectsExactly gateEndTailBits :=
  malformed_exact gateEndTailBits (by
    unfold gateEndTailBits
    exact decodeCircuit_encodeTokens_append_trailingOne_none
      (circuitHeaderTokens 0 1 ++
        encodeSourceTokens (.constant false) ++
        encodeSourceTokens (.constant true)) true)

/-! The same fail-closed path is pinned at the output source, its unary index,
both structural end tokens, and the final end-of-file boundary. -/

private def outputSourceTailBits : BitString :=
  encodeTokens
      (circuitGatesPrefixTokens 0 [] ++ [.programEnd]) ++
    [false]

example : rejectsExactly outputSourceTailBits :=
  malformed_exact outputSourceTailBits (by
    unfold outputSourceTailBits
    exact decodeCircuit_encodeTokens_append_trailingOne_none
      (circuitGatesPrefixTokens 0 [] ++ [.programEnd]) false)

private def outputInputIndexTailBits : BitString :=
  encodeTokens
      (circuitGatesPrefixTokens 1 [] ++ [.programEnd, .input]) ++
    [true]

example : rejectsExactly outputInputIndexTailBits :=
  malformed_exact outputInputIndexTailBits (by
    unfold outputInputIndexTailBits
    exact decodeCircuit_encodeTokens_append_trailingOne_none
      (circuitGatesPrefixTokens 1 [] ++ [.programEnd, .input]) true)

private def outputsEndTailBits : BitString :=
  encodeTokens
      (circuitOutputPrefixTokens 0 [] (.constant false)) ++
    [false]

example : rejectsExactly outputsEndTailBits :=
  malformed_exact outputsEndTailBits (by
    unfold outputsEndTailBits
    exact decodeCircuit_encodeTokens_append_trailingOne_none
      (circuitOutputPrefixTokens 0 [] (.constant false)) false)

private def instanceEndTailBits : BitString :=
  encodeTokens
      (circuitOutputPrefixTokens 0 [] (.constant false) ++
        [.outputsEnd]) ++
    [true]

example : rejectsExactly instanceEndTailBits :=
  malformed_exact instanceEndTailBits (by
    unfold instanceEndTailBits
    exact decodeCircuit_encodeTokens_append_trailingOne_none
      (circuitOutputPrefixTokens 0 [] (.constant false) ++
        [.outputsEnd]) true)

private def finalEofTailBits : BitString :=
  encodeTokens
      (circuitOutputPrefixTokens 0 [] (.constant false) ++
        [.outputsEnd, .instanceEnd]) ++
    [false]

example : rejectsExactly finalEofTailBits :=
  malformed_exact finalEofTailBits (by
    unfold finalEofTailBits
    exact decodeCircuit_encodeTokens_append_trailingOne_none
      (circuitOutputPrefixTokens 0 [] (.constant false) ++
        [.outputsEnd, .instanceEnd]) false)

/-! Canonical valid circuits: both zero-gate constants and a circuit with a
literal NAND gate. -/

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

example : constantFalseCircuit.wellFormed = true := rfl

example : constantTrueCircuit.wellFormed = true := rfl

example : oneGateCircuit.wellFormed = true := rfl

private theorem validEncoded_of_wellFormed
    (raw : RawCircuit) (wellFormed : raw.wellFormed = true) :
    ValidEncodedCircuit (encodeCircuit raw) := by
  unfold ValidEncodedCircuit
  exact
    (decodeElaboratedCircuit_exists_iff
      (encodeCircuit raw)).mpr
        ⟨raw, decodeCircuit_encodeCircuit raw, wellFormed⟩

private theorem constantFalseCircuit_valid :
    ValidEncodedCircuit (encodeCircuit constantFalseCircuit) :=
  validEncoded_of_wellFormed constantFalseCircuit rfl

private theorem constantTrueCircuit_valid :
    ValidEncodedCircuit (encodeCircuit constantTrueCircuit) :=
  validEncoded_of_wellFormed constantTrueCircuit rfl

private theorem oneGateCircuit_valid :
    ValidEncodedCircuit (encodeCircuit oneGateCircuit) :=
  validEncoded_of_wellFormed oneGateCircuit rfl

example : acceptsCanonicalExactly constantFalseCircuit :=
  wellFormed_exact constantFalseCircuit rfl

example : acceptsCanonicalExactly constantTrueCircuit :=
  wellFormed_exact constantTrueCircuit rfl

example : acceptsCanonicalExactly oneGateCircuit :=
  wellFormed_exact oneGateCircuit rfl

example :
    (encodeWorkTape
      (validFinalConfiguration constantFalseCircuit).tape).outputBits =
        encodeCircuit constantFalseCircuit := by
  simpa [validFinalConfiguration] using
    acceptedTape_outputBits constantFalseCircuit

example :
    (encodeWorkTape
      (validFinalConfiguration oneGateCircuit).tape).outputBits =
        encodeCircuit oneGateCircuit := by
  simpa [validFinalConfiguration] using
    acceptedTape_outputBits oneGateCircuit

/-! Canonically decoded but intrinsically ill-formed references are rejected:
one input index and one prior-gate index are each exactly out of range. -/

private def inputOutOfRangeCircuit : RawCircuit :=
  { inputCount := 0
    gates := []
    output := .input 0 }

private def gateOutOfRangeCircuit : RawCircuit :=
  { inputCount := 0
    gates := []
    output := .gate 0 }

example :
    decodeCircuit (encodeCircuit inputOutOfRangeCircuit) =
      some inputOutOfRangeCircuit :=
  decodeCircuit_encodeCircuit inputOutOfRangeCircuit

example : inputOutOfRangeCircuit.wellFormed = false := rfl

example :
    rejectsExactly (encodeCircuit inputOutOfRangeCircuit) :=
  illFormed_exact (encodeCircuit inputOutOfRangeCircuit)
    inputOutOfRangeCircuit
    (decodeCircuit_encodeCircuit inputOutOfRangeCircuit) rfl

example :
    decodeCircuit (encodeCircuit gateOutOfRangeCircuit) =
      some gateOutOfRangeCircuit :=
  decodeCircuit_encodeCircuit gateOutOfRangeCircuit

example : gateOutOfRangeCircuit.wellFormed = false := rfl

example :
    rejectsExactly (encodeCircuit gateOutOfRangeCircuit) :=
  illFormed_exact (encodeCircuit gateOutOfRangeCircuit)
    gateOutOfRangeCircuit
    (decodeCircuit_encodeCircuit gateOutOfRangeCircuit) rfl

/-! The unconditional work trace and all compiled observations are pinned
independently of any caller-supplied execution certificate. -/

example (bits : BitString) : runsTotallyExactly bits :=
  allInput_exact bits

example (bits : BitString) :
    boundedDecide compiledMachine
        (validRawTimePolynomial.eval bits.length) bits = .accept ↔
      ValidEncodedCircuit bits :=
  compiledBoundedDecide_accept_iff bits

example (bits : BitString) :
    boundedDecide compiledMachine
        (validRawTimePolynomial.eval bits.length) bits ≠ .timeout :=
  compiledBoundedDecide_ne_timeout bits

example (bits : BitString) :
    machineOutput compiledMachine
        (validRawTimePolynomial.eval bits.length) bits =
      validatedSourceBytes bits :=
  compiledMachineOutput_eq_validatedSourceBytes bits

example :
    FunctionProgram.RawRefinement
      validatedSourceBytesPolynomialTimeFunction.program :=
  validatedSourceBytesRawRefinement

example :
    boundedDecide compiledMachine
        (validRawTimePolynomial.eval
          (encodeCircuit constantFalseCircuit).length)
        (encodeCircuit constantFalseCircuit) = .accept :=
  (compiledBoundedDecide_accept_iff
    (encodeCircuit constantFalseCircuit)).mpr
      constantFalseCircuit_valid

example :
    boundedDecide compiledMachine
        (validRawTimePolynomial.eval
          (encodeCircuit constantTrueCircuit).length)
        (encodeCircuit constantTrueCircuit) = .accept :=
  (compiledBoundedDecide_accept_iff
    (encodeCircuit constantTrueCircuit)).mpr
      constantTrueCircuit_valid

example :
    boundedDecide compiledMachine
        (validRawTimePolynomial.eval
          (encodeCircuit oneGateCircuit).length)
        (encodeCircuit oneGateCircuit) = .accept :=
  (compiledBoundedDecide_accept_iff
    (encodeCircuit oneGateCircuit)).mpr
      oneGateCircuit_valid

example :
    machineOutput compiledMachine
        (validRawTimePolynomial.eval
          (encodeCircuit constantFalseCircuit).length)
        (encodeCircuit constantFalseCircuit) =
      encodeCircuit constantFalseCircuit := by
  rw [compiledMachineOutput_eq_validatedSourceBytes]
  exact validatedSourceBytes_of_valid constantFalseCircuit_valid

example :
    machineOutput compiledMachine
        (validRawTimePolynomial.eval 0) [] = [] := by
  simpa only [List.length_nil,
    validatedSourceBytes_empty] using
    (compiledMachineOutput_eq_validatedSourceBytes
      ([] : BitString))

example :
    boundedDecide compiledMachine
        (validRawTimePolynomial.eval 0) [] = .reject := by
  generalize verdictEq :
      boundedDecide compiledMachine
        (validRawTimePolynomial.eval 0) [] = verdict
  have notAccept : verdict ≠ .accept := by
    intro accepted
    have machineAccept :
        boundedDecide compiledMachine
            (validRawTimePolynomial.eval 0) [] =
          .accept :=
      verdictEq.trans accepted
    have valid : ValidEncodedCircuit [] :=
      (compiledBoundedDecide_accept_iff []).mp
        machineAccept
    exact empty_not_validEncodedCircuit valid
  have notTimeout : verdict ≠ .timeout := by
    intro timedOut
    exact
      (compiledBoundedDecide_ne_timeout [])
        (verdictEq.trans timedOut)
  cases verdict with
  | accept =>
      exact (notAccept rfl).elim
  | reject => rfl
  | timeout =>
      exact (notTimeout rfl).elim

example (bits : BitString) :
    Configuration.BlankEquivalent
      (startConfig compiledMachine bits)
      (encodeWorkConfiguration
        (workStartConfiguration machine
          (rawInputWorkTape bits))) :=
  compiledStart_blankEquivalent bits

example :
    PolynomialTimeMachine ValidEncodedCircuit :=
  polynomialTimeMachine

example :
    PolynomialTimeFunction :=
  validatedSourceBytesPolynomialTimeFunction

example (bits : BitString) :
    validatedSourceBytesPolynomialTimeFunction.output bits =
      validatedSourceBytes bits :=
  validatedSourceBytesPolynomialTimeFunction_output bits

/-! Literal machine size and polynomial arithmetic stay auditable. -/

example : SourceParser.statePrograms.length = 228 :=
  SourceParser.statePrograms_length

example : SourceParser.rules.length = 2052 := by
  simpa [SourceParser.ruleCount] using SourceParser.rules_length

example :
    SourceParser.rules.Pairwise SourceParser.QueryDistinct :=
  SourceParser.rules_pairwise_query_distinct

example :
    SourceParser.machine.startState ≠
      SourceParser.machine.acceptState :=
  SourceParser.machine_startState_ne_acceptState

example :
    SourceParser.machine.startState ≠
      SourceParser.machine.rejectState :=
  SourceParser.machine_startState_ne_rejectState

example :
    SourceParser.machine.acceptState ≠
      SourceParser.machine.rejectState :=
  SourceParser.machine_acceptState_ne_rejectState

example : validWorkBound 0 = 4096 := by
  rfl

example : validWorkBound 1 = 32768 := by
  rfl

example : validRawBound 0 = 24576 := by
  rfl

example : validRawTimePolynomial.eval 0 = 24576 := by
  rfl

example (bitLength : Nat) :
    validRawTimePolynomial.eval bitLength =
      6 *
        (4096 * (bitLength + 1) * (bitLength + 1) *
          (bitLength + 1)) := by
  rfl

end PNP.Concrete.LockedNAND.SourceParserRegression
