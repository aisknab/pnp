/-
Copyright (c) 2026 PNP Labs.

Machine-independent specification and output-size accounting for the complete
locked-NAND target emitter.  The standalone emitter's exact all-input function
is the grammar-only `RawBuilder.targetBytes`; parser composition supplies the
strict fail-closed external function below.  This file does not define an
emitter machine, runtime bound, `PolynomialTimeFunction`, or `RawRefinement`.
-/

import PNP.Concrete.LockedNANDRawBuilder
import PNP.Concrete.LockedNANDSourceParserSpec
import PNP.Concrete.LockedNANDSourceParserSemantics

namespace PNP.Concrete.LockedNAND
namespace TargetEmitterSpec

open DirectWire
open DirectWire.LockedNANDTrace
open DirectWire.LockedNANDGlobalCandidates

/-! ### Strict parser-composed target function -/

/-- The exact all-input target function after parser composition.

Successful strict-v0 decoding and elaboration launches the direct raw builder.
Every other input fails closed to the empty word. -/
def totalTargetBytes (bits : BitString) : BitString :=
  match decodeElaboratedCircuit bits with
  | none => []
  | some _ => RawBuilder.targetBytes bits

/-- Successful decoding selects the raw builder's exact target bytes. -/
theorem totalTargetBytes_of_decoded
    (bits : BitString) (packed : PackedCircuit)
    (decoded : decodeElaboratedCircuit bits = some packed) :
    totalTargetBytes bits = RawBuilder.targetBytes bits := by
  simp [totalTargetBytes, decoded]

/-- Failed strict decoding and elaboration clears the output completely. -/
theorem totalTargetBytes_of_malformed
    (bits : BitString)
    (malformed : decodeElaboratedCircuit bits = none) :
    totalTargetBytes bits = [] := by
  simp [totalTargetBytes, malformed]

/-- Validity is exactly the non-failure branch of the total target function. -/
theorem totalTargetBytes_of_valid
    {bits : BitString}
    (valid : SourceParser.ValidEncodedCircuit bits) :
    totalTargetBytes bits = RawBuilder.targetBytes bits := by
  rcases valid with ⟨packed, decoded⟩
  exact totalTargetBytes_of_decoded bits packed decoded

/-- Invalid strict-v0 sources are fail-closed. -/
theorem totalTargetBytes_of_not_valid
    {bits : BitString}
    (invalid : ¬ SourceParser.ValidEncodedCircuit bits) :
    totalTargetBytes bits = [] := by
  exact totalTargetBytes_of_malformed bits
    (SourceParser.decode_none_of_not_valid invalid)

/-- On a successful raw decode and elaboration, the target is byte-for-byte
the established legacy typed construction. -/
theorem totalTargetBytes_of_elaborated
    (bits : BitString) (raw : RawCircuit) (packed : PackedCircuit)
    (decoded : decodeCircuit bits = some raw)
    (elaborated : raw.elaborate = some packed) :
    totalTargetBytes bits =
      encodeLockedInstance (lockedInstanceOfCircuit packed.circuit) := by
  have strictDecoded :
      decodeElaboratedCircuit bits = some packed := by
    simp [decodeElaboratedCircuit, decoded, elaborated]
  rw [totalTargetBytes_of_decoded bits packed strictDecoded]
  rw [RawBuilder.targetBytes_of_decoded bits raw decoded]
  rw [RawBuilder.rawLockedInstance_of_elaborate raw packed elaborated]

/-- The direct raw target function and the pre-existing semantic builder agree
on every bitstring, including the empty failure branch. -/
theorem totalTargetBytes_eq_buildLockedNANDInstance
    (bits : BitString) :
    totalTargetBytes bits = buildLockedNANDInstance bits := by
  cases decoded : decodeElaboratedCircuit bits with
  | none =>
      rw [totalTargetBytes_of_malformed bits decoded]
      exact (buildLockedNANDInstance_of_malformed bits decoded).symm
  | some packed =>
      rw [totalTargetBytes_of_decoded bits packed decoded]
      unfold decodeElaboratedCircuit at decoded
      cases rawDecoded : decodeCircuit bits with
      | none =>
          rw [rawDecoded] at decoded
          contradiction
      | some raw =>
          rw [rawDecoded] at decoded
          exact RawBuilder.targetBytes_of_elaborated
            bits raw packed rawDecoded decoded

/-- The total target function therefore inherits the already-proved external
source/target language equivalence. -/
theorem totalTargetBytes_correct (bits : BitString) :
    EncodedNANDSAT bits ↔
      EncodedLockedNANDThreshold (totalTargetBytes bits) := by
  rw [totalTargetBytes_eq_buildLockedNANDInstance]
  exact buildLockedNANDInstance_correct bits

/-- The grammar-only raw target always emits at least its four-bit version
token whenever circuit decoding succeeds. -/
theorem encodeLockedInstance_ne_nil (rawInstance : RawLockedInstance) :
    encodeLockedInstance rawInstance ≠ [] := by
  cases rawInstance with
  | mk candidate baseline =>
      cases candidate with
      | mk inputs gates outputs =>
          simp [encodeLockedInstance, encodeLockedInstanceTokens,
            encodeTokens, Token.bits]

/-- A syntactically decoded but intrinsically invalid circuit still selects
the grammar-only raw-builder branch.  This behavior is intentional: strict
fail-closed behavior belongs to parser composition, not `RawBuilder.targetBytes`
in isolation. -/
theorem rawTargetBytes_ne_nil_of_decoded
    (bits : BitString) (raw : RawCircuit)
    (decoded : decodeCircuit bits = some raw) :
    RawBuilder.targetBytes bits ≠ [] := by
  rw [RawBuilder.targetBytes_of_decoded bits raw decoded]
  exact encodeLockedInstance_ne_nil _

/-- The strict total interface clears that same decoded-but-unelaboratable
input, making the two deliberately different boundaries explicit. -/
theorem totalTargetBytes_of_unelaboratable
    (bits : BitString) (raw : RawCircuit)
    (decoded : decodeCircuit bits = some raw)
    (unelaboratable : raw.elaborate = none) :
    totalTargetBytes bits = [] := by
  apply totalTargetBytes_of_malformed
  simp [decodeElaboratedCircuit, decoded, unelaboratable]

/-- The grammar-only builder and strict total target are observably distinct
on every decoded source that fails intrinsic elaboration. -/
theorem rawTargetBytes_ne_totalTargetBytes_of_unelaboratable
    (bits : BitString) (raw : RawCircuit)
    (decoded : decodeCircuit bits = some raw)
    (unelaboratable : raw.elaborate = none) :
    RawBuilder.targetBytes bits ≠ totalTargetBytes bits := by
  rw [totalTargetBytes_of_unelaboratable
    bits raw decoded unelaboratable]
  exact rawTargetBytes_ne_nil_of_decoded
    bits raw decoded

/-- Parser composition turns the grammar-only raw builder into the exact
strict total target function. -/
theorem targetBytes_validatedSourceBytes_eq_totalTargetBytes
    (bits : BitString) :
    RawBuilder.targetBytes (SourceParser.validatedSourceBytes bits) =
      totalTargetBytes bits := by
  cases decoded : decodeElaboratedCircuit bits with
  | none =>
      rw [SourceParser.validatedSourceBytes_of_decode_none bits decoded]
      rw [totalTargetBytes_of_malformed bits decoded]
      rfl
  | some packed =>
      rw [SourceParser.validatedSourceBytes_of_decoded
        bits packed decoded]
      exact (totalTargetBytes_of_decoded bits packed decoded).symm

/-- Crucial parser/emitter semantic handoff: validating first and then running
the grammar-only raw builder is exactly the pre-existing pure reduction on
every input. -/
theorem targetBytes_validatedSourceBytes_eq_buildLockedNANDInstance
    (bits : BitString) :
    RawBuilder.targetBytes (SourceParser.validatedSourceBytes bits) =
      buildLockedNANDInstance bits := by
  rw [targetBytes_validatedSourceBytes_eq_totalTargetBytes]
  exact totalTargetBytes_eq_buildLockedNANDInstance bits

/-! ### Exact codec lengths and typed serialization bounds -/

theorem encodeNatTokens_length (value : Nat) :
    (encodeNatTokens value).length = value + 1 := by
  induction value with
  | zero => rfl
  | succ value ih =>
      simp [encodeNatTokens, ih]

theorem encodeGateListTokens_append
    (first second : List RawGate) :
    encodeGateListTokens (first ++ second) =
      encodeGateListTokens first ++ encodeGateListTokens second := by
  induction first with
  | nil => rfl
  | cons gate rest ih =>
      simp [encodeGateListTokens, ih, List.append_assoc]

theorem encodeSourceListTokens_append
    (first second : List RawSource) :
    encodeSourceListTokens (first ++ second) =
      encodeSourceListTokens first ++ encodeSourceListTokens second := by
  induction first with
  | nil => rfl
  | cons source rest ih =>
      simp [encodeSourceListTokens, ih, List.append_assoc]

/-- Reifying one typed source uses at most the input width plus available
gate width plus one strict-v0 token. -/
theorem encodeSourceTokens_ofSource_length_le
    {inputs gates : Nat} (source : Source inputs gates) :
    (encodeSourceTokens (RawSource.ofSource source)).length ≤
      inputs + gates + 1 := by
  cases source with
  | input index =>
      simp [RawSource.ofSource, encodeSourceTokens,
        encodeNatTokens_length]
      omega
  | constant value =>
      cases value <;>
        simp [RawSource.ofSource, encodeSourceTokens]
  | gate index =>
      simp [RawSource.ofSource, encodeSourceTokens,
        encodeNatTokens_length]
      omega

/-- One reified typed gate obeys the corresponding two-source bound. -/
theorem encodeGateTokens_ofGate_length_le
    {inputs gates : Nat} (gate : Gate inputs gates) :
    (encodeGateTokens (RawGate.ofGate gate)).length ≤
      2 * (inputs + gates + 1) + 1 := by
  cases gate with
  | mk left right =>
      simp only [encodeGateTokens, RawGate.ofGate,
        List.length_append, List.length_cons, List.length_nil]
      have leftBound := encodeSourceTokens_ofSource_length_le left
      have rightBound := encodeSourceTokens_ofSource_length_le right
      omega

/-- Exact source-order reification of a typed program has a uniform gate-token
bound in its final input/gate dimensions. -/
theorem encodeGateListTokens_rawProgramGates_length_le
    {inputs gates : Nat} (program : Program inputs gates) :
    (encodeGateListTokens (rawProgramGates program)).length ≤
      gates * (2 * (inputs + gates + 1) + 1) := by
  induction program with
  | empty =>
      simp [rawProgramGates, encodeGateListTokens]
  | @snoc gates earlier gate ih =>
      rw [rawProgramGates, encodeGateListTokens_append]
      simp only [List.length_append, encodeGateListTokens,
        List.append_nil]
      let factor := 2 * (inputs + (gates + 1) + 1) + 1
      have earlierFactor :
          2 * (inputs + gates + 1) + 1 ≤ factor := by
        dsimp [factor]
        omega
      have earlierBound :
          (encodeGateListTokens (rawProgramGates earlier)).length ≤
            gates * factor :=
        Nat.le_trans ih (Nat.mul_le_mul_left gates earlierFactor)
      have gateBound :
          (encodeGateTokens (RawGate.ofGate gate)).length ≤ factor := by
        exact Nat.le_trans
          (encodeGateTokens_ofGate_length_le gate) earlierFactor
      have combined :=
        Nat.add_le_add earlierBound gateBound
      change
        (encodeGateListTokens (rawProgramGates earlier)).length +
            (encodeGateTokens (RawGate.ofGate gate)).length ≤
          (gates + 1) * factor
      rw [Nat.add_mul]
      simpa using combined

/-- A reified typed output tuple has the same uniform source-token bound. -/
theorem encodeSourceListTokens_rawOutputSources_length_le
    {inputs gates outputs : Nat}
    (word : OutputWord inputs gates outputs) :
    (encodeSourceListTokens (rawOutputSources word)).length ≤
      outputs * (inputs + gates + 1) := by
  induction word with
  | nil =>
      simp [rawOutputSources, encodeSourceListTokens]
  | @cons outputs head tail ih =>
      simp only [rawOutputSources, encodeSourceListTokens,
        List.length_append]
      have headBound := encodeSourceTokens_ofSource_length_le head
      have combined := Nat.add_le_add headBound ih
      rw [Nat.add_mul]
      simpa [Nat.add_comm] using combined

theorem rawOutputSources_length
    {inputs gates outputs : Nat}
    (word : OutputWord inputs gates outputs) :
    (rawOutputSources word).length = outputs := by
  induction word with
  | nil => rfl
  | @cons outputs head tail ih =>
      simp [rawOutputSources, ih]

/-- Serialization bound for any typed candidate reified at the raw boundary.
The right side records every unary header, gate/source payload, delimiter,
and threshold token before the fixed four-bit token encoding. -/
theorem encodeLockedInstance_ofCandidate_length_le
    {inputs gates outputs : Nat}
    (candidate : Candidate inputs gates outputs) (baseline : Nat) :
    (encodeLockedInstance
        (RawLockedInstance.ofCandidate candidate baseline)).length ≤
      4 *
        (inputs + gates + outputs + baseline + 9 +
          gates * (2 * (inputs + gates + 1) + 1) +
          outputs * (inputs + gates + 1)) := by
  rw [encodeLockedInstance, encodeTokens_length]
  have gateBound :=
    encodeGateListTokens_rawProgramGates_length_le candidate.program
  have outputBound :=
    encodeSourceListTokens_rawOutputSources_length_le candidate.outputs
  apply Nat.mul_le_mul_left 4
  simp only [encodeLockedInstanceTokens,
    RawLockedInstance.ofCandidate, RawCandidate.ofCandidate,
    List.length_cons, List.length_append, List.length_nil,
    encodeNatTokens_length, RawBuilder.rawProgramGates_length,
    rawOutputSources_length]
  omega

/-! ### Source-size accounting -/

/-- A circuit's unary input-width header is bounded by its encoded bits. -/
theorem inputCount_le_encodeCircuit_length (raw : RawCircuit) :
    raw.inputCount ≤ (encodeCircuit raw).length := by
  rw [encodeCircuit, encodeTokens_length]
  have tokenBound :
      raw.inputCount ≤ (encodeCircuitTokens raw).length := by
    simp only [encodeCircuitTokens, List.length_cons,
      List.length_append, List.length_nil, encodeNatTokens_length]
    omega
  exact Nat.le_trans tokenBound (by omega)

/-- The unary gate-count header gives the analogous source-size bound. -/
theorem gateCount_le_encodeCircuit_length (raw : RawCircuit) :
    raw.gates.length ≤ (encodeCircuit raw).length := by
  rw [encodeCircuit, encodeTokens_length]
  have tokenBound :
      raw.gates.length ≤ (encodeCircuitTokens raw).length := by
    simp only [encodeCircuitTokens, List.length_cons,
      List.length_append, List.length_nil, encodeNatTokens_length]
    omega
  exact Nat.le_trans tokenBound (by omega)

/-- Output normalization adds at most two source gates. -/
theorem normalize_gates_length_le (raw : RawCircuit) :
    raw.normalize.gates.length ≤ raw.gates.length + 2 := by
  cases raw with
  | mk inputs gates output =>
      cases output with
      | input index =>
          simp [RawCircuit.normalize]
      | gate index =>
          simp [RawCircuit.normalize]
      | constant value =>
          cases value <;> simp [RawCircuit.normalize]

/-- The source-derived locked baseline never exceeds 44 gates per normalized
source gate. -/
theorem lockedBaselineCount_le
    {inputs gates : Nat} (program : Program inputs gates) :
    lockedBaselineCount program ≤ 44 * gates := by
  rw [lockedBaselineCount_report_formula]
  have total := Program.sourceCounts_total program
  unfold SourceOccurrenceCounts.total at total
  omega

/-! ### Grammar-only raw-builder accounting -/

private def sourceCoordinatesLe (bound : Nat) : RawSource → Prop
  | .input index => index ≤ bound
  | .constant _ => True
  | .gate index => index ≤ bound

private def gateCoordinatesLe (bound : Nat) (gate : RawGate) : Prop :=
  sourceCoordinatesLe bound gate.left ∧
    sourceCoordinatesLe bound gate.right

private def gatesCoordinatesLe (bound : Nat) :
    List RawGate → Prop
  | [] => True
  | gate :: rest =>
      gateCoordinatesLe bound gate ∧ gatesCoordinatesLe bound rest

private def sourcesCoordinatesLe (bound : Nat) :
    List RawSource → Prop
  | [] => True
  | source :: rest =>
      sourceCoordinatesLe bound source ∧
        sourcesCoordinatesLe bound rest

private def bindingCoordinatesLe
    (bound : Nat) (binding : Nat → RawSource) : Prop :=
  ∀ index, sourceCoordinatesLe bound (binding index)

private def sourceCoordinatesLeDecidable (bound : Nat) :
    (source : RawSource) →
      Decidable (sourceCoordinatesLe bound source)
  | .input index => by
      change Decidable (index ≤ bound)
      infer_instance
  | .constant _ => isTrue trivial
  | .gate index => by
      change Decidable (index ≤ bound)
      infer_instance

private def gateCoordinatesLeDecidable
    (bound : Nat) (gate : RawGate) :
    Decidable (gateCoordinatesLe bound gate) := by
  change Decidable
    (sourceCoordinatesLe bound gate.left ∧
      sourceCoordinatesLe bound gate.right)
  letI := sourceCoordinatesLeDecidable bound gate.left
  letI := sourceCoordinatesLeDecidable bound gate.right
  exact inferInstance

private def gatesCoordinatesLeDecidable (bound : Nat) :
    (gates : List RawGate) →
      Decidable (gatesCoordinatesLe bound gates)
  | [] => isTrue trivial
  | gate :: rest => by
      change Decidable
        (gateCoordinatesLe bound gate ∧
          gatesCoordinatesLe bound rest)
      letI := gateCoordinatesLeDecidable bound gate
      letI := gatesCoordinatesLeDecidable bound rest
      exact inferInstance

private theorem sourceCoordinatesLe_mono
    {smaller larger : Nat} (bounded : smaller ≤ larger)
    {source : RawSource}
    (sourceBound : sourceCoordinatesLe smaller source) :
    sourceCoordinatesLe larger source := by
  cases source with
  | input index =>
      exact Nat.le_trans sourceBound bounded
  | constant value =>
      trivial
  | gate index =>
      exact Nat.le_trans sourceBound bounded

private theorem gateCoordinatesLe_mono
    {smaller larger : Nat} (bounded : smaller ≤ larger)
    {gate : RawGate}
    (gateBound : gateCoordinatesLe smaller gate) :
    gateCoordinatesLe larger gate := by
  cases gate
  exact ⟨sourceCoordinatesLe_mono bounded gateBound.1,
    sourceCoordinatesLe_mono bounded gateBound.2⟩

private theorem gatesCoordinatesLe_mono
    {smaller larger : Nat} (bounded : smaller ≤ larger)
    {gates : List RawGate}
    (gateBound : gatesCoordinatesLe smaller gates) :
    gatesCoordinatesLe larger gates := by
  induction gates with
  | nil => trivial
  | cons gate rest ih =>
      exact
        ⟨gateCoordinatesLe_mono bounded gateBound.1,
          ih gateBound.2⟩

private theorem sourcesCoordinatesLe_mono
    {smaller larger : Nat} (bounded : smaller ≤ larger)
    {sources : List RawSource}
    (sourceBound : sourcesCoordinatesLe smaller sources) :
    sourcesCoordinatesLe larger sources := by
  induction sources with
  | nil => trivial
  | cons source rest ih =>
      exact
        ⟨sourceCoordinatesLe_mono bounded sourceBound.1,
          ih sourceBound.2⟩

private theorem gatesCoordinatesLe_append
    (bound : Nat) (first second : List RawGate) :
    gatesCoordinatesLe bound (first ++ second) ↔
      gatesCoordinatesLe bound first ∧
        gatesCoordinatesLe bound second := by
  induction first with
  | nil =>
      simp [gatesCoordinatesLe]
  | cons gate rest ih =>
      simp only [List.cons_append, gatesCoordinatesLe]
      rw [ih]
      constructor
      · rintro ⟨gateBound, restBound, secondBound⟩
        exact ⟨⟨gateBound, restBound⟩, secondBound⟩
      · rintro ⟨⟨gateBound, restBound⟩, secondBound⟩
        exact ⟨gateBound, restBound, secondBound⟩

private theorem sourcesCoordinatesLe_append
    (bound : Nat) (first second : List RawSource) :
    sourcesCoordinatesLe bound (first ++ second) ↔
      sourcesCoordinatesLe bound first ∧
        sourcesCoordinatesLe bound second := by
  induction first with
  | nil =>
      simp [sourcesCoordinatesLe]
  | cons source rest ih =>
      simp only [List.cons_append, sourcesCoordinatesLe]
      rw [ih]
      constructor
      · rintro ⟨sourceBound, restBound, secondBound⟩
        exact ⟨⟨sourceBound, restBound⟩, secondBound⟩
      · rintro ⟨⟨sourceBound, restBound⟩, secondBound⟩
        exact ⟨sourceBound, restBound, secondBound⟩

private theorem sourceCoordinatesLe_encodeSourceTokens
    (source : RawSource) :
    sourceCoordinatesLe (encodeSourceTokens source).length source := by
  cases source with
  | input index =>
      simp [sourceCoordinatesLe, encodeSourceTokens,
        encodeNatTokens_length]
      omega
  | constant value =>
      simp [sourceCoordinatesLe]
  | gate index =>
      simp [sourceCoordinatesLe, encodeSourceTokens,
        encodeNatTokens_length]
      omega

private theorem gateCoordinatesLe_encodeGateTokens
    (gate : RawGate) :
    gateCoordinatesLe (encodeGateTokens gate).length gate := by
  cases gate with
  | mk left right =>
      constructor
      · exact sourceCoordinatesLe_mono
          (by
            simp only [encodeGateTokens, List.length_append,
              List.length_cons, List.length_nil]
            omega)
          (sourceCoordinatesLe_encodeSourceTokens left)
      · exact sourceCoordinatesLe_mono
          (by
            simp only [encodeGateTokens, List.length_append,
              List.length_cons, List.length_nil]
            omega)
          (sourceCoordinatesLe_encodeSourceTokens right)

private theorem gatesCoordinatesLe_encodeGateListTokens
    (gates : List RawGate) :
    gatesCoordinatesLe (encodeGateListTokens gates).length gates := by
  induction gates with
  | nil => trivial
  | cons gate rest ih =>
      constructor
      · exact gateCoordinatesLe_mono
          (by
            simp only [encodeGateListTokens, List.length_append]
            omega)
          (gateCoordinatesLe_encodeGateTokens gate)
      · exact gatesCoordinatesLe_mono
          (by
            simp only [encodeGateListTokens, List.length_append]
            omega)
          ih

private theorem rawCircuit_coordinates_le_encodeCircuit
    (raw : RawCircuit) :
    gatesCoordinatesLe (encodeCircuit raw).length raw.gates ∧
      sourceCoordinatesLe (encodeCircuit raw).length raw.output := by
  have gateTokensLe :
      (encodeGateListTokens raw.gates).length ≤
        (encodeCircuit raw).length := by
    rw [encodeCircuit, encodeTokens_length]
    simp only [encodeCircuitTokens, List.length_cons,
      List.length_append, List.length_nil]
    omega
  have outputTokensLe :
      (encodeSourceTokens raw.output).length ≤
        (encodeCircuit raw).length := by
    rw [encodeCircuit, encodeTokens_length]
    simp only [encodeCircuitTokens, List.length_cons,
      List.length_append, List.length_nil]
    omega
  exact
    ⟨gatesCoordinatesLe_mono gateTokensLe
        (gatesCoordinatesLe_encodeGateListTokens raw.gates),
      sourceCoordinatesLe_mono outputTokensLe
        (sourceCoordinatesLe_encodeSourceTokens raw.output)⟩

private theorem encodeSourceTokens_length_le_of_coordinates
    (bound : Nat) (source : RawSource)
    (sourceBound : sourceCoordinatesLe bound source) :
    (encodeSourceTokens source).length ≤ bound + 2 := by
  cases source with
  | input index =>
      simp [encodeSourceTokens, encodeNatTokens_length]
      simpa [sourceCoordinatesLe] using sourceBound
  | constant value =>
      cases value <;> simp [encodeSourceTokens]
  | gate index =>
      simp [encodeSourceTokens, encodeNatTokens_length]
      simpa [sourceCoordinatesLe] using sourceBound

private theorem encodeGateTokens_length_le_of_coordinates
    (bound : Nat) (gate : RawGate)
    (gateBound : gateCoordinatesLe bound gate) :
    (encodeGateTokens gate).length ≤ 2 * (bound + 2) + 1 := by
  cases gate with
  | mk left right =>
      simp only [encodeGateTokens, List.length_append,
        List.length_cons, List.length_nil]
      have leftBound :=
        encodeSourceTokens_length_le_of_coordinates
          bound left gateBound.1
      have rightBound :=
        encodeSourceTokens_length_le_of_coordinates
          bound right gateBound.2
      omega

private theorem encodeGateListTokens_length_le_of_coordinates
    (bound : Nat) (gates : List RawGate)
    (gateBound : gatesCoordinatesLe bound gates) :
    (encodeGateListTokens gates).length ≤
      gates.length * (2 * (bound + 2) + 1) := by
  induction gates with
  | nil =>
      simp [encodeGateListTokens]
  | cons gate rest ih =>
      simp only [encodeGateListTokens, List.length_append,
        List.length_cons]
      have headBound :=
        encodeGateTokens_length_le_of_coordinates
          bound gate gateBound.1
      have tailBound := ih gateBound.2
      have combined := Nat.add_le_add headBound tailBound
      rw [Nat.add_mul]
      simpa [Nat.add_comm] using combined

private theorem encodeSourceListTokens_length_le_of_coordinates
    (bound : Nat) (sources : List RawSource)
    (sourceBound : sourcesCoordinatesLe bound sources) :
    (encodeSourceListTokens sources).length ≤
      sources.length * (bound + 2) := by
  induction sources with
  | nil =>
      simp [encodeSourceListTokens]
  | cons source rest ih =>
      simp only [encodeSourceListTokens, List.length_append,
        List.length_cons]
      have headBound :=
        encodeSourceTokens_length_le_of_coordinates
          bound source sourceBound.1
      have tailBound := ih sourceBound.2
      have combined := Nat.add_le_add headBound tailBound
      rw [Nat.add_mul]
      simpa [Nat.add_comm] using combined

private theorem encodeLockedInstance_length_le_of_coordinates
    (rawInstance : RawLockedInstance) (bound : Nat)
    (gateBound :
      gatesCoordinatesLe bound rawInstance.candidate.gates)
    (outputBound :
      sourcesCoordinatesLe bound rawInstance.candidate.outputs) :
    (encodeLockedInstance rawInstance).length ≤
      4 *
        (rawInstance.candidate.inputCount +
            rawInstance.candidate.gates.length +
            rawInstance.candidate.outputs.length +
            rawInstance.baseline + 9 +
          rawInstance.candidate.gates.length *
            (2 * (bound + 2) + 1) +
          rawInstance.candidate.outputs.length * (bound + 2)) := by
  rw [encodeLockedInstance, encodeTokens_length]
  have gates :=
    encodeGateListTokens_length_le_of_coordinates
      bound rawInstance.candidate.gates gateBound
  have outputs :=
    encodeSourceListTokens_length_le_of_coordinates
      bound rawInstance.candidate.outputs outputBound
  apply Nat.mul_le_mul_left 4
  simp only [encodeLockedInstanceTokens,
    List.length_cons, List.length_append, List.length_nil,
    encodeNatTokens_length]
  omega

private theorem appendTemplate_length
    (gatePrefix : List RawGate) (binding : Nat → RawSource)
    (template : List RawGate) :
    (RawBuilder.appendTemplate gatePrefix binding template).length =
      gatePrefix.length + template.length := by
  simp [RawBuilder.appendTemplate]

private theorem instantiateSource_coordinatesLe
    (localBound offset bound : Nat)
    (binding : Nat → RawSource) (source : RawSource)
    (bindingBound : bindingCoordinatesLe bound binding)
    (sourceBound : sourceCoordinatesLe localBound source)
    (offsetBound : offset + localBound ≤ bound) :
    sourceCoordinatesLe bound
      (RawBuilder.instantiateSource offset binding source) := by
  cases source with
  | input index =>
      exact bindingBound index
  | constant value =>
      trivial
  | gate index =>
      simp only [sourceCoordinatesLe,
        RawBuilder.instantiateSource]
      have indexBound : index ≤ localBound := sourceBound
      omega

private theorem instantiateGate_coordinatesLe
    (localBound offset bound : Nat)
    (binding : Nat → RawSource) (gate : RawGate)
    (bindingBound : bindingCoordinatesLe bound binding)
    (gateBound : gateCoordinatesLe localBound gate)
    (offsetBound : offset + localBound ≤ bound) :
    gateCoordinatesLe bound
      (RawBuilder.instantiateGate offset binding gate) := by
  cases gate with
  | mk left right =>
      exact
        ⟨instantiateSource_coordinatesLe localBound offset bound
            binding left bindingBound gateBound.1 offsetBound,
          instantiateSource_coordinatesLe localBound offset bound
            binding right bindingBound gateBound.2 offsetBound⟩

private theorem instantiateGates_coordinatesLe
    (localBound offset bound : Nat)
    (binding : Nat → RawSource) (template : List RawGate)
    (bindingBound : bindingCoordinatesLe bound binding)
    (templateBound : gatesCoordinatesLe localBound template)
    (offsetBound : offset + localBound ≤ bound) :
    gatesCoordinatesLe bound
      (template.map
        (RawBuilder.instantiateGate offset binding)) := by
  induction template with
  | nil =>
      trivial
  | cons gate rest ih =>
      exact
        ⟨instantiateGate_coordinatesLe localBound offset bound
            binding gate bindingBound templateBound.1 offsetBound,
          ih templateBound.2⟩

private theorem appendTemplate_coordinatesLe
    (localBound bound : Nat)
    (gatePrefix template : List RawGate)
    (binding : Nat → RawSource)
    (prefixBound : gatesCoordinatesLe bound gatePrefix)
    (bindingBound : bindingCoordinatesLe bound binding)
    (templateBound : gatesCoordinatesLe localBound template)
    (offsetBound : gatePrefix.length + localBound ≤ bound) :
    gatesCoordinatesLe bound
      (RawBuilder.appendTemplate gatePrefix binding template) := by
  unfold RawBuilder.appendTemplate
  exact (gatesCoordinatesLe_append bound _ _).mpr
    ⟨prefixBound,
      instantiateGates_coordinatesLe localBound gatePrefix.length bound
        binding template bindingBound templateBound offsetBound⟩

private theorem rawBinding2_coordinatesLe
    (bound : Nat) (first second : RawSource)
    (firstBound : sourceCoordinatesLe bound first)
    (secondBound : sourceCoordinatesLe bound second) :
    bindingCoordinatesLe bound
      (RawBuilder.rawBinding2 first second) := by
  intro index
  unfold RawBuilder.rawBinding2
  split
  · exact firstBound
  split
  · exact secondBound
  · trivial

private theorem rawBinding3_coordinatesLe
    (bound : Nat) (first second third : RawSource)
    (firstBound : sourceCoordinatesLe bound first)
    (secondBound : sourceCoordinatesLe bound second)
    (thirdBound : sourceCoordinatesLe bound third) :
    bindingCoordinatesLe bound
      (RawBuilder.rawBinding3 first second third) := by
  intro index
  unfold RawBuilder.rawBinding3
  split
  · exact firstBound
  split
  · exact secondBound
  split
  · exact thirdBound
  · trivial

private theorem rawBinding4_coordinatesLe
    (bound : Nat) (first second third fourth : RawSource)
    (firstBound : sourceCoordinatesLe bound first)
    (secondBound : sourceCoordinatesLe bound second)
    (thirdBound : sourceCoordinatesLe bound third)
    (fourthBound : sourceCoordinatesLe bound fourth) :
    bindingCoordinatesLe bound
      (RawBuilder.rawBinding4 first second third fourth) := by
  intro index
  unfold RawBuilder.rawBinding4
  split
  · exact firstBound
  split
  · exact secondBound
  split
  · exact thirdBound
  split
  · exact fourthBound
  · trivial

private theorem equalityTemplate_coordinatesLe :
    gatesCoordinatesLe 18 RawBuilder.equalityTemplate := by
  letI :=
    gatesCoordinatesLeDecidable 18 RawBuilder.equalityTemplate
  decide

private theorem constantZeroTemplate_coordinatesLe :
    gatesCoordinatesLe 18 RawBuilder.constantZeroTemplate := by
  letI :=
    gatesCoordinatesLeDecidable 18 RawBuilder.constantZeroTemplate
  decide

private theorem constantOneTemplate_coordinatesLe :
    gatesCoordinatesLe 18 RawBuilder.constantOneTemplate := by
  letI :=
    gatesCoordinatesLeDecidable 18 RawBuilder.constantOneTemplate
  decide

private theorem traceTemplate_coordinatesLe :
    gatesCoordinatesLe 18 RawBuilder.traceTemplate := by
  letI :=
    gatesCoordinatesLeDecidable 18 RawBuilder.traceTemplate
  decide

private theorem prefixTemplate_coordinatesLe :
    gatesCoordinatesLe 18 RawBuilder.prefixTemplate := by
  letI :=
    gatesCoordinatesLeDecidable 18 RawBuilder.prefixTemplate
  decide

private theorem finalTemplate_coordinatesLe :
    gatesCoordinatesLe 18 RawBuilder.finalTemplate := by
  letI :=
    gatesCoordinatesLeDecidable 18 RawBuilder.finalTemplate
  decide

private theorem appendSourceMacro_gates_length_le
    (inputs totalGates gate side : Nat)
    (assembly : RawBuilder.MacroAssembly) (source : RawSource) :
    (RawBuilder.appendSourceMacro inputs totalGates gate side
        assembly source).gates.length ≤
      assembly.gates.length + 10 := by
  cases source with
  | input index =>
      simp [RawBuilder.appendSourceMacro, appendTemplate_length,
        RawBuilder.equalityTemplate_length]
  | constant value =>
      cases value <;>
        simp [RawBuilder.appendSourceMacro, appendTemplate_length,
          RawBuilder.constantZeroTemplate_length,
          RawBuilder.constantOneTemplate_length]
  | gate index =>
      simp [RawBuilder.appendSourceMacro, appendTemplate_length,
        RawBuilder.equalityTemplate_length]

private theorem appendTraceMacro_gates_length
    (inputs totalGates gate : Nat)
    (assembly : RawBuilder.MacroAssembly) :
    (RawBuilder.appendTraceMacro inputs totalGates gate
        assembly).gates.length =
      assembly.gates.length + 18 := by
  simp [RawBuilder.appendTraceMacro, appendTemplate_length,
    RawBuilder.traceTemplate_length]

private theorem sourceValueCoordinate_coordinatesLe
    (bitLength inputs totalGates : Nat) (source : RawSource)
    (inputBound : inputs ≤ bitLength)
    (_gateCountBound : totalGates ≤ bitLength)
    (sourceBound : sourceCoordinatesLe bitLength source) :
    sourceCoordinatesLe (100 * (bitLength + 1))
      (RawBuilder.sourceValueCoordinate inputs totalGates source) := by
  cases source with
  | input index =>
      change index ≤ 100 * (bitLength + 1)
      change index ≤ bitLength at sourceBound
      omega
  | constant value =>
      trivial
  | gate index =>
      change inputs + index ≤ 100 * (bitLength + 1)
      change index ≤ bitLength at sourceBound
      omega

private theorem appendSourceMacro_coordinatesLe
    (bitLength inputs totalGates gate side : Nat)
    (assembly : RawBuilder.MacroAssembly) (source : RawSource)
    (inputBound : inputs ≤ bitLength)
    (gateCountBound : totalGates ≤ bitLength)
    (gateBound : gate ≤ bitLength)
    (sideBound : side ≤ 1)
    (sourceBound : sourceCoordinatesLe bitLength source)
    (assemblyGates :
      gatesCoordinatesLe (100 * (bitLength + 1)) assembly.gates)
    (assemblyChecks :
      sourcesCoordinatesLe (100 * (bitLength + 1)) assembly.checks)
    (offsetBound :
      assembly.gates.length + 18 ≤ 100 * (bitLength + 1)) :
    let result :=
      RawBuilder.appendSourceMacro inputs totalGates gate side
        assembly source
    gatesCoordinatesLe (100 * (bitLength + 1)) result.gates ∧
      sourcesCoordinatesLe (100 * (bitLength + 1)) result.checks := by
  have lockBound :
      sourceCoordinatesLe (100 * (bitLength + 1))
        (.input
          (RawBuilder.sourceLockCoordinate
            inputs totalGates gate side)) := by
    change
      inputs + 3 * totalGates + (2 * gate + side) ≤
        100 * (bitLength + 1)
    omega
  have occurrenceBound :
      sourceCoordinatesLe (100 * (bitLength + 1))
        (.input
          (RawBuilder.occurrenceCoordinate
            inputs totalGates gate side)) := by
    change
      inputs + totalGates + (2 * gate + side) ≤
        100 * (bitLength + 1)
    omega
  have valueBound :=
    sourceValueCoordinate_coordinatesLe
      bitLength inputs totalGates source
      inputBound gateCountBound sourceBound
  cases source with
  | input index =>
      dsimp [RawBuilder.appendSourceMacro]
      constructor
      · exact appendTemplate_coordinatesLe 18
          (100 * (bitLength + 1)) assembly.gates
          RawBuilder.equalityTemplate
          (RawBuilder.rawBinding3
            (.input
              (RawBuilder.sourceLockCoordinate
                inputs totalGates gate side))
            (.input
              (RawBuilder.occurrenceCoordinate
                inputs totalGates gate side))
            (RawBuilder.sourceValueCoordinate
              inputs totalGates (.input index)))
          assemblyGates
          (rawBinding3_coordinatesLe _ _ _ _
            lockBound occurrenceBound valueBound)
          equalityTemplate_coordinatesLe offsetBound
      · exact (sourcesCoordinatesLe_append _ _ _).mpr
          ⟨assemblyChecks, by
            simp [sourcesCoordinatesLe, sourceCoordinatesLe]
            omega⟩
  | constant value =>
      cases value with
      | false =>
          dsimp [RawBuilder.appendSourceMacro]
          constructor
          · exact appendTemplate_coordinatesLe 18
              (100 * (bitLength + 1)) assembly.gates
              RawBuilder.constantZeroTemplate
              (RawBuilder.rawBinding2
                (.input
                  (RawBuilder.sourceLockCoordinate
                    inputs totalGates gate side))
                (.input
                  (RawBuilder.occurrenceCoordinate
                    inputs totalGates gate side)))
              assemblyGates
              (rawBinding2_coordinatesLe _ _ _
                lockBound occurrenceBound)
              constantZeroTemplate_coordinatesLe offsetBound
          · exact (sourcesCoordinatesLe_append _ _ _).mpr
              ⟨assemblyChecks, by
                simp [sourcesCoordinatesLe, sourceCoordinatesLe]
                omega⟩
      | true =>
          dsimp [RawBuilder.appendSourceMacro]
          constructor
          · exact appendTemplate_coordinatesLe 18
              (100 * (bitLength + 1)) assembly.gates
              RawBuilder.constantOneTemplate
              (RawBuilder.rawBinding2
                (.input
                  (RawBuilder.sourceLockCoordinate
                    inputs totalGates gate side))
                (.input
                  (RawBuilder.occurrenceCoordinate
                    inputs totalGates gate side)))
              assemblyGates
              (rawBinding2_coordinatesLe _ _ _
                lockBound occurrenceBound)
              constantOneTemplate_coordinatesLe offsetBound
          · exact (sourcesCoordinatesLe_append _ _ _).mpr
              ⟨assemblyChecks, by
                simp [sourcesCoordinatesLe, sourceCoordinatesLe]
                omega⟩
  | gate index =>
      dsimp [RawBuilder.appendSourceMacro]
      constructor
      · exact appendTemplate_coordinatesLe 18
          (100 * (bitLength + 1)) assembly.gates
          RawBuilder.equalityTemplate
          (RawBuilder.rawBinding3
            (.input
              (RawBuilder.sourceLockCoordinate
                inputs totalGates gate side))
            (.input
              (RawBuilder.occurrenceCoordinate
                inputs totalGates gate side))
            (RawBuilder.sourceValueCoordinate
              inputs totalGates (.gate index)))
          assemblyGates
          (rawBinding3_coordinatesLe _ _ _ _
            lockBound occurrenceBound valueBound)
          equalityTemplate_coordinatesLe offsetBound
      · exact (sourcesCoordinatesLe_append _ _ _).mpr
          ⟨assemblyChecks, by
            simp [sourcesCoordinatesLe, sourceCoordinatesLe]
            omega⟩

private theorem appendTraceMacro_coordinatesLe
    (bitLength inputs totalGates gate : Nat)
    (assembly : RawBuilder.MacroAssembly)
    (inputBound : inputs ≤ bitLength)
    (gateCountBound : totalGates ≤ bitLength)
    (gateBound : gate ≤ bitLength)
    (assemblyGates :
      gatesCoordinatesLe (100 * (bitLength + 1)) assembly.gates)
    (assemblyChecks :
      sourcesCoordinatesLe (100 * (bitLength + 1)) assembly.checks)
    (offsetBound :
      assembly.gates.length + 18 ≤ 100 * (bitLength + 1)) :
    let result :=
      RawBuilder.appendTraceMacro inputs totalGates gate assembly
    gatesCoordinatesLe (100 * (bitLength + 1)) result.gates ∧
      sourcesCoordinatesLe (100 * (bitLength + 1)) result.checks := by
  have traceLockBound :
      sourceCoordinatesLe (100 * (bitLength + 1))
        (.input
          (RawBuilder.traceLockCoordinate inputs totalGates gate)) := by
    change inputs + 5 * totalGates + gate ≤
      100 * (bitLength + 1)
    omega
  have traceBound :
      sourceCoordinatesLe (100 * (bitLength + 1))
        (.input
          (RawBuilder.traceCoordinate inputs totalGates gate)) := by
    change inputs + gate ≤ 100 * (bitLength + 1)
    omega
  have leftBound :
      sourceCoordinatesLe (100 * (bitLength + 1))
        (.input
          (RawBuilder.occurrenceCoordinate
            inputs totalGates gate 0)) := by
    change inputs + totalGates + (2 * gate + 0) ≤
      100 * (bitLength + 1)
    omega
  have rightBound :
      sourceCoordinatesLe (100 * (bitLength + 1))
        (.input
          (RawBuilder.occurrenceCoordinate
            inputs totalGates gate 1)) := by
    change inputs + totalGates + (2 * gate + 1) ≤
      100 * (bitLength + 1)
    omega
  dsimp [RawBuilder.appendTraceMacro]
  constructor
  · exact appendTemplate_coordinatesLe 18
      (100 * (bitLength + 1)) assembly.gates
      RawBuilder.traceTemplate
      (RawBuilder.rawBinding4
        (.input
          (RawBuilder.traceLockCoordinate inputs totalGates gate))
        (.input
          (RawBuilder.traceCoordinate inputs totalGates gate))
        (.input
          (RawBuilder.occurrenceCoordinate
            inputs totalGates gate 0))
        (.input
          (RawBuilder.occurrenceCoordinate
            inputs totalGates gate 1)))
      assemblyGates
      (rawBinding4_coordinatesLe _ _ _ _ _
        traceLockBound traceBound leftBound rightBound)
      traceTemplate_coordinatesLe offsetBound
  · exact (sourcesCoordinatesLe_append _ _ _).mpr
      ⟨assemblyChecks, by
        simp [sourcesCoordinatesLe, sourceCoordinatesLe]
        omega⟩

private theorem assembleGates_gates_length_le
    (inputs totalGates gate : Nat)
    (assembly : RawBuilder.MacroAssembly)
    (sourceGates : List RawGate) :
    (RawBuilder.assembleGates inputs totalGates gate
        assembly sourceGates).gates.length ≤
      assembly.gates.length + 38 * sourceGates.length := by
  induction sourceGates generalizing gate assembly with
  | nil =>
      simp [RawBuilder.assembleGates]
  | cons sourceGate rest ih =>
      simp only [RawBuilder.assembleGates]
      let left :=
        RawBuilder.appendSourceMacro inputs totalGates gate 0
          assembly sourceGate.left
      let right :=
        RawBuilder.appendSourceMacro inputs totalGates gate 1
          left sourceGate.right
      let trace :=
        RawBuilder.appendTraceMacro inputs totalGates gate right
      have leftLength :
          left.gates.length ≤ assembly.gates.length + 10 :=
        appendSourceMacro_gates_length_le
          inputs totalGates gate 0 assembly sourceGate.left
      have rightLength :
          right.gates.length ≤ left.gates.length + 10 :=
        appendSourceMacro_gates_length_le
          inputs totalGates gate 1 left sourceGate.right
      have traceLength :
          trace.gates.length = right.gates.length + 18 :=
        appendTraceMacro_gates_length
          inputs totalGates gate right
      have restLength := ih (gate + 1) trace
      dsimp only [left, right, trace] at leftLength rightLength traceLength restLength
      simp only [List.length_cons]
      omega

private theorem assembleGates_coordinatesLe
    (bitLength inputs totalGates gate : Nat)
    (assembly : RawBuilder.MacroAssembly)
    (sourceGates : List RawGate)
    (inputBound : inputs ≤ bitLength)
    (gateCountBound : totalGates ≤ bitLength)
    (progressBound : gate + sourceGates.length ≤ totalGates)
    (assemblyLength : assembly.gates.length ≤ 38 * gate)
    (assemblyGates :
      gatesCoordinatesLe (100 * (bitLength + 1)) assembly.gates)
    (assemblyChecks :
      sourcesCoordinatesLe (100 * (bitLength + 1)) assembly.checks)
    (sourceGatesBound :
      gatesCoordinatesLe bitLength sourceGates) :
    let result :=
      RawBuilder.assembleGates inputs totalGates gate assembly sourceGates
    gatesCoordinatesLe (100 * (bitLength + 1)) result.gates ∧
      sourcesCoordinatesLe (100 * (bitLength + 1)) result.checks := by
  induction sourceGates generalizing gate assembly with
  | nil =>
      exact ⟨assemblyGates, assemblyChecks⟩
  | cons sourceGate rest ih =>
      let left :=
        RawBuilder.appendSourceMacro inputs totalGates gate 0
          assembly sourceGate.left
      let right :=
        RawBuilder.appendSourceMacro inputs totalGates gate 1
          left sourceGate.right
      let trace :=
        RawBuilder.appendTraceMacro inputs totalGates gate right
      have gateBound : gate ≤ bitLength := by
        omega
      have leftOffset :
          assembly.gates.length + 18 ≤
            100 * (bitLength + 1) := by
        omega
      have leftFacts :=
        appendSourceMacro_coordinatesLe
          bitLength inputs totalGates gate 0 assembly sourceGate.left
          inputBound gateCountBound gateBound (by omega)
          sourceGatesBound.1.1 assemblyGates assemblyChecks leftOffset
      have leftLength :
          left.gates.length ≤ assembly.gates.length + 10 :=
        appendSourceMacro_gates_length_le
          inputs totalGates gate 0 assembly sourceGate.left
      have rightOffset :
          left.gates.length + 18 ≤
            100 * (bitLength + 1) := by
        omega
      have rightFacts :=
        appendSourceMacro_coordinatesLe
          bitLength inputs totalGates gate 1 left sourceGate.right
          inputBound gateCountBound gateBound (by omega)
          sourceGatesBound.1.2 leftFacts.1 leftFacts.2 rightOffset
      have rightLength :
          right.gates.length ≤ left.gates.length + 10 :=
        appendSourceMacro_gates_length_le
          inputs totalGates gate 1 left sourceGate.right
      have traceOffset :
          right.gates.length + 18 ≤
            100 * (bitLength + 1) := by
        omega
      have traceFacts :=
        appendTraceMacro_coordinatesLe
          bitLength inputs totalGates gate right
          inputBound gateCountBound gateBound
          rightFacts.1 rightFacts.2 traceOffset
      have traceLength :
          trace.gates.length = right.gates.length + 18 :=
        appendTraceMacro_gates_length
          inputs totalGates gate right
      have nextLength : trace.gates.length ≤ 38 * (gate + 1) := by
        omega
      have nextProgress :
          (gate + 1) + rest.length ≤ totalGates := by
        simp only [List.length_cons] at progressBound
        omega
      have result :=
        ih (gate + 1) trace nextProgress
          nextLength traceFacts.1 traceFacts.2 sourceGatesBound.2
      simpa only [RawBuilder.assembleGates] using result

private theorem macroAssembly_gates_length_le (raw : RawCircuit) :
    (RawBuilder.macroAssembly raw).gates.length ≤
      38 * raw.gates.length := by
  unfold RawBuilder.macroAssembly
  simpa [RawBuilder.emptyAssembly] using
    assembleGates_gates_length_le raw.inputCount raw.gates.length 0
      RawBuilder.emptyAssembly raw.gates

private theorem macroAssembly_coordinatesLe (raw : RawCircuit) :
    let bitLength := (encodeCircuit raw).length
    let assembly := RawBuilder.macroAssembly raw
    gatesCoordinatesLe (100 * (bitLength + 1)) assembly.gates ∧
      sourcesCoordinatesLe (100 * (bitLength + 1)) assembly.checks := by
  let bitLength := (encodeCircuit raw).length
  have inputBound : raw.inputCount ≤ bitLength :=
    inputCount_le_encodeCircuit_length raw
  have gateCountBound : raw.gates.length ≤ bitLength :=
    gateCount_le_encodeCircuit_length raw
  have rawCoordinates := rawCircuit_coordinates_le_encodeCircuit raw
  unfold RawBuilder.macroAssembly
  exact assembleGates_coordinatesLe
    bitLength raw.inputCount raw.gates.length 0
    RawBuilder.emptyAssembly raw.gates inputBound gateCountBound
    (by omega) (by simp [RawBuilder.emptyAssembly])
    (by simp [RawBuilder.emptyAssembly, gatesCoordinatesLe])
    (by simp [RawBuilder.emptyAssembly, sourcesCoordinatesLe])
    rawCoordinates.1

private theorem appendPrefix_gates_length_le
    (gatePrefix : List RawGate) (checks : List RawSource) :
    (RawBuilder.appendPrefix gatePrefix checks).gates.length ≤
      gatePrefix.length + 2 * checks.length := by
  induction checks generalizing gatePrefix with
  | nil =>
      simp [RawBuilder.appendPrefix]
  | cons head tail ih =>
      cases tail with
      | nil =>
          simp [RawBuilder.appendPrefix]
      | cons next rest =>
          simp only [RawBuilder.appendPrefix]
          let tailResult :=
            RawBuilder.appendPrefix gatePrefix (next :: rest)
          have tailLength := ih gatePrefix
          change
            tailResult.gates.length ≤
              gatePrefix.length + 2 * (next :: rest).length
            at tailLength
          change
            (RawBuilder.appendTemplate tailResult.gates
              (RawBuilder.rawBinding2 tailResult.output head)
              RawBuilder.prefixTemplate).length ≤
              gatePrefix.length +
                2 * (head :: next :: rest).length
          rw [appendTemplate_length, RawBuilder.prefixTemplate_length]
          simp only [List.length_cons] at tailLength ⊢
          omega

private theorem appendPrefix_coordinatesLe
    (bound : Nat) (gatePrefix : List RawGate)
    (checks : List RawSource)
    (gateBound : gatesCoordinatesLe bound gatePrefix)
    (checkBound : sourcesCoordinatesLe bound checks)
    (room :
      gatePrefix.length + 2 * checks.length + 18 ≤ bound) :
    let result := RawBuilder.appendPrefix gatePrefix checks
    gatesCoordinatesLe bound result.gates ∧
      sourceCoordinatesLe bound result.output := by
  induction checks generalizing gatePrefix with
  | nil =>
      exact ⟨gateBound, by trivial⟩
  | cons head tail ih =>
      cases tail with
      | nil =>
          exact ⟨gateBound, checkBound.1⟩
      | cons next rest =>
          let tailResult :=
            RawBuilder.appendPrefix gatePrefix (next :: rest)
          have tailRoom :
              gatePrefix.length +
                    2 * (next :: rest).length + 18 ≤
                bound := by
            simp only [List.length_cons] at room ⊢
            omega
          have tailFacts :=
            ih gatePrefix gateBound checkBound.2 tailRoom
          have tailLength :=
            appendPrefix_gates_length_le gatePrefix (next :: rest)
          have offsetRoom :
              tailResult.gates.length + 18 ≤ bound := by
            dsimp only [tailResult]
            exact Nat.le_trans
              (Nat.add_le_add_right tailLength 18) tailRoom
          have bindingBound :=
            rawBinding2_coordinatesLe bound tailResult.output head
              tailFacts.2 checkBound.1
          have appendedBound :=
            appendTemplate_coordinatesLe 18 bound
              tailResult.gates RawBuilder.prefixTemplate
              (RawBuilder.rawBinding2 tailResult.output head)
              tailFacts.1 bindingBound
              prefixTemplate_coordinatesLe offsetRoom
          simp only [RawBuilder.appendPrefix]
          exact
            ⟨appendedBound, by
              change tailResult.gates.length + 1 ≤ bound
              omega⟩

private theorem normalize_coordinatesLe (raw : RawCircuit) :
    let bitLength := (encodeCircuit raw).length
    gatesCoordinatesLe (bitLength + 2) raw.normalize.gates ∧
      sourceCoordinatesLe (bitLength + 2) raw.normalize.output := by
  let bitLength := (encodeCircuit raw).length
  have original := rawCircuit_coordinates_le_encodeCircuit raw
  cases raw with
  | mk inputs gates output =>
      cases output with
      | gate index =>
          exact
            ⟨gatesCoordinatesLe_mono (by omega) original.1,
              sourceCoordinatesLe_mono (by omega) original.2⟩
      | input index =>
          have indexBound : index ≤ bitLength := original.2
          have gatesBound :
              gatesCoordinatesLe (bitLength + 2) gates :=
            gatesCoordinatesLe_mono (by omega) original.1
          have gateLengthBound :
              gates.length ≤ bitLength :=
            gateCount_le_encodeCircuit_length
              { inputCount := inputs
                gates := gates
                output := .input index }
          simp only [RawCircuit.normalize]
          constructor
          · exact (gatesCoordinatesLe_append _ _ _).mpr
              ⟨gatesBound, by
                change
                  (index ≤ bitLength + 2 ∧ True) ∧
                    ((gates.length ≤ bitLength + 2 ∧
                        gates.length ≤ bitLength + 2) ∧ True)
                exact
                  ⟨⟨by omega, trivial⟩,
                    ⟨⟨by omega, by omega⟩, trivial⟩⟩⟩
          · change gates.length + 1 ≤ bitLength + 2
            omega
      | constant value =>
          have gatesBound :
              gatesCoordinatesLe (bitLength + 2) gates :=
            gatesCoordinatesLe_mono (by omega) original.1
          have gateLengthBound :
              gates.length ≤ bitLength :=
            gateCount_le_encodeCircuit_length
              { inputCount := inputs
                gates := gates
                output := .constant value }
          cases value <;>
            simp only [RawCircuit.normalize] <;>
            constructor
          all_goals
            first
            | exact (gatesCoordinatesLe_append _ _ _).mpr
                ⟨gatesBound, by
                  change (True ∧ True) ∧ True
                  exact ⟨⟨trivial, trivial⟩, trivial⟩⟩
            | change gates.length ≤ bitLength + 2
              omega

private theorem range_gate_sources_coordinatesLe
    (bound count : Nat) (countBound : count ≤ bound) :
    sourcesCoordinatesLe bound
      ((List.range count).map RawSource.gate) := by
  induction count with
  | zero =>
      trivial
  | succ count ih =>
      rw [List.range_succ, List.map_append]
      exact (sourcesCoordinatesLe_append _ _ _).mpr
        ⟨ih (by omega), by
          simp [sourcesCoordinatesLe, sourceCoordinatesLe]
          omega⟩

private structure RawInstanceBounds
    (rawInstance : RawLockedInstance)
    (sizeBound coordinateBound : Nat) : Prop where
  inputCount :
    rawInstance.candidate.inputCount ≤ sizeBound
  gateCount :
    rawInstance.candidate.gates.length ≤ sizeBound
  outputCount :
    rawInstance.candidate.outputs.length ≤ sizeBound
  baseline :
    rawInstance.baseline ≤ sizeBound
  gateCoordinates :
    gatesCoordinatesLe coordinateBound rawInstance.candidate.gates
  outputCoordinates :
    sourcesCoordinatesLe coordinateBound rawInstance.candidate.outputs

private theorem rawLockedInstance_bounds (raw : RawCircuit) :
    let bitLength := (encodeCircuit raw).length
    RawInstanceBounds (RawBuilder.rawLockedInstance raw)
      (100 * (bitLength + 1)) (300 * (bitLength + 1)) := by
  let bitLength := (encodeCircuit raw).length
  let circuit := raw.normalize
  let macroAssembly := RawBuilder.macroAssembly circuit
  let prefixAssembly :=
    RawBuilder.appendPrefix macroAssembly.gates macroAssembly.checks
  let baseline := prefixAssembly.gates.length
  let outputTrace : RawSource :=
    .input
      (RawBuilder.traceCoordinate circuit.inputCount circuit.gates.length
        (RawBuilder.outputGateIndex circuit.output))
  let finalGates :=
    RawBuilder.appendTemplate prefixAssembly.gates
      (RawBuilder.rawBinding3
        (.input
          (RawBuilder.finalLockCoordinate
            circuit.inputCount circuit.gates.length))
        prefixAssembly.output outputTrace)
      RawBuilder.finalTemplate
  have rawInputBound : raw.inputCount ≤ bitLength :=
    inputCount_le_encodeCircuit_length raw
  have rawGateBound : raw.gates.length ≤ bitLength :=
    gateCount_le_encodeCircuit_length raw
  have circuitInput :
      circuit.inputCount = raw.inputCount := by
    cases raw with
    | mk inputs gates output =>
        cases output with
        | input index => rfl
        | gate index => rfl
        | constant value => cases value <;> rfl
  have circuitGateBound :
      circuit.gates.length ≤ bitLength + 2 := by
    exact Nat.le_trans (normalize_gates_length_le raw)
      (Nat.add_le_add_right rawGateBound 2)
  have normalizedCoordinates := normalize_coordinatesLe raw
  have macroLength :
      macroAssembly.gates.length ≤ 38 * circuit.gates.length := by
    exact macroAssembly_gates_length_le circuit
  have macroChecksLength :
      macroAssembly.checks.length = 3 * circuit.gates.length := by
    unfold macroAssembly RawBuilder.macroAssembly
    rw [RawBuilder.assembleGates_checks_length]
    simp [RawBuilder.emptyAssembly]
  have macroCoordinatesSmall :
      gatesCoordinatesLe
          (100 * ((bitLength + 2) + 1)) macroAssembly.gates ∧
        sourcesCoordinatesLe
          (100 * ((bitLength + 2) + 1)) macroAssembly.checks := by
    unfold macroAssembly RawBuilder.macroAssembly
    exact assembleGates_coordinatesLe
      (bitLength + 2) circuit.inputCount circuit.gates.length 0
      RawBuilder.emptyAssembly circuit.gates
      (by rw [circuitInput]; omega)
      circuitGateBound (by omega)
      (by simp [RawBuilder.emptyAssembly])
      (by simp [RawBuilder.emptyAssembly, gatesCoordinatesLe])
      (by simp [RawBuilder.emptyAssembly, sourcesCoordinatesLe])
      normalizedCoordinates.1
  have coordinateScale :
      100 * ((bitLength + 2) + 1) ≤
        300 * (bitLength + 1) := by
    omega
  have macroCoordinates :
      gatesCoordinatesLe
          (300 * (bitLength + 1)) macroAssembly.gates ∧
        sourcesCoordinatesLe
          (300 * (bitLength + 1)) macroAssembly.checks :=
    ⟨gatesCoordinatesLe_mono coordinateScale macroCoordinatesSmall.1,
      sourcesCoordinatesLe_mono coordinateScale macroCoordinatesSmall.2⟩
  have prefixLength :
      prefixAssembly.gates.length ≤
        macroAssembly.gates.length + 2 * macroAssembly.checks.length := by
    exact appendPrefix_gates_length_le
      macroAssembly.gates macroAssembly.checks
  have baselineBound :
      baseline ≤ 44 * (bitLength + 2) := by
    dsimp only [baseline]
    omega
  have prefixRoom :
      macroAssembly.gates.length +
            2 * macroAssembly.checks.length + 18 ≤
        300 * (bitLength + 1) := by
    omega
  have prefixCoordinates :
      gatesCoordinatesLe
          (300 * (bitLength + 1)) prefixAssembly.gates ∧
        sourceCoordinatesLe
          (300 * (bitLength + 1)) prefixAssembly.output := by
    exact appendPrefix_coordinatesLe
      (300 * (bitLength + 1))
      macroAssembly.gates macroAssembly.checks
      macroCoordinates.1 macroCoordinates.2 prefixRoom
  rcases RawBuilder.normalize_output_isGate raw with
    ⟨outputIndex, outputGate⟩
  have outputIndexBound : outputIndex ≤ bitLength + 2 := by
    rw [outputGate] at normalizedCoordinates
    exact normalizedCoordinates.2
  have outputTraceBound :
      sourceCoordinatesLe (300 * (bitLength + 1)) outputTrace := by
    change
      circuit.inputCount +
          RawBuilder.outputGateIndex circuit.output ≤
        300 * (bitLength + 1)
    rw [outputGate]
    simp only [RawBuilder.outputGateIndex]
    rw [circuitInput]
    omega
  have finalLockBound :
      sourceCoordinatesLe (300 * (bitLength + 1))
        (.input
          (RawBuilder.finalLockCoordinate
            circuit.inputCount circuit.gates.length)) := by
    change
      circuit.inputCount + 6 * circuit.gates.length ≤
        300 * (bitLength + 1)
    rw [circuitInput]
    omega
  have finalRoom :
      prefixAssembly.gates.length + 18 ≤
        300 * (bitLength + 1) := by
    omega
  have finalCoordinates :
      gatesCoordinatesLe (300 * (bitLength + 1)) finalGates := by
    exact appendTemplate_coordinatesLe 18
      (300 * (bitLength + 1))
      prefixAssembly.gates RawBuilder.finalTemplate
      (RawBuilder.rawBinding3
        (.input
          (RawBuilder.finalLockCoordinate
            circuit.inputCount circuit.gates.length))
        prefixAssembly.output outputTrace)
      prefixCoordinates.1
      (rawBinding3_coordinatesLe _ _ _ _
        finalLockBound prefixCoordinates.2 outputTraceBound)
      finalTemplate_coordinatesLe finalRoom
  have finalLength :
      finalGates.length = baseline + 4 := by
    unfold finalGates
    rw [appendTemplate_length, RawBuilder.finalTemplate_length]
  have exposedCoordinates :
      sourcesCoordinatesLe (300 * (bitLength + 1))
        ((List.range baseline).map RawSource.gate ++
          [.gate (baseline + 3)]) := by
    apply (sourcesCoordinatesLe_append _ _ _).mpr
    constructor
    · exact range_gate_sources_coordinatesLe _ baseline (by omega)
    · simp [sourcesCoordinatesLe, sourceCoordinatesLe]
      omega
  have sizeScale :
      44 * (bitLength + 2) ≤ 100 * (bitLength + 1) := by
    omega
  unfold RawBuilder.rawLockedInstance
  dsimp only
  refine
    { inputCount := ?_
      gateCount := ?_
      outputCount := ?_
      baseline := ?_
      gateCoordinates := ?_
      outputCoordinates := ?_ }
  · change
      raw.normalize.inputCount + 6 * raw.normalize.gates.length + 1 ≤
        100 * (bitLength + 1)
    have normalizedGateBound :
        raw.normalize.gates.length ≤ bitLength + 2 := by
      simpa only [circuit] using circuitGateBound
    have normalizedInput :
        raw.normalize.inputCount = raw.inputCount := by
      simpa only [circuit] using circuitInput
    rw [normalizedInput]
    omega
  · change finalGates.length ≤ 100 * (bitLength + 1)
    rw [finalLength]
    omega
  · change
      ((List.range baseline).map RawSource.gate ++
        [RawSource.gate (baseline + 3)]).length ≤
          100 * (bitLength + 1)
    simp only [List.length_append, List.length_map,
      List.length_range, List.length_cons, List.length_nil]
    omega
  · change baseline ≤ 100 * (bitLength + 1)
    exact Nat.le_trans baselineBound sizeScale
  · change gatesCoordinatesLe (300 * (bitLength + 1)) finalGates
    exact finalCoordinates
  · change
      sourcesCoordinatesLe (300 * (bitLength + 1))
        ((List.range baseline).map RawSource.gate ++
          [.gate (baseline + 3)])
    exact exposedCoordinates

/-! ### Explicit polynomial output-size bounds -/

/-- All-input quadratic bound for the standalone grammar-only raw target.

Writing `s = n + 1`, its exact value is

`4 * (409*s + (100*s)*(605*s) + (100*s)*(302*s))`.

This bound includes decoded-but-unelaboratable circuits.  No validity or
well-formedness hypothesis occurs in its proof. -/
def rawTargetOutputSizePolynomial : NatPolynomial :=
  let shifted : NatPolynomial := .add .variable (.constant 1)
  .mul (.constant 4)
    (.add
      (.add
        (.mul (.constant 409) shifted)
        (.mul
          (.mul (.constant 100) shifted)
          (.mul (.constant 605) shifted)))
      (.mul
        (.mul (.constant 100) shifted)
        (.mul (.constant 302) shifted)))

theorem rawTargetOutputSizePolynomial_eval (bitLength : Nat) :
    rawTargetOutputSizePolynomial.eval bitLength =
      4 *
        (409 * (bitLength + 1) +
          (100 * (bitLength + 1)) * (605 * (bitLength + 1)) +
          (100 * (bitLength + 1)) * (302 * (bitLength + 1))) := by
  rfl

private theorem rawLockedInstance_length_le (raw : RawCircuit) :
    (encodeLockedInstance
        (RawBuilder.rawLockedInstance raw)).length ≤
      rawTargetOutputSizePolynomial.eval (encodeCircuit raw).length := by
  let bitLength := (encodeCircuit raw).length
  let shifted := bitLength + 1
  let rawInstance := RawBuilder.rawLockedInstance raw
  have bounds := rawLockedInstance_bounds raw
  have serialized :=
    encodeLockedInstance_length_le_of_coordinates
      rawInstance (300 * shifted)
      bounds.gateCoordinates bounds.outputCoordinates
  have shiftedPositive : 1 ≤ shifted := by
    dsimp [shifted]
    omega
  have inputCountBound :
      rawInstance.candidate.inputCount ≤ 100 * shifted := by
    simpa [rawInstance, bitLength, shifted] using bounds.inputCount
  have gateCountBound :
      rawInstance.candidate.gates.length ≤ 100 * shifted := by
    simpa [rawInstance, bitLength, shifted] using bounds.gateCount
  have outputCountBound :
      rawInstance.candidate.outputs.length ≤ 100 * shifted := by
    simpa [rawInstance, bitLength, shifted] using bounds.outputCount
  have baselineBound :
      rawInstance.baseline ≤ 100 * shifted := by
    simpa [rawInstance, bitLength, shifted] using bounds.baseline
  have headerBound :
      rawInstance.candidate.inputCount +
            rawInstance.candidate.gates.length +
            rawInstance.candidate.outputs.length +
            rawInstance.baseline + 9 ≤
        409 * shifted := by
    omega
  have gateFactorBound :
      2 * (300 * shifted + 2) + 1 ≤ 605 * shifted := by
    omega
  have outputFactorBound :
      300 * shifted + 2 ≤ 302 * shifted := by
    omega
  have gateProduct :
      rawInstance.candidate.gates.length *
          (2 * (300 * shifted + 2) + 1) ≤
        (100 * shifted) * (605 * shifted) :=
    Nat.mul_le_mul bounds.gateCount gateFactorBound
  have outputProduct :
      rawInstance.candidate.outputs.length *
          (300 * shifted + 2) ≤
        (100 * shifted) * (302 * shifted) :=
    Nat.mul_le_mul bounds.outputCount outputFactorBound
  have bodyBound :
      rawInstance.candidate.inputCount +
              rawInstance.candidate.gates.length +
              rawInstance.candidate.outputs.length +
              rawInstance.baseline + 9 +
            rawInstance.candidate.gates.length *
              (2 * (300 * shifted + 2) + 1) +
          rawInstance.candidate.outputs.length *
            (300 * shifted + 2) ≤
        409 * shifted +
            (100 * shifted) * (605 * shifted) +
          (100 * shifted) * (302 * shifted) := by
    exact Nat.add_le_add
      (Nat.add_le_add headerBound gateProduct) outputProduct
  rw [rawTargetOutputSizePolynomial_eval]
  exact Nat.le_trans serialized
    (by
      simpa [rawInstance, bitLength, shifted] using
        Nat.mul_le_mul_left 4 bodyBound)

/-- The standalone grammar-only target has the explicit quadratic bound on
every bitstring, including both framing failure and reference failure. -/
theorem targetBytes_length_le (bits : BitString) :
    (RawBuilder.targetBytes bits).length ≤
      rawTargetOutputSizePolynomial.eval bits.length := by
  cases decoded : decodeCircuit bits with
  | none =>
      rw [RawBuilder.targetBytes_of_malformed bits decoded]
      exact Nat.zero_le _
  | some raw =>
      rw [RawBuilder.targetBytes_of_decoded bits raw decoded]
      have canonical :=
        encodeCircuit_eq_of_decodeCircuit_eq_some bits raw decoded
      rw [← canonical]
      exact rawLockedInstance_length_le raw

/-- Named bit-size form of the standalone all-input output bound. -/
theorem targetBytes_size_le (bits : BitString) :
    BitString.size (RawBuilder.targetBytes bits) ≤
      rawTargetOutputSizePolynomial.eval (BitString.size bits) :=
  targetBytes_length_le bits

/-- Auditable quadratic output-size polynomial.

Writing `s = n + 1`, its exact value is

`4 * (409*s + (100*s)*(403*s) + (100*s)*(201*s))`.

The constants separately bound the fixed/header tokens, all gate-source
tokens, and all exposed-output tokens. -/
def outputSizePolynomial : NatPolynomial :=
  let shifted : NatPolynomial := .add .variable (.constant 1)
  .mul (.constant 4)
    (.add
      (.add
        (.mul (.constant 409) shifted)
        (.mul
          (.mul (.constant 100) shifted)
          (.mul (.constant 403) shifted)))
      (.mul
        (.mul (.constant 100) shifted)
        (.mul (.constant 201) shifted)))

theorem outputSizePolynomial_eval (bitLength : Nat) :
    outputSizePolynomial.eval bitLength =
      4 *
        (409 * (bitLength + 1) +
          (100 * (bitLength + 1)) * (403 * (bitLength + 1)) +
          (100 * (bitLength + 1)) * (201 * (bitLength + 1))) := by
  rfl

private theorem encodedLegacyTarget_length_le
    {inputs : Nat} (circuit : Circuit inputs) (bitLength : Nat)
    (inputBound : inputs ≤ bitLength)
    (gateBound : circuit.gateCount ≤ bitLength + 2) :
    (encodeLockedInstance (lockedInstanceOfCircuit circuit)).length ≤
      outputSizePolynomial.eval bitLength := by
  let shifted := bitLength + 1
  let baseline := lockedBaselineCount circuit.program
  have shiftedPositive : 1 ≤ shifted := by
    dsimp [shifted]
    omega
  have baselineLinear : baseline ≤ 44 * circuit.gateCount :=
    lockedBaselineCount_le circuit.program
  have inputWidthBound :
      carrierWidth inputs circuit.gateCount ≤ 100 * shifted := by
    unfold carrierWidth
    dsimp [shifted]
    omega
  have baselineBound : baseline ≤ 100 * shifted := by
    dsimp [baseline, shifted] at baselineLinear ⊢
    omega
  have fullGateBound : baseline + 4 ≤ 100 * shifted := by
    omega
  have outputCountBound : baseline + 1 ≤ 100 * shifted := by
    omega
  have headerBound :
      carrierWidth inputs circuit.gateCount +
          (baseline + 4) + (baseline + 1) + baseline + 9 ≤
        409 * shifted := by
    omega
  have gateFactorBound :
      2 *
            (carrierWidth inputs circuit.gateCount +
              (baseline + 4) + 1) +
          1 ≤
        403 * shifted := by
    omega
  have outputFactorBound :
      carrierWidth inputs circuit.gateCount +
          (baseline + 4) + 1 ≤
        201 * shifted := by
    omega
  have serialized :=
    encodeLockedInstance_ofCandidate_length_le
      (fullCandidate circuit) baseline
  have gateProduct :
      (baseline + 4) *
          (2 *
              (carrierWidth inputs circuit.gateCount +
                (baseline + 4) + 1) +
            1) ≤
        (100 * shifted) * (403 * shifted) :=
    Nat.mul_le_mul fullGateBound gateFactorBound
  have outputProduct :
      (baseline + 1) *
          (carrierWidth inputs circuit.gateCount +
            (baseline + 4) + 1) ≤
        (100 * shifted) * (201 * shifted) :=
    Nat.mul_le_mul outputCountBound outputFactorBound
  have bodyBound :
      carrierWidth inputs circuit.gateCount +
            (baseline + 4) + (baseline + 1) + baseline + 9 +
          (baseline + 4) *
            (2 *
                (carrierWidth inputs circuit.gateCount +
                  (baseline + 4) + 1) +
              1) +
          (baseline + 1) *
            (carrierWidth inputs circuit.gateCount +
              (baseline + 4) + 1) ≤
        409 * shifted +
            (100 * shifted) * (403 * shifted) +
          (100 * shifted) * (201 * shifted) := by
    exact Nat.add_le_add
      (Nat.add_le_add headerBound gateProduct) outputProduct
  rw [outputSizePolynomial_eval]
  exact Nat.le_trans serialized
    (by
      simpa [baseline, shifted] using
        Nat.mul_le_mul_left 4 bodyBound)

/-- Every valid strict-v0 source has a quadratic-size exact target. -/
theorem totalTargetBytes_length_le_of_valid
    {bits : BitString}
    (valid : SourceParser.ValidEncodedCircuit bits) :
    (totalTargetBytes bits).length ≤
      outputSizePolynomial.eval bits.length := by
  rcases valid with ⟨packed, decoded⟩
  rcases
      decodeElaboratedCircuit_eq_some_exists_encoded_wellFormed
        bits packed decoded with
    ⟨raw, encoded, _wellFormed⟩
  have rawDecoded : decodeCircuit bits = some raw := by
    rw [encoded, decodeCircuit_encodeCircuit]
  have elaborated : raw.elaborate = some packed := by
    unfold decodeElaboratedCircuit at decoded
    rw [rawDecoded] at decoded
    exact decoded
  rw [totalTargetBytes_of_elaborated
    bits raw packed rawDecoded elaborated]
  have inputBound :
      packed.inputCount ≤ bits.length := by
    have rawBound := inputCount_le_encodeCircuit_length raw
    rw [← encoded] at rawBound
    have normalizedEq :=
      RawBuilder.ofCircuit_eq_normalize_of_elaborate
        raw packed elaborated
    have inputEq :=
      congrArg RawCircuit.inputCount normalizedEq
    simp only [RawCircuit.ofCircuit] at inputEq
    have normalizeInput :
        raw.normalize.inputCount = raw.inputCount := by
      cases raw with
      | mk inputs gates output =>
          cases output with
          | input index => rfl
          | gate index => rfl
          | constant value => cases value <;> rfl
    rw [inputEq]
    rw [normalizeInput]
    exact rawBound
  have normalizedGateBound :
      raw.normalize.gates.length ≤ bits.length + 2 := by
    exact Nat.le_trans (normalize_gates_length_le raw)
      (Nat.add_le_add_right
        (by
          have rawBound := gateCount_le_encodeCircuit_length raw
          simpa [encoded] using rawBound)
        2)
  have packedGateBound :
      packed.circuit.gateCount ≤ bits.length + 2 := by
    have normalizedEq :=
      RawBuilder.ofCircuit_eq_normalize_of_elaborate
        raw packed elaborated
    have gateEq :=
      congrArg (fun circuit => circuit.gates.length) normalizedEq
    simp only [RawCircuit.ofCircuit,
      RawBuilder.rawProgramGates_length] at gateEq
    rw [gateEq]
    exact normalizedGateBound
  exact encodedLegacyTarget_length_le packed.circuit bits.length
    inputBound packedGateBound

/-- The named bit-size interface obeys the same explicit polynomial. -/
theorem totalTargetBytes_size_le (bits : BitString) :
    BitString.size (totalTargetBytes bits) ≤
      outputSizePolynomial.eval (BitString.size bits) := by
  cases decoded : decodeElaboratedCircuit bits with
  | none =>
      rw [totalTargetBytes_of_malformed bits decoded]
      exact Nat.zero_le _
  | some packed =>
      exact totalTargetBytes_length_le_of_valid
        ⟨packed, decoded⟩

/-! ### Machine-independent handoff contracts -/

/-- Exact extensional contract for a later standalone grammar-only target
emitter.

This is the all-input machine contract: decoded circuits are emitted even when
their references cannot be elaborated.  It deliberately does not require or
construct an executable machine witness. -/
def ImplementsRawTarget
    (output : BitString → BitString) : Prop :=
  ∀ bits, output bits = RawBuilder.targetBytes bits

namespace ImplementsRawTarget

/-- Every implementation of the raw contract inherits the all-input quadratic
output bound. -/
theorem output_size_le
    {output : BitString → BitString}
    (implements : ImplementsRawTarget output)
    (bits : BitString) :
    BitString.size (output bits) ≤
      rawTargetOutputSizePolynomial.eval (BitString.size bits) := by
  rw [implements bits]
  exact targetBytes_size_le bits

/-- Composing a raw emitter after strict validation recovers the established
legacy target on every source bitstring. -/
theorem validated_source_handoff
    {output : BitString → BitString}
    (implements : ImplementsRawTarget output)
    (bits : BitString) :
    output (SourceParser.validatedSourceBytes bits) =
      buildLockedNANDInstance bits := by
  rw [implements (SourceParser.validatedSourceBytes bits)]
  exact targetBytes_validatedSourceBytes_eq_buildLockedNANDInstance bits

/-- A raw implementation emits a nonempty target for every successfully decoded
circuit, without assuming elaboration. -/
theorem output_ne_nil_of_decoded
    {output : BitString → BitString}
    (implements : ImplementsRawTarget output)
    {bits : BitString}
    {raw : RawCircuit}
    (decoded : decodeCircuit bits = some raw) :
    output bits ≠ [] := by
  rw [implements bits]
  exact rawTargetBytes_ne_nil_of_decoded bits raw decoded

/-- The behavior intentionally differs from the strict parser-composed target
on decoded inputs whose references cannot be elaborated. -/
theorem output_ne_totalTarget_of_unelaboratable
    {output : BitString → BitString}
    (implements : ImplementsRawTarget output)
    {bits : BitString}
    {raw : RawCircuit}
    (decoded : decodeCircuit bits = some raw)
    (unelaboratable : raw.elaborate = none) :
    output bits ≠ totalTargetBytes bits := by
  rw [implements bits]
  exact
    rawTargetBytes_ne_totalTargetBytes_of_unelaboratable
      bits raw decoded unelaboratable

end ImplementsRawTarget

/-- Exact extensional contract for a later parser-composed target emitter.

Unlike `ImplementsRawTarget`, this strict interface rejects decoded inputs that
cannot be elaborated before invoking the raw target grammar. -/
def ImplementsTotalTarget
    (output : BitString → BitString) : Prop :=
  ∀ bits, output bits = totalTargetBytes bits

namespace ImplementsTotalTarget

theorem output_size_le
    {output : BitString → BitString}
    (implements : ImplementsTotalTarget output)
    (bits : BitString) :
    BitString.size (output bits) ≤
      outputSizePolynomial.eval (BitString.size bits) := by
  rw [implements bits]
  exact totalTargetBytes_size_le bits

theorem legacy_handoff
    {output : BitString → BitString}
    (implements : ImplementsTotalTarget output)
    (bits : BitString) :
    output bits = buildLockedNANDInstance bits := by
  rw [implements bits]
  exact totalTargetBytes_eq_buildLockedNANDInstance bits

theorem correct
    {output : BitString → BitString}
    (implements : ImplementsTotalTarget output)
    (bits : BitString) :
    EncodedNANDSAT bits ↔ EncodedLockedNANDThreshold (output bits) := by
  rw [implements bits]
  exact totalTargetBytes_correct bits

end ImplementsTotalTarget

end TargetEmitterSpec
end PNP.Concrete.LockedNAND
