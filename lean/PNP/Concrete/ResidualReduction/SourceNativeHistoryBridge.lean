import PNP.Concrete.ResidualReduction.SourceNativeEnvelopeOutput

/-! Closed native-system/history composition. Only the source bytes are supplied.
The converter constructs the complete family, the history machine reduces it,
and the final writer restores the original dimension before the reduction data.
Every relay clears its workspace, and all copying is subsequently compiled. -/

namespace PNP.Concrete.ResidualReduction.SourceNativeHistoryBridge
open PNP.Concrete PNP.Concrete.BitRegister PNP.Concrete.NormalizerBlocks
open PNP.Concrete.NativeNormalization NativeBitCodec
open PNP.Concrete.ResidualReduction.SourceNativeEnvelopeState

def dimension (input : BitString) : BitString := (SourceNativeSystemParse.result input).dimension
def family (input : BitString) : BitString := SourceNativeSystemInput.answer input
def answer (input : BitString) : BitString :=
  SourceNativeEnvelopeOutput.output (SourceHistoryRaw.answer (family input)) (dimension input)
def result (input : BitString) : Store 64 :=
  SourceNativeEnvelopeOutput.result (SourceHistoryRaw.answer (family input)) (dimension input)
def block : Block 64 :=
  .seq system (.seq captureDimension (.seq relay (.seq history (.seq relay SourceNativeEnvelopeOutput.block))))

def sizePolynomial : NatPolynomial := .add .variable SourceNativeSystemInput.sourceFuel
def costPolynomial : NatPolynomial := .add SourceNativeSystemInput.sourceFuel
  (.add (SourceHistoryRaw.sourceFuel.substitute sizePolynomial)
    (.add (.mul (.constant 4) sizePolynomial) (.constant 140)))
theorem costPolynomial_eval (L : Nat) :
    costPolynomial.eval L = SourceNativeSystemInput.sourceFuel.eval L +
      SourceHistoryRaw.sourceFuel.eval (sizePolynomial.eval L) + 4 * sizePolynomial.eval L + 140 := by
  simp only [costPolynomial,NatPolynomial.eval_add,NatPolynomial.eval_substitute,
    NatPolynomial.eval_mul,NatPolynomial.eval_constant,Nat.add_assoc]

theorem family_bound (input : BitString) : (family input).length ≤ sizePolynomial.eval input.length := by
  have bound := SourceNativeSystemPolynomial.output_length input
  rw [SourceNativeSystemPolynomial.polynomial_output] at bound
  exact bound
theorem dimension_bound (input : BitString) : (dimension input).length ≤ sizePolynomial.eval input.length := by
  have bound := SourceNativeSystemParse.field_bound input .dimension
  simp only [SourceNativeSystemState.Field.word] at bound
  simp only [dimension,sizePolynomial,NatPolynomial.eval_add,NatPolynomial.eval_variable,
    SourceNativeSystemInput.sourceFuel_eval,SourceNativeSystemInput.budget]
  omega

theorem block_exec (input : BitString) :
    ∃ used, Exec block (work input [] []) used (result input) ∧
      used ≤ costPolynomial.eval input.length := by
  let saved := dimension input
  have first := system_exec input []
  have capture := capture_exec (systemResult input) []
  rw [system_dimension] at capture
  have relayIn := relay_exec (systemResult input) saved
  rw [system_output] at relayIn
  obtain ⟨historyUsed,after,historyRun,historyBound,historyOutput⟩ := history_exec (family input) saved
  have relayOut := relay_exec after saved
  rw [historyOutput] at relayOut
  have last := SourceNativeEnvelopeOutput.block_exec (SourceHistoryRaw.answer (family input)) saved
  have checked := Exec.seq first (Exec.seq capture (Exec.seq relayIn
    (Exec.seq historyRun (Exec.seq relayOut last))))
  refine ⟨SourceNativeSystemInput.fuel input +
    (1 + (64 + (historyUsed + (64 + SourceNativeEnvelopeOutput.fuel
      (SourceHistoryRaw.answer (family input)) saved)))) ,?_,?_⟩
  · exact checked
  · have firstBound := SourceNativeSystemInput.fuel_bound input
    have firstFuel := SourceNativeSystemInput.sourceFuel_eval input.length
    have historyFuel := SourceHistoryRaw.sourceFuel_eval (family input).length
    have historyMono := NatPolynomial.eval_mono SourceHistoryRaw.sourceFuel (family_bound input)
    have lastBound := SourceNativeEnvelopeOutput.fuel_bound (SourceHistoryRaw.answer (family input)) saved
    have savedBound := dimension_bound input
    rw [costPolynomial_eval]
    dsimp only [saved] at *
    omega

theorem result_output (input : BitString) : (result input).get 8 = answer input :=
  SourceNativeEnvelopeOutput.result_output _ _

theorem canonical_answer {c : Nat} (D : NativeSparseSystem.System c) :
    answer (natural c ++ (NativeSystemCodec.systemCodec c).encode D) =
      SourceEncoding.encodeNativePacket (.system c D) := by
  have parsed : SourceNativeSystemParse.result (natural c ++ (NativeSystemCodec.systemCodec c).encode D) =
      SourceNativeSystemParse.canonical D [] := by
    simpa only [List.append_nil] using SourceNativeSystemParse.canonical_result D []
  rw [answer,family,SourceNativeSystemInput.canonical_answer,
    ← SourceNativeEncoding.family_packet,SourceHistoryRaw.answer_canonical,
    dimension,parsed,SourceNativeSystemParse.canonical_dimension]
  change true :: true :: ((List.replicate (2 * c) true).reverse ++
      false :: SourceEncoding.dataCodec.encode (SourceEncoding.toData
        (SourceChain.reduce (2 * c) (NativeSource.family D)))) =
    [true,true] ++ natural (2 * c) ++ SourceEncoding.dataCodec.encode
      (SourceEncoding.toData (SourceChain.reduce (2 * c) (NativeSource.family D)))
  simp only [List.reverse_replicate,natural,List.cons_append,List.nil_append,
    List.append_assoc]

end PNP.Concrete.ResidualReduction.SourceNativeHistoryBridge
