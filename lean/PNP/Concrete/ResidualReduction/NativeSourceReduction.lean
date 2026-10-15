import PNP.Concrete.ResidualReduction.NativeSourceSystem
import PNP.Concrete.ResidualReduction.SourceReductionChain
import PNP.Concrete.SerializedNormalizer

namespace PNP.Concrete.ResidualReduction.NativeSource
open PNP.Concrete.ResidualReduction.FactoredContraction
open PNP.Concrete PNP.Concrete.NativeNormalization

def reduceSystem {c : Nat} (D : NativeSparseSystem.System c) :
    SourceChain.Reduction (2*c) :=
  SourceChain.reduce (2*c) (family D)

def liftSystem {c : Nat} (D : NativeSparseSystem.System c)
    (z : Point (reduceSystem D).dimension) : NativeEquations.RowValues c :=
  pointRows ((reduceSystem D).lift z)

def projectSystem {c : Nat} (D : NativeSparseSystem.System c)
    (u : NativeEquations.RowValues c) : Point (reduceSystem D).dimension :=
  (reduceSystem D).project (sourcePoint u)

theorem reduced_model_iff {c : Nat} (D : NativeSparseSystem.System c)
    (z : Point (reduceSystem D).dimension) :
    models (reduceSystem D).core z = true ↔ D.Satisfied (liftSystem D z) := by
  unfold reduceSystem liftSystem
  rw [SourceChain.reduce_model_map]
  exact family_satisfied D _

theorem project_lift_system {c : Nat} (D : NativeSparseSystem.System c)
    (z : Point (reduceSystem D).dimension) :
    projectSystem D (liftSystem D z) = z := by
  unfold projectSystem liftSystem
  rw [sourcePoint_pointRows]
  exact SourceChain.reduce_parameter_roundtrip _ _ _

theorem lift_project_system {c : Nat} (D : NativeSparseSystem.System c)
    (u : NativeEquations.RowValues c) (hu : D.Satisfied u) :
    liftSystem D (projectSystem D u) = u := by
  unfold liftSystem projectSystem reduceSystem
  rw [SourceChain.reduce_source_roundtrip _ _ _ ((family_sourcePoint D u).mpr hu)]
  exact pointRows_sourcePoint u

theorem reduced_row_count {c : Nat} (D : NativeSparseSystem.System c) :
    (reduceSystem D).core.length = 1+D.e.length+D.a.length := by
  unfold reduceSystem
  rw [SourceChain.reduce_row_count]
  exact family_row_count D

theorem reduced_dimension_accounting {c : Nat} (D : NativeSparseSystem.System c) :
    (reduceSystem D).history.length+(reduceSystem D).dimension = 2*c :=
  SourceChain.reduce_dimension_accounting _ _

theorem reduced_trace_linked {c : Nat} (D : NativeSparseSystem.System c) :
    SourceChain.Linked (family D) (reduceSystem D).history (reduceSystem D).core :=
  SourceChain.reduce_trace_linked _ _

/-- The complete residual model set is equivalent to the original encoded source. -/
theorem reduced_source_iff (input : BitString) (c : Nat)
    (D : NativeSparseSystem.System c)
    (decoded : NativeOutputPacket.codec.decode (SerializedNormalizer.output input) =
      some (.system c D)) :
    (∃ z, models (reduceSystem D).core z = true) ↔ CNFSAT input := by
  exact (SourceChain.reduce_satisfiable_iff (2*c) (family D)).symm.trans
    ((family_certificate_iff D).trans
      (SerializedNormalizer.residual_system_iff input c D decoded))

theorem decoded_check (bytes certificate : BitString) (packet : NativeOutputPacket.Packet)
    (decoded : NativeOutputPacket.codec.decode bytes = some packet) :
    NativeSerializedNormalizer.checkEncoded bytes certificate =
      NativeSerializedNormalizer.check packet certificate := by
  simp only [NativeSerializedNormalizer.checkEncoded,decoded]

/-- Construct an actual accepted public certificate from a remaining core model. -/
theorem lifted_certificate (input : BitString) (c : Nat)
    (D : NativeSparseSystem.System c)
    (decoded : NativeOutputPacket.codec.decode (SerializedNormalizer.output input) =
      some (.system c D))
    (z : Point (reduceSystem D).dimension)
    (hz : models (reduceSystem D).core z = true) :
    (pointBytes ((reduceSystem D).lift z)).length = 2*c ∧
      NativeSerializedNormalizer.checkEncoded (SerializedNormalizer.output input)
        (pointBytes ((reduceSystem D).lift z)) = true := by
  have hs : D.Satisfied
      (MeasuredBits.rowValues c (pointBytes ((reduceSystem D).lift z))) := by
    rw [rowValues_pointBytes]
    exact (reduced_model_iff D z).mp hz
  have accepted := (NativeSerializedNormalizer.check_system_iff D _).mpr
    ⟨pointBytes_length ((reduceSystem D).lift z),hs⟩
  exact ⟨pointBytes_length _,(decoded_check _ _ _ decoded).trans accepted⟩

/-- A step-count bound only: this is not a complete encoded runtime theorem. -/
theorem source_step_bound (input : BitString) (c : Nat)
    (D : NativeSparseSystem.System c)
    (decoded : NativeOutputPacket.codec.decode (SerializedNormalizer.output input) =
      some (.system c D)) :
    (reduceSystem D).history.length ≤ 30*input.length+12 := by
  have packet : NativeSerializedNormalizer.packet input = .system c D :=
    Option.some.inj ((SerializedNormalizer.decode_output input).symm.trans decoded)
  have bounds := NativeSerializedNormalizer.packet_bounded input
  rw [packet] at bounds
  have rows : c ≤ 15*input.length+6 := bounds.1
  have steps := reduced_dimension_accounting D
  omega

def packetVerdict : NativeOutputPacket.Packet → Option Bool
  | .malformed => some false
  | .model _ => some true
  | .system _ D => SourceChain.verdict (family D)

/-- Read the actual machine output. An unresolved nonzero core remains unknown. -/
def sourceVerdict (input : BitString) : Option Bool :=
  (NativeOutputPacket.codec.decode (SerializedNormalizer.output input)).bind packetVerdict

theorem sourceVerdict_packet (input : BitString) :
    sourceVerdict input = packetVerdict (NativeSerializedNormalizer.packet input) := by
  simp only [sourceVerdict,SerializedNormalizer.decode_output,Option.bind_some]

theorem packetVerdict_true_certificate (packet : NativeOutputPacket.Packet)
    (h : packetVerdict packet = some true) :
    ∃ certificate, NativeSerializedNormalizer.check packet certificate = true := by
  cases packet with
  | malformed => cases h
  | model assignment => exact ⟨[],rfl⟩
  | system c D =>
      obtain ⟨certificate,hc⟩ := (family_certificate_iff D).mp
        (SourceChain.verdict_true_sound (family D) h)
      exact ⟨certificate,(NativeSerializedNormalizer.check_system_iff D certificate).mpr hc⟩

theorem packetVerdict_false_no_certificate (packet : NativeOutputPacket.Packet)
    (h : packetVerdict packet = some false) :
    ¬ ∃ certificate, NativeSerializedNormalizer.check packet certificate = true := by
  cases packet with
  | malformed => rintro ⟨certificate,hc⟩; cases hc
  | model assignment => cases h
  | system c D =>
      rintro ⟨certificate,hc⟩
      have hs := (NativeSerializedNormalizer.check_system_iff D certificate).mp hc
      exact SourceChain.verdict_false_sound (family D) h
        ((family_certificate_iff D).mpr ⟨certificate,hs⟩)

theorem sourceVerdict_true_sound (input : BitString)
    (h : sourceVerdict input = some true) : CNFSAT input := by
  have hp := (sourceVerdict_packet input).symm.trans h
  exact (NativeSerializedNormalizer.packet_check_iff input).mp
    (packetVerdict_true_certificate _ hp)

theorem sourceVerdict_false_sound (input : BitString)
    (h : sourceVerdict input = some false) : ¬ CNFSAT input := by
  have hp := (sourceVerdict_packet input).symm.trans h
  intro sat
  exact packetVerdict_false_no_certificate _ hp
    ((NativeSerializedNormalizer.packet_check_iff input).mpr sat)

theorem decoded_verdict (bytes : BitString) (packet : NativeOutputPacket.Packet)
    (decoded : NativeOutputPacket.codec.decode bytes = some packet) :
    (NativeOutputPacket.codec.decode bytes).bind packetVerdict = packetVerdict packet := by
  simp only [decoded,Option.bind_some]

theorem systemVerdict_nonzero {c : Nat} (D : NativeSparseSystem.System c)
    (remaining : (reduceSystem D).dimension ≠ 0) :
    packetVerdict (.system c D) = none := by
  have unknown (n : Nat) (F : Family n) (hn : n ≠ 0) :
      SourceChain.zeroVerdict n F = none := by
    cases n with
    | zero => exact (hn rfl).elim
    | succ n => rfl
  exact unknown _ _ remaining

theorem sourceVerdict_unresolved (input : BitString) (c : Nat)
    (D : NativeSparseSystem.System c)
    (decoded : NativeOutputPacket.codec.decode (SerializedNormalizer.output input) =
      some (.system c D))
    (remaining : (reduceSystem D).dimension ≠ 0) :
    sourceVerdict input = none := by
  exact (decoded_verdict _ _ decoded).trans (systemVerdict_nonzero D remaining)

end PNP.Concrete.ResidualReduction.NativeSource
