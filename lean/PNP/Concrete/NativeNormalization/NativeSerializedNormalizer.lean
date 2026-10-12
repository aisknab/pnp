import PNP.Concrete.NativeNormalization.NativeOutputPacket

namespace PNP.Concrete.NativeNormalization.NativeSerializedNormalizer

open PNP.Concrete NativeBitCodec NativeSystemCodec NativeOutputPacket
open NativeSparseSystem MeasuredReach

def ofResult : MeasuredSharedNormalizer.Result → Packet
  | .malformed => .malformed
  | .success (.model a) => .model a
  | .success (.system c D _) => .system c D

def packet (bits : BitString) : Packet := ofResult (MeasuredSharedNormalizer.convert bits).value

/-- Finite output bytes, without a function closure. Serialization execution cost
still requires its own measured and concrete-machine refinement. -/
def serialize (bits : BitString) : BitString := encode (packet bits)

def check : Packet → BitString → Bool
  | .malformed,_ => false
  | .model _,_ => true
  | .system c D,a => decide (a.length = 2*c) && D.check (MeasuredBits.rowValues c a)

theorem check_system_iff (D : System c) (a : BitString) :
    check (.system c D) a = true ↔
      a.length = 2*c ∧ D.Satisfied (MeasuredBits.rowValues c a) := by
  simp only [check,Bool.and_eq_true,decide_eq_true_eq,System.check_iff]

theorem decoded_sat_iff (bits : BitString) (F : CNFFormula)
    (decoded : decodeEncodedCNF bits = some F) : CNFSAT bits ↔ F.Satisfiable := by
  constructor
  · rintro ⟨G,hG,hSat⟩
    have same : G = F := Option.some.inj (hG.symm.trans decoded)
    subst G
    exact hSat
  · intro h
    exact ⟨F,decoded,h⟩

theorem ofResult_check_iff (bits : BitString) (r : MeasuredSharedNormalizer.Result)
    (correct : MeasuredSharedNormalizer.Correct bits r) :
    (∃ a, check (ofResult r) a = true) ↔ CNFSAT bits := by
  cases r with
  | malformed =>
      have decoded : decodeEncodedCNF bits = none := correct
      constructor
      · rintro ⟨a,h⟩
        cases h
      · rintro ⟨F,hF,_⟩
        rw [decoded] at hF
        cases hF
  | success result =>
      obtain ⟨F,decoded,h⟩ := correct
      have source := decoded_sat_iff bits F decoded
      cases result with
      | model a =>
          constructor
          · intro _
            exact source.mpr ⟨a,h⟩
          · intro _
            exact ⟨[],rfl⟩
      | system c D liftModel =>
          simpa only [ofResult,check_system_iff] using (source.trans h.1).symm

theorem packet_check_iff (bits : BitString) :
    (∃ a, check (packet bits) a = true) ↔ CNFSAT bits :=
  ofResult_check_iff bits _ (MeasuredSharedNormalizer.convert_correct bits)

def Bounded (m : Nat) : Packet → Prop
  | .malformed => True
  | .model a => a.length ≤ m
  | .system c D => c ≤ 15*m+6 ∧ NativeFrontend.SparseBounds D

theorem ofResult_bounded (bits : BitString) (r : MeasuredSharedNormalizer.Result)
    (correct : MeasuredSharedNormalizer.Correct bits r) :
    Bounded bits.length (ofResult r) := by
  cases r with
  | malformed => trivial
  | success result =>
      obtain ⟨F,decoded,h⟩ := correct
      cases result with
      | model a =>
          have size := CNFCore.decoded_width_bound bits F decoded
          have width : a.length = F.variableCount := h.1
          change a.length ≤ bits.length
          omega
      | system c D liftModel =>
          obtain ⟨_,_,rows,bounds,_⟩ := h
          have sizes := MeasuredFrontendCost.frontend_encoded_counts bits F decoded
          have kept : (CNFCore.positions (NativeTseitin.frontend F)).length ≤
              (NativeTseitin.frontend F).clauses.length := by
            simpa only [CNFCore.positions,List.length_finRange] using
              List.length_filter_le (CNFCore.kept (NativeTseitin.frontend F))
                (List.finRange (NativeTseitin.frontend F).clauses.length)
          exact ⟨by omega,bounds⟩

theorem packet_bounded (bits : BitString) : Bounded bits.length (packet bits) :=
  ofResult_bounded bits _ (MeasuredSharedNormalizer.convert_correct bits)

def outputPolynomial : NatPolynomial :=
  let c : NatPolynomial := .add (.mul (.constant 15) .variable) (.constant 6)
  let d : NatPolynomial := .add c (.constant 2)
  let b : NatPolynomial := .add (.mul d (.constant 3)) (.constant 1)
  let a : NatPolynomial := .add (.mul (.add (.mul d (.constant 8)) (.constant 1))
    (.mul (.constant 2) c)) (.constant 1)
  let e : NatPolynomial := .add (.mul (.add (.mul d (.constant 6)) (.constant 2)) c) (.constant 1)
  let system : NatPolynomial := .add (.add b a) e
  let full : NatPolynomial := .add (.add c system) (.constant 4)
  .add full (.add (.mul (.constant 2) .variable) (.constant 4))

theorem outputPolynomial_eval (m : Nat) :
    outputPolynomial.eval m = packetBound (15*m+6)+(2*m+4) := rfl

theorem bounded_encode_length (m : Nat) (p : Packet) (h : Bounded m p) :
    (encode p).length ≤ outputPolynomial.eval m := by
  rw [outputPolynomial_eval]
  cases p with
  | malformed => change 3 ≤ _; omega
  | model a =>
      have bound : a.length ≤ m := h
      rw [model_length]
      omega
  | system c D =>
      obtain ⟨rows,bounds⟩ := h
      have encoded := NativeOutputPacket.system_length_bound D bounds
      have mono := packetBound_mono c (15*m+6) rows
      omega

theorem serialize_length (bits : BitString) :
    (serialize bits).length ≤ outputPolynomial.eval bits.length :=
  bounded_encode_length bits.length _ (packet_bounded bits)

theorem decode_serialize (bits : BitString) : codec.decode (serialize bits) = some (packet bits) :=
  roundtrip (packet bits)

def checkEncoded (output witness : BitString) : Bool :=
  match codec.decode output with
  | none => false
  | some p => check p witness

theorem checkEncoded_serialize (bits a : BitString) :
    checkEncoded (serialize bits) a = check (packet bits) a := by
  simp only [checkEncoded,decode_serialize]

/-- Exact finite-language translation, not a polynomial-time reduction until
serialization and concrete-machine execution have also been proved. -/
theorem encoded_language_iff (bits : BitString) :
    (∃ a, checkEncoded (serialize bits) a = true) ↔ CNFSAT bits := by
  simp only [checkEncoded_serialize]
  exact packet_check_iff bits

/-- This proves the existence of a short certificate, not a way to find one. -/
theorem bounded_certificate (bits : BitString) (satisfiable : CNFSAT bits) :
    ∃ a, a.length ≤ 30*bits.length+12 ∧ checkEncoded (serialize bits) a = true := by
  obtain ⟨a,ha⟩ := (packet_check_iff bits).mpr satisfiable
  have bound := packet_bounded bits
  cases hp : packet bits with
  | malformed =>
      rw [hp] at ha
      cases ha
  | model assignment =>
      refine ⟨[],by simp,?_⟩
      rw [checkEncoded_serialize,hp]
      rfl
  | system c D =>
      rw [hp] at ha bound
      obtain ⟨width,_⟩ := (check_system_iff D a).mp ha
      refine ⟨a,by have rows := bound.1; omega,?_⟩
      rw [checkEncoded_serialize,hp]
      exact ha


end PNP.Concrete.NativeNormalization.NativeSerializedNormalizer
