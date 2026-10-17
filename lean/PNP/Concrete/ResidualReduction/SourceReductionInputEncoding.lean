import PNP.Concrete.ResidualReduction.SourceReductionReplay
import PNP.Concrete.ResidualReduction.NativeSourceSystem
import PNP.Concrete.NativeNormalization.NativeSerializedNormalizer

/-! Original-input encoded storage for the complete source reduction history.
This fixes the finite output specification for the runtime implementation. It
does not establish the running time needed to construct that output. -/

namespace PNP.Concrete.ResidualReduction.SourceEncoding
open PNP.Concrete.NativeNormalization
open PNP.Concrete.NativeNormalization.NativeBitCodec
open PNP.Concrete.ResidualReduction.FactoredContraction
open PNP.Concrete.ResidualReduction.SourceChain

theorem dataBound_mono {n N m M : Nat} (hn : n ≤ N) (hm : m ≤ M) :
    dataBound n m ≤ dataBound N M := by
  have rows := Nat.mul_le_mul (show 2 * n + 4 ≤ 2 * N + 4 by omega) hm
  have step : stepBound n m ≤ stepBound N M := by
    unfold stepBound
    omega
  have sources := Nat.mul_le_mul
    (show 2 * (n + 1) + 4 ≤ 2 * (N + 1) + 4 by omega) hm
  have record : recordBound n m ≤ recordBound N M := by
    unfold recordBound
    omega
  have history := Nat.mul_le_mul (Nat.add_le_add_right record 1) hn
  unfold dataBound
  omega

/-- Polynomial syntax for the already proved data bound, not a runtime budget. -/
def dataPolynomial (n m : NatPolynomial) : NatPolynomial :=
  let rows : NatPolynomial :=
    .add (.mul (.add (.mul (.constant 2) n) (.constant 4)) m) (.constant 1)
  let sources : NatPolynomial :=
    .add (.mul (.add (.mul (.constant 2) (.add n (.constant 1))) (.constant 4)) m)
      (.constant 1)
  let step : NatPolynomial := .add (.add (.add m (.add n (.constant 1))) n) rows
  let record : NatPolynomial := .add (.add (.add n (.constant 1)) sources) step
  .add (.add (.add n (.constant 1)) rows)
    (.add (.mul (.add record (.constant 1)) n) (.constant 1))

theorem dataPolynomial_eval (n m : NatPolynomial) (size : Nat) :
    (dataPolynomial n m).eval size = dataBound (n.eval size) (m.eval size) := rfl

/-- Distinct prefixes retain malformed, already solved, and residual outputs.
A residual also carries its original dimension for checked witness replay. -/
def encodeNativePacket : NativeOutputPacket.Packet → BitString
  | .malformed => [false]
  | .model a => [true, false] ++ (listCodec bitCodec).encode a
  | .system c D => [true, true] ++ natural (2 * c) ++
    dataCodec.encode (toData (reduce (2 * c) (NativeSource.family D)))

def sourceEncode (input : BitString) : BitString :=
  encodeNativePacket (NativeSerializedNormalizer.packet input)

def sourceOutputPolynomial : NatPolynomial :=
  let c : NatPolynomial := .add (.mul (.constant 15) .variable) (.constant 6)
  let n : NatPolynomial := .mul (.constant 2) c
  let m : NatPolynomial := .add (.constant 1) (.mul (.constant 3) c)
  .add (.add (.add (.constant 3) n) (dataPolynomial n m))
    (.add (.mul (.constant 2) .variable) (.constant 3))

theorem sourceOutputPolynomial_eval (size : Nat) :
    sourceOutputPolynomial.eval size =
      3 + 2 * (15 * size + 6) +
        dataBound (2 * (15 * size + 6)) (1 + 3 * (15 * size + 6)) + (2 * size + 3) := rfl

/-- All original input bitstrings are covered. The source normalizer supplies
the dimension and row bounds; the caller supplies no family or certificate. -/
theorem source_encoded_bound (input : BitString) :
    (sourceEncode input).length ≤ sourceOutputPolynomial.eval input.length := by
  have bounded := NativeSerializedNormalizer.packet_bounded input
  rw [sourceOutputPolynomial_eval]
  cases packet : NativeSerializedNormalizer.packet input with
  | malformed =>
    simp only [sourceEncode, packet, encodeNativePacket, List.length_cons, List.length_nil]
    omega
  | model a =>
    rw [packet] at bounded
    have size : a.length ≤ input.length := bounded
    have encoded := list_length_bound bitCodec a 1 (fun _ _ => Nat.le_refl 1)
    simp only [sourceEncode, packet, encodeNativePacket, List.length_append,
      List.length_cons, List.length_nil]
    omega
  | system c D =>
    rw [packet] at bounded
    obtain ⟨dimension, bounds⟩ := bounded
    obtain ⟨_, _, _, products, equations, _⟩ := bounds
    have rows : (NativeSource.family D).length ≤ 1 + 3 * (15 * input.length + 6) := by
      rw [NativeSource.family_row_count]
      omega
    have storage := Nat.le_trans (reduce_encoded_bound (2 * c) (NativeSource.family D))
      (dataBound_mono (show 2 * c ≤ 2 * (15 * input.length + 6) by omega) rows)
    simp only [sourceEncode, packet, encodeNativePacket, List.length_append,
      List.length_cons, List.length_nil, natural_length]
    omega

end PNP.Concrete.ResidualReduction.SourceEncoding
