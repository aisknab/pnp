import PNP.Concrete.NativeNormalization.NativeSystemCodec

namespace PNP.Concrete.NativeNormalization.NativeOutputPacket

open PNP.Concrete NativeBitCodec NativeSystemCodec NativeSparseSystem

/-- Finite transport data. Recovery is deliberately not serialized as a function. -/
inductive Packet where
  | malformed
  | model (assignment : BitString)
  | system (rows : Nat) (data : System rows)
deriving Repr

def encode : Packet → BitString
  | .malformed => [false,false,false]
  | .model a => [false,false,true]++(listCodec bitCodec).encode a
  | .system c D => [false,true,false]++natural c++(systemCodec c).encode D

def parse : BitString → Option (Packet × BitString)
  | false::false::false::rest => some (.malformed,rest)
  | false::false::true::rest =>
      match (listCodec bitCodec).parse rest with
      | none => none
      | some (a,suffix) => some (.model a,suffix)
  | false::true::false::rest =>
      match BitString.decodeLength rest with
      | none => none
      | some (c,afterCount) =>
          match (systemCodec c).parse afterCount with
          | none => none
          | some (D,suffix) => some (.system c D,suffix)
  | _ => none

theorem parse_encode (p : Packet) (suffix : BitString) :
    parse (encode p++suffix) = some (p,suffix) := by
  cases p with
  | malformed => rfl
  | model a =>
      simp only [encode,List.cons_append,List.nil_append,parse,
        (listCodec bitCodec).roundtrip]
  | system c D =>
      simp only [encode,List.cons_append,List.nil_append,List.append_assoc,parse,
        natural_roundtrip,(systemCodec c).roundtrip]

theorem parse_sound (bits : BitString) (p : Packet) (suffix : BitString)
    (h : parse bits = some (p,suffix)) : encode p++suffix = bits := by
  cases bits with
  | nil => cases h
  | cons version tail =>
      cases version with
      | true => cases h
      | false =>
          cases tail with
          | nil => cases h
          | cons kind rest =>
              cases rest with
              | nil => cases kind <;> cases h
              | cons subtype payload =>
                  cases kind with
                  | false =>
                      cases subtype with
                      | false => cases h; rfl
                      | true =>
                          cases hp : (listCodec bitCodec).parse payload with
                          | none => simp only [parse,hp] at h; cases h
                          | some value =>
                              rcases value with ⟨a,remaining⟩
                              simp only [parse,hp] at h
                              cases h
                              simpa only [encode,List.cons_append,List.nil_append] using
                                congrArg (fun tail => false::false::true::tail)
                                  ((listCodec bitCodec).sound payload a suffix hp)
                  | true =>
                      cases subtype with
                      | true => cases h
                      | false =>
                          cases hc : BitString.decodeLength payload with
                          | none => simp only [parse,hc] at h; cases h
                          | some count =>
                              rcases count with ⟨c,afterCount⟩
                              cases hd : (systemCodec c).parse afterCount with
                              | none => simp only [parse,hc,hd] at h; cases h
                              | some value =>
                                  rcases value with ⟨D,remaining⟩
                                  simp only [parse,hc,hd] at h
                                  cases h
                                  have inner : natural c++((systemCodec c).encode D++suffix) = payload := by
                                    rw [(systemCodec c).sound afterCount D suffix hd]
                                    exact natural_sound payload c afterCount hc
                                  simpa only [encode,List.cons_append,List.nil_append,List.append_assoc] using
                                    congrArg (fun tail => false::true::false::tail) inner

def codec : Codec Packet := ⟨encode,parse,parse_encode,parse_sound⟩

theorem roundtrip (p : Packet) : codec.decode (encode p) = some p :=
  decode_encode codec p

theorem canonical (bits : BitString) (p : Packet) :
    codec.decode bits = some p ↔ encode p = bits :=
  decode_eq_some_iff codec bits p

theorem injective : Function.Injective encode := encode_injective codec

theorem reject_trailing (p : Packet) (extra : BitString) (nonempty : extra ≠ []) :
    codec.decode (encode p++extra) = none := by
  simp only [Codec.decode,codec,parse_encode]
  cases extra with
  | nil => exact False.elim (nonempty rfl)
  | cons x xs => rfl

theorem encodeSeq_bits (a : BitString) : encodeSeq bitCodec.encode a = a := by
  induction a with
  | nil => rfl
  | cons bit rest ih =>
      change bit::encodeSeq bitCodec.encode rest = bit::rest
      exact congrArg (List.cons bit) ih

/-- Model framing is byte-identical to the existing concrete bitstring frame. -/
theorem model_frame (a : BitString) :
    encode (.model a) = [false,false,true]++BitString.frame a := by
  simp only [encode,listCodec,encodeSeq_bits,natural,BitString.frame,
    List.append_assoc,List.cons_append,List.nil_append]

theorem model_length (a : BitString) : (encode (.model a)).length = 2*a.length+4 := by
  rw [model_frame]
  have h := BitString.size_frame a
  change (BitString.frame a).length = _ at h
  simp only [List.length_append,List.length_cons,List.length_nil,h]
  omega

def packetBound (c : Nat) : Nat := c+systemBound c+4

theorem system_length_bound (D : System c) (bounds : NativeFrontend.SparseBounds D) :
    (encode (.system c D)).length ≤ packetBound c := by
  have h := NativeSystemCodec.system_length_bound D bounds
  simp only [encode,List.length_append,List.length_cons,List.length_nil,natural_length]
  unfold packetBound
  omega

theorem packetBound_mono (a b : Nat) (h : a ≤ b) : packetBound a ≤ packetBound b := by
  have hb := systemBound_mono a b h
  unfold packetBound
  omega


end PNP.Concrete.NativeNormalization.NativeOutputPacket
