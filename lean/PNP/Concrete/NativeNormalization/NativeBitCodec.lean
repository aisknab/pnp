import PNP.Concrete.NativeNormalization.MeasuredSharedNormalizer

namespace PNP.Concrete.NativeNormalization.NativeBitCodec

open PNP.Concrete

/-- A prefix codec is both total on encoded values and canonical on every
accepted input. Its soundness field excludes alternative encodings. -/
structure Codec (α : Type) where
  encode : α → BitString
  parse : BitString → Option (α × BitString)
  roundtrip : ∀ a suffix, parse (encode a++suffix) = some (a,suffix)
  sound : ∀ bits a suffix, parse bits = some (a,suffix) → encode a++suffix = bits

def natural (n : Nat) : BitString := List.replicate n true++[false]

theorem natural_length (n : Nat) : (natural n).length = n+1 := by
  simp only [natural,List.length_append,List.length_replicate,List.length_cons,List.length_nil]

theorem natural_roundtrip (n : Nat) (suffix : BitString) :
    BitString.decodeLength (natural n++suffix) = some (n,suffix) := by
  simpa only [natural,List.append_assoc,List.cons_append,List.nil_append] using
    BitString.decodeLength_frameHeader n suffix

theorem natural_sound (bits : BitString) (n : Nat) (suffix : BitString)
    (h : BitString.decodeLength bits = some (n,suffix)) : natural n++suffix = bits := by
  induction bits generalizing n suffix with
  | nil => cases h
  | cons bit rest ih =>
      cases bit with
      | false => cases h; rfl
      | true =>
          cases hd : BitString.decodeLength rest with
          | none => simp only [BitString.decodeLength,hd] at h; cases h
          | some pair =>
              rcases pair with ⟨m,tail⟩
              simp only [BitString.decodeLength,hd,Option.some.injEq,Prod.mk.injEq] at h
              rcases h with ⟨rfl,rfl⟩
              simpa only [natural,List.replicate_succ,List.cons_append] using
                congrArg (List.cons true) (ih m tail hd)

def natCodec : Codec Nat :=
  ⟨natural,BitString.decodeLength,natural_roundtrip,natural_sound⟩

def parseBit : BitString → Option (Bool × BitString)
  | [] => none
  | b::rest => some (b,rest)

def bitCodec : Codec Bool where
  encode b := [b]
  parse := parseBit
  roundtrip := by intro b suffix; rfl
  sound := by
    intro bits b suffix h
    cases bits with
    | nil => cases h
    | cons a rest => cases h; rfl

def finCodec (n : Nat) : Codec (Fin n) where
  encode i := natural i.val
  parse bits :=
    match BitString.decodeLength bits with
    | none => none
    | some (i,rest) => if h : i < n then some (⟨i,h⟩,rest) else none
  roundtrip := by
    intro i suffix
    rw [natural_roundtrip]
    simp only [i.isLt,dif_pos]
  sound := by
    intro bits i suffix h
    cases hn : BitString.decodeLength bits with
    | none => simp only [hn] at h; cases h
    | some pair =>
        rcases pair with ⟨j,rest⟩
        by_cases hj : j < n
        · simp only [hn,hj,dif_pos,Option.some.injEq,Prod.mk.injEq] at h
          rcases h with ⟨rfl,rfl⟩
          exact natural_sound bits j rest hn
        · simp only [hn,hj] at h; cases h

def pairCodec (A : Codec α) (B : Codec β) : Codec (α × β) where
  encode value := A.encode value.1++B.encode value.2
  parse bits :=
    match A.parse bits with
    | none => none
    | some (a,rest) =>
        match B.parse rest with
        | none => none
        | some (b,suffix) => some ((a,b),suffix)
  roundtrip := by
    rintro ⟨a,b⟩ suffix
    simp only [List.append_assoc,A.roundtrip,B.roundtrip]
  sound := by
    intro bits value suffix h
    cases ha : A.parse bits with
    | none => simp only [ha] at h; cases h
    | some first =>
        rcases first with ⟨a,rest⟩
        cases hb : B.parse rest with
        | none => simp only [ha,hb] at h; cases h
        | some second =>
            rcases second with ⟨b,tail⟩
            simp only [ha,hb,Option.some.injEq,Prod.mk.injEq] at h
            rcases h with ⟨rfl,rfl⟩
            rw [List.append_assoc,B.sound rest b tail hb]
            exact A.sound bits a rest ha

def encodeSeq (encode : α → BitString) : List α → BitString
  | [] => []
  | a::rest => encode a++encodeSeq encode rest

def parseN (parse : BitString → Option (α × BitString)) :
    Nat → BitString → Option (List α × BitString)
  | 0,bits => some ([],bits)
  | n+1,bits =>
      match parse bits with
      | none => none
      | some (a,rest) =>
          match parseN parse n rest with
          | none => none
          | some (tail,suffix) => some (a::tail,suffix)

theorem parseN_roundtrip (C : Codec α) (xs : List α) (suffix : BitString) :
    parseN C.parse xs.length (encodeSeq C.encode xs++suffix) = some (xs,suffix) := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
      simp only [List.length_cons,encodeSeq,List.append_assoc,parseN,C.roundtrip,ih]

theorem parseN_sound (C : Codec α) (n : Nat) (bits : BitString)
    (xs : List α) (suffix : BitString)
    (h : parseN C.parse n bits = some (xs,suffix)) :
    xs.length = n ∧ encodeSeq C.encode xs++suffix = bits := by
  induction n generalizing bits xs suffix with
  | zero => cases h; exact ⟨rfl,rfl⟩
  | succ n ih =>
      cases ha : C.parse bits with
      | none => simp only [parseN,ha] at h; cases h
      | some first =>
          rcases first with ⟨a,rest⟩
          cases ht : parseN C.parse n rest with
          | none => simp only [parseN,ha,ht] at h; cases h
          | some second =>
              rcases second with ⟨tail,remaining⟩
              simp only [parseN,ha,ht,Option.some.injEq,Prod.mk.injEq] at h
              rcases h with ⟨rfl,rfl⟩
              obtain ⟨hlen,heq⟩ := ih rest tail remaining ht
              refine ⟨congrArg Nat.succ hlen,?_⟩
              simp only [encodeSeq,List.append_assoc,heq]
              exact C.sound bits a rest ha

def listCodec (C : Codec α) : Codec (List α) where
  encode xs := natural xs.length++encodeSeq C.encode xs
  parse bits :=
    match BitString.decodeLength bits with
    | none => none
    | some (n,rest) => parseN C.parse n rest
  roundtrip := by
    intro xs suffix
    simp only [List.append_assoc,natural_roundtrip,parseN_roundtrip]
  sound := by
    intro bits xs suffix h
    cases hn : BitString.decodeLength bits with
    | none => simp only [hn] at h; cases h
    | some first =>
        rcases first with ⟨n,rest⟩
        have hp : parseN C.parse n rest = some (xs,suffix) := by simpa only [hn] using h
        obtain ⟨hlen,heq⟩ := parseN_sound C n rest xs suffix hp
        rw [List.append_assoc,heq,hlen]
        exact natural_sound bits n rest hn

/-- Transport a codec across an actual data isomorphism, not an assumed validator. -/
def mappedCodec (C : Codec α) (forward : α → β) (backward : β → α)
    (fb : ∀ b, forward (backward b) = b)
    (bf : ∀ a, backward (forward a) = a) : Codec β where
  encode b := C.encode (backward b)
  parse bits := (C.parse bits).map (fun value => (forward value.1,value.2))
  roundtrip := by
    intro b suffix
    rw [C.roundtrip]
    simp only [Option.map_some,fb]
  sound := by
    intro bits b suffix h
    cases hp : C.parse bits with
    | none => simp only [hp,Option.map_none] at h; cases h
    | some value =>
        rcases value with ⟨a,rest⟩
        simp only [hp,Option.map_some,Option.some.injEq,Prod.mk.injEq] at h
        rcases h with ⟨rfl,rfl⟩
        rw [bf]
        exact C.sound bits a rest hp

def Codec.decode (C : Codec α) (bits : BitString) : Option α :=
  match C.parse bits with
  | some (a,[]) => some a
  | _ => none

theorem decode_encode (C : Codec α) (a : α) : C.decode (C.encode a) = some a := by
  have h := C.roundtrip a []
  rw [List.append_nil] at h
  simp only [Codec.decode,h]

theorem decode_eq_some_iff (C : Codec α) (bits : BitString) (a : α) :
    C.decode bits = some a ↔ C.encode a = bits := by
  constructor
  · intro h
    cases hp : C.parse bits with
    | none => simp only [Codec.decode,hp] at h; cases h
    | some value =>
        rcases value with ⟨b,rest⟩
        cases rest with
        | nil =>
            simp only [Codec.decode,hp,Option.some.injEq] at h
            subst b
            simpa only [List.append_nil] using C.sound bits a [] hp
        | cons x xs => simp only [Codec.decode,hp] at h; cases h
  · rintro rfl
    exact decode_encode C a

theorem encode_injective (C : Codec α) : Function.Injective C.encode := by
  intro a b h
  have hp := congrArg C.decode h
  rw [decode_encode,decode_encode] at hp
  exact Option.some.inj hp

theorem encodeSeq_length_bound (encode : α → BitString) (xs : List α) (K : Nat)
    (bounded : ∀ x ∈ xs, (encode x).length ≤ K) :
    (encodeSeq encode xs).length ≤ K*xs.length := by
  induction xs with
  | nil => exact Nat.le_refl _
  | cons x xs ih =>
      have hx := bounded x (by simp)
      have ht := ih (fun y hy => bounded y (by simp [hy]))
      simp only [encodeSeq,List.length_append,List.length_cons,Nat.mul_succ]
      omega

theorem list_length_bound (C : Codec α) (xs : List α) (K : Nat)
    (bounded : ∀ x ∈ xs, (C.encode x).length ≤ K) :
    ((listCodec C).encode xs).length ≤ (K+1)*xs.length+1 := by
  have h := encodeSeq_length_bound C.encode xs K bounded
  simp only [listCodec,List.length_append,natural_length,Nat.add_mul,Nat.one_mul]
  omega


end PNP.Concrete.NativeNormalization.NativeBitCodec
