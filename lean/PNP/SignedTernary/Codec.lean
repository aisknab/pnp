import PNP.Concrete.CNFDecoderGrammar
import PNP.SignedTernary.Network.GroundRows

namespace PNP.SignedTernary.Codec
open PNP.Concrete PNP.SignedTernary.Field PNP.SignedTernary.Linear PNP.SignedTernary.CNF

private theorem unaryLength (k : Nat) : (encodeUnaryTokens k).length = k+1 := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [encodeUnaryTokens,List.length_cons,ih]

private theorem literalLength (l : CNFLiteral) : 2 ≤ (encodeLiteralTokens l).length := by
  simp only [encodeLiteralTokens,List.length_cons,unaryLength]
  omega

private theorem literalsLength (c : List CNFLiteral) :
    2*c.length ≤ (encodeLiteralListTokens c).length := by
  induction c with
  | nil => exact Nat.le_refl _
  | cons l c ih =>
    have hh := literalLength l
    simp only [encodeLiteralListTokens,List.length_append,List.length_cons]
    omega

private theorem clausesLength (cs : List (List CNFLiteral)) :
    2*occurrences cs + 2*cs.length ≤ (encodeClauseListTokens cs).length := by
  induction cs with
  | nil => exact Nat.le_refl _
  | cons c cs ih =>
    have hc := literalsLength c
    simp only [encodeClauseListTokens,List.length_append,encodeClauseTokens,
      List.length_cons,List.length_nil,occurrences]
    omega

/-- Lower bound on the REAL raw bytes-as-bits, not on a decoded record supplied by a caller. -/
theorem admitted_lower (raw : BitString) (F : CNFFormula)
    (h : decodeEncodedCNF raw = some F) :
    2*F.variableCount + 4*occurrences F.clauses + 4*F.clauses.length + 5 ≤ raw.length := by
  have hc := clausesLength F.clauses
  rw [← CNFRegisterDecoder.encoded_of_decode raw F h,encodeCNF,List.length_append,
    encodeTokenPairs_length]
  simp only [encodeCNFTokens,List.length_append,List.length_cons,List.length_nil,unaryLength]
  omega

/-- Matrix dimension from the two dimensions of PNP.SignedTernary.Network.sourceMatrix, including the real
    contradictory pair of forms on a malformed word. -/
def parsedDimension (p : Option CNFFormula) : Nat :=
  5+4*(3*(parsedForms p).length)+(PNP.SignedTernary.Network.parsedSites p).length

def dimension (raw : BitString) : Nat := parsedDimension (decodeEncodedCNF raw)

theorem dimension_actual (raw : BitString) : dimension raw =
    5+4*(3*(rawForms raw).length)+(PNP.SignedTernary.Network.parsedSites (decodeEncodedCNF raw)).length := rfl

theorem dimension_valid (raw : BitString) (F : CNFFormula)
    (h : decodeEncodedCNF raw = some F) :
    dimension raw = 6+F.variableCount+51*occurrences F.clauses+24*F.clauses.length := by
  rw [dimension,h]
  change 5+4*(3*(forms F).length)+(portSites F).length = _
  rw [portSites_length,form_count]
  omega

theorem dimension_malformed (raw : BitString) (h : decodeEncodedCNF raw = none) :
    dimension raw = 30 := by
  rw [dimension,h]
  rfl

theorem dimension_pos (raw : BitString) : 0 < dimension raw := by
  unfold dimension parsedDimension
  omega

theorem dimension_valid_bound (raw : BitString) (F : CNFFormula)
    (h : decodeEncodedCNF raw = some F) : dimension raw ≤ 13*raw.length := by
  have hlen := admitted_lower raw F h
  rw [dimension_valid raw F h]
  omega

theorem dimension_bound (raw : BitString) : dimension raw ≤ 13*raw.length+30 := by
  cases h : decodeEncodedCNF raw with
  | none => rw [dimension_malformed raw h]; omega
  | some F => have hv := dimension_valid_bound raw F h; omega

def tag : F3 → BitString
  | .z => [false,false]
  | .o => [false,true]
  | .t => [true,false]

def readTag : Bool → Bool → Option F3
  | false,false => some .z
  | false,true => some .o
  | true,false => some .t
  | true,true => none

private theorem tag_length (a : F3) : (tag a).length = 2 := by cases a <;> rfl

private theorem tag_sound (p q : Bool) (a : F3) (h : readTag p q = some a) :
    tag a = [p,q] := by
  cases p <;> cases q <;> cases a <;> first | rfl | cases h

def header : Nat → BitString → BitString
  | 0, tail => false :: tail
  | n+1, tail => true :: header n tail

def readHeader : BitString → Option (Nat × BitString)
  | [] => none
  | false :: tail => some (0,tail)
  | true :: tail =>
    match readHeader tail with
    | none => none
    | some (n,data) => some (n+1,data)

theorem header_spec (n : Nat) (tail : BitString) :
    header n tail = List.replicate n true ++ false :: tail := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [header,List.replicate_succ,List.cons_append,ih]

private theorem header_read (n : Nat) (tail : BitString) :
    readHeader (header n tail) = some (n,tail) := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [header,readHeader,ih]

private theorem header_sound : ∀ (bs : BitString) (n : Nat) (tail : BitString),
    readHeader bs = some (n,tail) → header n tail = bs
  | [], _, _, h => by cases h
  | false::bs, _, _, h => by cases h; rfl
  | true::bs, n, tail, h => by
    cases hr : readHeader bs with
    | none => simp only [readHeader,hr] at h; cases h
    | some nt =>
      rcases nt with ⟨k,r⟩
      have back := header_sound bs k r hr
      simp only [readHeader,hr] at h
      cases h
      exact congrArg (List.cons true) back

def vecBits : (n : Nat) → Vec n → BitString
  | 0, _ => []
  | n+1, v => tag v.1 ++ vecBits n v.2

def rowsBits (n : Nat) : (m : Nat) → Rows n m → BitString
  | 0, _ => []
  | m+1, A => vecBits n A.1 ++ rowsBits n m A.2

def readVec : (n : Nat) → BitString → Option (Vec n × BitString)
  | 0, bs => some ((),bs)
  | n+1, p::q::bs =>
      match readTag p q with
      | none => none
      | some a =>
        match readVec n bs with
        | none => none
        | some (v,r) => some ((a,v),r)
  | _+1, _ => none

def readRows (n : Nat) : (m : Nat) → BitString → Option (Rows n m × BitString)
  | 0, bs => some ((),bs)
  | m+1, bs =>
    match readVec n bs with
    | none => none
    | some (v,r) =>
      match readRows n m r with
      | none => none
      | some (A,t) => some ((v,A),t)

theorem vecBits_length (n : Nat) (v : Vec n) : (vecBits n v).length = 2*n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [vecBits,List.length_append,tag_length,ih]; omega

theorem rowsBits_length (n m : Nat) (A : Rows n m) :
    (rowsBits n m A).length = 2*(n*m) := by
  induction m with
  | zero => rfl
  | succ m ih =>
    simp only [rowsBits,List.length_append,vecBits_length,ih,Nat.mul_succ]
    omega

theorem readVec_bits (n : Nat) (v : Vec n) (tail : BitString) :
    readVec n (vecBits n v ++ tail) = some (v,tail) := by
  induction n with
  | zero => cases v; rfl
  | succ n ih =>
    rcases v with ⟨a,v⟩
    cases a <;> simp only [vecBits,tag,List.cons_append,List.nil_append,
      readVec,readTag,ih]

theorem readRows_bits (n m : Nat) (A : Rows n m) (tail : BitString) :
    readRows n m (rowsBits n m A ++ tail) = some (A,tail) := by
  induction m with
  | zero => cases A; rfl
  | succ m ih =>
    rcases A with ⟨v,A⟩
    simp only [rowsBits,List.append_assoc,readRows,readVec_bits,ih]

theorem readVec_sound : ∀ (n : Nat) (bs : BitString) (v : Vec n) (tail : BitString),
    readVec n bs = some (v,tail) → vecBits n v ++ tail = bs
  | 0, _, v, _, h => by cases v; cases h; rfl
  | _+1, [], _, _, h => by cases h
  | _+1, [_], _, _, h => by cases h
  | n+1, p::q::bs, v, tail, h => by
    cases ht : readTag p q with
    | none => simp only [readVec,ht] at h; cases h
    | some a =>
      cases hr : readVec n bs with
      | none => simp only [readVec,ht,hr] at h; cases h
      | some vr =>
        rcases vr with ⟨v',r⟩
        have back := readVec_sound n bs v' r hr
        simp only [readVec,ht,hr] at h
        cases h
        rw [vecBits,List.append_assoc,back,tag_sound p q a ht]
        rfl

theorem readRows_sound (n : Nat) : ∀ (m : Nat) (bs : BitString) (A : Rows n m) (tail : BitString),
    readRows n m bs = some (A,tail) → rowsBits n m A ++ tail = bs
  | 0, _, A, _, h => by cases A; cases h; rfl
  | m+1, bs, A, tail, h => by
    cases hv : readVec n bs with
    | none => simp only [readRows,hv] at h; cases h
    | some vr =>
      rcases vr with ⟨v,r⟩
      cases hm : readRows n m r with
      | none => simp only [readRows,hv,hm] at h; cases h
      | some ar =>
        rcases ar with ⟨A',t⟩
        have more := readRows_sound n m r A' t hm
        have head := readVec_sound n bs v r hv
        simp only [readRows,hv,hm] at h
        cases h
        rw [rowsBits,List.append_assoc,more,head]

abbrev Square := Sigma (fun n : Nat => Rows n n)

def pack (n : Nat) (A : Rows n n) : BitString := header n (rowsBits n n A)

def unpack (bytes : BitString) : Option Square :=
  match readHeader bytes with
  | some (n+1,payload) =>
    match readRows (n+1) (n+1) payload with
    | some (A,[]) => some ⟨n+1,A⟩
    | _ => none
  | _ => none

theorem unpack_pack (n : Nat) (A : Rows (n+1) (n+1)) :
    unpack (pack (n+1) A) = some ⟨n+1,A⟩ := by
  have hr := readRows_bits (n+1) (n+1) A []
  rw [List.append_nil] at hr
  simp only [unpack,pack,header_read,hr]

/-- Positive exact dimension, no missing/trailing pair, no invalid 11 tag: ANY success is
    the unique canonical row-major word for exactly the ordered typed F3 matrix returned. -/
theorem unpack_exact (bytes : BitString) (A : Square) :
    unpack bytes = some A ↔ 0 < A.1 ∧ pack A.1 A.2 = bytes := by
  constructor
  · intro h
    cases hh : readHeader bytes with
    | none => simp only [unpack,hh] at h; cases h
    | some np =>
      rcases np with ⟨n,payload⟩
      cases n with
      | zero => simp only [unpack,hh] at h; cases h
      | succ n =>
        cases hr : readRows (n+1) (n+1) payload with
        | none => simp only [unpack,hh,hr] at h; cases h
        | some atail =>
          rcases atail with ⟨m,tail⟩
          cases tail with
          | cons b t => simp only [unpack,hh,hr] at h; cases h
          | nil =>
            simp only [unpack,hh,hr] at h
            cases h
            have hd := readRows_sound (n+1) (n+1) payload m [] hr
            rw [List.append_nil] at hd
            exact ⟨Nat.zero_lt_succ n, (congrArg (header (n+1)) hd).trans
              (header_sound bytes (n+1) payload hh)⟩
  · rcases A with ⟨n,m⟩
    rintro ⟨hp,hb⟩
    cases n with
    | zero => exact (Nat.not_lt_zero _ hp).elim
    | succ n => rw [← hb]; exact unpack_pack n m

theorem reject_trailing (n : Nat) (A : Rows (n+1) (n+1)) (b : Bool) (tail : BitString) :
    unpack (pack (n+1) A ++ b::tail) = none := by
  have hh : ∀ (k : Nat) (data extra : BitString),
      header k data ++ extra = header k (data++extra) := by
    intro k data extra
    induction k with
    | zero => rfl
    | succ k ih => exact congrArg (List.cons true) ih
  simp only [pack,hh,unpack,header_read,readRows_bits]

theorem reject_bad_tag (n : Nat) (tail : BitString) :
    readVec (n+1) (true::true::tail) = none := rfl

theorem pack_length (n : Nat) (A : Rows n n) :
    (pack n A).length = n+1+2*(n*n) := by
  simp only [pack,header_spec,List.length_append,List.length_replicate,List.length_cons,
    rowsBits_length]
  omega

theorem raw_pack_recovers (raw : BitString) (A : Rows (dimension raw) (dimension raw)) :
    unpack (pack (dimension raw) A) = some ⟨dimension raw,A⟩ := by
  exact (unpack_exact _ _).2 ⟨dimension_pos raw,rfl⟩

/-- Actual emitted dense-square SIZE polynomial. The theorem quantifies every square with the
    source's real computed dimension, so no assumed physical entries, model, or row semantics
    enter a size assertion. Computing a reduction trace is a separate obligation. -/
theorem raw_pack_bound (raw : BitString) (A : Rows (dimension raw) (dimension raw)) :
    (pack (dimension raw) A).length ≤
      (13*raw.length+30)+1+2*((13*raw.length+30)*(13*raw.length+30)) := by
  have hw := dimension_bound raw
  have hs := Nat.mul_le_mul hw hw
  rw [pack_length]
  omega

end PNP.SignedTernary.Codec
