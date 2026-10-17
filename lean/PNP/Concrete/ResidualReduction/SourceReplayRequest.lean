import PNP.Concrete.ResidualReduction.SourceReplayBlob

/-! Canonical external request for whole-history witness replay. The request
contains only a direction, original dimension, actual serialized history and
actual witness bytes. It supplies no parsed objects or correctness authority. -/

namespace PNP.Concrete.ResidualReduction.SourceReplayRequest
open PNP.Concrete PNP.Concrete.NativeNormalization.NativeBitCodec

structure Request where
  recover : Bool
  dimension : Nat
  data : BitString
  witness : BitString

def codec : Codec Request :=
  mappedCodec (pairCodec bitCodec (pairCodec natCodec
    (pairCodec (listCodec bitCodec) (listCodec bitCodec))))
    (fun x => ⟨x.1,x.2.1,x.2.2.1,x.2.2.2⟩)
    (fun r => (r.recover,r.dimension,r.data,r.witness))
    (by intro r; cases r; rfl)
    (by rintro ⟨b,n,d,w⟩; rfl)

def first (tail : BitString) : BitString := (MatrixStrictHeader.scan tail).rest
def second (tail : BitString) : BitString := SourceReplayBlob.rest (first tail)
def suffix (tail : BitString) : BitString := SourceReplayBlob.rest (second tail)
def scanned (mode : Bool) (tail : BitString) : Request :=
  ⟨mode,(MatrixStrictHeader.scan tail).count,SourceReplayBlob.bytes (first tail),SourceReplayBlob.bytes (second tail)⟩
def valid (tail : BitString) : Bool :=
  (MatrixStrictHeader.scan tail).terminated && SourceReplayBlob.valid (first tail) && SourceReplayBlob.valid (second tail)
def parse : BitString → Option (Request × BitString)
  | [] => none
  | mode :: tail => if valid tail then some (scanned mode tail,suffix tail) else none

theorem codec_parse (input : BitString) : codec.parse input = parse input := by
  cases input with
  | nil => rfl
  | cons mode tail =>
    have bitParsed : bitCodec.parse (mode :: tail) = some (mode,tail) := rfl
    cases h : (MatrixStrictHeader.scan tail).terminated <;>
      cases a : SourceReplayBlob.valid (first tail) <;>
      cases b : SourceReplayBlob.valid (second tail) <;>
      simp only [codec,mappedCodec,pairCodec,bitParsed,natCodec,MatrixStrictHeader.scan_parse,
        SourceReplayBlob.parse_eq,parse,valid,scanned,suffix,second,first,h,
        show SourceReplayBlob.valid (MatrixStrictHeader.scan tail).rest = _ from a,
        show SourceReplayBlob.valid (SourceReplayBlob.rest (MatrixStrictHeader.scan tail).rest) = _ from b,
        Bool.false_eq_true,Bool.and_false,Bool.and_true,
        ↓reduceIte,Option.map_none,Option.map_some]

def accepted (input : BitString) : Option Request :=
  match parse input with
  | some (r,[]) => some r
  | _ => none

theorem accepted_eq (input : BitString) : accepted input = codec.decode input := by
  unfold accepted Codec.decode
  rw [codec_parse]
  cases parse input with
  | none => rfl
  | some pair => rcases pair with ⟨r,tail⟩; cases tail <;> rfl

theorem roundtrip (r : Request) : accepted (codec.encode r) = some r := by
  rw [accepted_eq,decode_encode]

theorem first_bound (tail : BitString) : (first tail).length ≤ tail.length := by
  have h := MatrixStrictHeader.scan_size tail
  unfold first
  omega
theorem second_bound (tail : BitString) : (second tail).length ≤ tail.length :=
  Nat.le_trans (SourceReplayBlob.rest_bound (first tail)) (first_bound tail)
theorem suffix_bound (tail : BitString) : (suffix tail).length ≤ tail.length :=
  Nat.le_trans (SourceReplayBlob.rest_bound (second tail)) (second_bound tail)

def evaluate (r : Request) : Option BitString :=
  if r.recover then SourceEncoding.recoverBytes r.dimension r.data r.witness
  else SourceEncoding.projectBytes r.dimension r.data r.witness
def answer (input : BitString) : Option BitString := (codec.decode input).bind evaluate

theorem answer_canonical (r : Request) : answer (codec.encode r) = evaluate r := by
  simp only [answer,decode_encode,Option.bind_some]

theorem malformed (input : BitString) (bad : codec.decode input = none) :
    answer input = none := by simp only [answer,bad,Option.bind_none]

end PNP.Concrete.ResidualReduction.SourceReplayRequest
