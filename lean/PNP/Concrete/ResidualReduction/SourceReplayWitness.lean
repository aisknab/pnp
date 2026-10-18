import PNP.Concrete.ResidualReduction.SourceReplayDataMachine

/-! Exact-width witness decoding and its literal finite-register reader.
A point has no padding or ignored suffix. The EOF guard preserves failure of
the fixed-width reader, so a short field cannot become valid at end of input. -/

namespace PNP.Concrete.ResidualReduction.SourceReplayWitness
open PNP.Concrete PNP.Concrete.BitRegister PNP.Concrete.NormalizerBlocks
open PNP.Concrete.NormalizerBlocks.Occurrence (Registers)
open PNP.Concrete.NativeNormalization.NativeBitCodec
open PNP.Concrete.ResidualReduction.FactoredContraction

theorem decode_width (n : Nat) (input : BitString) (x : Point n)
    (parsed : (SourceEncoding.pointCodec n).decode input = some x) : input.length = n := by
  have bytes := (decode_eq_some_iff (SourceEncoding.pointCodec n) input x).mp parsed
  have length := congrArg List.length bytes
  rw [SourceEncoding.point_length] at length
  exact length.symm

theorem decode_complete (n : Nat) (input : BitString) (width : input.length = n) :
    ∃ x : Point n, (SourceEncoding.pointCodec n).decode input = some x := by
  have enough : n ≤ input.length := Nat.le_of_eq width.symm
  obtain ⟨x,parsed⟩ := SourceReplayFixed.valid_parse n input enough
  have empty : input.drop n = [] := by
    rw [← width,List.drop_length]
  rw [empty] at parsed
  exact ⟨x,by simp only [Codec.decode,parsed]⟩

theorem decode_iff_width (n : Nat) (input : BitString) :
    (∃ x : Point n, (SourceEncoding.pointCodec n).decode input = some x) ↔ input.length = n :=
  ⟨fun ⟨x,parsed⟩ => decode_width n input x parsed,decode_complete n input⟩

theorem decode_encoded {d n : Nat} (x : Point d) :
    (SourceEncoding.pointCodec n).decode ((SourceEncoding.pointCodec d).encode x) =
      if h : d = n then some (h ▸ x) else none := by
  by_cases same : d = n
  · subst n
    rw [dif_pos rfl,PNP.Concrete.NativeNormalization.NativeBitCodec.decode_encode]
  · rw [dif_neg same]
    cases parsed : (SourceEncoding.pointCodec n).decode ((SourceEncoding.pointCodec d).encode x) with
    | none => rfl
    | some y =>
      have width := decode_width n ((SourceEncoding.pointCodec d).encode x) y parsed
      rw [SourceEncoding.point_length] at width
      exact (same width).elim

private theorem drop_empty (n : Nat) (input : BitString) :
    (input.drop n).isEmpty = true ↔ input.length ≤ n := by
  cases cursor : input.drop n with
  | nil =>
    have length := congrArg List.length cursor
    simp only [List.length_drop,List.length_nil] at length
    constructor
    · intro _; omega
    · intro _; rfl
  | cons bit rest =>
    have length := congrArg List.length cursor
    simp only [List.length_drop,List.length_cons] at length
    constructor
    · intro bad; cases bad
    · intro bad; omega

def valid (n : Nat) (input : BitString) : Bool :=
  decide (n ≤ input.length) && (input.drop n).isEmpty

theorem valid_iff_width (n : Nat) (input : BitString) :
    valid n input = true ↔ input.length = n := by
  simp only [valid,Bool.and_eq_true,decide_eq_true_eq,drop_empty]
  constructor
  · rintro ⟨lower,upper⟩; omega
  · intro same; exact ⟨Nat.le_of_eq same.symm,Nat.le_of_eq same⟩

def finish (r : Registers) : Registers :=
  {r with mode := if r.input.isEmpty then r.mode else []}
def endCheck : Block 9 := .branch 0 .skip (.action (.clear 5)) (.action (.clear 5))
theorem endCheck_exec (r : Registers) : Exec endCheck r.store 2 (finish r).store := by
  have read : r.store.get 0 = r.input := rfl
  cases cursor : r.input with
  | nil =>
    have checked : Exec endCheck r.store 2 r.store := Exec.empty (read.trans cursor) (.skip _)
    simpa only [finish,Registers.store,cursor,List.isEmpty_nil,↓reduceIte] using checked
  | cons bit rest =>
    cases bit with
    | false =>
      have checked : Exec endCheck r.store 2 ({r with mode := []} : Registers).store :=
        Exec.zero (read.trans cursor) (.action _ _)
      simpa only [finish,Registers.store,cursor,List.isEmpty_cons,Bool.false_eq_true,↓reduceIte] using checked
    | true =>
      have checked : Exec endCheck r.store 2 ({r with mode := []} : Registers).store :=
        Exec.one (read.trans cursor) (.action _ _)
      simpa only [finish,Registers.store,cursor,List.isEmpty_cons,Bool.false_eq_true,↓reduceIte] using checked

def result (r : Registers) (n : Nat) (input : BitString) : Registers :=
  {SourceReplayFixed.result r n input with mode := SourceReplayRecordState.flag (valid n input)}
def block : Block 9 := .seq SourceReplayFixed.block endCheck
def fuel (n : Nat) (input : BitString) : Nat := SourceReplayFixed.fuel n input + 2
theorem block_exec (r : Registers) (n : Nat) (input : BitString) :
    Exec block ({r with input := input,remaining := List.replicate n true}).store
      (fuel n input) (result r n input).store := by
  have finished : finish (SourceReplayFixed.result r n input) = result r n input := by
    by_cases enough : n ≤ input.length <;> cases empty : (input.drop n).isEmpty <;>
      simp only [finish,result,SourceReplayFixed.result,SourceReplayRecordState.flag,valid,
        enough,empty,decide_true,decide_false,Bool.false_and,Bool.true_and,Bool.false_eq_true,↓reduceIte]
  have checked := Exec.seq (SourceReplayFixed.block_exec r n input) (endCheck_exec (SourceReplayFixed.result r n input))
  rw [finished] at checked
  exact checked

theorem fuel_bound (n : Nat) (input : BitString) : fuel n input ≤ 5 * n + 4 * input.length + 8 := by
  have bound := SourceReplayFixed.fuel_bound n input
  unfold fuel
  omega

theorem parsed_fields (r : Registers) (n : Nat) (input : BitString) (x : Point n)
    (parsed : (SourceEncoding.pointCodec n).decode input = some x) :
    (result r n input).input = [] ∧ (result r n input).output = input ∧
      (result r n input).mode = [true] := by
  have width := decode_width n input x parsed
  have good := (valid_iff_width n input).mpr width
  simp only [result,SourceReplayFixed.result,good,SourceReplayRecordState.flag,↓reduceIte]
  rw [← width,List.drop_length,List.take_length]
  exact ⟨rfl,rfl,True.intro⟩

theorem rejected (r : Registers) (n : Nat) (input : BitString)
    (bad : (SourceEncoding.pointCodec n).decode input = none) : (result r n input).mode = [] := by
  have invalid : valid n input = false := by
    cases flag : valid n input with
    | false => rfl
    | true =>
      obtain ⟨x,parsed⟩ := decode_complete n input ((valid_iff_width n input).mp flag)
      rw [bad] at parsed
      cases parsed
  simp only [result,invalid,SourceReplayRecordState.flag,Bool.false_eq_true,↓reduceIte]

end PNP.Concrete.ResidualReduction.SourceReplayWitness
