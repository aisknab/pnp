import PNP.Concrete.ResidualReduction.SourceReplayFamily

/-! Strict fixed-width point fields for stored weights and tails. Width is
an encoded counter already read from the record. A short field clears success;
the machine never supplies missing bits, even at a nonzero width. -/

namespace PNP.Concrete.ResidualReduction.SourceReplayFixed
open PNP.Concrete PNP.Concrete.BitRegister PNP.Concrete.NormalizerBlocks
open PNP.Concrete.NormalizerBlocks.Occurrence
open PNP.Concrete.ResidualReduction.FactoredContraction

theorem point_prefix (n : Nat) (input : BitString) (enough : n ≤ input.length) :
    ∃ x : Point n, ∃ suffix, input = (SourceEncoding.pointCodec n).encode x ++ suffix := by
  induction n generalizing input with
  | zero => exact ⟨(),input,rfl⟩
  | succ n ih =>
    cases input with
    | nil => exact (Nat.not_succ_le_zero n enough).elim
    | cons b rest =>
      have bound : n ≤ rest.length := Nat.le_of_succ_le_succ enough
      obtain ⟨x,suffix,bytes⟩ := ih rest bound
      refine ⟨(b,x),suffix,?_⟩
      change b :: rest = b :: ((SourceEncoding.pointCodec n).encode x ++ suffix)
      exact congrArg (List.cons b) bytes

theorem parse_iff {n : Nat} (input : BitString) (x : Point n) (suffix : BitString) :
    (SourceEncoding.pointCodec n).parse input = some (x,suffix) ↔
      n ≤ input.length ∧ (SourceEncoding.pointCodec n).encode x = input.take n ∧ suffix = input.drop n := by
  constructor
  · intro parsed
    have bytes := (SourceEncoding.pointCodec n).sound input x suffix parsed
    rw [← bytes]
    have width := SourceEncoding.point_length x
    refine ⟨?_,?_,?_⟩
    · rw [List.length_append,width]; omega
    · exact (List.take_left' (l₂ := suffix) width).symm
    · exact (List.drop_left' (l₂ := suffix) width).symm
  · rintro ⟨_,bytes,tail⟩
    have whole : (SourceEncoding.pointCodec n).encode x ++ suffix = input := by
      rw [bytes,tail,List.take_append_drop]
    rw [← whole]
    exact (SourceEncoding.pointCodec n).roundtrip x suffix

theorem valid_parse (n : Nat) (input : BitString) (enough : n ≤ input.length) :
    ∃ x : Point n, (SourceEncoding.pointCodec n).parse input = some (x,input.drop n) := by
  obtain ⟨x,suffix,split⟩ := point_prefix n input enough
  refine ⟨x,?_⟩
  rw [split,List.drop_left' (l₂ := suffix) (SourceEncoding.point_length x)]
  exact (SourceEncoding.pointCodec n).roundtrip x suffix

theorem invalid_parse (n : Nat) (input : BitString) (short : ¬ n ≤ input.length) :
    (SourceEncoding.pointCodec n).parse input = none := by
  cases parsed : (SourceEncoding.pointCodec n).parse input with
  | none => rfl
  | some pair =>
    rcases pair with ⟨x,suffix⟩
    exact (short ((parse_iff input x suffix).mp parsed).1).elim

def prepared (r : Registers) : Registers := {r with excess := [],output := [],mode := [true]}
def result (r : Registers) (count : Nat) (input : BitString) : Registers :=
  {r with input := input.drop count,remaining := [],excess := [],output := input.take count,mode := if count ≤ input.length then [true] else []}
def seed : Block 9 := .seq (.action (.clear 3)) (.seq (.action (.clear 8))
  (.seq (.action (.clear 5)) (.action (.push 5 true))))
def block : Block 9 := .seq seed (.seq MatrixCountedPayload.loop ClauseQuery.reverseLoop)
def fuel (count : Nat) (input : BitString) : Nat := 5 * count + 4 * (input.take count).length + 6

theorem block_exec (r : Registers) (count : Nat) (input : BitString) :
    Exec block ({r with input := input,remaining := List.replicate count true}).store
      (fuel count input) (result r count input).store := by
  let start := {r with input := input,remaining := List.replicate count true}
  let copied := MatrixCountedPayload.result count input (prepared r)
  have setup : Exec seed start.store 4
      ({prepared r with input := input,remaining := List.replicate count true}).store :=
    Exec.seq (.action _ _) (Exec.seq (.action _ _) (Exec.seq (.action _ _) (.action _ _)))
  have copy := MatrixCountedPayload.loop_exec count input (prepared r)
  have reverse : Exec ClauseQuery.reverseLoop copied.store (4 * (input.take count).length + 1)
      (result r count input).store := by
    have checked := ClauseQuery.reverse_exec {copied with excess := []} (input.take count).reverse
    simpa only [copied,MatrixCountedPayload.result,prepared,result,List.append_nil,List.reverse_reverse,List.length_reverse] using checked
  have cost : fuel count input = 4 + ((5 * count + 1) + (4 * (input.take count).length + 1)) := by unfold fuel; omega
  simpa only [block,cost,start,copied] using Exec.seq setup (Exec.seq copy reverse)

theorem fuel_bound (count : Nat) (input : BitString) : fuel count input ≤ 5 * count + 4 * input.length + 6 := by
  have bound := Nat.min_le_right count input.length
  simp only [fuel,List.length_take]
  omega

end PNP.Concrete.ResidualReduction.SourceReplayFixed
