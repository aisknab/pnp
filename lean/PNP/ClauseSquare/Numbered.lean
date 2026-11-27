import PNP.ClauseSquare.Packed

set_option autoImplicit false
namespace PNP.ClauseSquare
open Concrete
open SignedTernary.CNF (readWord readWord_length)

def numberedHead (n a : Nat) : Head n := fun i => a.testBit i.val
def headMask {n : Nat} (x : Head n) := pack (readWord n x)

theorem headMask_bound {n : Nat} (x : Head n) : headMask x<2^n := by
  have g := packed_bound (readWord n x); rw [readWord_length] at g; exact g

theorem mask_head {n : Nat} (x : Head n) : numberedHead n (headMask x)=x := by
  funext i; exact (packed_word x i.val).trans (wire_hit _ i.isLt)

theorem head_mask (n a : Nat) (ha : a<2^n) : headMask (numberedHead n a)=a := by
  apply Nat.eq_of_testBit_eq
  intro i; rw [headMask,packed_word]
  by_cases hi : i<n
  · rw [wire_hit _ hi]; rfl
  · unfold wire; rw [dif_neg hi]
    exact (Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le ha (Nat.pow_le_pow_right (by decide : 0<2) (by omega : n≤i)))).symm

def NumberedKernel (s : Raw) (a : Nat) := a<2^s.n ∧ MaskWitness s (numberedHead s.n a)

theorem numbered_exact (F : CNFFormula) (a : Nat) :
    NumberedKernel (parsed (some F)) a ↔ a<2^F.variableCount ∧
      F.Satisfied (readWord F.variableCount (numberedHead F.variableCount a)) := by
  change (_ ∧ MaskWitness _ _) ↔ _ ∧ _
  rw [← mask_witness]
  exact and_congr_right (fun _ => singular_iff_numbered _ _)

theorem reject_high_mask (s : Raw) (a : Nat) (bad : 2^s.n≤a) : ¬ NumberedKernel s a := by
  intro g; exact (Nat.not_lt_of_ge bad) g.1

theorem strict_all_numbered (bits : BitString) :
    CNFSAT bits ↔ ∃ a : Nat, NumberedKernel (compile bits) a := by
  rw [all_original_masks]
  constructor
  · rintro ⟨x,hx⟩
    refine ⟨headMask x,headMask_bound x,?_⟩
    rw [mask_head]; exact hx
  · rintro ⟨a,_,hz⟩; exact ⟨numberedHead _ a,hz⟩

theorem strict_same_mask_word (bits w : BitString) :
    (∃ F, decodeEncodedCNF bits=some F ∧ F.Satisfied w) ↔
      ∃ a : Nat, NumberedKernel (compile bits) a ∧
        readWord (compile bits).n (numberedHead (compile bits).n a)=w := by
  rw [packed_same_word]
  constructor
  · rintro ⟨x,hw,hx⟩
    refine ⟨headMask x,⟨headMask_bound x,?_⟩,?_⟩
    · rw [mask_head]; exact hx
    · rw [mask_head]; exact hw
  · rintro ⟨a,⟨_,hz⟩,hw⟩; exact ⟨_,hw,hz⟩

end PNP.ClauseSquare
