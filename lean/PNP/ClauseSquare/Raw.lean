import PNP.ClauseSquare.Pencil

set_option autoImplicit false
namespace PNP.ClauseSquare
open Concrete
open SignedTernary.CNF (readWord readWord_length readWord_surjective)

def lift (F : CNFFormula) (x : Head F.variableCount) : Head (h F+1) :=
  augmented (h F) (answer F x true) true

theorem lift_nonzero (F : CNFFormula) (x : Head F.variableCount) : ∃ i, lift F x i=true :=
  ⟨⟨h F,Nat.lt_succ_self _⟩,if_pos rfl⟩

theorem lift_exact (F : CNFFormula) (x : Head F.variableCount) :
    KernelRows (h F+1) x (wire (lift F x)) (pencil F) ↔ F.Satisfied (readWord F.variableCount x) := by
  constructor
  · intro hz; exact (singular_iff_numbered _ _).mp ⟨_,lift_nonzero _ _,hz⟩
  · intro hs
    apply (actual_matrix_rows _ _ _).mpr
    change Rows x (wire (augmented _ _ true) _) _ 0 _ ∧ _
    rw [attached_tag]
    constructor
    · apply rows_transfer x true (h F) 0 _ (program_order F) (by simp only [Nat.zero_add,h,Nat.le_refl]) _ (answer_solves F x true)
      intro j hj; exact (attached_before _ _ _ j hj).symm
    · unfold lift
      rw [attached_tag,attached_before _ _ _ _ (last_in F),answer_last,Bool.true_and]
      exact (checkClauses_eq_true_iff _ _).mpr hs.2

theorem only_nonzero_witness (F : CNFFormula) (x : Head F.variableCount) (z : Head (h F+1))
    (hn : ∃ j, z j=true) (hz : KernelRows (h F+1) x (wire z) (pencil F)) : z=lift F x := by
  have hq := kernel_tag_one F x z hn hz
  have hr := ((actual_matrix_rows _ _ _).mp hz).1
  rw [hq] at hr
  have ha := answer_unique F x true hr
  funext i
  by_cases e : i.val=h F
  · have he : wire z i.val=true := by rw [e]; exact hq
    rw [wire_hit _ i.isLt] at he
    exact he.trans (if_pos e).symm
  · have hi : i.val<h F := by have := i.isLt; omega
    have he := ha i.val hi; rw [wire_hit _ i.isLt] at he
    exact he.trans (if_neg e).symm

structure Raw where
  n : Nat
  d : Nat
  rows : List (List (Term n))

def parsed : Option CNFFormula → Raw
  | some F => ⟨F.variableCount,h F+1,pencil F⟩
  | none => ⟨0,1,[[constant 0]]⟩

def compile (source : BitString) : Raw := parsed (decodeEncodedCNF source)

def Raw.NullWitness (S : Raw) (x : Head S.n) :=
  ∃ z : Head S.d, (∃ j, z j=true) ∧ KernelRows S.d x (wire z) S.rows

theorem always_square (q : Option CNFFormula) : (parsed q).rows.length=(parsed q).d := by
  cases q with
  | none => rfl
  | some F => exact square F

theorem reject_singleton (x : Head (parsed none).n) : ¬ (parsed none).NullWitness x := by
  rintro ⟨z,⟨i,hi⟩,hr,_⟩
  have hb : ∀ u ∈ [constant (n:=0) 0], u.col<1 := by
    intro u hu
    have he : u=constant (n:=0) 0 := List.mem_singleton.mp hu
    subst u; decide
  change dot 1 (entry (val x) [constant 0]) (wire z)=false at hr
  have hw : weight (n:=0) x (wire z) [constant 0]=false := (row_dot (n:=0) (d:=1) x (wire z) [constant 0] hb).symm.trans hr
  simp only [weight,constant_val,constant_col,Bool.true_and,Bool.xor_false] at hw
  have ei : i.val=0 := by have hlt : i.val<1 := i.isLt; omega
  have h0 : wire z i.val=false := by rw [ei]; exact hw
  rw [wire_hit z i.isLt,hi] at h0
  cases h0

theorem source_words (F : CNFFormula) (w : BitString) : F.Satisfied w ↔
    ∃ x : Head F.variableCount, readWord F.variableCount x=w ∧ Singular F x := by
  constructor
  · intro hw
    cases F with
    | mk n cs =>
      have hlen : w.length=n := hw.1
      subst n
      obtain ⟨x,hx⟩ := readWord_surjective w
      refine ⟨x,hx,(singular_iff_numbered _ _).mpr ?_⟩
      change CNFFormula.Satisfied ⟨w.length,cs⟩ (readWord w.length x)
      rw [hx]; exact hw
  · rintro ⟨x,hx,hz⟩
    rw [← hx]; exact (singular_iff_numbered _ _).mp hz

theorem parsed_readback (q : Option CNFFormula) (w : BitString) :
    (∃ F, q=some F ∧ F.Satisfied w) ↔
    ∃ x : Head (parsed q).n, readWord _ x=w ∧ (parsed q).NullWitness x := by
  cases q with
  | none =>
    constructor
    · rintro ⟨_,he,_⟩; cases he
    · rintro ⟨x,_,h⟩; exact False.elim (reject_singleton x h)
  | some F =>
    constructor
    · rintro ⟨G,he,hg⟩; cases he; exact (source_words F _).mp hg
    · intro h; exact ⟨F,rfl,(source_words F _).mpr h⟩

theorem exact_original_word (s w : BitString) :
    (∃ F, decodeEncodedCNF s=some F ∧ F.Satisfied w) ↔
      ∃ x : Head (compile s).n, readWord _ x=w ∧ (compile s).NullWitness x :=
  parsed_readback (decodeEncodedCNF s) w

theorem wrong_width (s w : BitString) (bad : w.length≠(compile s).n) :
    ¬ ∃ x : Head (compile s).n, readWord _ x=w ∧ (compile s).NullWitness x := by
  rintro ⟨x,hw,_⟩
  exact bad (hw ▸ readWord_length _ x)

theorem all_original (s : BitString) :
    CNFSAT s ↔ ∃ x : Head (compile s).n, (compile s).NullWitness x := by
  constructor
  · rintro ⟨F,hd,w,hw⟩
    obtain ⟨x,_,hx⟩ := (exact_original_word s w).mp ⟨F,hd,hw⟩
    exact ⟨x,hx⟩
  · rintro ⟨x,hx⟩
    obtain ⟨F,hd,hw⟩ := (exact_original_word s (readWord _ x)).mpr ⟨x,rfl,hx⟩
    exact ⟨F,hd,_,hw⟩

end PNP.ClauseSquare
