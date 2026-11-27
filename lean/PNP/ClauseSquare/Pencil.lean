import PNP.ClauseSquare.Dot

set_option autoImplicit false
namespace PNP.ClauseSquare
open Concrete
open SignedTernary.CNF (readWord)

def rowData (n top k : Nat) (o : Op) : List (Term n) :=
  (constant k) :: (match o with
    | .one => [constant top]
    | .mul p l => [litTerm n p l]
    | .add p t => [constant p,constant t])

def numbered (n top k : Nat) : List Op → List (List (Term n))
  | [] => []
  | o :: os => rowData n top k o :: numbered n top (k+1) os

def bottom (n top last : Nat) : List (Term n) := [constant last, constant top]

def pencil (F : CNFFormula) : List (List (Term F.variableCount)) :=
  numbered F.variableCount (h F) 0 (program F) ++ [bottom _ (h F) (last F)]

theorem numbered_length (n top k : Nat) (os : List Op) : (numbered n top k os).length=os.length := by
  induction os generalizing k with
  | nil => rfl
  | cons o os ih => simp only [numbered,List.length_cons,ih]

theorem square (F : CNFFormula) : (pencil F).length=h F+1 := by
  unfold pencil; rw [List.length_append,numbered_length]; rfl

def KernelRows {n : Nat} (d : Nat) (x : Head n) (z : Word) : List (List (Term n)) → Prop
  | [] => True
  | r :: rs => dot d (entry (val x) r) z = false ∧ KernelRows d x z rs

theorem kernel_append {n : Nat} (d : Nat) (x : Head n) (z : Word) (a b : List (List (Term n))) :
    KernelRows d x z (a++b) ↔ KernelRows d x z a ∧ KernelRows d x z b := by
  induction a with
  | nil => exact ⟨fun g => ⟨True.intro,g⟩,fun g => g.2⟩
  | cons r a ih =>
    change (_ ∧ KernelRows d x z (a++b)) ↔ (_ ∧ _) ∧ _
    rw [ih]; exact and_assoc.symm

theorem row_bounded {n top k : Nat} (o : Op) (hk : k<top) (ho : Earlier k o) :
    ∀ t ∈ rowData n top k o, t.col<top+1 := by
  intro t ht
  cases o with
  | one =>
    simp only [rowData,List.mem_cons,List.not_mem_nil,or_false] at ht
    rcases ht with e|e <;> subst t <;> change _ < top+1 <;>
      first | exact Nat.lt_succ_of_lt hk | exact Nat.lt_succ_self _
  | mul p l =>
    simp only [rowData,List.mem_cons,List.not_mem_nil,or_false] at ht
    rcases ht with e|e <;> subst t
    · exact Nat.lt_succ_of_lt hk
    · rw [lit_col]; exact Nat.lt_succ_of_lt (Nat.lt_trans ho hk)
  | add p a =>
    simp only [rowData,List.mem_cons,List.not_mem_nil,or_false] at ht
    rcases ht with e|e|e <;> subst t
    · exact Nat.lt_succ_of_lt hk
    · exact Nat.lt_succ_of_lt (Nat.lt_trans ho.1 hk)
    · exact Nat.lt_succ_of_lt (Nat.lt_trans ho.2 hk)

theorem constant_val {n : Nat} (x : Head n) (k : Nat) : val x (constant k) = true := rfl
theorem constant_col {n : Nat} (k : Nat) : (constant (n:=n) k).col = k := rfl

theorem row_value {n : Nat} (x : Head n) (z : Word) (top k : Nat) (o : Op) :
    weight x z (rowData n top k o) = (z k ^^ rhs x (z top) z o) := by
  cases o with
  | one => simp only [rowData,weight,constant_col,constant_val,Bool.true_and,Bool.xor_false,rhs]
  | mul p l =>
    simp only [rowData,weight,constant_col,constant_val,Bool.true_and,Bool.xor_false,rhs,value_literal,lit_col]
    rw [Bool.and_comm]
  | add p a => simp only [rowData,weight,constant_col,constant_val,Bool.true_and,Bool.xor_false,rhs]

theorem xor_zero (a b : Bool) : (a ^^ b) = false ↔ a=b := by cases a <;> cases b <;> decide

theorem numbered_rows {n : Nat} (x : Head n) (z : Word) (top k : Nat) (os : List Op)
    (ho : Ordered k os) (hk : k+os.length≤top) :
    KernelRows (top+1) x z (numbered n top k os) ↔ Rows x (z top) z k os := by
  induction os generalizing k with
  | nil => exact Iff.rfl
  | cons o os ih =>
    simp only [List.length_cons] at hk
    change (_ = false ∧ KernelRows (top+1) x z (numbered n top (k+1) os)) ↔ _ ∧ _
    rw [row_dot x z _ (row_bounded o (by omega : k<top) ho.1),row_value,xor_zero,ih (k+1) ho.2 (by omega)]

theorem bottom_row {n : Nat} (x : Head n) (z : Word) (top last : Nat) (hb : last < top) :
    KernelRows (top+1) x z [bottom n top last] ↔ z last = z top := by
  have b : ∀ t ∈ bottom n top last, t.col<top+1 := by
    intro t ht
    simp only [bottom,List.mem_cons,List.not_mem_nil,or_false] at ht
    rcases ht with e|e <;> subst t
    · exact Nat.lt_succ_of_lt hb
    · exact Nat.lt_succ_self _
  change (dot (top+1) (entry (val x) _) z = false ∧ True) ↔ _
  rw [row_dot x z _ b]
  simp only [bottom,weight,constant_col,constant_val,Bool.true_and,Bool.xor_false,xor_zero,and_true]

theorem actual_matrix_rows (F : CNFFormula) (x : Head F.variableCount) (z : Word) :
    KernelRows (h F+1) x z (pencil F) ↔
      Rows x (z (h F)) z 0 (program F) ∧ z (last F)=z (h F) := by
  rw [pencil,kernel_append,numbered_rows _ _ _ _ _ (program_order F) (by simp only [Nat.zero_add,h,Nat.le_refl]),
    bottom_row _ _ _ _ (last_in F)]

theorem rows_transfer {n : Nat} (x : Head n) (q : Bool) {z w : Word} (top k : Nat) (os : List Op)
    (ho : Ordered k os) (ht : k+os.length≤top) (ha : Agree top z w)
    (hs : Rows x q z k os) : Rows x q w k os := by
  induction os generalizing k with
  | nil => trivial
  | cons o os ih =>
    simp only [List.length_cons] at ht
    have eqo := rhs_agree x q o ho.1 (fun j hj => ha j (by omega))
    exact ⟨(ha k (by omega)).symm.trans (hs.1.trans eqo),ih (k+1) ho.2 (by omega) hs.2⟩

theorem wire_hit {d j : Nat} (v : Head d) (u : j<d) : wire v j = v ⟨j,u⟩ := dif_pos u

def augmented (top : Nat) (t : Word) (q : Bool) : Head (top+1) := fun i => if i.val=top then q else t i.val

theorem attached_tag (t : Word) (top : Nat) (q : Bool) : wire (augmented top t q) top=q := by
  rw [wire_hit _ (Nat.lt_succ_self _)]
  exact if_pos rfl

theorem attached_before (t : Word) (top : Nat) (q : Bool) : Agree top (wire (augmented top t q)) t := by
  intro j hj
  rw [wire_hit _ (Nat.lt_succ_of_lt hj)]
  exact if_neg (Nat.ne_of_lt hj)

def First (F : CNFFormula) (x : Head F.variableCount) (q : Bool) (t : Head (h F)) : Prop :=
  KernelRows (h F+1) x (wire (augmented (h F) (wire t) q)) (numbered _ (h F) 0 (program F))

/-- Full uniqueness of the actual finite tail vector *before* imposing the bottom row. -/
theorem prefix_exact (F : CNFFormula) (x : Head F.variableCount) (q : Bool) (t : Head (h F)) :
    First F x q t ↔ t=(fun i => answer F x q i.val) := by
  unfold First
  rw [numbered_rows _ _ _ _ _ (program_order F) (by simp only [Nat.zero_add,h,Nat.le_refl]),attached_tag]
  constructor
  · intro hs
    have ha := answer_unique F x q hs
    funext i
    have hi := (attached_before (wire t) (h F) q i.val i.isLt).symm.trans (ha i.val i.isLt)
    rw [wire_hit _ i.isLt] at hi; exact hi
  · intro ht; subst t
    apply rows_transfer x q (h F) 0 _ (program_order F) (by simp only [Nat.zero_add,h,Nat.le_refl]) _ (answer_solves F x q)
    intro j hj
    rw [attached_before _ (h F) q j hj,wire_hit _ hj]

def Singular (F : CNFFormula) (x : Head F.variableCount) : Prop :=
  ∃ z : Head (h F+1), (∃ j, z j=true) ∧ KernelRows (h F+1) x (wire z) (pencil F)

theorem false_tag_trivial (F : CNFFormula) (x : Head F.variableCount) (z : Head (h F+1))
    (hz : KernelRows (h F+1) x (wire z) (pencil F)) (hq : wire z (h F)=false) :
    ∀ j, z j=false := by
  obtain ⟨hr,_⟩ := (actual_matrix_rows F x _).mp hz
  rw [hq] at hr
  have ha := answer_unique F x false hr
  rw [answer_zero] at ha
  intro j
  by_cases he : j.val=h F
  · have e : wire z j.val=false := by rw [he]; exact hq
    rw [wire_hit _ j.isLt] at e; exact e
  · have e := ha j.val (by have := j.isLt; omega)
    rw [wire_hit _ j.isLt] at e; exact e

theorem kernel_tag_one (F : CNFFormula) (x : Head F.variableCount) (z : Head (h F+1))
    (nz : ∃ j, z j=true) (hz : KernelRows (h F+1) x (wire z) (pencil F)) :
    wire z (h F)=true := by
  cases ht : wire z (h F) with
  | true => rfl
  | false =>
    obtain ⟨j,hj⟩ := nz
    rw [false_tag_trivial F x z hz ht j] at hj
    cases hj

/-- A square matrix over the two-element field is singular exactly when its finite
linear map has a nonzero kernel vector. This target indexes every original variable. -/
theorem singular_iff_numbered (F : CNFFormula) (x : Head F.variableCount) :
    Singular F x ↔ F.Satisfied (readWord F.variableCount x) := by
  constructor
  · rintro ⟨z,nz,hz⟩
    have hq := kernel_tag_one F x z nz hz
    have hc := (actual_matrix_rows F x _).mp hz
    rw [hq] at hc
    exact (complete_iff F x).mp ⟨wire z,hc⟩
  · intro hs
    obtain ⟨t,ht,hl⟩ := (complete_iff F x).mpr hs
    let z := augmented (h F) t true
    refine ⟨z,⟨⟨h F,Nat.lt_succ_self _⟩,if_pos rfl⟩,(actual_matrix_rows F x _).mpr ?_⟩
    rw [show wire z (h F)=true from attached_tag _ _ _]
    constructor
    · apply rows_transfer x true (h F) 0 _ (program_order F) (by simp only [Nat.zero_add,h,Nat.le_refl]) _ ht
      intro j hj; exact (attached_before _ _ _ j hj).symm
    · exact (attached_before _ _ _ _ (last_in F)).trans hl

end PNP.ClauseSquare
