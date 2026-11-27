import PNP.ClauseSquare.Trace

set_option autoImplicit false
namespace PNP.ClauseSquare
open Concrete
open SignedTernary.CNF (readWord readWord_length)

def used (n : Nat) : List CNFLiteral → Nat
  | [] => 0
  | l :: ls => if l.variableIndex < n then 1+used n ls else used n ls

def literals (n : Nat) (p : Nat) : List CNFLiteral → List Op
  | [] => []
  | l :: ls => if l.variableIndex < n then
      .mul p l :: literals n (p+1) ls else literals n p ls

theorem literals_length (n p : Nat) (c : List CNFLiteral) : (literals n p c).length=used n c := by
  induction c generalizing p with
  | nil => rfl
  | cons l ls ih =>
    by_cases h : l.variableIndex<n
    · simp only [literals,used,if_pos h,List.length_cons,ih]; omega
    · simp only [literals,used,if_neg h,ih]

theorem literals_ordered (n p : Nat) (c : List CNFLiteral) : Ordered (p+1) (literals n p c) := by
  induction c generalizing p with
  | nil => trivial
  | cons l ls ih =>
    by_cases h : l.variableIndex<n
    · rw [literals,if_pos h]; exact ⟨Nat.lt_succ_self p,ih (p+1)⟩
    · rw [literals,if_neg h]; exact ih p

private theorem combine_failure (a b c : Bool) : ((a && !b) && !c) = (a && !(b || c)) := by
  cases a <;> cases b <;> cases c <;> rfl

theorem literals_value {n : Nat} (x : Head n) (q : Bool) (p : Nat) (c : List CNFLiteral) (t : Word) :
    fill x q (p+1) (literals n p c) t (p+used n c) = (t p && !checkClause c (readWord n x)) := by
  induction c generalizing p t with
  | nil =>
    change t p = (t p && true); exact (Bool.and_true _).symm
  | cons l ls ih =>
    by_cases h : l.variableIndex<n
    · rw [literals,if_pos h,used,if_pos h]
      have hn : p+(1+used n ls)=(p+1)+used n ls := by omega
      rw [hn]
      change fill x q ((p+1)+1) (literals n (p+1) ls) (put (p+1) (t p && factor x l) t) _ = _
      rw [ih,put_here,factor_check]
      exact combine_failure _ _ _
    · rw [literals,if_neg h,used,if_neg h,ih]
      have hf : checkLiteral l (readWord n x) = false := by
        unfold checkLiteral
        rw [SignedTernary.CNF.readWord_at,dif_neg h]
      simp only [checkClause,hf,Bool.false_or]

def block (n s : Nat) (c : List CNFLiteral) : List Op :=
  literals n s c ++ [.add s (s+used n c)]

theorem block_length (n s : Nat) (c : List CNFLiteral) : (block n s c).length = used n c + 1 := by
  rw [block,List.length_append,literals_length]; rfl

theorem block_ordered (n s : Nat) (c : List CNFLiteral) : Ordered (s+1) (block n s c) := by
  apply ordered_append _ _ _ (literals_ordered n s c)
  rw [literals_length]
  exact ⟨⟨by omega,by omega⟩,True.intro⟩

private theorem xor_failure (b c : Bool) : (b ^^ (b && !c)) = (b && c) := by
  cases b <;> cases c <;> rfl

theorem block_value {n : Nat} (x : Head n) (q : Bool) (s : Nat) (c : List CNFLiteral) (t : Word) :
    fill x q (s+1) (block n s c) t (s+used n c+1) = (t s && checkClause c (readWord n x)) := by
  rw [block,fill_append,literals_length]
  have hi : s+1+used n c = s+used n c+1 := by omega
  rw [hi]
  change put _ (_ ^^ _) _ _ = _
  rw [put_here,fill_preserves x q (s+1) (literals n s c) t s (Nat.lt_succ_self s),literals_value,xor_failure]

def afterClauses (n s : Nat) : List (List CNFLiteral) → List Op
  | [] => []
  | c :: cs => block n s c ++ afterClauses n (s+used n c+1) cs

theorem after_ordered (n s : Nat) (cs : List (List CNFLiteral)) :
    Ordered (s+1) (afterClauses n s cs) := by
  induction cs generalizing s with
  | nil => trivial
  | cons c cs ih =>
    apply ordered_append _ _ _ (block_ordered n s c)
    rw [block_length]
    have hk : s+1+(used n c+1)=(s+used n c+1)+1 := by omega
    rw [hk]; exact ih _

theorem after_value {n : Nat} (x : Head n) (q : Bool) (s : Nat) (cs : List (List CNFLiteral))
    (t : Word) : fill x q (s+1) (afterClauses n s cs) t (s+(afterClauses n s cs).length) =
    (t s && checkClauses cs (readWord n x)) := by
  induction cs generalizing s t with
  | nil => change t s = (t s && true); exact (Bool.and_true _).symm
  | cons c cs ih =>
    rw [afterClauses,fill_append,List.length_append,block_length]
    have hi : s+1+(used n c+1)=(s+used n c+1)+1 := by omega
    have hj : s+(used n c+1+(afterClauses n (s+used n c+1) cs).length)=
        (s+used n c+1)+(afterClauses n (s+used n c+1) cs).length := by omega
    rw [hi,hj,ih,block_value,checkClauses,Bool.and_assoc]

def program (F : CNFFormula) : List Op := .one :: afterClauses F.variableCount 0 F.clauses
def last (F : CNFFormula) : Nat := (afterClauses F.variableCount 0 F.clauses).length
def h (F : CNFFormula) : Nat := (program F).length

theorem height (F : CNFFormula) : h F = last F + 1 := rfl
theorem last_in (F : CNFFormula) : last F < h F := Nat.lt_succ_self _
theorem program_order (F : CNFFormula) : Ordered 0 (program F) := ⟨True.intro,after_ordered _ _ _⟩

def answer (F : CNFFormula) (x : Head F.variableCount) (q : Bool) : Word := fill x q 0 (program F) zero

theorem answer_solves (F : CNFFormula) (x : Head F.variableCount) (q : Bool) :
    Rows x q (answer F x q) 0 (program F) := fill_solves x q 0 _ _ (program_order F)

theorem answer_unique (F : CNFFormula) (x : Head F.variableCount) (q : Bool) {t : Word}
    (hs : Rows x q t 0 (program F)) : Agree (h F) t (answer F x q) := by
  have g := rows_unique x q 0 (program F) (t:=zero) (program_order F) hs
    (by intro j hj; exact False.elim (Nat.not_lt_zero _ hj))
  simpa only [Nat.zero_add,h,answer] using g

theorem answer_last (F : CNFFormula) (x : Head F.variableCount) (q : Bool) :
    answer F x q (last F) = (q && checkClauses F.clauses (readWord F.variableCount x)) := by
  let w : Word := put 0 q zero
  change fill x q (0+1) (afterClauses _ 0 F.clauses) w (last F) = _
  have e := after_value x q 0 F.clauses w
  simp only [Nat.zero_add] at e
  exact e.trans (congrArg (fun b => b && checkClauses F.clauses (readWord _ x)) (put_here 0 q zero))

theorem answer_zero (F : CNFFormula) (x : Head F.variableCount) : answer F x false = zero :=
  fill_zero x 0 (program F)

def Complete (F : CNFFormula) (x : Head F.variableCount) (t : Word) : Prop :=
  Rows x true t 0 (program F) ∧ t (last F)=true

theorem complete_iff (F : CNFFormula) (x : Head F.variableCount) :
    (∃ t, Complete F x t) ↔ F.Satisfied (readWord F.variableCount x) := by
  constructor
  · rintro ⟨t,ht,hl⟩
    have z := answer_unique F x true ht (last F) (last_in F)
    rw [answer_last,Bool.true_and] at z
    exact ⟨readWord_length _ x,(checkClauses_eq_true_iff _ _).mp (z.symm.trans hl)⟩
  · intro hs
    refine ⟨answer F x true,answer_solves F x true,?_⟩
    rw [answer_last,Bool.true_and]
    exact (checkClauses_eq_true_iff _ _).mpr hs.2

end PNP.ClauseSquare
