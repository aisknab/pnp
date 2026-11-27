import PNP.SignedTernary.CNF.Source

set_option autoImplicit false
namespace PNP.ClauseSquare
open Concrete
open SignedTernary.CNF (readWord readWord_at readWord_length readWord_surjective)

abbrev Word := Nat → Bool
abbrev Head (n : Nat) := Fin n → Bool

/-- Absolute zero-based physical tail-column addresses. An omitted literal has no row. -/
inductive Op where
  | one
  | mul (previous : Nat) (literal : CNFLiteral)
  | add (start last : Nat)
deriving DecidableEq, Repr

def factor {n : Nat} (x : Head n) (l : CNFLiteral) : Bool :=
  if h : l.variableIndex < n then (x ⟨l.variableIndex,h⟩ ^^ l.positive) else true

theorem factor_check {n : Nat} (x : Head n) (l : CNFLiteral) :
    factor x l = !(checkLiteral l (readWord n x)) := by
  unfold factor checkLiteral
  rw [readWord_at]
  by_cases h : l.variableIndex < n
  · rw [dif_pos h,dif_pos h]
    cases x ⟨l.variableIndex,h⟩ <;> cases l.positive <;> rfl
  · rw [dif_neg h,dif_neg h]; rfl

def rhs {n : Nat} (x : Head n) (tag : Bool) (z : Word) : Op → Bool
  | .one => tag
  | .mul p l => z p && factor x l
  | .add p q => z p ^^ z q

def Earlier (k : Nat) : Op → Prop
  | .one => True
  | .mul p _ => p < k
  | .add p q => p < k ∧ q < k

def Ordered (k : Nat) : List Op → Prop
  | [] => True
  | o :: os => Earlier k o ∧ Ordered (k+1) os

def Agree (k : Nat) (a b : Word) : Prop := ∀ j, j < k → a j = b j

theorem rhs_agree {n k : Nat} (x : Head n) (q : Bool) {a b : Word} (o : Op)
    (he : Earlier k o) (ha : Agree k a b) : rhs x q a o = rhs x q b o := by
  cases o with
  | one => rfl
  | mul p l => change (a p && _) = (b p && _); rw [ha p he]
  | add p t => change (a p ^^ a t) = (b p ^^ b t); rw [ha p he.1,ha t he.2]

def put (k : Nat) (v : Bool) (z : Word) : Word := fun j => if j=k then v else z j

theorem put_here (k : Nat) (v : Bool) (z : Word) : put k v z k = v := if_pos rfl
theorem put_away {k j : Nat} (h : j ≠ k) (v : Bool) (z : Word) : put k v z j = z j := if_neg h

def fill {n : Nat} (x : Head n) (q : Bool) : Nat → List Op → Word → Word
  | _, [], t => t
  | k, o :: os, t => fill x q (k+1) os (put k (rhs x q t o) t)

def Rows {n : Nat} (x : Head n) (q : Bool) (z : Word) : Nat → List Op → Prop
  | _, [] => True
  | k, o :: os => z k = rhs x q z o ∧ Rows x q z (k+1) os

theorem ordered_append (k : Nat) (a b : List Op) (ha : Ordered k a)
    (hb : Ordered (k+a.length) b) : Ordered k (a++b) := by
  induction a generalizing k with
  | nil => exact hb
  | cons o os ih =>
    constructor
    · exact ha.1
    · apply ih (k+1) ha.2
      have h : k+1+os.length = k+(o::os).length := by simp only [List.length_cons]; omega
      rw [h]; exact hb

theorem fill_append {n : Nat} (x : Head n) (q : Bool) (k : Nat) (os bs : List Op) (t : Word) :
    fill x q k (os++bs) t = fill x q (k+os.length) bs (fill x q k os t) := by
  induction os generalizing k t with
  | nil => rfl
  | cons o os ih =>
    simp only [List.cons_append,List.length_cons,fill]
    rw [ih]
    have ht : k+1+os.length = k+(os.length+1) := by omega
    rw [ht]

theorem fill_preserves {n : Nat} (x : Head n) (q : Bool) (k : Nat) (os : List Op) (t : Word) :
    Agree k (fill x q k os t) t := by
  induction os generalizing k t with
  | nil => intro j _; rfl
  | cons o os ih =>
    intro j hj
    change fill x q (k+1) os (put k (rhs x q t o) t) j = _
    rw [ih (k+1) _ j (by omega), put_away (by omega)]

theorem fill_solves {n : Nat} (x : Head n) (q : Bool) (k : Nat) (os : List Op) (t : Word)
    (ho : Ordered k os) : Rows x q (fill x q k os t) k os := by
  induction os generalizing k t with
  | nil => trivial
  | cons o os ih =>
    let u := put k (rhs x q t o) t
    let w := fill x q (k+1) os u
    have h : Agree (k+1) w u := fill_preserves x q (k+1) os u
    have ht : Agree k w t := by
      intro j hj
      rw [h j (by omega)]
      exact put_away (by omega) _ _
    constructor
    · change w k = rhs x q w o
      rw [h k (by omega),rhs_agree x q o ho.1 ht]
      exact put_here _ _ _
    · exact ih (k+1) u ho.2

theorem rows_unique {n : Nat} (x : Head n) (q : Bool) (k : Nat) (os : List Op) {z t : Word}
    (ho : Ordered k os) (hz : Rows x q z k os) (ht : Agree k z t) :
    Agree (k+os.length) z (fill x q k os t) := by
  induction os generalizing k t with
  | nil => exact ht
  | cons o os ih =>
    have h : Agree (k+1) z (put k (rhs x q t o) t) := by
      intro j hj
      by_cases e : j=k
      · subst j; rw [put_here]; exact hz.1.trans (rhs_agree x q o ho.1 ht)
      · rw [put_away e]; exact ht j (by omega)
    have g := ih (k+1) ho.2 hz.2 h
    have hk : k+(o::os).length=k+1+os.length := by simp only [List.length_cons]; omega
    rw [hk]; exact g

def zero : Word := fun _ => false

theorem fill_zero {n : Nat} (x : Head n) (k : Nat) (os : List Op) :
    fill x false k os zero = zero := by
  induction os generalizing k with
  | nil => rfl
  | cons o os ih =>
    have e : rhs x false zero o = false := by cases o <;> rfl
    have u : put k false zero = zero := by
      funext j; unfold put zero; split <;> rfl
    simp only [fill,e,u,ih]

end PNP.ClauseSquare
