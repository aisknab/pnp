import PNP.ClauseSquare.Layout

set_option autoImplicit false
namespace PNP.ClauseSquare
open Concrete

def dot : Nat → Word → Word → Bool
  | 0, _, _ => false
  | k+1, a, b => dot k a b ^^ (a k && b k)

def delta (k : Nat) (b : Bool) : Word := fun i => if i=k then b else false

private theorem distribute (a b c d e : Bool) :
    ((a ^^ b) ^^ ((c ^^ d) && e)) = ((a ^^ (c && e)) ^^ (b ^^ (d && e))) := by
  cases a <;> cases b <;> cases c <;> cases d <;> cases e <;> rfl

theorem dot_xor (d : Nat) (a b z : Word) :
    dot d (fun k => a k ^^ b k) z = (dot d a z ^^ dot d b z) := by
  induction d with
  | zero => rfl
  | succ d ih =>
    change (_ ^^ ((a d ^^ b d) && z d)) = _
    rw [ih]; exact distribute _ _ _ _ _

theorem dot_zero (d : Nat) (z : Word) : dot d (fun _ => false) z = false := by
  induction d with
  | zero => rfl
  | succ d ih =>
    change (_ ^^ (false && _))=false
    rw [ih]; rfl

theorem dot_delta (d k : Nat) (v : Bool) (z : Word) :
    dot d (delta k v) z = (if k<d then v && z k else false) := by
  induction d with
  | zero => rfl
  | succ d ih =>
    rw [dot,ih]
    by_cases e : d=k
    · subst k; rw [if_neg (Nat.lt_irrefl _),if_pos (Nat.lt_succ_self _)]
      change (false ^^ ((if d=d then v else false) && z d)) = _
      rw [if_pos rfl,Bool.false_xor]
    · change (_ ^^ ((if d=k then v else false) && z d)) = _
      rw [if_neg e]
      by_cases g : k<d
      · rw [if_pos g,if_pos (by omega : k<d+1),Bool.false_and,Bool.xor_false]
      · rw [if_neg g,if_neg (by omega : ¬ k<d+1)]; rfl

structure Term (n : Nat) where
  col : Nat
  bias : Bool
  axis : Option (Fin n)

def constant {n : Nat} (c : Nat) : Term n := ⟨c,true,none⟩

def litTerm (n p : Nat) (l : CNFLiteral) : Term n :=
  if h : l.variableIndex<n then ⟨p,l.positive,some ⟨l.variableIndex,h⟩⟩ else ⟨p,true,none⟩

def axisBit {n : Nat} (t : Term n) : Word :=
  match t.axis with
  | none => fun _ => false
  | some j => delta j.val true

def val {n : Nat} (x : Head n) (t : Term n) : Bool := t.bias ^^ (t.axis.map x).getD false

def wire {n : Nat} (x : Head n) : Word := fun j => if h : j<n then x ⟨j,h⟩ else false

theorem val_affine {n : Nat} (x : Head n) (t : Term n) :
    val x t = (t.bias ^^ dot n (axisBit t) (wire x)) := by
  cases t with
  | mk c b j =>
    cases j with
    | none =>
      change (b ^^ false) = (b ^^ dot n (fun _ => false) _)
      rw [dot_zero]
    | some j =>
      change (b ^^ x j) = (b ^^ dot n (delta j.val true) _)
      rw [dot_delta,if_pos j.isLt,Bool.true_and]
      unfold wire; rw [dif_pos j.isLt]

theorem value_literal {n : Nat} (x : Head n) (p : Nat) (l : CNFLiteral) :
    val x (litTerm n p l) = factor x l := by
  unfold litTerm factor
  by_cases e : l.variableIndex<n
  · rw [dif_pos e,dif_pos e]
    exact Bool.xor_comm _ _
  · rw [dif_neg e,dif_neg e]; rfl

theorem lit_col (n p : Nat) (l : CNFLiteral) : (litTerm n p l).col=p := by
  unfold litTerm; split <;> rfl

def entry {n : Nat} (f : Term n → Bool) : List (Term n) → Word
  | [] => fun _ => false
  | t :: ts => fun j => delta t.col (f t) j ^^ entry f ts j

def weight {n : Nat} (x : Head n) (z : Word) : List (Term n) → Bool
  | [] => false
  | t :: ts => (val x t && z t.col) ^^ weight x z ts

theorem row_dot {n d : Nat} (x : Head n) (z : Word) (ts : List (Term n))
    (hb : ∀ t ∈ ts, t.col<d) : dot d (entry (val x) ts) z = weight x z ts := by
  induction ts with
  | nil => exact dot_zero _ _
  | cons t ts ih =>
    change dot d (fun j => delta t.col (val x t) j ^^ entry (val x) ts j) z = _
    rw [dot_xor,dot_delta,if_pos (hb t (.head _)),ih (fun a ha => hb a (.tail _ ha))]
    rfl

private theorem rearr (a b c d : Bool) : ((a ^^ b) ^^ (c ^^ d)) = ((a ^^ c) ^^ (b ^^ d)) := by
  cases a <;> cases b <;> cases c <;> cases d <;> rfl

/-- Entries of the evaluated matrix are the constant column array XORed
with the per-original-axis column arrays actually selected by the head. -/
theorem choose_entry {n : Nat} (x : Head n) (ts : List (Term n)) (j : Nat) :
    entry (val x) ts j = (entry Term.bias ts j ^^
        dot n (fun i => entry (fun t => axisBit t i) ts j) (wire x)) := by
  induction ts with
  | nil => change false = (false ^^ dot n (fun _ => false) _); rw [dot_zero]; rfl
  | cons t ts ih =>
    by_cases h : j=t.col
    · have e (f : Term n → Bool) : entry f (t::ts) j = (f t ^^ entry f ts j) := by
        change ((if j=t.col then _ else _) ^^ _) = _; rw [if_pos h]
      have f : (fun i => entry (fun a => axisBit a i) (t::ts) j) =
          (fun i => axisBit t i ^^ entry (fun a => axisBit a i) ts j) := by
        funext i; exact e _
      rw [e,e,f,dot_xor,ih,val_affine x t]
      exact rearr _ _ _ _
    · have e (f : Term n → Bool) : entry f (t::ts) j = entry f ts j := by
        change ((if j=t.col then _ else false) ^^ _) = _; rw [if_neg h,Bool.false_xor]
      have f : (fun i => entry (fun a => axisBit a i) (t::ts) j) =
          fun i => entry (fun a => axisBit a i) ts j := by funext i; exact e _
      rw [e,e,f]; exact ih

end PNP.ClauseSquare
