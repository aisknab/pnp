import Std

/-!
# Group operations and signed words

Use the three entries above the diagonal of a unitriangular binary matrix as coordinates for the group. Word evaluation multiplies tokens in order; an inverse token is not a second free value.
-/

set_option autoImplicit false

namespace PNP.ThreeUse

structure G where
  a : Bool
  b : Bool
  c : Bool
deriving DecidableEq, Repr

def gmul (x y : G) : G := ⟨x.a ^^ y.a, x.b ^^ y.b, (x.c ^^ y.c) ^^ (x.a && y.b)⟩

def ginv (x : G) : G := ⟨x.a, x.b, x.c ^^ (x.a && x.b)⟩

def center (c : Bool) : G := ⟨false, false, c⟩

def one : G := center false

def mark : G := center true

def det (x y : G) : Bool := (x.a && y.b) ^^ (x.b && y.a)

theorem assoc (x y z : G) : gmul (gmul x y) z = gmul x (gmul y z) := by
  cases x; cases y; cases z; decide +revert

theorem lid (x : G) : gmul one x = x := by cases x; decide +revert

theorem rid (x : G) : gmul x one = x := by cases x; decide +revert

theorem inv_cancel (x y : G) : gmul x (ginv y) = one ↔ x = y := by cases x; cases y; decide +revert

theorem inv_one : ginv one = one := rfl

theorem inv_prod (x y : G) : ginv (gmul x y) = gmul (ginv y) (ginv x) := by cases x; cases y; decide +revert

theorem centermul (a b : Bool) : gmul (center a) (center b) = center (a ^^ b) := by cases a <;> cases b <;> rfl

theorem center_inj (a b : Bool) : center a = center b ↔ a = b := by cases a <;> cases b <;> decide

theorem comm_form (x y : G) : gmul (gmul x y) (gmul (ginv x) (ginv y)) = center (det x y) := by
  cases x; cases y; decide +revert

abbrev Tok (ι : Type) := ι × Bool  -- false=positive, true=inverse

abbrev Word (ι : Type) := List (Tok ι)

def wt {ι : Type} (v : ι → G) (a : Tok ι) : G := if a.2 then ginv (v a.1) else v a.1

def eval {ι : Type} (v : ι → G) : Word ι → G
  | [] => one
  | a :: ls => gmul (wt v a) (eval v ls)

def atom {ι : Type} (a : ι) : Word ι := [(a, false)]

def negWord {ι : Type} : Word ι → Word ι
  | [] => []
  | (a, s) :: w => negWord w ++ [(a, !s)]

def comm {ι : Type} (p q : Word ι) : Word ι := p ++ q ++ negWord p ++ negWord q

theorem eval_append {ι : Type} (v : ι → G) (p q : Word ι) :
    eval v (p ++ q) = gmul (eval v p) (eval v q) := by
  induction p with
  | nil => exact (lid _).symm
  | cons a p ih => simp only [List.cons_append, eval, ih, assoc]

theorem atom_val {ι : Type} (v : ι → G) (n : ι) : eval v (atom n) = v n := rid _

theorem tok_inv {ι : Type} (v : ι → G) (a : ι) (s : Bool) : wt v (a, !s) = ginv (wt v (a, s)) := by
  cases s
  · rfl
  · have h (x : G) : ginv (ginv x) = x := by cases x; decide +revert
    exact (h _).symm

theorem eval_neg {ι : Type} (v : ι → G) (w : Word ι) : eval v (negWord w) = ginv (eval v w) := by
  induction w with
  | nil => rfl
  | cons x w ih =>
    rcases x with ⟨a, s⟩
    rw [negWord, eval_append, ih, eval, eval, rid, tok_inv, eval, inv_prod]

theorem eval_comm {ι : Type} (v : ι → G) (p q : Word ι) : eval v (comm p q) = center (det (eval v p) (eval v q)) := by
  unfold comm; rw [eval_append, eval_append, eval_append, eval_neg, eval_neg, assoc]; exact comm_form _ _

structure Row (ι : Type) where
  w : Word ι
  out : G

def holds {ι : Type} (v : ι → G) (rs : List (Row ι)) : Prop := ∀ e, e ∈ rs → eval v e.w = e.out

def feasible {ι : Type} (rs : List (Row ι)) : Prop := ∃ v, holds v rs

def zero {ι : Type} (w : Word ι) : Row ι := ⟨w, one⟩

theorem holds_cons {ι : Type} (v : ι → G) (e : Row ι) (rs : List (Row ι)) :
    holds v (e :: rs) ↔ eval v e.w = e.out ∧ holds v rs := by
  constructor
  · intro h; exact ⟨h e List.mem_cons_self, fun a ha => h a (List.mem_cons_of_mem _ ha)⟩
  · intro ⟨h, hr⟩ a ha; rcases List.mem_cons.mp ha with e|k
    · subst a; exact h
    · exact hr a k

theorem holds_append {ι : Type} (v : ι → G) (xs ys : List (Row ι)) :
    holds v (xs ++ ys) ↔ holds v xs ∧ holds v ys := by
  constructor
  · intro h; exact ⟨fun a ha => h _ (List.mem_append_left _ ha), fun a ha => h _ (List.mem_append_right _ ha)⟩
  · intro ⟨hx, hy⟩ a ha; rcases List.mem_append.mp ha with e|e
    · exact hx _ e
    · exact hy _ e

def gateVal (u : Bool) (a p : G) : G := if u then gmul a p else p

theorem twist_bit (a b p : G) (u : Bool) (hf : det a b = true) :
    det (gateVal u a p) b = (det p b ^^ u) := by
  cases a; cases b; cases p; cases u <;> revert hf <;> decide +revert

theorem gate_factor (a b p q : G) (u v : Bool) (hf : det a b = true) (hp : det q b = false) :
    det (gateVal u a p) (gateVal v b q) = ((det p b ^^ u) && (det a q ^^ v)) := by
  cases a with | mk a1 a2 a3 =>
    cases b with | mk b1 b2 b3 =>
      cases p with | mk p1 p2 p3 =>
        cases q with | mk q1 q2 q3 =>
          change ((a1 && b2) ^^ (a2 && b1)) = true at hf
          change ((q1 && b2) ^^ (q2 && b1)) = false at hp
          cases u <;> cases v <;> simp only [gateVal, det, gmul, Bool.false_eq_true, if_false, if_true] <;>
            revert hf hp <;> clear a3 b3 p3 q3 <;> decide +revert

end PNP.ThreeUse
