import PNP.ThreeUse.Group

/-!
# Commutator gates for clause failures

The distinguished commutator selects an independent frame. With that same frame, word equations multiply the failure bits of a clause; the converse reads an original Boolean assignment from every solution.
-/

set_option autoImplicit false

namespace PNP.ThreeUse

structure Lit where
  i : Nat
  pos : Bool
deriving DecidableEq, Repr

inductive Name where
  | A | B | p (i : Nat) | q (i : Nat) | acc (row : Nat) (past : List Lit)
deriving DecidableEq, Repr

abbrev Sig := Name × Bool

def framed (v : Name → G) : Prop := det (v .A) (v .B) = true

def project (v : Name → G) (i : Nat) : Bool := det (v (.p i)) (v .B)

def bit (v : Name → G) (p : Sig) : Bool := det (v p.1) (v .B) ^^ p.2

def fals (h : Nat → Bool) (l : Lit) : Bool := h l.i ^^ l.pos

def bads (h : Nat → Bool) : List Lit → Bool
  | [] => true
  | l :: ls => fals h l && bads h ls

def twist (base n : Name) (t : Bool) : Word Name := if t then atom base ++ atom n else atom n

theorem twist_eval (v : Name → G) (a n : Name) (u : Bool) :
    eval v (twist a n u) = gateVal u (v a) (v n) := by
  cases u <;> simp only [twist, gateVal, Bool.false_eq_true, if_false, if_true, atom_val, eval_append]

def frameW : Word Name := comm (atom .A) (atom .B)

def frame : Row Name := ⟨frameW, mark⟩

def link1 (i : Nat) : Word Name := comm (atom (.q i)) (atom .B)

def link2 (i : Nat) : Word Name := comm (atom .A) (atom (.q i)) ++ comm (atom (.p i)) (atom .B)

def bindOK (v : Name → G) (i : Nat) : Prop :=
  det (v (.q i)) (v .B) = false ∧ det (v .A) (v (.q i)) = project v i

theorem center_zero (s : Bool) : center s = one ↔ s = false := center_inj _ _

theorem pair_zero (a b : Bool) : center (a ^^ b) = one ↔ a = b := by cases a <;> cases b <;> decide

theorem frame_eq (v : Name → G) : eval v frameW = mark ↔ framed v := by
  unfold frameW framed; rw [eval_comm, atom_val, atom_val]; exact center_inj _ _

theorem links (v : Name → G) (i : Nat) :
    (eval v (link1 i) = one ∧ eval v (link2 i) = one) ↔ bindOK v i := by
  unfold link1 link2 bindOK project
  simp only [eval_append, eval_comm, atom_val, centermul]
  rw [pair_zero, center_zero]

def pin (s : Sig) : Word Name := comm (twist .A s.1 s.2) (atom .B)

def times (s : Sig) (l : Lit) : Word Name := comm (twist .A s.1 s.2) (twist .B (.q l.i) l.pos)

def gate (s : Sig) (l : Lit) (out : Name) : Word Name := times s l ++ comm (atom out) (atom .B)

theorem pin_eq (v : Name → G) (hf : framed v) (s : Sig) :
    eval v (pin s) = one ↔ bit v s = false := by
  unfold pin bit; rw [eval_comm, twist_eval, atom_val, twist_bit _ _ _ _ hf, center_zero]

theorem gate_eq (v : Name → G) (hf : framed v) (s : Sig) (l : Lit) (hb : bindOK v l.i) (out : Name) :
    eval v (gate s l out) = one ↔ det (v out) (v .B) = (bit v s && fals (project v) l) := by
  unfold gate times bit fals
  rw [eval_append, eval_comm, eval_comm, twist_eval, twist_eval, atom_val, atom_val,
    gate_factor _ _ _ _ _ _ hf hb.1, hb.2, centermul, pair_zero, eq_comm]

/-- A concrete word per product, followed by a unary zero check on the final prefix.
The structural labels carry no assigned values. -/
def walk (row : Nat) (past : List Lit) (s : Sig) : List Lit → List (Row Name)
  | [] => [zero (pin s)]
  | l :: ls =>
    let out := Name.acc row (l :: past)
    zero (link1 l.i) :: zero (link2 l.i) :: zero (gate s l out) :: walk row (l :: past) (out, false) ls

def clause (row : Nat) : List Lit → List (Row Name)
  | [] => [zero frameW]
  | l :: ls => walk row [l] (.p l.i, l.pos) ls

def bank : List (List Lit) → List (Row Name)
  | [] => []
  | c :: cs => clause cs.length c ++ bank cs

def macroRows (cs : List (List Lit)) : List (Row Name) := frame :: bank cs

def source (h : Nat → Bool) : List (List Lit) → Prop
  | [] => True
  | c :: cs => bads h c = false ∧ source h cs

theorem narrow (v : Name → G) (row : Nat) (p : List Lit) (s : Sig) (ls : List Lit) (hf : framed v)
    (ok : holds v (walk row p s ls)) : (bit v s && bads (project v) ls) = false := by
  induction ls generalizing p s with
  | nil =>
    have h : eval v (pin s) = one := (holds_cons _ _ _).mp ok |>.1
    rw [(pin_eq _ hf _).mp h]; rfl
  | cons l ls ih =>
    obtain ⟨b1, rest⟩ := (holds_cons _ _ _).mp ok
    obtain ⟨b2, rest⟩ := (holds_cons _ _ _).mp rest
    obtain ⟨gateOk, rest⟩ := (holds_cons _ _ _).mp rest
    have hb : bindOK v l.i := (links _ _).mp ⟨b1, b2⟩
    have hout := (gate_eq _ hf _ _ hb _).mp gateOk
    have use := ih _ _ rest
    change ((det (v (.acc row (l :: p))) (v .B) ^^ false) && bads (project v) ls) = false at use
    rw [Bool.xor_false, hout] at use
    change (bit v s && (fals (project v) l && bads (project v) ls)) = false
    rw [←Bool.and_assoc]; exact use

theorem row_sound (v : Name → G) (r : Nat) (c : List Lit) (hf : framed v) (ok : holds v (clause r c)) :
    bads (project v) c = false := by
  cases c with
  | nil =>
    have h : eval v frameW = one := (holds_cons _ _ _).mp ok |>.1
    rw [(frame_eq _).mpr hf] at h; contradiction
  | cons l ls => exact narrow _ _ _ _ _ hf ok

def send (h : Nat → Bool) : Name → G
  | .A => ⟨true, false, false⟩
  | .B => ⟨false, true, false⟩
  | .p i => ⟨h i, false, false⟩
  | .q i => ⟨false, h i, false⟩
  | .acc _ p => ⟨bads h p, false, false⟩

theorem sender_proj (h : Nat → Bool) : project (send h) = h := by
  funext i; change ((h i && true) ^^ (false && false)) = h i
  cases h i <;> rfl

theorem sender_frame (h : Nat → Bool) : framed (send h) := rfl

theorem sender_bind (h : Nat → Bool) (i : Nat) : bindOK (send h) i := by
  change (((false && true) ^^ (h i && false)) = false) ∧ (((true && h i) ^^ (false && false)) = ((h i && true) ^^ (false && false)))
  cases h i <;> exact ⟨rfl, rfl⟩

theorem sender_acc (h : Nat → Bool) (r : Nat) (p : List Lit) :
    det (send h (.acc r p)) (send h .B) = bads h p := by
  change ((bads h p && true) ^^ (false && false)) = bads h p
  cases bads h p <;> rfl

theorem wide (h : Nat → Bool) (r : Nat) (p : List Lit) (s : Sig) (ls : List Lit)
    (pref : bit (send h) s = bads h p) (good : (bads h p && bads h ls) = false) :
    holds (send h) (walk r p s ls) := by
  induction ls generalizing p s with
  | nil =>
    apply (holds_cons _ _ _).mpr; constructor
    · apply (pin_eq _ (sender_frame _) _).mpr
      rw [pref]; simpa only [bads, Bool.and_true] using good
    · intro a ha; cases ha
  | cons l ls ih =>
    have hb := sender_bind h l.i
    obtain ⟨b1, b2⟩ := (links _ _).mpr hb
    apply (holds_cons _ _ _).mpr; refine ⟨b1, ?_⟩
    apply (holds_cons _ _ _).mpr; refine ⟨b2, ?_⟩
    apply (holds_cons _ _ _).mpr; constructor
    · apply (gate_eq _ (sender_frame _) _ _ hb _).mpr
      rw [sender_acc, sender_proj, pref, bads, Bool.and_comm]
    · apply ih
      · change (det (send h (.acc r (l :: p))) (send h .B) ^^ false) = _
        rw [Bool.xor_false, sender_acc]
      · change ((fals h l && bads h p) && bads h ls) = false
        rw [Bool.and_comm (fals h l), Bool.and_assoc]
        exact good

theorem row_complete (h : Nat → Bool) (r : Nat) (c : List Lit) (good : bads h c = false) :
    holds (send h) (clause r c) := by
  cases c with
  | nil => contradiction
  | cons l ls =>
    apply wide
    · change (project (send h) l.i ^^ l.pos) = (fals h l && true)
      rw [sender_proj, Bool.and_true]; rfl
    · change ((fals h l && true) && bads h ls) = false
      rw [Bool.and_true]; exact good

theorem bank_sound (v : Name → G) (cs : List (List Lit)) (hf : framed v) (ok : holds v (bank cs)) :
    source (project v) cs := by
  induction cs with
  | nil => trivial
  | cons c cs ih =>
    obtain ⟨h1, h2⟩ := (holds_append _ _ _).mp ok
    exact ⟨row_sound _ _ _ hf h1, ih h2⟩

theorem bank_complete (h : Nat → Bool) (cs : List (List Lit)) (good : source h cs) : holds (send h) (bank cs) := by
  induction cs with
  | nil => intro a ha; cases ha
  | cons c cs ih => exact (holds_append _ _ _).mpr ⟨row_complete _ _ _ good.1, ih good.2⟩

theorem macro_sound (v : Name → G) (cs : List (List Lit)) (ok : holds v (macroRows cs)) :
    source (project v) cs := by
  obtain ⟨f, hs⟩ := (holds_cons _ _ _).mp ok
  exact bank_sound _ _ ((frame_eq _).mp f) hs

theorem macro_complete (h : Nat → Bool) (cs : List (List Lit)) (good : source h cs) :
    holds (send h) (macroRows cs) := (holds_cons _ _ _).mpr ⟨(frame_eq _).mpr (sender_frame _), bank_complete _ _ good⟩

end PNP.ThreeUse
