import PNP.SignedTernary.CNF.Clause

namespace PNP.SignedTernary.CNF
open PNP.SignedTernary.Field

@[reducible] def Bank {α : Type} : List (List (Form α)) → Type
  | [] => Empty
  | c::cs => Sum (Aux c.length) (Bank cs)

def headEmbed {α : Type} {c : List (Form α)} {cs : List (List (Form α))} :
    Sum α (Aux c.length) → Sum α (Bank (c::cs))
  | .inl a => .inl a
  | .inr i => .inr (.inl i)

def restEmbed {α : Type} {c : List (Form α)} {cs : List (List (Form α))} :
    Sum α (Bank cs) → Sum α (Bank (c::cs))
  | .inl a => .inl a
  | .inr i => .inr (.inr i)

theorem env_head {α : Type} {c : List (Form α)} {cs : List (List (Form α))}
    (base : α → F3) (aux : Bank (c::cs) → F3) :
    (fun i => env base aux (headEmbed i)) = env base (fun i => aux (.inl i)) := by
  funext i
  cases i <;> rfl

theorem env_rest {α : Type} {c : List (Form α)} {cs : List (List (Form α))}
    (base : α → F3) (aux : Bank (c::cs) → F3) :
    (fun i => env base aux (restEmbed i)) = env base (fun i => aux (.inr i)) := by
  funext i
  cases i <;> rfl

def compileBank {α : Type} (gauge : α) :
    (cs : List (List (Form α))) → List (Form (Sum α (Bank cs)))
  | [] => []
  | c::cs =>
      sub (rename headEmbed (compileClause gauge c).1) (.var (.inl gauge)) ::
      ((compileClause gauge c).2.map (rename headEmbed) ++
        (compileBank gauge cs).map (rename restEmbed))

def BankBits {α : Type} (g : F3) (base : α → F3) : List (List (Form α)) → Prop
  | [] => True
  | c::cs => Bits g base c ∧ BankBits g base cs

def BankTruth {α : Type} (base : α → F3) : List (List (Form α)) → Prop
  | [] => True
  | c::cs => truth base c = true ∧ BankTruth base cs

def canonicalBank {α : Type} (g : F3) (base : α → F3) :
    (cs : List (List (Form α))) → Bank cs → F3
  | [], i => nomatch i
  | c::_, .inl i => canonicalAux g base c i
  | _::cs, .inr i => canonicalBank g base cs i

theorem canonical_bank_signed {α : Type} (g : F3) (hg : g ≠ .z) (base : α → F3)
    (cs : List (List (Form α))) : ∀ i, canonicalBank g base cs i ≠ .z := by
  induction cs with
  | nil => intro i; nomatch i
  | cons c cs ih =>
    intro i
    cases i with
    | inl i => exact canonical_signed g hg base c i
    | inr i => exact ih i

theorem bit_target_iff (g : F3) (hg : g ≠ .z) (b : Bool) :
    add (bit g b) (neg g) = .z ↔ b = true := by
  cases g <;> cases b <;> simp_all [bit,add,neg]

theorem bank_sound {α : Type} (gauge : α) (base : α → F3)
    (cs : List (List (Form α))) (aux : Bank cs → F3)
    (hg : base gauge ≠ .z) (hb : BankBits (base gauge) base cs)
    (hs : ∀ i, aux i ≠ .z) (hr : RowsHold (env base aux) (compileBank gauge cs)) :
    BankTruth base cs ∧ ∀ i, aux i = canonicalBank (base gauge) base cs i := by
  induction cs with
  | nil => exact ⟨True.intro,fun i => nomatch i⟩
  | cons c cs ih =>
    have hsplit := (rows_append (env base aux) _ _).1 hr.2
    have hc := hsplit.1
    have ht := hsplit.2
    rw [rows_rename,env_head] at hc
    rw [rows_rename,env_rest] at ht
    obtain ⟨hval,hunique⟩ := clause_sound gauge base c (fun i => aux (.inl i)) hg hb.1
      (fun i => hs (.inl i)) hc
    obtain ⟨htruth,hut⟩ := ih (fun i => aux (.inr i)) hb.2 (fun i => hs (.inr i)) ht
    have hterm := hr.1
    simp only [sub,eval,eval_rename] at hterm
    rw [env_head] at hterm
    change add (eval (env base (fun i => aux (.inl i))) (compileClause gauge c).1)
      (neg (base gauge)) = .z at hterm
    rw [hval] at hterm
    refine ⟨⟨(bit_target_iff _ hg _).1 hterm,htruth⟩,?_⟩
    intro i
    cases i with
    | inl i => exact hunique i
    | inr i => exact hut i

theorem bank_complete {α : Type} (gauge : α) (base : α → F3)
    (cs : List (List (Form α))) (hg : base gauge ≠ .z)
    (hb : BankBits (base gauge) base cs) (ht : BankTruth base cs) :
    RowsHold (env base (canonicalBank (base gauge) base cs)) (compileBank gauge cs) := by
  induction cs with
  | nil => exact True.intro
  | cons c cs ih =>
    have hc := clause_complete gauge base c hg hb.1
    have hv := (clause_sound gauge base c (canonicalAux (base gauge) base c) hg hb.1
      (canonical_signed _ hg base c) hc).1
    refine ⟨?_,?_⟩
    · simp only [sub,eval,eval_rename]
      rw [env_head]
      change add (eval (env base (canonicalAux (base gauge) base c)) (compileClause gauge c).1)
        (neg (base gauge)) = .z
      rw [hv]
      exact (bit_target_iff _ hg _).2 ht.1
    · apply (rows_append _ _ _).2
      constructor
      · rw [rows_rename,env_head]
        exact hc
      · rw [rows_rename,env_rest]
        exact ih hb.2 ht.2

def occurrences {α : Type} : List (List α) → Nat
  | [] => 0
  | c::cs => c.length + occurrences cs

theorem bank_row_count {α : Type} (gauge : α) (cs : List (List (Form α))) :
    (compileBank gauge cs).length = 2*occurrences cs + cs.length := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    simp only [compileBank,List.length_cons,List.length_append,List.length_map,
      clause_row_count,occurrences,ih]
    omega

theorem pair_row_count {α : Type} (g : Form α) (rs : List (Form α)) :
    (pairRows g rs).length = 2*rs.length := by
  induction rs with
  | nil => rfl
  | cons r rs ih => simp only [pairRows,List.length_cons,ih]; omega

end PNP.SignedTernary.CNF
