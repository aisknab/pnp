import PNP.SignedTernary.Field

namespace PNP.SignedTernary.CNF
open PNP.SignedTernary.Field

inductive Form (α : Type) where
  | zero
  | var (i : α)
  | add (f g : Form α)
  | neg (f : Form α)

def eval {α : Type} (w : α → F3) : Form α → F3
  | .zero => .z
  | .var i => w i
  | .add f g => add (eval w f) (eval w g)
  | .neg f => neg (eval w f)

def rename {α β : Type} (f : α → β) : Form α → Form β
  | .zero => .zero
  | .var i => .var (f i)
  | .add a b => .add (rename f a) (rename f b)
  | .neg a => .neg (rename f a)

theorem eval_rename {α β : Type} (f : α → β) (w : β → F3) (p : Form α) :
    eval w (rename f p) = eval (fun i => w (f i)) p := by
  induction p with
  | zero => rfl
  | var i => rfl
  | add a b ha hb => simp only [rename,eval,ha,hb]
  | neg a ha => simp only [rename,eval,ha]

def sub {α : Type} (f g : Form α) : Form α := .add f (.neg g)

def RowsHold {α : Type} (w : α → F3) : List (Form α) → Prop
  | [] => True
  | r::rs => eval w r = .z ∧ RowsHold w rs

def RowsNonzero {α : Type} (w : α → F3) : List (Form α) → Prop
  | [] => True
  | r::rs => eval w r ≠ .z ∧ RowsNonzero w rs

theorem rows_rename {α β : Type} (f : α → β) (w : β → F3) (rs : List (Form α)) :
    RowsHold w (rs.map (rename f)) ↔ RowsHold (fun i => w (f i)) rs := by
  induction rs with
  | nil => exact Iff.rfl
  | cons r rs ih => simp only [List.map_cons,RowsHold,eval_rename,ih]

theorem rows_append {α : Type} (w : α → F3) (rs ts : List (Form α)) :
    RowsHold w (rs++ts) ↔ RowsHold w rs ∧ RowsHold w ts := by
  induction rs with
  | nil => exact ⟨fun h => ⟨True.intro,h⟩,fun h => h.2⟩
  | cons r rs ih =>
    change (eval w r = .z ∧ RowsHold w (rs++ts)) ↔
      (eval w r = .z ∧ RowsHold w rs) ∧ RowsHold w ts
    rw [ih]
    exact ⟨fun h => ⟨⟨h.1,h.2.1⟩,h.2.2⟩,fun h => ⟨h.1.1,h.1.2,h.2⟩⟩

def bit (g : F3) (b : Bool) : F3 := if b then g else .z

def encode (g : F3) (b : Bool) : F3 := add g (bit g b)

def readBit (g x : F3) : F3 := add x (neg g)

def truthBit (x : F3) : Bool := x != .z

def decode (g x : F3) : Bool := x != g

theorem encode_nonzero (g : F3) (hg : g ≠ .z) (b : Bool) : encode g b ≠ .z := by
  cases g <;> cases b <;> simp_all [encode,bit,add]

theorem read_encode (g : F3) (b : Bool) : readBit g (encode g b) = bit g b := by
  cases g <;> cases b <;> rfl

theorem encode_decode (g x : F3) (hg : g ≠ .z) (hx : x ≠ .z) :
    encode g (decode g x) = x := by
  cases g <;> cases x <;> simp_all [encode,decode,bit,add]

theorem bit_truth (g x : F3) (hg : g ≠ .z) (h : x = .z ∨ x = g) :
    bit g (truthBit x) = x := by
  cases g <;> cases x <;> simp_all [bit,truthBit]

theorem paired_scalar (g x : F3) (hg : g ≠ .z) :
    (add x g ≠ .z ∧ add x (neg g) ≠ .z) ↔ x = .z := by
  cases g <;> cases x <;> simp_all [add,neg]

def pairRows {α : Type} (g : Form α) : List (Form α) → List (Form α)
  | [] => []
  | r::rs => .add r g :: sub r g :: pairRows g rs

theorem paired_rows_iff {α : Type} (w : α → F3) (g : Form α)
    (hg : eval w g ≠ .z) (rs : List (Form α)) :
    RowsNonzero w (pairRows g rs) ↔ RowsHold w rs := by
  induction rs with
  | nil => exact Iff.rfl
  | cons r rs ih =>
    change (add (eval w r) (eval w g) ≠ .z ∧
      add (eval w r) (neg (eval w g)) ≠ .z ∧ RowsNonzero w (pairRows g rs)) ↔
      (eval w r = .z ∧ RowsHold w rs)
    constructor
    · intro h
      exact ⟨(paired_scalar _ _ hg).1 ⟨h.1,h.2.1⟩,ih.1 h.2.2⟩
    · intro h
      have hp := (paired_scalar _ _ hg).2 h.1
      exact ⟨hp.1,hp.2,ih.2 h.2⟩

inductive Slot where
  | out | both | diff
  deriving DecidableEq, Repr

@[reducible] def Aux : Nat → Type
  | 0 => Empty
  | k+1 => Sum Slot (Aux k)

def env {α β : Type} (base : α → F3) (aux : β → F3) : Sum α β → F3
  | .inl a => base a
  | .inr i => aux i

def tailEmbed {α : Type} {k : Nat} : Sum α (Aux k) → Sum α (Aux (k+1))
  | .inl a => .inl a
  | .inr i => .inr (.inr i)

theorem env_tail {α : Type} {k : Nat} (base : α → F3) (aux : Aux (k+1) → F3) :
    (fun i => env base aux (tailEmbed i)) = env base (fun i => aux (.inr i)) := by
  funext i
  cases i <;> rfl

def gateOne (g a b zo ta : F3) : F3 :=
  add (add a b) (neg (add (readBit g zo) (readBit g ta)))

def gateTwo (g zo ta h : F3) : F3 :=
  add (readBit g zo) (neg (add (readBit g ta) (readBit g h)))

theorem gate_exact (g : F3) (hg : g ≠ .z) (a b : Bool) (zo ta h : F3)
    (hz : zo ≠ .z) (ht : ta ≠ .z) (hh : h ≠ .z) :
    (gateOne g (bit g a) (bit g b) zo ta = .z ∧ gateTwo g zo ta h = .z) ↔
    (zo = encode g (a || b) ∧ ta = encode g (a && b) ∧ h = encode g (Bool.xor a b)) := by
  cases g <;> cases a <;> cases b <;> cases zo <;> cases ta <;> cases h <;>
    simp_all [gateOne,gateTwo,readBit,encode,bit,add,neg,Bool.xor]

def compileClause {α : Type} (gauge : α) :
    (inputs : List (Form α)) →
      Form (Sum α (Aux inputs.length)) × List (Form (Sum α (Aux inputs.length)))
  | [] => (.zero,[])
  | a::as =>
      let tail := compileClause gauge as
      let g : Form (Sum α (Aux (as.length+1))) := .var (.inl gauge)
      let zo : Form (Sum α (Aux (as.length+1))) := .var (.inr (.inl .out))
      let ta : Form (Sum α (Aux (as.length+1))) := .var (.inr (.inl .both))
      let h : Form (Sum α (Aux (as.length+1))) := .var (.inr (.inl .diff))
      let b := rename tailEmbed tail.1
      (sub zo g,
       sub (.add (rename Sum.inl a) b) (.add (sub zo g) (sub ta g)) ::
       sub (sub zo g) (.add (sub ta g) (sub h g)) ::
       tail.2.map (rename tailEmbed))

def truth {α : Type} (base : α → F3) : List (Form α) → Bool
  | [] => false
  | f::fs => truthBit (eval base f) || truth base fs

def Bits {α : Type} (g : F3) (base : α → F3) : List (Form α) → Prop
  | [] => True
  | f::fs => (eval base f = .z ∨ eval base f = g) ∧ Bits g base fs

def canonicalAux {α : Type} (g : F3) (base : α → F3) :
    (inputs : List (Form α)) → Aux inputs.length → F3
  | [], i => nomatch i
  | a::as, .inl .out => encode g (truthBit (eval base a) || truth base as)
  | a::as, .inl .both => encode g (truthBit (eval base a) && truth base as)
  | a::as, .inl .diff => encode g (Bool.xor (truthBit (eval base a)) (truth base as))
  | _::as, .inr i => canonicalAux g base as i

theorem canonical_signed {α : Type} (g : F3) (hg : g ≠ .z) (base : α → F3)
    (inputs : List (Form α)) : ∀ i, canonicalAux g base inputs i ≠ .z := by
  induction inputs with
  | nil => intro i; nomatch i
  | cons a as ih =>
    intro i
    cases i with
    | inl s => cases s <;> exact encode_nonzero g hg _
    | inr i => exact ih i

theorem clause_sound {α : Type} (gauge : α) (base : α → F3)
    (inputs : List (Form α)) (aux : Aux inputs.length → F3)
    (hg : base gauge ≠ .z) (hb : Bits (base gauge) base inputs)
    (hs : ∀ i, aux i ≠ .z)
    (hr : RowsHold (env base aux) (compileClause gauge inputs).2) :
    eval (env base aux) (compileClause gauge inputs).1 = bit (base gauge) (truth base inputs) ∧
      ∀ i, aux i = canonicalAux (base gauge) base inputs i := by
  induction inputs with
  | nil => exact ⟨rfl,fun i => nomatch i⟩
  | cons a as ih =>
    have ht : RowsHold (env base (fun i => aux (.inr i))) (compileClause gauge as).2 := by
      have hh := hr.2.2
      rw [rows_rename,env_tail] at hh
      exact hh
    obtain ⟨hval,hunique⟩ := ih (fun i => aux (.inr i)) hb.2 (fun i => hs (.inr i)) ht
    have hgate : gateOne (base gauge) (bit (base gauge) (truthBit (eval base a)))
        (bit (base gauge) (truth base as)) (aux (.inl .out)) (aux (.inl .both)) = .z ∧
      gateTwo (base gauge) (aux (.inl .out)) (aux (.inl .both)) (aux (.inl .diff)) = .z := by
      have h1 := hr.1
      have h2 := hr.2.1
      simp only [sub,eval,eval_rename] at h1 h2
      rw [env_tail] at h1
      change gateOne (base gauge) (eval base a)
        (eval (env base (fun i => aux (.inr i))) (compileClause gauge as).1)
        (aux (.inl .out)) (aux (.inl .both)) = .z at h1
      rw [hval,← bit_truth _ _ hg hb.1] at h1
      exact ⟨h1,h2⟩
    obtain ⟨hz,ht,hh⟩ := (gate_exact _ hg _ _ _ _ _ (hs (.inl .out))
      (hs (.inl .both)) (hs (.inl .diff))).1 hgate
    constructor
    · change readBit (base gauge) (aux (.inl .out)) = _
      rw [hz,read_encode]
      rfl
    · intro i
      cases i with
      | inl s => cases s <;> assumption
      | inr i => exact hunique i

theorem clause_complete {α : Type} (gauge : α) (base : α → F3)
    (inputs : List (Form α)) (hg : base gauge ≠ .z) (hb : Bits (base gauge) base inputs) :
    RowsHold (env base (canonicalAux (base gauge) base inputs)) (compileClause gauge inputs).2 := by
  induction inputs with
  | nil => exact True.intro
  | cons a as ih =>
    have hr := ih hb.2
    have ht := (clause_sound gauge base as (canonicalAux (base gauge) base as) hg hb.2
      (canonical_signed _ hg base as) hr).1
    have hgate := (gate_exact (base gauge) hg (truthBit (eval base a)) (truth base as)
      _ _ _ (encode_nonzero _ hg _) (encode_nonzero _ hg _) (encode_nonzero _ hg _)).2
        ⟨rfl,rfl,rfl⟩
    refine ⟨?_,?_,?_⟩
    · simp only [sub,eval,eval_rename]
      rw [env_tail]
      change gateOne (base gauge) (eval base a)
        (eval (env base (canonicalAux (base gauge) base as)) (compileClause gauge as).1)
        _ _ = .z
      rw [ht,← bit_truth _ _ hg hb.1]
      exact hgate.1
    · exact hgate.2
    · rw [rows_rename,env_tail]
      exact hr

theorem clause_row_count {α : Type} (gauge : α) (inputs : List (Form α)) :
    (compileClause gauge inputs).2.length = 2*inputs.length := by
  induction inputs with
  | nil => rfl
  | cons a as ih =>
    simp only [compileClause,List.length_cons,List.length_map,ih]
    omega

end PNP.SignedTernary.CNF
