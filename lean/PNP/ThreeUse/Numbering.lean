import PNP.ThreeUse.Codec
import PNP.ThreeUse.DistinctPorts

/-!
# Replacing structural occurrences by numeric slots

Prove that the numbering preserves all words and constraints in both directions and gives an assignment on the original source coordinates.
-/

set_option autoImplicit false

namespace PNP.ThreeUse.Encoding
open PNP.Concrete

def relabelW {α β : Type} (f : α → β) (w : Word α) : Word β := w.map fun t => (f t.1, t.2)

def relabel {α β : Type} (f : α → β) (rs : List (Row α)) : List (Row β) := rs.map fun r => ⟨relabelW f r.w, r.out⟩

theorem eval_relabel {α β : Type} (f : α → β) (v : β → G) (w : Word α) :
    eval v (relabelW f w) = eval (fun p => v (f p)) w := by
  induction w with
  | nil => rfl
  | cons t ts ih => change gmul (wt v (f t.1, t.2)) (eval v (relabelW f ts)) = gmul (wt (fun p => v (f p)) t) _; rw [ih]; rfl

theorem holds_relabel {α β : Type} (f : α → β) (rs : List (Row α)) (v : β → G) :
    holds v (relabel f rs) ↔ holds (fun p => v (f p)) rs := by
  induction rs with
  | nil => constructor <;> intro _ e he <;> cases he
  | cons r rs ih =>
    change holds _ (⟨relabelW f r.w, r.out⟩ :: relabel f rs) ↔ _
    rw [holds_cons, holds_cons, ih]
    exact and_congr (Iff.of_eq (congrArg (fun g => g = r.out) (eval_relabel f v r.w))) Iff.rfl

theorem renamed_labels_w {α β : Type} (f : α → β) (w : Word α) :
    (relabelW f w).map Prod.fst = (w.map Prod.fst).map f := by
  induction w with
  | nil => rfl
  | cons x xs ih => exact congrArg (List.cons (f x.1)) ih

theorem renamed_labels {α β : Type} (f : α → β) (rs : List (Row α)) :
    labels (relabel f rs) = (labels rs).map f := by
  induction rs with
  | nil => rfl
  | cons r rs ih =>
    change ((relabelW f r.w).map Prod.fst) ++ labels (relabel f rs) = (r.w.map Prod.fst ++ labels rs).map f
    rw [List.map_append, renamed_labels_w, ih]

theorem same_word_slot {α : Type} (n : Nat) (w : Word α) {p q : Port α}
    (hp : p ∈ (tagWord n w).map Prod.fst) (hq : q ∈ (tagWord n w).map Prod.fst) (e : p.2 = q.2) : p = q := by
  induction w with
  | nil => cases hp
  | cons z w ih =>
    rcases z with ⟨a, s⟩
    change p ∈ (a, n+w.length) :: (tagWord n w).map Prod.fst at hp
    change q ∈ (a, n+w.length) :: (tagWord n w).map Prod.fst at hq
    rcases List.mem_cons.mp hp with p1|p1 <;> rcases List.mem_cons.mp hq with q1|q1
    · exact p1.trans q1.symm
    · subst p; have z := (tagBounds n w _ q1).2; change n+w.length = q.2 at e; exfalso; omega
    · subst q; have z := (tagBounds n w _ p1).2; change p.2 = n+w.length at e; exfalso; omega
    · exact ih p1 q1

theorem same_slot {α : Type} (rs : List (Row α)) {p q : Port α}
    (hp : p ∈ labels (tagged rs)) (hq : q ∈ labels (tagged rs)) (e : p.2 = q.2) : p = q := by
  induction rs with
  | nil => cases hp
  | cons r rs ih =>
    rcases List.mem_append.mp hp with p1|p1 <;> rcases List.mem_append.mp hq with q1|q1
    · exact same_word_slot _ _ p1 q1 e
    · have z := (tagBounds _ _ _ p1).1; have t := allBounds rs _ q1; exfalso; omega
    · have z := (tagBounds _ _ _ q1).1; have t := allBounds rs _ p1; exfalso; omega
    · exact ih p1 q1

theorem supported {α : Type} [DecidableEq α] (rs : List (Row α)) {p : Port α}
    (h : p ∈ labels (splitRows rs)) : p ∈ labels (tagged rs) := by
  by_cases e : p ∈ labels (tagged rs)
  · exact e
  · have c := third_uses rs p; rw [if_neg e] at c
    have k := (hit_mem p _).mp h; exfalso; omega

def pack (bits : BitString) : Packet :=
  ⟨slots (macroRows (normalized bits)), relabel Prod.snd (targetRows bits)⟩

def compile (bits : BitString) : BitString := encode (pack bits)

theorem pack_range (bits : BitString) : ranged (pack bits) = true := by
  apply (ranged_iff _).mpr; intro i hi
  change i ∈ labels (relabel Prod.snd (targetRows bits)) at hi
  rw [renamed_labels] at hi
  obtain ⟨p, hp, e⟩ := List.mem_map.mp hi
  subst i; exact allBounds _ _ (supported _ hp)

def bySlot {α : Type} (v : Port α → G) (i : Nat) : List (Port α) → G
  | [] => one
  | p :: ps => if p.2 = i then v p else bySlot v i ps

theorem bySlot_agrees {α : Type} (v : Port α → G) (ps : List (Port α)) {p : Port α}
    (hp : p ∈ ps) (u : ∀ q, q ∈ ps → q.2 = p.2 → q = p) : bySlot v p.2 ps = v p := by
  induction ps with
  | nil => cases hp
  | cons t ts ih =>
    rw [bySlot]; by_cases e : t.2 = p.2
    · rw [if_pos e, u _ List.mem_cons_self e]
    · rw [if_neg e]; apply ih
      · rcases List.mem_cons.mp hp with eq|k
        · exact False.elim (e (congrArg Prod.snd eq.symm))
        · exact k
      · intro q h; exact u _ (List.mem_cons_of_mem _ h)

theorem holds_agree {α : Type} (rs : List (Row α)) (v u : α → G) (h : ∀ p, p ∈ labels rs → v p = u p)
    (ok : holds u rs) : holds v rs := by
  induction rs with
  | nil => intro e he; cases he
  | cons r rs ih =>
    obtain ⟨rr, rest⟩ := (holds_cons _ _ _).mp ok
    apply (holds_cons _ _ _).mpr; constructor
    · exact (eval_agree _ _ _ (fun p hp => h _ (List.mem_append_left _ hp))).trans rr
    · exact ih (fun p hp => h _ (List.mem_append_right _ hp)) rest

theorem slot_iff (bits : BitString) : feasible (pack bits).rows ↔ feasible (targetRows bits) := by
  let ts := labels (tagged (macroRows (normalized bits)))
  constructor
  · rintro ⟨v, h⟩; exact ⟨_, (holds_relabel _ _ v).mp h⟩
  · rintro ⟨v, h⟩
    let u := fun i => bySlot v i ts
    refine ⟨u, (holds_relabel _ _ _).mpr (holds_agree _ _ _ ?_ h)⟩
    intro p hp
    have g : p ∈ ts := supported _ hp
    exact bySlot_agrees _ _ g (fun q hq e => same_slot _ hq g e)

def WordSAT (bs : BitString) : Prop := ∃ p, decode bs = some p ∧ finiteFeasible p.rows

theorem byte_iff (bits : BitString) : CNFSAT bits ↔ WordSAT (compile bits) := by
  have dec : decode (compile bits) = some (pack bits) := decode_spec _ (pack_range _)
  have cf : CNFSAT bits ↔ finiteFeasible (pack bits).rows := ((raw_iff _).trans (slot_iff bits).symm).trans (finite_iff _)
  constructor
  · intro h; exact ⟨_, dec, cf.mp h⟩
  · rintro ⟨p, a, b⟩; rw [dec] at a; cases a; exact cf.mpr b

theorem numbered_replay (bits : BitString) (v : Nat → G) (ok : holds v (pack bits).rows) :
    ∃ f, decodeEncodedCNF bits = some f ∧
      f.Satisfied (sourceWord bits (fun p => v p.2)) := original_replay _ _ ((holds_relabel _ _ v).mp ok)

end PNP.ThreeUse.Encoding
