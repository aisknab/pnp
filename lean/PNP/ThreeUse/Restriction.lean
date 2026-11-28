import PNP.ThreeUse.Numbering
import PNP.ThreeUse.Reduction

/-!
# The restricted target language

The declared numeric labels are all used, precisely three times each. The target predicate also checks distinct labels per word, the marker, and feasibility of the decoded rows.
-/

set_option autoImplicit false

namespace PNP.ThreeUse.Encoding
open PNP.Concrete

theorem port_in_word {α : Type} (n : Nat) (w : Word α) (i : Nat)
    (lo : n ≤ i) (hi : i<n+w.length) : ∃ a, (a, i) ∈ (tagWord n w).map Prod.fst := by
  induction w with
  | nil => change i<n+0 at hi; exfalso; omega
  | cons t w ih =>
    rcases t with ⟨a, s⟩
    by_cases h : i = n+w.length
    · subst i; exact ⟨a, List.mem_cons_self⟩
    · have b : i<n+w.length := by rw [List.length_cons] at hi; omega
      obtain ⟨q, e⟩ := ih b; exact ⟨q, List.mem_cons_of_mem _ e⟩

theorem port_in_bank {α : Type} (rs : List (Row α)) (i : Nat)
    (hi : i<slots rs) : ∃ a, (a, i) ∈ labels (tagged rs) := by
  induction rs with
  | nil => change i<0 at hi; cases hi
  | cons r rs ih =>
    by_cases e : i<slots rs
    · obtain ⟨a, h⟩ := ih e; exact ⟨a, List.mem_append_right _ h⟩
    · obtain ⟨a, h⟩ := port_in_word (slots rs) r.w i (by omega) (by change i<r.w.length+slots rs at hi; omega)
      exact ⟨a, List.mem_append_left _ h⟩

theorem hit_inj_map {α β : Type} [DecidableEq α] [DecidableEq β] (f : α → β) (xs : List α) (p : α)
    (ok : ∀ q, q ∈ xs → f q = f p → q = p) : hits (f p) (xs.map f) = hits p xs := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    rw [List.map_cons, hits, hits, ih (fun q hq => ok _ (List.mem_cons_of_mem _ hq))]
    by_cases e : a = p
    · subst a; rw [hit, if_pos rfl, hit, if_pos rfl]
    · have d : f a≠f p := fun yes => e (ok _ List.mem_cons_self yes)
      rw [hit, if_neg d, hit, if_neg e]

theorem row_ports {α : Type} (rs : List (Row α)) {r : Row α} (hr : r ∈ rs) {p : α}
    (hp : p ∈ r.w.map Prod.fst) : p ∈ labels rs := by
  induction rs with
  | nil => cases hr
  | cons e rs ih =>
    obtain h|h := List.mem_cons.mp hr
    · subst e; exact List.mem_append_left _ hp
    · exact List.mem_append_right _ (ih h)

theorem simple_map {α β : Type} (f : α → β) (xs : List α) (nd : xs.Nodup)
    (ok : ∀ p, p ∈ xs → ∀ q, q ∈ xs → f p = f q → p = q) : (xs.map f).Nodup := by
  induction xs with
  | nil => exact List.nodup_nil
  | cons a xs ih =>
    rw [List.map_cons]; apply List.nodup_cons.mpr; constructor
    · intro bad; obtain ⟨b, hb, he⟩ := List.mem_map.mp bad
      have eq := ok _ (List.mem_cons_of_mem _ hb) _ List.mem_cons_self he
      subst b; exact (List.nodup_cons.mp nd).1 hb
    · exact ih (List.nodup_cons.mp nd).2 (fun p hp q hq => ok _ (List.mem_cons_of_mem _ hp) _ (List.mem_cons_of_mem _ hq))

theorem all_three (bits : BitString) (i : Nat) (hi : i<(pack bits).width) :
    hits i (labels (pack bits).rows) = 3 := by
  let rs := macroRows (normalized bits)
  obtain ⟨a, hp⟩ := port_in_bank rs i hi
  have inrows : (a, i) ∈ labels (targetRows bits) := by
    change (a, i) ∈ labels (tagged rs ++ ties (labels (tagged rs)))
    rw [lab_app]; exact List.mem_append_left _ hp
  change hits i (labels (relabel Prod.snd (targetRows bits))) = 3
  rw [renamed_labels]
  have inj : ∀ q, q ∈ labels (targetRows bits) → q.2 = (a, i).2 → q = (a, i) := fun q h e => same_slot rs (supported rs h) hp e
  exact (hit_inj_map Prod.snd _ (a, i) inj).trans (every_used_exactly_three _ _ inrows)

theorem all_simple (bits : BitString) (r : Row Nat) (hr : r ∈ (pack bits).rows) : Simple r.w := by
  obtain ⟨e, he, d⟩ := List.mem_map.mp hr; subst r
  change ((relabelW Prod.snd e.w).map Prod.fst).Nodup; rw [renamed_labels_w]
  apply simple_map _ _ (target_simple _ _ he)
  intro p hp q hq eq
  have a := supported _ (row_ports _ he hp)
  have b := supported _ (row_ports _ he hq)
  exact same_slot _ a b eq

def marked (rows : List (Row Nat)) : Prop := ∃ head tail, rows = head :: tail ∧ head.out = mark ∧ head.w.length = 4 ∧ ∀ e, e ∈ tail → plain e

theorem numeric_marked (bits : BitString) : marked (pack bits).rows := by
  obtain ⟨u, rest, eq, tag, len, good⟩ := target_shape bits
  change marked (relabel Prod.snd (targetRows bits))
  rw [eq]
  refine ⟨⟨relabelW Prod.snd u.w, u.out⟩, relabel Prod.snd rest, rfl, tag, ?_, ?_⟩
  · change (List.map _ u.w).length = 4; rw [List.length_map, len]
  · intro e he; obtain ⟨v, hv, equiv⟩ := List.mem_map.mp he; subst e
    refine ⟨(good v hv).1, ?_⟩
    change (List.map _ v.w).length ≤ 12; rw [List.length_map]; exact (good v hv).2

def restricted (p : Packet) : Prop := (∀ i, i<p.width → hits i (labels p.rows) = 3) ∧
    (∀ r, r ∈ p.rows → Simple r.w) ∧ marked p.rows

theorem pack_restricted (bits : BitString) : restricted (pack bits) := ⟨all_three bits, all_simple bits, numeric_marked bits⟩

def ThreeUseSAT (bs : BitString) : Prop := ∃ p, decode bs = some p ∧ restricted p ∧ finiteFeasible p.rows

theorem strict_restricted (bits : BitString) : CNFSAT bits ↔ ThreeUseSAT (compile bits) := by
  constructor
  · intro h; obtain ⟨p, dec, ok⟩ := (byte_iff _).mp h
    have a : decode (compile bits) = some (pack bits) := decode_spec _ (pack_range _)
    rw [a] at dec; cases dec; exact ⟨_, a, pack_restricted bits, ok⟩
  · rintro ⟨p, dec, _, h⟩; exact (byte_iff _).mpr ⟨_, dec, h⟩
end PNP.ThreeUse.Encoding
