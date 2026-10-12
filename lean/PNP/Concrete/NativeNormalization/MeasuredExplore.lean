import PNP.Concrete.NativeNormalization.MeasuredReach

namespace PNP.Concrete.NativeNormalization.MeasuredReach

def explore [DecidableEq α] (seed : α → Measured Bool) (edge : α → α → Measured Bool) :
    Nat → List α → Trace α → Measured (Trace α)
  | 0, _, tr => ⟨tr,1⟩
  | fuel+1, unseen, tr =>
      let visited := extract (eligible seed edge tr) unseen
      match visited.value with
      | none => ⟨tr,visited.cost+1⟩
      | some ((v,p),rest) =>
          let next := explore seed edge fuel rest ((v,p)::tr)
          ⟨next.value,visited.cost+next.cost+1⟩

theorem explore_value [DecidableEq α] (seed : α → Measured Bool)
    (edge : α → α → Measured Bool) (fuel : Nat) (unseen : List α) (tr : Trace α) :
    (explore seed edge fuel unseen tr).value =
      PNP.Concrete.NativeNormalization.explore (fun a => (seed a).value)
        (fun a b => (edge a b).value) fuel unseen tr := by
  induction fuel generalizing unseen tr with
  | zero => rfl
  | succ fuel ih =>
      have hread : (extract (eligible seed edge tr) unseen).value =
          extractMap (PNP.Concrete.NativeNormalization.eligible (fun a => (seed a).value)
            (fun a b => (edge a b).value) tr) unseen := by
        rw [extract_value]
        congr 1
        funext v
        exact eligible_value seed edge tr v
      cases h : extractMap (PNP.Concrete.NativeNormalization.eligible (fun a => (seed a).value)
          (fun a b => (edge a b).value) tr) unseen with
      | none => simp only [explore, hread, h, PNP.Concrete.NativeNormalization.explore]
      | some entry =>
          rcases entry with ⟨⟨v,p⟩,rest⟩
          simpa only [explore, hread, h, PNP.Concrete.NativeNormalization.explore] using ih rest ((v,p)::tr)

/-- Callback costs are explicit. This is a source-operation bound, not a tape-runtime theorem. -/
theorem explore_cost [DecidableEq α] (seed : α → Measured Bool)
    (edge : α → α → Measured Bool) (S E : Nat)
    (hs : ∀ a, (seed a).cost ≤ S) (he : ∀ a b, (edge a b).cost ≤ E)
    (fuel : Nat) (unseen : List α) (tr : Trace α) (N B : Nat)
    (hu : unseen.length ≤ N) (hb : tr.length+fuel ≤ B) :
    (explore seed edge fuel unseen tr).cost ≤
      fuel * ((((E+3)*B+S+7)*N)+2)+1 := by
  induction fuel generalizing unseen tr with
  | zero => simp [explore]
  | succ fuel ih =>
      have ht : tr.length ≤ B := by omega
      have hel : ∀ v, (eligible seed edge tr v).cost ≤ (E+3)*B+S+5 := by
        intro v
        exact Nat.le_trans (eligible_cost seed edge tr v S E hs he)
          (Nat.add_le_add_right (Nat.add_le_add_right (Nat.mul_le_mul_left (E+3) ht) S) 5)
      have hex : (extract (eligible seed edge tr) unseen).cost ≤
          ((E+3)*B+S+7)*unseen.length+1 := by
        simpa only [Nat.add_assoc] using
          extract_cost (eligible seed edge tr) unseen ((E+3)*B+S+5) hel
      have hvisit : (extract (eligible seed edge tr) unseen).cost ≤
          ((E+3)*B+S+7)*N+1 :=
        Nat.le_trans hex (Nat.add_le_add_right (Nat.mul_le_mul_left _ hu) 1)
      cases h : (extract (eligible seed edge tr) unseen).value with
      | none =>
          simp only [explore, h]
          rw [Nat.succ_mul]
          omega
      | some entry =>
          rcases entry with ⟨⟨v,p⟩,rest⟩
          have hsource : extractMap (fun a => (eligible seed edge tr a).value) unseen =
              some ((v,p),rest) := by
            rw [← extract_value]
            exact h
          have hlength := (extractMap_some _ _ hsource).2.length_eq
          simp only [List.length_cons] at hlength
          have hu' : rest.length ≤ N := by omega
          have hb' : ((v,p)::tr).length+fuel ≤ B := by
            simp only [List.length_cons]
            omega
          have tail := ih rest ((v,p)::tr) hu' hb'
          simp only [explore, h]
          rw [Nat.succ_mul]
          omega

def reachable (n : Nat) (seed : Fin n → Measured Bool)
    (edge : Fin n → Fin n → Measured Bool) : Measured (Trace (Fin n)) :=
  explore seed edge n (List.finRange n) []

theorem reachable_value (n : Nat) (seed : Fin n → Measured Bool)
    (edge : Fin n → Fin n → Measured Bool) :
    (reachable n seed edge).value =
      reachableTrace n (fun a => (seed a).value) (fun a b => (edge a b).value) :=
  explore_value seed edge n (List.finRange n) []

theorem reachable_cost (n : Nat) (seed : Fin n → Measured Bool)
    (edge : Fin n → Fin n → Measured Bool) (S E : Nat)
    (hs : ∀ a, (seed a).cost ≤ S) (he : ∀ a b, (edge a b).cost ≤ E) :
    (reachable n seed edge).cost ≤ n*((((E+3)*n+S+7)*n)+2)+1 := by
  exact explore_cost seed edge S E hs he n (List.finRange n) [] n n (by simp) (by simp)


end PNP.Concrete.NativeNormalization.MeasuredReach
