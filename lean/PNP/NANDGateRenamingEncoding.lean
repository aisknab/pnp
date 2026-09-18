/-
Copyright (c) 2026 PNP Labs.

Constructive completeness of the existing raw gate-swap encoding. Every finite
bijection has a computed code of at most one transposition per gate. This is an
encoding theorem, not full carrier-profile semantics or polynomial PCCMin.
-/

import PNP.NANDGateRenaming

namespace PNP.DirectWire.StructuralReindexing.GateRenaming

private theorem encoding_ext {nodes : Nat} (left right : GateRenaming nodes)
    (same : ∀ index, left.forward index = right.forward index) : left = right := by
  have forwardSame : left.forward = right.forward := funext same
  have backwardSame : left.backward = right.backward := by
    funext index
    apply left.forward_injective
    rw [left.forward_backward, same]
    exact (right.forward_backward index).symm
  cases left
  cases right
  cases forwardSame
  cases backwardSame
  rfl

private theorem encoding_succ_injective {nodes : Nat} {left right : Fin nodes}
    (same : left.succ = right.succ) : left = right := by
  apply Fin.ext
  have values := congrArg Fin.val same
  change left.val + 1 = right.val + 1 at values
  omega

private theorem encoding_succ_ne_zero {nodes : Nat} (index : Fin nodes) :
    index.succ ≠ (0 : Fin (nodes + 1)) := by
  intro same
  have values := congrArg Fin.val same
  change index.val + 1 = 0 at values
  omega

private def encodingLower {nodes : Nat} (index : Fin (nodes + 1))
    (nonzero : index ≠ 0) : Fin nodes :=
  ⟨index.val - 1, by
    have positive : index.val ≠ 0 := fun same => nonzero (Fin.ext same)
    have bound := index.isLt
    omega⟩

private theorem encodingLower_succ {nodes : Nat} (index : Fin (nodes + 1))
    (nonzero : index ≠ 0) : (encodingLower index nonzero).succ = index := by
  apply Fin.ext
  have positive : index.val ≠ 0 := fun same => nonzero (Fin.ext same)
  change index.val - 1 + 1 = index.val
  omega

private theorem encoding_backward_zero {nodes : Nat}
    (relabeling : GateRenaming (nodes + 1)) (fixed : relabeling.forward 0 = 0) :
    relabeling.backward 0 = 0 := by
  have inverse := relabeling.backward_forward 0
  rw [fixed] at inverse
  exact inverse

private def encodingRestrictForward {nodes : Nat}
    (relabeling : GateRenaming (nodes + 1)) (fixed : relabeling.forward 0 = 0)
    (index : Fin nodes) : Fin nodes :=
  encodingLower (relabeling.forward index.succ) (fun same =>
    encoding_succ_ne_zero index (relabeling.forward_injective (same.trans fixed.symm)))

private def encodingRestrictBackward {nodes : Nat}
    (relabeling : GateRenaming (nodes + 1)) (fixed : relabeling.forward 0 = 0)
    (index : Fin nodes) : Fin nodes :=
  encodingLower (relabeling.backward index.succ) (fun same =>
    encoding_succ_ne_zero index (relabeling.backward_injective
      (same.trans (encoding_backward_zero relabeling fixed).symm)))

private theorem encodingRestrictForward_succ {nodes : Nat}
    (relabeling : GateRenaming (nodes + 1)) (fixed : relabeling.forward 0 = 0)
    (index : Fin nodes) :
    (encodingRestrictForward relabeling fixed index).succ = relabeling.forward index.succ :=
  encodingLower_succ _ _

private theorem encodingRestrictBackward_succ {nodes : Nat}
    (relabeling : GateRenaming (nodes + 1)) (fixed : relabeling.forward 0 = 0)
    (index : Fin nodes) :
    (encodingRestrictBackward relabeling fixed index).succ = relabeling.backward index.succ :=
  encodingLower_succ _ _

private def encodingRestrict {nodes : Nat} (relabeling : GateRenaming (nodes + 1))
    (fixed : relabeling.forward 0 = 0) : GateRenaming nodes where
  forward := encodingRestrictForward relabeling fixed
  backward := encodingRestrictBackward relabeling fixed
  backward_forward := by
    intro index
    apply encoding_succ_injective
    rw [encodingRestrictBackward_succ, encodingRestrictForward_succ,
      relabeling.backward_forward]
  forward_backward := by
    intro index
    apply encoding_succ_injective
    rw [encodingRestrictForward_succ, encodingRestrictBackward_succ,
      relabeling.forward_backward]

private def encodingLift {nodes : Nat} (relabeling : GateRenaming nodes) :
    GateRenaming (nodes + 1) where
  forward := Fin.cases 0 (fun index => (relabeling.forward index).succ)
  backward := Fin.cases 0 (fun index => (relabeling.backward index).succ)
  backward_forward := by
    intro index
    refine Fin.cases ?_ (fun earlier => ?_) index
    · rfl
    · change (relabeling.backward (relabeling.forward earlier)).succ = earlier.succ
      rw [relabeling.backward_forward]
  forward_backward := by
    intro index
    refine Fin.cases ?_ (fun earlier => ?_) index
    · rfl
    · change (relabeling.forward (relabeling.backward earlier)).succ = earlier.succ
      rw [relabeling.forward_backward]

private theorem encodingLift_restrict {nodes : Nat}
    (relabeling : GateRenaming (nodes + 1)) (fixed : relabeling.forward 0 = 0) :
    encodingLift (encodingRestrict relabeling fixed) = relabeling := by
  apply encoding_ext
  intro index
  refine Fin.cases ?_ (fun earlier => ?_) index
  · exact fixed.symm
  · exact encodingRestrictForward_succ relabeling fixed earlier

private theorem encoding_swap_forward {nodes : Nat} (left right index : Fin nodes) :
    (swap left right).forward index =
      if index = left then right else if index = right then left else index := rfl

private theorem encoding_swap_forward_left {nodes : Nat} (left right : Fin nodes) :
    (swap left right).forward left = right := by
  rw [encoding_swap_forward, if_pos rfl]

private theorem encodingLift_swap {nodes : Nat} (left right : Fin nodes) :
    encodingLift (swap left right) = swap left.succ right.succ := by
  apply encoding_ext
  intro index
  refine Fin.cases ?_ (fun earlier => ?_) index
  · change (0 : Fin (nodes + 1)) = (swap left.succ right.succ).forward 0
    rw [encoding_swap_forward, if_neg (Ne.symm (encoding_succ_ne_zero left)),
      if_neg (Ne.symm (encoding_succ_ne_zero right))]
  · change ((swap left right).forward earlier).succ =
      (swap left.succ right.succ).forward earlier.succ
    rw [encoding_swap_forward, encoding_swap_forward]
    by_cases first : earlier = left
    · subst earlier
      simp only [ite_true]
    · have firstSucc : earlier.succ ≠ left.succ := fun same =>
        first (encoding_succ_injective same)
      by_cases second : earlier = right
      · subst earlier
        simp only [if_neg first, if_neg firstSucc, ite_true]
      · have secondSucc : earlier.succ ≠ right.succ := fun same =>
          second (encoding_succ_injective same)
        rw [if_neg first, if_neg second, if_neg firstSucc, if_neg secondSucc]

private theorem encodingLift_compose {nodes : Nat} (first second : GateRenaming nodes) :
    encodingLift (compose first second) = compose (encodingLift first) (encodingLift second) := by
  apply encoding_ext
  intro index
  refine Fin.cases ?_ (fun earlier => ?_) index <;> rfl

private theorem encodingLift_identity (nodes : Nat) :
    encodingLift (identity nodes) = identity (nodes + 1) := by
  apply encoding_ext
  intro index
  refine Fin.cases ?_ (fun earlier => ?_) index <;> rfl

private abbrev EncodingCode (nodes : Nat) := List (Fin nodes × Fin nodes)

private def encodingValue {nodes : Nat} : EncodingCode nodes → GateRenaming nodes
  | [] => identity nodes
  | (left, right) :: remaining => compose (swap left right) (encodingValue remaining)

private def encodingRaw {nodes : Nat} (code : EncodingCode nodes) : List (Nat × Nat) :=
  code.map fun pair => (pair.1.val, pair.2.val)

private theorem decode_encodingRaw {nodes : Nat} (code : EncodingCode nodes) :
    decode nodes (encodingRaw code) = some (encodingValue code) := by
  induction code with
  | nil => rfl
  | cons pair remaining ih =>
      rcases pair with ⟨left, right⟩
      change (if first : left.val < nodes then
        if second : right.val < nodes then
          (decode nodes (encodingRaw remaining)).map (fun rest =>
            compose (swap ⟨left.val, first⟩ ⟨right.val, second⟩) rest)
        else none else none) = _
      rw [dif_pos left.isLt, dif_pos right.isLt, ih]
      rfl

private def encodingLiftCode {nodes : Nat} (code : EncodingCode nodes) :
    EncodingCode (nodes + 1) := code.map fun pair => (pair.1.succ, pair.2.succ)

private theorem encodingValue_lift {nodes : Nat} (code : EncodingCode nodes) :
    encodingValue (encodingLiftCode code) = encodingLift (encodingValue code) := by
  induction code with
  | nil => exact (encodingLift_identity nodes).symm
  | cons pair remaining ih =>
      rcases pair with ⟨left, right⟩
      change compose (swap left.succ right.succ) (encodingValue (encodingLiftCode remaining)) =
        encodingLift (compose (swap left right) (encodingValue remaining))
      rw [ih, encodingLift_compose, encodingLift_swap]

private def encodingFixed {nodes : Nat} (relabeling : GateRenaming (nodes + 1)) :
    GateRenaming (nodes + 1) := compose (swap 0 (relabeling.backward 0)) relabeling

private theorem encodingFixed_zero {nodes : Nat} (relabeling : GateRenaming (nodes + 1)) :
    (encodingFixed relabeling).forward 0 = 0 := by
  change relabeling.forward ((swap 0 (relabeling.backward 0)).forward 0) = 0
  rw [encoding_swap_forward_left, relabeling.forward_backward]

private theorem encodingFixed_recover {nodes : Nat} (relabeling : GateRenaming (nodes + 1)) :
    compose (swap 0 (relabeling.backward 0)) (encodingFixed relabeling) = relabeling := by
  apply encoding_ext
  intro index
  change relabeling.forward ((swap 0 (relabeling.backward 0)).forward
    ((swap 0 (relabeling.backward 0)).forward index)) = relabeling.forward index
  have twice := (swap 0 (relabeling.backward 0)).backward_forward index
  change (swap 0 (relabeling.backward 0)).forward
    ((swap 0 (relabeling.backward 0)).forward index) = index at twice
  rw [twice]

private def encodingTyped : (nodes : Nat) → GateRenaming nodes → EncodingCode nodes
  | 0, _relabeling => []
  | nodes + 1, relabeling =>
      (0, relabeling.backward 0) :: encodingLiftCode (encodingTyped nodes
        (encodingRestrict (encodingFixed relabeling) (encodingFixed_zero relabeling)))

private theorem encodingTyped_value (nodes : Nat) (relabeling : GateRenaming nodes) :
    encodingValue (encodingTyped nodes relabeling) = relabeling := by
  induction nodes with
  | zero =>
      apply encoding_ext
      intro index
      exact Fin.elim0 index
  | succ nodes ih =>
      change compose (swap 0 (relabeling.backward 0))
        (encodingValue (encodingLiftCode (encodingTyped nodes
          (encodingRestrict (encodingFixed relabeling) (encodingFixed_zero relabeling))))) = _
      rw [encodingValue_lift, ih, encodingLift_restrict, encodingFixed_recover]

private theorem encodingTyped_length (nodes : Nat) (relabeling : GateRenaming nodes) :
    (encodingTyped nodes relabeling).length ≤ nodes := by
  induction nodes with
  | zero => exact Nat.le_refl 0
  | succ nodes ih =>
      change (encodingLiftCode (encodingTyped nodes
        (encodingRestrict (encodingFixed relabeling) (encodingFixed_zero relabeling)))).length + 1 ≤ nodes + 1
      simpa only [encodingLiftCode, List.length_map] using Nat.add_le_add_right
        (ih (encodingRestrict (encodingFixed relabeling) (encodingFixed_zero relabeling))) 1

/-- Compute a complete raw code for every finite gate bijection. -/
def encode {nodes : Nat} (relabeling : GateRenaming nodes) : List (Nat × Nat) :=
  encodingRaw (encodingTyped nodes relabeling)

/-- The existing decoder reconstructs both exact maps, not merely some bijection. -/
theorem decode_encode {nodes : Nat} (relabeling : GateRenaming nodes) :
    decode nodes (encode relabeling) = some relabeling := by
  rw [encode, decode_encodingRaw, encodingTyped_value]

/-- No more than one raw transposition is emitted per original gate. -/
theorem encode_length_le {nodes : Nat} (relabeling : GateRenaming nodes) :
    (encode relabeling).length ≤ nodes := by
  simpa only [encode, encodingRaw, List.length_map] using encodingTyped_length nodes relabeling

/-- Every emitted coordinate is valid for the complete existing raw decoder. -/
theorem validCode_encode {nodes : Nat} (relabeling : GateRenaming nodes) :
    validCode nodes (encode relabeling) = true := by
  have checked := decode_isSome nodes (encode relabeling)
  rw [decode_encode] at checked
  exact checked.symm

end PNP.DirectWire.StructuralReindexing.GateRenaming
