/-
Copyright (c) 2026 PNP Labs.

Compute finite gate renamings from raw transposition instructions. Inverse maps
are constructed, not supplied. Out-of-range coordinates fail closed. This is
only the encoding component for structural circuit transport, not a proof of
the complete normalization or arbitrary-support replacement theorem.
-/

import PNP.NANDTopologicalWireStructure

namespace PNP.DirectWire.StructuralReindexing

structure GateRenaming (nodes : Nat) where
  forward : Fin nodes → Fin nodes
  backward : Fin nodes → Fin nodes
  backward_forward : ∀ node, backward (forward node) = node
  forward_backward : ∀ node, forward (backward node) = node

namespace GateRenaming

def identity (nodes : Nat) : GateRenaming nodes :=
  ⟨id, id, fun _ => rfl, fun _ => rfl⟩

def compose {nodes : Nat} (first second : GateRenaming nodes) : GateRenaming nodes :=
  { forward := fun node => second.forward (first.forward node)
    backward := fun node => first.backward (second.backward node)
    backward_forward := by
      intro node
      rw [second.backward_forward, first.backward_forward]
    forward_backward := by
      intro node
      rw [first.forward_backward, second.forward_backward] }

private def swapIndex {nodes : Nat} (left right index : Fin nodes) : Fin nodes :=
  if index = left then right else if index = right then left else index

private theorem swapIndex_twice {nodes : Nat} (left right index : Fin nodes) :
    swapIndex left right (swapIndex left right index) = index := by
  by_cases first : index = left
  · subst index
    by_cases same : left = right
    · subst right
      simp only [swapIndex, ite_true]
    · simp only [swapIndex, ite_true, if_neg (Ne.symm same)]
  · by_cases second : index = right
    · subst index
      simp only [swapIndex, if_neg first, ite_true]
    · simp only [swapIndex, if_neg first, if_neg second]

def swap {nodes : Nat} (left right : Fin nodes) : GateRenaming nodes :=
  ⟨swapIndex left right, swapIndex left right,
    swapIndex_twice left right, swapIndex_twice left right⟩

theorem forward_injective {nodes : Nat} (relabeling : GateRenaming nodes) :
    Function.Injective relabeling.forward := by
  intro left right same
  have original := congrArg relabeling.backward same
  rw [relabeling.backward_forward, relabeling.backward_forward] at original
  exact original

theorem backward_injective {nodes : Nat} (relabeling : GateRenaming nodes) :
    Function.Injective relabeling.backward := by
  intro left right same
  have original := congrArg relabeling.forward same
  rw [relabeling.forward_backward, relabeling.forward_backward] at original
  exact original

/-- Each accepted raw coordinate pair denotes an actual involutive swap. -/
def decode (nodes : Nat) : List (Nat × Nat) → Option (GateRenaming nodes)
  | [] => some (identity nodes)
  | (left, right) :: remaining =>
      if leftValid : left < nodes then
        if rightValid : right < nodes then
          (decode nodes remaining).map
            (fun rest => compose (swap ⟨left, leftValid⟩ ⟨right, rightValid⟩) rest)
        else none
      else none

def validCode (nodes : Nat) : List (Nat × Nat) → Bool
  | [] => true
  | (left, right) :: remaining =>
      decide (left < nodes) && decide (right < nodes) && validCode nodes remaining

private theorem map_isSome {alpha beta : Type} (value : Option alpha)
    (function : alpha → beta) : (value.map function).isSome = value.isSome := by
  cases value <;> rfl

/-- Exact acceptance covers the complete raw sequence, not a successful prefix. -/
theorem decode_isSome (nodes : Nat) (code : List (Nat × Nat)) :
    (decode nodes code).isSome = validCode nodes code := by
  induction code with
  | nil => rfl
  | cons pair remaining ih =>
      rcases pair with ⟨left, right⟩
      unfold decode
      split
      next leftValid =>
        split
        next rightValid =>
          rw [map_isSome, ih]
          simp only [validCode, decide_eq_true leftValid, decide_eq_true rightValid,
            Bool.true_and]
        next rightInvalid =>
          simp only [validCode, decide_eq_true leftValid, decide_eq_false rightInvalid,
            Bool.true_and, Bool.false_and]
          rfl
      next leftInvalid =>
        simp only [validCode, decide_eq_false leftInvalid, Bool.false_and]
        rfl

end GateRenaming

/-- Relabel only gate references; constants and primary inputs are unchanged. -/
def sourceMap {inputs fromGates toGates : Nat} (rename : Fin fromGates → Fin toGates) :
    Source inputs fromGates → Source inputs toGates
  | .input index => .input index
  | .constant value => .constant value
  | .gate node => .gate (rename node)

theorem sourceMap_compose {inputs first second third : Nat}
    (left : Fin first → Fin second) (right : Fin second → Fin third)
    (source : Source inputs first) :
    sourceMap right (sourceMap left source) = sourceMap (fun node => right (left node)) source := by
  cases source <;> rfl

theorem sourceMap_eq_gate_iff {inputs nodes : Nat} (relabeling : GateRenaming nodes)
    (source : Source inputs nodes) (node : Fin nodes) :
    sourceMap relabeling.forward source = .gate node ↔
      source = .gate (relabeling.backward node) := by
  cases source with
  | input index => constructor <;> intro impossible <;> cases impossible
  | constant value => constructor <;> intro impossible <;> cases impossible
  | gate original =>
      change (Source.gate (relabeling.forward original) : Source inputs nodes) = Source.gate node ↔
        (Source.gate original : Source inputs nodes) = Source.gate (relabeling.backward node)
      constructor
      · intro same
        have raw := congrArg relabeling.backward (Source.gate.inj same)
        rw [relabeling.backward_forward] at raw
        exact congrArg Source.gate raw
      · intro same
        have originalAt := Source.gate.inj same
        rw [originalAt, relabeling.forward_backward]

theorem sourceMap_eval {inputs nodes : Nat} (relabeling : GateRenaming nodes)
    (source : Source inputs nodes) (input : Valuation inputs) (values : Valuation nodes) :
    (sourceMap relabeling.forward source).eval input (fun node => values (relabeling.backward node)) =
      source.eval input values := by
  cases source with
  | input index => rfl
  | constant value => rfl
  | gate node => exact congrArg values (relabeling.backward_forward node)

end PNP.DirectWire.StructuralReindexing
