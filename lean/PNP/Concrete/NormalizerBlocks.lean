/-
Copyright (c) 2026 PNP Labs.

Structured assembly for the source-derived normalizer. Every construct lowers
to the existing finite bit-register instructions; there is no function-valued
instruction or callback. Loop termination and whole-input polynomial fuel must
still be proved for each concrete use.
-/

import PNP.Concrete.NANDFrontendProgram

namespace PNP.Concrete.NormalizerBlocks

open BitRegister

inductive Action (count : Nat) where
  | clear (destination : Fin count)
  | copy (destination source : Fin count)
  | push (destination : Fin count) (bit : Bool)
  | pop (destination : Fin count)
deriving Repr

def Action.instruction {count : Nat} : Action count → Nat → Instruction count
  | .clear destination, next => .clear destination next
  | .copy destination source, next => .copy destination source next
  | .push destination bit, next => .push destination bit next
  | .pop destination, next => .pop destination next

def Action.update {count : Nat} (action : Action count) (store : Store count) : Store count :=
  (action.instruction 0).update store

theorem Action.execute {count : Nat} (action : Action count) (next : Nat) (store : Store count) :
    (action.instruction next).execute store = ⟨.running next, action.update store⟩ := by
  cases action <;> rfl

inductive Block (count : Nat) where
  | skip
  | action (operation : Action count)
  | seq (first second : Block count)
  | branch (source : Fin count) (empty zero one : Block count)
  | loop (source : Fin count) (body : Block count)
deriving Repr

def Block.size {count : Nat} : Block count → Nat
  | .skip => 1
  | .action _ => 1
  | .seq first second => first.size + second.size
  | .branch _ empty zero one => 1 + empty.size + zero.size + one.size
  | .loop _ body => 1 + body.size

def Block.code {count : Nat} : Block count → Nat → Nat → List (Instruction count)
  | .skip, _, next => [.jump next]
  | .action operation, _, next => [operation.instruction next]
  | .seq first second, base, next =>
      first.code base (base + first.size) ++ second.code (base + first.size) next
  | .branch source empty zero one, base, next =>
      .branch source (base + 1) (base + 1 + empty.size) (base + 1 + empty.size + zero.size) ::
        (empty.code (base + 1) next ++ zero.code (base + 1 + empty.size) next ++
          one.code (base + 1 + empty.size + zero.size) next)
  | .loop source body, base, next =>
      .branch source next (base + 1) (base + 1) :: body.code (base + 1) base

theorem Block.code_length {count : Nat} (block : Block count) (base next : Nat) :
    (block.code base next).length = block.size := by
  induction block generalizing base next with
  | skip => rfl
  | action => rfl
  | seq first second ihf ihs => simp only [Block.code, Block.size, List.length_append, ihf, ihs]
  | branch source empty zero one ihe ihz iho =>
      simp only [Block.code, Block.size, List.length_cons, List.length_append, ihe, ihz, iho]
      omega
  | loop source body ih =>
      simp only [Block.code, Block.size, List.length_cons, ih]
      omega

theorem Block.size_positive {count : Nat} (block : Block count) : 0 < block.size := by
  induction block <;> simp only [Block.size] at * <;> omega

def Placed {count : Nat} (program : Program count) (base : Nat) (code : List (Instruction count)) : Prop :=
  ∀ offset, offset < code.length → BitRegister.lookup program.code (base + offset) = BitRegister.lookup code offset

theorem Placed.full {count : Nat} (program : Program count) : Placed program 0 program.code := by
  intro offset _
  rw [Nat.zero_add]

theorem Placed.head {count : Nat} {program : Program count} {base : Nat}
    {instruction : Instruction count} {rest : List (Instruction count)}
    (placed : Placed program base (instruction :: rest)) :
    BitRegister.lookup program.code base = some instruction := by
  simpa only [Nat.add_zero, BitRegister.lookup] using placed 0 (by simp only [List.length_cons]; omega)

theorem Placed.prefix {count : Nat} {program : Program count} {base : Nat}
    (front back : List (Instruction count)) (placed : Placed program base (front ++ back)) :
    Placed program base front := by
  intro offset inside
  have h := placed offset (by rw [List.length_append]; omega)
  rw [NANDFrontend.lookup_append_left front back offset inside] at h
  exact h

theorem Placed.suffix {count : Nat} {program : Program count} {base : Nat}
    (front back : List (Instruction count)) (placed : Placed program base (front ++ back)) :
    Placed program (base + front.length) back := by
  intro offset inside
  have h := placed (front.length + offset) (by rw [List.length_append]; omega)
  rw [NANDFrontend.lookup_append_skip] at h
  simpa only [Nat.add_assoc] using h

theorem Placed.tail {count : Nat} {program : Program count} {base : Nat}
    {instruction : Instruction count} {rest : List (Instruction count)}
    (placed : Placed program base (instruction :: rest)) : Placed program (base + 1) rest := by
  exact Placed.suffix [instruction] rest placed

theorem branch_segments {count : Nat} {program : Program count} (base next : Nat)
    (source : Fin count) (empty zero one : Block count)
    (placed : Placed program base ((Block.branch source empty zero one).code base next)) :
    BitRegister.lookup program.code base =
        some (.branch source (base + 1) (base + 1 + empty.size) (base + 1 + empty.size + zero.size)) ∧
      Placed program (base + 1) (empty.code (base + 1) next) ∧
      Placed program (base + 1 + empty.size) (zero.code (base + 1 + empty.size) next) ∧
      Placed program (base + 1 + empty.size + zero.size) (one.code (base + 1 + empty.size + zero.size) next) := by
  have tail := Placed.tail placed
  rw [List.append_assoc] at tail
  have pe := Placed.prefix _ _ tail
  have rest := Placed.suffix _ _ tail
  rw [Block.code_length] at rest
  have pz := Placed.prefix _ _ rest
  have po := Placed.suffix _ _ rest
  rw [Block.code_length] at po
  exact ⟨Placed.head placed, pe, pz, po⟩

inductive Exec {count : Nat} : Block count → Store count → Nat → Store count → Prop where
  | skip (store : Store count) : Exec .skip store 1 store
  | action (operation : Action count) (store : Store count) :
      Exec (.action operation) store 1 (operation.update store)
  | seq {first second : Block count} {before middle after : Store count} {firstCost secondCost : Nat}
      (front : Exec first before firstCost middle) (back : Exec second middle secondCost after) :
      Exec (.seq first second) before (firstCost + secondCost) after
  | empty {source : Fin count} {empty zero one : Block count} {before after : Store count} {cost : Nat}
      (read : before.get source = []) (body : Exec empty before cost after) :
      Exec (.branch source empty zero one) before (1 + cost) after
  | zero {source : Fin count} {empty zero one : Block count} {before after : Store count}
      {cost : Nat} {rest : BitString}
      (read : before.get source = false :: rest) (body : Exec zero before cost after) :
      Exec (.branch source empty zero one) before (1 + cost) after
  | one {source : Fin count} {empty zero one : Block count} {before after : Store count}
      {cost : Nat} {rest : BitString}
      (read : before.get source = true :: rest) (body : Exec one before cost after) :
      Exec (.branch source empty zero one) before (1 + cost) after
  | loopStop {source : Fin count} {body : Block count} {store : Store count}
      (read : store.get source = []) : Exec (.loop source body) store 1 store
  | loopStep {source : Fin count} {body : Block count} {before middle after : Store count}
      {bodyCost restCost : Nat} {bit : Bool} {rest : BitString}
      (read : before.get source = bit :: rest) (step : Exec body before bodyCost middle)
      (tail : Exec (.loop source body) middle restCost after) :
      Exec (.loop source body) before (1 + (bodyCost + restCost)) after

end PNP.Concrete.NormalizerBlocks
