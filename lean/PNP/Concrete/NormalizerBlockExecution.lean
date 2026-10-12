/-
Copyright (c) 2026 PNP Labs.

Exact execution of structured normalizer blocks by their literal finite code.
The execution relation is a proof object, never an executable callback or a
caller-supplied premise of the eventual closed normalizer.
-/

import PNP.Concrete.NormalizerBlocks

namespace PNP.Concrete.NormalizerBlocks

open BitRegister

theorem single_step {count : Nat} (program : Program count) (address : Nat)
    (instruction : Instruction count) (store : Store count)
    (found : BitRegister.lookup program.code address = some instruction) :
    BitRegister.run program 1 ⟨.running address, store⟩ = instruction.execute store := by
  simp only [BitRegister.run, BitRegister.step, found]

theorem branch_empty {count : Nat} (program : Program count) (address : Nat)
    (source : Fin count) (emptyTarget zeroTarget oneTarget : Nat) (store : Store count)
    (found : BitRegister.lookup program.code address = some (.branch source emptyTarget zeroTarget oneTarget))
    (read : store.get source = []) :
    BitRegister.run program 1 ⟨.running address, store⟩ = ⟨.running emptyTarget, store⟩ := by
  rw [single_step program address _ store found]
  simp only [Instruction.execute, Instruction.nextControl, Instruction.update, read]

theorem branch_zero {count : Nat} (program : Program count) (address : Nat)
    (source : Fin count) (emptyTarget zeroTarget oneTarget : Nat) (store : Store count) (rest : BitString)
    (found : BitRegister.lookup program.code address = some (.branch source emptyTarget zeroTarget oneTarget))
    (read : store.get source = false :: rest) :
    BitRegister.run program 1 ⟨.running address, store⟩ = ⟨.running zeroTarget, store⟩ := by
  rw [single_step program address _ store found]
  simp only [Instruction.execute, Instruction.nextControl, Instruction.update, read]

theorem branch_one {count : Nat} (program : Program count) (address : Nat)
    (source : Fin count) (emptyTarget zeroTarget oneTarget : Nat) (store : Store count) (rest : BitString)
    (found : BitRegister.lookup program.code address = some (.branch source emptyTarget zeroTarget oneTarget))
    (read : store.get source = true :: rest) :
    BitRegister.run program 1 ⟨.running address, store⟩ = ⟨.running oneTarget, store⟩ := by
  rw [single_step program address _ store found]
  simp only [Instruction.execute, Instruction.nextControl, Instruction.update, read]

theorem Exec.run {count : Nat} {block : Block count} {before after : Store count} {fuel : Nat}
    (execution : Exec block before fuel after) (program : Program count) (base next : Nat)
    (placed : Placed program base (block.code base next)) :
    BitRegister.run program fuel ⟨.running base, before⟩ = ⟨.running next, after⟩ := by
  induction execution generalizing base next with
  | skip store =>
      exact single_step program base (.jump next) store (Placed.head placed)
  | action operation store =>
      rw [single_step program base _ store (Placed.head placed), Action.execute]
  | seq front back ihf ihb =>
      have pf := Placed.prefix _ _ placed
      have pb := Placed.suffix _ _ placed
      rw [Block.code_length] at pb
      rw [BitRegister.run_add, ihf _ _ pf, ihb _ _ pb]
  | empty read body ih =>
      have parts := branch_segments _ _ _ _ _ _ placed
      rw [BitRegister.run_add, branch_empty program _ _ _ _ _ _ parts.1 read, ih _ _ parts.2.1]
  | zero read body ih =>
      have parts := branch_segments _ _ _ _ _ _ placed
      rw [BitRegister.run_add, branch_zero program _ _ _ _ _ _ _ parts.1 read, ih _ _ parts.2.2.1]
  | one read body ih =>
      have parts := branch_segments _ _ _ _ _ _ placed
      rw [BitRegister.run_add, branch_one program _ _ _ _ _ _ _ parts.1 read, ih _ _ parts.2.2.2]
  | loopStop read =>
      exact branch_empty program _ _ _ _ _ _ (Placed.head placed) read
  | @loopStep source body before middle after bodyCost restCost bit rest read step tail ihs iht =>
      have entry := Placed.head placed
      have bodyPlaced := Placed.tail placed
      have begin : BitRegister.run program 1 ⟨.running base, before⟩ =
          ⟨.running (base + 1), before⟩ := by
        cases bit
        · exact branch_zero program _ _ _ _ _ _ _ entry read
        · exact branch_one program _ _ _ _ _ _ _ entry read
      rw [BitRegister.run_add, begin, BitRegister.run_add, ihs _ _ bodyPlaced, iht _ _ placed]

theorem Exec.bounded {count : Nat} {block : Block count} {before after : Store count} {fuel : Nat}
    (execution : Exec block before fuel after) (bound : Nat) (bounded : before.Bounded bound) :
    after.Bounded (bound + fuel) := by
  induction execution generalizing bound with
  | skip store => exact Store.bounded_mono bounded (Nat.le_succ bound)
  | action operation store => exact Instruction.update_bounded (operation.instruction 0) store bounded
  | seq front back ihf ihb =>
      simpa only [Nat.add_assoc] using ihb _ (ihf _ bounded)
  | empty read body ih =>
      simpa only [Nat.add_assoc] using ih (bound + 1) (Store.bounded_mono bounded (Nat.le_succ bound))
  | zero read body ih =>
      simpa only [Nat.add_assoc] using ih (bound + 1) (Store.bounded_mono bounded (Nat.le_succ bound))
  | one read body ih =>
      simpa only [Nat.add_assoc] using ih (bound + 1) (Store.bounded_mono bounded (Nat.le_succ bound))
  | loopStop read => exact Store.bounded_mono bounded (Nat.le_succ bound)
  | loopStep read step tail ihs iht =>
      simpa only [Nat.add_assoc] using
        iht _ (ihs (bound + 1) (Store.bounded_mono bounded (Nat.le_succ bound)))

def Block.program {count : Nat} (block : Block count) (input output : Fin count) : Program count :=
  ⟨block.code 0 block.size ++ [.accept], 0, input, output⟩

theorem Block.program_placed {count : Nat} (block : Block count) (input output : Fin count) :
    Placed (block.program input output) 0 (block.code 0 block.size) :=
  Placed.prefix _ _ (Placed.full (block.program input output))

theorem Block.program_accept {count : Nat} (block : Block count) (input output : Fin count) :
    BitRegister.lookup (block.program input output).code block.size = some .accept := by
  change BitRegister.lookup (block.code 0 block.size ++ [.accept]) block.size = some .accept
  have h := NANDFrontend.lookup_append_skip (block.code 0 block.size) [Instruction.accept] 0
  simpa only [Nat.add_zero, Block.code_length, BitRegister.lookup] using h

theorem Exec.program_run {count : Nat} {block : Block count} {before after : Store count} {fuel : Nat}
    (execution : Exec block before fuel after) (input output : Fin count) :
    BitRegister.run (block.program input output) (fuel + 1) ⟨.running 0, before⟩ =
      ⟨.accepted, after⟩ := by
  rw [BitRegister.run_add, execution.run _ 0 block.size (block.program_placed input output)]
  exact single_step _ _ .accept _ (block.program_accept input output)

end PNP.Concrete.NormalizerBlocks
