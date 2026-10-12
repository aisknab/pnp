/-
Copyright (c) 2026 PNP Labs.

Consume the concrete frontend record once. Original width is saved in
register 36; transformed width is used only to frame the checker input.
Scratch reset reuses the existing closed reader and finite framing blocks.
-/
import PNP.Concrete.NormalizerOutputDispatch

namespace PNP.Concrete.NormalizerBlocks.OutputLoader
open BitRegister Occurrence
open SystemAssembly (Routine)
open OutputBranches (State liftPacket liftPacket_exec)

def popTag : Routine where
  block := .action (.pop 0)
  result r := r.withRegisters {r.registers with input := r.registers.input.tail}
  fuel _ := 1
  bound := .constant 1
  exec _ := .action _ _
  cost _ _ _ := Nat.le_refl 1
def readHeader : Routine where
  block := liftPacket (.seq CandidatePacket.resetCore TableInit.header)
  result r := r.withRegisters (TableInit.readCount r.registers.input).state
  fuel r := 8+TableInit.headerFuel r.registers.input
  bound := .linear 4 14
  exec r := liftPacket_exec _ r _ _
    (Exec.seq (CandidatePacket.resetCore_exec r.registers) (TableInit.header_exec r.registers.input))
  cost r n bounded := by
    have length := Store.get_length_le r.store (0 : Fin 38) bounded
    change r.registers.input.length ≤ n at length
    have work := TableInit.headerFuel_bound r.registers.input
    change 8+TableInit.headerFuel r.registers.input ≤ 4*n+14
    omega

inductive WidthSlot where
  | original | frontend
deriving Repr
def WidthSlot.index : WidthSlot → Fin 38
  | .original => 36
  | .frontend => 37
def WidthSlot.save : WidthSlot → State → BitString → State
  | .original,r,value => {r with b := value}
  | .frontend,r,value => {r with a := value}
theorem saveWidth_store (slot : WidthSlot) (r : State) (value : BitString) :
    r.store.set slot.index value = (slot.save r value).store := by
  cases slot with
  | original =>
      have outer := SystemAssembly.frame_set r.core.store r.frame (7 : Fin 9) value
      have inner := SystemAssembly.frame_set r.recovery (.cons r.b (.cons r.a .nil)) (0 : Fin 2) value
      change (Frame.join r.recovery (.cons r.b (.cons r.a .nil))).set (7 : Fin 9) value = _ at inner
      dsimp only [SystemAssembly.State.frame] at outer
      rw [inner] at outer
      exact outer
  | frontend =>
      have outer := SystemAssembly.frame_set r.core.store r.frame (8 : Fin 9) value
      have inner := SystemAssembly.frame_set r.recovery (.cons r.b (.cons r.a .nil)) (1 : Fin 2) value
      change (Frame.join r.recovery (.cons r.b (.cons r.a .nil))).set (8 : Fin 9) value = _ at inner
      dsimp only [SystemAssembly.State.frame] at outer
      rw [inner] at outer
      exact outer
def saveWidth (slot : WidthSlot) : Routine where
  block := .action (.copy slot.index 1)
  result r := slot.save r r.registers.target
  fuel _ := 1
  bound := .constant 1
  exec r := by
    have work := Exec.action (.copy slot.index (1 : Fin 38)) r.store
    change Exec (.action (.copy slot.index 1)) r.store 1 (r.store.set slot.index r.registers.target) at work
    rw [saveWidth_store] at work
    exact work
  cost _ _ _ := Nat.le_refl 1

def lengthPrefix : Routine where
  block := liftPacket PacketFrame.lengthPrefix
  result r := r.withRegisters (PacketFrame.prefixed r.registers)
  fuel r := 3*r.registers.excess.length+2
  bound := .linear 3 2
  exec r := liftPacket_exec _ r _ _ (PacketFrame.lengthPrefix_exec r.registers)
  cost r n bounded := by
    have length := Store.get_length_le r.store (3 : Fin 38) bounded
    change r.registers.excess.length ≤ n at length
    change 3*r.registers.excess.length+2 ≤ 3*n+2
    omega
def copyPayload : Routine where
  block := .seq (.action (.copy 8 0)) (.action (.copy 3 0))
  result r := r.withRegisters {r.registers with output := r.registers.input,excess := r.registers.input}
  fuel _ := 2
  bound := .constant 2
  exec r := by
    let first := r.withRegisters {r.registers with output := r.registers.input}
    have a : Exec (.action (.copy 8 0)) r.store 1 first.store := .action _ _
    have b : Exec (.action (.copy 3 0)) first.store 1
        (r.withRegisters {r.registers with output := r.registers.input,excess := r.registers.input}).store := .action _ _
    exact Exec.seq a b
  cost _ _ _ := Nat.le_refl 2
def loadFrontend : Routine where
  block := .action (.copy 3 37)
  result r := r.withRegisters {r.registers with excess := r.a}
  fuel _ := 1
  bound := .constant 1
  exec r := by
    have work := Exec.action (.copy (3 : Fin 38) 37) r.store
    change Exec (.action (.copy 3 37)) r.store 1 (r.store.set 3 (r.store.get 37)) at work
    have read : r.store.get (37 : Fin 38) = r.a := SystemAssembly.slot_read .a r
    rw [read] at work
    exact work
  cost _ _ _ := Nat.le_refl 1

def transferInput : Routine where
  block := .action (.copy 0 8)
  result r := r.withRegisters {r.registers with input := r.registers.output}
  fuel _ := 1
  bound := .constant 1
  exec _ := .action _ _
  cost _ _ _ := Nat.le_refl 1
def resetCore : Routine where
  block := liftPacket CandidatePacket.resetCore
  result r := r.withRegisters (initialRegisters r.registers.input)
  fuel _ := 8
  bound := .constant 8
  exec r := liftPacket_exec _ r _ _ (CandidatePacket.resetCore_exec r.registers)
  cost _ _ _ := Nat.le_refl 8
def clearFrontend : Routine where
  block := .action (.clear 37)
  result r := {r with a := []}
  fuel _ := 1
  bound := .constant 1
  exec r := by
    have work := Exec.action (.clear (37 : Fin 38)) r.store
    change Exec (.action (.clear 37)) r.store 1 (r.store.set 37 []) at work
    rw [show (37 : Fin 38) = WidthSlot.frontend.index from rfl,saveWidth_store] at work
    exact work
  cost _ _ _ := Nat.le_refl 1

def headers : Routine := Routine.seq popTag (Routine.seq readHeader
  (Routine.seq (saveWidth .original) (Routine.seq readHeader (saveWidth .frontend))))
def frameInput : Routine := Routine.seq copyPayload (Routine.seq lengthPrefix
  (Routine.seq loadFrontend lengthPrefix))
def commitInput : Routine := Routine.seq transferInput (Routine.seq resetCore clearFrontend)
def routine : Routine := Routine.seq headers (Routine.seq frameInput commitInput)
def block : Block 38 := routine.block
def loaded (r : State) : State := routine.result r
def fuel (r : State) : Nat := routine.fuel r
def bound : NatPolynomial := routine.bound
theorem block_exec (r : State) : Exec block r.store (fuel r) (loaded r).store := routine.exec r
theorem fuel_bound (r : State) (n : Nat) (bounded : r.store.Bounded n) : fuel r ≤ bound.eval n :=
  routine.cost r n bounded
theorem loaded_bounded (r : State) (n : Nat) (bounded : r.store.Bounded n) :
    (loaded r).store.Bounded (n+bound.eval n) := routine.result_bounded r n bounded

end PNP.Concrete.NormalizerBlocks.OutputLoader
