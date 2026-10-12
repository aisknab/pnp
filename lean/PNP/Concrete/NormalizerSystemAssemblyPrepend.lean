/-
Copyright (c) 2026 PNP Labs.

Prepend a saved packet using two finite reversals. No old output is scanned
by either reversal; the literal register compiler separately charges copies
against the proved whole-store bound.
-/
import PNP.Concrete.NormalizerSystemAssemblyState

namespace PNP.Concrete.NormalizerBlocks.SystemAssembly
open BitRegister Occurrence

inductive PacketSlot where
  | b | a
def PacketSlot.index : PacketSlot → Fin 38
  | .b => 36
  | .a => 37
def PacketSlot.word : PacketSlot → State → BitString
  | .b,r => r.b
  | .a,r => r.a
theorem slot_read (slot : PacketSlot) (r : State) :
    r.store.get slot.index = slot.word r := by
  cases slot with
  | b =>
      exact (Frame.get_frame r.core.store r.frame (7 : Fin 9)).trans
        (Frame.get_frame r.recovery (.cons r.b (.cons r.a .nil)) (0 : Fin 2))
  | a =>
      exact (Frame.get_frame r.core.store r.frame (8 : Fin 9)).trans
        (Frame.get_frame r.recovery (.cons r.b (.cons r.a .nil)) (1 : Fin 2))
def State.withAuxiliary (r : State) (word : BitString) : State :=
  r.withRows (r.core.withCore {r.core.core with auxiliary := word})
def prefixPrepared (slot : PacketSlot) (r : State) : State :=
  (r.withAuxiliary r.registers.output).withRegisters
    {r.registers with excess := slot.word r,output := []}
def preparePrefix (slot : PacketSlot) : Routine where
  block := .seq (.action (.copy 23 8))
    (.seq (.action (.copy 3 slot.index)) (.action (.clear 8)))
  result := prefixPrepared slot
  fuel _ := 3
  bound := .constant 3
  exec r := by
    let stash := r.withAuxiliary r.registers.output
    let loaded := stash.withRegisters {r.registers with excess := slot.word r}
    have a : Exec (.action (.copy 23 8)) r.store 1 stash.store := .action _ _
    have b : Exec (.action (.copy 3 slot.index)) stash.store 1 loaded.store := by
      have checked := Exec.action (.copy 3 slot.index) stash.store
      change Exec (.action (.copy 3 slot.index)) stash.store 1
        (stash.store.set 3 (stash.store.get slot.index)) at checked
      rw [slot_read] at checked
      cases slot <;> exact checked
    have c : Exec (.action (.clear 8)) loaded.store 1 (prefixPrepared slot r).store := .action _ _
    exact Exec.seq a (Exec.seq b c)
  cost _ _ _ := Nat.le_refl 3
def reversePrefix : Routine where
  block := liftRows (SystemRows.liftCore Coefficient.reverseRoutine.block)
  result r := r.withRegisters {r.registers with excess := [],output := r.registers.excess.reverse ++ r.registers.output}
  fuel r := 4*r.registers.excess.length+1
  bound := .linear 4 1
  exec r := liftRows_exec _ r _ _ (SystemRows.liftCore_exec _ r.core _ _ (Coefficient.reverseRoutine.exec _))
  cost r n bounded := by
    have input := Store.get_length_le r.store (3 : Fin 38) bounded
    change r.registers.excess.length ≤ n at input
    change 4*r.registers.excess.length+1 ≤ 4*n+1
    omega
def prepareAgain : Routine where
  block := .seq (.action (.copy 3 8)) (.action (.copy 8 23))
  result r := r.withRegisters {r.registers with excess := r.registers.output,output := r.core.core.auxiliary}
  fuel _ := 2
  bound := .constant 2
  exec _ := Exec.seq (.action _ _) (.action _ _)
  cost _ _ _ := Nat.le_refl 2
def prepend (slot : PacketSlot) : Routine :=
  Routine.seq (preparePrefix slot) (Routine.seq reversePrefix (Routine.seq prepareAgain reversePrefix))
theorem prepend_output (slot : PacketSlot) (r : State) :
    ((prepend slot).result r).registers.output = slot.word r ++ r.registers.output := by
  change ((slot.word r).reverse ++ []).reverse ++ r.registers.output = _
  rw [List.append_nil,List.reverse_reverse]
theorem prepend_saved (slot : PacketSlot) (r : State) :
    ((prepend slot).result r).b = r.b ∧ ((prepend slot).result r).a = r.a := ⟨rfl,rfl⟩
theorem prepend_recovery (slot : PacketSlot) (r : State) :
    ((prepend slot).result r).recovery = r.recovery := rfl
theorem prepend_shared (slot : PacketSlot) (r : State) :
    ((prepend slot).result r).core.shared = r.core.shared := rfl
theorem prepend_rows (slot : PacketSlot) (r : State) :
    ((prepend slot).result r).core.rows = r.core.rows := rfl
theorem prepend_fuel (slot : PacketSlot) (r : State) :
    (prepend slot).fuel r = 8*(slot.word r).length+7 := by
  change 3+((4*(slot.word r).length+1)+(2+(4*((slot.word r).reverse++[]).length+1))) = _
  rw [List.append_nil,List.length_reverse]
  omega

end PNP.Concrete.NormalizerBlocks.SystemAssembly
