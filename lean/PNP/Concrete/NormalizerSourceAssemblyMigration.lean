/-
Copyright (c) 2026 PNP Labs.

Copy every source value to its assembly field before the outer loops reuse
the old cache slots. The option tag is stripped only by the guarded caller;
an empty payload is a valid failure at row zero.
-/
import PNP.Concrete.NormalizerSourceAssemblyOverlay

namespace PNP.Concrete.NormalizerBlocks.SourceAssembly
open BitRegister Occurrence
open SystemAssembly (Routine)

def withCoefficient (r : State) (core : Coefficient.State) : State :=
  r.withRows (r.core.withCore core)
def copyLiterals : Routine where
  block := .action (.copy 13 28)
  result r := withCoefficient r (r.core.core.withDense {r.core.core.core.core with formula := r.core.buffer})
  fuel _ := 1
  bound := .constant 1
  exec _ := .action _ _
  cost _ _ _ := Nat.le_refl 1
def copyOwners : Routine where
  block := .action (.copy 16 27)
  result r := withCoefficient r {r.core.core with core := {r.core.core.core with matching := r.core.count}}
  fuel _ := 1
  bound := .constant 1
  exec _ := .action _ _
  cost _ _ _ := Nat.le_refl 1
def copySlots : Routine where
  block := .action (.copy 17 25)
  result r := withCoefficient r {r.core.core with core := {r.core.core.core with counter := r.core.remaining}}
  fuel _ := 1
  bound := .constant 1
  exec _ := .action _ _
  cost _ _ _ := Nat.le_refl 1
def copyModes : Routine where
  block := .action (.copy 18 26)
  result r := withCoefficient r {r.core.core with core := {r.core.core.core with target := r.core.counter}}
  fuel _ := 1
  bound := .constant 1
  exec _ := .action _ _
  cost _ _ _ := Nat.le_refl 1
def copyCandidate : Routine where
  block := .action (.copy 19 22)
  result r := withCoefficient r {r.core.core with assignment := r.core.core.row}
  fuel _ := 1
  bound := .constant 1
  exec _ := .action _ _
  cost _ _ _ := Nat.le_refl 1
def copyFailure : Routine where
  block := .seq (.action (.copy 20 8)) (.action (.pop 20))
  result r := withCoefficient r {r.core.core with failed := r.registers.output.tail}
  fuel _ := 2
  bound := .constant 2
  exec r := by
    dsimp only [withCoefficient,SystemAssembly.State.withRows,SystemRows.State.withCore,
      SystemAssembly.State.store,SystemAssembly.State.frame,SystemRows.State.store,SystemRows.State.frame,
      Coefficient.State.store,Coefficient.State.frame,CacheMode.State.store,CacheMode.State.frame,
      DenseClauses.State.store,DenseClauses.State.frame,CompactClause.State.store,CompactClause.State.frame,
      Registers.store,Frame.join]
    exact Exec.seq (.action _ _) (.action _ _)
  cost _ _ _ := Nat.le_refl 2
def migrate : Routine :=
  Routine.seq copyLiterals (Routine.seq copyOwners (Routine.seq copySlots
    (Routine.seq copyModes (Routine.seq copyCandidate copyFailure))))
def migrated (r : State) : State := migrate.result r
theorem migrate_exec (r : State) : Exec migrate.block r.store 7 (migrated r).store := migrate.exec r
theorem migrated_data (r : State) :
    (migrated r).core.core.data =
      ⟨r.core.buffer,r.core.count,r.core.remaining,r.core.counter,
       r.core.core.row,r.registers.output.tail,r.core.core.row⟩ := rfl
theorem migrated_frame (r : State) :
    (migrated r).core.rows = r.core.rows ∧ (migrated r).recovery = r.recovery ∧
    (migrated r).b = r.b ∧ (migrated r).a = r.a := ⟨rfl,rfl,rfl,rfl⟩
theorem migrated_output (r : State) : (migrated r).registers.output = r.registers.output := rfl
theorem migrated_bounded (r : State) (n : Nat) (bounded : r.store.Bounded n) :
    (migrated r).store.Bounded (n+7) := (migrate_exec r).bounded n bounded

theorem migrated_source_data (r : CutDriver.State) :
    (migrated (extended r)).core.core.data =
      ⟨SourceCacheDriver.literals r,SourceCacheDriver.owners r,SourceCacheDriver.slots r,
       SourceCacheDriver.modes r,SourceCheck.candidate r,r.registers.output.tail,SourceCheck.candidate r⟩ := by
  rw [migrated_data]
  have fields := extended_inputs r
  rw [fields.1,fields.2.1,fields.2.2.1,fields.2.2.2.1,fields.2.2.2.2.1,extended_registers]
theorem migrated_source_rows (r : CutDriver.State) :
    (migrated (extended r)).core.rows = SourceCacheDriver.rows r :=
  (migrated_frame (extended r)).1.trans (extended_inputs r).2.2.2.2.2
theorem migrated_source_recovery (r : CutDriver.State) :
    (migrated (extended r)).recovery = recovery r :=
  (migrated_frame (extended r)).2.1.trans (extended_recovery r)

end PNP.Concrete.NormalizerBlocks.SourceAssembly
