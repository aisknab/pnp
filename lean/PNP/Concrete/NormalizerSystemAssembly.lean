/-
Copyright (c) 2026 PNP Labs.

Complete b/A/E byte assembly. Both full row loops are closed finite
programs; all seven recovery registers remain untouched. This constructor
does not solve the assembled equations.
-/
import PNP.Concrete.NormalizerSystemAssemblyPrepend

namespace PNP.Concrete.NormalizerBlocks.SystemAssembly
open BitRegister Occurrence

def afterB (r : State) : State := saveB.result (bRoutine.result r)
def afterA (r : State) : State := saveA.result ((listRoutine SystemRows.aIteration).result (afterB r))
def afterE (r : State) : State := (listRoutine SystemRows.eIteration).result (afterA r)
def construction : Routine :=
  Routine.seq bRoutine (Routine.seq saveB
    (Routine.seq (listRoutine SystemRows.aIteration)
      (Routine.seq saveA (listRoutine SystemRows.eIteration))))
theorem construction_result (r : State) : construction.result r = afterE r := rfl
theorem afterB_shared (r : State) : (afterB r).core.shared = r.core.shared := b_shared r
theorem afterA_shared (r : State) : (afterA r).core.shared = r.core.shared :=
  (list_shared SystemRows.aIteration (afterB r)).trans (afterB_shared r)
theorem afterE_shared (r : State) : (afterE r).core.shared = r.core.shared :=
  (list_shared SystemRows.eIteration (afterA r)).trans (afterA_shared r)
theorem afterB_rows (r : State) : (afterB r).core.rows = r.core.rows := b_rows r
theorem afterA_rows (r : State) : (afterA r).core.rows = r.core.rows :=
  (list_rows SystemRows.aIteration (afterB r)).trans (afterB_rows r)
theorem afterE_rows (r : State) : (afterE r).core.rows = r.core.rows :=
  (list_rows SystemRows.eIteration (afterA r)).trans (afterA_rows r)

theorem afterB_packet (r : State) :
    (afterB r).b = (bRoutine.result r).registers.output := rfl
theorem afterA_packet (r : State) :
    (afterA r).a = ((listRoutine SystemRows.aIteration).result (afterB r)).registers.output := rfl
theorem afterE_packets (r : State) :
    (afterE r).b = (bRoutine.result r).registers.output ∧
    (afterE r).a = ((listRoutine SystemRows.aIteration).result (afterB r)).registers.output :=
  ⟨rfl,rfl⟩
theorem construction_recovery (r : State) : (construction.result r).recovery = r.recovery := rfl

def joinPackets : Routine := Routine.seq (prepend .a) (prepend .b)
theorem joinPackets_output (r : State) :
    (joinPackets.result r).registers.output = r.b ++ (r.a ++ r.registers.output) := by
  change ((prepend .b).result ((prepend .a).result r)).registers.output = _
  rw [prepend_output]
  change ((prepend .a).result r).b ++ ((prepend .a).result r).registers.output = _
  rw [(prepend_saved .a r).1,prepend_output]
  rfl
theorem joinPackets_recovery (r : State) : (joinPackets.result r).recovery = r.recovery :=
  (prepend_recovery .b _).trans (prepend_recovery .a r)
theorem joinPackets_shared (r : State) : (joinPackets.result r).core.shared = r.core.shared :=
  (prepend_shared .b _).trans (prepend_shared .a r)

def routine : Routine := Routine.seq construction joinPackets
def block : Block 38 := routine.block
def result (r : State) : State := routine.result r
def fuel (r : State) : Nat := routine.fuel r
def bound : NatPolynomial := routine.bound
theorem block_exec (r : State) : Exec block r.store (fuel r) (result r).store := routine.exec r
theorem fuel_bound (r : State) (n : Nat) (bounded : r.store.Bounded n) :
    fuel r ≤ bound.eval n := routine.cost r n bounded
theorem result_bounded (r : State) (n : Nat) (bounded : r.store.Bounded n) :
    (result r).store.Bounded (n+bound.eval n) := routine.result_bounded r n bounded
theorem result_recovery (r : State) : (result r).recovery = r.recovery :=
  (joinPackets_recovery (construction.result r)).trans (construction_recovery r)
theorem result_shared (r : State) : (result r).core.shared = r.core.shared :=
  (joinPackets_shared (construction.result r)).trans (afterE_shared r)
theorem result_output (r : State) :
    (result r).registers.output =
      (bRoutine.result r).registers.output ++
        (((listRoutine SystemRows.aIteration).result (afterB r)).registers.output ++
          ((listRoutine SystemRows.eIteration).result (afterA r)).registers.output) := by
  change (joinPackets.result (afterE r)).registers.output = _
  rw [joinPackets_output,(afterE_packets r).1,(afterE_packets r).2]
  rfl

end PNP.Concrete.NormalizerBlocks.SystemAssembly
