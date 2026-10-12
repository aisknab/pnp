/-
Copyright (c) 2026 PNP Labs.

Framed finite lookups for candidate selection. Four protected registers retain
the matching table, trace-node table, remaining candidate count and final
answer while the existing nine-register owner loop runs.
-/

import PNP.Concrete.NormalizerOwnerFrame

namespace PNP.Concrete.NormalizerBlocks.Candidate

open BitRegister

structure State where
  core : Occurrence.Registers
  matching : BitString
  seen : BitString
  remaining : BitString
  output : BitString
deriving Repr

def State.frame (r : State) : Store 4 :=
  .cons r.matching (.cons r.seen (.cons r.remaining (.cons r.output .nil)))
def State.store (r : State) : Store 13 := Frame.join r.core.store r.frame

structure Result where
  fuel : Nat
  state : State
deriving Repr

def clearScratch : Block 9 :=
  .seq (.action (.clear 2)) <| .seq (.action (.clear 3)) <|
  .seq (.action (.clear 4)) (.action (.clear 5))
def scratchCleared (r : Occurrence.Registers) : Occurrence.Registers :=
  {r with remaining := [], excess := [], sign := [], mode := []}

theorem clearScratch_exec (r : Occurrence.Registers) :
    Exec clearScratch r.store 4 (scratchCleared r).store :=
  Exec.seq (.action _ _) (Exec.seq (.action _ _) (Exec.seq (.action _ _) (.action _ _)))

def activate : Block 9 :=
  .seq (.action (.clear 6)) <| .seq (.action (.clear 7)) <|
  .seq (.action (.clear 8)) <| .seq (.action (.push 6 true)) (.action (.push 8 false))
def activated (r : Occurrence.Registers) : Occurrence.Registers :=
  {r with active := [true], reserved := [], output := [false]}

theorem activate_exec (r : Occurrence.Registers) :
    Exec activate r.store 5 (activated r).store :=
  Exec.seq (.action _ _) (Exec.seq (.action _ _) (Exec.seq (.action _ _) (Exec.seq (.action _ _) (.action _ _))))

def clean : Block 9 := .seq clearScratch activate

theorem clean_exec (r : Occurrence.Registers) :
    Exec clean r.store 9 (TableOwner.prepared r.target r.input).store :=
  Exec.seq (clearScratch_exec r) (activate_exec (scratchCleared r))

def setup (source : Fin 13) : Block 13 :=
  .seq (.action (.copy 0 source)) (Frame.block 4 clean)

def ready (r : State) (table : BitString) : State :=
  ⟨TableOwner.prepared r.core.target table, r.matching, r.seen, r.remaining, r.output⟩
def copied (r : State) (source : Fin 13) : State :=
  ⟨{r.core with input := r.store.get source}, r.matching, r.seen, r.remaining, r.output⟩

theorem setup_exec (source : Fin 13) (r : State) :
    Exec (setup source) r.store 10 (ready r (r.store.get source)).store := by
  have copy : Exec (.action (.copy 0 source)) r.store 1 (copied r source).store := .action _ _
  exact Exec.seq copy (Frame.execution (clean_exec (copied r source).core) r.frame)

def lookup : Block 13 := Frame.block 4 TableOwner.loop
def looked (r : State) : State := ⟨(TableOwner.queryResult r.core).state, r.matching, r.seen, r.remaining, r.output⟩
def lookupFuel (r : State) : Nat := (TableOwner.queryResult r.core).fuel

theorem lookup_exec (r : State) : Exec lookup r.store (lookupFuel r) (looked r).store :=
  Frame.execution (TableOwner.query_exec r.core) r.frame

def readMatching : Block 13 := .seq (setup 9) lookup
def matchingResult (r : State) : State := looked (ready r r.matching)
def matchingFuel (r : State) : Nat := 10 + lookupFuel (ready r r.matching)

theorem readMatching_exec (r : State) :
    Exec readMatching r.store (matchingFuel r) (matchingResult r).store :=
  Exec.seq (setup_exec 9 r) (lookup_exec (ready r r.matching))

def readSeen : Block 13 := .seq (setup 10) lookup
def seenResult (r : State) : State := looked (ready r r.seen)
def seenFuel (r : State) : Nat := 10 + lookupFuel (ready r r.seen)

theorem readSeen_exec (r : State) :
    Exec readSeen r.store (seenFuel r) (seenResult r).store :=
  Exec.seq (setup_exec 10 r) (lookup_exec (ready r r.seen))

theorem matching_target (r : State) : (matchingResult r).core.target = r.core.target :=
  TableOwner.query_target (TableOwner.prepared r.core.target r.matching)

theorem seen_target (r : State) : (seenResult r).core.target = r.core.target :=
  TableOwner.query_target (TableOwner.prepared r.core.target r.seen)

theorem matchingFuel_bound (r : State) : matchingFuel r ≤ 12 * r.matching.length + 23 := by
  have bound := TableOwner.query_fuel_bound (TableOwner.prepared r.core.target r.matching)
  change (TableOwner.queryResult (TableOwner.prepared r.core.target r.matching)).fuel ≤
    12 * (r.matching.length + 1) + 1 at bound
  simp only [matchingFuel, lookupFuel, ready]
  omega

theorem seenFuel_bound (r : State) : seenFuel r ≤ 12 * r.seen.length + 23 := by
  have bound := TableOwner.query_fuel_bound (TableOwner.prepared r.core.target r.seen)
  change (TableOwner.queryResult (TableOwner.prepared r.core.target r.seen)).fuel ≤
    12 * (r.seen.length + 1) + 1 at bound
  simp only [seenFuel, lookupFuel, ready]
  omega

theorem matching_canonical (r : State) (target : Nat) (entries : MatchingTable.Entries)
    (index : r.core.target = List.replicate target true) (table : r.matching = MatchingTable.encode entries) :
    (matchingResult r).core.output = TableOwner.answer (TableOwner.owner entries target) := by
  change (TableOwner.queryResult (TableOwner.prepared r.core.target r.matching)).state.output = _
  rw [index, table]
  exact TableOwner.prepared_canonical target entries

theorem seen_canonical (r : State) (target : Nat) (entries : MatchingTable.Entries)
    (index : r.core.target = List.replicate target true) (table : r.seen = MatchingTable.encode entries) :
    (seenResult r).core.output = TableOwner.answer (TableOwner.owner entries target) := by
  change (TableOwner.queryResult (TableOwner.prepared r.core.target r.seen)).state.output = _
  rw [index, table]
  exact TableOwner.prepared_canonical target entries

end PNP.Concrete.NormalizerBlocks.Candidate
