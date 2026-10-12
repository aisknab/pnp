/-
Copyright (c) 2026 PNP Labs.

Reset and table-loader blocks for the closed candidate packet. Register zero
retains the unread suffix while all other core registers are reset. Framed
matching, trace, counter and result words are not modified by table parsing.
-/

import PNP.Concrete.NormalizerCandidateCanonical

namespace PNP.Concrete.NormalizerBlocks.CandidatePacket

open BitRegister Occurrence

def clearLeft : Block 9 :=
  .seq (.action (.clear 1)) <| .seq (.action (.clear 2)) <|
  .seq (.action (.clear 3)) (.action (.clear 4))
def leftCleared (r : Registers) : Registers :=
  {r with target := [], remaining := [], excess := [], sign := []}

theorem clearLeft_exec (r : Registers) : Exec clearLeft r.store 4 (leftCleared r).store :=
  Exec.seq (.action _ _) (Exec.seq (.action _ _) (Exec.seq (.action _ _) (.action _ _)))

def clearRight : Block 9 :=
  .seq (.action (.clear 5)) <| .seq (.action (.clear 6)) <|
  .seq (.action (.clear 7)) (.action (.clear 8))
def rightCleared (r : Registers) : Registers :=
  {r with mode := [], active := [], reserved := [], output := []}

theorem clearRight_exec (r : Registers) : Exec clearRight r.store 4 (rightCleared r).store :=
  Exec.seq (.action _ _) (Exec.seq (.action _ _) (Exec.seq (.action _ _) (.action _ _)))

def resetCore : Block 9 := .seq clearLeft clearRight

theorem resetCore_exec (r : Registers) : Exec resetCore r.store 8 (initialRegisters r.input).store :=
  Exec.seq (clearLeft_exec r) (clearRight_exec (leftCleared r))

def loadTable : Block 13 := Frame.block 4 (.seq resetCore BatchPacket.coreLoader)
def tableResult (r : Candidate.State) : Candidate.State :=
  ⟨BatchPacket.coreResult r.core.input, r.matching, r.seen, r.remaining, r.output⟩
def tableFuel (r : Candidate.State) : Nat := 8 + BatchPacket.coreFuel r.core.input

theorem loadTable_exec (r : Candidate.State) :
    Exec loadTable r.store (tableFuel r) (tableResult r).store :=
  Frame.execution (Exec.seq (resetCore_exec r.core) (BatchPacket.core_exec r.core.input)) r.frame

theorem tableFuel_bound (r : Candidate.State) : tableFuel r ≤ 33 * r.core.input.length + 50 := by
  have bound := BatchPacket.coreFuel_bound r.core.input
  simp only [tableFuel]
  omega

theorem tableResult_size (r : Candidate.State) :
    (tableResult r).core.input.length ≤ r.core.input.length ∧
      (tableResult r).core.output.length ≤ r.core.input.length := by
  have bound := BatchPacket.core_size r.core.input
  change (BatchPacket.coreResult r.core.input).input.length ≤ r.core.input.length ∧
    (BatchPacket.coreResult r.core.input).output.length ≤ r.core.input.length
  constructor <;> omega

def saveCount : Block 13 := .action (.copy 11 1)
def counted (r : Candidate.State) : Candidate.State := ⟨r.core, r.matching, r.seen, r.core.target, r.output⟩

theorem saveCount_exec (r : Candidate.State) : Exec saveCount r.store 1 (counted r).store := .action _ _

def saveMatching : Block 13 := .action (.copy 9 8)
def matched (r : Candidate.State) : Candidate.State := ⟨r.core, r.core.output, r.seen, r.remaining, r.output⟩

theorem saveMatching_exec (r : Candidate.State) : Exec saveMatching r.store 1 (matched r).store := .action _ _

def saveSeen : Block 13 := .action (.copy 10 8)
def traced (r : Candidate.State) : Candidate.State := ⟨r.core, r.matching, r.core.output, r.remaining, r.output⟩

theorem saveSeen_exec (r : Candidate.State) : Exec saveSeen r.store 1 (traced r).store := .action _ _

def startCandidates : Block 13 :=
  .seq (Frame.block 4 resetCore) (.seq (.action (.clear 12)) (.action (.push 12 false)))
def started (r : Candidate.State) : Candidate.State :=
  ⟨initialRegisters r.core.input, r.matching, r.seen, r.remaining, [false]⟩

theorem startCandidates_exec (r : Candidate.State) :
    Exec startCandidates r.store 10 (started r).store :=
  Exec.seq (Frame.execution (resetCore_exec r.core) r.frame)
    (Exec.seq (.action _ _) (.action _ _))

end PNP.Concrete.NormalizerBlocks.CandidatePacket
