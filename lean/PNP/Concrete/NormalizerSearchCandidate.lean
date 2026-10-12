/-
Copyright (c) 2026 PNP Labs.

Complete candidate selection from the search's own matching and seen
tables. The variable count is reread from the protected original input;
candidate indices retain the verified increasing source order.
-/
import PNP.Concrete.NormalizerSearchTrace

namespace PNP.Concrete.NormalizerBlocks.Search
open BitRegister

def copyTablePrefix : Block 13 := .seq (.action (.copy 10 8)) (.action (.copy 9 12))
def tablePrefixCopied (r : Candidate.State) : Candidate.State := {r with matching := r.output, seen := r.core.output}
theorem copyTablePrefix_exec (r : Candidate.State) : Exec copyTablePrefix r.store 2 (tablePrefixCopied r).store :=
  Exec.seq (.action _ _) (.action _ _)

def copyTables : Block 29 := liftCandidate copyTablePrefix
def tablesCopied (r : State) : State := r.withCandidate (tablePrefixCopied r.candidate)
theorem copyTables_exec (r : State) : Exec copyTables r.store 2 (tablesCopied r).store :=
  liftCandidate_exec _ r _ _ (copyTablePrefix_exec r.candidate)

def loadOriginal : Block 29 := .action (.copy (Frame.index 1 (0 : Fin 28)) (Frame.frameIndex 28 (0 : Fin 1)))
def originalLoaded (r : State) : State := r.withRegisters {r.registers with input := r.original}
theorem loadOriginal_exec (r : State) : Exec loadOriginal r.store 1 (originalLoaded r).store := by
  have original : r.frame.get (0 : Fin 1) = r.original := rfl
  have updated : r.core.store.set (0 : Fin 28) r.original =
      (r.core.withRegisters {r.registers with input := r.original}).store := rfl
  have checked := Exec.action (.copy (Frame.index 1 (0 : Fin 28)) (Frame.frameIndex 28 (0 : Fin 1))) r.store
  simp only [Action.update, Action.instruction, Instruction.update, State.store, Frame.get_frame, Frame.set_core] at checked
  rw [original, updated] at checked
  simpa only [loadOriginal, originalLoaded, State.withRegisters, State.withCore, State.store, State.frame] using checked

def saveTables : Block 29 := .seq copyTables loadOriginal
def tablesSaved (r : State) : State := originalLoaded (tablesCopied r)
theorem saveTables_exec (r : State) : Exec saveTables r.store 3 (tablesSaved r).store :=
  Exec.seq (copyTables_exec r) (loadOriginal_exec (tablesCopied r))

def readWidth : Block 29 := liftCore (.seq CandidatePacket.resetCore TableInit.header)
def widthRead (r : State) : State := r.withRegisters (TableInit.readCount r.registers.input).state
def readWidthFuel (r : State) : Nat := 8 + TableInit.headerFuel r.registers.input
theorem readWidth_exec (r : State) : Exec readWidth r.store (readWidthFuel r) (widthRead r).store :=
  liftCore_exec _ r _ _ (Exec.seq (CandidatePacket.resetCore_exec r.registers) (TableInit.header_exec r.registers.input))

def saveWidth : Block 29 := .action (.copy 11 1)
def widthSaved (r : State) : State := r.withCandidate {r.candidate with remaining := r.registers.target}
theorem saveWidth_exec (r : State) : Exec saveWidth r.store 1 (widthSaved r).store := .action _ _

def startCandidates : Block 29 := liftCandidate CandidatePacket.startCandidates
def candidatesStarted (r : State) : State := r.withCandidate (CandidatePacket.started r.candidate)
theorem startCandidates_exec (r : State) : Exec startCandidates r.store 10 (candidatesStarted r).store :=
  liftCandidate_exec _ r _ _ (CandidatePacket.startCandidates_exec r.candidate)

def prepareCandidate : Block 29 := .seq saveTables (.seq readWidth (.seq saveWidth startCandidates))
def candidatePrepared (r : State) : State := candidatesStarted (widthSaved (widthRead (tablesSaved r)))
def prepareCandidateFuel (r : State) : Nat := 22 + TableInit.headerFuel r.original
theorem prepareCandidate_exec (r : State) :
    Exec prepareCandidate r.store (prepareCandidateFuel r) (candidatePrepared r).store := by
  have checked := Exec.seq (saveTables_exec r) <| Exec.seq (readWidth_exec (tablesSaved r)) <|
    Exec.seq (saveWidth_exec (widthRead (tablesSaved r))) (startCandidates_exec (widthSaved (widthRead (tablesSaved r))))
  change Exec prepareCandidate r.store (3 + ((8 + TableInit.headerFuel r.original) + (1 + 10))) (candidatePrepared r).store at checked
  have cost : 3 + ((8 + TableInit.headerFuel r.original) + (1 + 10)) = prepareCandidateFuel r := by
    unfold prepareCandidateFuel
    omega
  rw [cost] at checked
  exact checked
theorem prepareCandidateFuel_bound (r : State) : prepareCandidateFuel r ≤ 4 * r.original.length + 28 := by
  have checked := TableInit.headerFuel_bound r.original
  unfold prepareCandidateFuel
  omega

theorem candidatePrepared_fields (r : State) :
    (candidatePrepared r).candidate.matching = r.parent.graph.core.matching ∧
      (candidatePrepared r).candidate.seen = r.registers.output ∧
        (candidatePrepared r).candidate.remaining = (TableInit.readCount r.original).state.target ∧
          (candidatePrepared r).candidate.core.target = [] ∧
            (candidatePrepared r).candidate.output = [false] ∧
              (candidatePrepared r).core.core.trace = r.core.core.trace ∧
                (candidatePrepared r).original = r.original := ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

def selectCandidate : Block 29 := liftCandidate Candidate.loop
def candidateSelected (r : State) : State := r.withCandidate (Candidate.whole r.candidate).state
def selectCandidateFuel (r : State) : Nat := (Candidate.whole r.candidate).fuel
theorem selectCandidate_exec (r : State) :
    Exec selectCandidate r.store (selectCandidateFuel r) (candidateSelected r).store :=
  liftCandidate_exec _ r _ _ (Candidate.whole_exec r.candidate)

def select : Block 29 := .seq prepareCandidate selectCandidate
def selected (r : State) : State := candidateSelected (candidatePrepared r)
def selectFuel (r : State) : Nat := prepareCandidateFuel r + selectCandidateFuel (candidatePrepared r)
theorem select_exec (r : State) : Exec select r.store (selectFuel r) (selected r).store :=
  Exec.seq (prepareCandidate_exec r) (selectCandidate_exec (candidatePrepared r))

theorem selected_frame (r : State) :
    (selected r).core.core.trace = r.core.core.trace ∧ (selected r).original = r.original := ⟨rfl, rfl⟩

theorem selected_canonical (r : State) (variables : Nat) (matching seen : MatchingTable.Entries)
    (width : (TableInit.readCount r.original).state.target = List.replicate variables true)
    (matchingRead : r.parent.graph.core.matching = MatchingTable.encode matching)
    (seenRead : r.registers.output = MatchingTable.encode seen) :
    (selected r).parent.graph.core.matching = TableOwner.answer (Candidate.selectFrom matching seen variables 0) := by
  have fields := candidatePrepared_fields r
  have counter := fields.2.2.1.trans width
  have enough : variables < (candidatePrepared r).candidate.remaining.length + 1 := by
    rw [counter, List.length_replicate]
    exact Nat.lt_succ_self _
  exact Candidate.run_canonical variables 0 _ (candidatePrepared r).candidate matching seen
    counter fields.2.2.2.1 (fields.1.trans matchingRead) (fields.2.1.trans seenRead) fields.2.2.2.2.1 enough

end PNP.Concrete.NormalizerBlocks.Search
