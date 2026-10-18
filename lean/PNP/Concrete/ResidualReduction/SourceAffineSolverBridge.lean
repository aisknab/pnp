import PNP.Concrete.ResidualReduction.SourceAffineInputBridge

/-! The search consumes the actual map and unary parameter counter retained
by the linear solver. All copies and resets are literal instructions. There
is no second solution decoder and no caller-supplied map or activity premise. -/

namespace PNP.Concrete.ResidualReduction.SourceAffineInput
open PNP.Concrete PNP.Concrete.BitRegister
open PNP.Concrete.NormalizerBlocks
open PNP.Concrete.ResidualReduction.FactoredContraction
open PNP.Concrete.ResidualReduction.BinaryLinear
open PNP.Concrete.ResidualReduction.SourceMatrixEncoding
open PNP.Concrete.ResidualReduction.MatrixSolutionEncoding
open PNP.Concrete.ResidualReduction.SourceAffineOutput (core setCore setRegisters)

def solutionState {n : Nat} (F : Family n) (s : Space F.length) : SourceAffineSearch.State :=
  saved F (MatrixSolutionSerialization.result s)
theorem solutionState_eq {n : Nat} (F : Family n) (s : Space F.length)
    (computed : solve F.length (SourceClosure.affineMaskRows F) = some s) :
    solverResult F = solutionState F s := by
  unfold solverResult solutionState
  rw [result_some F.length (SourceClosure.affineMaskRows F) s computed]

def sourceSaved {n : Nat} (F : Family n) (s : Space F.length) : SourceAffineSearch.State :=
  ⟨⟨⟨⟨MatrixSolutionSerialization.result s, []⟩, familyBits F, List.replicate n true, List.replicate F.length true⟩,
      [], [], [], [], (affineMatrixPacket F).tail⟩, []⟩
def mapSaved {n : Nat} (F : Family n) (s : Space F.length) : SourceAffineSearch.State :=
  {sourceSaved F s with core := {(sourceSaved F s).core with sourceMap := mapBits s.forms, parameters := List.replicate (s.parameters + 1) true}}

def transferSource : Block 22 := .seq (.action (.copy 13 12)) (.action (.clear 12))
def transferMap : Block 22 := .seq (.action (.copy 16 0)) (.action (.copy 17 1))
def transferData : Block 22 := .seq transferSource transferMap
theorem transferData_exec {n : Nat} (F : Family n) (s : Space F.length) :
    Exec transferData (solutionState F s).store 4 (mapSaved F s).store := by
  have source : Exec transferSource (solutionState F s).store 2 (sourceSaved F s).store :=
    Exec.seq (.action _ _) (.action _ _)
  have map : Exec transferMap (sourceSaved F s).store 2 (mapSaved F s).store :=
    Exec.seq (.action _ _) (.action _ _)
  exact Exec.seq source map

def countersSaved {n : Nat} (F : Family n) (s : Space F.length) : SourceAffineSearch.State :=
  ⟨⟨⟨⟨{MatrixSolutionSerialization.result s with width := List.replicate n true, pending := List.replicate n true}, []⟩,
      familyBits F, List.replicate n true, []⟩,
      mapBits s.forms, List.replicate s.parameters true, [], [], (affineMatrixPacket F).tail⟩, []⟩
def transferCounters : Block 22 := .seq (.action (.pop 17)) <| .seq (.action (.clear 15)) <|
  .seq (.action (.copy 9 14)) (.action (.copy 11 14))

theorem transferCounters_exec {n : Nat} (F : Family n) (s : Space F.length) :
    Exec transferCounters (mapSaved F s).store 4 (countersSaved F s).store := by
  let pop := {mapSaved F s with core := {(mapSaved F s).core with parameters := List.replicate s.parameters true}}
  let clear := {pop with core := {pop.core with core := {pop.core.core with direction := []}}}
  let width := setCore clear {core clear with width := List.replicate n true}
  have a : Exec (.action (.pop (17 : Fin 22))) (mapSaved F s).store 1 pop.store := .action _ _
  have b : Exec (.action (.clear (15 : Fin 22))) pop.store 1 clear.store := .action _ _
  have c : Exec (.action (.copy (9 : Fin 22) 14)) clear.store 1 width.store := .action _ _
  have d : Exec (.action (.copy (11 : Fin 22) 14)) width.store 1 (countersSaved F s).store := .action _ _
  exact Exec.seq a (Exec.seq b (Exec.seq c d))

def finishSearch : Block 22 := .seq (.action (.copy 20 14)) <|
  .seq (.seq (.action (.clear 0)) (.action (.clear 1))) <|
  .seq (.seq (.action (.clear 7)) (.action (.clear 8)))
    (.action (.push 8 false))

theorem finishSearch_exec {n : Nat} (F : Family n) (s : Space F.length) :
    Exec finishSearch (countersSaved F s).store 6
      (SourceAffineSearch.ready F s.forms false 0 0 n 0 false).store := by
  let countdown := withScratch (countersSaved F s) (List.replicate n true)
  let input := setRegisters countdown {(core countdown).core with input := [], target := []}
  let clean := setRegisters input {(core input).core with reserved := [], output := []}
  have a : Exec (.action (.copy (20 : Fin 22) 14)) (countersSaved F s).store 1 countdown.store := .action _ _
  have b : Exec (.seq (.action (.clear (0 : Fin 22))) (.action (.clear 1))) countdown.store 2 input.store :=
    Exec.seq (.action _ _) (.action _ _)
  have c : Exec (.seq (.action (.clear (7 : Fin 22))) (.action (.clear 8))) input.store 2 clean.store :=
    Exec.seq (.action _ _) (.action _ _)
  have d : Exec (.action (.push (8 : Fin 22) false)) clean.store 1
      (SourceAffineSearch.ready F s.forms false 0 0 n 0 false).store := .action _ _
  have checked := Exec.seq a (Exec.seq b (Exec.seq c d))
  exact checked

def prepareSearch : Block 22 := .seq transferData (.seq transferCounters finishSearch)
theorem prepareSearch_exec {n : Nat} (F : Family n) (s : Space F.length) :
    Exec prepareSearch (solutionState F s).store 14
      (SourceAffineSearch.ready F s.forms false 0 0 n 0 false).store :=
  Exec.seq (transferData_exec F s) (Exec.seq (transferCounters_exec F s) (finishSearch_exec F s))

def search : Block 22 := .seq prepareSearch SourceAffineOutput.query
theorem search_exec {n : Nat} (F : Family n) (s : Space F.length)
    (computed : solve F.length (SourceClosure.affineMaskRows F) = some s) :
    ∃ used after, Exec search (solverResult F).store used after ∧
      after.get 8 = (SourceAffineOutput.witnessCodec F.length n).encode (SourceClosure.sourceAffineQuery F) ∧
      used ≤ 14 + SourceAffineOutput.originalInputBudget (codec.encode ⟨n, F⟩).length := by
  obtain ⟨used, after, execution, bytes, bound⟩ := SourceAffineOutput.computed_query_exec F s computed
  rw [solutionState_eq F s computed]
  refine ⟨14 + used, after, Exec.seq (prepareSearch_exec F s) execution, bytes, ?_⟩
  exact Nat.add_le_add_left bound 14

def select : Block 22 := .branch 8 .skip .skip search
theorem select_exec {n : Nat} (F : Family n) :
    ∃ used after, Exec select (solverResult F).store used after ∧
      after.get 8 = (SourceAffineOutput.witnessCodec F.length n).encode (SourceClosure.sourceAffineQuery F) ∧
      used ≤ 15 + SourceAffineOutput.originalInputBudget (codec.encode ⟨n, F⟩).length := by
  cases computed : solve F.length (SourceClosure.affineMaskRows F) with
  | none =>
    have output : (solverResult F).store.get 8 = [false] := by
      change (core (solverResult F)).core.output = [false]
      rw [solver_output, computed]; rfl
    refine ⟨2, (solverResult F).store, Exec.zero (source := (8 : Fin 22)) output (.skip _), ?_, ?_⟩
    · rw [output, SourceClosure.sourceAffineQuery, computed]; rfl
    · omega
  | some s =>
    obtain ⟨used, after, execution, bytes, bound⟩ := search_exec F s computed
    have output : (solverResult F).store.get 8 = true ::
        (List.replicate s.parameters true ++ false :: mapBits s.forms) := by
      change (core (solverResult F)).core.output = _
      rw [solver_output, computed]
      exact MatrixSolutionSerialization.solution_some_bits s
    refine ⟨1 + used, after, Exec.one (source := (8 : Fin 22)) output execution, bytes, ?_⟩
    omega

end PNP.Concrete.ResidualReduction.SourceAffineInput
