import PNP.Concrete.ResidualReduction.SourceReplayFamilyFields

/-! Literal arbitrary-family prefix reader. A stored unary dimension fixes
row width; the row count is read from the input and its product countdown is
constructed by existing finite loops. The unread suffix is preserved, even
when it contains another field or record. -/

namespace PNP.Concrete.ResidualReduction.SourceReplayFamily
open PNP.Concrete PNP.Concrete.BitRegister PNP.Concrete.NormalizerBlocks
open PNP.Concrete.NormalizerBlocks.Occurrence
open PNP.Concrete.ResidualReduction.SourceMatrixPacket
open PNP.Concrete.ResidualReduction.SourceFamilyLoader (wrap)
open PNP.Concrete.ResidualReduction.SourceReplayFamilyFields
open PNP.Concrete.ResidualReduction.MatrixInstructions

def initial (n : Nat) (input : BitString) : State :=
  wrap ⟨SourceReplayParserState.blank input [],List.replicate n true,[],[]⟩ []
def header (n : Nat) (input : BitString) : State :=
  wrap ⟨MatrixStrictHeader.result input (SourceReplayParserState.blank [] []),List.replicate n true,[],[]⟩ []
def ready (n rows : Nat) (input : BitString) : State :=
  wrap ⟨{SourceReplayParserState.blank (input.drop ((2 * n + 3) * rows)) (input.take ((2 * n + 3) * rows)) with mode := if (2 * n + 3) * rows ≤ input.length then [true] else []},List.replicate n true,[],[]⟩ (List.replicate rows true)
def result (n : Nat) (input : BitString) : State :=
  wrap ⟨{SourceReplayParserState.blank (rest n input) (payload n input) with mode := if valid n input then [true] else []},List.replicate n true,[],[]⟩ (List.replicate (count input) true)

def clearCore : Block 9 :=
  .seq (.action (.clear 1)) <| .seq (.action (.clear 2)) <|
  .seq (.action (.clear 3)) <| .seq (.action (.clear 4)) <|
  .seq (.action (.clear 5)) <| .seq (.action (.clear 6)) <|
  .seq (.action (.clear 7)) (.action (.clear 8))
theorem clearCore_exec (r : Registers) :
    Exec clearCore r.store 8 (SourceReplayParserState.blank r.input []).store :=
  Exec.seq (.action _ _) <| Exec.seq (.action _ _) <| Exec.seq (.action _ _) <|
  Exec.seq (.action _ _) <| Exec.seq (.action _ _) <| Exec.seq (.action _ _) <|
  Exec.seq (.action _ _) (.action _ _)
def clearWorking : Block 16 := lift9 clearCore
theorem clearWorking_exec (r : State) :
    Exec clearWorking r.store 8
      (setCore r (SourceReplayParserState.blank r.core.core.core.input [])).store :=
  lift9_exec clearCore r 8 _ (clearCore_exec r.core.core.core)

def failure : Block 16 := .seq (.action (.copy 15 1)) clearWorking
def success : Block 16 := .seq SourceFamilyLoader.seed (.seq SourceFamilyLoader.block
  (.seq (lift9 ClauseQuery.reverseLoop) (.action (.clear 1))))
def successFuel (n rows : Nat) (input : BitString) : Nat :=
  3 * n + 14 + SourceFamilyLoader.fuel n rows + 4 * (input.take ((2 * n + 3) * rows)).length

theorem success_exec (n rows : Nat) (input : BitString) :
    Exec success (SourceFamilyLoader.headerState n rows input).store (successFuel n rows input) (ready n rows input).store := by
  let copied := SourceFamilyLoader.result n rows input
  let after := setCore copied {copied.core.core.core with excess := [],output := input.take ((2 * n + 3) * rows)}
  have reverseCore : Exec ClauseQuery.reverseLoop copied.core.core.core.store
      (4 * (input.take ((2 * n + 3) * rows)).length + 1) after.core.core.core.store := by
    have checked := ClauseQuery.reverse_exec {copied.core.core.core with excess := []}
      (input.take ((2 * n + 3) * rows)).reverse
    simpa only [copied,after,setCore,SourceFamilyLoader.result,MatrixCountedPayload.result,
      SourceFamilyLoader.start,wrap,base,List.append_nil,List.reverse_reverse,List.length_reverse] using checked
  have reverse := lift9_exec ClauseQuery.reverseLoop copied _ after.core.core.core reverseCore
  have clear : Exec (.action (.clear (1 : Fin 16))) after.store 1 (ready n rows input).store := .action _ _
  have cost : successFuel n rows input =
      (3 * n + 12) + (SourceFamilyLoader.fuel n rows +
        ((4 * (input.take ((2 * n + 3) * rows)).length + 1) + 1)) := by
    unfold successFuel
    omega
  simpa only [success,cost,after,copied] using Exec.seq (SourceFamilyLoader.seed_exec n rows input)
    (Exec.seq (SourceFamilyLoader.block_exec n rows input) (Exec.seq reverse clear))

theorem header_exec (n : Nat) (input : BitString) :
    Exec (lift9 MatrixStrictHeader.block) (initial n input).store (MatrixStrictHeader.blockFuel input) (header n input).store :=
  lift9_exec MatrixStrictHeader.block (initial n input) _ (MatrixStrictHeader.result input (SourceReplayParserState.blank [] []))
    (MatrixStrictHeader.block_exec input (SourceReplayParserState.blank [] []))

theorem failure_exec (n : Nat) (input : BitString) (bad : (MatrixStrictHeader.scan input).terminated = false) :
    Exec failure (header n input).store 9 (result n input).store := by
  have empty := MatrixInputFields.scan_failure_rest input bad
  let saved := {header n input with rows := List.replicate (count input) true}
  have target : (header n input).core.core.core.target = List.replicate (count input) true := by
    change List.replicate (count input) true ++ [] = _
    rw [List.append_nil]
  have first : Exec (.action (.copy (15 : Fin 16) 1)) (header n input).store 1 saved.store := by
    have copied : Exec (.action (.copy (15 : Fin 16) 1)) (header n input).store 1
        ({header n input with rows := (header n input).core.core.core.target}).store := .action _ _
    rw [target] at copied
    exact copied
  have last := clearWorking_exec saved
  simpa only [failure,saved,header,result,valid,payload,rest,MatrixStrictHeader.result,
    SourceReplayParserState.blank,setCore,wrap,count,bad,empty,ite_self,List.drop_nil,List.take_nil,Bool.false_eq_true,↓reduceIte,List.append_nil] using Exec.seq first last

def select : Block 16 := .branch 4 failure failure success
def block : Block 16 := .seq (lift9 MatrixStrictHeader.block) select
def fuel (n : Nat) (input : BitString) : Nat :=
  MatrixStrictHeader.blockFuel input + 1 +
    (if (MatrixStrictHeader.scan input).terminated then
      successFuel n (count input) (MatrixStrictHeader.scan input).rest else 9)

theorem block_exec (n : Nat) (input : BitString) :
    Exec block (initial n input).store (fuel n input) (result n input).store := by
  have first := header_exec n input
  cases flag : (MatrixStrictHeader.scan input).terminated with
  | false =>
    have read : (header n input).store.get 4 = [] := by
      simp only [header,MatrixStrictHeader.result,SourceReplayParserState.blank,flag,Bool.false_eq_true,↓reduceIte,wrap,State.store]
      rfl
    have cost : fuel n input = MatrixStrictHeader.blockFuel input + (1 + 9) := by
      simp only [fuel,flag,Bool.false_eq_true,↓reduceIte] <;> omega
    simpa only [block,select,cost] using Exec.seq first (Exec.empty read (failure_exec n input flag))
  | true =>
    have head : header n input = SourceFamilyLoader.headerState n (count input) (MatrixStrictHeader.scan input).rest := by
      simp only [header,SourceFamilyLoader.headerState,MatrixStrictHeader.result,SourceReplayParserState.blank,flag,↓reduceIte,List.append_nil,base,count]
    have finished : ready n (count input) (MatrixStrictHeader.scan input).rest = result n input := by
      by_cases enough : (2 * n + 3) * count input ≤ (MatrixStrictHeader.scan input).rest.length <;>
        simp only [ready,result,payload,rest,valid,amount,flag,enough,↓reduceIte,Bool.false_eq_true]
    have read : (header n input).store.get 4 = [true] := by rw [head]; rfl
    have last := success_exec n (count input) (MatrixStrictHeader.scan input).rest
    rw [← head,finished] at last
    have cost : fuel n input = MatrixStrictHeader.blockFuel input +
        (1 + successFuel n (count input) (MatrixStrictHeader.scan input).rest) := by
      simp only [fuel,flag,↓reduceIte]; omega
    simpa only [block,select,cost] using Exec.seq first (Exec.one read last)

theorem loader_cost (n rows : Nat) : SourceFamilyLoader.fuel n rows = (16 * n + 28) * rows + 2 := by
  simp only [SourceFamilyLoader.fuel,Nat.mul_add,Nat.add_mul,Nat.mul_assoc]
  omega

theorem fuel_bound (n : Nat) (input : BitString) :
    fuel n input ≤ (16 * n + 36) * input.length + 3 * n + 26 := by
  have header := MatrixStrictHeader.blockFuel_bound input
  have rows := count_bound input
  have bytes := payload_bound n input
  have product := Nat.mul_le_mul_left (16 * n + 28) rows
  cases flag : (MatrixStrictHeader.scan input).terminated <;>
    simp only [fuel,flag,Bool.false_eq_true,↓reduceIte,successFuel,loader_cost,
      Nat.add_mul,payload,amount] at * <;> omega

end PNP.Concrete.ResidualReduction.SourceReplayFamily
