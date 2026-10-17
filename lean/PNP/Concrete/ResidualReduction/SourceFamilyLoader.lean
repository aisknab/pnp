import PNP.Concrete.ResidualReduction.SourceFamilyInput

/-! Literal family-payload validation. Two unary headers determine the exact
width 2*n+3 and row count. The width, product countdown and copied source bytes
are all constructed by finite instructions. Truncated and trailing payloads
remain rejected, including zero-dimensional and empty families. -/

namespace PNP.Concrete.ResidualReduction.SourceFamilyLoader
open PNP.Concrete PNP.Concrete.BitRegister
open PNP.Concrete.NormalizerBlocks PNP.Concrete.NormalizerBlocks.Occurrence
open PNP.Concrete.ResidualReduction.FactoredContraction
open PNP.Concrete.ResidualReduction.MatrixInstructions
open PNP.Concrete.ResidualReduction.SourceMatrixPacket

def wrap (core : MatrixReconstruction.State) (rows : BitString) : State := ⟨⟨core, [], [], []⟩, rows⟩
def rawStart (input : BitString) : State := wrap (MatrixInputHeaders.start input) []
def rawHeaders (input : BitString) : State := wrap (MatrixInputHeaders.result input) []
theorem headers_exec (input : BitString) :
    Exec (lift12 MatrixInputHeaders.block) (rawStart input).store (MatrixInputHeaders.fuel input)
      (rawHeaders input).store := lift12_exec _ (rawStart input) _ (MatrixInputHeaders.result input)
        (MatrixInputHeaders.block_exec input)

def headerState (n count : Nat) (input : BitString) : State :=
  wrap ⟨{base count [] with input := input, sign := [true]}, List.replicate n true, [], []⟩ []
theorem headers_valid (input : BitString) (success : (MatrixInputFields.fields input).terminated = true) :
    rawHeaders input = headerState (MatrixInputFields.fields input).dimension
      (MatrixInputFields.fields input).rows (MatrixInputFields.fields input).payload := by
  simp only [rawHeaders, MatrixInputHeaders.result, headerState, success, if_true, base, List.replicate_zero]

def start (n count : Nat) (input : BitString) : State :=
  wrap ⟨{base (2 * n + 3) [] with input := input, mode := [true]}, List.replicate n true, [], List.replicate count true⟩
    (List.replicate count true)

def seedPrefix : Block 16 := .seq (.action (.copy 15 1))
  (.seq (.action (.copy 2 9)) (.action (.copy 6 9)))
def seedWidth : Block 16 := .seq (.action (.push 2 true))
  (.seq (.action (.push 2 true)) (.action (.push 2 true)))
def seedFinish : Block 16 := .seq (.action (.copy 1 2)) <| .seq (.action (.clear 2)) <|
  .seq (.action (.copy 11 15)) <| .seq (.action (.copy 5 4)) (.action (.clear 4))
def seedSuffix : Block 16 := .seq seedWidth seedFinish
def seed : Block 16 := .seq seedPrefix (.seq (lift9 MatrixPayloadCounter.addLoop) seedSuffix)

theorem seed_exec (n count : Nat) (input : BitString) :
    Exec seed (headerState n count input).store (3 * n + 12) (start n count input).store := by
  let loaded : State := wrap
    ⟨{base count [] with input := input, sign := [true], remaining := List.replicate n true, active := List.replicate n true},
      List.replicate n true, [], []⟩ (List.replicate count true)
  let added : State := wrap
    ⟨{base count [] with input := input, sign := [true], remaining := List.replicate (2 * n) true},
      List.replicate n true, [], []⟩ (List.replicate count true)
  have seedRead : Exec seedPrefix (headerState n count input).store 3 loaded.store :=
    Exec.seq (.action _ _) (Exec.seq (.action _ _) (.action _ _))
  have core : Exec MatrixPayloadCounter.addLoop loaded.core.core.core.store (3 * n + 1) added.core.core.core.store := by
    have doubled : n + n = 2 * n := by omega
    simpa only [loaded, added, wrap, base, MatrixStrictHeader.replicate_add, doubled] using
      MatrixPayloadCounter.addLoop_exec n {loaded.core.core.core with active := []}
  have middle := lift9_exec MatrixPayloadCounter.addLoop loaded (3 * n + 1) added.core.core.core core
  let wide := setCore added {added.core.core.core with remaining := List.replicate (2 * n + 3) true}
  have width : Exec seedWidth added.store 3 wide.store :=
    Exec.seq (.action _ _) (Exec.seq (.action _ _) (.action _ _))
  have finished : Exec seedFinish wide.store 5 (start n count input).store :=
    Exec.seq (.action _ _) (Exec.seq (.action _ _) (Exec.seq (.action _ _)
      (Exec.seq (.action _ _) (.action _ _))))
  have suffix : Exec seedSuffix added.store 8 (start n count input).store :=
    Exec.seq width finished
  have cost : 3 * n + 12 = 3 + ((3 * n + 1) + 8) := by omega
  simpa only [seed, cost, loaded, added, wrap] using Exec.seq seedRead (Exec.seq middle suffix)

def counted (n count : Nat) (input : BitString) : State :=
  wrap (MatrixPayloadCounter.counted (2 * n + 3) 0 ((2 * n + 3) * count) (start n count input).core.core)
    (List.replicate count true)
def result (n count : Nat) (input : BitString) : State :=
  wrap ⟨MatrixCountedPayload.result ((2 * n + 3) * count) input (start n count input).core.core.core,
    List.replicate n true, [], []⟩ (List.replicate count true)
def block : Block 16 := .seq (lift12 MatrixPayloadCounter.loop) (lift9 MatrixCountedPayload.loop)
def fuel (n count : Nat) : Nat := ((3 * (2 * n + 3) + 4) * count + 1) + (5 * ((2 * n + 3) * count) + 1)

theorem block_exec (n count : Nat) (input : BitString) :
    Exec block (start n count input).store (fuel n count) (result n count input).store := by
  have coreCounter : Exec MatrixPayloadCounter.loop (start n count input).core.core.store
      ((3 * (2 * n + 3) + 4) * count + 1) (counted n count input).core.core.store := by
    simpa only [start, counted, wrap, MatrixPayloadCounter.counted, base,
      Nat.add_zero, List.replicate_zero] using
      MatrixPayloadCounter.loop_exec (2 * n + 3) count 0 (start n count input).core.core
  have counter : Exec (lift12 MatrixPayloadCounter.loop) (start n count input).store
      ((3 * (2 * n + 3) + 4) * count + 1) (counted n count input).store :=
    lift12_exec _ (start n count input) _ (counted n count input).core.core coreCounter
  have coreCopy : Exec MatrixCountedPayload.loop (counted n count input).core.core.core.store
      (5 * ((2 * n + 3) * count) + 1) (result n count input).core.core.core.store :=
    MatrixCountedPayload.loop_exec ((2 * n + 3) * count) input (start n count input).core.core.core
  have copy : Exec (lift9 MatrixCountedPayload.loop) (counted n count input).store
      (5 * ((2 * n + 3) * count) + 1) (result n count input).store :=
    lift9_exec _ (counted n count input) _ (result n count input).core.core.core coreCopy
  exact Exec.seq counter copy

theorem valid_iff (n count : Nat) (input : BitString) :
    (result n count input).core.core.core.mode = [true] ∧ (result n count input).core.core.core.input = [] ↔
      input.length = (2 * n + 3) * count :=
  MatrixCountedPayload.exact_payload_iff ((2 * n + 3) * count) input (base (2 * n + 3) [])

def validated (n count : Nat) (input : BitString) : State :=
  wrap ⟨{base (2 * n + 3) [] with excess := input.reverse, mode := [true]}, List.replicate n true, [], []⟩
    (List.replicate count true)
theorem result_complete (n count : Nat) (input : BitString) (length : input.length = (2 * n + 3) * count) :
    result n count input = validated n count input := by
  simp only [result, MatrixCountedPayload.result, start, wrap, base, ← length,
    List.drop_length, List.take_length, List.append_nil, if_pos (Nat.le_refl input.length)]
  rfl

def prepared (n count : Nat) (input : BitString) : State :=
  wrap ⟨{base 0 [] with input := input}, List.replicate n true, [], []⟩ (List.replicate count true)
def reset : Block 16 := .seq (.action (.copy 0 8)) <| .seq (.action (.clear 8)) <|
  .seq (.action (.clear 1)) (.action (.clear 5))
def prepare : Block 16 := .seq (lift9 ClauseQuery.reverseLoop) reset
theorem prepare_exec (n count : Nat) (input : BitString) :
    Exec prepare (validated n count input).store (4 * input.length + 5) (prepared n count input).store := by
  let reversed := setCore (validated n count input)
    {(validated n count input).core.core.core with excess := [], output := input}
  have core : Exec ClauseQuery.reverseLoop (validated n count input).core.core.core.store (4 * input.length + 1)
      reversed.core.core.core.store := by
    simpa only [validated, reversed, setCore, wrap, base, List.length_reverse, List.reverse_reverse, List.append_nil] using
      ClauseQuery.reverse_exec {(validated n count input).core.core.core with excess := []} input.reverse
  have reverse : Exec (lift9 ClauseQuery.reverseLoop) (validated n count input).store
      (4 * input.length + 1) reversed.store := lift9_exec _ (validated n count input) _ reversed.core.core.core core
  have finish : Exec reset reversed.store 4 (prepared n count input).store :=
    Exec.seq (.action _ _) (Exec.seq (.action _ _) (Exec.seq (.action _ _) (.action _ _)))
  have cost : 4 * input.length + 5 = (4 * input.length + 1) + 4 := by omega
  simpa only [prepare, cost] using Exec.seq reverse finish

theorem prepared_family {n : Nat} (F : Family n) :
    prepared n F.length (SourceMatrixEncoding.familyBits F) = SourceMatrixPacket.inputState F := rfl

end PNP.Concrete.ResidualReduction.SourceFamilyLoader
