import PNP.Concrete.ResidualReduction.SourceHistoryBounds

/-! Strict all-bitstring entry to the history runner. The source headers and
entire fixed-width row payload are validated before the loop can become active.
The original input is the only initially populated word. -/

namespace PNP.Concrete.ResidualReduction.SourceHistoryInput
open PNP.Concrete PNP.Concrete.BitRegister PNP.Concrete.NormalizerBlocks
open PNP.Concrete.NormalizerBlocks.Occurrence
open PNP.Concrete.ResidualReduction.FactoredContraction
open PNP.Concrete.ResidualReduction.SourceHistoryEncoding
open PNP.Concrete.ResidualReduction.SourceHistoryState
open PNP.Concrete.ResidualReduction.SourceMatrixEncoding (codec familyBits)
open PNP.Concrete.ResidualReduction.MatrixInputFields (fields size_bounds)

def retained (input : BitString) : Saved := {emptySaved with current := input}
def loaded (r : Store 16) (input : BitString) : Store 63 :=
  full (Frame.join r (Store.empty 40)) (retained input)
def use16 (b : Block 16) : Block 63 := Frame.block 7 (Frame.block 40 b)
theorem use16_exec {b : Block 16} {r out : Store 16} {ticks : Nat}
    (h : Exec b r ticks out) (input : BitString) :
    Exec (use16 b) (loaded r input) ticks (loaded out input) :=
  Frame.execution (Frame.execution h (Store.empty 40)) (retained input).store
theorem loader_get (r : Store 16) (input : BitString) (i : Fin 16) :
    (loaded r input).get (Frame.index 47 i) = r.get i := by
  have outer := Frame.get_core (Frame.join r (Store.empty 40)) (retained input).store (Frame.index 40 i)
  exact outer.trans (Frame.get_core r (Store.empty 40) i)

def retain : Block 63 := .action (.copy 56 0)
theorem retain_exec (input : BitString) :
    Exec retain (initial input) 1 (loaded (SourceFamilyLoader.rawStart input).store input) := .action _ _
def failure : Block 63 := .seq reset (.action (.push 8 false))
def failed (input : BitString) : Store 63 := work [] [false] (retained input)
theorem failure_exec (r : Store 16) (input : BitString) :
    Exec failure (loaded r input) 58 (failed input) :=
  Exec.seq (reset_exec (Frame.join r (Store.empty 40)) (retained input)) (.action _ _)

def capture : Block 63 := .seq (save .dimension 9) <| .seq (save .rows 15) <|
  .seq reset (.action (.push 62 true))
theorem capture_exec (n : Nat) (F : Family n) :
    Exec capture (loaded (SourceFamilyLoader.result n F.length (familyBits F)).store (packet F)) 60
      (work [] [] (data F [])) := by
  let r := Frame.join (SourceFamilyLoader.result n F.length (familyBits F)).store (Store.empty 40)
  let s := retained (packet F)
  let dimension := fieldSet .dimension s (List.replicate n true)
  let both := fieldSet .rows dimension (List.replicate F.length true)
  have dimRead : r.get 9 = List.replicate n true :=
    (Frame.get_core (SourceFamilyLoader.result n F.length (familyBits F)).store (Store.empty 40) (9 : Fin 16)).trans rfl
  have rowRead : r.get 15 = List.replicate F.length true :=
    (Frame.get_core (SourceFamilyLoader.result n F.length (familyBits F)).store (Store.empty 40) (15 : Fin 16)).trans rfl
  have first := save_exec Field.dimension 9 r s
  rw [dimRead] at first
  have second := save_exec Field.rows 15 r dimension
  rw [rowRead] at second
  have clear := reset_exec r both
  have enable := field_push_exec Field.active
    (Frame.join (SourceScalarState.work []).store (Store.empty 47)) both true
  have activeSlot : Field.active.slot = (62 : Fin 63) := rfl
  rw [activeSlot] at enable
  have finish : Exec (.action (.push (62 : Fin 63) true)) (work [] [] both) 1
      (work [] [] (data F [])) := by
    simpa only [work,withCore,SourceScalarState.work,fieldSet,Field.word,both,dimension,s,retained,
      emptySaved,data,records,NativeNormalization.NativeBitCodec.encodeSeq,List.reverse_nil,
      List.length_nil,List.replicate_zero] using enable
  exact Exec.seq first (Exec.seq second (Exec.seq clear finish))

def endCheck : Block 63 := .branch 0 capture failure failure
def payloadCheck : Block 63 := .branch 5 failure failure endCheck
def parsed : Block 63 := .seq (use16 SourceFamilyLoader.seed) <|
  .seq (use16 SourceFamilyLoader.block) payloadCheck
def selection : Block 63 := .branch 4 failure failure parsed
def headers : Block 63 := use16 (SourceMatrixPacket.lift12 MatrixInputHeaders.block)
def block : Block 63 := .seq retain (.seq headers selection)
def budget (L : Nat) : Nat := 11 * L + SourceFamilyLoader.fuel L L + 100
def polynomial : NatPolynomial :=
  .add (.mul (.constant 16) (.mul .variable .variable)) (.linear 39 102)
theorem polynomial_eval (L : Nat) : polynomial.eval L = budget L := by
  simp only [polynomial,NatPolynomial.eval_add,NatPolynomial.eval_mul,NatPolynomial.eval_constant,
    NatPolynomial.eval_variable,NatPolynomial.eval_linear,budget,SourceFamilyLoader.fuel,
    Nat.add_mul,Nat.mul_add,Nat.mul_assoc]
  omega

theorem headers_exec (input : BitString) :
    Exec headers (loaded (SourceFamilyLoader.rawStart input).store input) (MatrixInputHeaders.fuel input)
      (loaded (SourceFamilyLoader.rawHeaders input).store input) :=
  use16_exec (SourceFamilyLoader.headers_exec input) input

theorem complete_check (n : Nat) (F : Family n) :
    Exec payloadCheck (loaded (SourceFamilyLoader.result n F.length (familyBits F)).store (packet F)) 62
      (work [] [] (data F [])) := by
  have completed := SourceFamilyLoader.result_complete n F.length (familyBits F)
    (SourceMatrixEncoding.familyBits_length F)
  have checked := capture_exec n F
  rw [completed] at checked ⊢
  exact Exec.one ((loader_get _ _ 5).trans rfl) (Exec.empty ((loader_get _ _ 0).trans rfl) checked)

theorem short_check (n count : Nat) (payload input : BitString)
    (short : ¬ (2 * n + 3) * count ≤ payload.length) :
    Exec payloadCheck (loaded (SourceFamilyLoader.result n count payload).store input) 59 (failed input) := by
  have flag : (SourceFamilyLoader.result n count payload).store.get 5 = [] := by
    change (if (2 * n + 3) * count ≤ payload.length then [true] else []) = []
    rw [if_neg short]
  exact Exec.empty ((loader_get _ input 5).trans flag) (failure_exec _ input)

theorem extra_check (n count : Nat) (payload input : BitString)
    (enough : (2 * n + 3) * count ≤ payload.length)
    (wrong : payload.length ≠ (2 * n + 3) * count) :
    Exec payloadCheck (loaded (SourceFamilyLoader.result n count payload).store input) 60 (failed input) := by
  have flag : (SourceFamilyLoader.result n count payload).store.get 5 = [true] := by
    change (if (2 * n + 3) * count ≤ payload.length then [true] else []) = [true]
    rw [if_pos enough]
  have nonempty : payload.drop ((2 * n + 3) * count) ≠ [] := by
    intro empty
    have bound := List.drop_eq_nil_iff.mp empty
    omega
  cases tail : payload.drop ((2 * n + 3) * count) with
  | nil => exact (nonempty tail).elim
  | cons bit rest =>
    have read : (SourceFamilyLoader.result n count payload).store.get 0 = bit :: rest := tail
    cases bit
    · exact Exec.one ((loader_get _ input 5).trans flag)
        (Exec.zero ((loader_get _ input 0).trans read) (failure_exec _ input))
    · exact Exec.one ((loader_get _ input 5).trans flag)
        (Exec.one ((loader_get _ input 0).trans read) (failure_exec _ input))

theorem valid_exec (n : Nat) (F : Family n) :
    ∃ used, Exec block (initial (packet F)) used (work [] [] (data F [])) ∧ used ≤ budget (packet F).length := by
  let input := codec.encode ⟨n,F⟩
  have success : (fields input).terminated = true := by rw [SourceFamilyInput.canonical_fields]
  have seed : Exec SourceFamilyLoader.seed (SourceFamilyLoader.rawHeaders input).store (3 * n + 12)
      (SourceFamilyLoader.start n F.length (familyBits F)).store := by
    rw [SourceFamilyLoader.headers_valid input success,SourceFamilyInput.canonical_fields]
    exact SourceFamilyLoader.seed_exec n F.length (familyBits F)
  have flag : (SourceFamilyLoader.rawHeaders input).store.get 4 = [true] := by
    change (if (fields input).terminated then [true] else []) = [true]
    rw [success]
    rfl
  refine ⟨1 + (MatrixInputHeaders.fuel input + (1 + ((3 * n + 12) +
    (SourceFamilyLoader.fuel n F.length + 62)))),
    Exec.seq (retain_exec input) (Exec.seq (headers_exec input)
      (Exec.one ((loader_get _ input 4).trans flag) (Exec.seq (use16_exec seed input)
        (Exec.seq (use16_exec (SourceFamilyLoader.block_exec n F.length (familyBits F)) input)
          (complete_check n F))))),?_⟩
  have header := MatrixInputHeaders.fuel_bound input
  have dimension := SourceMatrixEncoding.dimension_bound n F
  have loader := SourceEncodedMatrix.loaderFuel_bound n F.length input.length dimension
    (SourceMatrixEncoding.rowCount_bound n F)
  unfold budget
  dsimp only [input,packet] at *
  omega

theorem failed_header (input : BitString) (bad : (fields input).terminated = false) :
    ∃ used, Exec block (initial input) used (failed input) ∧ used ≤ budget input.length := by
  have flag : (SourceFamilyLoader.rawHeaders input).store.get 4 = [] := by
    change (if (fields input).terminated then [true] else []) = []
    rw [bad]
    rfl
  refine ⟨1 + (MatrixInputHeaders.fuel input + 59),
    Exec.seq (retain_exec input) (Exec.seq (headers_exec input)
      (Exec.empty ((loader_get _ input 4).trans flag) (failure_exec _ input))),?_⟩
  have header := MatrixInputHeaders.fuel_bound input
  unfold budget
  omega

theorem failed_payload (input : BitString) (success : (fields input).terminated = true)
    (wrong : (fields input).payload.length ≠ (2 * (fields input).dimension + 3) * (fields input).rows) :
    ∃ used, Exec block (initial input) used (failed input) ∧ used ≤ budget input.length := by
  let f := fields input
  have rejected : ∃ used, Exec payloadCheck (loaded (SourceFamilyLoader.result f.dimension f.rows f.payload).store input)
      used (failed input) ∧ used ≤ 60 := by
    by_cases enough : (2 * f.dimension + 3) * f.rows ≤ f.payload.length
    · exact ⟨60,extra_check f.dimension f.rows f.payload input enough wrong,Nat.le_refl 60⟩
    · exact ⟨59,short_check f.dimension f.rows f.payload input enough,by decide⟩
  obtain ⟨lastFuel,last,lastBound⟩ := rejected
  have seed : Exec SourceFamilyLoader.seed (SourceFamilyLoader.rawHeaders input).store (3 * f.dimension + 12)
      (SourceFamilyLoader.start f.dimension f.rows f.payload).store := by
    rw [SourceFamilyLoader.headers_valid input success]
    exact SourceFamilyLoader.seed_exec f.dimension f.rows f.payload
  have flag : (SourceFamilyLoader.rawHeaders input).store.get 4 = [true] := by
    change (if (fields input).terminated then [true] else []) = [true]
    rw [success]
    rfl
  refine ⟨1 + (MatrixInputHeaders.fuel input + (1 + ((3 * f.dimension + 12) +
    (SourceFamilyLoader.fuel f.dimension f.rows + lastFuel)))),
    Exec.seq (retain_exec input) (Exec.seq (headers_exec input)
      (Exec.one ((loader_get _ input 4).trans flag) (Exec.seq (use16_exec seed input)
        (Exec.seq (use16_exec (SourceFamilyLoader.block_exec f.dimension f.rows f.payload) input) last)))),?_⟩
  have sizes := size_bounds input
  have header := MatrixInputHeaders.fuel_bound input
  have loader := SourceEncodedMatrix.loaderFuel_bound f.dimension f.rows input.length sizes.1 sizes.2.1
  unfold budget
  dsimp only [f] at *
  omega

def result (input : BitString) : Store 63 :=
  match codec.decode input with
  | none => failed input
  | some ⟨_,F⟩ => work [] [] (data F [])

theorem block_exec (input : BitString) :
    ∃ used, Exec block (initial input) used (result input) ∧ used ≤ budget input.length := by
  cases success : (fields input).terminated with
  | false =>
    have invalid := SourceFamilyInput.decode_none_header input success
    simpa only [result,invalid] using failed_header input success
  | true =>
    by_cases length : (fields input).payload.length = (2 * (fields input).dimension + 3) * (fields input).rows
    · obtain ⟨F,_,_,bytes⟩ := SourceFamilyInput.valid_payload input success length
      generalize nEq : (fields input).dimension = n at F bytes
      rw [← bytes]
      simpa only [packet,result,SourceMatrixEncoding.roundtrip] using valid_exec n F
    · have invalid := SourceFamilyInput.decode_none_length input length
      simpa only [result,invalid] using failed_payload input success length

end PNP.Concrete.ResidualReduction.SourceHistoryInput
