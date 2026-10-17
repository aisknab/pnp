import PNP.Concrete.ResidualReduction.SourceWitnessPairInstructions
import PNP.Concrete.ResidualReduction.SourceOrderedMatrixSelector

/-! Full matrix-to-parameter-witness instruction path. Seed discovery, ordered
candidate choice, and vector construction are internal. Absence is explicit;
neither valid seed coordinates nor a successful witness is an input premise. -/

namespace PNP.Concrete.ResidualReduction.SourceMatrixWitness
open PNP.Concrete PNP.Concrete.BitRegister
open PNP.Concrete.NormalizerBlocks PNP.Concrete.NormalizerBlocks.Occurrence
open PNP.Concrete.ResidualReduction.FactoredContraction
open PNP.Concrete.ResidualReduction.ConstrainedBilinear
open PNP.Concrete.ResidualReduction.SourceCandidateChoice (Choice)
open PNP.Concrete.ResidualReduction.SourceLinePullback (transfers transfers_exec)

structure Pick (m n : Nat) where
  first : Fin m × Fin n
  second : Fin m × Fin n
  choice : Choice
def selected {m n : Nat} (A C : Matrix m n) : Option (Pick m n) :=
  (SourceOrderedSelectorPrelude.selectedSeeds A C).bind fun p =>
    (SourceCandidateSelection.choice A C p.1.1 p.2.1 p.1.2 p.2.2).map fun c => ⟨p.1, p.2, c⟩
def extra (m : Nat) : Store 3 := .cons (List.replicate m true) (.cons [] (.cons [] .nil))
def extend (core : Store 16) (m : Nat) : Store 19 := Frame.join core (extra m)
def extendPair (core : Store 18) : Store 19 := Frame.join core (.cons [] .nil)
def start (r : Registers) {m n : Nat} (A C : Matrix m n) : Store 19 :=
  extend (SourceOrderedMatrixSelector.start r A C) m
def afterSelector (r : Registers) {m n : Nat} (A C : Matrix m n) : Store 19 :=
  extend (SourceOrderedMatrixSelector.result r A C) m
def successfulCore (r : Registers) (c : Choice) : Registers :=
  {r with input := [], sign := [true], output := SourceCandidateChoice.outputBits (some c)}
def readyCore (r : Registers) {m n : Nat} (A C : Matrix m n) (p : Pick m n) : Registers :=
  successfulCore (SourceCandidateSelection.result (SourceOrderedSelectorPrelude.second r A C)
    A C p.first.1 p.second.1 p.first.2 p.second.2) p.choice
def successfulResult (r : Registers) {m n : Nat} (A C : Matrix m n) (p : Pick m n) : Store 19 :=
  extendPair (SourceWitnessPair.result (readyCore r A C p) p.first.1 p.second.1 p.first.2 p.second.2 p.choice)

-- Copy the row width before the old slot is reused for the second column.
def relocate : Block 19 := transfers
  [.copy 9 16, .copy 16 15, .copy 15 14, .copy 14 11, .copy 10 12, .copy 11 13]
def prepareChoice : Block 19 := transfers
  [.clear 12, .clear 13, .copy 0 8, .pop 0, .clear 4, .push 4 true]
def handoff : Block 19 := .seq relocate prepareChoice
def relocated (r : Registers) {m n : Nat} (e f : Fin m × Fin n) (c : Choice) : Store 19 :=
  extendPair (SourceWitnessPair.store
    (SourceAxisWitness.store {r with output := SourceCandidateChoice.outputBits (some c)}
      (SourceAxisWitness.data e.1 f.1 (List.replicate e.1.val true) (List.replicate f.1.val true)))
    (SourceWitnessPair.data e.2 f.2 []))
theorem relocate_exec (r : Registers) {m n : Nat} (A C : Matrix m n)
    (e f : Fin m × Fin n) (c : Choice) :
    Exec relocate
      (extend (SourceCandidateCorners.store {r with output := SourceCandidateChoice.outputBits (some c)}
        (SourceCandidateCorners.data A C e.1 f.1 e.2 f.2)) m) 7 (relocated r e f c) :=
  transfers_exec _ _
private def choiceState (r : Registers) {m n : Nat} (e f : Fin m × Fin n) (c : Choice)
    (input sign work tail : BitString) : Store 19 :=
  extendPair (SourceWitnessPair.store
    (SourceAxisWitness.store {r with input := input, sign := sign, output := SourceCandidateChoice.outputBits (some c)}
      (SourceAxisWitness.data e.1 f.1 work tail)) (SourceWitnessPair.data e.2 f.2 []))
theorem prepare_choice_exec (r : Registers) {m n : Nat} (e f : Fin m × Fin n) (c : Choice) :
    Exec prepareChoice (relocated r e f c) 7
      (extendPair (SourceWitnessPair.start (successfulCore r c) e.1 f.1 e.2 f.2 c)) := by
  let word := SourceCandidateChoice.axisBits c.1 ++ SourceCandidateChoice.axisBits c.2
  let s1 := choiceState r e f c r.input r.sign [] (List.replicate f.1.val true)
  let s2 := choiceState r e f c r.input r.sign [] []
  let s3 := choiceState r e f c (true :: word) r.sign [] []
  let s4 := choiceState r e f c word r.sign [] []
  let s5 := choiceState r e f c word [] [] []
  let s6 := choiceState r e f c word [true] [] []
  have a1 : Exec (.action (.clear (12 : Fin 19))) (relocated r e f c) 1 s1 := .action _ _
  have a2 : Exec (.action (.clear (13 : Fin 19))) s1 1 s2 := .action _ _
  have a3 : Exec (.action (.copy (0 : Fin 19) 8)) s2 1 s3 := .action _ _
  have a4 : Exec (.action (.pop (0 : Fin 19))) s3 1 s4 := .action _ _
  have a5 : Exec (.action (.clear (4 : Fin 19))) s4 1 s5 := .action _ _
  have a6 : Exec (.action (.push (4 : Fin 19) true)) s5 1 s6 := .action _ _
  have same : s6 = extendPair (SourceWitnessPair.start (successfulCore r c) e.1 f.1 e.2 f.2 c) := by
    simp only [s6, word, choiceState, SourceWitnessPair.start, SourceWitnessPair.rowInput,
      SourceAxisWitness.start, successfulCore, List.append_nil]
  have done : Exec (.skip : Block 19) s6 1
      (extendPair (SourceWitnessPair.start (successfulCore r c) e.1 f.1 e.2 f.2 c)) := by
    rw [← same]
    exact Exec.skip _
  exact Exec.seq a1 (Exec.seq a2 (Exec.seq a3 (Exec.seq a4 (Exec.seq a5 (Exec.seq a6 done)))))
theorem handoff_exec (r : Registers) {m n : Nat} (A C : Matrix m n)
    (e f : Fin m × Fin n) (c : Choice) :
    Exec handoff
      (extend (SourceCandidateCorners.store {r with output := SourceCandidateChoice.outputBits (some c)}
        (SourceCandidateCorners.data A C e.1 f.1 e.2 f.2)) m) 14
      (extendPair (SourceWitnessPair.start (successfulCore r c) e.1 f.1 e.2 f.2 c)) :=
  Exec.seq (relocate_exec r A C e f c) (prepare_choice_exec r e f c)
theorem selected_handoff (r : Registers) {m n : Nat} (A C : Matrix m n)
    (e f : Fin m × Fin n) (c : Choice)
    (seeds : SourceOrderedSelectorPrelude.selectedSeeds A C = some (e, f))
    (choice : SourceCandidateSelection.choice A C e.1 f.1 e.2 f.2 = some c) :
    Exec handoff (afterSelector r A C) 14
      (extendPair (SourceWitnessPair.start (readyCore r A C ⟨e, f, c⟩) e.1 f.1 e.2 f.2 c)) := by
  simpa only [afterSelector, SourceOrderedMatrixSelector.result, seeds, readyCore,
    SourceCandidateSelection.result, choice, successfulCore] using
    handoff_exec (SourceCandidateSelection.result (SourceOrderedSelectorPrelude.second r A C)
      A C e.1 f.1 e.2 f.2) A C e f c
theorem after_code (r : Registers) {m n : Nat} (A C : Matrix m n) :
    (afterSelector r A C).get 8 =
      SourceCandidateChoice.outputBits (SourceOrderedMatrixSelector.code A C) :=
  (Frame.get_core _ _ (8 : Fin 16)).trans (SourceOrderedMatrixSelector.output_exact r A C)

def rejectResult (s : Store 19) : Store 19 := s.set 4 []
def finish : Block 19 :=
  .branch 8 (.action (.clear 4)) (.action (.clear 4))
    (.seq handoff (Frame.block 1 SourceWitnessPair.block))
def finishFuel {m n : Nat} (A C : Matrix m n) : Nat :=
  match selected A C with
  | none => 2
  | some p => 1 + (14 + SourceWitnessPair.fuel p.first.1 p.second.1 p.first.2 p.second.2 p.choice)
def result (r : Registers) {m n : Nat} (A C : Matrix m n) : Store 19 :=
  match selected A C with
  | none => rejectResult (afterSelector r A C)
  | some p => successfulResult r A C p

theorem finish_exec (r : Registers) {m n : Nat} (A C : Matrix m n) :
    Exec finish (afterSelector r A C) (finishFuel A C) (result r A C) := by
  have flag := after_code r A C
  cases seeds : SourceOrderedSelectorPrelude.selectedSeeds A C with
  | none =>
    simp only [finishFuel, result, selected, seeds, Option.bind_none]
    rw [SourceOrderedMatrixSelector.code, seeds] at flag
    exact Exec.zero flag (.action _ _)
  | some p =>
    rcases p with ⟨e, f⟩
    cases choice : SourceCandidateSelection.choice A C e.1 f.1 e.2 f.2 with
    | none =>
      simp only [finishFuel, result, selected, seeds, Option.bind_some, choice, Option.map_none]
      rw [SourceOrderedMatrixSelector.code, seeds, Option.bind_some, choice] at flag
      exact Exec.zero flag (.action _ _)
    | some c =>
      simp only [finishFuel, result, selected, seeds, Option.bind_some, choice, Option.map_some]
      rw [SourceOrderedMatrixSelector.code, seeds, Option.bind_some, choice] at flag
      exact Exec.one flag (Exec.seq (selected_handoff r A C e f c seeds choice)
        (Frame.execution (SourceWitnessPair.block_exec (readyCore r A C ⟨e, f, c⟩) e.1 f.1 e.2 f.2 c)
          (.cons [] .nil)))

def block : Block 19 := .seq (Frame.block 3 SourceOrderedMatrixSelector.block) finish
def fuel {m n : Nat} (A C : Matrix m n) : Nat :=
  SourceOrderedMatrixSelector.fuel A C + finishFuel A C
theorem block_exec (r : Registers) {m n : Nat} (A C : Matrix m n) :
    Exec block (start r A C) (fuel A C) (result r A C) :=
  Exec.seq (Frame.execution (SourceOrderedMatrixSelector.block_exec r A C) (extra m)) (finish_exec r A C)

def witnessBytes {m n : Nat} (A C : Matrix m n) : Option (BitString × BitString) :=
  (BilinearSelection.select A C).witness.map fun w =>
    ((SourceEncoding.pointCodec m).encode (sumUnits w.1), (SourceEncoding.pointCodec n).encode (sumUnits w.2))
def pickBytes {m n : Nat} (p : Pick m n) : BitString × BitString :=
  ((SourceEncoding.pointCodec m).encode (SourceAxisWitness.point p.first.1 p.second.1 p.choice.1),
    (SourceEncoding.pointCodec n).encode (SourceAxisWitness.point p.first.2 p.second.2 p.choice.2))
theorem selected_witness {m n : Nat} (A C : Matrix m n) :
    (selected A C).map pickBytes = witnessBytes A C := by
  rw [witnessBytes, SourceOrderedMatrixSelector.witness_exact]
  cases seeds : SourceOrderedSelectorPrelude.selectedSeeds A C with
  | none => simp only [selected, seeds, Option.bind_none, Option.map_none]
  | some p =>
    rcases p with ⟨e, f⟩
    cases choice : SourceCandidateSelection.choice A C e.1 f.1 e.2 f.2 with
    | none => simp only [selected, seeds, Option.bind_some, choice, Option.map_none]
    | some c =>
      simp only [selected, seeds, Option.bind_some, choice, Option.map_some, pickBytes,
        SourceAxisWitness.point_exact, SourceCandidateChoice.decode]

def observed (s : Store 19) : Option (BitString × BitString) :=
  if (s.get 4).isEmpty then none else some (s.get 17, s.get 8)
theorem reject_observed (s : Store 19) : observed (rejectResult s) = none := by
  simp only [observed, rejectResult, Store.get_set_same]
  rfl
theorem successful_observed (r : Registers) {m n : Nat} (A C : Matrix m n) (p : Pick m n) :
    observed (successfulResult r A C p) = some (pickBytes p) := rfl
theorem result_exact (r : Registers) {m n : Nat} (A C : Matrix m n) :
    observed (result r A C) = witnessBytes A C := by
  rw [← selected_witness]
  cases h : selected A C with
  | none =>
    simp only [result, h, Option.map_none]
    exact reject_observed _
  | some p =>
    simp only [result, h, Option.map_some]
    exact successful_observed r A C p

theorem finish_bound {m n : Nat} (A C : Matrix m n) :
    finishFuel A C ≤ 15 * m + 15 * n + 80 := by
  unfold finishFuel
  cases h : selected A C with
  | none => dsimp only; omega
  | some p =>
    dsimp only
    have bound := SourceWitnessPair.fuel_bound p.first.1 p.second.1 p.first.2 p.second.2 p.choice
    omega
theorem fuel_bound {m n : Nat} (A C : Matrix m n) :
    fuel A C ≤ 26 * (m * n) + (6 + SourceMatrixEntry.budget m n) * 8 + 15 * m + 15 * n + 157 := by
  have search := SourceOrderedMatrixSelector.fuel_bound A C
  have vectors := finish_bound A C
  unfold fuel
  omega
def sourceCostPolynomial : NatPolynomial :=
  .add (.add SourceOrderedMatrixSelector.sourceCostPolynomial (.mul (.constant 45) .variable)) (.constant 80)
theorem source_bound {n : Nat} (F : Family n) (alpha : Affine n) :
    fuel (SourceLinePullback.normalPull F alpha) (SourceLinePullback.activityPull F alpha) ≤
      sourceCostPolynomial.eval (SourceDirectionEncoding.codec.encode ⟨n, [alpha], F⟩).length := by
  have search := SourceOrderedMatrixSelector.source_bound F alpha
  have vectors := finish_bound (SourceLinePullback.normalPull F alpha) (SourceLinePullback.activityPull F alpha)
  have rows := SourceLinePullback.left_parameter_bound F alpha
  have columns := SourceLinePullback.right_parameter_bound F alpha
  change SourceOrderedMatrixSelector.fuel _ _ + finishFuel _ _ ≤
    SourceOrderedMatrixSelector.sourceCostPolynomial.eval _ +
      45 * (SourceDirectionEncoding.codec.encode ⟨n, [alpha], F⟩).length + 80
  omega

def program : Program 19 := block.program 0 8
theorem program_run (r : Registers) {m n : Nat} (A C : Matrix m n) :
    BitRegister.run program (fuel A C + 1) ⟨.running 0, start r A C⟩ =
      ⟨.accepted, result r A C⟩ := (block_exec r A C).program_run 0 8

end PNP.Concrete.ResidualReduction.SourceMatrixWitness
