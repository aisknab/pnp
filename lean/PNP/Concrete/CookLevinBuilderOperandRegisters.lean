/-
Copyright (c) 2026 PNP Labs.

Source-derived access to the token-width, clause-count and cursor-index registers
already materialized by initialization. The selected offset depends only on the
fixed verifier and operand kind. No caller supplies a divisor, count, prepared
tape or correctness certificate. Copy endpoints remain at the new scratch end;
divider layout, cleanup, selection, emission and the complete loop remain open.
-/

import PNP.Concrete.CookLevinBuilderRegisterAccess

namespace PNP.Concrete.CookLevin.BuilderOperandRegisters

open PipelineTape PipelineStateNamespace
open BuilderUnaryPolynomial

inductive Operand where
  | tokenWidth
  | clauseCount
  | index
  deriving DecidableEq

/-- A deterministic view of existing postorder cells, used only in endpoint specifications. -/
def rootPrefix (polynomial : NatPolynomial) (input : Nat) : List Nat :=
  (registerValues polynomial input).take (nodeCount polynomial - 1)

theorem registerValues_rootPrefix (polynomial : NatPolynomial) (input : Nat) :
    registerValues polynomial input = rootPrefix polynomial input ++ [polynomial.eval input] := by
  obtain ⟨beforeRoot, hRoot⟩ := registerValues_eq_prefix_append_root polynomial input
  have hLength : nodeCount polynomial = beforeRoot.length + 1 := by
    have h := congrArg List.length hRoot
    simpa only [registerValues_length, List.length_append, List.length_cons,
      List.length_nil] using h
  have hIndex : nodeCount polynomial - 1 = beforeRoot.length := by omega
  have hPrefix : rootPrefix polynomial input = beforeRoot := by
    unfold rootPrefix
    rw [hRoot, hIndex]
    exact List.take_left
  rw [hPrefix]
  exact hRoot

def prefixValues (counter width : NatPolynomial) (input : Nat) : List Nat :=
  registerValues counter input ++ [0] ++ registerValues width input

theorem prefixWord_values (counter width : NatPolynomial) (input : Nat) :
    BuilderCursorSource.prefixWord counter width input =
      registerWord (prefixValues counter width input) := by
  have hWord :
      scratchWord (BuilderDimensionRegisters.preparationPolynomial counter width) input =
        registerWord (prefixValues counter width input) ++ registerWord [0, counter.eval input] := by
    simp [scratchWord, BuilderDimensionRegisters.preparationPolynomial,
      registerValues, prefixValues, NatPolynomial.eval_mul, NatPolynomial.eval_constant,
      registerWord_append, List.append_assoc]
  have hTail : (registerWord [0, counter.eval input]).length = counter.eval input + 2 := by
    simp [registerWord_length] <;> omega
  unfold BuilderCursorSource.prefixWord
  rw [hWord, List.length_append, hTail, Nat.add_sub_cancel]
  exact List.take_left

def retainedValues {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) : List Nat :=
  prefixValues (BuilderFullScheduleCursorController.bodySlotCountPolynomial problem.verifier)
    (BuilderDimensionRegisters.widthPolynomial problem.verifier) problem.input.length ++
      [index, remaining]

theorem cursorWord_values {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) :
    BuilderBalancedCursor.word (BuilderCursorSource.registerPrefix problem) index remaining =
      registerWord (retainedValues problem index remaining) := by
  unfold BuilderCursorSource.registerPrefix
  rw [prefixWord_values]
  simp only [retainedValues, BuilderBalancedCursor.word, registerWord_append, registerWord,
    List.append_nil, List.append_assoc]

private def middleValues {language : Language} (problem : VerifierTableauProblem language) :
    List Nat :=
  [(formulaClauseCountPolynomial problem.verifier).eval problem.input.length *
      (formulaClauseTokenPolynomial problem.verifier).eval problem.input.length,
    1, BuilderFullScheduleCursorController.bodySlotCount problem, 0]

private theorem retainedValues_layout {language : Language}
    (problem : VerifierTableauProblem language) (index remaining : Nat) :
    retainedValues problem index remaining =
      registerValues (formulaClauseCountPolynomial problem.verifier) problem.input.length ++
      registerValues (formulaClauseTokenPolynomial problem.verifier) problem.input.length ++
      middleValues problem ++
      registerValues (BuilderDimensionRegisters.widthPolynomial problem.verifier)
        problem.input.length ++ [index, remaining] := by
  simp [retainedValues, prefixValues, BuilderFullScheduleCursorController.bodySlotCountPolynomial,
    BuilderFullScheduleCursorController.bodySlotCount, registerValues, middleValues,
    NatPolynomial.eval_add, NatPolynomial.eval_mul, NatPolynomial.eval_constant, List.append_assoc]

def olderValues {language : Language} (problem : VerifierTableauProblem language) :
    Operand → List Nat
  | .tokenWidth =>
    registerValues (formulaClauseCountPolynomial problem.verifier) problem.input.length ++
      rootPrefix (formulaClauseTokenPolynomial problem.verifier) problem.input.length
  | .clauseCount => rootPrefix (formulaClauseCountPolynomial problem.verifier) problem.input.length
  | .index =>
    prefixValues (BuilderFullScheduleCursorController.bodySlotCountPolynomial problem.verifier)
      (BuilderDimensionRegisters.widthPolynomial problem.verifier) problem.input.length

def copiedValue {language : Language} (problem : VerifierTableauProblem language)
    (index : Nat) : Operand → Nat
  | .tokenWidth => (formulaClauseTokenPolynomial problem.verifier).eval problem.input.length
  | .clauseCount => (formulaClauseCountPolynomial problem.verifier).eval problem.input.length
  | .index => index

def newerValues {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) : Operand → List Nat
  | .tokenWidth =>
    middleValues problem ++
      registerValues (BuilderDimensionRegisters.widthPolynomial problem.verifier)
        problem.input.length ++ [index, remaining]
  | .clauseCount =>
    registerValues (formulaClauseTokenPolynomial problem.verifier) problem.input.length ++
      middleValues problem ++
      registerValues (BuilderDimensionRegisters.widthPolynomial problem.verifier)
        problem.input.length ++ [index, remaining]
  | .index => [remaining]

/-- Fixed delimiter offsets, not a per-input control-table construction. -/
def newerCount {language : Language} (verifier : PolynomialTimeVerifier language) : Operand → Nat
  | .tokenWidth => nodeCount (BuilderDimensionRegisters.widthPolynomial verifier) + 6
  | .clauseCount => nodeCount (formulaClauseTokenPolynomial verifier) +
      nodeCount (BuilderDimensionRegisters.widthPolynomial verifier) + 6
  | .index => 1

theorem newerValues_length {language : Language} (problem : VerifierTableauProblem language)
    (operand : Operand) (index remaining : Nat) :
    (newerValues problem index remaining operand).length =
      newerCount problem.verifier operand := by
  cases operand <;>
    simp [newerValues, newerCount, middleValues, registerValues_length] <;> omega

theorem tokenWidth_value {language : Language} (problem : VerifierTableauProblem language)
    (index : Nat) : copiedValue problem index .tokenWidth = problem.formulaTokensPerClause := by rfl

theorem clauseCount_value {language : Language} (problem : VerifierTableauProblem language)
    (index : Nat) : copiedValue problem index .clauseCount = problem.formulaClauseSlotCount := by rfl

theorem index_value {language : Language} (problem : VerifierTableauProblem language)
    (index : Nat) : copiedValue problem index .index = index := rfl

theorem retainedValues_selection {language : Language} (problem : VerifierTableauProblem language)
    (operand : Operand) (index remaining : Nat) :
    retainedValues problem index remaining =
      olderValues problem operand ++ [copiedValue problem index operand] ++
        newerValues problem index remaining operand := by
  cases operand with
  | tokenWidth =>
    rw [retainedValues_layout,
      registerValues_rootPrefix (formulaClauseTokenPolynomial problem.verifier) problem.input.length]
    simp only [olderValues, copiedValue, newerValues, List.append_assoc]
  | clauseCount =>
    rw [retainedValues_layout,
      registerValues_rootPrefix (formulaClauseCountPolynomial problem.verifier) problem.input.length]
    simp only [olderValues, copiedValue, newerValues, List.append_assoc]
  | index =>
    simp only [retainedValues, olderValues, copiedValue, newerValues, List.append_assoc,
      List.cons_append, List.nil_append]

theorem cursorWord_selection {language : Language} (problem : VerifierTableauProblem language)
    (operand : Operand) (index remaining : Nat) :
    BuilderBalancedCursor.word (BuilderCursorSource.registerPrefix problem) index remaining =
      BuilderRegisterAccess.encodedWord (registerWord (olderValues problem operand))
        (copiedValue problem index operand) (newerValues problem index remaining operand) := by
  rw [cursorWord_values, retainedValues_selection problem operand index remaining]
  simp only [BuilderRegisterAccess.encodedWord, registerWord_append, List.append_assoc]

private def inputFrame (input : BitString) (output : List CNFToken) : WorkTape :=
  BuilderTokenAppender.workspaceTape input [] output

private theorem inputFrame_head_valid (input : BitString) (output : List CNFToken) :
    (inputFrame input output).head = .blank ∨
      (inputFrame input output).head = .zeroBlank ∨
      (inputFrame input output).head = .oneBlank := by
  cases input with
  | nil => exact Or.inl rfl
  | cons bit rest =>
    cases bit with
    | false => exact Or.inr (Or.inl rfl)
    | true => exact Or.inr (Or.inr rfl)

private theorem cursorTape_shape {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (output : List CNFToken) :
    BuilderCursorSource.cursorTape problem index remaining output =
      BuilderRegisterAccess.sourceTape (inputFrame problem.input output).head
        (inputFrame problem.input output).right
        (BuilderBalancedCursor.word (BuilderCursorSource.registerPrefix problem) index remaining)
        (BuilderCursorSource.preservedTail problem) := rfl

def machine {language : Language} (verifier : PolynomialTimeVerifier language) (operand : Operand) :
    WorkMachine :=
  BuilderRegisterAccess.machine (newerCount verifier operand)

def initialConfiguration {language : Language} (problem : VerifierTableauProblem language)
    (operand : Operand) (index remaining : Nat) (output : List CNFToken) : WorkConfiguration :=
  workStartConfiguration (machine problem.verifier operand)
    (BuilderCursorSource.cursorTape problem index remaining output)

def finalConfiguration {language : Language} (problem : VerifierTableauProblem language)
    (operand : Operand) (index remaining : Nat) (output : List CNFToken) : WorkConfiguration :=
  BuilderRegisterAccess.finalConfiguration (inputFrame problem.input output).head
    (inputFrame problem.input output).right (registerWord (olderValues problem operand))
    (copiedValue problem index operand) (newerValues problem index remaining operand)
    (BuilderCursorSource.preservedTail problem)

def workSteps {language : Language} (problem : VerifierTableauProblem language)
    (operand : Operand) (index remaining : Nat) : Nat :=
  BuilderRegisterAccess.workSteps (registerWord (olderValues problem operand))
    (copiedValue problem index operand) (newerValues problem index remaining operand)

theorem initial_tape_handoff {language : Language} (problem : VerifierTableauProblem language)
    (operand : Operand) (index remaining : Nat) (output : List CNFToken) :
    BuilderCursorSource.cursorTape problem index remaining output =
      (BuilderRegisterAccess.initialConfiguration (inputFrame problem.input output).head
        (inputFrame problem.input output).right (registerWord (olderValues problem operand))
        (copiedValue problem index operand) (newerValues problem index remaining operand)
        (BuilderCursorSource.preservedTail problem)).tape := by
  rw [cursorTape_shape, cursorWord_selection problem operand index remaining]
  rfl

theorem initializer_tape_handoff {language : Language} (problem : VerifierTableauProblem language)
    (operand : Operand) :
    (BuilderInitialization.finalConfiguration problem).tape =
      (initialConfiguration problem operand 0
        (BuilderFullScheduleCursorController.bodySlotCount problem)
        (encodeUnaryTokens problem.FormulaWidth)).tape :=
  BuilderCursorSource.initializer_tape_handoff problem

theorem workRunExact {language : Language} (problem : VerifierTableauProblem language)
    (operand : Operand) (index remaining : Nat) (output : List CNFToken) :
    workRunExact? (machine problem.verifier operand) (workSteps problem operand index remaining)
        (initialConfiguration problem operand index remaining output) =
      some (finalConfiguration problem operand index remaining output) := by
  have hRun := BuilderRegisterAccess.workRunExact (inputFrame problem.input output).head
    (inputFrame problem.input output).right (registerWord (olderValues problem operand))
    (copiedValue problem index operand) (newerValues problem index remaining operand)
    (BuilderCursorSource.preservedTail problem)
    (inputFrame_head_valid problem.input output)
    (BuilderRegisterAccess.registerWord_symbols (olderValues problem operand))
  have hInitial : initialConfiguration problem operand index remaining output =
      BuilderRegisterAccess.initialConfiguration (inputFrame problem.input output).head
        (inputFrame problem.input output).right (registerWord (olderValues problem operand))
        (copiedValue problem index operand) (newerValues problem index remaining operand)
        (BuilderCursorSource.preservedTail problem) := by
    unfold initialConfiguration machine
    rw [← newerValues_length problem operand index remaining,
      initial_tape_handoff problem operand index remaining output]
    rfl
  rw [hInitial]
  simpa only [machine, workSteps, finalConfiguration, newerValues_length] using hRun

theorem run_compile_exact {language : Language} (problem : VerifierTableauProblem language)
    (operand : Operand) (index remaining : Nat) (output : List CNFToken) :
    run (compileWorkMachine (machine problem.verifier operand))
        (6 * workSteps problem operand index remaining)
        (encodeWorkConfiguration (initialConfiguration problem operand index remaining output)) =
      encodeWorkConfiguration (finalConfiguration problem operand index remaining output) :=
  run_compileWorkMachine_mul_of_workRunExact _ _ _ _
    (workRunExact problem operand index remaining output)

/-- Includes the complete outward scan, real stage bridge, allocation and copying. -/
def rawTimeBound {language : Language} (verifier : PolynomialTimeVerifier language) : NatPolynomial :=
  let span := registerSpanPolynomial (BuilderDimensionRegisters.polynomial verifier)
  let plusOne := NatPolynomial.add span (.constant 1)
  .mul (.constant 6)
    (.add (.add span (.constant 4))
      (.add
        (.add (.mul (.mul (.constant 4) plusOne) plusOne) (.mul (.constant 9) plusOne))
        (.constant 5)))

theorem rawTimeBound_eval {language : Language} (problem : VerifierTableauProblem language) :
    let span := (scratchWord (BuilderDimensionRegisters.polynomial problem.verifier)
      problem.input.length).length
    (rawTimeBound problem.verifier).eval problem.input.length =
      6 * (span + 4 + (4 * (span + 1) * (span + 1) + 9 * (span + 1) + 5)) := by
  simp only [rawTimeBound, NatPolynomial.eval_mul, NatPolynomial.eval_add,
    NatPolynomial.eval_constant, ← scratchWord_length]

theorem rawTimeBound_le {language : Language} (problem : VerifierTableauProblem language)
    (operand : Operand) (index remaining : Nat)
    (hBalance : index + remaining = BuilderFullScheduleCursorController.bodySlotCount problem) :
    6 * workSteps problem operand index remaining ≤
      (rawTimeBound problem.verifier).eval problem.input.length := by
  have hSpan :
      (BuilderRegisterAccess.encodedWord (registerWord (olderValues problem operand))
        (copiedValue problem index operand) (newerValues problem index remaining operand)).length =
      (scratchWord (BuilderDimensionRegisters.polynomial problem.verifier)
        problem.input.length).length := by
    rw [← cursorWord_selection problem operand index remaining]
    exact BuilderCursorSource.invariant_span problem index remaining hBalance
  have hBound := BuilderRegisterAccess.workSteps_le (registerWord (olderValues problem operand))
    (copiedValue problem index operand) (newerValues problem index remaining operand)
    (scratchWord (BuilderDimensionRegisters.polynomial problem.verifier) problem.input.length).length
    (Nat.le_of_eq hSpan)
  rw [rawTimeBound_eval]
  exact Nat.mul_le_mul_left 6 hBound

theorem finalConfiguration_state {language : Language} (problem : VerifierTableauProblem language)
    (operand : Operand) (index remaining : Nat) (output : List CNFToken) :
    (finalConfiguration problem operand index remaining output).state =
      (machine problem.verifier operand).acceptState := by
  have h := BuilderRegisterAccess.finalConfiguration_state (inputFrame problem.input output).head
    (inputFrame problem.input output).right (registerWord (olderValues problem operand))
    (copiedValue problem index operand) (newerValues problem index remaining operand)
    (BuilderCursorSource.preservedTail problem)
  simpa only [finalConfiguration, machine, newerValues_length] using h

/-- Initialization and access are one literal machine, with a charged physical bridge. -/
def fromRawMachine {language : Language} (verifier : PolynomialTimeVerifier language)
    (operand : Operand) : WorkMachine :=
  WorkMachineChain.machine (BuilderInitialization.machine verifier) (machine verifier operand)

def fromRawInitial {language : Language} (problem : VerifierTableauProblem language)
    (operand : Operand) : WorkConfiguration :=
  workStartConfiguration (fromRawMachine problem.verifier operand) (rawInputWorkTape problem.input)

def fromRawFinal {language : Language} (problem : VerifierTableauProblem language)
    (operand : Operand) : WorkConfiguration :=
  renameConfiguration WorkMachineChain.secondState
    (finalConfiguration problem operand 0
      (BuilderFullScheduleCursorController.bodySlotCount problem)
      (encodeUnaryTokens problem.FormulaWidth))

def fromRawSteps {language : Language} (problem : VerifierTableauProblem language)
    (operand : Operand) : Nat :=
  BuilderInitialization.workSteps problem + 1 +
    workSteps problem operand 0 (BuilderFullScheduleCursorController.bodySlotCount problem)

theorem fromRaw_workRunExact {language : Language} (problem : VerifierTableauProblem language)
    (operand : Operand) :
    workRunExact? (fromRawMachine problem.verifier operand) (fromRawSteps problem operand)
        (fromRawInitial problem operand) = some (fromRawFinal problem operand) := by
  have hRead :
      workRunExact? (machine problem.verifier operand)
        (workSteps problem operand 0 (BuilderFullScheduleCursorController.bodySlotCount problem))
        { state := (machine problem.verifier operand).startState,
          tape := (BuilderInitialization.finalConfiguration problem).tape } =
      some (finalConfiguration problem operand 0
        (BuilderFullScheduleCursorController.bodySlotCount problem)
        (encodeUnaryTokens problem.FormulaWidth)) := by
    rw [initializer_tape_handoff problem operand]
    exact workRunExact problem operand 0 (BuilderFullScheduleCursorController.bodySlotCount problem)
      (encodeUnaryTokens problem.FormulaWidth)
  exact WorkMachineChain.workRunExact
    (BuilderInitialization.machine problem.verifier) (machine problem.verifier operand)
    (BuilderInitialization.workSteps problem)
    (workSteps problem operand 0 (BuilderFullScheduleCursorController.bodySlotCount problem))
    (BuilderInitialization.initialConfiguration problem)
    (BuilderInitialization.finalConfiguration problem)
    (finalConfiguration problem operand 0 (BuilderFullScheduleCursorController.bodySlotCount problem)
      (encodeUnaryTokens problem.FormulaWidth))
    (BuilderInitialization.workRunExact problem)
    (BuilderInitialization.finalConfiguration_state problem) hRead

theorem fromRaw_run_compile_exact {language : Language} (problem : VerifierTableauProblem language)
    (operand : Operand) :
    run (compileWorkMachine (fromRawMachine problem.verifier operand))
        (6 * fromRawSteps problem operand) (encodeWorkConfiguration (fromRawInitial problem operand)) =
      encodeWorkConfiguration (fromRawFinal problem operand) :=
  run_compileWorkMachine_mul_of_workRunExact _ _ _ _ (fromRaw_workRunExact problem operand)

def fromRawTimeBound {language : Language} (verifier : PolynomialTimeVerifier language) :
    NatPolynomial :=
  .add (.add (BuilderInitialization.rawTimeBound verifier) (.constant 6)) (rawTimeBound verifier)

theorem fromRawTimeBound_le {language : Language} (problem : VerifierTableauProblem language)
    (operand : Operand) :
    6 * fromRawSteps problem operand ≤
      (fromRawTimeBound problem.verifier).eval problem.input.length := by
  have hInit := BuilderInitialization.rawTimeBound_le problem
  have hRead := rawTimeBound_le problem operand 0
    (BuilderFullScheduleCursorController.bodySlotCount problem) (Nat.zero_add _)
  simp only [fromRawTimeBound, NatPolynomial.eval_add, NatPolynomial.eval_constant]
  unfold fromRawSteps
  omega

end PNP.Concrete.CookLevin.BuilderOperandRegisters
