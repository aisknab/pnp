/-
Copyright (c) 2026 PNP Labs.

Literal composition of the Cook--Levin body-start prefix with a structurally
compiled unary next-token cursor and the first canonical literal.

For every fixed verifier problem, the finite work machine in this file starts
from an ordinary raw bitstring, emits exactly `T^FormulaWidth F Sep T F`, and
retains the next padded token-schedule coordinate in unary scratch.  This is
only a first-literal prefix.  It does not dynamically interpret later cursor
slots, emit a complete clause, construct the complete formula, provide a
RawRefinement or polynomial reduction, prove CNF-SAT is in P, or establish
P = NP.
-/

import PNP.Concrete.CookLevinBuilderBodyStartPrefix

namespace PNP.Concrete

namespace CookLevin

namespace BuilderFirstLiteralPrefix

open PipelineTape PipelineStateNamespace PipelineStageBridges

/-! ### Retained next-token coordinate -/

/-- Polynomial for the token opportunity immediately after the first
canonical literal.  The padded header occupies
`formulaVariableSlotBound + 1` opportunities, then the separator, sign, and
zero-variable terminator consume three more opportunities. -/
def nextTokenSlotPolynomial {language : Language}
    (verifier : PolynomialTimeVerifier language) : NatPolynomial :=
  .add (formulaVariableCountPolynomial verifier) (.constant 4)

def nextTokenSlot {language : Language}
    (problem : VerifierTableauProblem language) : Nat :=
  (nextTokenSlotPolynomial problem.verifier).eval problem.input.length

theorem nextTokenSlot_eq_formulaVariableSlotBound_add_four
    {language : Language} (problem : VerifierTableauProblem language) :
    nextTokenSlot problem = problem.formulaVariableSlotBound + 4 := by
  rfl

/-- Raw-bit coordinate corresponding to the retained token coordinate. -/
def nextBitSlot {language : Language}
    (problem : VerifierTableauProblem language) : Nat :=
  2 * nextTokenSlot problem

/-- Specification cursor aligned with the retained token coordinate.  The
work tape stores the token coordinate itself; this definition records the
proved conversion to the existing raw-bit cursor specification. -/
def nextBitCursor {language : Language}
    (problem : VerifierTableauProblem language) :
    VerifierTableauProblem.FormulaBitCursor :=
  ⟨nextBitSlot problem⟩

theorem nextBitCursor_nextSlot {language : Language}
    (problem : VerifierTableauProblem language) :
    (nextBitCursor problem).nextSlot =
      2 * (problem.formulaVariableSlotBound + 4) := by
  rw [nextBitCursor, nextBitSlot,
    nextTokenSlot_eq_formulaVariableSlotBound_add_four]

/-! ### Four collision-free component images -/

def prefixState (state : Nat) : Nat := 4 * state
def evaluatorState (state : Nat) : Nat := 4 * state + 1
def tAppenderState (state : Nat) : Nat := 4 * state + 2
def fAppenderState (state : Nat) : Nat := 4 * state + 3

theorem prefixState_injective : Function.Injective prefixState := by
  intro left right h
  simp only [prefixState] at h
  omega

theorem evaluatorState_injective : Function.Injective evaluatorState := by
  intro left right h
  simp only [evaluatorState] at h
  omega

theorem tAppenderState_injective : Function.Injective tAppenderState := by
  intro left right h
  simp only [tAppenderState] at h
  omega

theorem fAppenderState_injective : Function.Injective fAppenderState := by
  intro left right h
  simp only [fAppenderState] at h
  omega

theorem prefixState_ne_evaluatorState (left right : Nat) :
    prefixState left ≠ evaluatorState right := by
  simp only [prefixState, evaluatorState]
  omega

theorem prefixState_ne_tAppenderState (left right : Nat) :
    prefixState left ≠ tAppenderState right := by
  simp only [prefixState, tAppenderState]
  omega

theorem prefixState_ne_fAppenderState (left right : Nat) :
    prefixState left ≠ fAppenderState right := by
  simp only [prefixState, fAppenderState]
  omega

theorem evaluatorState_ne_tAppenderState (left right : Nat) :
    evaluatorState left ≠ tAppenderState right := by
  simp only [evaluatorState, tAppenderState]
  omega

theorem evaluatorState_ne_fAppenderState (left right : Nat) :
    evaluatorState left ≠ fAppenderState right := by
  simp only [evaluatorState, fAppenderState]
  omega

theorem tAppenderState_ne_fAppenderState (left right : Nat) :
    tAppenderState left ≠ fAppenderState right := by
  simp only [tAppenderState, fAppenderState]
  omega

def prefixEvaluatorBridge {language : Language}
    (problem : VerifierTableauProblem language) : List WorkRule :=
  launchRules
    (prefixState (BuilderBodyStartPrefix.machine problem).acceptState)
    (evaluatorState
      (BuilderUnaryPolynomial.machine
        (nextTokenSlotPolynomial problem.verifier)).startState)

def evaluatorTBridge {language : Language}
    (problem : VerifierTableauProblem language) : List WorkRule :=
  launchRules
    (evaluatorState
      (BuilderUnaryPolynomial.machine
        (nextTokenSlotPolynomial problem.verifier)).acceptState)
    (tAppenderState (BuilderTokenAppender.seekInputState .t))

def tFBridge {language : Language}
    (_problem : VerifierTableauProblem language) : List WorkRule :=
  launchRules
    (tAppenderState BuilderTokenAppender.machine.acceptState)
    (fAppenderState (BuilderTokenAppender.seekInputState .f))

def bridgeRules {language : Language}
  (problem : VerifierTableauProblem language) : List WorkRule :=
  prefixEvaluatorBridge problem ++
    (evaluatorTBridge problem ++ tFBridge problem)

private def componentRules {language : Language}
    (problem : VerifierTableauProblem language) : List WorkRule :=
  (BuilderBodyStartPrefix.machine problem).rules.map
      (renameRule prefixState) ++
    ((BuilderUnaryPolynomial.machine
        (nextTokenSlotPolynomial problem.verifier)).rules.map
        (renameRule evaluatorState) ++
      (BuilderTokenAppender.machine.rules.map (renameRule tAppenderState) ++
        BuilderTokenAppender.machine.rules.map (renameRule fAppenderState)))

/-- One bridge-first literal table containing the body-start prefix, cursor
evaluator, and two fixed-token appender tables. -/
def rules {language : Language}
    (problem : VerifierTableauProblem language) : List WorkRule :=
  bridgeRules problem ++ componentRules problem

/-- Only the final appender copy contributes global halts. -/
def machine {language : Language}
    (problem : VerifierTableauProblem language) : WorkMachine :=
  { rules := rules problem
    startState := prefixState (BuilderBodyStartPrefix.machine problem).startState
    acceptState := fAppenderState BuilderTokenAppender.machine.acceptState
    rejectState := fAppenderState BuilderTokenAppender.machine.rejectState }

theorem rules_length {language : Language}
    (problem : VerifierTableauProblem language) :
    (rules problem).length =
      585 +
        BuilderUnaryPolynomial.ruleCount
          (BuilderCompleteHeader.widthPolynomial problem) +
        BuilderUnaryPolynomial.ruleCount
          (BuilderBodyStartPrefix.nextTokenSlotPolynomial problem.verifier) +
        BuilderUnaryPolynomial.ruleCount
          (nextTokenSlotPolynomial problem.verifier) := by
  have hPrefix := BuilderBodyStartPrefix.rules_length problem
  have hEvaluator := BuilderUnaryPolynomial.rules_length
    (nextTokenSlotPolynomial problem.verifier)
  have hAppender := BuilderTokenAppender.rules_length
  have hPrefix' : (BuilderBodyStartPrefix.machine problem).rules.length =
      440 +
        BuilderUnaryPolynomial.ruleCount
          (BuilderCompleteHeader.widthPolynomial problem) +
        BuilderUnaryPolynomial.ruleCount
          (BuilderBodyStartPrefix.nextTokenSlotPolynomial problem.verifier) := by
    simpa [BuilderBodyStartPrefix.machine] using hPrefix
  have hEvaluator' :
      (BuilderUnaryPolynomial.machine
        (nextTokenSlotPolynomial problem.verifier)).rules.length =
      BuilderUnaryPolynomial.ruleCount
        (nextTokenSlotPolynomial problem.verifier) := by
    simpa [BuilderUnaryPolynomial.machine] using hEvaluator
  have hAppender' : BuilderTokenAppender.machine.rules.length = 59 := by
    simpa [BuilderTokenAppender.machine] using hAppender
  have hBridgeOne : (prefixEvaluatorBridge problem).length = 9 := by rfl
  have hBridgeTwo : (evaluatorTBridge problem).length = 9 := by rfl
  have hBridgeThree : (tFBridge problem).length = 9 := by rfl
  simp only [rules, bridgeRules, componentRules, List.length_append,
    List.length_map]
  rw [hPrefix', hEvaluator', hAppender', hBridgeOne, hBridgeTwo,
    hBridgeThree]
  omega

theorem machine_acceptState_ne_rejectState {language : Language}
    (problem : VerifierTableauProblem language) :
    (machine problem).acceptState ≠ (machine problem).rejectState := by
  intro h
  exact BuilderTokenAppender.machine_acceptState_ne_rejectState
    (fAppenderState_injective h)

/-! ### Literal-table determinism -/

private def QueryDistinct (left right : WorkRule) : Prop :=
  (left.sourceState, left.readSymbol) ≠
    (right.sourceState, right.readSymbol)

private theorem queryDistinct_of_source_ne (left right : WorkRule)
    (hSource : left.sourceState ≠ right.sourceState) :
    QueryDistinct left right := by
  intro hQuery
  exact hSource (congrArg Prod.fst hQuery)

private theorem renameRules_pairwise (encode : Nat → Nat)
    (hInjective : Function.Injective encode) (localRules : List WorkRule)
    (hPairwise : localRules.Pairwise QueryDistinct) :
    (localRules.map (renameRule encode)).Pairwise QueryDistinct := by
  exact List.Pairwise.map (renameRule encode) (fun left right hDistinct => by
    intro hEqual
    apply hDistinct
    apply Prod.ext
    · exact hInjective (by
        simpa [renameRule] using congrArg Prod.fst hEqual)
    · simpa [renameRule] using congrArg Prod.snd hEqual) hPairwise

private theorem launchRules_pairwise (source target : Nat) :
    (launchRules source target).Pairwise QueryDistinct := by
  unfold launchRules PipelineMachineSimulation.allWorkSymbols
  simp [QueryDistinct, launchRule, WorkSymbol.blank,
    WorkSymbol.blankZero, WorkSymbol.blankOne, WorkSymbol.zeroBlank,
    WorkSymbol.zeroZero, WorkSymbol.zeroOne, WorkSymbol.oneBlank,
    WorkSymbol.oneZero, WorkSymbol.oneOne]

private theorem launchRules_source_eq {source target : Nat}
    {rule : WorkRule} (hMem : rule ∈ launchRules source target) :
    rule.sourceState = source := by
  rcases List.mem_map.mp hMem with ⟨symbol, _hSymbol, hRule⟩
  rw [← hRule]
  rfl

private theorem renamedRules_source {encode : Nat → Nat}
    {localRules : List WorkRule} {rule : WorkRule}
    (hMem : rule ∈ localRules.map (renameRule encode)) :
    ∃ localRule ∈ localRules,
      rule.sourceState = encode localRule.sourceState := by
  rcases List.mem_map.mp hMem with ⟨localRule, hLocal, hRule⟩
  exact ⟨localRule, hLocal, by rw [← hRule]; rfl⟩

private theorem renamedRules_cross
    (leftEncode rightEncode : Nat → Nat)
    (leftRules rightRules : List WorkRule)
    (hDisjoint : ∀ left right,
      leftEncode left ≠ rightEncode right) :
    ∀ leftRule ∈ leftRules.map (renameRule leftEncode),
      ∀ rightRule ∈ rightRules.map (renameRule rightEncode),
        QueryDistinct leftRule rightRule := by
  intro leftRule hLeft rightRule hRight
  rcases renamedRules_source hLeft with
    ⟨leftLocal, _hLeftLocal, hLeftSource⟩
  rcases renamedRules_source hRight with
    ⟨rightLocal, _hRightLocal, hRightSource⟩
  apply queryDistinct_of_source_ne
  rw [hLeftSource, hRightSource]
  exact hDisjoint leftLocal.sourceState rightLocal.sourceState

private theorem appender_rule_source_ne_accept (rule : WorkRule)
    (hMem : rule ∈ BuilderTokenAppender.machine.rules) :
    rule.sourceState ≠ BuilderTokenAppender.machine.acceptState := by
  decide +revert

private theorem appender_rule_source_ne_reject (rule : WorkRule)
    (hMem : rule ∈ BuilderTokenAppender.machine.rules) :
    rule.sourceState ≠ BuilderTokenAppender.machine.rejectState := by
  decide +revert

private theorem bodyStart_rule_source_ne_accept
    {language : Language} (problem : VerifierTableauProblem language)
    (rule : WorkRule)
    (hMem : rule ∈ (BuilderBodyStartPrefix.machine problem).rules) :
    rule.sourceState ≠ (BuilderBodyStartPrefix.machine problem).acceptState := by
  exact BuilderBodyStartPrefix.rule_source_ne_acceptState problem rule hMem

private theorem bodyStart_rule_source_ne_reject
    {language : Language} (problem : VerifierTableauProblem language)
    (rule : WorkRule)
    (hMem : rule ∈ (BuilderBodyStartPrefix.machine problem).rules) :
    rule.sourceState ≠ (BuilderBodyStartPrefix.machine problem).rejectState := by
  exact BuilderBodyStartPrefix.rule_source_ne_rejectState problem rule hMem

private theorem componentRules_pairwise {language : Language}
    (problem : VerifierTableauProblem language) :
    (componentRules problem).Pairwise QueryDistinct := by
  have hPrefix := renameRules_pairwise prefixState prefixState_injective
    (BuilderBodyStartPrefix.machine problem).rules
    (BuilderBodyStartPrefix.rules_pairwise_query_distinct problem)
  have hEvaluator := renameRules_pairwise evaluatorState evaluatorState_injective
    (BuilderUnaryPolynomial.machine
      (nextTokenSlotPolynomial problem.verifier)).rules
    (BuilderUnaryPolynomial.rules_pairwise_query_distinct
      (nextTokenSlotPolynomial problem.verifier))
  have hT := renameRules_pairwise tAppenderState tAppenderState_injective
    BuilderTokenAppender.machine.rules
    BuilderTokenAppender.rules_pairwise_query_distinct
  have hF := renameRules_pairwise fAppenderState fAppenderState_injective
    BuilderTokenAppender.machine.rules
    BuilderTokenAppender.rules_pairwise_query_distinct
  have hPE := renamedRules_cross prefixState evaluatorState
    (BuilderBodyStartPrefix.machine problem).rules
    (BuilderUnaryPolynomial.machine
      (nextTokenSlotPolynomial problem.verifier)).rules
    prefixState_ne_evaluatorState
  have hPT := renamedRules_cross prefixState tAppenderState
    (BuilderBodyStartPrefix.machine problem).rules
    BuilderTokenAppender.machine.rules prefixState_ne_tAppenderState
  have hPF := renamedRules_cross prefixState fAppenderState
    (BuilderBodyStartPrefix.machine problem).rules
    BuilderTokenAppender.machine.rules prefixState_ne_fAppenderState
  have hET := renamedRules_cross evaluatorState tAppenderState
    (BuilderUnaryPolynomial.machine
      (nextTokenSlotPolynomial problem.verifier)).rules
    BuilderTokenAppender.machine.rules evaluatorState_ne_tAppenderState
  have hEF := renamedRules_cross evaluatorState fAppenderState
    (BuilderUnaryPolynomial.machine
      (nextTokenSlotPolynomial problem.verifier)).rules
    BuilderTokenAppender.machine.rules evaluatorState_ne_fAppenderState
  have hTF := renamedRules_cross tAppenderState fAppenderState
    BuilderTokenAppender.machine.rules BuilderTokenAppender.machine.rules
    tAppenderState_ne_fAppenderState
  unfold componentRules
  rw [List.pairwise_append]
  refine ⟨hPrefix, ?_, ?_⟩
  · rw [List.pairwise_append]
    refine ⟨hEvaluator, ?_, ?_⟩
    · rw [List.pairwise_append]
      exact ⟨hT, hF, hTF⟩
    · intro left hLeft right hRight
      simp only [List.mem_append] at hRight
      rcases hRight with hRight | hRight
      · exact hET left hLeft right hRight
      · exact hEF left hLeft right hRight
  · intro left hLeft right hRight
    simp only [List.mem_append] at hRight
    rcases hRight with hRight | hRight | hRight
    · exact hPE left hLeft right hRight
    · exact hPT left hLeft right hRight
    · exact hPF left hLeft right hRight

private theorem launchRules_cross (leftSource leftTarget rightSource
    rightTarget : Nat) (hSource : leftSource ≠ rightSource) :
    ∀ left ∈ launchRules leftSource leftTarget,
      ∀ right ∈ launchRules rightSource rightTarget,
        QueryDistinct left right := by
  intro left hLeft right hRight
  apply queryDistinct_of_source_ne
  rw [launchRules_source_eq hLeft, launchRules_source_eq hRight]
  exact hSource

private theorem launchRenamed_cross (source target : Nat)
    (encode : Nat → Nat) (localRules : List WorkRule)
    (hSource : ∀ localRule ∈ localRules,
      source ≠ encode localRule.sourceState) :
    ∀ bridgeRule ∈ launchRules source target,
      ∀ componentRule ∈ localRules.map (renameRule encode),
        QueryDistinct bridgeRule componentRule := by
  intro bridgeRule hBridge componentRule hComponent
  rcases renamedRules_source hComponent with
    ⟨localRule, hLocal, hComponentSource⟩
  apply queryDistinct_of_source_ne
  rw [launchRules_source_eq hBridge, hComponentSource]
  exact hSource localRule hLocal

private theorem bridgeRules_pairwise {language : Language}
    (problem : VerifierTableauProblem language) :
    (bridgeRules problem).Pairwise QueryDistinct := by
  have hPrefix := launchRules_pairwise
    (prefixState (BuilderBodyStartPrefix.machine problem).acceptState)
    (evaluatorState
      (BuilderUnaryPolynomial.machine
        (nextTokenSlotPolynomial problem.verifier)).startState)
  have hEvaluator := launchRules_pairwise
    (evaluatorState
      (BuilderUnaryPolynomial.machine
        (nextTokenSlotPolynomial problem.verifier)).acceptState)
    (tAppenderState (BuilderTokenAppender.seekInputState .t))
  have hT := launchRules_pairwise
    (tAppenderState BuilderTokenAppender.machine.acceptState)
    (fAppenderState (BuilderTokenAppender.seekInputState .f))
  have hPE := launchRules_cross
    (prefixState (BuilderBodyStartPrefix.machine problem).acceptState)
    (evaluatorState
      (BuilderUnaryPolynomial.machine
        (nextTokenSlotPolynomial problem.verifier)).startState)
    (evaluatorState
      (BuilderUnaryPolynomial.machine
        (nextTokenSlotPolynomial problem.verifier)).acceptState)
    (tAppenderState (BuilderTokenAppender.seekInputState .t))
    (prefixState_ne_evaluatorState _ _)
  have hPT := launchRules_cross
    (prefixState (BuilderBodyStartPrefix.machine problem).acceptState)
    (evaluatorState
      (BuilderUnaryPolynomial.machine
        (nextTokenSlotPolynomial problem.verifier)).startState)
    (tAppenderState BuilderTokenAppender.machine.acceptState)
    (fAppenderState (BuilderTokenAppender.seekInputState .f))
    (prefixState_ne_tAppenderState _ _)
  have hET := launchRules_cross
    (evaluatorState
      (BuilderUnaryPolynomial.machine
        (nextTokenSlotPolynomial problem.verifier)).acceptState)
    (tAppenderState (BuilderTokenAppender.seekInputState .t))
    (tAppenderState BuilderTokenAppender.machine.acceptState)
    (fAppenderState (BuilderTokenAppender.seekInputState .f))
    (evaluatorState_ne_tAppenderState _ _)
  unfold bridgeRules prefixEvaluatorBridge evaluatorTBridge tFBridge
  rw [List.pairwise_append]
  refine ⟨hPrefix, ?_, ?_⟩
  · rw [List.pairwise_append]
    exact ⟨hEvaluator, hT, hET⟩
  · intro left hLeft right hRight
    simp only [List.mem_append] at hRight
    rcases hRight with hRight | hRight
    · exact hPE left hLeft right hRight
    · exact hPT left hLeft right hRight

private theorem prefixBridge_component_cross {language : Language}
    (problem : VerifierTableauProblem language) :
    ∀ bridge ∈ prefixEvaluatorBridge problem,
      ∀ component ∈ componentRules problem,
        QueryDistinct bridge component := by
  have hP := launchRenamed_cross
    (prefixState (BuilderBodyStartPrefix.machine problem).acceptState)
    (evaluatorState
      (BuilderUnaryPolynomial.machine
        (nextTokenSlotPolynomial problem.verifier)).startState)
    prefixState (BuilderBodyStartPrefix.machine problem).rules (by
      intro localRule hLocal hEqual
      exact bodyStart_rule_source_ne_accept problem localRule hLocal
        (prefixState_injective hEqual).symm)
  have hE := launchRenamed_cross
    (prefixState (BuilderBodyStartPrefix.machine problem).acceptState)
    (evaluatorState
      (BuilderUnaryPolynomial.machine
        (nextTokenSlotPolynomial problem.verifier)).startState)
    evaluatorState
    (BuilderUnaryPolynomial.machine
      (nextTokenSlotPolynomial problem.verifier)).rules (by
      intro localRule _hLocal
      exact prefixState_ne_evaluatorState _ _)
  have hT := launchRenamed_cross
    (prefixState (BuilderBodyStartPrefix.machine problem).acceptState)
    (evaluatorState
      (BuilderUnaryPolynomial.machine
        (nextTokenSlotPolynomial problem.verifier)).startState)
    tAppenderState BuilderTokenAppender.machine.rules (by
      intro localRule _hLocal
      exact prefixState_ne_tAppenderState _ _)
  have hF := launchRenamed_cross
    (prefixState (BuilderBodyStartPrefix.machine problem).acceptState)
    (evaluatorState
      (BuilderUnaryPolynomial.machine
        (nextTokenSlotPolynomial problem.verifier)).startState)
    fAppenderState BuilderTokenAppender.machine.rules (by
      intro localRule _hLocal
      exact prefixState_ne_fAppenderState _ _)
  intro bridge hBridge component hComponent
  simp only [componentRules, List.mem_append] at hComponent
  rcases hComponent with hComponent | hComponent | hComponent | hComponent
  · exact hP bridge hBridge component hComponent
  · exact hE bridge hBridge component hComponent
  · exact hT bridge hBridge component hComponent
  · exact hF bridge hBridge component hComponent

private theorem evaluatorBridge_component_cross {language : Language}
    (problem : VerifierTableauProblem language) :
    ∀ bridge ∈ evaluatorTBridge problem,
      ∀ component ∈ componentRules problem,
        QueryDistinct bridge component := by
  let evaluatorMachine := BuilderUnaryPolynomial.machine
    (nextTokenSlotPolynomial problem.verifier)
  have hP := launchRenamed_cross
    (evaluatorState evaluatorMachine.acceptState)
    (tAppenderState (BuilderTokenAppender.seekInputState .t))
    prefixState (BuilderBodyStartPrefix.machine problem).rules (by
      intro localRule _hLocal
      exact Ne.symm (prefixState_ne_evaluatorState _ _))
  have hE := launchRenamed_cross
    (evaluatorState evaluatorMachine.acceptState)
    (tAppenderState (BuilderTokenAppender.seekInputState .t))
    evaluatorState evaluatorMachine.rules (by
      intro localRule hLocal hEqual
      have hState := evaluatorState_injective hEqual
      have hLt := BuilderUnaryPolynomial.rule_source_lt_acceptState
        (nextTokenSlotPolynomial problem.verifier) localRule hLocal
      change localRule.sourceState < evaluatorMachine.acceptState at hLt
      omega)
  have hT := launchRenamed_cross
    (evaluatorState evaluatorMachine.acceptState)
    (tAppenderState (BuilderTokenAppender.seekInputState .t))
    tAppenderState BuilderTokenAppender.machine.rules (by
      intro localRule _hLocal
      exact evaluatorState_ne_tAppenderState _ _)
  have hF := launchRenamed_cross
    (evaluatorState evaluatorMachine.acceptState)
    (tAppenderState (BuilderTokenAppender.seekInputState .t))
    fAppenderState BuilderTokenAppender.machine.rules (by
      intro localRule _hLocal
      exact evaluatorState_ne_fAppenderState _ _)
  intro bridge hBridge component hComponent
  simp only [componentRules, List.mem_append] at hComponent
  rcases hComponent with hComponent | hComponent | hComponent | hComponent
  · exact hP bridge hBridge component hComponent
  · exact hE bridge hBridge component hComponent
  · exact hT bridge hBridge component hComponent
  · exact hF bridge hBridge component hComponent

private theorem tBridge_component_cross {language : Language}
    (problem : VerifierTableauProblem language) :
    ∀ bridge ∈ tFBridge problem,
      ∀ component ∈ componentRules problem,
        QueryDistinct bridge component := by
  have hP := launchRenamed_cross
    (tAppenderState BuilderTokenAppender.machine.acceptState)
    (fAppenderState (BuilderTokenAppender.seekInputState .f))
    prefixState (BuilderBodyStartPrefix.machine problem).rules (by
      intro localRule _hLocal
      exact Ne.symm (prefixState_ne_tAppenderState _ _))
  have hE := launchRenamed_cross
    (tAppenderState BuilderTokenAppender.machine.acceptState)
    (fAppenderState (BuilderTokenAppender.seekInputState .f))
    evaluatorState
      (BuilderUnaryPolynomial.machine
        (nextTokenSlotPolynomial problem.verifier)).rules (by
      intro localRule _hLocal
      exact Ne.symm (evaluatorState_ne_tAppenderState _ _))
  have hT := launchRenamed_cross
    (tAppenderState BuilderTokenAppender.machine.acceptState)
    (fAppenderState (BuilderTokenAppender.seekInputState .f))
    tAppenderState BuilderTokenAppender.machine.rules (by
      intro localRule hLocal hEqual
      exact appender_rule_source_ne_accept localRule hLocal
        (tAppenderState_injective hEqual).symm)
  have hF := launchRenamed_cross
    (tAppenderState BuilderTokenAppender.machine.acceptState)
    (fAppenderState (BuilderTokenAppender.seekInputState .f))
    fAppenderState BuilderTokenAppender.machine.rules (by
      intro localRule _hLocal
      exact tAppenderState_ne_fAppenderState _ _)
  intro bridge hBridge component hComponent
  simp only [componentRules, List.mem_append] at hComponent
  rcases hComponent with hComponent | hComponent | hComponent | hComponent
  · exact hP bridge hBridge component hComponent
  · exact hE bridge hBridge component hComponent
  · exact hT bridge hBridge component hComponent
  · exact hF bridge hBridge component hComponent

private theorem bridgeRules_componentRules_cross {language : Language}
    (problem : VerifierTableauProblem language) :
    ∀ bridge ∈ bridgeRules problem,
      ∀ component ∈ componentRules problem,
        QueryDistinct bridge component := by
  intro bridge hBridge component hComponent
  simp only [bridgeRules, List.mem_append] at hBridge
  rcases hBridge with hBridge | hBridge | hBridge
  · exact prefixBridge_component_cross problem bridge hBridge component hComponent
  · exact evaluatorBridge_component_cross problem bridge hBridge component hComponent
  · exact tBridge_component_cross problem bridge hBridge component hComponent

theorem rules_pairwise_query_distinct {language : Language}
    (problem : VerifierTableauProblem language) :
    (rules problem).Pairwise (fun left right =>
      (left.sourceState, left.readSymbol) ≠
        (right.sourceState, right.readSymbol)) := by
  change (rules problem).Pairwise QueryDistinct
  have hBridges := bridgeRules_pairwise problem
  have hComponents := componentRules_pairwise problem
  have hCross := bridgeRules_componentRules_cross problem
  unfold rules
  rw [List.pairwise_append]
  exact ⟨hBridges, hComponents, hCross⟩

/-- No local rule leaves the global accepting state.  Later bridge-first
compositions use this separation to preserve query determinism. -/
theorem rule_source_ne_acceptState {language : Language}
    (problem : VerifierTableauProblem language) (rule : WorkRule)
    (hMem : rule ∈ (machine problem).rules) :
    rule.sourceState ≠ (machine problem).acceptState := by
  unfold machine rules at hMem ⊢
  rw [List.mem_append] at hMem
  rcases hMem with hBridge | hComponent
  · unfold bridgeRules at hBridge
    simp only [List.mem_append] at hBridge
    rcases hBridge with hPrefix | hEvaluator | hT
    · have hSource := launchRules_source_eq
        (by simpa [prefixEvaluatorBridge] using hPrefix)
      rw [hSource]
      exact prefixState_ne_fAppenderState _ _
    · have hSource := launchRules_source_eq
        (by simpa [evaluatorTBridge] using hEvaluator)
      rw [hSource]
      exact evaluatorState_ne_fAppenderState _ _
    · have hSource := launchRules_source_eq
        (by simpa [tFBridge] using hT)
      rw [hSource]
      exact tAppenderState_ne_fAppenderState _ _
  · unfold componentRules at hComponent
    simp only [List.mem_append] at hComponent
    rcases hComponent with hPrefix | hEvaluator | hT | hF
    · rcases renamedRules_source hPrefix with
        ⟨localRule, _hLocal, hSource⟩
      rw [hSource]
      exact prefixState_ne_fAppenderState _ _
    · rcases renamedRules_source hEvaluator with
        ⟨localRule, _hLocal, hSource⟩
      rw [hSource]
      exact evaluatorState_ne_fAppenderState _ _
    · rcases renamedRules_source hT with
        ⟨localRule, _hLocal, hSource⟩
      rw [hSource]
      exact tAppenderState_ne_fAppenderState _ _
    · rcases renamedRules_source hF with
        ⟨localRule, hLocal, hSource⟩
      rw [hSource]
      intro hEqual
      exact appender_rule_source_ne_accept localRule hLocal
        (fAppenderState_injective hEqual)

/-! ### Exact endpoint and costs -/

def firstLiteralSignTokens {language : Language}
    (problem : VerifierTableauProblem language) : List CNFToken :=
  BuilderBodyStartPrefix.bodyStartTokens problem ++ [.t]

def firstLiteralTokens {language : Language}
    (problem : VerifierTableauProblem language) : List CNFToken :=
  firstLiteralSignTokens problem ++ [.f]

def finalOutside {language : Language}
    (problem : VerifierTableauProblem language) : List WorkSymbol :=
  BuilderUnaryPolynomial.finalOutsideLeft
    (nextTokenSlotPolynomial problem.verifier) problem.input
    (BuilderBodyStartPrefix.finalOutside problem)

def finalTape {language : Language}
    (problem : VerifierTableauProblem language) : WorkTape :=
  BuilderTokenAppender.workspaceTape problem.input
    (finalOutside problem) (firstLiteralTokens problem)

def finalConfiguration {language : Language}
    (problem : VerifierTableauProblem language) : WorkConfiguration :=
  { state := (machine problem).acceptState
    tape := finalTape problem }

def workSteps {language : Language}
    (problem : VerifierTableauProblem language) : Nat :=
  BuilderBodyStartPrefix.workSteps problem + 1 +
    BuilderUnaryPolynomial.workSteps
      (nextTokenSlotPolynomial problem.verifier) problem.input + 1 +
    BuilderTokenAppender.workSteps problem.input
      (BuilderBodyStartPrefix.bodyStartTokens problem) + 1 +
    BuilderTokenAppender.workSteps problem.input
      (firstLiteralSignTokens problem)

private def scalePolynomial (coefficient : Nat)
    (polynomial : NatPolynomial) : NatPolynomial :=
  .mul (.constant coefficient) polynomial

/-- External compiled-time polynomial for the first-literal prefix. -/
def rawTimeBound {language : Language}
    (verifier : PolynomialTimeVerifier language) : NatPolynomial :=
  .add (BuilderBodyStartPrefix.rawTimeBound verifier)
    (.add (.constant 174)
      (.add
        (scalePolynomial 6
          (BuilderUnaryPolynomial.workTimePolynomial
            (nextTokenSlotPolynomial verifier)))
        (.add (scalePolynomial 48 .variable)
          (scalePolynomial 24 (formulaWidthPolynomial verifier)))))

theorem finalTape_represents {language : Language}
    (problem : VerifierTableauProblem language) :
    Represents (Tape.ofInput problem.input) (finalTape problem) := by
  exact BuilderTokenAppender.workspaceTape_represents problem.input
    (finalOutside problem) (firstLiteralTokens problem)

/-- The final exterior-left region contains the evaluator's root register as
an exact unary encoding of the next token coordinate. -/
theorem finalOutside_contains_nextTokenSlot {language : Language}
    (problem : VerifierTableauProblem language) :
    ∃ wordPrefix tail,
      finalOutside problem =
        wordPrefix ++ BuilderUnaryPolynomial.separatorSymbol ::
          List.replicate (nextTokenSlot problem)
            BuilderUnaryPolynomial.unitSymbol ++
          BuilderUnaryPolynomial.scratchEndSymbol :: tail := by
  rcases BuilderUnaryPolynomial.root_register_length
      (nextTokenSlotPolynomial problem.verifier) problem.input.length with
    ⟨wordPrefix, hScratch, _hPrefixLength⟩
  refine ⟨wordPrefix,
    (BuilderBodyStartPrefix.finalOutside problem).drop
      ((BuilderUnaryPolynomial.scratchWord
        (nextTokenSlotPolynomial problem.verifier)
        problem.input.length).length + 1), ?_⟩
  unfold finalOutside BuilderUnaryPolynomial.finalOutsideLeft
    BuilderUnaryPolynomial.overlayScratch
  rw [hScratch]
  rfl

/-! ### Halt separation and lookup isolation -/

private theorem nat_beq_false_of_ne (left right : Nat)
    (h : left ≠ right) : (left == right) = false := by
  cases hBool : (left == right) with
  | false => rfl
  | true =>
      exact False.elim (h ((nat_beq_true_iff left right).mp hBool))

private theorem state_ne_accept_of_not_halted
    (source : WorkMachine) (config : WorkConfiguration)
    (hHalted : source.isHalted config = false) :
    config.state ≠ source.acceptState := by
  intro hState
  unfold WorkMachine.isHalted at hHalted
  rw [hState] at hHalted
  have hRefl : (source.acceptState == source.acceptState) = true :=
    (nat_beq_true_iff _ _).mpr rfl
  rw [hRefl] at hHalted
  contradiction

private theorem state_ne_reject_of_not_halted
    (source : WorkMachine) (config : WorkConfiguration)
    (hHalted : source.isHalted config = false) :
    config.state ≠ source.rejectState := by
  intro hState
  unfold WorkMachine.isHalted at hHalted
  rw [hState] at hHalted
  have hRefl : (source.rejectState == source.rejectState) = true :=
    (nat_beq_true_iff _ _).mpr rfl
  cases hAccept : (source.rejectState == source.acceptState) with
  | false =>
      rw [hAccept, hRefl] at hHalted
      contradiction
  | true =>
      rw [hAccept, hRefl] at hHalted
      contradiction

private theorem machine_isHalted_prefix_false {language : Language}
    (problem : VerifierTableauProblem language)
    (config : WorkConfiguration) :
    (machine problem).isHalted
      (renameConfiguration prefixState config) = false := by
  unfold WorkMachine.isHalted machine renameConfiguration
  rw [nat_beq_false_of_ne _ _
      (prefixState_ne_fAppenderState config.state
        BuilderTokenAppender.machine.acceptState),
    nat_beq_false_of_ne _ _
      (prefixState_ne_fAppenderState config.state
        BuilderTokenAppender.machine.rejectState)]
  rfl

private theorem machine_isHalted_evaluator_false {language : Language}
    (problem : VerifierTableauProblem language)
    (config : WorkConfiguration) :
    (machine problem).isHalted
      (renameConfiguration evaluatorState config) = false := by
  unfold WorkMachine.isHalted machine renameConfiguration
  rw [nat_beq_false_of_ne _ _
      (evaluatorState_ne_fAppenderState config.state
        BuilderTokenAppender.machine.acceptState),
    nat_beq_false_of_ne _ _
      (evaluatorState_ne_fAppenderState config.state
        BuilderTokenAppender.machine.rejectState)]
  rfl

private theorem machine_isHalted_tAppender_false
    {language : Language} (problem : VerifierTableauProblem language)
    (config : WorkConfiguration) :
    (machine problem).isHalted
      (renameConfiguration tAppenderState config) = false := by
  unfold WorkMachine.isHalted machine renameConfiguration
  rw [nat_beq_false_of_ne _ _
      (tAppenderState_ne_fAppenderState config.state
        BuilderTokenAppender.machine.acceptState),
    nat_beq_false_of_ne _ _
      (tAppenderState_ne_fAppenderState config.state
        BuilderTokenAppender.machine.rejectState)]
  rfl

private theorem machine_isHalted_fAppender_false_of_local
    {language : Language} (problem : VerifierTableauProblem language)
    (config : WorkConfiguration)
    (hLocal : BuilderTokenAppender.machine.isHalted config = false) :
    (machine problem).isHalted
      (renameConfiguration fAppenderState config) = false := by
  have hAccept := state_ne_accept_of_not_halted
    BuilderTokenAppender.machine config hLocal
  have hReject := state_ne_reject_of_not_halted
    BuilderTokenAppender.machine config hLocal
  have hGlobalAccept : fAppenderState config.state ≠
      fAppenderState BuilderTokenAppender.machine.acceptState := by
    intro h
    exact hAccept (fAppenderState_injective h)
  have hGlobalReject : fAppenderState config.state ≠
      fAppenderState BuilderTokenAppender.machine.rejectState := by
    intro h
    exact hReject (fAppenderState_injective h)
  unfold WorkMachine.isHalted machine renameConfiguration
  rw [nat_beq_false_of_ne _ _ hGlobalAccept,
    nat_beq_false_of_ne _ _ hGlobalReject]
  rfl

theorem findWorkRule_prefix_of_some {language : Language}
    (problem : VerifierTableauProblem language)
    (state : Nat) (symbol : WorkSymbol) (rule : WorkRule)
    (hAccept : state ≠ (BuilderBodyStartPrefix.machine problem).acceptState)
    (hFind : findWorkRule (BuilderBodyStartPrefix.machine problem).rules
      state symbol = some rule) :
    findWorkRule (machine problem).rules (prefixState state) symbol =
      some (renameRule prefixState rule) := by
  have hBridgeOne : findWorkRule (prefixEvaluatorBridge problem)
      (prefixState state) symbol = none := by
    apply findWorkRule_launchRules_none_of_source_ne
    intro h
    exact hAccept (prefixState_injective h).symm
  have hBridgeTwo : findWorkRule (evaluatorTBridge problem)
      (prefixState state) symbol = none := by
    apply findWorkRule_launchRules_none_of_source_ne
    exact Ne.symm (prefixState_ne_evaluatorState _ _)
  have hBridgeThree : findWorkRule (tFBridge problem)
      (prefixState state) symbol = none := by
    apply findWorkRule_launchRules_none_of_source_ne
    exact Ne.symm (prefixState_ne_tAppenderState _ _)
  have hBridges : findWorkRule (bridgeRules problem)
      (prefixState state) symbol = none := by
    unfold bridgeRules
    rw [findWorkRule_append_of_none _ _ _ _ hBridgeOne]
    rw [findWorkRule_append_of_none _ _ _ _ hBridgeTwo]
    exact hBridgeThree
  have hRenamed := findWorkRule_rename prefixState prefixState_injective
    (BuilderBodyStartPrefix.machine problem).rules state symbol
  rw [hFind] at hRenamed
  unfold machine rules componentRules
  rw [findWorkRule_append_of_none _ _ _ _ hBridges]
  exact findWorkRule_append_of_some _ _ _ _ _ hRenamed

theorem findWorkRule_evaluator_of_some {language : Language}
    (problem : VerifierTableauProblem language)
    (state : Nat) (symbol : WorkSymbol) (rule : WorkRule)
    (hAccept : state ≠
      (BuilderUnaryPolynomial.machine
        (nextTokenSlotPolynomial problem.verifier)).acceptState)
    (hFind : findWorkRule
      (BuilderUnaryPolynomial.machine
        (nextTokenSlotPolynomial problem.verifier)).rules
      state symbol = some rule) :
    findWorkRule (machine problem).rules (evaluatorState state) symbol =
      some (renameRule evaluatorState rule) := by
  have hBridgeOne : findWorkRule (prefixEvaluatorBridge problem)
      (evaluatorState state) symbol = none := by
    apply findWorkRule_launchRules_none_of_source_ne
    exact prefixState_ne_evaluatorState _ _
  have hBridgeTwo : findWorkRule (evaluatorTBridge problem)
      (evaluatorState state) symbol = none := by
    apply findWorkRule_launchRules_none_of_source_ne
    intro h
    exact hAccept (evaluatorState_injective h).symm
  have hBridgeThree : findWorkRule (tFBridge problem)
      (evaluatorState state) symbol = none := by
    apply findWorkRule_launchRules_none_of_source_ne
    exact Ne.symm (evaluatorState_ne_tAppenderState _ _)
  have hBridges : findWorkRule (bridgeRules problem)
      (evaluatorState state) symbol = none := by
    unfold bridgeRules
    rw [findWorkRule_append_of_none _ _ _ _ hBridgeOne]
    rw [findWorkRule_append_of_none _ _ _ _ hBridgeTwo]
    exact hBridgeThree
  have hHeader : findWorkRule
      ((BuilderBodyStartPrefix.machine problem).rules.map
        (renameRule prefixState)) (evaluatorState state) symbol = none := by
    apply findWorkRule_renamedRules_none
    intro source
    exact prefixState_ne_evaluatorState source state
  have hRenamed := findWorkRule_rename evaluatorState evaluatorState_injective
    (BuilderUnaryPolynomial.machine
      (nextTokenSlotPolynomial problem.verifier)).rules state symbol
  rw [hFind] at hRenamed
  unfold machine rules componentRules
  rw [findWorkRule_append_of_none _ _ _ _ hBridges,
    findWorkRule_append_of_none _ _ _ _ hHeader]
  exact findWorkRule_append_of_some _ _ _ _ _ hRenamed

theorem findWorkRule_tAppender_of_some {language : Language}
    (problem : VerifierTableauProblem language)
    (state : Nat) (symbol : WorkSymbol) (rule : WorkRule)
    (hAccept : state ≠ BuilderTokenAppender.machine.acceptState)
    (hFind : findWorkRule BuilderTokenAppender.machine.rules
      state symbol = some rule) :
    findWorkRule (machine problem).rules (tAppenderState state) symbol =
      some (renameRule tAppenderState rule) := by
  have hBridgeOne : findWorkRule (prefixEvaluatorBridge problem)
      (tAppenderState state) symbol = none := by
    apply findWorkRule_launchRules_none_of_source_ne
    exact prefixState_ne_tAppenderState _ _
  have hBridgeTwo : findWorkRule (evaluatorTBridge problem)
      (tAppenderState state) symbol = none := by
    apply findWorkRule_launchRules_none_of_source_ne
    exact evaluatorState_ne_tAppenderState _ _
  have hBridgeThree : findWorkRule (tFBridge problem)
      (tAppenderState state) symbol = none := by
    apply findWorkRule_launchRules_none_of_source_ne
    intro h
    exact hAccept (tAppenderState_injective h).symm
  have hBridges : findWorkRule (bridgeRules problem)
      (tAppenderState state) symbol = none := by
    unfold bridgeRules
    rw [findWorkRule_append_of_none _ _ _ _ hBridgeOne]
    rw [findWorkRule_append_of_none _ _ _ _ hBridgeTwo]
    exact hBridgeThree
  have hHeader : findWorkRule
      ((BuilderBodyStartPrefix.machine problem).rules.map
        (renameRule prefixState)) (tAppenderState state) symbol = none := by
    apply findWorkRule_renamedRules_none
    intro source
    exact prefixState_ne_tAppenderState source state
  have hCursor : findWorkRule
      ((BuilderUnaryPolynomial.machine
        (nextTokenSlotPolynomial problem.verifier)).rules.map
          (renameRule evaluatorState))
      (tAppenderState state) symbol = none := by
    apply findWorkRule_renamedRules_none
    intro source
    exact evaluatorState_ne_tAppenderState source state
  have hRenamed := findWorkRule_rename tAppenderState tAppenderState_injective
    BuilderTokenAppender.machine.rules state symbol
  rw [hFind] at hRenamed
  unfold machine rules componentRules
  rw [findWorkRule_append_of_none _ _ _ _ hBridges,
    findWorkRule_append_of_none _ _ _ _ hHeader,
    findWorkRule_append_of_none _ _ _ _ hCursor]
  exact findWorkRule_append_of_some _ _ _ _ _ hRenamed

theorem findWorkRule_fAppender_of_some {language : Language}
    (problem : VerifierTableauProblem language)
    (state : Nat) (symbol : WorkSymbol) (rule : WorkRule)
    (hFind : findWorkRule BuilderTokenAppender.machine.rules
      state symbol = some rule) :
    findWorkRule (machine problem).rules (fAppenderState state) symbol =
      some (renameRule fAppenderState rule) := by
  have hBridgeOne : findWorkRule (prefixEvaluatorBridge problem)
      (fAppenderState state) symbol = none := by
    apply findWorkRule_launchRules_none_of_source_ne
    exact prefixState_ne_fAppenderState _ _
  have hBridgeTwo : findWorkRule (evaluatorTBridge problem)
      (fAppenderState state) symbol = none := by
    apply findWorkRule_launchRules_none_of_source_ne
    exact evaluatorState_ne_fAppenderState _ _
  have hBridgeThree : findWorkRule (tFBridge problem)
      (fAppenderState state) symbol = none := by
    apply findWorkRule_launchRules_none_of_source_ne
    exact tAppenderState_ne_fAppenderState _ _
  have hBridges : findWorkRule (bridgeRules problem)
      (fAppenderState state) symbol = none := by
    unfold bridgeRules
    rw [findWorkRule_append_of_none _ _ _ _ hBridgeOne]
    rw [findWorkRule_append_of_none _ _ _ _ hBridgeTwo]
    exact hBridgeThree
  have hPrefix : findWorkRule
      ((BuilderBodyStartPrefix.machine problem).rules.map
        (renameRule prefixState)) (fAppenderState state) symbol = none := by
    apply findWorkRule_renamedRules_none
    intro source
    exact prefixState_ne_fAppenderState source state
  have hEvaluator : findWorkRule
      ((BuilderUnaryPolynomial.machine
        (nextTokenSlotPolynomial problem.verifier)).rules.map
          (renameRule evaluatorState))
      (fAppenderState state) symbol = none := by
    apply findWorkRule_renamedRules_none
    intro source
    exact evaluatorState_ne_fAppenderState source state
  have hT : findWorkRule
      (BuilderTokenAppender.machine.rules.map (renameRule tAppenderState))
      (fAppenderState state) symbol = none := by
    apply findWorkRule_renamedRules_none
    intro source
    exact tAppenderState_ne_fAppenderState source state
  have hRenamed := findWorkRule_rename fAppenderState fAppenderState_injective
    BuilderTokenAppender.machine.rules state symbol
  rw [hFind] at hRenamed
  unfold machine rules componentRules
  rw [findWorkRule_append_of_none _ _ _ _ hBridges,
    findWorkRule_append_of_none _ _ _ _ hPrefix,
    findWorkRule_append_of_none _ _ _ _ hEvaluator,
    findWorkRule_append_of_none _ _ _ _ hT]
  exact hRenamed

private theorem prefix_workStep_of_some {language : Language}
    (problem : VerifierTableauProblem language)
    (config next : WorkConfiguration)
    (hStep : workStep? (BuilderBodyStartPrefix.machine problem) config =
      some next) :
    workStep? (machine problem) (renameConfiguration prefixState config) =
      some (renameConfiguration prefixState next) := by
  rcases workStep?_some_exists (BuilderBodyStartPrefix.machine problem)
      config next hStep with ⟨rule, hHalted, hFind, hNext⟩
  have hAccept := state_ne_accept_of_not_halted
    (BuilderBodyStartPrefix.machine problem) config hHalted
  have hGlobalHalted := machine_isHalted_prefix_false problem config
  have hGlobalFind := findWorkRule_prefix_of_some problem
    config.state config.tape.head rule hAccept hFind
  have hGlobalStep := workStep?_eq_apply_of_find (machine problem)
    (renameConfiguration prefixState config) (renameRule prefixState rule)
    hGlobalHalted hGlobalFind
  calc
    workStep? (machine problem) (renameConfiguration prefixState config) =
        some (applyWorkRule (renameRule prefixState rule)
          (renameConfiguration prefixState config)) := hGlobalStep
    _ = some (renameConfiguration prefixState
          (applyWorkRule rule config)) :=
      congrArg Option.some (applyWorkRule_rename prefixState rule config)
    _ = some (renameConfiguration prefixState next) :=
      congrArg (fun value => some (renameConfiguration prefixState value))
        hNext.symm

private theorem evaluator_workStep_of_some {language : Language}
    (problem : VerifierTableauProblem language)
    (config next : WorkConfiguration)
    (hStep : workStep?
      (BuilderUnaryPolynomial.machine
        (nextTokenSlotPolynomial problem.verifier)) config = some next) :
    workStep? (machine problem) (renameConfiguration evaluatorState config) =
      some (renameConfiguration evaluatorState next) := by
  let cursorMachine := BuilderUnaryPolynomial.machine
    (nextTokenSlotPolynomial problem.verifier)
  rcases workStep?_some_exists cursorMachine config next hStep with
    ⟨rule, hHalted, hFind, hNext⟩
  have hAccept := state_ne_accept_of_not_halted cursorMachine config hHalted
  have hGlobalHalted := machine_isHalted_evaluator_false problem config
  have hGlobalFind := findWorkRule_evaluator_of_some problem
    config.state config.tape.head rule hAccept hFind
  have hGlobalStep := workStep?_eq_apply_of_find (machine problem)
    (renameConfiguration evaluatorState config) (renameRule evaluatorState rule)
    hGlobalHalted hGlobalFind
  calc
    workStep? (machine problem) (renameConfiguration evaluatorState config) =
        some (applyWorkRule (renameRule evaluatorState rule)
          (renameConfiguration evaluatorState config)) := hGlobalStep
    _ = some (renameConfiguration evaluatorState
          (applyWorkRule rule config)) :=
      congrArg Option.some (applyWorkRule_rename evaluatorState rule config)
    _ = some (renameConfiguration evaluatorState next) :=
      congrArg (fun value => some (renameConfiguration evaluatorState value))
        hNext.symm

private theorem tAppender_workStep_of_some {language : Language}
    (problem : VerifierTableauProblem language)
    (config next : WorkConfiguration)
    (hStep : workStep? BuilderTokenAppender.machine config = some next) :
    workStep? (machine problem) (renameConfiguration tAppenderState config) =
      some (renameConfiguration tAppenderState next) := by
  rcases workStep?_some_exists BuilderTokenAppender.machine config next hStep
    with ⟨rule, hHalted, hFind, hNext⟩
  have hAccept := state_ne_accept_of_not_halted
    BuilderTokenAppender.machine config hHalted
  have hGlobalHalted :=
    machine_isHalted_tAppender_false problem config
  have hGlobalFind := findWorkRule_tAppender_of_some problem
    config.state config.tape.head rule hAccept hFind
  have hGlobalStep := workStep?_eq_apply_of_find (machine problem)
    (renameConfiguration tAppenderState config) (renameRule tAppenderState rule)
    hGlobalHalted hGlobalFind
  calc
    workStep? (machine problem) (renameConfiguration tAppenderState config) =
        some (applyWorkRule (renameRule tAppenderState rule)
          (renameConfiguration tAppenderState config)) := hGlobalStep
    _ = some (renameConfiguration tAppenderState
          (applyWorkRule rule config)) :=
      congrArg Option.some (applyWorkRule_rename tAppenderState rule config)
    _ = some (renameConfiguration tAppenderState next) :=
      congrArg (fun value => some (renameConfiguration tAppenderState value))
        hNext.symm

private theorem fAppender_workStep_of_some {language : Language}
    (problem : VerifierTableauProblem language)
    (config next : WorkConfiguration)
    (hStep : workStep? BuilderTokenAppender.machine config = some next) :
    workStep? (machine problem) (renameConfiguration fAppenderState config) =
      some (renameConfiguration fAppenderState next) := by
  rcases workStep?_some_exists BuilderTokenAppender.machine config next hStep
    with ⟨rule, hHalted, hFind, hNext⟩
  have hGlobalHalted :=
    machine_isHalted_fAppender_false_of_local problem config hHalted
  have hGlobalFind := findWorkRule_fAppender_of_some problem
    config.state config.tape.head rule hFind
  have hGlobalStep := workStep?_eq_apply_of_find (machine problem)
    (renameConfiguration fAppenderState config) (renameRule fAppenderState rule)
    hGlobalHalted hGlobalFind
  calc
    workStep? (machine problem) (renameConfiguration fAppenderState config) =
        some (applyWorkRule (renameRule fAppenderState rule)
          (renameConfiguration fAppenderState config)) := hGlobalStep
    _ = some (renameConfiguration fAppenderState
          (applyWorkRule rule config)) :=
      congrArg Option.some (applyWorkRule_rename fAppenderState rule config)
    _ = some (renameConfiguration fAppenderState next) :=
      congrArg (fun value => some (renameConfiguration fAppenderState value))
        hNext.symm

/-! ### Launches and exact all-input trace -/

theorem prefixEvaluator_launch_workStep {language : Language}
    (problem : VerifierTableauProblem language) :
    workStep? (machine problem)
        (renameConfiguration prefixState
          (BuilderBodyStartPrefix.finalConfiguration problem)) =
      some (renameConfiguration evaluatorState
        (BuilderUnaryPolynomial.initialConfiguration
          (nextTokenSlotPolynomial problem.verifier) problem.input
          (BuilderBodyStartPrefix.finalOutside problem)
          (BuilderBodyStartPrefix.bodyStartTokens problem))) := by
  let final := BuilderBodyStartPrefix.finalConfiguration problem
  have hHalted := machine_isHalted_prefix_false problem final
  have hLaunch := findWorkRule_launchRules
    (prefixState (BuilderBodyStartPrefix.machine problem).acceptState)
    (evaluatorState
      (BuilderUnaryPolynomial.machine
        (nextTokenSlotPolynomial problem.verifier)).startState)
    final.tape.head
  have hBridgeFind : findWorkRule (bridgeRules problem)
      (prefixState final.state) final.tape.head =
        some (launchRule
          (prefixState (BuilderBodyStartPrefix.machine problem).acceptState)
          (evaluatorState
            (BuilderUnaryPolynomial.machine
              (nextTokenSlotPolynomial problem.verifier)).startState)
          final.tape.head) := by
    unfold bridgeRules
    simpa [prefixEvaluatorBridge, final,
      BuilderBodyStartPrefix.finalConfiguration] using
      (findWorkRule_append_of_some _ _ _ _ _ hLaunch)
  have hFind : findWorkRule (machine problem).rules
      (prefixState final.state) final.tape.head =
        some (launchRule
          (prefixState (BuilderBodyStartPrefix.machine problem).acceptState)
          (evaluatorState
            (BuilderUnaryPolynomial.machine
              (nextTokenSlotPolynomial problem.verifier)).startState)
          final.tape.head) := by
    unfold machine rules
    exact findWorkRule_append_of_some _ _ _ _ _ hBridgeFind
  have hStep := workStep?_eq_apply_of_find (machine problem)
    (renameConfiguration prefixState final)
    (launchRule
      (prefixState (BuilderBodyStartPrefix.machine problem).acceptState)
      (evaluatorState
        (BuilderUnaryPolynomial.machine
          (nextTokenSlotPolynomial problem.verifier)).startState)
      final.tape.head) hHalted hFind
  simpa [final, launchRule, applyWorkRule, WorkTape.write, WorkTape.move,
    renameConfiguration, BuilderBodyStartPrefix.finalConfiguration,
    BuilderBodyStartPrefix.finalTape,
    BuilderUnaryPolynomial.initialConfiguration] using hStep

theorem evaluatorT_launch_workStep {language : Language}
    (problem : VerifierTableauProblem language) :
    workStep? (machine problem)
        (renameConfiguration evaluatorState
          (BuilderUnaryPolynomial.finalConfiguration
            (nextTokenSlotPolynomial problem.verifier) problem.input
            (BuilderBodyStartPrefix.finalOutside problem)
            (BuilderBodyStartPrefix.bodyStartTokens problem))) =
      some (renameConfiguration tAppenderState
        (BuilderTokenAppender.entryConfiguration .t
          (BuilderTokenAppender.workspaceTape problem.input
            (finalOutside problem)
            (BuilderBodyStartPrefix.bodyStartTokens problem)))) := by
  let final := BuilderUnaryPolynomial.finalConfiguration
    (nextTokenSlotPolynomial problem.verifier) problem.input
    (BuilderBodyStartPrefix.finalOutside problem)
    (BuilderBodyStartPrefix.bodyStartTokens problem)
  have hHalted := machine_isHalted_evaluator_false problem final
  have hLaunch := findWorkRule_launchRules
    (evaluatorState
      (BuilderUnaryPolynomial.machine
        (nextTokenSlotPolynomial problem.verifier)).acceptState)
    (tAppenderState (BuilderTokenAppender.seekInputState .t))
    final.tape.head
  have hBridgeOne : findWorkRule (prefixEvaluatorBridge problem)
      (evaluatorState final.state) final.tape.head = none := by
    apply findWorkRule_launchRules_none_of_source_ne
    exact prefixState_ne_evaluatorState _ _
  have hBridgeFind : findWorkRule (bridgeRules problem)
      (evaluatorState final.state) final.tape.head =
        some (launchRule
          (evaluatorState
            (BuilderUnaryPolynomial.machine
              (nextTokenSlotPolynomial problem.verifier)).acceptState)
          (tAppenderState (BuilderTokenAppender.seekInputState .t))
          final.tape.head) := by
    unfold bridgeRules
    rw [findWorkRule_append_of_none _ _ _ _ hBridgeOne]
    simpa [evaluatorTBridge, final,
      BuilderUnaryPolynomial.finalConfiguration] using
      (findWorkRule_append_of_some _ _ _ _ _ hLaunch)
  have hFind : findWorkRule (machine problem).rules
      (evaluatorState final.state) final.tape.head =
        some (launchRule
          (evaluatorState
            (BuilderUnaryPolynomial.machine
              (nextTokenSlotPolynomial problem.verifier)).acceptState)
          (tAppenderState (BuilderTokenAppender.seekInputState .t))
          final.tape.head) := by
    unfold machine rules
    exact findWorkRule_append_of_some _ _ _ _ _ hBridgeFind
  have hStep := workStep?_eq_apply_of_find (machine problem)
    (renameConfiguration evaluatorState final)
    (launchRule
      (evaluatorState
        (BuilderUnaryPolynomial.machine
          (nextTokenSlotPolynomial problem.verifier)).acceptState)
      (tAppenderState (BuilderTokenAppender.seekInputState .t))
      final.tape.head) hHalted hFind
  simpa [final, launchRule, applyWorkRule, WorkTape.write, WorkTape.move,
    renameConfiguration, BuilderUnaryPolynomial.finalConfiguration,
    BuilderTokenAppender.entryConfiguration, finalOutside] using hStep

theorem tF_launch_workStep {language : Language}
    (problem : VerifierTableauProblem language) :
    workStep? (machine problem)
        (renameConfiguration tAppenderState
          (BuilderTokenAppender.finalConfiguration problem.input
            (finalOutside problem)
            (firstLiteralSignTokens problem))) =
      some (renameConfiguration fAppenderState
        (BuilderTokenAppender.entryConfiguration .f
          (BuilderTokenAppender.workspaceTape problem.input
            (finalOutside problem)
            (firstLiteralSignTokens problem)))) := by
  let final := BuilderTokenAppender.finalConfiguration problem.input
    (finalOutside problem)
    (firstLiteralSignTokens problem)
  have hHalted := machine_isHalted_tAppender_false problem final
  have hLaunch := findWorkRule_launchRules
    (tAppenderState BuilderTokenAppender.machine.acceptState)
    (fAppenderState (BuilderTokenAppender.seekInputState .f))
    final.tape.head
  have hBridgeOne : findWorkRule (prefixEvaluatorBridge problem)
      (tAppenderState final.state) final.tape.head = none := by
    apply findWorkRule_launchRules_none_of_source_ne
    exact prefixState_ne_tAppenderState _ _
  have hBridgeTwo : findWorkRule (evaluatorTBridge problem)
      (tAppenderState final.state) final.tape.head = none := by
    apply findWorkRule_launchRules_none_of_source_ne
    exact evaluatorState_ne_tAppenderState _ _
  have hBridgeFind : findWorkRule (bridgeRules problem)
      (tAppenderState final.state) final.tape.head =
        some (launchRule
          (tAppenderState BuilderTokenAppender.machine.acceptState)
          (fAppenderState (BuilderTokenAppender.seekInputState .f))
          final.tape.head) := by
    unfold bridgeRules
    rw [findWorkRule_append_of_none _ _ _ _ hBridgeOne]
    rw [findWorkRule_append_of_none _ _ _ _ hBridgeTwo]
    simpa [tFBridge, final, BuilderTokenAppender.finalConfiguration] using
      hLaunch
  have hFind : findWorkRule (machine problem).rules
      (tAppenderState final.state) final.tape.head =
        some (launchRule
          (tAppenderState BuilderTokenAppender.machine.acceptState)
          (fAppenderState (BuilderTokenAppender.seekInputState .f))
          final.tape.head) := by
    unfold machine rules
    exact findWorkRule_append_of_some _ _ _ _ _ hBridgeFind
  have hStep := workStep?_eq_apply_of_find (machine problem)
    (renameConfiguration tAppenderState final)
    (launchRule
      (tAppenderState BuilderTokenAppender.machine.acceptState)
      (fAppenderState (BuilderTokenAppender.seekInputState .f))
      final.tape.head) hHalted hFind
  simpa [final, launchRule, applyWorkRule, WorkTape.write, WorkTape.move,
    renameConfiguration, BuilderTokenAppender.finalConfiguration,
    BuilderTokenAppender.entryConfiguration] using hStep

theorem prefix_workRunExact {language : Language}
    (problem : VerifierTableauProblem language) :
    workRunExact? (machine problem) (BuilderBodyStartPrefix.workSteps problem)
        (workStartConfiguration (machine problem)
          (rawInputWorkTape problem.input)) =
      some (renameConfiguration prefixState
        (BuilderBodyStartPrefix.finalConfiguration problem)) := by
  have hTransport := PipelineStageBridges.workRunExact?_transport
    (BuilderBodyStartPrefix.machine problem) (machine problem) prefixState
    (prefix_workStep_of_some problem) (BuilderBodyStartPrefix.workSteps problem)
    (workStartConfiguration (BuilderBodyStartPrefix.machine problem)
      (rawInputWorkTape problem.input))
    (BuilderBodyStartPrefix.finalConfiguration problem)
    (BuilderBodyStartPrefix.workRunExact problem)
  simpa [machine, workStartConfiguration, renameConfiguration] using hTransport

theorem evaluator_workRunExact {language : Language}
    (problem : VerifierTableauProblem language) :
    workRunExact? (machine problem)
        (BuilderUnaryPolynomial.workSteps
          (nextTokenSlotPolynomial problem.verifier) problem.input)
        (renameConfiguration evaluatorState
          (BuilderUnaryPolynomial.initialConfiguration
            (nextTokenSlotPolynomial problem.verifier) problem.input
            (BuilderBodyStartPrefix.finalOutside problem)
            (BuilderBodyStartPrefix.bodyStartTokens problem))) =
      some (renameConfiguration evaluatorState
        (BuilderUnaryPolynomial.finalConfiguration
          (nextTokenSlotPolynomial problem.verifier) problem.input
          (BuilderBodyStartPrefix.finalOutside problem)
          (BuilderBodyStartPrefix.bodyStartTokens problem))) := by
  have hLocal := BuilderUnaryPolynomial.workRunExact
    (nextTokenSlotPolynomial problem.verifier) problem.input
    (BuilderBodyStartPrefix.finalOutside problem)
    (BuilderBodyStartPrefix.bodyStartTokens problem)
  exact PipelineStageBridges.workRunExact?_transport
    (BuilderUnaryPolynomial.machine
      (nextTokenSlotPolynomial problem.verifier))
    (machine problem) evaluatorState (evaluator_workStep_of_some problem)
    (BuilderUnaryPolynomial.workSteps
      (nextTokenSlotPolynomial problem.verifier) problem.input)
    (BuilderUnaryPolynomial.initialConfiguration
      (nextTokenSlotPolynomial problem.verifier) problem.input
      (BuilderBodyStartPrefix.finalOutside problem)
      (BuilderBodyStartPrefix.bodyStartTokens problem))
    (BuilderUnaryPolynomial.finalConfiguration
      (nextTokenSlotPolynomial problem.verifier) problem.input
      (BuilderBodyStartPrefix.finalOutside problem)
      (BuilderBodyStartPrefix.bodyStartTokens problem)) hLocal

private theorem appender_workRunExact_transport {language : Language}
    (problem : VerifierTableauProblem language) (encode : Nat → Nat)
    (hStep : ∀ config next,
      workStep? BuilderTokenAppender.machine config = some next →
      workStep? (machine problem) (renameConfiguration encode config) =
        some (renameConfiguration encode next))
    (outside : List WorkSymbol) (output : List CNFToken)
    (token : CNFToken) :
    workRunExact? (machine problem)
        (BuilderTokenAppender.workSteps problem.input output)
        (renameConfiguration encode
          (BuilderTokenAppender.entryConfiguration token
            (BuilderTokenAppender.workspaceTape problem.input outside output))) =
      some (renameConfiguration encode
        (BuilderTokenAppender.finalConfiguration problem.input outside
          (output ++ [token]))) := by
  exact PipelineStageBridges.workRunExact?_transport
    BuilderTokenAppender.machine (machine problem) encode hStep
    (BuilderTokenAppender.workSteps problem.input output)
    (BuilderTokenAppender.entryConfiguration token
      (BuilderTokenAppender.workspaceTape problem.input outside output))
    (BuilderTokenAppender.finalConfiguration problem.input outside
      (output ++ [token]))
    (BuilderTokenAppender.appendToken_workRunExact
      problem.input outside output token)

theorem tAppender_workRunExact {language : Language}
    (problem : VerifierTableauProblem language) :
    workRunExact? (machine problem)
        (BuilderTokenAppender.workSteps problem.input
          (BuilderBodyStartPrefix.bodyStartTokens problem))
        (renameConfiguration tAppenderState
          (BuilderTokenAppender.entryConfiguration .t
            (BuilderTokenAppender.workspaceTape problem.input
              (finalOutside problem)
              (BuilderBodyStartPrefix.bodyStartTokens problem)))) =
      some (renameConfiguration tAppenderState
        (BuilderTokenAppender.finalConfiguration problem.input
          (finalOutside problem)
          (firstLiteralSignTokens problem))) := by
  exact appender_workRunExact_transport problem tAppenderState
    (tAppender_workStep_of_some problem) (finalOutside problem)
    (BuilderBodyStartPrefix.bodyStartTokens problem) .t

set_option maxRecDepth 2000 in
set_option maxHeartbeats 800000 in
theorem fAppender_workRunExact {language : Language}
    (problem : VerifierTableauProblem language) :
    workRunExact? (machine problem)
        (BuilderTokenAppender.workSteps problem.input
          (firstLiteralSignTokens problem))
        (renameConfiguration fAppenderState
          (BuilderTokenAppender.entryConfiguration .f
            (BuilderTokenAppender.workspaceTape problem.input
              (finalOutside problem)
              (firstLiteralSignTokens problem)))) =
      some (renameConfiguration fAppenderState
        (BuilderTokenAppender.finalConfiguration problem.input
          (finalOutside problem)
          ((firstLiteralSignTokens problem) ++
            [.f]))) := by
  exact appender_workRunExact_transport
    (problem := problem)
    (encode := fAppenderState)
    (hStep := fAppender_workStep_of_some problem)
    (outside := finalOutside problem)
    (output := firstLiteralSignTokens problem)
    (token := .f)

private theorem fAppenderFinal_eq_finalConfiguration {language : Language}
    (problem : VerifierTableauProblem language) :
    renameConfiguration fAppenderState
        (BuilderTokenAppender.finalConfiguration problem.input
          (finalOutside problem)
          ((firstLiteralSignTokens problem) ++
            [.f])) =
      finalConfiguration problem := by
  simp [renameConfiguration, BuilderTokenAppender.finalConfiguration,
    finalConfiguration, finalTape, firstLiteralTokens, machine]

set_option maxRecDepth 2000 in
set_option maxHeartbeats 1200000 in
/-- Every raw input follows one exact successful trace through the body-start
prefix, retained cursor construction, and first canonical literal. -/
theorem workRunExact {language : Language}
    (problem : VerifierTableauProblem language) :
    workRunExact? (machine problem) (workSteps problem)
        (workStartConfiguration (machine problem)
          (rawInputWorkTape problem.input)) =
      some (finalConfiguration problem) := by
  have hLaunchOne : workRunExact? (machine problem) 1
      (renameConfiguration prefixState
        (BuilderBodyStartPrefix.finalConfiguration problem)) =
      some (renameConfiguration evaluatorState
        (BuilderUnaryPolynomial.initialConfiguration
          (nextTokenSlotPolynomial problem.verifier) problem.input
          (BuilderBodyStartPrefix.finalOutside problem)
          (BuilderBodyStartPrefix.bodyStartTokens problem))) := by
    change
      (match workStep? (machine problem)
          (renameConfiguration prefixState
            (BuilderBodyStartPrefix.finalConfiguration problem)) with
       | none => none
       | some next => workRunExact? (machine problem) 0 next) = _
    rw [prefixEvaluator_launch_workStep problem]
    rfl
  have hLaunchTwo : workRunExact? (machine problem) 1
      (renameConfiguration evaluatorState
        (BuilderUnaryPolynomial.finalConfiguration
          (nextTokenSlotPolynomial problem.verifier) problem.input
          (BuilderBodyStartPrefix.finalOutside problem)
          (BuilderBodyStartPrefix.bodyStartTokens problem))) =
      some (renameConfiguration tAppenderState
        (BuilderTokenAppender.entryConfiguration .t
          (BuilderTokenAppender.workspaceTape problem.input
            (finalOutside problem)
            (BuilderBodyStartPrefix.bodyStartTokens problem)))) := by
    change
      (match workStep? (machine problem)
          (renameConfiguration evaluatorState
            (BuilderUnaryPolynomial.finalConfiguration
              (nextTokenSlotPolynomial problem.verifier) problem.input
              (BuilderBodyStartPrefix.finalOutside problem)
              (BuilderBodyStartPrefix.bodyStartTokens problem))) with
       | none => none
       | some next => workRunExact? (machine problem) 0 next) = _
    rw [evaluatorT_launch_workStep problem]
    rfl
  have hLaunchThree : workRunExact? (machine problem) 1
      (renameConfiguration tAppenderState
        (BuilderTokenAppender.finalConfiguration problem.input
          (finalOutside problem)
          (firstLiteralSignTokens problem))) =
      some (renameConfiguration fAppenderState
        (BuilderTokenAppender.entryConfiguration .f
          (BuilderTokenAppender.workspaceTape problem.input
            (finalOutside problem)
            (firstLiteralSignTokens problem)))) := by
    change
      (match workStep? (machine problem)
          (renameConfiguration tAppenderState
            (BuilderTokenAppender.finalConfiguration problem.input
              (finalOutside problem)
              (firstLiteralSignTokens problem))) with
       | none => none
       | some next => workRunExact? (machine problem) 0 next) = _
    rw [tF_launch_workStep problem]
    rfl
  have h01 := PipelineMachineSimulation.workRunExact?_compose
    (machine problem) (BuilderBodyStartPrefix.workSteps problem) 1
    (workStartConfiguration (machine problem)
      (rawInputWorkTape problem.input))
    (renameConfiguration prefixState
      (BuilderBodyStartPrefix.finalConfiguration problem))
    (renameConfiguration evaluatorState
      (BuilderUnaryPolynomial.initialConfiguration
        (nextTokenSlotPolynomial problem.verifier) problem.input
        (BuilderBodyStartPrefix.finalOutside problem)
        (BuilderBodyStartPrefix.bodyStartTokens problem)))
    (prefix_workRunExact problem) hLaunchOne
  have h02 := PipelineMachineSimulation.workRunExact?_compose
    (machine problem) (BuilderBodyStartPrefix.workSteps problem + 1)
    (BuilderUnaryPolynomial.workSteps
      (nextTokenSlotPolynomial problem.verifier) problem.input)
    (workStartConfiguration (machine problem)
      (rawInputWorkTape problem.input))
    (renameConfiguration evaluatorState
      (BuilderUnaryPolynomial.initialConfiguration
        (nextTokenSlotPolynomial problem.verifier) problem.input
        (BuilderBodyStartPrefix.finalOutside problem)
        (BuilderBodyStartPrefix.bodyStartTokens problem)))
    (renameConfiguration evaluatorState
      (BuilderUnaryPolynomial.finalConfiguration
        (nextTokenSlotPolynomial problem.verifier) problem.input
        (BuilderBodyStartPrefix.finalOutside problem)
        (BuilderBodyStartPrefix.bodyStartTokens problem))) h01
    (evaluator_workRunExact problem)
  have h03 := PipelineMachineSimulation.workRunExact?_compose
    (machine problem)
    (BuilderBodyStartPrefix.workSteps problem + 1 +
      BuilderUnaryPolynomial.workSteps
        (nextTokenSlotPolynomial problem.verifier) problem.input) 1
    (workStartConfiguration (machine problem)
      (rawInputWorkTape problem.input))
    (renameConfiguration evaluatorState
      (BuilderUnaryPolynomial.finalConfiguration
        (nextTokenSlotPolynomial problem.verifier) problem.input
        (BuilderBodyStartPrefix.finalOutside problem)
        (BuilderBodyStartPrefix.bodyStartTokens problem)))
    (renameConfiguration tAppenderState
      (BuilderTokenAppender.entryConfiguration .t
        (BuilderTokenAppender.workspaceTape problem.input
          (finalOutside problem)
          (BuilderBodyStartPrefix.bodyStartTokens problem)))) h02 hLaunchTwo
  have h04 := PipelineMachineSimulation.workRunExact?_compose
    (machine problem)
    (BuilderBodyStartPrefix.workSteps problem + 1 +
      BuilderUnaryPolynomial.workSteps
        (nextTokenSlotPolynomial problem.verifier) problem.input + 1)
    (BuilderTokenAppender.workSteps problem.input
      (BuilderBodyStartPrefix.bodyStartTokens problem))
    (workStartConfiguration (machine problem)
      (rawInputWorkTape problem.input))
    (renameConfiguration tAppenderState
      (BuilderTokenAppender.entryConfiguration .t
        (BuilderTokenAppender.workspaceTape problem.input
          (finalOutside problem)
          (BuilderBodyStartPrefix.bodyStartTokens problem))))
    (renameConfiguration tAppenderState
      (BuilderTokenAppender.finalConfiguration problem.input
        (finalOutside problem)
        (firstLiteralSignTokens problem)))
    h03 (tAppender_workRunExact problem)
  let tFinal := renameConfiguration tAppenderState
    (BuilderTokenAppender.finalConfiguration problem.input
      (finalOutside problem)
      (firstLiteralSignTokens problem))
  let fInitial := renameConfiguration fAppenderState
    (BuilderTokenAppender.entryConfiguration .f
      (BuilderTokenAppender.workspaceTape problem.input
        (finalOutside problem)
        (firstLiteralSignTokens problem)))
  have h04' : workRunExact? (machine problem)
      (BuilderBodyStartPrefix.workSteps problem + 1 +
        BuilderUnaryPolynomial.workSteps
          (nextTokenSlotPolynomial problem.verifier) problem.input + 1 +
        BuilderTokenAppender.workSteps problem.input
          (BuilderBodyStartPrefix.bodyStartTokens problem))
      (workStartConfiguration (machine problem)
        (rawInputWorkTape problem.input)) = some tFinal := by
    simpa [tFinal, Nat.add_assoc] using h04
  have hLaunchThree' : workRunExact? (machine problem) 1 tFinal =
      some fInitial := by
    simpa [tFinal, fInitial] using hLaunchThree
  have h05 := PipelineMachineSimulation.workRunExact?_compose
    (machine problem)
    (BuilderBodyStartPrefix.workSteps problem + 1 +
      BuilderUnaryPolynomial.workSteps
        (nextTokenSlotPolynomial problem.verifier) problem.input + 1 +
      BuilderTokenAppender.workSteps problem.input
        (BuilderBodyStartPrefix.bodyStartTokens problem)) 1
    (workStartConfiguration (machine problem)
      (rawInputWorkTape problem.input))
    tFinal fInitial h04' hLaunchThree'
  let fFinal := renameConfiguration fAppenderState
    (BuilderTokenAppender.finalConfiguration problem.input
      (finalOutside problem)
      ((firstLiteralSignTokens problem) ++ [.f]))
  have hF : workRunExact? (machine problem)
      (BuilderTokenAppender.workSteps problem.input
        (firstLiteralSignTokens problem))
      fInitial = some fFinal := by
    simpa [fInitial, fFinal] using fAppender_workRunExact problem
  let beforeFSteps := BuilderBodyStartPrefix.workSteps problem + 1 +
    BuilderUnaryPolynomial.workSteps
      (nextTokenSlotPolynomial problem.verifier) problem.input + 1 +
    BuilderTokenAppender.workSteps problem.input
      (BuilderBodyStartPrefix.bodyStartTokens problem) + 1
  let fSteps := BuilderTokenAppender.workSteps problem.input
    (firstLiteralSignTokens problem)
  have h05' : workRunExact? (machine problem) beforeFSteps
      (workStartConfiguration (machine problem)
        (rawInputWorkTape problem.input)) = some fInitial := by
    simpa [beforeFSteps, Nat.add_assoc] using h05
  have hF' : workRunExact? (machine problem) fSteps fInitial =
      some fFinal := by
    simpa [fSteps] using hF
  have h06 := PipelineMachineSimulation.workRunExact?_compose
    (machine problem) beforeFSteps fSteps
    (workStartConfiguration (machine problem)
      (rawInputWorkTape problem.input))
    fInitial fFinal h05' hF'
  have hFinal : fFinal = finalConfiguration problem := by
    simpa [fFinal] using fAppenderFinal_eq_finalConfiguration problem
  rw [hFinal] at h06
  simpa [workSteps, beforeFSteps, fSteps, Nat.add_assoc] using h06

/-! ### Canonical first literal and external bound -/

theorem firstLiteralTokens_eq_canonical_prefix {language : Language}
    (problem : VerifierTableauProblem language) :
    firstLiteralTokens problem =
      encodeUnaryTokens problem.FormulaWidth ++ [.sep, .t, .f] := by
  unfold firstLiteralTokens firstLiteralSignTokens
  rw [BuilderBodyStartPrefix.bodyStartTokens_eq_canonical_prefix]
  simp [List.append_assoc]

private theorem finiteIndices_starts_zero (width : Nat)
    (hWidth : 0 < width) :
    ∃ rest, finiteIndices width = ⟨0, hWidth⟩ :: rest := by
  cases width with
  | zero => exact False.elim (Nat.not_lt_zero 0 hWidth)
  | succ width => exact ⟨(finiteIndices width).map Fin.succ, rfl⟩

private theorem scheduledShapeConstraints_starts_firstSymbol
    {language : Language} (problem : VerifierTableauProblem language) :
    let time : Fin problem.dimensions.timeCount :=
      ⟨0, problem.dimensions.timeCount_positive⟩
    let position : Fin
        (problem.dimensions.tapeWidth problem.tableauInputMode) :=
      ⟨0, problem.dimensions.tapeWidth_positive problem.tableauInputMode⟩
    ∃ rest,
      problem.scheduledShapeConstraints =
        some (problem.symbolShapeAt time position) :: rest := by
  dsimp
  let time : Fin problem.dimensions.timeCount :=
    ⟨0, problem.dimensions.timeCount_positive⟩
  let position : Fin
      (problem.dimensions.tapeWidth problem.tableauInputMode) :=
    ⟨0, problem.dimensions.tapeWidth_positive problem.tableauInputMode⟩
  rcases finiteIndices_starts_zero problem.dimensions.timeCount
      problem.dimensions.timeCount_positive with ⟨times, hTimes⟩
  rcases finiteIndices_starts_zero
      (problem.dimensions.tapeWidth problem.tableauInputMode)
      (problem.dimensions.tapeWidth_positive problem.tableauInputMode) with
    ⟨positions, hPositions⟩
  refine ⟨(positions.map fun next =>
      some (problem.symbolShapeAt time next)) ++
      [some (problem.headShapeAt time), some (problem.stateShapeAt time)] ++
      times.flatMap fun next =>
        ((finiteIndices
          (problem.dimensions.tapeWidth problem.tableauInputMode)).map
            fun nextPosition =>
              some (problem.symbolShapeAt next nextPosition)) ++
          [some (problem.headShapeAt next), some (problem.stateShapeAt next)],
    ?_⟩
  unfold VerifierTableauProblem.scheduledShapeConstraints
  rw [hTimes]
  simp only [List.flatMap_cons]
  rw [hPositions]
  rfl

private theorem formulaConstraintSchedule_starts_firstSymbol
    {language : Language} (problem : VerifierTableauProblem language) :
    let time : Fin problem.dimensions.timeCount :=
      ⟨0, problem.dimensions.timeCount_positive⟩
    let position : Fin
        (problem.dimensions.tapeWidth problem.tableauInputMode) :=
      ⟨0, problem.dimensions.tapeWidth_positive problem.tableauInputMode⟩
    ∃ rest,
      problem.formulaConstraintSchedule =
        some (problem.symbolShapeAt time position) :: rest := by
  dsimp
  rcases scheduledShapeConstraints_starts_firstSymbol problem with
    ⟨rest, hRest⟩
  refine ⟨rest ++ problem.scheduledInitialConstraints ++
      problem.scheduledControlConstraints ++
      problem.scheduledPreservationConstraints ++
      [some (.require
        (problem.stateLiteral problem.finalTime problem.acceptingState))], ?_⟩
  unfold VerifierTableauProblem.formulaConstraintSchedule
  rw [hRest]
  simp [List.append_assoc]

private theorem formulaClauseSchedule_starts_firstShapeClause
    {language : Language} (problem : VerifierTableauProblem language) :
    let time : Fin problem.dimensions.timeCount :=
      ⟨0, problem.dimensions.timeCount_positive⟩
    let position : Fin
        (problem.dimensions.tapeWidth problem.tableauInputMode) :=
      ⟨0, problem.dimensions.tapeWidth_positive problem.tableauInputMode⟩
    ∃ rest,
      problem.formulaClauseSchedule =
        some (atLeastOneBoundedClause
          (problem.symbolVariables time position)) :: rest := by
  dsimp
  rcases formulaConstraintSchedule_starts_firstSymbol problem with
    ⟨constraints, hConstraints⟩
  rw [VerifierTableauProblem.formulaClauseSchedule, hConstraints]
  simp only [List.flatMap_cons]
  unfold VerifierTableauProblem.symbolShapeAt
  dsimp [VerifierTableauProblem.scheduledConstraintClauses,
    LocalConstraint.emit, exactlyOneBoundedClauses, FormulaSchedule.pad]
  exact ⟨_, rfl⟩

private theorem firstShapeClause_emit_starts_zero
    {language : Language} (problem : VerifierTableauProblem language) :
    let time : Fin problem.dimensions.timeCount :=
      ⟨0, problem.dimensions.timeCount_positive⟩
    let position : Fin
        (problem.dimensions.tapeWidth problem.tableauInputMode) :=
      ⟨0, problem.dimensions.tapeWidth_positive problem.tableauInputMode⟩
    ∃ rest,
      BoundedClause.emit
          (atLeastOneBoundedClause
            (problem.symbolVariables time position)) =
        ({ positive := true, variableIndex := 0 } : CNFLiteral) :: rest := by
  dsimp
  simp [BoundedClause.emit, atLeastOneBoundedClause,
    VerifierTableauProblem.symbolVariables, tapeSymbols, trueLiteral,
    BoundedLiteral.emit, VerifierTableauProblem.symbolLiteral,
    VariableLayout.symbolVariable, VariableLayout.symbolLocalIndex,
    VariableLayout.symbolBlock, VariableBlock.index,
    VariableLayout.flattenTwo, VariableLayout.tapeSymbolCode]

private theorem formulaClauseTokens_starts_firstLiteral
    {language : Language} (problem : VerifierTableauProblem language) :
    ∃ rest,
      problem.formulaClauseSchedule.flatMap problem.scheduledClauseTokens =
        some CNFToken.sep :: some CNFToken.t :: some CNFToken.f :: rest := by
  rcases formulaClauseSchedule_starts_firstShapeClause problem with
    ⟨clauses, hClauses⟩
  rcases firstShapeClause_emit_starts_zero problem with
    ⟨literals, hLiterals⟩
  rw [hClauses]
  simp only [List.flatMap_cons]
  dsimp [VerifierTableauProblem.scheduledClauseTokens]
  rw [hLiterals]
  simp only [encodeClauseTokens, encodeLiteralListTokens,
    encodeLiteralTokens, encodeUnaryTokens]
  unfold FormulaSchedule.pad
  exact ⟨_, rfl⟩

/-- The first literal sign is the positive sign of the blank-symbol variable
at time zero and tape position zero. -/
theorem firstLiteralSignSlotDirect_eq_t {language : Language}
    (problem : VerifierTableauProblem language) :
    problem.formulaTokenSlotDirect
        (problem.formulaVariableSlotBound + 2) =
      some (some CNFToken.t) := by
  rw [problem.formulaTokenSlotDirect_eq]
  have hHeader :
      (FormulaSchedule.pad (problem.formulaVariableSlotBound + 1)
        (encodeUnaryTokens problem.FormulaWidth)).length =
      problem.formulaVariableSlotBound + 1 := by
    apply FormulaSchedule.pad_length
    rw [encodeUnaryTokens_length]
    unfold VerifierTableauProblem.formulaVariableSlotBound
    exact Nat.add_le_add_right
      problem.formulaWidth_le_formulaVariableCountPolynomial 1
  unfold VerifierTableauProblem.formulaTokenSchedule
  rw [List.append_assoc, List.getElem?_append, hHeader]
  have hNotLt : ¬ problem.formulaVariableSlotBound + 2 <
      problem.formulaVariableSlotBound + 1 := by omega
  simp only [hNotLt, ↓reduceIte]
  rcases formulaClauseTokens_starts_firstLiteral problem with ⟨rest, hRest⟩
  rw [hRest]
  simp

/-- Variable index zero is encoded by the immediate unary terminator `F`. -/
theorem firstLiteralZeroTerminatorSlotDirect_eq_f {language : Language}
    (problem : VerifierTableauProblem language) :
    problem.formulaTokenSlotDirect
        (problem.formulaVariableSlotBound + 3) =
      some (some CNFToken.f) := by
  rw [problem.formulaTokenSlotDirect_eq]
  have hHeader :
      (FormulaSchedule.pad (problem.formulaVariableSlotBound + 1)
        (encodeUnaryTokens problem.FormulaWidth)).length =
      problem.formulaVariableSlotBound + 1 := by
    apply FormulaSchedule.pad_length
    rw [encodeUnaryTokens_length]
    unfold VerifierTableauProblem.formulaVariableSlotBound
    exact Nat.add_le_add_right
      problem.formulaWidth_le_formulaVariableCountPolynomial 1
  unfold VerifierTableauProblem.formulaTokenSchedule
  rw [List.append_assoc, List.getElem?_append, hHeader]
  have hNotLt : ¬ problem.formulaVariableSlotBound + 3 <
      problem.formulaVariableSlotBound + 1 := by omega
  simp only [hNotLt, ↓reduceIte]
  rcases formulaClauseTokens_starts_firstLiteral problem with ⟨rest, hRest⟩
  rw [hRest]
  simp

private theorem encodeTokenPairs_append_local
    (left right : List CNFToken) :
    encodeTokenPairs (left ++ right) =
      encodeTokenPairs left ++ encodeTokenPairs right := by
  induction left with
  | nil => rfl
  | cons token rest ih =>
      cases token <;>
        simp [encodeTokenPairs, ih, List.append_assoc]

private theorem encodeCNFTokens_starts_firstLiteralPrefix
    {language : Language} (problem : VerifierTableauProblem language) :
    ∃ rest,
      encodeCNFTokens problem.formula =
        encodeUnaryTokens problem.FormulaWidth ++
          CNFToken.sep :: CNFToken.t :: CNFToken.f :: rest := by
  rcases formulaClauseTokens_starts_firstLiteral problem with
    ⟨clauseTail, hClauseTail⟩
  refine ⟨FormulaSchedule.emit clauseTail ++ [CNFToken.finish], ?_⟩
  rw [← problem.formulaTokenSchedule_emit_eq_encodeCNFTokens]
  unfold VerifierTableauProblem.formulaTokenSchedule
  rw [FormulaSchedule.emit_append, FormulaSchedule.emit_append,
    FormulaSchedule.emit_pad, hClauseTail]
  simp [List.append_assoc]

/-- The emitted tokens are exactly the canonical formula prefix through its
first literal, namely positive variable zero. -/
theorem firstLiteralTokens_eq_canonical_formula_prefix {language : Language}
    (problem : VerifierTableauProblem language) :
    ∃ rest, encodeCNFTokens problem.formula =
      firstLiteralTokens problem ++ rest := by
  rcases encodeCNFTokens_starts_firstLiteralPrefix problem with
    ⟨rest, hRest⟩
  refine ⟨rest, ?_⟩
  rw [firstLiteralTokens_eq_canonical_prefix]
  simpa [List.append_assoc] using hRest

/-- The emitted token pairs are exactly the canonical encoded-formula prefix
through the first literal. -/
theorem finalTokenBits_eq_encodedFormula_firstLiteral {language : Language}
    (problem : VerifierTableauProblem language) :
    encodeTokenPairs (firstLiteralTokens problem) =
      problem.encodedFormula.take (2 * (problem.FormulaWidth + 4)) := by
  rw [firstLiteralTokens_eq_canonical_prefix]
  rcases encodeCNFTokens_starts_firstLiteralPrefix problem with
    ⟨rest, hTokens⟩
  have hLength := encodeTokenPairs_length
    (encodeUnaryTokens problem.FormulaWidth ++
      [CNFToken.sep, CNFToken.t, CNFToken.f])
  have hUnaryLength := encodeUnaryTokens_length problem.FormulaWidth
  simp only [List.length_append, List.length_cons, List.length_nil,
    hUnaryLength] at hLength
  let suffix := encodeTokenPairs rest ++ [false]
  have hShape : problem.encodedFormula =
      encodeTokenPairs
          (encodeUnaryTokens problem.FormulaWidth ++
            [CNFToken.sep, CNFToken.t, CNFToken.f]) ++
        suffix := by
    simp only [VerifierTableauProblem.encodedFormula, encodeCNF]
    rw [hTokens,
      show CNFToken.sep :: CNFToken.t :: CNFToken.f :: rest =
        [CNFToken.sep, CNFToken.t, CNFToken.f] ++ rest by rfl,
      ← List.append_assoc, encodeTokenPairs_append_local]
    simp [suffix, List.append_assoc]
  rw [hShape, ← hLength]
  exact List.take_left.symm

private theorem tAppender_workSteps_le (input : BitString)
    (output : List CNFToken) :
    BuilderTokenAppender.workSteps input output ≤
      4 * input.length + 2 * output.length + 8 := by
  have hSource := BuilderTokenAppender.sourceCellCount_le input
  unfold BuilderTokenAppender.workSteps BuilderTokenAppender.halfSteps
  omega

theorem rawTimeBound_eval {language : Language}
    (problem : VerifierTableauProblem language) :
    (rawTimeBound problem.verifier).eval problem.input.length =
      (BuilderBodyStartPrefix.rawTimeBound problem.verifier).eval
          problem.input.length + 174 +
        6 * BuilderUnaryPolynomial.workSteps
          (nextTokenSlotPolynomial problem.verifier) problem.input +
        48 * problem.input.length +
        24 * problem.FormulaWidth := by
  rw [rawTimeBound]
  simp only [NatPolynomial.eval_add, NatPolynomial.eval_constant,
    NatPolynomial.eval_mul, scalePolynomial,
    BuilderUnaryPolynomial.workTimePolynomial_eval,
    NatPolynomial.eval_variable]
  have hWidth :
      (formulaWidthPolynomial problem.verifier).eval problem.input.length =
        problem.FormulaWidth := by
    simpa [BitString.size] using problem.formulaWidthPolynomial_eval
  rw [hWidth]
  omega

theorem rawTimeBound_le {language : Language}
    (problem : VerifierTableauProblem language) :
    6 * workSteps problem ≤
      (rawTimeBound problem.verifier).eval problem.input.length := by
  have hPrefix := BuilderBodyStartPrefix.rawTimeBound_le problem
  have hT := tAppender_workSteps_le problem.input
    (BuilderBodyStartPrefix.bodyStartTokens problem)
  have hF := tAppender_workSteps_le problem.input
    (firstLiteralSignTokens problem)
  have hBodyLength :
      (BuilderBodyStartPrefix.bodyStartTokens problem).length =
        problem.FormulaWidth + 2 := by
    rw [BuilderBodyStartPrefix.bodyStartTokens_eq_canonical_prefix]
    simp [encodeUnaryTokens_length]
  have hTLength :
      (firstLiteralSignTokens problem).length =
        problem.FormulaWidth + 3 := by
    unfold firstLiteralSignTokens
    rw [List.length_append, hBodyLength]
    simp
  rw [hBodyLength] at hT
  rw [hTLength] at hF
  rw [rawTimeBound_eval]
  unfold workSteps
  omega

private theorem finalConfiguration_isHalted {language : Language}
    (problem : VerifierTableauProblem language) :
    (machine problem).isHalted (finalConfiguration problem) = true := by
  rfl

theorem run_compile_exact {language : Language}
    (problem : VerifierTableauProblem language) :
    run (compileWorkMachine (machine problem)) (6 * workSteps problem)
        (encodeWorkConfiguration
          (workStartConfiguration (machine problem)
            (rawInputWorkTape problem.input))) =
      encodeWorkConfiguration (finalConfiguration problem) := by
  exact run_compileWorkMachine_mul_of_workRunExact (machine problem)
    (workSteps problem)
    (workStartConfiguration (machine problem)
      (rawInputWorkTape problem.input))
    (finalConfiguration problem) (workRunExact problem)

theorem run_compile_rawTimeBound {language : Language}
    (problem : VerifierTableauProblem language) :
    run (compileWorkMachine (machine problem))
        ((rawTimeBound problem.verifier).eval problem.input.length)
        (encodeWorkConfiguration
          (workStartConfiguration (machine problem)
            (rawInputWorkTape problem.input))) =
      encodeWorkConfiguration (finalConfiguration problem) := by
  exact run_compileWorkMachine_of_workRunExact_halted_le
    (machine problem) (workSteps problem)
    ((rawTimeBound problem.verifier).eval problem.input.length)
    (workStartConfiguration (machine problem)
      (rawInputWorkTape problem.input))
    (finalConfiguration problem) (workRunExact problem)
    (finalConfiguration_isHalted problem) (rawTimeBound_le problem)

theorem run_compile_rawTimeBound_blankEquivalent {language : Language}
    (problem : VerifierTableauProblem language) :
    Configuration.BlankEquivalent
      (run (compileWorkMachine (machine problem))
        ((rawTimeBound problem.verifier).eval problem.input.length)
        (startConfig (compileWorkMachine (machine problem)) problem.input))
      (encodeWorkConfiguration (finalConfiguration problem)) := by
  have hStart := startConfig_compileWorkMachine_blankEquivalent
    (machine problem) problem.input
  have hRun := run_blankEquivalent (compileWorkMachine (machine problem))
    ((rawTimeBound problem.verifier).eval problem.input.length) hStart
  rw [run_compile_rawTimeBound problem] at hRun
  exact hRun

theorem boundedDecide_compile_accept {language : Language}
    (problem : VerifierTableauProblem language) :
    boundedDecide (compileWorkMachine (machine problem))
        ((rawTimeBound problem.verifier).eval problem.input.length)
        problem.input = .accept := by
  apply (boundedDecide_accept_iff_final
    (compileWorkMachine (machine problem))
    ((rawTimeBound problem.verifier).eval problem.input.length)
    problem.input).mpr
  exact (run_compile_rawTimeBound_blankEquivalent problem).1

theorem boundedDecide_compile_ne_timeout {language : Language}
    (problem : VerifierTableauProblem language) :
    boundedDecide (compileWorkMachine (machine problem))
        ((rawTimeBound problem.verifier).eval problem.input.length)
        problem.input ≠ .timeout := by
  rw [boundedDecide_compile_accept]
  intro impossible
  contradiction

theorem workBoundedDecide_accept {language : Language}
    (problem : VerifierTableauProblem language) :
    workBoundedDecide (machine problem) (workSteps problem)
      (rawInputWorkTape problem.input) = .accept := by
  unfold workBoundedDecide
  rw [workRun_eq_of_workRunExact (machine problem) (workSteps problem)
    (workStartConfiguration (machine problem)
      (rawInputWorkTape problem.input))
    (finalConfiguration problem) (workRunExact problem)]
  rfl

/-! ### Fail-closed trace boundaries -/

private theorem verdict_timeout_of_not_halted {language : Language}
    (problem : VerifierTableauProblem language)
    (config : WorkConfiguration)
    (hHalted : (machine problem).isHalted config = false) :
    (if config.state == (machine problem).acceptState then WorkVerdict.accept
     else if config.state == (machine problem).rejectState then
       WorkVerdict.reject
     else WorkVerdict.timeout) = WorkVerdict.timeout := by
  unfold WorkMachine.isHalted at hHalted
  cases hAccept : (config.state == (machine problem).acceptState) with
  | true =>
      rw [hAccept] at hHalted
      contradiction
  | false =>
      cases hReject : (config.state == (machine problem).rejectState) with
      | true =>
          rw [hAccept, hReject] at hHalted
          contradiction
      | false => rfl

private theorem stuck_timeout {language : Language}
    (problem : VerifierTableauProblem language) (fuel : Nat)
    (config : WorkConfiguration)
    (hHalted : (machine problem).isHalted config = false)
    (hStep : workStep? (machine problem) config = none) :
    (let result := workRun (machine problem) fuel config
     if result.state == (machine problem).acceptState then WorkVerdict.accept
     else if result.state == (machine problem).rejectState then
       WorkVerdict.reject
     else WorkVerdict.timeout) = WorkVerdict.timeout := by
  have hRun := workRun_eq_self_of_workStep?_eq_none
    (machine problem) config fuel hStep
  rw [hRun]
  exact verdict_timeout_of_not_halted problem config hHalted

/-- The complete-header endpoint remains nonhalting until the first new
bridge launches the unary next-token cursor. -/
theorem prefixEndpoint_before_launch_timeout {language : Language}
    (problem : VerifierTableauProblem language) :
    workBoundedDecide (machine problem)
        (BuilderBodyStartPrefix.workSteps problem)
        (rawInputWorkTape problem.input) = .timeout := by
  unfold workBoundedDecide
  rw [workRun_eq_of_workRunExact (machine problem)
    (BuilderBodyStartPrefix.workSteps problem)
    (workStartConfiguration (machine problem)
      (rawInputWorkTape problem.input))
    (renameConfiguration prefixState
      (BuilderBodyStartPrefix.finalConfiguration problem))
    (prefix_workRunExact problem)]
  exact verdict_timeout_of_not_halted problem _
    (machine_isHalted_prefix_false problem
      (BuilderBodyStartPrefix.finalConfiguration problem))

private theorem findWorkRule_none_of_sources_ne
    (localRules : List WorkRule) (state : Nat) (symbol : WorkSymbol)
    (hSource : ∀ rule ∈ localRules, rule.sourceState ≠ state) :
    findWorkRule localRules state symbol = none := by
  induction localRules with
  | nil => rfl
  | cons first rest ih =>
      rw [findWorkRule_cons_of_not_matches]
      · exact ih (fun rule hMem => hSource rule (List.mem_cons_of_mem first hMem))
      · intro hMatch
        exact hSource first (List.mem_cons_self) hMatch.1

private theorem findWorkRule_prefixReject_none {language : Language}
    (problem : VerifierTableauProblem language) (symbol : WorkSymbol) :
    findWorkRule (machine problem).rules
        (prefixState (BuilderBodyStartPrefix.machine problem).rejectState)
        symbol = none := by
  let headerMachine := BuilderBodyStartPrefix.machine problem
  have hBridgeOne : findWorkRule (prefixEvaluatorBridge problem)
      (prefixState headerMachine.rejectState) symbol = none := by
    apply findWorkRule_launchRules_none_of_source_ne
    intro h
    exact BuilderBodyStartPrefix.machine_acceptState_ne_rejectState problem
      (prefixState_injective h)
  have hBridgeTwo : findWorkRule (evaluatorTBridge problem)
      (prefixState headerMachine.rejectState) symbol = none := by
    apply findWorkRule_launchRules_none_of_source_ne
    exact Ne.symm (prefixState_ne_evaluatorState _ _)
  have hBridges : findWorkRule (bridgeRules problem)
      (prefixState headerMachine.rejectState) symbol = none := by
    unfold bridgeRules
    rw [findWorkRule_append_of_none _ _ _ _ hBridgeOne]
    exact hBridgeTwo
  have hLocal : findWorkRule headerMachine.rules
      headerMachine.rejectState symbol = none := by
    apply findWorkRule_none_of_sources_ne
    intro rule hMem
    exact bodyStart_rule_source_ne_reject problem rule hMem
  have hHeader := findWorkRule_rename prefixState prefixState_injective
    headerMachine.rules headerMachine.rejectState symbol
  rw [hLocal] at hHeader
  have hCursor : findWorkRule
      ((BuilderUnaryPolynomial.machine
        (nextTokenSlotPolynomial problem.verifier)).rules.map
          (renameRule evaluatorState))
      (prefixState headerMachine.rejectState) symbol = none := by
    apply findWorkRule_renamedRules_none
    intro source
    exact Ne.symm (prefixState_ne_evaluatorState _ _)
  have hAppender : findWorkRule
      (BuilderTokenAppender.machine.rules.map (renameRule tAppenderState))
      (prefixState headerMachine.rejectState) symbol = none := by
    apply findWorkRule_renamedRules_none
    intro source
    exact Ne.symm (prefixState_ne_tAppenderState _ _)
  unfold machine rules componentRules
  rw [findWorkRule_append_of_none _ _ _ _ hBridges,
    findWorkRule_append_of_none _ _ _ _ hHeader,
    findWorkRule_append_of_none _ _ _ _ hCursor]
  exact hAppender

private theorem prefixReject_workStep_none {language : Language}
    (problem : VerifierTableauProblem language) (tape : WorkTape) :
    workStep? (machine problem)
        (renameConfiguration prefixState
          { state := (BuilderBodyStartPrefix.machine problem).rejectState
            tape := tape }) = none := by
  have hFind := findWorkRule_prefixReject_none problem tape.head
  unfold workStep?
  rw [machine_isHalted_prefix_false problem]
  change
    (match findWorkRule (machine problem).rules
        (prefixState (BuilderBodyStartPrefix.machine problem).rejectState)
        tape.head with
     | none => none
     | some rule =>
         some (applyWorkRule rule
           (renameConfiguration prefixState
             { state := (BuilderBodyStartPrefix.machine problem).rejectState
               tape := tape }))) = none
  rw [hFind]

/-- A reject endpoint inside the renamed header component is deliberately
not a global reject; with no outgoing rule it remains timeout for all fuel. -/
theorem prefixRejectEndpoint_timeout {language : Language}
    (problem : VerifierTableauProblem language) (fuel : Nat)
    (tape : WorkTape) :
    (let config := renameConfiguration prefixState
        { state := (BuilderBodyStartPrefix.machine problem).rejectState
          tape := tape }
     let result := workRun (machine problem) fuel config
     if result.state == (machine problem).acceptState then WorkVerdict.accept
     else if result.state == (machine problem).rejectState then
       WorkVerdict.reject
     else WorkVerdict.timeout) = WorkVerdict.timeout := by
  let bad : WorkConfiguration :=
    { state := (BuilderBodyStartPrefix.machine problem).rejectState
      tape := tape }
  exact stuck_timeout problem fuel (renameConfiguration prefixState bad)
    (machine_isHalted_prefix_false problem bad)
    (by simpa [bad] using prefixReject_workStep_none problem tape)

private theorem evaluatorEndpoint_workRunExact {language : Language}
    (problem : VerifierTableauProblem language) :
    workRunExact? (machine problem)
        (BuilderBodyStartPrefix.workSteps problem + 1 +
          BuilderUnaryPolynomial.workSteps
            (nextTokenSlotPolynomial problem.verifier) problem.input)
        (workStartConfiguration (machine problem)
          (rawInputWorkTape problem.input)) =
      some (renameConfiguration evaluatorState
        (BuilderUnaryPolynomial.finalConfiguration
          (nextTokenSlotPolynomial problem.verifier) problem.input
          (BuilderBodyStartPrefix.finalOutside problem)
          (BuilderBodyStartPrefix.bodyStartTokens problem))) := by
  let headerFinal := renameConfiguration prefixState
    (BuilderBodyStartPrefix.finalConfiguration problem)
  let cursorInitial := renameConfiguration evaluatorState
    (BuilderUnaryPolynomial.initialConfiguration
      (nextTokenSlotPolynomial problem.verifier) problem.input
      (BuilderBodyStartPrefix.finalOutside problem)
      (BuilderBodyStartPrefix.bodyStartTokens problem))
  let cursorFinal := renameConfiguration evaluatorState
    (BuilderUnaryPolynomial.finalConfiguration
      (nextTokenSlotPolynomial problem.verifier) problem.input
      (BuilderBodyStartPrefix.finalOutside problem)
      (BuilderBodyStartPrefix.bodyStartTokens problem))
  have hHeader : workRunExact? (machine problem)
      (BuilderBodyStartPrefix.workSteps problem)
      (workStartConfiguration (machine problem)
        (rawInputWorkTape problem.input)) = some headerFinal := by
    simpa [headerFinal] using prefix_workRunExact problem
  have hLaunch : workRunExact? (machine problem) 1 headerFinal =
      some cursorInitial := by
    change
      (match workStep? (machine problem) headerFinal with
       | none => none
       | some next => workRunExact? (machine problem) 0 next) =
        some cursorInitial
    rw [show workStep? (machine problem) headerFinal = some cursorInitial by
      simpa [headerFinal, cursorInitial] using
        prefixEvaluator_launch_workStep problem]
    rfl
  have hCursor : workRunExact? (machine problem)
      (BuilderUnaryPolynomial.workSteps
        (nextTokenSlotPolynomial problem.verifier) problem.input)
      cursorInitial = some cursorFinal := by
    simpa [cursorInitial, cursorFinal] using evaluator_workRunExact problem
  have h01 := PipelineMachineSimulation.workRunExact?_compose
    (machine problem) (BuilderBodyStartPrefix.workSteps problem) 1
    (workStartConfiguration (machine problem)
      (rawInputWorkTape problem.input))
    headerFinal cursorInitial hHeader hLaunch
  have h02 := PipelineMachineSimulation.workRunExact?_compose
    (machine problem) (BuilderBodyStartPrefix.workSteps problem + 1)
    (BuilderUnaryPolynomial.workSteps
      (nextTokenSlotPolynomial problem.verifier) problem.input)
    (workStartConfiguration (machine problem)
      (rawInputWorkTape problem.input))
    cursorInitial cursorFinal h01 hCursor
  simpa [cursorFinal, Nat.add_assoc] using h02

/-- The exact cursor endpoint is still nonhalting until the second new
bridge launches the separator appender. -/
theorem evaluatorEndpoint_before_launch_timeout {language : Language}
    (problem : VerifierTableauProblem language) :
    workBoundedDecide (machine problem)
        (BuilderBodyStartPrefix.workSteps problem + 1 +
          BuilderUnaryPolynomial.workSteps
            (nextTokenSlotPolynomial problem.verifier) problem.input)
        (rawInputWorkTape problem.input) = .timeout := by
  unfold workBoundedDecide
  rw [workRun_eq_of_workRunExact (machine problem)
    (BuilderBodyStartPrefix.workSteps problem + 1 +
      BuilderUnaryPolynomial.workSteps
        (nextTokenSlotPolynomial problem.verifier) problem.input)
    (workStartConfiguration (machine problem)
      (rawInputWorkTape problem.input))
    (renameConfiguration evaluatorState
      (BuilderUnaryPolynomial.finalConfiguration
        (nextTokenSlotPolynomial problem.verifier) problem.input
        (BuilderBodyStartPrefix.finalOutside problem)
        (BuilderBodyStartPrefix.bodyStartTokens problem)))
    (evaluatorEndpoint_workRunExact problem)]
  exact verdict_timeout_of_not_halted problem _
    (machine_isHalted_evaluator_false problem
      (BuilderUnaryPolynomial.finalConfiguration
        (nextTokenSlotPolynomial problem.verifier) problem.input
        (BuilderBodyStartPrefix.finalOutside problem)
        (BuilderBodyStartPrefix.bodyStartTokens problem)))

private theorem workRunExact_one_of_workStep {language : Language}
    (problem : VerifierTableauProblem language)
    (start next : WorkConfiguration)
    (hStep : workStep? (machine problem) start = some next) :
    workRunExact? (machine problem) 1 start = some next := by
  change
    (match workStep? (machine problem) start with
     | none => none
     | some result => workRunExact? (machine problem) 0 result) = some next
  rw [hStep]
  rfl

private theorem tAppenderEndpoint_workRunExact {language : Language}
    (problem : VerifierTableauProblem language) :
    workRunExact? (machine problem)
        (BuilderBodyStartPrefix.workSteps problem + 1 +
          BuilderUnaryPolynomial.workSteps
            (nextTokenSlotPolynomial problem.verifier) problem.input + 1 +
          BuilderTokenAppender.workSteps problem.input
            (BuilderBodyStartPrefix.bodyStartTokens problem))
        (workStartConfiguration (machine problem)
          (rawInputWorkTape problem.input)) =
      some (renameConfiguration tAppenderState
        (BuilderTokenAppender.finalConfiguration problem.input
          (finalOutside problem) (firstLiteralSignTokens problem))) := by
  let start := workStartConfiguration (machine problem)
    (rawInputWorkTape problem.input)
  let prefixFinal := renameConfiguration prefixState
    (BuilderBodyStartPrefix.finalConfiguration problem)
  let evaluatorInitial := renameConfiguration evaluatorState
    (BuilderUnaryPolynomial.initialConfiguration
      (nextTokenSlotPolynomial problem.verifier) problem.input
      (BuilderBodyStartPrefix.finalOutside problem)
      (BuilderBodyStartPrefix.bodyStartTokens problem))
  let evaluatorFinal := renameConfiguration evaluatorState
    (BuilderUnaryPolynomial.finalConfiguration
      (nextTokenSlotPolynomial problem.verifier) problem.input
      (BuilderBodyStartPrefix.finalOutside problem)
      (BuilderBodyStartPrefix.bodyStartTokens problem))
  let tInitial := renameConfiguration tAppenderState
    (BuilderTokenAppender.entryConfiguration .t
      (BuilderTokenAppender.workspaceTape problem.input
        (finalOutside problem)
        (BuilderBodyStartPrefix.bodyStartTokens problem)))
  let tFinal := renameConfiguration tAppenderState
    (BuilderTokenAppender.finalConfiguration problem.input
      (finalOutside problem) (firstLiteralSignTokens problem))
  have hPrefix : workRunExact? (machine problem)
      (BuilderBodyStartPrefix.workSteps problem) start = some prefixFinal := by
    simpa [start, prefixFinal] using prefix_workRunExact problem
  have hLaunchOne : workRunExact? (machine problem) 1 prefixFinal =
      some evaluatorInitial := by
    apply workRunExact_one_of_workStep problem
    simpa [prefixFinal, evaluatorInitial] using
      prefixEvaluator_launch_workStep problem
  have hEvaluator : workRunExact? (machine problem)
      (BuilderUnaryPolynomial.workSteps
        (nextTokenSlotPolynomial problem.verifier) problem.input)
      evaluatorInitial = some evaluatorFinal := by
    simpa [evaluatorInitial, evaluatorFinal] using evaluator_workRunExact problem
  have hLaunchTwo : workRunExact? (machine problem) 1 evaluatorFinal =
      some tInitial := by
    apply workRunExact_one_of_workStep problem
    simpa [evaluatorFinal, tInitial] using evaluatorT_launch_workStep problem
  have hT : workRunExact? (machine problem)
      (BuilderTokenAppender.workSteps problem.input
        (BuilderBodyStartPrefix.bodyStartTokens problem))
      tInitial = some tFinal := by
    simpa [tInitial, tFinal] using tAppender_workRunExact problem
  have h01 := PipelineMachineSimulation.workRunExact?_compose
    (machine problem) (BuilderBodyStartPrefix.workSteps problem) 1
    start prefixFinal evaluatorInitial hPrefix hLaunchOne
  have h02 := PipelineMachineSimulation.workRunExact?_compose
    (machine problem) (BuilderBodyStartPrefix.workSteps problem + 1)
    (BuilderUnaryPolynomial.workSteps
      (nextTokenSlotPolynomial problem.verifier) problem.input)
    start evaluatorInitial evaluatorFinal h01 hEvaluator
  have h03 := PipelineMachineSimulation.workRunExact?_compose
    (machine problem)
    (BuilderBodyStartPrefix.workSteps problem + 1 +
      BuilderUnaryPolynomial.workSteps
        (nextTokenSlotPolynomial problem.verifier) problem.input) 1
    start evaluatorFinal tInitial h02 hLaunchTwo
  have h04 := PipelineMachineSimulation.workRunExact?_compose
    (machine problem)
    (BuilderBodyStartPrefix.workSteps problem + 1 +
      BuilderUnaryPolynomial.workSteps
        (nextTokenSlotPolynomial problem.verifier) problem.input + 1)
    (BuilderTokenAppender.workSteps problem.input
      (BuilderBodyStartPrefix.bodyStartTokens problem))
    start tInitial tFinal h03 hT
  simpa [start, tFinal, Nat.add_assoc] using h04

/-- The successful `T` appender endpoint remains a timeout until the third
bridge launches the final `F` appender. -/
theorem tAppenderEndpoint_before_launch_timeout {language : Language}
    (problem : VerifierTableauProblem language) :
    workBoundedDecide (machine problem)
        (BuilderBodyStartPrefix.workSteps problem + 1 +
          BuilderUnaryPolynomial.workSteps
            (nextTokenSlotPolynomial problem.verifier) problem.input + 1 +
          BuilderTokenAppender.workSteps problem.input
            (BuilderBodyStartPrefix.bodyStartTokens problem))
        (rawInputWorkTape problem.input) = .timeout := by
  unfold workBoundedDecide
  rw [workRun_eq_of_workRunExact (machine problem)
    (BuilderBodyStartPrefix.workSteps problem + 1 +
      BuilderUnaryPolynomial.workSteps
        (nextTokenSlotPolynomial problem.verifier) problem.input + 1 +
      BuilderTokenAppender.workSteps problem.input
        (BuilderBodyStartPrefix.bodyStartTokens problem))
    (workStartConfiguration (machine problem)
      (rawInputWorkTape problem.input))
    (renameConfiguration tAppenderState
      (BuilderTokenAppender.finalConfiguration problem.input
        (finalOutside problem) (firstLiteralSignTokens problem)))
    (tAppenderEndpoint_workRunExact problem)]
  exact verdict_timeout_of_not_halted problem _
    (machine_isHalted_tAppender_false problem
      (BuilderTokenAppender.finalConfiguration problem.input
        (finalOutside problem) (firstLiteralSignTokens problem)))

private theorem findWorkRule_evaluatorDead_none {language : Language}
    (problem : VerifierTableauProblem language) (symbol : WorkSymbol) :
    findWorkRule (machine problem).rules
        (evaluatorState (BuilderUnaryPolynomial.deadState
          (nextTokenSlotPolynomial problem.verifier))) symbol = none := by
  let polynomial := nextTokenSlotPolynomial problem.verifier
  have hBridgeOne : findWorkRule (prefixEvaluatorBridge problem)
      (evaluatorState (BuilderUnaryPolynomial.deadState polynomial)) symbol =
        none := by
    apply findWorkRule_launchRules_none_of_source_ne
    exact prefixState_ne_evaluatorState _ _
  have hBridgeTwo : findWorkRule (evaluatorTBridge problem)
      (evaluatorState (BuilderUnaryPolynomial.deadState polynomial)) symbol =
        none := by
    apply findWorkRule_launchRules_none_of_source_ne
    intro h
    have hLocal := evaluatorState_injective h
    unfold BuilderUnaryPolynomial.deadState at hLocal
    change BuilderUnaryPolynomial.acceptState polynomial =
      BuilderUnaryPolynomial.stateCount polynomial + 2 at hLocal
    unfold BuilderUnaryPolynomial.acceptState at hLocal
    omega
  have hBridges : findWorkRule (bridgeRules problem)
      (evaluatorState (BuilderUnaryPolynomial.deadState polynomial)) symbol =
        none := by
    unfold bridgeRules
    rw [findWorkRule_append_of_none _ _ _ _ hBridgeOne]
    exact hBridgeTwo
  have hHeader : findWorkRule
      ((BuilderBodyStartPrefix.machine problem).rules.map
        (renameRule prefixState))
      (evaluatorState (BuilderUnaryPolynomial.deadState polynomial)) symbol =
        none := by
    apply findWorkRule_renamedRules_none
    intro source
    exact prefixState_ne_evaluatorState _ _
  have hLocal : findWorkRule
      (BuilderUnaryPolynomial.machine polynomial).rules
      (BuilderUnaryPolynomial.deadState polynomial) symbol = none := by
    apply findWorkRule_none_of_sources_ne
    intro rule hMem hEqual
    have hBound := BuilderUnaryPolynomial.rule_source_lt_acceptState
      polynomial rule hMem
    change rule.sourceState < BuilderUnaryPolynomial.stateCount polynomial
      at hBound
    rw [hEqual] at hBound
    unfold BuilderUnaryPolynomial.deadState at hBound
    omega
  have hCursor := findWorkRule_rename evaluatorState evaluatorState_injective
    (BuilderUnaryPolynomial.machine polynomial).rules
    (BuilderUnaryPolynomial.deadState polynomial) symbol
  rw [hLocal] at hCursor
  have hAppender : findWorkRule
      (BuilderTokenAppender.machine.rules.map (renameRule tAppenderState))
      (evaluatorState (BuilderUnaryPolynomial.deadState polynomial)) symbol =
        none := by
    apply findWorkRule_renamedRules_none
    intro source
    exact Ne.symm (evaluatorState_ne_tAppenderState _ source)
  unfold machine rules componentRules
  rw [findWorkRule_append_of_none _ _ _ _ hBridges,
    findWorkRule_append_of_none _ _ _ _ hHeader,
    findWorkRule_append_of_none _ _ _ _ hCursor]
  exact hAppender

private theorem evaluatorDead_workStep_none {language : Language}
    (problem : VerifierTableauProblem language) (tape : WorkTape) :
    workStep? (machine problem)
        (renameConfiguration evaluatorState
          { state := BuilderUnaryPolynomial.deadState
              (nextTokenSlotPolynomial problem.verifier)
            tape := tape }) = none := by
  have hFind := findWorkRule_evaluatorDead_none problem tape.head
  unfold workStep?
  rw [machine_isHalted_evaluator_false problem]
  change
    (match findWorkRule (machine problem).rules
        (evaluatorState (BuilderUnaryPolynomial.deadState
          (nextTokenSlotPolynomial problem.verifier))) tape.head with
     | none => none
     | some rule =>
         some (applyWorkRule rule
           (renameConfiguration evaluatorState
             { state := BuilderUnaryPolynomial.deadState
                 (nextTokenSlotPolynomial problem.verifier)
               tape := tape }))) = none
  rw [hFind]

/-- Every evaluator failure target is isolated from both global halts and
all component tables, so it remains timeout for every fuel budget. -/
theorem evaluatorDeadState_timeout {language : Language}
    (problem : VerifierTableauProblem language) (fuel : Nat)
    (tape : WorkTape) :
    (let config := renameConfiguration evaluatorState
        { state := BuilderUnaryPolynomial.deadState
            (nextTokenSlotPolynomial problem.verifier)
          tape := tape }
     let result := workRun (machine problem) fuel config
     if result.state == (machine problem).acceptState then WorkVerdict.accept
     else if result.state == (machine problem).rejectState then
       WorkVerdict.reject
     else WorkVerdict.timeout) = WorkVerdict.timeout := by
  let bad : WorkConfiguration :=
    { state := BuilderUnaryPolynomial.deadState
        (nextTokenSlotPolynomial problem.verifier)
      tape := tape }
  exact stuck_timeout problem fuel (renameConfiguration evaluatorState bad)
    (machine_isHalted_evaluator_false problem bad)
    (by simpa [bad] using evaluatorDead_workStep_none problem tape)

private theorem findWorkRule_none_of_workStep_none
    (source : WorkMachine) (config : WorkConfiguration)
    (hHalted : source.isHalted config = false)
    (hStep : workStep? source config = none) :
    findWorkRule source.rules config.state config.tape.head = none := by
  unfold workStep? at hStep
  rw [hHalted] at hStep
  cases hFind : findWorkRule source.rules config.state config.tape.head with
  | none => rfl
  | some rule =>
      rw [hFind] at hStep
      contradiction

private theorem findWorkRule_tAppender_of_none {language : Language}
    (problem : VerifierTableauProblem language)
    (state : Nat) (symbol : WorkSymbol)
    (hAccept : state ≠ BuilderTokenAppender.machine.acceptState)
    (hFind : findWorkRule BuilderTokenAppender.machine.rules state symbol =
      none) :
    findWorkRule (machine problem).rules (tAppenderState state) symbol =
      none := by
  have hBridgeOne : findWorkRule (prefixEvaluatorBridge problem)
      (tAppenderState state) symbol = none := by
    apply findWorkRule_launchRules_none_of_source_ne
    exact prefixState_ne_tAppenderState _ _
  have hBridgeTwo : findWorkRule (evaluatorTBridge problem)
      (tAppenderState state) symbol = none := by
    apply findWorkRule_launchRules_none_of_source_ne
    exact evaluatorState_ne_tAppenderState _ _
  have hBridgeThree : findWorkRule (tFBridge problem)
      (tAppenderState state) symbol = none := by
    apply findWorkRule_launchRules_none_of_source_ne
    intro h
    exact hAccept (tAppenderState_injective h).symm
  have hBridges : findWorkRule (bridgeRules problem)
      (tAppenderState state) symbol = none := by
    unfold bridgeRules
    rw [findWorkRule_append_of_none _ _ _ _ hBridgeOne]
    rw [findWorkRule_append_of_none _ _ _ _ hBridgeTwo]
    exact hBridgeThree
  have hHeader : findWorkRule
      ((BuilderBodyStartPrefix.machine problem).rules.map
        (renameRule prefixState)) (tAppenderState state) symbol = none := by
    apply findWorkRule_renamedRules_none
    intro source
    exact prefixState_ne_tAppenderState _ _
  have hCursor : findWorkRule
      ((BuilderUnaryPolynomial.machine
        (nextTokenSlotPolynomial problem.verifier)).rules.map
          (renameRule evaluatorState))
      (tAppenderState state) symbol = none := by
    apply findWorkRule_renamedRules_none
    intro source
    exact evaluatorState_ne_tAppenderState _ _
  have hRenamed := findWorkRule_rename tAppenderState tAppenderState_injective
    BuilderTokenAppender.machine.rules state symbol
  rw [hFind] at hRenamed
  have hF : findWorkRule
      (BuilderTokenAppender.machine.rules.map (renameRule fAppenderState))
      (tAppenderState state) symbol = none := by
    apply findWorkRule_renamedRules_none
    intro source
    exact Ne.symm (tAppenderState_ne_fAppenderState state source)
  unfold machine rules componentRules
  rw [findWorkRule_append_of_none _ _ _ _ hBridges,
    findWorkRule_append_of_none _ _ _ _ hHeader,
    findWorkRule_append_of_none _ _ _ _ hCursor]
  rw [findWorkRule_append_of_none _ _ _ _ hRenamed]
  exact hF

private theorem tAppender_workStep_none_of_local {language : Language}
    (problem : VerifierTableauProblem language)
    (config : WorkConfiguration)
    (hLocalHalted : BuilderTokenAppender.machine.isHalted config = false)
    (hLocalStep : workStep? BuilderTokenAppender.machine config = none) :
    workStep? (machine problem) (renameConfiguration tAppenderState config) =
      none := by
  have hFind := findWorkRule_none_of_workStep_none
    BuilderTokenAppender.machine config hLocalHalted hLocalStep
  have hAccept := state_ne_accept_of_not_halted
    BuilderTokenAppender.machine config hLocalHalted
  have hGlobalFind := findWorkRule_tAppender_of_none problem
    config.state config.tape.head hAccept hFind
  unfold workStep?
  rw [machine_isHalted_tAppender_false problem config]
  change
    (match findWorkRule (machine problem).rules
        (tAppenderState config.state) config.tape.head with
     | none => none
     | some rule =>
         some (applyWorkRule rule
           (renameConfiguration tAppenderState config))) = none
  rw [hGlobalFind]

/-- An invalid tally-phase symbol in the separator appender cannot fall
through to a global accept or reject endpoint. -/
theorem malformedAppenderTally_timeout {language : Language}
    (problem : VerifierTableauProblem language) (fuel : Nat)
    (request : CNFToken) (left right : List WorkSymbol) :
    (let config := renameConfiguration tAppenderState
        (BuilderTokenAppender.malformedTallyConfiguration
          request left right)
     let result := workRun (machine problem) fuel config
     if result.state == (machine problem).acceptState then WorkVerdict.accept
     else if result.state == (machine problem).rejectState then
       WorkVerdict.reject
     else WorkVerdict.timeout) = WorkVerdict.timeout := by
  let bad := BuilderTokenAppender.malformedTallyConfiguration
    request left right
  have hLocalHalted :=
    BuilderTokenAppender.malformedTallySymbol_isHalted_false
      request left right
  have hLocalStep := BuilderTokenAppender.malformedTallySymbol_workStep_none
    request left right
  have hStep := tAppender_workStep_none_of_local problem bad
    hLocalHalted hLocalStep
  exact stuck_timeout problem fuel (renameConfiguration tAppenderState bad)
    (machine_isHalted_tAppender_false problem bad) hStep

/-- An invalid output-phase symbol in the separator appender likewise
remains timeout. -/
theorem malformedAppenderOutput_timeout {language : Language}
    (problem : VerifierTableauProblem language) (fuel : Nat)
    (request : CNFToken) (left right : List WorkSymbol) :
    (let config := renameConfiguration tAppenderState
        (BuilderTokenAppender.malformedOutputConfiguration
          request left right)
     let result := workRun (machine problem) fuel config
     if result.state == (machine problem).acceptState then WorkVerdict.accept
     else if result.state == (machine problem).rejectState then
       WorkVerdict.reject
     else WorkVerdict.timeout) = WorkVerdict.timeout := by
  let bad := BuilderTokenAppender.malformedOutputConfiguration
    request left right
  have hLocalHalted :=
    BuilderTokenAppender.malformedOutputSymbol_isHalted_false
      request left right
  have hLocalStep := BuilderTokenAppender.malformedOutputSymbol_workStep_none
    request left right
  have hStep := tAppender_workStep_none_of_local problem bad
    hLocalHalted hLocalStep
  exact stuck_timeout problem fuel (renameConfiguration tAppenderState bad)
    (machine_isHalted_tAppender_false problem bad) hStep

private theorem findWorkRule_fAppender_of_none {language : Language}
    (problem : VerifierTableauProblem language)
    (state : Nat) (symbol : WorkSymbol)
    (hFind : findWorkRule BuilderTokenAppender.machine.rules state symbol =
      none) :
    findWorkRule (machine problem).rules (fAppenderState state) symbol =
      none := by
  have hBridgeOne : findWorkRule (prefixEvaluatorBridge problem)
      (fAppenderState state) symbol = none := by
    apply findWorkRule_launchRules_none_of_source_ne
    exact prefixState_ne_fAppenderState _ _
  have hBridgeTwo : findWorkRule (evaluatorTBridge problem)
      (fAppenderState state) symbol = none := by
    apply findWorkRule_launchRules_none_of_source_ne
    exact evaluatorState_ne_fAppenderState _ _
  have hBridgeThree : findWorkRule (tFBridge problem)
      (fAppenderState state) symbol = none := by
    apply findWorkRule_launchRules_none_of_source_ne
    exact tAppenderState_ne_fAppenderState _ _
  have hBridges : findWorkRule (bridgeRules problem)
      (fAppenderState state) symbol = none := by
    unfold bridgeRules
    rw [findWorkRule_append_of_none _ _ _ _ hBridgeOne]
    rw [findWorkRule_append_of_none _ _ _ _ hBridgeTwo]
    exact hBridgeThree
  have hPrefix : findWorkRule
      ((BuilderBodyStartPrefix.machine problem).rules.map
        (renameRule prefixState)) (fAppenderState state) symbol = none := by
    apply findWorkRule_renamedRules_none
    intro source
    exact prefixState_ne_fAppenderState _ _
  have hEvaluator : findWorkRule
      ((BuilderUnaryPolynomial.machine
        (nextTokenSlotPolynomial problem.verifier)).rules.map
          (renameRule evaluatorState))
      (fAppenderState state) symbol = none := by
    apply findWorkRule_renamedRules_none
    intro source
    exact evaluatorState_ne_fAppenderState _ _
  have hT : findWorkRule
      (BuilderTokenAppender.machine.rules.map (renameRule tAppenderState))
      (fAppenderState state) symbol = none := by
    apply findWorkRule_renamedRules_none
    intro source
    exact tAppenderState_ne_fAppenderState _ _
  have hRenamed := findWorkRule_rename fAppenderState fAppenderState_injective
    BuilderTokenAppender.machine.rules state symbol
  rw [hFind] at hRenamed
  unfold machine rules componentRules
  rw [findWorkRule_append_of_none _ _ _ _ hBridges,
    findWorkRule_append_of_none _ _ _ _ hPrefix,
    findWorkRule_append_of_none _ _ _ _ hEvaluator,
    findWorkRule_append_of_none _ _ _ _ hT]
  exact hRenamed

private theorem fAppender_workStep_none_of_local {language : Language}
    (problem : VerifierTableauProblem language)
    (config : WorkConfiguration)
    (hLocalHalted : BuilderTokenAppender.machine.isHalted config = false)
    (hLocalStep : workStep? BuilderTokenAppender.machine config = none) :
    workStep? (machine problem) (renameConfiguration fAppenderState config) =
      none := by
  have hFind := findWorkRule_none_of_workStep_none
    BuilderTokenAppender.machine config hLocalHalted hLocalStep
  have hGlobalFind := findWorkRule_fAppender_of_none problem
    config.state config.tape.head hFind
  unfold workStep?
  rw [machine_isHalted_fAppender_false_of_local problem config hLocalHalted]
  change
    (match findWorkRule (machine problem).rules
        (fAppenderState config.state) config.tape.head with
     | none => none
     | some rule =>
         some (applyWorkRule rule
           (renameConfiguration fAppenderState config))) = none
  rw [hGlobalFind]

/-- A malformed tally symbol in the final `F` appender is isolated from the
global halts and remains timeout for every fuel budget. -/
theorem malformedFAppenderTally_timeout {language : Language}
    (problem : VerifierTableauProblem language) (fuel : Nat)
    (request : CNFToken) (left right : List WorkSymbol) :
    (let config := renameConfiguration fAppenderState
        (BuilderTokenAppender.malformedTallyConfiguration
          request left right)
     let result := workRun (machine problem) fuel config
     if result.state == (machine problem).acceptState then WorkVerdict.accept
     else if result.state == (machine problem).rejectState then
       WorkVerdict.reject
     else WorkVerdict.timeout) = WorkVerdict.timeout := by
  let bad := BuilderTokenAppender.malformedTallyConfiguration
    request left right
  have hLocalHalted :=
    BuilderTokenAppender.malformedTallySymbol_isHalted_false
      request left right
  have hLocalStep := BuilderTokenAppender.malformedTallySymbol_workStep_none
    request left right
  have hStep := fAppender_workStep_none_of_local problem bad
    hLocalHalted hLocalStep
  exact stuck_timeout problem fuel (renameConfiguration fAppenderState bad)
    (machine_isHalted_fAppender_false_of_local problem bad hLocalHalted) hStep

/-- A malformed output symbol in the final `F` appender likewise remains a
timeout instead of reaching the global accept or reject state. -/
theorem malformedFAppenderOutput_timeout {language : Language}
    (problem : VerifierTableauProblem language) (fuel : Nat)
    (request : CNFToken) (left right : List WorkSymbol) :
    (let config := renameConfiguration fAppenderState
        (BuilderTokenAppender.malformedOutputConfiguration
          request left right)
     let result := workRun (machine problem) fuel config
     if result.state == (machine problem).acceptState then WorkVerdict.accept
     else if result.state == (machine problem).rejectState then
       WorkVerdict.reject
     else WorkVerdict.timeout) = WorkVerdict.timeout := by
  let bad := BuilderTokenAppender.malformedOutputConfiguration
    request left right
  have hLocalHalted :=
    BuilderTokenAppender.malformedOutputSymbol_isHalted_false
      request left right
  have hLocalStep := BuilderTokenAppender.malformedOutputSymbol_workStep_none
    request left right
  have hStep := fAppender_workStep_none_of_local problem bad
    hLocalHalted hLocalStep
  exact stuck_timeout problem fuel (renameConfiguration fAppenderState bad)
    (machine_isHalted_fAppender_false_of_local problem bad hLocalHalted) hStep

private theorem workRunExact_succ_split_last {language : Language}
    (problem : VerifierTableauProblem language) :
    ∀ (steps : Nat) (initial final : WorkConfiguration),
      workRunExact? (machine problem) (steps + 1) initial = some final →
      ∃ before,
        workRunExact? (machine problem) steps initial = some before ∧
        workStep? (machine problem) before = some final := by
  intro steps
  induction steps with
  | zero =>
      intro initial final hRun
      cases hStep : workStep? (machine problem) initial with
      | none =>
          change
            (match workStep? (machine problem) initial with
             | none => none
             | some next => some next) = some final at hRun
          rw [hStep] at hRun
          contradiction
      | some next =>
          have hNext : next = final := by
            change
              (match workStep? (machine problem) initial with
               | none => none
               | some result => some result) = some final at hRun
            rw [hStep] at hRun
            exact Option.some.inj hRun
          subst final
          exact ⟨initial, rfl, hStep⟩
  | succ steps ih =>
      intro initial final hRun
      cases hStep : workStep? (machine problem) initial with
      | none =>
          change
            (match workStep? (machine problem) initial with
             | none => none
             | some next =>
                 workRunExact? (machine problem) (steps + 1) next) =
              some final at hRun
          rw [hStep] at hRun
          contradiction
      | some next =>
          have hTail : workRunExact? (machine problem) (steps + 1) next =
              some final := by
            change
              (match workStep? (machine problem) initial with
               | none => none
               | some result =>
                   workRunExact? (machine problem) (steps + 1) result) =
                some final at hRun
            rw [hStep] at hRun
            exact hRun
          rcases ih next final hTail with ⟨before, hPrefix, hLast⟩
          refine ⟨before, ?_, hLast⟩
          change
            (match workStep? (machine problem) initial with
             | none => none
             | some result =>
                 workRunExact? (machine problem) steps result) = some before
          rw [hStep]
          exact hPrefix

private theorem isHalted_false_of_workStep_some {language : Language}
    (problem : VerifierTableauProblem language)
    (config next : WorkConfiguration)
    (hStep : workStep? (machine problem) config = some next) :
    (machine problem).isHalted config = false := by
  cases hHalted : (machine problem).isHalted config with
  | false => rfl
  | true =>
      unfold workStep? at hStep
      rw [hHalted] at hStep
      contradiction

private theorem workSteps_positive {language : Language}
    (problem : VerifierTableauProblem language) : 0 < workSteps problem := by
  unfold workSteps
  omega

/-- Removing the final successful transition leaves a nonhalting state, so
the exact all-input trace cannot accept one work step early. -/
theorem work_one_step_short_timeout {language : Language}
    (problem : VerifierTableauProblem language) :
    workBoundedDecide (machine problem) (workSteps problem - 1)
        (rawInputWorkTape problem.input) = .timeout := by
  let short := workSteps problem - 1
  let initial := workStartConfiguration (machine problem)
    (rawInputWorkTape problem.input)
  let final := finalConfiguration problem
  have hSucc : short + 1 = workSteps problem := by
    dsimp [short]
    have hPositive := workSteps_positive problem
    omega
  have hExact := workRunExact problem
  change workRunExact? (machine problem) (workSteps problem) initial =
    some final at hExact
  rw [← hSucc] at hExact
  rcases workRunExact_succ_split_last problem short initial final hExact with
    ⟨before, hPrefix, hLast⟩
  have hRun : workRun (machine problem) short initial = before :=
    workRun_eq_of_workRunExact (machine problem) short initial before hPrefix
  have hNotHalted := isHalted_false_of_workStep_some
    problem before final hLast
  unfold workBoundedDecide
  change
    (let result := workRun (machine problem) short initial
     if result.state == (machine problem).acceptState then WorkVerdict.accept
     else if result.state == (machine problem).rejectState then
       WorkVerdict.reject
     else WorkVerdict.timeout) = WorkVerdict.timeout
  rw [hRun]
  exact verdict_timeout_of_not_halted problem before hNotHalted

end BuilderFirstLiteralPrefix

end CookLevin

end PNP.Concrete
