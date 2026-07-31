/-
Copyright (c) 2026 PNP Labs.

The bounded workspace boundary for the physical CNF-to-NAND compiler.

The executable prefix in this module is assembled only from literal work
machines.  A carrier encoder first rewrites canonical packed CNF tokens as a
strict-v0 raw-circuit carrier.  The existing strict-v0 grammar scanner then
checks that carrier, and the existing source-driven ledger machine reserves
the fixed six-slot controller workspace.

There are deliberately two register records below.  `postLedgerRegisters` is
the exact physical endpoint produced by this prefix.  `workspaceRegisters` is
the contract for the following carrier-traversal controller: that later
machine must replace the carrier input-count and current-gate slots by the CNF
width and exact compiler gate count.  Keeping the records distinct prevents
this module from claiming that those deferred writes have already occurred.
-/

import PNP.Concrete.CNFToNANDCarrierEncoder
import PNP.Concrete.CNFToNANDEmitterPlan
import PNP.Concrete.CookLevinFormulaSize
import PNP.Concrete.LockedNANDTargetEmitterLedger
import PNP.Concrete.WorkMachineChain

namespace PNP.Concrete.CNFToNANDWorkspace

open PNP.Concrete
open PNP.Concrete.LockedNAND

/-! ## Carrier-derived physical ledger endpoint -/

/-- The canonical two-bit token word retained by the physical carrier. -/
def formulaTokens (formula : CNFFormula) : List CNFToken :=
  encodeFormulaTokens formula

theorem formulaTokens_ne_nil (formula : CNFFormula) :
    formulaTokens formula ≠ [] := by
  unfold formulaTokens encodeFormulaTokens encodeCNFTokens
  cases formula.variableCount <;> simp [encodeUnaryTokens]

/-- The strict-v0 carrier whose inert gates record the canonical CNF tokens. -/
def carrierCircuit (formula : CNFFormula) : RawCircuit :=
  CNFToNANDCarrierEncoder.Source.carrierCircuit
    (formulaTokens formula)

/-- Fixed capacity selected by the existing source-driven ledger. -/
def capacity (formula : CNFFormula) : Nat :=
  TargetEmitterLedger.slotCapacity (carrierCircuit formula)

/-- The exact register record physically produced by the ledger prefix. -/
def postLedgerRegisters (formula : CNFFormula) :
    TargetEmitter.UnaryRegisters :=
  TargetEmitterLedger.ledgerRegisters (carrierCircuit formula)

/-- The exact six-slot word physically produced by the ledger prefix. -/
def postLedgerWord (formula : CNFFormula) : List WorkSymbol :=
  TargetEmitterLedger.ledgerWord
    (capacity formula) (postLedgerRegisters formula)

theorem carrierCircuit_inputCount (formula : CNFFormula) :
    (carrierCircuit formula).inputCount = 0 := by
  exact
    CNFToNANDCarrierEncoder.Source.carrierCircuit_inputCount
      (formulaTokens formula)

theorem carrierCircuit_gates_length (formula : CNFFormula) :
    (carrierCircuit formula).gates.length =
      (formulaTokens formula).length := by
  exact
    CNFToNANDCarrierEncoder.Source.carrierCircuit_gates_length
      (formulaTokens formula)

theorem carrierCircuit_output (formula : CNFFormula) :
    (carrierCircuit formula).output = .constant false := by
  exact
    CNFToNANDCarrierEncoder.Source.carrierCircuit_output
      (formulaTokens formula)

theorem carrierCircuit_cells_length (formula : CNFFormula) :
    (LockedNAND.SourceParser.circuitCells
      (carrierCircuit formula)).length =
        8 * (formulaTokens formula).length + 14 := by
  exact
    CNFToNANDCarrierEncoder.Source.carrierCircuit_cells_length
      (formulaTokens formula)

theorem capacity_exact (formula : CNFFormula) :
    capacity formula =
      64 * (8 * (formulaTokens formula).length + 14) + 64 := by
  unfold capacity TargetEmitterLedger.slotCapacity
  rw [carrierCircuit_cells_length]

theorem postLedgerRegisters_inputCount (formula : CNFFormula) :
    (postLedgerRegisters formula).inputCount = 0 := by
  simp [postLedgerRegisters, TargetEmitterLedger.ledgerRegisters,
    carrierCircuit_inputCount]

theorem postLedgerRegisters_normalizedGateCount
    (formula : CNFFormula) :
    (postLedgerRegisters formula).normalizedGateCount =
      (formulaTokens formula).length + 1 := by
  simp [postLedgerRegisters, TargetEmitterLedger.ledgerRegisters,
    TargetEmitterLedger.normalizedGateCount,
    TargetEmitterLedger.normalizationAddedGates,
    carrierCircuit_gates_length, carrierCircuit_output]

theorem postLedgerRegisters_carrierWidth
    (formula : CNFFormula) :
    (postLedgerRegisters formula).carrierWidth =
      6 * ((formulaTokens formula).length + 1) + 1 := by
  simp [postLedgerRegisters, TargetEmitterLedger.ledgerRegisters,
    TargetEmitterLedger.carrierWidthValue,
    TargetEmitterLedger.normalizedGateCount,
    TargetEmitterLedger.normalizationAddedGates,
    carrierCircuit_inputCount, carrierCircuit_gates_length,
    carrierCircuit_output]

theorem postLedgerRegisters_currentGate (formula : CNFFormula) :
    (postLedgerRegisters formula).currentGate = 0 := by
  rfl

theorem postLedgerRegisters_outputIndex (formula : CNFFormula) :
    (postLedgerRegisters formula).outputIndex = 0 := by
  rfl

theorem postLedgerShape (formula : CNFFormula) :
    TargetEmitterLedger.LedgerShape
      (capacity formula) (postLedgerRegisters formula)
      (postLedgerWord formula) := by
  exact TargetEmitterLedger.ledgerShape (carrierCircuit formula)

/-! ## Contract for the following carrier traversal

The values below are descriptive specifications.  The physical prefix above
has not yet written the two changed fields.  The next literal controller will
recover tokens from the carrier gates and establish this record physically.
-/

/-- Exact number of gates emitted by the semantic postfix compiler. -/
def compilerGateCount (formula : CNFFormula) : Nat :=
  (CNFToNAND.compileFormula formula).gates.length

/-- Register contract required by the subsequent physical postfix emitter. -/
def workspaceRegisters (formula : CNFFormula) :
    TargetEmitter.UnaryRegisters :=
  { postLedgerRegisters formula with
    inputCount := formula.variableCount
    currentGate := compilerGateCount formula
    outputIndex := 0 }

/-- Desired six-slot word after the deferred carrier traversal has populated
the compiler coordinates.  This is not the endpoint of this module's physical
prefix. -/
def workspaceWord (formula : CNFFormula) : List WorkSymbol :=
  TargetEmitterLedger.ledgerWord
    (capacity formula) (workspaceRegisters formula)

theorem workspaceRegisters_inputCount (formula : CNFFormula) :
    (workspaceRegisters formula).inputCount =
      formula.variableCount := by
  rfl

theorem workspaceRegisters_normalizedGateCount
    (formula : CNFFormula) :
    (workspaceRegisters formula).normalizedGateCount =
      (formulaTokens formula).length + 1 := by
  exact postLedgerRegisters_normalizedGateCount formula

theorem workspaceRegisters_carrierWidth (formula : CNFFormula) :
    (workspaceRegisters formula).carrierWidth =
      6 * ((formulaTokens formula).length + 1) + 1 := by
  exact postLedgerRegisters_carrierWidth formula

theorem workspaceRegisters_baseline (formula : CNFFormula) :
    (workspaceRegisters formula).baseline =
      (postLedgerRegisters formula).baseline := by
  rfl

theorem workspaceRegisters_currentGate (formula : CNFFormula) :
    (workspaceRegisters formula).currentGate =
      compilerGateCount formula := by
  rfl

theorem workspaceRegisters_outputIndex (formula : CNFFormula) :
    (workspaceRegisters formula).outputIndex = 0 := by
  rfl

/-- Unique delimiter used by the later formula-coordinate stack.  This value
is already present at the physical post-ledger endpoint and is retained by
`workspaceRegisters`. -/
def formulaStackMarker (formula : CNFFormula) : Nat :=
  (postLedgerRegisters formula).carrierWidth

theorem formulaStackMarker_exact (formula : CNFFormula) :
    formulaStackMarker formula =
      6 * ((formulaTokens formula).length + 1) + 1 := by
  exact postLedgerRegisters_carrierWidth formula

theorem workspaceRegisters_carrierWidth_eq_formulaStackMarker
    (formula : CNFFormula) :
    (workspaceRegisters formula).carrierWidth =
      formulaStackMarker formula := by
  rfl

/-! ## Capacity for the later compiler and its LIFO sentinel -/

private theorem compilerGateCount_le_formulaPlan
    (formula : CNFFormula) :
    compilerGateCount formula ≤
      (CNFToNAND.formulaPlan formula).length := by
  unfold compilerGateCount
  rw [CNFToNAND.compileFormula_gateCount_exact,
    CNFToNAND.formulaPlan_length_exact]
  split <;> omega

theorem canonicalEncodedBits_length (formula : CNFFormula) :
    (encodeCNF formula).length =
      2 * (formulaTokens formula).length + 1 := by
  simp [encodeCNF, formulaTokens, encodeFormulaTokens,
    encodeTokenPairs_length]

/-- A direct token-linear bound on the exact compiler gate count. -/
theorem compilerGateCount_le_tokenBound (formula : CNFFormula) :
    compilerGateCount formula ≤
      10 * (formulaTokens formula).length + 6 := by
  have planBound :=
    CNFToNAND.formulaPlan_length_le_encoded_bits
      (encodeCNF formula) formula (decodeEncodedCNF_canonical formula)
  have gateBound := compilerGateCount_le_formulaPlan formula
  rw [canonicalEncodedBits_length] at planBound
  omega

private theorem literalTokenMass_le
    (clause : List CNFLiteral) :
    2 * clause.length ≤
      (clause.map CookLevin.literalTokenCost).sum := by
  induction clause with
  | nil =>
      exact Nat.le_refl 0
  | cons literal rest ih =>
      simp only [List.length_cons, List.map_cons, List.sum_cons,
        CookLevin.literalTokenCost] at ih ⊢
      omega

private theorem clauseTokenMass_le
    (clauses : List (List CNFLiteral)) :
    2 * (clauses.map List.length).sum +
        2 * clauses.length ≤
      CookLevin.clauseListTokenCost clauses := by
  induction clauses with
  | nil =>
      exact Nat.le_refl 0
  | cons clause rest ih =>
      have clauseBound := literalTokenMass_le clause
      simp only [CookLevin.clauseListTokenCost,
        CookLevin.clauseTokenCost, List.map_cons, List.sum_cons,
        List.length_cons] at ih ⊢
      omega

private theorem formulaMass_le_formulaTokens_length
    (formula : CNFFormula) :
    2 * CNFToNAND.literalCount formula +
        2 * formula.clauses.length ≤
      (formulaTokens formula).length := by
  have clauseBound := clauseTokenMass_le formula.clauses
  rw [formulaTokens, encodeFormulaTokens,
    CookLevin.encodeCNFTokens_length]
  unfold CNFToNAND.literalCount
  omega

/-- The carrier-width register is a delimiter unavailable to every real
compiler gate coordinate.  The later controller can therefore use it as the
unique formula-stack marker without manufacturing another comparison bound. -/
theorem compilerGateCount_lt_carrierWidth
    (formula : CNFFormula) :
    compilerGateCount formula <
      (postLedgerRegisters formula).carrierWidth := by
  have gateBound := CNFToNAND.compileFormula_gateCount_le formula
  have tokenMass := formulaMass_le_formulaTokens_length formula
  rw [postLedgerRegisters_carrierWidth]
  unfold compilerGateCount at gateBound ⊢
  omega

theorem compilerGateCount_lt_formulaStackMarker
    (formula : CNFFormula) :
    compilerGateCount formula < formulaStackMarker formula :=
  compilerGateCount_lt_carrierWidth formula

theorem compilerGateCount_lt_workspaceCarrierWidth
    (formula : CNFFormula) :
    compilerGateCount formula <
      (workspaceRegisters formula).carrierWidth := by
  change compilerGateCount formula <
    (postLedgerRegisters formula).carrierWidth
  exact compilerGateCount_lt_carrierWidth formula

theorem formulaStackMarker_le_capacity (formula : CNFFormula) :
    formulaStackMarker formula ≤ capacity formula := by
  exact (postLedgerShape formula).carrierWidthBound

private theorem variableCount_le_formulaTokens_length
    (formula : CNFFormula) :
    formula.variableCount ≤ (formulaTokens formula).length := by
  rw [formulaTokens, encodeFormulaTokens,
    CookLevin.encodeCNFTokens_length]
  omega

theorem variableCount_le_capacity (formula : CNFFormula) :
    formula.variableCount ≤ capacity formula := by
  have widthBound := variableCount_le_formulaTokens_length formula
  rw [capacity_exact]
  omega

/-- The exact gate-count sentinel and one following stack cell both fit in
the source-derived fixed capacity. -/
theorem compilerGateCount_add_two_le_capacity
    (formula : CNFFormula) :
    compilerGateCount formula + 2 ≤ capacity formula := by
  have gateBound := compilerGateCount_le_tokenBound formula
  rw [capacity_exact]
  omega

theorem compilerGateCount_lt_capacity (formula : CNFFormula) :
    compilerGateCount formula < capacity formula := by
  have bounded := compilerGateCount_add_two_le_capacity formula
  omega

theorem compilerGateCount_succ_lt_capacity
    (formula : CNFFormula) :
    compilerGateCount formula + 1 < capacity formula := by
  have bounded := compilerGateCount_add_two_le_capacity formula
  omega

theorem realGateCoordinate_lt_sentinel
    (formula : CNFFormula) (coordinate : Nat)
    (bounded : coordinate < compilerGateCount formula) :
    coordinate <
      (workspaceRegisters formula).currentGate := by
  simpa [workspaceRegisters_currentGate] using bounded

theorem realGateCoordinate_lt_formulaStackMarker
    (formula : CNFFormula) (coordinate : Nat)
    (bounded : coordinate < compilerGateCount formula) :
    coordinate < formulaStackMarker formula := by
  exact Nat.lt_trans bounded
    (compilerGateCount_lt_formulaStackMarker formula)

theorem realGateCoordinate_succ_lt_capacity
    (formula : CNFFormula) (coordinate : Nat)
    (bounded : coordinate < compilerGateCount formula) :
    coordinate + 1 < capacity formula := by
  have sentinelBound := compilerGateCount_lt_capacity formula
  omega

/-- The desired later-controller record is representable in the already
reserved physical slot bank. -/
theorem workspaceShape (formula : CNFFormula) :
    TargetEmitterLedger.LedgerShape
      (capacity formula) (workspaceRegisters formula)
      (workspaceWord formula) := by
  have physical := postLedgerShape formula
  refine
    { inputBound := variableCount_le_capacity formula
      normalizedGateBound := physical.normalizedGateBound
      carrierWidthBound := physical.carrierWidthBound
      baselineBound := physical.baselineBound
      currentGateBound := Nat.le_of_lt
        (compilerGateCount_lt_capacity formula)
      outputIndexBound := by
        simp [workspaceRegisters, capacity]
      exact := rfl }

/-! ## Exact physical post-ledger source retention -/

/-- The exact physical endpoint before the deferred register-population pass. -/
def postLedgerConfiguration (formula : CNFFormula) :
    WorkConfiguration :=
  TargetEmitterLedger.finalConfiguration (carrierCircuit formula)

theorem postLedgerConfiguration_left (formula : CNFFormula) :
    (postLedgerConfiguration formula).tape.left =
      TargetEmitterLedger.ledgerLeftWorkspace
        (capacity formula) (postLedgerRegisters formula)
        [TargetEmitterLedger.cellBlank] := by
  exact TargetEmitterLedger.finalConfiguration_left
    (carrierCircuit formula)

theorem postLedgerConfiguration_source_and_blank_target
    (formula : CNFFormula) :
    let cells :=
      LockedNAND.SourceParser.circuitCells (carrierCircuit formula)
    match cells with
    | [] =>
        (postLedgerConfiguration formula).tape.head =
            TargetEmitterLedger.cellBlank ∧
          (postLedgerConfiguration formula).tape.right =
            [TargetEmitterLedger.sourceTargetBoundary,
             TargetEmitterLedger.cellBlank,
             TargetEmitterLedger.cellBlank,
             TargetEmitterLedger.cellBlank]
    | first :: rest =>
        (postLedgerConfiguration formula).tape.head = first ∧
          (postLedgerConfiguration formula).tape.right =
            rest ++
              [TargetEmitterLedger.sourceTargetBoundary,
               TargetEmitterLedger.cellBlank,
               TargetEmitterLedger.cellBlank,
               TargetEmitterLedger.cellBlank] := by
  exact
    TargetEmitterLedger.finalConfiguration_source_and_blank_target
      (carrierCircuit formula)


/-! ## Literal physical prefix

The raw-input framer launches the fixed carrier graph.  The carrier is then
followed by a nested chain of the already-audited strict-v0 grammar scanner
and source ledger.  `WorkMachineChain` contributes one total nine-symbol
bridge at each boundary and injectively renames every local state.
-/

/-- Strict-v0 grammar validation followed by exact six-slot reservation. -/
def scannerLedgerMachine : WorkMachine :=
  WorkMachineChain.machine
    TargetEmitterGrammarScanner.machine
    TargetEmitterLedger.machine

/-- Raw canonical CNF framing, carrier construction, validation, and ledger
reservation.  No definition in this executable performs a semantic decode. -/
def machine : WorkMachine :=
  WorkMachineChain.machine
    CNFToNANDCarrierEncoder.machine scannerLedgerMachine

def compiledMachine : Machine :=
  compileWorkMachine machine

private theorem noRuleAt_of_find_none
    (localRules : List WorkRule) (state : Nat)
    (missing :
      ∀ symbol, findWorkRule localRules state symbol = none) :
    ∀ rule, rule ∈ localRules → rule.sourceState ≠ state := by
  induction localRules with
  | nil =>
      intro rule member
      contradiction
  | cons first rest inductionHypothesis =>
      intro rule member sourceEquality
      cases member with
      | head =>
          have found := findWorkRule_cons_of_matches
            first rest state first.readSymbol
            ⟨sourceEquality, rfl⟩
          rw [missing first.readSymbol] at found
          contradiction
      | tail _ restMember =>
          have restMissing :
              ∀ symbol,
                findWorkRule rest state symbol = none := by
            intro symbol
            by_cases queryMatches :
                first.sourceState = state ∧
                  first.readSymbol = symbol
            · have found := findWorkRule_cons_of_matches
                first rest state symbol queryMatches
              rw [missing symbol] at found
              contradiction
            · rw [← findWorkRule_cons_of_not_matches
                  first rest state symbol queryMatches]
              exact missing symbol
          exact inductionHypothesis restMissing
            rule restMember sourceEquality

private theorem carrierNoRuleAtAccept :
    WorkMachineChain.NoRuleAtAccept
      CNFToNANDCarrierEncoder.machine :=
  noRuleAt_of_find_none _ _
    CNFToNANDCarrierEncoder.no_rule_at_accept

private theorem scannerNoRuleAtAccept :
    WorkMachineChain.NoRuleAtAccept
      TargetEmitterGrammarScanner.machine :=
  noRuleAt_of_find_none _ _
    TargetEmitterGrammarScanner.no_rule_at_accept

private theorem ledgerNoRuleAtAccept :
    WorkMachineChain.NoRuleAtAccept
      TargetEmitterLedger.machine :=
  noRuleAt_of_find_none _ _
    TargetEmitterLedger.no_rule_at_accept

private theorem scannerLedgerNoRuleAtAccept :
    WorkMachineChain.NoRuleAtAccept scannerLedgerMachine := by
  exact WorkMachineChain.noRuleAtAccept
    TargetEmitterGrammarScanner.machine TargetEmitterLedger.machine
    ledgerNoRuleAtAccept

theorem scannerLedger_rules_length :
    scannerLedgerMachine.rules.length = 21105 := by
  have hLaunch : ∀ source target,
      (PipelineStageBridges.launchRules source target).length = 9 := by
    intro source target
    rfl
  unfold scannerLedgerMachine WorkMachineChain.machine
    WorkMachineChain.rules WorkMachineChain.bridgeRules
  simp only [List.length_append, List.length_map]
  have scannerMachineRules :
      TargetEmitterGrammarScanner.machine.rules.length =
        TargetEmitterGrammarScanner.rules.length := rfl
  have ledgerMachineRules :
      TargetEmitterLedger.machine.rules.length =
        TargetEmitterLedger.rules.length := rfl
  rw [scannerMachineRules, ledgerMachineRules,
    TargetEmitterGrammarScanner.rules_length,
    TargetEmitterLedger.rules_length, hLaunch]
  rfl

theorem rules_length :
    machine.rules.length = 34958 := by
  have hLaunch : ∀ source target,
      (PipelineStageBridges.launchRules source target).length = 9 := by
    intro source target
    rfl
  unfold machine WorkMachineChain.machine
    WorkMachineChain.rules WorkMachineChain.bridgeRules
  simp only [List.length_append, List.length_map]
  rw [CNFToNANDCarrierEncoder.rules_length,
    scannerLedger_rules_length, hLaunch]

private theorem scannerLedgerRulesPairwise :
    scannerLedgerMachine.rules.Pairwise
      WorkMachineChain.QueryDistinct := by
  exact WorkMachineChain.rules_pairwise_query_distinct
    TargetEmitterGrammarScanner.machine
    TargetEmitterLedger.machine
    TargetEmitterGrammarScanner.rules_pairwise_query_distinct
    TargetEmitterLedger.rules_pairwise_query_distinct
    scannerNoRuleAtAccept

theorem rules_pairwise :
    machine.rules.Pairwise WorkMachineChain.QueryDistinct := by
  exact WorkMachineChain.rules_pairwise_query_distinct
    CNFToNANDCarrierEncoder.machine scannerLedgerMachine
    CNFToNANDCarrierEncoder.rules_pairwise
    scannerLedgerRulesPairwise carrierNoRuleAtAccept

theorem machine_accept_ne_reject :
    machine.acceptState ≠ machine.rejectState := by
  apply WorkMachineChain.machine_acceptState_ne_rejectState
  exact WorkMachineChain.machine_acceptState_ne_rejectState
      TargetEmitterGrammarScanner.machine TargetEmitterLedger.machine
      TargetEmitterLedger.machine_accept_ne_reject

theorem rule_source_ne_accept
    (rule : WorkRule) (member : rule ∈ machine.rules) :
    rule.sourceState ≠ machine.acceptState := by
  exact WorkMachineChain.noRuleAtAccept
    CNFToNANDCarrierEncoder.machine scannerLedgerMachine
    scannerLedgerNoRuleAtAccept rule member

/-- Exact local endpoint supplied to the carrier after raw-input framing. -/
def carrierEntryConfiguration (formula : CNFFormula) :
    WorkConfiguration :=
  CNFToNANDCarrierEncoder.entryConfiguration
    (formulaTokens formula) [] []

def entryConfiguration (formula : CNFFormula) :
    WorkConfiguration :=
  PipelineStateNamespace.renameConfiguration
    WorkMachineChain.firstState
    (carrierEntryConfiguration formula)

/-- Exact nested-state representation of the physical post-ledger endpoint. -/
def finalConfiguration (formula : CNFFormula) :
    WorkConfiguration :=
  PipelineStateNamespace.renameConfiguration
    WorkMachineChain.secondState
    (PipelineStateNamespace.renameConfiguration
      WorkMachineChain.secondState
      (postLedgerConfiguration formula))

theorem entryConfiguration_state (formula : CNFFormula) :
    (entryConfiguration formula).state = machine.startState := by
  rfl

/-- The explicitly reserved carrier entry denotes the same infinite blank
tape as the ordinary packed canonical CNF launch. -/
theorem entryConfiguration_blankEquivalent_rawInput
    (formula : CNFFormula) :
    WorkConfiguration.BlankEquivalent
      (entryConfiguration formula)
      (workStartConfiguration machine (rawInputWorkTape (encodeCNF formula))) := by
  refine ⟨?_, ?_⟩
  · simpa only [workStartConfiguration] using
      entryConfiguration_state formula
  · simpa only [entryConfiguration, carrierEntryConfiguration,
      PipelineStateNamespace.renameConfiguration,
      workStartConfiguration, encodeCNF, formulaTokens,
      encodeFormulaTokens,
      CNFToNANDCarrierEncoder.entryConfiguration] using
      CNFToNANDCarrierEncoder.entryTape_blankEquivalent_rawInput
        (formulaTokens formula)

theorem finalConfiguration_state (formula : CNFFormula) :
    (finalConfiguration formula).state = machine.acceptState := by
  rfl

theorem finalConfiguration_tape (formula : CNFFormula) :
    (finalConfiguration formula).tape =
      (postLedgerConfiguration formula).tape := by
  rfl

theorem finalConfiguration_left (formula : CNFFormula) :
    (finalConfiguration formula).tape.left =
      TargetEmitterLedger.ledgerLeftWorkspace
        (capacity formula) (postLedgerRegisters formula)
        [TargetEmitterLedger.cellBlank] := by
  exact postLedgerConfiguration_left formula

theorem finalConfiguration_source_and_blank_target
    (formula : CNFFormula) :
    let cells :=
      LockedNAND.SourceParser.circuitCells (carrierCircuit formula)
    match cells with
    | [] =>
        (finalConfiguration formula).tape.head =
            TargetEmitterLedger.cellBlank ∧
          (finalConfiguration formula).tape.right =
            [TargetEmitterLedger.sourceTargetBoundary,
             TargetEmitterLedger.cellBlank,
             TargetEmitterLedger.cellBlank,
             TargetEmitterLedger.cellBlank]
    | first :: rest =>
        (finalConfiguration formula).tape.head = first ∧
          (finalConfiguration formula).tape.right =
            rest ++
              [TargetEmitterLedger.sourceTargetBoundary,
               TargetEmitterLedger.cellBlank,
               TargetEmitterLedger.cellBlank,
               TargetEmitterLedger.cellBlank] := by
  exact postLedgerConfiguration_source_and_blank_target formula

theorem finalConfiguration_outputBits (formula : CNFFormula) :
    (encodeWorkTape (finalConfiguration formula).tape).outputBits =
      encodeCircuit (carrierCircuit formula) := by
  let raw := carrierCircuit formula
  change
    (encodeWorkTape
      (TargetEmitterLedger.finalTape raw)).outputBits =
        encodeCircuit raw
  cases cellsEq : SourceParser.circuitCells raw with
  | nil =>
      exact False.elim
        (SourceParser.circuitCells_ne_empty raw cellsEq)
  | cons first rest =>
      have encoded := SourceParser.encodeWorkRight_circuitCells raw
      rw [cellsEq] at encoded
      unfold TargetEmitterLedger.finalTape
      rw [cellsEq]
      change
        Tape.decodeOutputCells
          (first.first :: first.second ::
            encodeWorkRight
              (rest ++
                [TargetEmitterLedger.sourceTargetBoundary,
                 TargetEmitterLedger.cellBlank,
                 TargetEmitterLedger.cellBlank,
                 TargetEmitterLedger.cellBlank])) =
          encodeCircuit raw
      change
        encodeWorkRight (first :: rest) =
          (encodeCircuit raw).map TapeSymbol.ofBool at encoded
      rw [encodeWorkRight_append]
      change
        Tape.decodeOutputCells
          (encodeWorkRight (first :: rest) ++
            TapeSymbol.blank ::
              [TapeSymbol.one,
               TapeSymbol.blank, TapeSymbol.blank,
               TapeSymbol.blank, TapeSymbol.blank,
               TapeSymbol.blank, TapeSymbol.blank]) =
          encodeCircuit raw
      rw [encoded, Tape.decodeOutputCells_append_blank]

def scannerLedgerWorkSteps (formula : CNFFormula) : Nat :=
  TargetEmitterGrammarScanner.canonicalSteps (carrierCircuit formula) +
    1 + TargetEmitterLedger.workSteps (carrierCircuit formula)

/-- Exact work-transition count for the canonical carrier, scanner, and
ledger prefix, including both literal graph bridges. -/
def workSteps (formula : CNFFormula) : Nat :=
  CNFToNANDCarrierEncoder.canonicalWorkSteps (formulaTokens formula) +
    1 + scannerLedgerWorkSteps formula

theorem workSteps_eq (formula : CNFFormula) :
    workSteps formula =
      CNFToNANDCarrierEncoder.canonicalWorkSteps
          (formulaTokens formula) + 1 +
        (TargetEmitterGrammarScanner.canonicalSteps
            (carrierCircuit formula) + 1 +
          TargetEmitterLedger.workSteps
            (carrierCircuit formula)) := by
  rfl

theorem carrierWorkSteps_polynomial_bound
    (formula : CNFFormula) :
    CNFToNANDCarrierEncoder.canonicalWorkSteps
        (formulaTokens formula) ≤
      CNFToNANDCarrierEncoder.workPolynomial.eval
        (formulaTokens formula).length := by
  exact
    CNFToNANDCarrierEncoder.canonicalWorkSteps_polynomial_bound
      (formulaTokens formula)

theorem carrierWorkSteps_encodedPolynomial_bound
    (formula : CNFFormula) :
    CNFToNANDCarrierEncoder.canonicalWorkSteps
        (formulaTokens formula) ≤
      CNFToNANDCarrierEncoder.workPolynomial.eval
        (encodeCNF formula).length := by
  have tokenLength :
      (formulaTokens formula).length ≤
        (encodeCNF formula).length := by
    rw [canonicalEncodedBits_length]
    omega
  exact Nat.le_trans
    (carrierWorkSteps_polynomial_bound formula)
    (NatPolynomial.eval_mono
      CNFToNANDCarrierEncoder.workPolynomial tokenLength)

/-- Exact composition after any proved carrier trace.  The endpoint is
existential only because each blank-equivalence transport preserves the
infinite tape while retaining the caller's finite exterior blank window. -/
private theorem exact_after_carrier
    (formula : CNFFormula) (carrierSteps : Nat)
    (carrierRun :
      workRunExact? CNFToNANDCarrierEncoder.machine carrierSteps
          (carrierEntryConfiguration formula) =
        some
          (CNFToNANDCarrierEncoder.finalConfiguration
            (formulaTokens formula) [] [])) :
    ∃ actualFinal,
      workRunExact? machine
          (carrierSteps + 1 + scannerLedgerWorkSteps formula)
          (entryConfiguration formula) =
        some actualFinal ∧
      WorkConfiguration.BlankEquivalent
        actualFinal (finalConfiguration formula) := by
  let raw := carrierCircuit formula
  let carrierFinal :=
    CNFToNANDCarrierEncoder.finalConfiguration
      (formulaTokens formula) [] []
  let scannerInitial : WorkConfiguration :=
    { state := TargetEmitterGrammarScanner.machine.startState
      tape := carrierFinal.tape }
  have scannerInitialEquivalent :
      WorkConfiguration.BlankEquivalent scannerInitial
        (workStartConfiguration
          TargetEmitterGrammarScanner.machine
          (rawInputWorkTape (encodeCircuit raw))) := by
    refine ⟨rfl, ?_⟩
    change
      WorkTape.BlankEquivalent
        (CNFToNANDCarrierEncoder.finalTape
          (formulaTokens formula) [] [])
        (rawInputWorkTape
          (encodeCircuit
            (CNFToNANDCarrierEncoder.Source.carrierCircuit
              (formulaTokens formula))))
    exact
      CNFToNANDCarrierEncoder.finalTape_blankEquivalent_rawInput
        (formulaTokens formula)
  rcases PNP.Concrete.workRunExact?_transport
      TargetEmitterGrammarScanner.machine
      (TargetEmitterGrammarScanner.canonicalSteps raw)
      scannerInitialEquivalent
      (TargetEmitterGrammarScanner.canonical_exact raw) with
    ⟨scannerFinal, scannerRun, scannerFinalEquivalent⟩
  have scannerFinalAccept :
      scannerFinal.state =
        TargetEmitterGrammarScanner.machine.acceptState :=
    scannerFinalEquivalent.state.trans
      (TargetEmitterGrammarScanner.acceptedConfiguration_state raw)
  let ledgerInitial : WorkConfiguration :=
    { state := TargetEmitterLedger.machine.startState
      tape := scannerFinal.tape }
  have ledgerInitialEquivalent :
      WorkConfiguration.BlankEquivalent ledgerInitial
        (TargetEmitterLedger.entryConfiguration raw) := by
    refine ⟨rfl, ?_⟩
    exact scannerFinalEquivalent.tape
  rcases PNP.Concrete.workRunExact?_transport
      TargetEmitterLedger.machine
      (TargetEmitterLedger.workSteps raw)
      ledgerInitialEquivalent
      (TargetEmitterLedger.exact_execution raw) with
    ⟨ledgerFinal, ledgerRun, ledgerFinalEquivalent⟩
  have scannerLedgerRun :
      workRunExact? scannerLedgerMachine
          (scannerLedgerWorkSteps formula)
          (PipelineStateNamespace.renameConfiguration
            WorkMachineChain.firstState scannerInitial) =
        some
          (PipelineStateNamespace.renameConfiguration
            WorkMachineChain.secondState ledgerFinal) := by
    simpa [scannerLedgerMachine, scannerLedgerWorkSteps, raw,
      ledgerInitial] using
      WorkMachineChain.workRunExact
        TargetEmitterGrammarScanner.machine
        TargetEmitterLedger.machine
        (TargetEmitterGrammarScanner.canonicalSteps raw)
        (TargetEmitterLedger.workSteps raw)
        scannerInitial scannerFinal ledgerFinal
        scannerRun scannerFinalAccept ledgerRun
  have combined :
      workRunExact? machine
          (carrierSteps + 1 + scannerLedgerWorkSteps formula)
          (entryConfiguration formula) =
        some
          (PipelineStateNamespace.renameConfiguration
            WorkMachineChain.secondState
            (PipelineStateNamespace.renameConfiguration
              WorkMachineChain.secondState ledgerFinal)) := by
    simpa [machine, entryConfiguration, scannerInitial,
      carrierFinal] using
      WorkMachineChain.workRunExact
        CNFToNANDCarrierEncoder.machine scannerLedgerMachine
        carrierSteps (scannerLedgerWorkSteps formula)
        (carrierEntryConfiguration formula) carrierFinal
        (PipelineStateNamespace.renameConfiguration
          WorkMachineChain.secondState ledgerFinal)
        carrierRun rfl scannerLedgerRun
  refine
    ⟨PipelineStateNamespace.renameConfiguration
        WorkMachineChain.secondState
        (PipelineStateNamespace.renameConfiguration
          WorkMachineChain.secondState ledgerFinal),
      combined, ?_⟩
  refine ⟨?_, ledgerFinalEquivalent.tape⟩
  change
    WorkMachineChain.secondState
        (WorkMachineChain.secondState ledgerFinal.state) =
      WorkMachineChain.secondState
        (WorkMachineChain.secondState
          (TargetEmitterLedger.finalConfiguration
            (carrierCircuit formula)).state)
  exact congrArg
    (fun state =>
      WorkMachineChain.secondState
        (WorkMachineChain.secondState state))
    (by simpa [raw] using ledgerFinalEquivalent.state)

/-- Certificate-free execution of the complete canonical physical workspace
prefix.  The reached finite tape window is allowed to retain different
exterior blanks, but denotes exactly the canonical post-ledger tape. -/
theorem exact_execution (formula : CNFFormula) :
    ∃ actualFinal,
      workRunExact? machine (workSteps formula)
          (entryConfiguration formula) =
        some actualFinal ∧
      WorkConfiguration.BlankEquivalent
        actualFinal (finalConfiguration formula) := by
  cases tokensEq : formulaTokens formula with
  | nil =>
      exact False.elim (formulaTokens_ne_nil formula tokensEq)
  | cons first rest =>
      have carrierRun :
          workRunExact? CNFToNANDCarrierEncoder.machine
              (CNFToNANDCarrierEncoder.canonicalWorkSteps
                (formulaTokens formula))
              (carrierEntryConfiguration formula) =
            some
              (CNFToNANDCarrierEncoder.finalConfiguration
                (formulaTokens formula) [] []) := by
        simpa [carrierEntryConfiguration, tokensEq] using
          CNFToNANDCarrierEncoder.canonical_exact first rest
      simpa [workSteps] using
        exact_after_carrier formula
          (CNFToNANDCarrierEncoder.canonicalWorkSteps
            (formulaTokens formula))
          carrierRun

/-- Exact output corollary at the canonical post-ledger representative of the
reached blank-equivalence class. -/
theorem exact_execution_output (formula : CNFFormula) :
    ∃ actualFinal,
      workRunExact? machine (workSteps formula)
          (entryConfiguration formula) =
        some actualFinal ∧
      WorkConfiguration.BlankEquivalent
        actualFinal (finalConfiguration formula) ∧
      (encodeWorkTape (finalConfiguration formula).tape).outputBits =
        encodeCircuit (carrierCircuit formula) := by
  rcases exact_execution formula with
    ⟨actualFinal, run, equivalent⟩
  exact
    ⟨actualFinal, run, equivalent,
      finalConfiguration_outputBits formula⟩

/-- Exact retained-register corollary for the canonical post-ledger
representative reached by `exact_execution`. -/
theorem exact_execution_registers (formula : CNFFormula) :
    ∃ actualFinal,
      workRunExact? machine (workSteps formula)
          (entryConfiguration formula) =
        some actualFinal ∧
      WorkConfiguration.BlankEquivalent
          actualFinal (finalConfiguration formula) ∧
        (postLedgerRegisters formula).inputCount = 0 ∧
        (postLedgerRegisters formula).normalizedGateCount =
          (formulaTokens formula).length + 1 ∧
        (postLedgerRegisters formula).carrierWidth =
          6 * ((formulaTokens formula).length + 1) + 1 ∧
        (postLedgerRegisters formula).currentGate = 0 ∧
        (postLedgerRegisters formula).outputIndex = 0 := by
  rcases exact_execution formula with
    ⟨actualFinal, run, equivalent⟩
  exact
    ⟨actualFinal, run, equivalent,
      postLedgerRegisters_inputCount formula,
      postLedgerRegisters_normalizedGateCount formula,
      postLedgerRegisters_carrierWidth formula,
      postLedgerRegisters_currentGate formula,
      postLedgerRegisters_outputIndex formula⟩

end PNP.Concrete.CNFToNANDWorkspace
