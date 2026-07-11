import PNP.Concrete.CNFWorkCorrectness


namespace PNP.Concrete

namespace GrammarFailureDesign

inductive FormulaGrammarMode where
  | header (count : Nat)
  | clauses
  | clause
  | literal (positive : Bool) (index : Nat)

def formulaGrammarSucceeded
    (mode : FormulaGrammarMode) (tokens : List CNFToken) : Bool :=
  match mode with
  | .header count =>
      match decodeFormulaHeader count tokens with
      | none => false
      | some _ => true
  | .clauses =>
      match decodeFormulaClauses tokens with
      | none => false
      | some _ => true
  | .clause =>
      match decodeFormulaClause tokens with
      | none => false
      | some _ => true
  | .literal positive index =>
      match decodeFormulaLiteral positive index tokens with
      | none => false
      | some _ => true

theorem formulaGrammarSucceeded_header
    (count : Nat) (tokens : List CNFToken) :
    formulaGrammarSucceeded (.header count) tokens =
      match decodeFormulaHeader count tokens with
      | none => false
      | some _ => true := rfl

theorem formulaGrammarSucceeded_clauses (tokens : List CNFToken) :
    formulaGrammarSucceeded .clauses tokens =
      match decodeFormulaClauses tokens with
      | none => false
      | some _ => true := rfl

theorem formulaGrammarSucceeded_clause (tokens : List CNFToken) :
    formulaGrammarSucceeded .clause tokens =
      match decodeFormulaClause tokens with
      | none => false
      | some _ => true := rfl

theorem formulaGrammarSucceeded_literal
    (positive : Bool) (index : Nat) (tokens : List CNFToken) :
    formulaGrammarSucceeded (.literal positive index) tokens =
      match decodeFormulaLiteral positive index tokens with
      | none => false
      | some _ => true := rfl

inductive FormulaGrammarFailure :
    FormulaGrammarMode → List CNFToken → Prop where
  | headerEmpty (count : Nat) :
      FormulaGrammarFailure (.header count) []
  | headerSep (count : Nat) (rest : List CNFToken) :
      FormulaGrammarFailure (.header count) (.sep :: rest)
  | headerFinish (count : Nat) (rest : List CNFToken) :
      FormulaGrammarFailure (.header count) (.finish :: rest)
  | headerT {count : Nat} {rest : List CNFToken}
      (tail : FormulaGrammarFailure (.header (count + 1)) rest) :
      FormulaGrammarFailure (.header count) (.t :: rest)
  | headerF {count : Nat} {rest : List CNFToken}
      (tail : FormulaGrammarFailure .clauses rest) :
      FormulaGrammarFailure (.header count) (.f :: rest)
  | clausesEmpty : FormulaGrammarFailure .clauses []
  | clausesF (rest : List CNFToken) :
      FormulaGrammarFailure .clauses (.f :: rest)
  | clausesT (rest : List CNFToken) :
      FormulaGrammarFailure .clauses (.t :: rest)
  | clausesSep {rest : List CNFToken}
      (tail : FormulaGrammarFailure .clause rest) :
      FormulaGrammarFailure .clauses (.sep :: rest)
  | clausesFinishTrailing (next : CNFToken) (rest : List CNFToken) :
      FormulaGrammarFailure .clauses (.finish :: next :: rest)
  | clauseEmpty : FormulaGrammarFailure .clause []
  | clauseSep (rest : List CNFToken) :
      FormulaGrammarFailure .clause (.sep :: rest)
  | clauseF {rest : List CNFToken}
      (tail : FormulaGrammarFailure (.literal false 0) rest) :
      FormulaGrammarFailure .clause (.f :: rest)
  | clauseT {rest : List CNFToken}
      (tail : FormulaGrammarFailure (.literal true 0) rest) :
      FormulaGrammarFailure .clause (.t :: rest)
  | clauseFinish {rest : List CNFToken}
      (tail : FormulaGrammarFailure .clauses rest) :
      FormulaGrammarFailure .clause (.finish :: rest)
  | literalEmpty (positive : Bool) (index : Nat) :
      FormulaGrammarFailure (.literal positive index) []
  | literalSep (positive : Bool) (index : Nat) (rest : List CNFToken) :
      FormulaGrammarFailure (.literal positive index) (.sep :: rest)
  | literalFinish (positive : Bool) (index : Nat)
      (rest : List CNFToken) :
      FormulaGrammarFailure (.literal positive index) (.finish :: rest)
  | literalF {positive : Bool} {index : Nat} {rest : List CNFToken}
      (tail : FormulaGrammarFailure .clause rest) :
      FormulaGrammarFailure (.literal positive index) (.f :: rest)
  | literalT {positive : Bool} {index : Nat} {rest : List CNFToken}
      (tail : FormulaGrammarFailure (.literal positive (index + 1)) rest) :
      FormulaGrammarFailure (.literal positive index) (.t :: rest)

set_option maxRecDepth 100000

theorem formulaGrammarFailure_of_unsuccessful
    (tokens : List CNFToken) :
    ∀ mode, formulaGrammarSucceeded mode tokens = false →
      FormulaGrammarFailure mode tokens := by
  induction tokens with
  | nil =>
      intro mode failed
      cases mode with
      | header count => exact .headerEmpty count
      | clauses => exact .clausesEmpty
      | clause => exact .clauseEmpty
      | literal positive index => exact .literalEmpty positive index
  | cons token rest ih =>
      intro mode failed
      cases mode with
      | header count =>
          cases token with
          | f =>
              cases tailResult : decodeFormulaClauses rest with
              | none =>
                  apply FormulaGrammarFailure.headerF
                  apply ih .clauses
                  rw [formulaGrammarSucceeded_clauses, tailResult]
              | some clauses =>
                  rw [formulaGrammarSucceeded_header] at failed
                  unfold decodeFormulaHeader at failed
                  rw [tailResult] at failed
                  contradiction
          | t =>
              cases tailResult : decodeFormulaHeader (count + 1) rest with
              | none =>
                  apply FormulaGrammarFailure.headerT
                  apply ih (.header (count + 1))
                  rw [formulaGrammarSucceeded_header, tailResult]
              | some formula =>
                  rw [formulaGrammarSucceeded_header] at failed
                  change (match decodeFormulaHeader (count + 1) rest with
                    | none => false
                    | some formula => true) = false at failed
                  rw [tailResult] at failed
                  contradiction
          | sep => exact .headerSep count rest
          | finish => exact .headerFinish count rest
      | clauses =>
          cases token with
          | f => exact .clausesF rest
          | t => exact .clausesT rest
          | sep =>
              cases tailResult : decodeFormulaClause rest with
              | none =>
                  apply FormulaGrammarFailure.clausesSep
                  apply ih .clause
                  rw [formulaGrammarSucceeded_clause, tailResult]
              | some found =>
                  rw [formulaGrammarSucceeded_clauses] at failed
                  unfold decodeFormulaClauses at failed
                  rw [tailResult] at failed
                  contradiction
          | finish =>
              cases rest with
              | nil =>
                  rw [formulaGrammarSucceeded_clauses] at failed
                  change true = false at failed
                  contradiction
              | cons next suffix => exact .clausesFinishTrailing next suffix
      | clause =>
          cases token with
          | f =>
              cases tailResult : decodeFormulaLiteral false 0 rest with
              | none =>
                  apply FormulaGrammarFailure.clauseF
                  apply ih (.literal false 0)
                  rw [formulaGrammarSucceeded_literal, tailResult]
              | some found =>
                  rw [formulaGrammarSucceeded_clause] at failed
                  change (match decodeFormulaLiteral false 0 rest with
                    | none => false
                    | some found => true) = false at failed
                  rw [tailResult] at failed
                  contradiction
          | t =>
              cases tailResult : decodeFormulaLiteral true 0 rest with
              | none =>
                  apply FormulaGrammarFailure.clauseT
                  apply ih (.literal true 0)
                  rw [formulaGrammarSucceeded_literal, tailResult]
              | some found =>
                  rw [formulaGrammarSucceeded_clause] at failed
                  change (match decodeFormulaLiteral true 0 rest with
                    | none => false
                    | some found => true) = false at failed
                  rw [tailResult] at failed
                  contradiction
          | sep => exact .clauseSep rest
          | finish =>
              cases tailResult : decodeFormulaClauses rest with
              | none =>
                  apply FormulaGrammarFailure.clauseFinish
                  apply ih .clauses
                  rw [formulaGrammarSucceeded_clauses, tailResult]
              | some clauses =>
                  rw [formulaGrammarSucceeded_clause] at failed
                  unfold decodeFormulaClause at failed
                  rw [tailResult] at failed
                  contradiction
      | literal positive index =>
          cases token with
          | f =>
              cases tailResult : decodeFormulaClause rest with
              | none =>
                  apply FormulaGrammarFailure.literalF
                  apply ih .clause
                  rw [formulaGrammarSucceeded_clause, tailResult]
              | some found =>
                  rw [formulaGrammarSucceeded_literal] at failed
                  unfold decodeFormulaLiteral at failed
                  rw [tailResult] at failed
                  contradiction
          | t =>
              cases tailResult :
                  decodeFormulaLiteral positive (index + 1) rest with
              | none =>
                  apply FormulaGrammarFailure.literalT
                  apply ih (.literal positive (index + 1))
                  rw [formulaGrammarSucceeded_literal, tailResult]
              | some found =>
                  rw [formulaGrammarSucceeded_literal] at failed
                  change
                    (match decodeFormulaLiteral positive (index + 1) rest with
                    | none => false
                    | some found => true) = false at failed
                  rw [tailResult] at failed
                  contradiction
          | sep => exact .literalSep positive index rest
          | finish => exact .literalFinish positive index rest

theorem decodeCNFTokens_none_to_failure (tokens : List CNFToken)
    (decoded : decodeCNFTokens tokens = none) :
    FormulaGrammarFailure (.header 0) tokens := by
  apply formulaGrammarFailure_of_unsuccessful tokens (.header 0)
  rw [formulaGrammarSucceeded_header]
  unfold decodeCNFTokens at decoded
  rw [decoded]

end GrammarFailureDesign

end PNP.Concrete


namespace PNP.Concrete

namespace GrammarTerminalDesign

open FrameTraceDesign
open ClauseLiteralDesign

set_option maxRecDepth 100000

theorem workConsAppend (head : WorkSymbol)
    (first second : List WorkSymbol) :
    (head :: first) ++ second = head :: (first ++ second) := rfl

def literalRestoreBadLeft (assignment : BitString)
    (counter formulaSuffix leftBase : List WorkSymbol)
    (bad : WorkSymbol)
    (markedIndexLength rawIndexTailLength : Nat) : List WorkSymbol :=
  let markedLeft := pushWorkLeft
    (List.replicate markedIndexLength cnfMarkTrue)
    (cnfBoundaryGuard :: leftBase)
  let rawLeft := pushWorkLeft
    (List.replicate rawIndexTailLength cnfT) markedLeft
  let suffixLeft := pushWorkLeft formulaSuffix (bad :: rawLeft)
  let counterLeft := pushWorkLeft counter
    (cnfBoundaryGuard :: suffixLeft)
  pushWorkLeft (markedAssignmentWorkSymbols assignment)
    (cnfFinish :: counterLeft)

theorem literalRestore_badFormulaSymbol_exact
    (result positive : Bool)
    (assignment : BitString)
    (counter formulaSuffix leftBase right : List WorkSymbol)
    (bad : WorkSymbol)
    (markedIndexLength rawIndexTailLength : Nat)
    (counterAllowed : ∀ symbol, List.Mem symbol counter →
      symbol = cnfMarkFalse)
    (formulaAllowed : ∀ symbol, List.Mem symbol formulaSuffix →
      FormulaScanSymbol symbol)
    (badScanAllowed : RestoreSignScanSymbol bad)
    (badIndexInvalid : ¬ RestoreIndexSymbol bad) :
    workRunExact? cnfWorkMachine
        (literalRestoreSteps assignment.length counter.length
          formulaSuffix.length markedIndexLength rawIndexTailLength)
        (workConfigAtLeftWord
          (CNFWorkState.literalRestoreAssignment result positive)
          (literalRestoreBadLeft assignment counter formulaSuffix leftBase bad
            markedIndexLength rawIndexTailLength)
          right) =
      some (workConfigAtWord CNFWorkState.reject
        (pushWorkLeft (List.replicate rawIndexTailLength cnfT)
          (pushWorkLeft (List.replicate markedIndexLength cnfT)
            ((if positive then cnfT else cnfF) :: leftBase)))
        (bad ::
          (formulaSuffix ++
            (cnfBoundaryGuard ::
              (counter ++
                (cnfFinish ::
                  (assignmentWorkSymbols assignment ++ right))))))) := by
  unfold literalRestoreSteps literalRestoreBadLeft
  let formulaLeft :=
    pushWorkLeft formulaSuffix
      (bad ::
        pushWorkLeft (List.replicate rawIndexTailLength cnfT)
          (pushWorkLeft (List.replicate markedIndexLength cnfMarkTrue)
            (cnfBoundaryGuard :: leftBase)))
  let assignmentTail := assignmentWorkSymbols assignment ++ right
  let counterTail := cnfFinish :: assignmentTail
  let formulaTail := cnfBoundaryGuard :: (counter ++ counterTail)
  let restoredFormulaTail := formulaSuffix ++ formulaTail
  let indexBadTail := bad :: restoredFormulaTail
  let rawIndexTail :=
    List.replicate rawIndexTailLength cnfT ++ indexBadTail
  let markedIndexTail :=
    List.replicate markedIndexLength cnfMarkTrue ++ rawIndexTail
  have hAssignment := literalRestoreAssignment_scan result positive
    assignment (cnfFinish :: pushWorkLeft counter
      (cnfBoundaryGuard :: formulaLeft)) right
  have hAssignmentFinish := workRunExact?_one_of_step cnfWorkMachine _ _
    (literalRestoreAssignment_finish_step result positive
      (pushWorkLeft counter (cnfBoundaryGuard :: formulaLeft))
      assignmentTail)
  have hCounter := literalRestoreCounter_scan result positive counter
    (cnfBoundaryGuard :: formulaLeft)
    counterTail counterAllowed
  have hCounterBoundary := workRunExact?_one_of_step cnfWorkMachine _ _
    (literalRestoreCounter_boundary_step result positive formulaLeft
      (counter ++ counterTail))
  have suffixAllowed : ∀ symbol, List.Mem symbol formulaSuffix →
      RestoreSignScanSymbol symbol := by
    intro symbol member
    exact formulaScan_restoreSign symbol (formulaAllowed symbol member)
  have hFormulaSuffix := literalRestoreSign_scan result positive
    formulaSuffix
    (bad ::
      pushWorkLeft (List.replicate rawIndexTailLength cnfT)
        (pushWorkLeft (List.replicate markedIndexLength cnfMarkTrue)
          (cnfBoundaryGuard :: leftBase)))
    formulaTail suffixAllowed
  have hBad := workRunExact?_one_of_step cnfWorkMachine _ _
    (literalRestoreSign_keep_step result positive bad
      (pushWorkLeft (List.replicate rawIndexTailLength cnfT)
        (pushWorkLeft (List.replicate markedIndexLength cnfMarkTrue)
          (cnfBoundaryGuard :: leftBase)))
      restoredFormulaTail badScanAllowed)
  have rawAllowed : ∀ symbol,
      List.Mem symbol (List.replicate rawIndexTailLength cnfT) →
        RestoreSignScanSymbol symbol := by
    intro symbol member
    have equal := mem_replicate_workSymbol_eq
      rawIndexTailLength cnfT symbol member
    cases equal
    exact .t
  have hRawTail := literalRestoreSign_scan result positive
    (List.replicate rawIndexTailLength cnfT)
    (pushWorkLeft (List.replicate markedIndexLength cnfMarkTrue)
      (cnfBoundaryGuard :: leftBase))
    indexBadTail rawAllowed
  rw [length_replicate_workSymbol] at hRawTail
  have markedAllowed : ∀ symbol,
      List.Mem symbol (List.replicate markedIndexLength cnfMarkTrue) →
        RestoreSignScanSymbol symbol := by
    intro symbol member
    have equal := mem_replicate_workSymbol_eq
      markedIndexLength cnfMarkTrue symbol member
    cases equal
    exact .markTrue
  have hMarked := literalRestoreSign_scan result positive
    (List.replicate markedIndexLength cnfMarkTrue)
    (cnfBoundaryGuard :: leftBase)
    rawIndexTail markedAllowed
  rw [length_replicate_workSymbol] at hMarked
  have hSign := workRunExact?_one_of_step cnfWorkMachine _ _
    (literalRestoreSign_boundary_step result positive leftBase
      markedIndexTail)
  have hRestoreMarked := literalRestoreIndex_marked_scan result positive
    markedIndexLength
    ((if positive then cnfT else cnfF) :: leftBase)
    rawIndexTail
  have hKeepRaw := literalRestoreIndex_t_scan result positive
    rawIndexTailLength
    (pushWorkLeft (List.replicate markedIndexLength cnfT)
      ((if positive then cnfT else cnfF) :: leftBase))
    indexBadTail
  have hIndexBad := literalRestoreIndex_reject_run result positive
    (pushWorkLeft (List.replicate rawIndexTailLength cnfT)
      (pushWorkLeft (List.replicate markedIndexLength cnfT)
        ((if positive then cnfT else cnfF) :: leftBase)))
    restoredFormulaTail bad badIndexInvalid
  have h1 := workRunExact?_compose cnfWorkMachine assignment.length 1
    _ _ _ hAssignment hAssignmentFinish
  have h2 := workRunExact?_compose cnfWorkMachine
    (assignment.length + 1) counter.length _ _ _ h1 hCounter
  have h3 := workRunExact?_compose cnfWorkMachine
    ((assignment.length + 1) + counter.length) 1 _ _ _ h2 hCounterBoundary
  have h4 := workRunExact?_compose cnfWorkMachine
    (((assignment.length + 1) + counter.length) + 1)
    formulaSuffix.length _ _ _ h3 hFormulaSuffix
  have h5 := workRunExact?_compose cnfWorkMachine
    ((((assignment.length + 1) + counter.length) + 1) +
      formulaSuffix.length) 1 _ _ _ h4 hBad
  have h6 := workRunExact?_compose cnfWorkMachine
    (((((assignment.length + 1) + counter.length) + 1) +
      formulaSuffix.length) + 1) rawIndexTailLength _ _ _ h5 hRawTail
  have h7 := workRunExact?_compose cnfWorkMachine
    ((((((assignment.length + 1) + counter.length) + 1) +
      formulaSuffix.length) + 1) + rawIndexTailLength)
    markedIndexLength _ _ _ h6 hMarked
  have h8 := workRunExact?_compose cnfWorkMachine
    (((((((assignment.length + 1) + counter.length) + 1) +
      formulaSuffix.length) + 1) + rawIndexTailLength) +
      markedIndexLength) 1 _ _ _ h7 hSign
  have h9 := workRunExact?_compose cnfWorkMachine
    ((((((((assignment.length + 1) + counter.length) + 1) +
      formulaSuffix.length) + 1) + rawIndexTailLength) +
      markedIndexLength) + 1) markedIndexLength _ _ _ h8 hRestoreMarked
  have h10 := workRunExact?_compose cnfWorkMachine
    (((((((((assignment.length + 1) + counter.length) + 1) +
      formulaSuffix.length) + 1) + rawIndexTailLength) +
      markedIndexLength) + 1) + markedIndexLength)
    rawIndexTailLength _ _ _ h9 hKeepRaw
  exact workRunExact?_compose cnfWorkMachine
    ((((((((((assignment.length + 1) + counter.length) + 1) +
      formulaSuffix.length) + 1) + rawIndexTailLength) +
      markedIndexLength) + 1) + markedIndexLength) +
      rawIndexTailLength) 1 _ _ _ h10 hIndexBad

theorem literalRestore_sep_exact
    (result positive : Bool) (assignment : BitString)
    (counter formulaSuffix leftBase right : List WorkSymbol)
    (markedIndexLength rawIndexTailLength : Nat)
    (counterAllowed : ∀ symbol, List.Mem symbol counter →
      symbol = cnfMarkFalse)
    (formulaAllowed : ∀ symbol, List.Mem symbol formulaSuffix →
      FormulaScanSymbol symbol) :
    workRunExact? cnfWorkMachine
        (literalRestoreSteps assignment.length counter.length
          formulaSuffix.length markedIndexLength rawIndexTailLength)
        (workConfigAtLeftWord
          (CNFWorkState.literalRestoreAssignment result positive)
          (literalRestoreBadLeft assignment counter formulaSuffix leftBase
            cnfSep markedIndexLength rawIndexTailLength)
          right) =
      some (workConfigAtWord CNFWorkState.reject
        (pushWorkLeft (List.replicate rawIndexTailLength cnfT)
          (pushWorkLeft (List.replicate markedIndexLength cnfT)
            ((if positive then cnfT else cnfF) :: leftBase)))
        (cnfSep ::
          (formulaSuffix ++
            (cnfBoundaryGuard ::
              (counter ++
                (cnfFinish ::
                  (assignmentWorkSymbols assignment ++ right))))))) := by
  apply literalRestore_badFormulaSymbol_exact result positive assignment
    counter formulaSuffix leftBase right cnfSep markedIndexLength
    rawIndexTailLength counterAllowed formulaAllowed
  · exact .sep
  · intro allowed
    cases allowed

theorem literalRestore_finish_exact
    (result positive : Bool) (assignment : BitString)
    (counter formulaSuffix leftBase right : List WorkSymbol)
    (markedIndexLength rawIndexTailLength : Nat)
    (counterAllowed : ∀ symbol, List.Mem symbol counter →
      symbol = cnfMarkFalse)
    (formulaAllowed : ∀ symbol, List.Mem symbol formulaSuffix →
      FormulaScanSymbol symbol) :
    workRunExact? cnfWorkMachine
        (literalRestoreSteps assignment.length counter.length
          formulaSuffix.length markedIndexLength rawIndexTailLength)
        (workConfigAtLeftWord
          (CNFWorkState.literalRestoreAssignment result positive)
          (literalRestoreBadLeft assignment counter formulaSuffix leftBase
            cnfFinish markedIndexLength rawIndexTailLength)
          right) =
      some (workConfigAtWord CNFWorkState.reject
        (pushWorkLeft (List.replicate rawIndexTailLength cnfT)
          (pushWorkLeft (List.replicate markedIndexLength cnfT)
            ((if positive then cnfT else cnfF) :: leftBase)))
        (cnfFinish ::
          (formulaSuffix ++
            (cnfBoundaryGuard ::
              (counter ++
                (cnfFinish ::
                  (assignmentWorkSymbols assignment ++ right))))))) := by
  apply literalRestore_badFormulaSymbol_exact result positive assignment
    counter formulaSuffix leftBase right cnfFinish markedIndexLength
    rawIndexTailLength counterAllowed formulaAllowed
  · exact .finish
  · intro allowed
    cases allowed

def literalRestoreMissingSteps
    (assignmentLength counterLength markedIndexLength
      rawIndexTailLength : Nat) : Nat :=
  (((((((((assignmentLength + 1) + counterLength) + 1) +
    rawIndexTailLength) + markedIndexLength) + 1) +
    markedIndexLength) + rawIndexTailLength) + 1)

def literalRestoreMissingLeft (assignment : BitString)
    (counter leftBase : List WorkSymbol)
    (markedIndexLength rawIndexTailLength : Nat) : List WorkSymbol :=
  let markedLeft := pushWorkLeft
    (List.replicate markedIndexLength cnfMarkTrue)
    (cnfBoundaryGuard :: leftBase)
  let rawLeft := pushWorkLeft
    (List.replicate rawIndexTailLength cnfT) markedLeft
  let counterLeft := pushWorkLeft counter
    (cnfBoundaryGuard :: rawLeft)
  pushWorkLeft (markedAssignmentWorkSymbols assignment)
    (cnfFinish :: counterLeft)

theorem literalRestore_missingIndex_exact
    (result positive : Bool) (assignment : BitString)
    (counter leftBase right : List WorkSymbol)
    (markedIndexLength rawIndexTailLength : Nat)
    (counterAllowed : ∀ symbol, List.Mem symbol counter →
      symbol = cnfMarkFalse) :
    workRunExact? cnfWorkMachine
        (literalRestoreMissingSteps assignment.length counter.length
          markedIndexLength rawIndexTailLength)
        (workConfigAtLeftWord
          (CNFWorkState.literalRestoreAssignment result positive)
          (literalRestoreMissingLeft assignment counter leftBase
            markedIndexLength rawIndexTailLength)
          right) =
      some (workConfigAtWord CNFWorkState.reject
        (pushWorkLeft (List.replicate rawIndexTailLength cnfT)
          (pushWorkLeft (List.replicate markedIndexLength cnfT)
            ((if positive then cnfT else cnfF) :: leftBase)))
        (cnfBoundaryGuard ::
          (counter ++
            (cnfFinish ::
              (assignmentWorkSymbols assignment ++ right))))) := by
  unfold literalRestoreMissingSteps literalRestoreMissingLeft
  let formulaLeft :=
    pushWorkLeft (List.replicate rawIndexTailLength cnfT)
      (pushWorkLeft (List.replicate markedIndexLength cnfMarkTrue)
        (cnfBoundaryGuard :: leftBase))
  let assignmentTail := assignmentWorkSymbols assignment ++ right
  let counterTail := cnfFinish :: assignmentTail
  let formulaTail := cnfBoundaryGuard :: (counter ++ counterTail)
  let rawIndexTail :=
    List.replicate rawIndexTailLength cnfT ++ formulaTail
  let markedIndexTail :=
    List.replicate markedIndexLength cnfMarkTrue ++ rawIndexTail
  have hAssignment := literalRestoreAssignment_scan result positive
    assignment (cnfFinish :: pushWorkLeft counter
      (cnfBoundaryGuard :: formulaLeft)) right
  have hAssignmentFinish := workRunExact?_one_of_step cnfWorkMachine _ _
    (literalRestoreAssignment_finish_step result positive
      (pushWorkLeft counter (cnfBoundaryGuard :: formulaLeft))
      assignmentTail)
  have hCounter := literalRestoreCounter_scan result positive counter
    (cnfBoundaryGuard :: formulaLeft) counterTail counterAllowed
  have hCounterBoundary := workRunExact?_one_of_step cnfWorkMachine _ _
    (literalRestoreCounter_boundary_step result positive formulaLeft
      (counter ++ counterTail))
  have rawAllowed : ∀ symbol,
      List.Mem symbol (List.replicate rawIndexTailLength cnfT) →
        RestoreSignScanSymbol symbol := by
    intro symbol member
    have equal := mem_replicate_workSymbol_eq
      rawIndexTailLength cnfT symbol member
    cases equal
    exact .t
  have hRawTail := literalRestoreSign_scan result positive
    (List.replicate rawIndexTailLength cnfT)
    (pushWorkLeft (List.replicate markedIndexLength cnfMarkTrue)
      (cnfBoundaryGuard :: leftBase)) formulaTail rawAllowed
  rw [length_replicate_workSymbol] at hRawTail
  have markedAllowed : ∀ symbol,
      List.Mem symbol (List.replicate markedIndexLength cnfMarkTrue) →
        RestoreSignScanSymbol symbol := by
    intro symbol member
    have equal := mem_replicate_workSymbol_eq
      markedIndexLength cnfMarkTrue symbol member
    cases equal
    exact .markTrue
  have hMarked := literalRestoreSign_scan result positive
    (List.replicate markedIndexLength cnfMarkTrue)
    (cnfBoundaryGuard :: leftBase) rawIndexTail markedAllowed
  rw [length_replicate_workSymbol] at hMarked
  have hSign := workRunExact?_one_of_step cnfWorkMachine _ _
    (literalRestoreSign_boundary_step result positive leftBase
      markedIndexTail)
  have hRestoreMarked := literalRestoreIndex_marked_scan result positive
    markedIndexLength
    ((if positive then cnfT else cnfF) :: leftBase)
    rawIndexTail
  have hKeepRaw := literalRestoreIndex_t_scan result positive
    rawIndexTailLength
    (pushWorkLeft (List.replicate markedIndexLength cnfT)
      ((if positive then cnfT else cnfF) :: leftBase)) formulaTail
  have hMissing := literalRestoreIndex_reject_run result positive
    (pushWorkLeft (List.replicate rawIndexTailLength cnfT)
      (pushWorkLeft (List.replicate markedIndexLength cnfT)
        ((if positive then cnfT else cnfF) :: leftBase)))
    (counter ++ counterTail) cnfBoundaryGuard (by
      intro allowed
      cases allowed)
  have h1 := workRunExact?_compose cnfWorkMachine assignment.length 1
    _ _ _ hAssignment hAssignmentFinish
  have h2 := workRunExact?_compose cnfWorkMachine
    (assignment.length + 1) counter.length _ _ _ h1 hCounter
  have h3 := workRunExact?_compose cnfWorkMachine
    ((assignment.length + 1) + counter.length) 1 _ _ _ h2 hCounterBoundary
  have h4 := workRunExact?_compose cnfWorkMachine
    (((assignment.length + 1) + counter.length) + 1)
    rawIndexTailLength _ _ _ h3 hRawTail
  have h5 := workRunExact?_compose cnfWorkMachine
    ((((assignment.length + 1) + counter.length) + 1) +
      rawIndexTailLength) markedIndexLength _ _ _ h4 hMarked
  have h6 := workRunExact?_compose cnfWorkMachine
    (((((assignment.length + 1) + counter.length) + 1) +
      rawIndexTailLength) + markedIndexLength) 1 _ _ _ h5 hSign
  have h7 := workRunExact?_compose cnfWorkMachine
    ((((((assignment.length + 1) + counter.length) + 1) +
      rawIndexTailLength) + markedIndexLength) + 1)
    markedIndexLength _ _ _ h6 hRestoreMarked
  have h8 := workRunExact?_compose cnfWorkMachine
    (((((((assignment.length + 1) + counter.length) + 1) +
      rawIndexTailLength) + markedIndexLength) + 1) +
      markedIndexLength) rawIndexTailLength _ _ _ h7 hKeepRaw
  exact workRunExact?_compose cnfWorkMachine
    ((((((((assignment.length + 1) + counter.length) + 1) +
      rawIndexTailLength) + markedIndexLength) + 1) +
      markedIndexLength) + rawIndexTailLength) 1 _ _ _ h8 hMissing

theorem literalMark_oob_badFormulaSymbol_exact
    (alreadySatisfied positive : Bool) (assignment : BitString)
    (counter formulaSuffix leftBase right : List WorkSymbol)
    (bad : WorkSymbol) (rawIndexTailLength : Nat)
    (counterAllowed : ∀ symbol, List.Mem symbol counter →
      symbol = cnfMarkFalse)
    (formulaAllowed : ∀ symbol, List.Mem symbol formulaSuffix →
      FormulaScanSymbol symbol)
    (badFormulaAllowed : FormulaScanSymbol bad)
    (badIndexInvalid : ¬ RestoreIndexSymbol bad) :
    workRunExact? cnfWorkMachine
        (literalMarkOOBSteps assignment.length counter.length
          formulaSuffix.length rawIndexTailLength)
        (workConfigAtWord
          (CNFWorkState.literalIndex alreadySatisfied positive)
          (pushWorkLeft (List.replicate assignment.length cnfMarkTrue)
            (cnfBoundaryGuard :: leftBase))
          (cnfT ::
            (List.replicate rawIndexTailLength cnfT ++
              (bad ::
                (formulaSuffix ++
                  (cnfBoundaryGuard ::
                    (counter ++
                      (cnfFinish ::
                        (markedAssignmentWorkSymbols assignment ++
                          (cnfRootGuard :: right)))))))))) =
      some (workConfigAtWord CNFWorkState.reject
        (pushWorkLeft (List.replicate rawIndexTailLength cnfT)
          (pushWorkLeft
            (List.replicate (Nat.succ assignment.length) cnfT)
            ((if positive then cnfT else cnfF) :: leftBase)))
        (bad ::
          (formulaSuffix ++
            (cnfBoundaryGuard ::
              (counter ++
                (cnfFinish ::
                  (assignmentWorkSymbols assignment ++
                    (cnfRootGuard :: right)))))))) := by
  unfold literalMarkOOBSteps
  let signLeft := pushWorkLeft
    (List.replicate assignment.length cnfMarkTrue)
    (cnfBoundaryGuard :: leftBase)
  let formulaTail :=
    List.replicate rawIndexTailLength cnfT ++ bad :: formulaSuffix
  let assignmentRight := cnfRootGuard :: right
  let markedAssignmentTail :=
    markedAssignmentWorkSymbols assignment ++ assignmentRight
  let certificateTail := cnfBoundaryGuard ::
    (counter ++ (cnfFinish :: markedAssignmentTail))
  have tailAllowed : ∀ symbol, List.Mem symbol formulaTail →
      FormulaScanSymbol symbol := by
    intro symbol member
    unfold formulaTail at member
    have split := ClauseLiteralDesign.workSymbol_mem_append_cases
      (List.replicate rawIndexTailLength cnfT)
      (bad :: formulaSuffix) symbol member
    cases split with
    | inl rawMember =>
        have equal := mem_replicate_workSymbol_eq
          rawIndexTailLength cnfT symbol rawMember
        cases equal
        exact .t
    | inr tailMember =>
        cases tailMember with
        | head => exact badFormulaAllowed
        | tail _ suffixMember => exact formulaAllowed symbol suffixMember
  have hMarkIndex := workRunExact?_one_of_step cnfWorkMachine _ _
    (literalIndex_t_mark_step alreadySatisfied positive signLeft
      (formulaTail ++ certificateTail))
  have hOut := literalIndexToAssignmentPrefix_run alreadySatisfied positive
    formulaTail counter (markedAssignmentWorkSymbols assignment)
    (cnfMarkTrue :: signLeft) right cnfRootGuard tailAllowed counterAllowed
    (markedAssignmentWorkSymbols_allowed assignment)
  have hRoot := workRunExact?_one_of_step cnfWorkMachine _ _
    (literalMarkAssignment_root_step alreadySatisfied positive
      (pushWorkLeft (markedAssignmentWorkSymbols assignment)
        (cnfFinish ::
          pushWorkLeft counter
            (cnfBoundaryGuard ::
              pushWorkLeft formulaTail (cnfMarkTrue :: signLeft)))) right)
  have hMarkedShape :
      pushWorkLeft
          (List.replicate (Nat.succ assignment.length) cnfMarkTrue)
          (cnfBoundaryGuard :: leftBase) =
        cnfMarkTrue :: signLeft := by
    exact pushWorkLeft_replicate_markTrue_succ assignment.length
      (cnfBoundaryGuard :: leftBase)
  have hFormulaShape :
      pushWorkLeft formulaTail (cnfMarkTrue :: signLeft) =
        pushWorkLeft formulaSuffix
          (bad ::
            pushWorkLeft (List.replicate rawIndexTailLength cnfT)
              (pushWorkLeft
                (List.replicate (Nat.succ assignment.length) cnfMarkTrue)
                (cnfBoundaryGuard :: leftBase))) := by
    unfold formulaTail
    rw [pushWorkLeft_append]
    rw [hMarkedShape]
    rfl
  rw [hFormulaShape] at hRoot
  have hRestore := literalRestore_badFormulaSymbol_exact
    alreadySatisfied positive assignment counter formulaSuffix leftBase
    assignmentRight bad (Nat.succ assignment.length) rawIndexTailLength
    counterAllowed formulaAllowed
    (formulaScan_restoreSign bad badFormulaAllowed) badIndexInvalid
  unfold literalRestoreBadLeft at hRestore
  have formulaTailLength : formulaTail.length =
      rawIndexTailLength + 1 + formulaSuffix.length := by
    unfold formulaTail
    rw [frame_length_append]
    rw [length_replicate_workSymbol]
    rw [List.length_cons]
    exact natAddRightUnitExchange rawIndexTailLength formulaSuffix.length
  rw [formulaTailLength] at hOut
  rw [markedAssignmentWorkSymbols_length assignment] at hOut
  have h1 := workRunExact?_compose cnfWorkMachine 1
    ((((rawIndexTailLength + 1 + formulaSuffix.length) + 1) +
      counter.length + 1) + assignment.length)
    _ _ _ hMarkIndex hOut
  rw [hFormulaShape] at h1
  have h2 := workRunExact?_compose cnfWorkMachine
    (1 + ((((rawIndexTailLength + 1 + formulaSuffix.length) + 1) +
      counter.length + 1) + assignment.length)) 1 _ _ _ h1 hRoot
  unfold signLeft formulaTail certificateTail markedAssignmentTail at h2
  unfold assignmentRight at h2
  repeat' rw [frameWork_append_assoc] at h2
  unfold assignmentRight at hRestore
  exact workRunExact?_compose cnfWorkMachine
    ((1 + ((((rawIndexTailLength + 1 + formulaSuffix.length) + 1) +
      counter.length + 1) + assignment.length)) + 1)
    (literalRestoreSteps assignment.length counter.length
      formulaSuffix.length (Nat.succ assignment.length)
      rawIndexTailLength) _ _ _ h2 hRestore

theorem literalMark_oob_sep_exact
    (alreadySatisfied positive : Bool) (assignment : BitString)
    (counter formulaSuffix leftBase right : List WorkSymbol)
    (rawIndexTailLength : Nat)
    (counterAllowed : ∀ symbol, List.Mem symbol counter →
      symbol = cnfMarkFalse)
    (formulaAllowed : ∀ symbol, List.Mem symbol formulaSuffix →
      FormulaScanSymbol symbol) :
    workRunExact? cnfWorkMachine
        (literalMarkOOBSteps assignment.length counter.length
          formulaSuffix.length rawIndexTailLength)
        (workConfigAtWord
          (CNFWorkState.literalIndex alreadySatisfied positive)
          (pushWorkLeft (List.replicate assignment.length cnfMarkTrue)
            (cnfBoundaryGuard :: leftBase))
          (cnfT ::
            (List.replicate rawIndexTailLength cnfT ++
              (cnfSep ::
                (formulaSuffix ++
                  (cnfBoundaryGuard ::
                    (counter ++
                      (cnfFinish ::
                        (markedAssignmentWorkSymbols assignment ++
                          (cnfRootGuard :: right)))))))))) =
      some (workConfigAtWord CNFWorkState.reject
        (pushWorkLeft (List.replicate rawIndexTailLength cnfT)
          (pushWorkLeft
            (List.replicate (Nat.succ assignment.length) cnfT)
            ((if positive then cnfT else cnfF) :: leftBase)))
        (cnfSep ::
          (formulaSuffix ++
            (cnfBoundaryGuard ::
              (counter ++
                (cnfFinish ::
                  (assignmentWorkSymbols assignment ++
                    (cnfRootGuard :: right)))))))) := by
  apply literalMark_oob_badFormulaSymbol_exact alreadySatisfied positive
    assignment counter formulaSuffix leftBase right cnfSep
    rawIndexTailLength counterAllowed formulaAllowed
  · exact .sep
  · intro allowed
    cases allowed

theorem literalMark_oob_finish_exact
    (alreadySatisfied positive : Bool) (assignment : BitString)
    (counter formulaSuffix leftBase right : List WorkSymbol)
    (rawIndexTailLength : Nat)
    (counterAllowed : ∀ symbol, List.Mem symbol counter →
      symbol = cnfMarkFalse)
    (formulaAllowed : ∀ symbol, List.Mem symbol formulaSuffix →
      FormulaScanSymbol symbol) :
    workRunExact? cnfWorkMachine
        (literalMarkOOBSteps assignment.length counter.length
          formulaSuffix.length rawIndexTailLength)
        (workConfigAtWord
          (CNFWorkState.literalIndex alreadySatisfied positive)
          (pushWorkLeft (List.replicate assignment.length cnfMarkTrue)
            (cnfBoundaryGuard :: leftBase))
          (cnfT ::
            (List.replicate rawIndexTailLength cnfT ++
              (cnfFinish ::
                (formulaSuffix ++
                  (cnfBoundaryGuard ::
                    (counter ++
                      (cnfFinish ::
                        (markedAssignmentWorkSymbols assignment ++
                          (cnfRootGuard :: right)))))))))) =
      some (workConfigAtWord CNFWorkState.reject
        (pushWorkLeft (List.replicate rawIndexTailLength cnfT)
          (pushWorkLeft
            (List.replicate (Nat.succ assignment.length) cnfT)
            ((if positive then cnfT else cnfF) :: leftBase)))
        (cnfFinish ::
          (formulaSuffix ++
            (cnfBoundaryGuard ::
              (counter ++
                (cnfFinish ::
                  (assignmentWorkSymbols assignment ++
                    (cnfRootGuard :: right)))))))) := by
  apply literalMark_oob_badFormulaSymbol_exact alreadySatisfied positive
    assignment counter formulaSuffix leftBase right cnfFinish
    rawIndexTailLength counterAllowed formulaAllowed
  · exact .finish
  · intro allowed
    cases allowed

def literalMarkOOBMissingSteps
    (assignmentLength counterLength rawIndexTailLength : Nat) : Nat :=
  ((1 + (((rawIndexTailLength + 1) + counterLength + 1) +
    assignmentLength)) + 1) +
      literalRestoreMissingSteps assignmentLength counterLength
        (Nat.succ assignmentLength) rawIndexTailLength

theorem literalMark_oob_missingIndex_exact
    (alreadySatisfied positive : Bool) (assignment : BitString)
    (counter leftBase right : List WorkSymbol)
    (rawIndexTailLength : Nat)
    (counterAllowed : ∀ symbol, List.Mem symbol counter →
      symbol = cnfMarkFalse) :
    workRunExact? cnfWorkMachine
        (literalMarkOOBMissingSteps assignment.length counter.length
          rawIndexTailLength)
        (workConfigAtWord
          (CNFWorkState.literalIndex alreadySatisfied positive)
          (pushWorkLeft (List.replicate assignment.length cnfMarkTrue)
            (cnfBoundaryGuard :: leftBase))
          (cnfT ::
            (List.replicate rawIndexTailLength cnfT ++
              (cnfBoundaryGuard ::
                (counter ++
                  (cnfFinish ::
                    (markedAssignmentWorkSymbols assignment ++
                      (cnfRootGuard :: right)))))))) =
      some (workConfigAtWord CNFWorkState.reject
        (pushWorkLeft (List.replicate rawIndexTailLength cnfT)
          (pushWorkLeft
            (List.replicate (Nat.succ assignment.length) cnfT)
            ((if positive then cnfT else cnfF) :: leftBase)))
        (cnfBoundaryGuard ::
          (counter ++
            (cnfFinish ::
              (assignmentWorkSymbols assignment ++
                (cnfRootGuard :: right)))))) := by
  unfold literalMarkOOBMissingSteps
  let signLeft := pushWorkLeft
    (List.replicate assignment.length cnfMarkTrue)
    (cnfBoundaryGuard :: leftBase)
  let formulaTail := List.replicate rawIndexTailLength cnfT
  let assignmentRight := cnfRootGuard :: right
  let markedAssignmentTail :=
    markedAssignmentWorkSymbols assignment ++ assignmentRight
  let certificateTail := cnfBoundaryGuard ::
    (counter ++ (cnfFinish :: markedAssignmentTail))
  have tailAllowed : ∀ symbol, List.Mem symbol formulaTail →
      FormulaScanSymbol symbol := by
    intro symbol member
    unfold formulaTail at member
    have equal := mem_replicate_workSymbol_eq
      rawIndexTailLength cnfT symbol member
    cases equal
    exact .t
  have hMarkIndex := workRunExact?_one_of_step cnfWorkMachine _ _
    (literalIndex_t_mark_step alreadySatisfied positive signLeft
      (formulaTail ++ certificateTail))
  have hOut := literalIndexToAssignmentPrefix_run alreadySatisfied positive
    formulaTail counter (markedAssignmentWorkSymbols assignment)
    (cnfMarkTrue :: signLeft) right cnfRootGuard tailAllowed counterAllowed
    (markedAssignmentWorkSymbols_allowed assignment)
  have hRoot := workRunExact?_one_of_step cnfWorkMachine _ _
    (literalMarkAssignment_root_step alreadySatisfied positive
      (pushWorkLeft (markedAssignmentWorkSymbols assignment)
        (cnfFinish ::
          pushWorkLeft counter
            (cnfBoundaryGuard ::
              pushWorkLeft formulaTail (cnfMarkTrue :: signLeft)))) right)
  have hMarkedShape :
      pushWorkLeft
          (List.replicate (Nat.succ assignment.length) cnfMarkTrue)
          (cnfBoundaryGuard :: leftBase) =
        cnfMarkTrue :: signLeft := by
    exact pushWorkLeft_replicate_markTrue_succ assignment.length
      (cnfBoundaryGuard :: leftBase)
  have hFormulaShape :
      pushWorkLeft formulaTail (cnfMarkTrue :: signLeft) =
        pushWorkLeft (List.replicate rawIndexTailLength cnfT)
          (pushWorkLeft
            (List.replicate (Nat.succ assignment.length) cnfMarkTrue)
            (cnfBoundaryGuard :: leftBase)) := by
    unfold formulaTail
    rw [hMarkedShape]
  rw [hFormulaShape] at hRoot
  have hRestore := literalRestore_missingIndex_exact alreadySatisfied positive
    assignment counter leftBase assignmentRight
    (Nat.succ assignment.length) rawIndexTailLength counterAllowed
  unfold literalRestoreMissingLeft at hRestore
  unfold formulaTail at hOut
  rw [length_replicate_workSymbol] at hOut
  rw [markedAssignmentWorkSymbols_length assignment] at hOut
  have h1 := workRunExact?_compose cnfWorkMachine 1
    (((rawIndexTailLength + 1) + counter.length + 1) +
      assignment.length) _ _ _ hMarkIndex hOut
  rw [hFormulaShape] at h1
  have h2 := workRunExact?_compose cnfWorkMachine
    (1 + (((rawIndexTailLength + 1) + counter.length + 1) +
      assignment.length)) 1 _ _ _ h1 hRoot
  unfold signLeft formulaTail certificateTail markedAssignmentTail at h2
  unfold assignmentRight at h2
  repeat' rw [frameWork_append_assoc] at h2
  unfold assignmentRight at hRestore
  exact workRunExact?_compose cnfWorkMachine
    ((1 + (((rawIndexTailLength + 1) + counter.length + 1) +
      assignment.length)) + 1)
    (literalRestoreMissingSteps assignment.length counter.length
      (Nat.succ assignment.length) rawIndexTailLength)
    _ _ _ h2 hRestore

theorem literalReturnSeekIndex_reject_run
    (alreadySatisfied positive : Bool)
    (left right : List WorkSymbol) (symbol : WorkSymbol)
    (invalid : ¬ RestoreIndexSymbol symbol) :
    workRunExact? cnfWorkMachine 1
        { state := CNFWorkState.literalReturnSeekIndex
            alreadySatisfied positive
          tape := WorkTape.focus left symbol right } =
      some
        { state := CNFWorkState.reject
          tape := WorkTape.focus left symbol right } := by
  apply cnfReject_run_one
    (CNFWorkState.literalReturnSeekIndex alreadySatisfied positive) _
    (by cases alreadySatisfied <;> cases positive <;> rfl)
  cases cnfWorkSymbolCase symbol with
  | blank => cases alreadySatisfied <;> cases positive <;> rfl
  | markFalse => cases alreadySatisfied <;> cases positive <;> rfl
  | markTrue => exact False.elim (invalid .markTrue)
  | rootGuard => cases alreadySatisfied <;> cases positive <;> rfl
  | f => exact False.elim (invalid .f)
  | sep => cases alreadySatisfied <;> cases positive <;> rfl
  | boundaryGuard => cases alreadySatisfied <;> cases positive <;> rfl
  | finish => cases alreadySatisfied <;> cases positive <;> rfl
  | t => exact False.elim (invalid .t)

theorem literalMark_inRange_badFormulaSymbol_exact
    (alreadySatisfied positive value : Bool)
    (assignmentPrefix : BitString)
    (counter formulaRest leftBase assignmentRight : List WorkSymbol)
    (bad : WorkSymbol)
    (counterAllowed : ∀ symbol, List.Mem symbol counter →
      symbol = cnfMarkFalse)
    (formulaAllowed : ∀ symbol, List.Mem symbol formulaRest →
      FormulaScanSymbol symbol)
    (badFormulaAllowed : FormulaScanSymbol bad)
    (badIndexInvalid : ¬ RestoreIndexSymbol bad) :
    workRunExact? cnfWorkMachine
        (literalMarkIterationSteps assignmentPrefix.length counter.length
          (Nat.succ formulaRest.length))
        (workConfigAtWord
          (CNFWorkState.literalIndex alreadySatisfied positive)
          (pushWorkLeft
            (List.replicate assignmentPrefix.length cnfMarkTrue)
            (cnfBoundaryGuard :: leftBase))
          (cnfT ::
            (bad ::
              (formulaRest ++
                (cnfBoundaryGuard ::
                  (counter ++
                    (cnfFinish ::
                      (markedAssignmentWorkSymbols assignmentPrefix ++
                        (assignmentValueWorkSymbol value ::
                          assignmentRight))))))))) =
      some (workConfigAtWord CNFWorkState.reject
        (pushWorkLeft
          (List.replicate (Nat.succ assignmentPrefix.length) cnfMarkTrue)
          (cnfBoundaryGuard :: leftBase))
        (bad ::
          (formulaRest ++
            (cnfBoundaryGuard ::
              (counter ++
                (cnfFinish ::
                  (markedAssignmentWorkSymbols assignmentPrefix ++
                    (markedAssignmentValueWorkSymbol value ::
                      assignmentRight)))))))) := by
  unfold literalMarkIterationSteps
  let signLeft := pushWorkLeft
    (List.replicate assignmentPrefix.length cnfMarkTrue)
    (cnfBoundaryGuard :: leftBase)
  let formulaTail := bad :: formulaRest
  let initialAssignmentTail :=
    markedAssignmentWorkSymbols assignmentPrefix ++
      (assignmentValueWorkSymbol value :: assignmentRight)
  let markedAssignmentTail :=
    markedAssignmentWorkSymbols assignmentPrefix ++
      (markedAssignmentValueWorkSymbol value :: assignmentRight)
  let initialCertificateTail := cnfBoundaryGuard ::
    (counter ++ (cnfFinish :: initialAssignmentTail))
  let markedCertificateTail := cnfBoundaryGuard ::
    (counter ++ (cnfFinish :: markedAssignmentTail))
  have tailAllowed : ∀ symbol, List.Mem symbol formulaTail →
      FormulaScanSymbol symbol := by
    intro symbol member
    unfold formulaTail at member
    cases member with
    | head => exact badFormulaAllowed
    | tail _ tailMember => exact formulaAllowed symbol tailMember
  have returnTailAllowed : ∀ symbol, List.Mem symbol formulaTail →
      RestoreSignScanSymbol symbol := by
    intro symbol member
    exact formulaScan_restoreSign symbol (tailAllowed symbol member)
  have hMarkIndex := workRunExact?_one_of_step cnfWorkMachine _ _
    (literalIndex_t_mark_step alreadySatisfied positive signLeft
      (formulaTail ++ initialCertificateTail))
  have hOut := literalIndexToAssignmentPrefix_run alreadySatisfied positive
    formulaTail counter (markedAssignmentWorkSymbols assignmentPrefix)
    (cnfMarkTrue :: signLeft) assignmentRight
    (assignmentValueWorkSymbol value) tailAllowed counterAllowed
    (markedAssignmentWorkSymbols_allowed assignmentPrefix)
  have hValue := workRunExact?_one_of_step cnfWorkMachine _ _
    (literalMarkAssignment_value_step alreadySatisfied positive value
      (pushWorkLeft (markedAssignmentWorkSymbols assignmentPrefix)
        (cnfFinish ::
          pushWorkLeft counter
            (cnfBoundaryGuard ::
              pushWorkLeft formulaTail (cnfMarkTrue :: signLeft))))
      assignmentRight)
  have hBackAssignment := literalReturnAssignment_scan
    alreadySatisfied positive assignmentPrefix
    (cnfFinish ::
      pushWorkLeft counter
        (cnfBoundaryGuard ::
          pushWorkLeft formulaTail (cnfMarkTrue :: signLeft)))
    (markedAssignmentValueWorkSymbol value :: assignmentRight)
  have hAssignmentFinish := workRunExact?_one_of_step cnfWorkMachine _ _
    (literalReturnAssignment_finish_step alreadySatisfied positive
      (pushWorkLeft counter
        (cnfBoundaryGuard ::
          pushWorkLeft formulaTail (cnfMarkTrue :: signLeft)))
      markedAssignmentTail)
  have hBackCounter := literalReturnCounter_scan alreadySatisfied positive
    counter
    (cnfBoundaryGuard ::
      pushWorkLeft formulaTail (cnfMarkTrue :: signLeft))
    (cnfFinish :: markedAssignmentTail) counterAllowed
  have hCounterBoundary := workRunExact?_one_of_step cnfWorkMachine _ _
    (literalReturnCounter_boundary_step alreadySatisfied positive
      (pushWorkLeft formulaTail (cnfMarkTrue :: signLeft))
      (counter ++ cnfFinish :: markedAssignmentTail))
  have hMarkedShape :
      pushWorkLeft
          (List.replicate (Nat.succ assignmentPrefix.length) cnfMarkTrue)
          (cnfBoundaryGuard :: leftBase) =
        cnfMarkTrue :: signLeft :=
    pushWorkLeft_replicate_markTrue_succ assignmentPrefix.length
      (cnfBoundaryGuard :: leftBase)
  rw [← hMarkedShape] at hCounterBoundary
  have hBackFormula := literalReturnSign_scan alreadySatisfied positive
    formulaTail
    (pushWorkLeft
      (List.replicate (Nat.succ assignmentPrefix.length) cnfMarkTrue)
      (cnfBoundaryGuard :: leftBase))
    markedCertificateTail returnTailAllowed
  have markedAllowed : ∀ symbol,
      List.Mem symbol
        (List.replicate (Nat.succ assignmentPrefix.length) cnfMarkTrue) →
      RestoreSignScanSymbol symbol := by
    intro symbol member
    have equal := mem_replicate_workSymbol_eq
      (Nat.succ assignmentPrefix.length) cnfMarkTrue symbol member
    cases equal
    exact .markTrue
  have hBackMarked := literalReturnSign_scan alreadySatisfied positive
    (List.replicate (Nat.succ assignmentPrefix.length) cnfMarkTrue)
    (cnfBoundaryGuard :: leftBase)
    (formulaTail ++ markedCertificateTail) markedAllowed
  rw [length_replicate_workSymbol] at hBackMarked
  have hSign := workRunExact?_one_of_step cnfWorkMachine _ _
    (literalReturnSign_boundary_step alreadySatisfied positive leftBase
      (List.replicate (Nat.succ assignmentPrefix.length) cnfMarkTrue ++
        formulaTail ++ markedCertificateTail))
  have hForwardMarked := literalReturnIndex_marked_scan
    alreadySatisfied positive (Nat.succ assignmentPrefix.length)
    (cnfBoundaryGuard :: leftBase)
    (formulaTail ++ markedCertificateTail)
  have hBad := literalReturnSeekIndex_reject_run alreadySatisfied positive
    (pushWorkLeft
      (List.replicate (Nat.succ assignmentPrefix.length) cnfMarkTrue)
      (cnfBoundaryGuard :: leftBase))
    (formulaRest ++ markedCertificateTail) bad badIndexInvalid
  have formulaTailLength : formulaTail.length = Nat.succ formulaRest.length :=
    rfl
  rw [formulaTailLength] at hOut
  rw [formulaTailLength] at hBackFormula
  rw [markedAssignmentWorkSymbols_length assignmentPrefix] at hOut
  have h1 := workRunExact?_compose cnfWorkMachine 1
    ((((Nat.succ formulaRest.length + 1) + counter.length) + 1) +
      assignmentPrefix.length) _ _ _ hMarkIndex hOut
  have h2 := workRunExact?_compose cnfWorkMachine
    (1 + ((((Nat.succ formulaRest.length + 1) + counter.length) + 1) +
      assignmentPrefix.length)) 1 _ _ _ h1 hValue
  have h3 := workRunExact?_compose cnfWorkMachine
    ((1 + ((((Nat.succ formulaRest.length + 1) + counter.length) + 1) +
      assignmentPrefix.length)) + 1) assignmentPrefix.length
    _ _ _ h2 hBackAssignment
  have h4 := workRunExact?_compose cnfWorkMachine
    (((1 + ((((Nat.succ formulaRest.length + 1) + counter.length) + 1) +
      assignmentPrefix.length)) + 1) + assignmentPrefix.length) 1
    _ _ _ h3 hAssignmentFinish
  have h5 := workRunExact?_compose cnfWorkMachine
    ((((1 + ((((Nat.succ formulaRest.length + 1) + counter.length) + 1) +
      assignmentPrefix.length)) + 1) + assignmentPrefix.length) + 1)
    counter.length _ _ _ h4 hBackCounter
  rw [← hMarkedShape] at h5
  have h6 := workRunExact?_compose cnfWorkMachine
    (((((1 + ((((Nat.succ formulaRest.length + 1) + counter.length) + 1) +
      assignmentPrefix.length)) + 1) + assignmentPrefix.length) + 1) +
      counter.length) 1 _ _ _ h5 hCounterBoundary
  have h7 := workRunExact?_compose cnfWorkMachine
    ((((((1 + ((((Nat.succ formulaRest.length + 1) + counter.length) + 1) +
      assignmentPrefix.length)) + 1) + assignmentPrefix.length) + 1) +
      counter.length) + 1) (Nat.succ formulaRest.length)
    _ _ _ h6 hBackFormula
  have h8 := workRunExact?_compose cnfWorkMachine
    (((((((1 + ((((Nat.succ formulaRest.length + 1) + counter.length) + 1) +
      assignmentPrefix.length)) + 1) + assignmentPrefix.length) + 1) +
      counter.length) + 1) + Nat.succ formulaRest.length)
    (Nat.succ assignmentPrefix.length) _ _ _ h7 hBackMarked
  rw [frameWork_append_assoc] at hSign
  have h9 := workRunExact?_compose cnfWorkMachine
    ((((((((1 + ((((Nat.succ formulaRest.length + 1) + counter.length) + 1) +
      assignmentPrefix.length)) + 1) + assignmentPrefix.length) + 1) +
      counter.length) + 1) + Nat.succ formulaRest.length) +
      Nat.succ assignmentPrefix.length) 1 _ _ _ h8 hSign
  have h10 := workRunExact?_compose cnfWorkMachine
    (((((((((1 + ((((Nat.succ formulaRest.length + 1) + counter.length) + 1) +
      assignmentPrefix.length)) + 1) + assignmentPrefix.length) + 1) +
      counter.length) + 1) + Nat.succ formulaRest.length) +
      Nat.succ assignmentPrefix.length) + 1)
    (Nat.succ assignmentPrefix.length) _ _ _ h9 hForwardMarked
  exact workRunExact?_compose cnfWorkMachine
    ((((((((((1 + ((((Nat.succ formulaRest.length + 1) + counter.length) + 1) +
      assignmentPrefix.length)) + 1) + assignmentPrefix.length) + 1) +
      counter.length) + 1) + Nat.succ formulaRest.length) +
      Nat.succ assignmentPrefix.length) + 1) +
      Nat.succ assignmentPrefix.length) 1 _ _ _ h10 hBad

theorem literalMark_inRange_sep_exact
    (alreadySatisfied positive value : Bool)
    (assignmentPrefix : BitString)
    (counter formulaRest leftBase assignmentRight : List WorkSymbol)
    (counterAllowed : ∀ symbol, List.Mem symbol counter →
      symbol = cnfMarkFalse)
    (formulaAllowed : ∀ symbol, List.Mem symbol formulaRest →
      FormulaScanSymbol symbol) :
    workRunExact? cnfWorkMachine
        (literalMarkIterationSteps assignmentPrefix.length counter.length
          (Nat.succ formulaRest.length))
        (workConfigAtWord
          (CNFWorkState.literalIndex alreadySatisfied positive)
          (pushWorkLeft
            (List.replicate assignmentPrefix.length cnfMarkTrue)
            (cnfBoundaryGuard :: leftBase))
          (cnfT ::
            (cnfSep ::
              (formulaRest ++
                (cnfBoundaryGuard ::
                  (counter ++
                    (cnfFinish ::
                      (markedAssignmentWorkSymbols assignmentPrefix ++
                        (assignmentValueWorkSymbol value ::
                          assignmentRight))))))))) =
      some (workConfigAtWord CNFWorkState.reject
        (pushWorkLeft
          (List.replicate (Nat.succ assignmentPrefix.length) cnfMarkTrue)
          (cnfBoundaryGuard :: leftBase))
        (cnfSep ::
          (formulaRest ++
            (cnfBoundaryGuard ::
              (counter ++
                (cnfFinish ::
                  (markedAssignmentWorkSymbols assignmentPrefix ++
                    (markedAssignmentValueWorkSymbol value ::
                      assignmentRight)))))))) := by
  apply literalMark_inRange_badFormulaSymbol_exact alreadySatisfied positive
    value assignmentPrefix counter formulaRest leftBase assignmentRight cnfSep
    counterAllowed formulaAllowed
  · exact .sep
  · intro allowed
    cases allowed

theorem literalMark_inRange_finish_exact
    (alreadySatisfied positive value : Bool)
    (assignmentPrefix : BitString)
    (counter formulaRest leftBase assignmentRight : List WorkSymbol)
    (counterAllowed : ∀ symbol, List.Mem symbol counter →
      symbol = cnfMarkFalse)
    (formulaAllowed : ∀ symbol, List.Mem symbol formulaRest →
      FormulaScanSymbol symbol) :
    workRunExact? cnfWorkMachine
        (literalMarkIterationSteps assignmentPrefix.length counter.length
          (Nat.succ formulaRest.length))
        (workConfigAtWord
          (CNFWorkState.literalIndex alreadySatisfied positive)
          (pushWorkLeft
            (List.replicate assignmentPrefix.length cnfMarkTrue)
            (cnfBoundaryGuard :: leftBase))
          (cnfT ::
            (cnfFinish ::
              (formulaRest ++
                (cnfBoundaryGuard ::
                  (counter ++
                    (cnfFinish ::
                      (markedAssignmentWorkSymbols assignmentPrefix ++
                        (assignmentValueWorkSymbol value ::
                          assignmentRight))))))))) =
      some (workConfigAtWord CNFWorkState.reject
        (pushWorkLeft
          (List.replicate (Nat.succ assignmentPrefix.length) cnfMarkTrue)
          (cnfBoundaryGuard :: leftBase))
        (cnfFinish ::
          (formulaRest ++
            (cnfBoundaryGuard ::
              (counter ++
                (cnfFinish ::
                  (markedAssignmentWorkSymbols assignmentPrefix ++
                    (markedAssignmentValueWorkSymbol value ::
                      assignmentRight)))))))) := by
  apply literalMark_inRange_badFormulaSymbol_exact alreadySatisfied positive
    value assignmentPrefix counter formulaRest leftBase assignmentRight
    cnfFinish counterAllowed formulaAllowed
  · exact .finish
  · intro allowed
    cases allowed

theorem literalMark_inRange_missingIndex_exact
    (alreadySatisfied positive value : Bool)
    (assignmentPrefix : BitString)
    (counter leftBase assignmentRight : List WorkSymbol)
    (counterAllowed : ∀ symbol, List.Mem symbol counter →
      symbol = cnfMarkFalse) :
    workRunExact? cnfWorkMachine
        (literalMarkIterationSteps assignmentPrefix.length counter.length 0)
        (workConfigAtWord
          (CNFWorkState.literalIndex alreadySatisfied positive)
          (pushWorkLeft
            (List.replicate assignmentPrefix.length cnfMarkTrue)
            (cnfBoundaryGuard :: leftBase))
          (cnfT ::
            (cnfBoundaryGuard ::
              (counter ++
                (cnfFinish ::
                  (markedAssignmentWorkSymbols assignmentPrefix ++
                    (assignmentValueWorkSymbol value ::
                      assignmentRight))))))) =
      some (workConfigAtWord CNFWorkState.reject
        (pushWorkLeft
          (List.replicate (Nat.succ assignmentPrefix.length) cnfMarkTrue)
          (cnfBoundaryGuard :: leftBase))
        (cnfBoundaryGuard ::
          (counter ++
            (cnfFinish ::
              (markedAssignmentWorkSymbols assignmentPrefix ++
                (markedAssignmentValueWorkSymbol value ::
                  assignmentRight)))))) := by
  unfold literalMarkIterationSteps
  let signLeft := pushWorkLeft
    (List.replicate assignmentPrefix.length cnfMarkTrue)
    (cnfBoundaryGuard :: leftBase)
  let formulaTail : List WorkSymbol := []
  let initialAssignmentTail :=
    markedAssignmentWorkSymbols assignmentPrefix ++
      (assignmentValueWorkSymbol value :: assignmentRight)
  let markedAssignmentTail :=
    markedAssignmentWorkSymbols assignmentPrefix ++
      (markedAssignmentValueWorkSymbol value :: assignmentRight)
  let initialCertificateTail := cnfBoundaryGuard ::
    (counter ++ (cnfFinish :: initialAssignmentTail))
  let markedCertificateTail := cnfBoundaryGuard ::
    (counter ++ (cnfFinish :: markedAssignmentTail))
  have tailAllowed : ∀ symbol, List.Mem symbol formulaTail →
      FormulaScanSymbol symbol := by
    intro symbol member
    unfold formulaTail at member
    contradiction
  have returnTailAllowed : ∀ symbol, List.Mem symbol formulaTail →
      RestoreSignScanSymbol symbol := by
    intro symbol member
    unfold formulaTail at member
    contradiction
  have hMarkIndex := workRunExact?_one_of_step cnfWorkMachine _ _
    (literalIndex_t_mark_step alreadySatisfied positive signLeft
      (formulaTail ++ initialCertificateTail))
  have hOut := literalIndexToAssignmentPrefix_run alreadySatisfied positive
    formulaTail counter (markedAssignmentWorkSymbols assignmentPrefix)
    (cnfMarkTrue :: signLeft) assignmentRight
    (assignmentValueWorkSymbol value) tailAllowed counterAllowed
    (markedAssignmentWorkSymbols_allowed assignmentPrefix)
  have hValue := workRunExact?_one_of_step cnfWorkMachine _ _
    (literalMarkAssignment_value_step alreadySatisfied positive value
      (pushWorkLeft (markedAssignmentWorkSymbols assignmentPrefix)
        (cnfFinish ::
          pushWorkLeft counter
            (cnfBoundaryGuard ::
              pushWorkLeft formulaTail (cnfMarkTrue :: signLeft))))
      assignmentRight)
  have hBackAssignment := literalReturnAssignment_scan
    alreadySatisfied positive assignmentPrefix
    (cnfFinish ::
      pushWorkLeft counter
        (cnfBoundaryGuard ::
          pushWorkLeft formulaTail (cnfMarkTrue :: signLeft)))
    (markedAssignmentValueWorkSymbol value :: assignmentRight)
  have hAssignmentFinish := workRunExact?_one_of_step cnfWorkMachine _ _
    (literalReturnAssignment_finish_step alreadySatisfied positive
      (pushWorkLeft counter
        (cnfBoundaryGuard ::
          pushWorkLeft formulaTail (cnfMarkTrue :: signLeft)))
      markedAssignmentTail)
  have hBackCounter := literalReturnCounter_scan alreadySatisfied positive
    counter
    (cnfBoundaryGuard ::
      pushWorkLeft formulaTail (cnfMarkTrue :: signLeft))
    (cnfFinish :: markedAssignmentTail) counterAllowed
  have hCounterBoundary := workRunExact?_one_of_step cnfWorkMachine _ _
    (literalReturnCounter_boundary_step alreadySatisfied positive
      (pushWorkLeft formulaTail (cnfMarkTrue :: signLeft))
      (counter ++ cnfFinish :: markedAssignmentTail))
  have hMarkedShape :
      pushWorkLeft
          (List.replicate (Nat.succ assignmentPrefix.length) cnfMarkTrue)
          (cnfBoundaryGuard :: leftBase) =
        cnfMarkTrue :: signLeft :=
    pushWorkLeft_replicate_markTrue_succ assignmentPrefix.length
      (cnfBoundaryGuard :: leftBase)
  rw [← hMarkedShape] at hCounterBoundary
  have hBackFormula := literalReturnSign_scan alreadySatisfied positive
    formulaTail
    (pushWorkLeft
      (List.replicate (Nat.succ assignmentPrefix.length) cnfMarkTrue)
      (cnfBoundaryGuard :: leftBase))
    markedCertificateTail returnTailAllowed
  have markedAllowed : ∀ symbol,
      List.Mem symbol
        (List.replicate (Nat.succ assignmentPrefix.length) cnfMarkTrue) →
      RestoreSignScanSymbol symbol := by
    intro symbol member
    have equal := mem_replicate_workSymbol_eq
      (Nat.succ assignmentPrefix.length) cnfMarkTrue symbol member
    cases equal
    exact .markTrue
  have hBackMarked := literalReturnSign_scan alreadySatisfied positive
    (List.replicate (Nat.succ assignmentPrefix.length) cnfMarkTrue)
    (cnfBoundaryGuard :: leftBase)
    (formulaTail ++ markedCertificateTail) markedAllowed
  rw [length_replicate_workSymbol] at hBackMarked
  have hSign := workRunExact?_one_of_step cnfWorkMachine _ _
    (literalReturnSign_boundary_step alreadySatisfied positive leftBase
      (List.replicate (Nat.succ assignmentPrefix.length) cnfMarkTrue ++
        formulaTail ++ markedCertificateTail))
  have hForwardMarked := literalReturnIndex_marked_scan
    alreadySatisfied positive (Nat.succ assignmentPrefix.length)
    (cnfBoundaryGuard :: leftBase)
    (formulaTail ++ markedCertificateTail)
  have hMissing := literalReturnSeekIndex_reject_run
    alreadySatisfied positive
    (pushWorkLeft
      (List.replicate (Nat.succ assignmentPrefix.length) cnfMarkTrue)
      (cnfBoundaryGuard :: leftBase))
    (counter ++ cnfFinish :: markedAssignmentTail)
    cnfBoundaryGuard (by
      intro allowed
      cases allowed)
  unfold formulaTail at hOut hBackFormula
  rw [markedAssignmentWorkSymbols_length assignmentPrefix] at hOut
  have h1 := workRunExact?_compose cnfWorkMachine 1
    ((((0 + 1) + counter.length) + 1) + assignmentPrefix.length)
    _ _ _ hMarkIndex hOut
  have h2 := workRunExact?_compose cnfWorkMachine
    (1 + ((((0 + 1) + counter.length) + 1) +
      assignmentPrefix.length)) 1 _ _ _ h1 hValue
  have h3 := workRunExact?_compose cnfWorkMachine
    ((1 + ((((0 + 1) + counter.length) + 1) +
      assignmentPrefix.length)) + 1) assignmentPrefix.length
    _ _ _ h2 hBackAssignment
  have h4 := workRunExact?_compose cnfWorkMachine
    (((1 + ((((0 + 1) + counter.length) + 1) +
      assignmentPrefix.length)) + 1) + assignmentPrefix.length) 1
    _ _ _ h3 hAssignmentFinish
  have h5 := workRunExact?_compose cnfWorkMachine
    ((((1 + ((((0 + 1) + counter.length) + 1) +
      assignmentPrefix.length)) + 1) + assignmentPrefix.length) + 1)
    counter.length _ _ _ h4 hBackCounter
  rw [← hMarkedShape] at h5
  have h6 := workRunExact?_compose cnfWorkMachine
    (((((1 + ((((0 + 1) + counter.length) + 1) +
      assignmentPrefix.length)) + 1) + assignmentPrefix.length) + 1) +
      counter.length) 1 _ _ _ h5 hCounterBoundary
  have h7 := workRunExact?_compose cnfWorkMachine
    ((((((1 + ((((0 + 1) + counter.length) + 1) +
      assignmentPrefix.length)) + 1) + assignmentPrefix.length) + 1) +
      counter.length) + 1) 0 _ _ _ h6 hBackFormula
  have h8 := workRunExact?_compose cnfWorkMachine
    (((((((1 + ((((0 + 1) + counter.length) + 1) +
      assignmentPrefix.length)) + 1) + assignmentPrefix.length) + 1) +
      counter.length) + 1) + 0)
    (Nat.succ assignmentPrefix.length) _ _ _ h7 hBackMarked
  rw [frameWork_append_assoc] at hSign
  have h9 := workRunExact?_compose cnfWorkMachine
    ((((((((1 + ((((0 + 1) + counter.length) + 1) +
      assignmentPrefix.length)) + 1) + assignmentPrefix.length) + 1) +
      counter.length) + 1) + 0) + Nat.succ assignmentPrefix.length)
    1 _ _ _ h8 hSign
  have h10 := workRunExact?_compose cnfWorkMachine
    (((((((((1 + ((((0 + 1) + counter.length) + 1) +
      assignmentPrefix.length)) + 1) + assignmentPrefix.length) + 1) +
      counter.length) + 1) + 0) + Nat.succ assignmentPrefix.length) + 1)
    (Nat.succ assignmentPrefix.length) _ _ _ h9 hForwardMarked
  exact workRunExact?_compose cnfWorkMachine
    ((((((((((1 + ((((0 + 1) + counter.length) + 1) +
      assignmentPrefix.length)) + 1) + assignmentPrefix.length) + 1) +
      counter.length) + 1) + 0) + Nat.succ assignmentPrefix.length) + 1) +
      Nat.succ assignmentPrefix.length) 1 _ _ _ h10 hMissing

def malformedLiteralSymbolStart
    (alreadySatisfied positive : Bool)
    (assignmentPrefix : BitString) (count : Nat)
    (remainingAssignment : BitString)
    (counter formulaRest leftBase right : List WorkSymbol)
    (bad : WorkSymbol) : WorkConfiguration :=
  workConfigAtWord (CNFWorkState.literalIndex alreadySatisfied positive)
    (pushWorkLeft
      (List.replicate assignmentPrefix.length cnfMarkTrue)
      (cnfBoundaryGuard :: leftBase))
    (List.replicate count cnfT ++
      (bad ::
        (formulaRest ++
          (cnfBoundaryGuard ::
            (counter ++
              (cnfFinish ::
                (markedAssignmentWorkSymbols assignmentPrefix ++
                  (assignmentWorkSymbols remainingAssignment ++
                    (cnfRootGuard :: right)))))))))

theorem malformedLiteralSymbol_exact
    (alreadySatisfied positive : Bool)
    (assignmentPrefix remainingAssignment : BitString)
    (count : Nat)
    (counter formulaRest leftBase right : List WorkSymbol)
    (bad : WorkSymbol)
    (counterAllowed : ∀ symbol, List.Mem symbol counter →
      symbol = cnfMarkFalse)
    (formulaAllowed : ∀ symbol, List.Mem symbol formulaRest →
      FormulaScanSymbol symbol)
    (badFormulaAllowed : FormulaScanSymbol bad)
    (badIndexInvalid : ¬ RestoreIndexSymbol bad) :
    ∃ steps tape,
      workRunExact? cnfWorkMachine steps
          (malformedLiteralSymbolStart alreadySatisfied positive
            assignmentPrefix count remainingAssignment counter formulaRest
            leftBase right bad) =
        some
          ({ state := CNFWorkState.reject, tape := tape } :
            WorkConfiguration) := by
  induction count generalizing assignmentPrefix remainingAssignment with
  | zero =>
      have literalInvalid : ¬ LiteralSignSymbol bad := by
        intro allowed
        cases allowed with
        | f => exact badIndexInvalid .f
        | t => exact badIndexInvalid .t
      let suffix := formulaRest ++
        (cnfBoundaryGuard ::
          (counter ++
            (cnfFinish ::
              (markedAssignmentWorkSymbols assignmentPrefix ++
                (assignmentWorkSymbols remainingAssignment ++
                  (cnfRootGuard :: right))))))
      have hReject := literalIndex_reject_run alreadySatisfied positive
        (pushWorkLeft
          (List.replicate assignmentPrefix.length cnfMarkTrue)
          (cnfBoundaryGuard :: leftBase))
        suffix bad literalInvalid
      refine ⟨1, (workConfigAtWord CNFWorkState.reject
        (pushWorkLeft
          (List.replicate assignmentPrefix.length cnfMarkTrue)
          (cnfBoundaryGuard :: leftBase))
        (bad :: suffix)).tape, ?_⟩
      unfold malformedLiteralSymbolStart suffix
      exact hReject
  | succ count ih =>
      cases remainingAssignment with
      | nil =>
          have hReject := literalMark_oob_badFormulaSymbol_exact
            alreadySatisfied positive assignmentPrefix counter formulaRest
            leftBase right bad count counterAllowed formulaAllowed
            badFormulaAllowed badIndexInvalid
          refine ⟨literalMarkOOBSteps assignmentPrefix.length counter.length
            formulaRest.length count,
            (workConfigAtWord CNFWorkState.reject
              (pushWorkLeft (List.replicate count cnfT)
                (pushWorkLeft
                  (List.replicate (Nat.succ assignmentPrefix.length) cnfT)
                  ((if positive then cnfT else cnfF) :: leftBase)))
              (bad ::
                (formulaRest ++
                  (cnfBoundaryGuard ::
                    (counter ++
                      (cnfFinish ::
                        (assignmentWorkSymbols assignmentPrefix ++
                          (cnfRootGuard :: right)))))))).tape, ?_⟩
          unfold malformedLiteralSymbolStart
          rw [show assignmentWorkSymbols ([] : BitString) = [] from rfl]
          exact hReject
      | cons value rest =>
          cases count with
          | zero =>
              let assignmentRight :=
                assignmentWorkSymbols rest ++ cnfRootGuard :: right
              have hReject := literalMark_inRange_badFormulaSymbol_exact
                alreadySatisfied positive value assignmentPrefix counter
                formulaRest leftBase assignmentRight bad counterAllowed
                formulaAllowed badFormulaAllowed badIndexInvalid
              refine ⟨literalMarkIterationSteps assignmentPrefix.length
                counter.length (Nat.succ formulaRest.length),
                (workConfigAtWord CNFWorkState.reject
                  (pushWorkLeft
                    (List.replicate
                      (Nat.succ assignmentPrefix.length) cnfMarkTrue)
                    (cnfBoundaryGuard :: leftBase))
                  (bad ::
                    (formulaRest ++
                      (cnfBoundaryGuard ::
                        (counter ++
                          (cnfFinish ::
                            (markedAssignmentWorkSymbols assignmentPrefix ++
                              (markedAssignmentValueWorkSymbol value ::
                                assignmentRight)))))))).tape, ?_⟩
              unfold malformedLiteralSymbolStart
              rw [assignmentWorkSymbols_cons]
              unfold assignmentRight at hReject ⊢
              repeat' rw [frameWork_append_assoc] at hReject ⊢
              exact hReject
          | succ count =>
              let laterFormula :=
                List.replicate count cnfT ++ bad :: formulaRest
              have laterAllowed : ∀ symbol,
                  List.Mem symbol laterFormula → FormulaScanSymbol symbol := by
                intro symbol member
                unfold laterFormula at member
                have split := workSymbol_mem_append_cases
                  (List.replicate count cnfT) (bad :: formulaRest)
                  symbol member
                cases split with
                | inl rawMember =>
                    have equal := mem_replicate_workSymbol_eq
                      count cnfT symbol rawMember
                    cases equal
                    exact .t
                | inr tailMember =>
                    cases tailMember with
                    | head => exact badFormulaAllowed
                    | tail _ suffixMember =>
                        exact formulaAllowed symbol suffixMember
              let assignmentRight :=
                assignmentWorkSymbols rest ++ cnfRootGuard :: right
              have iterationRun := literalMark_inRange_iteration_exact
                alreadySatisfied positive value true assignmentPrefix counter
                laterFormula leftBase assignmentRight counterAllowed laterAllowed
              let extendedPrefix := assignmentPrefix ++ [value]
              rcases ih extendedPrefix rest with
                ⟨remainingSteps, tape, remainingRun⟩
              have bridge :
                  malformedLiteralSymbolStart alreadySatisfied positive
                      extendedPrefix (Nat.succ count) rest counter formulaRest
                      leftBase right bad =
                    workConfigAtWord
                      (CNFWorkState.literalIndex alreadySatisfied positive)
                      (pushWorkLeft
                        (List.replicate
                          (Nat.succ assignmentPrefix.length) cnfMarkTrue)
                        (cnfBoundaryGuard :: leftBase))
                      (assignmentValueWorkSymbol true ::
                        (laterFormula ++
                          (cnfBoundaryGuard ::
                            (counter ++
                              (cnfFinish ::
                                (markedAssignmentWorkSymbols
                                    assignmentPrefix ++
                                  (markedAssignmentValueWorkSymbol value ::
                                    assignmentRight))))))) := by
                unfold malformedLiteralSymbolStart extendedPrefix
                rw [length_append_value assignmentPrefix value]
                rw [markedAssignment_append_value_tail assignmentPrefix value
                  (assignmentWorkSymbols rest ++ cnfRootGuard :: right)]
                unfold laterFormula assignmentRight
                repeat' rw [frameWork_append_assoc]
                rfl
              rw [bridge] at remainingRun
              have complete := workRunExact?_compose cnfWorkMachine
                (literalMarkIterationSteps assignmentPrefix.length
                  counter.length (Nat.succ laterFormula.length))
                remainingSteps _ _ _ iterationRun remainingRun
              have startBridge :
                  malformedLiteralSymbolStart alreadySatisfied positive
                      assignmentPrefix (Nat.succ (Nat.succ count))
                      (value :: rest) counter formulaRest leftBase right bad =
                    workConfigAtWord
                      (CNFWorkState.literalIndex alreadySatisfied positive)
                      (pushWorkLeft
                        (List.replicate assignmentPrefix.length cnfMarkTrue)
                        (cnfBoundaryGuard :: leftBase))
                      (cnfT ::
                        (assignmentValueWorkSymbol true ::
                          (laterFormula ++
                            (cnfBoundaryGuard ::
                              (counter ++
                                (cnfFinish ::
                                  (markedAssignmentWorkSymbols
                                      assignmentPrefix ++
                                    (assignmentValueWorkSymbol value ::
                                      assignmentRight)))))))) := by
                unfold malformedLiteralSymbolStart
                rw [assignmentWorkSymbols_cons]
                unfold laterFormula assignmentRight
                rw [List.replicate_succ]
                rw [List.replicate_succ]
                repeat' rw [frameWork_append_assoc]
                rfl
              refine ⟨literalMarkIterationSteps assignmentPrefix.length
                  counter.length (Nat.succ laterFormula.length) +
                remainingSteps, tape, ?_⟩
              rw [startBridge]
              exact complete

theorem malformedLiteralSep_exact
    (alreadySatisfied positive : Bool)
    (assignmentPrefix remainingAssignment : BitString)
    (count : Nat)
    (counter formulaRest leftBase right : List WorkSymbol)
    (counterAllowed : ∀ symbol, List.Mem symbol counter →
      symbol = cnfMarkFalse)
    (formulaAllowed : ∀ symbol, List.Mem symbol formulaRest →
      FormulaScanSymbol symbol) :
    ∃ steps tape,
      workRunExact? cnfWorkMachine steps
          (malformedLiteralSymbolStart alreadySatisfied positive
            assignmentPrefix count remainingAssignment counter formulaRest
            leftBase right cnfSep) =
        some
          ({ state := CNFWorkState.reject, tape := tape } :
            WorkConfiguration) := by
  apply malformedLiteralSymbol_exact alreadySatisfied positive
    assignmentPrefix remainingAssignment count counter formulaRest leftBase
    right cnfSep counterAllowed formulaAllowed
  · exact .sep
  · intro allowed
    cases allowed

theorem malformedLiteralFinish_exact
    (alreadySatisfied positive : Bool)
    (assignmentPrefix remainingAssignment : BitString)
    (count : Nat)
    (counter formulaRest leftBase right : List WorkSymbol)
    (counterAllowed : ∀ symbol, List.Mem symbol counter →
      symbol = cnfMarkFalse)
    (formulaAllowed : ∀ symbol, List.Mem symbol formulaRest →
      FormulaScanSymbol symbol) :
    ∃ steps tape,
      workRunExact? cnfWorkMachine steps
          (malformedLiteralSymbolStart alreadySatisfied positive
            assignmentPrefix count remainingAssignment counter formulaRest
            leftBase right cnfFinish) =
        some
          ({ state := CNFWorkState.reject, tape := tape } :
            WorkConfiguration) := by
  apply malformedLiteralSymbol_exact alreadySatisfied positive
    assignmentPrefix remainingAssignment count counter formulaRest leftBase
    right cnfFinish counterAllowed formulaAllowed
  · exact .finish
  · intro allowed
    cases allowed

def malformedLiteralMissingStart
    (alreadySatisfied positive : Bool)
    (assignmentPrefix : BitString) (count : Nat)
    (remainingAssignment : BitString)
    (counter leftBase right : List WorkSymbol) : WorkConfiguration :=
  workConfigAtWord (CNFWorkState.literalIndex alreadySatisfied positive)
    (pushWorkLeft
      (List.replicate assignmentPrefix.length cnfMarkTrue)
      (cnfBoundaryGuard :: leftBase))
    (List.replicate count cnfT ++
      (cnfBoundaryGuard ::
        (counter ++
          (cnfFinish ::
            (markedAssignmentWorkSymbols assignmentPrefix ++
              (assignmentWorkSymbols remainingAssignment ++
                (cnfRootGuard :: right)))))))

theorem malformedLiteralMissing_exact
    (alreadySatisfied positive : Bool)
    (assignmentPrefix remainingAssignment : BitString)
    (count : Nat)
    (counter leftBase right : List WorkSymbol)
    (counterAllowed : ∀ symbol, List.Mem symbol counter →
      symbol = cnfMarkFalse) :
    ∃ steps tape,
      workRunExact? cnfWorkMachine steps
          (malformedLiteralMissingStart alreadySatisfied positive
            assignmentPrefix count remainingAssignment counter leftBase
            right) =
        some
          ({ state := CNFWorkState.reject, tape := tape } :
            WorkConfiguration) := by
  induction count generalizing assignmentPrefix remainingAssignment with
  | zero =>
      have boundaryInvalid : ¬ LiteralSignSymbol cnfBoundaryGuard := by
        intro allowed
        cases allowed
      let suffix := counter ++
        (cnfFinish ::
          (markedAssignmentWorkSymbols assignmentPrefix ++
            (assignmentWorkSymbols remainingAssignment ++
              (cnfRootGuard :: right))))
      have hReject := literalIndex_reject_run alreadySatisfied positive
        (pushWorkLeft
          (List.replicate assignmentPrefix.length cnfMarkTrue)
          (cnfBoundaryGuard :: leftBase))
        suffix cnfBoundaryGuard boundaryInvalid
      refine ⟨1, (workConfigAtWord CNFWorkState.reject
        (pushWorkLeft
          (List.replicate assignmentPrefix.length cnfMarkTrue)
          (cnfBoundaryGuard :: leftBase))
        (cnfBoundaryGuard :: suffix)).tape, ?_⟩
      unfold malformedLiteralMissingStart suffix
      exact hReject
  | succ count ih =>
      cases remainingAssignment with
      | nil =>
          have hReject := literalMark_oob_missingIndex_exact
            alreadySatisfied positive assignmentPrefix counter leftBase right
            count counterAllowed
          refine ⟨literalMarkOOBMissingSteps assignmentPrefix.length
            counter.length count,
            (workConfigAtWord CNFWorkState.reject
              (pushWorkLeft (List.replicate count cnfT)
                (pushWorkLeft
                  (List.replicate (Nat.succ assignmentPrefix.length) cnfT)
                  ((if positive then cnfT else cnfF) :: leftBase)))
              (cnfBoundaryGuard ::
                (counter ++
                  (cnfFinish ::
                    (assignmentWorkSymbols assignmentPrefix ++
                      (cnfRootGuard :: right)))))).tape, ?_⟩
          unfold malformedLiteralMissingStart
          rw [show assignmentWorkSymbols ([] : BitString) = [] from rfl]
          exact hReject
      | cons value rest =>
          cases count with
          | zero =>
              let assignmentRight :=
                assignmentWorkSymbols rest ++ cnfRootGuard :: right
              have hReject := literalMark_inRange_missingIndex_exact
                alreadySatisfied positive value assignmentPrefix counter
                leftBase assignmentRight counterAllowed
              refine ⟨literalMarkIterationSteps assignmentPrefix.length
                counter.length 0,
                (workConfigAtWord CNFWorkState.reject
                  (pushWorkLeft
                    (List.replicate
                      (Nat.succ assignmentPrefix.length) cnfMarkTrue)
                    (cnfBoundaryGuard :: leftBase))
                  (cnfBoundaryGuard ::
                    (counter ++
                      (cnfFinish ::
                        (markedAssignmentWorkSymbols assignmentPrefix ++
                          (markedAssignmentValueWorkSymbol value ::
                            assignmentRight)))))).tape, ?_⟩
              unfold malformedLiteralMissingStart
              rw [assignmentWorkSymbols_cons]
              unfold assignmentRight at hReject ⊢
              repeat' rw [frameWork_append_assoc] at hReject ⊢
              exact hReject
          | succ count =>
              let laterFormula := List.replicate count cnfT
              have laterAllowed : ∀ symbol,
                  List.Mem symbol laterFormula →
                    FormulaScanSymbol symbol := by
                intro symbol member
                unfold laterFormula at member
                have equal := mem_replicate_workSymbol_eq
                  count cnfT symbol member
                cases equal
                exact .t
              let assignmentRight :=
                assignmentWorkSymbols rest ++ cnfRootGuard :: right
              have iterationRun := literalMark_inRange_iteration_exact
                alreadySatisfied positive value true assignmentPrefix counter
                laterFormula leftBase assignmentRight counterAllowed
                laterAllowed
              let extendedPrefix := assignmentPrefix ++ [value]
              rcases ih extendedPrefix rest with
                ⟨remainingSteps, tape, remainingRun⟩
              have bridge :
                  malformedLiteralMissingStart alreadySatisfied positive
                      extendedPrefix (Nat.succ count) rest counter leftBase
                      right =
                    workConfigAtWord
                      (CNFWorkState.literalIndex alreadySatisfied positive)
                      (pushWorkLeft
                        (List.replicate
                          (Nat.succ assignmentPrefix.length) cnfMarkTrue)
                        (cnfBoundaryGuard :: leftBase))
                      (assignmentValueWorkSymbol true ::
                        (laterFormula ++
                          (cnfBoundaryGuard ::
                            (counter ++
                              (cnfFinish ::
                                (markedAssignmentWorkSymbols
                                    assignmentPrefix ++
                                  (markedAssignmentValueWorkSymbol value ::
                                    assignmentRight))))))) := by
                unfold malformedLiteralMissingStart extendedPrefix
                rw [length_append_value assignmentPrefix value]
                rw [markedAssignment_append_value_tail assignmentPrefix value
                  (assignmentWorkSymbols rest ++ cnfRootGuard :: right)]
                unfold laterFormula assignmentRight
                repeat' rw [frameWork_append_assoc]
                rfl
              rw [bridge] at remainingRun
              have complete := workRunExact?_compose cnfWorkMachine
                (literalMarkIterationSteps assignmentPrefix.length
                  counter.length (Nat.succ laterFormula.length))
                remainingSteps _ _ _ iterationRun remainingRun
              have startBridge :
                  malformedLiteralMissingStart alreadySatisfied positive
                      assignmentPrefix (Nat.succ (Nat.succ count))
                      (value :: rest) counter leftBase right =
                    workConfigAtWord
                      (CNFWorkState.literalIndex alreadySatisfied positive)
                      (pushWorkLeft
                        (List.replicate assignmentPrefix.length cnfMarkTrue)
                        (cnfBoundaryGuard :: leftBase))
                      (cnfT ::
                        (assignmentValueWorkSymbol true ::
                          (laterFormula ++
                            (cnfBoundaryGuard ::
                              (counter ++
                                (cnfFinish ::
                                  (markedAssignmentWorkSymbols
                                      assignmentPrefix ++
                                    (assignmentValueWorkSymbol value ::
                                      assignmentRight)))))))) := by
                unfold malformedLiteralMissingStart
                rw [assignmentWorkSymbols_cons]
                unfold laterFormula assignmentRight
                rw [List.replicate_succ]
                rw [List.replicate_succ]
                repeat' rw [frameWork_append_assoc]
                rfl
              refine ⟨literalMarkIterationSteps assignmentPrefix.length
                  counter.length (Nat.succ laterFormula.length) +
                remainingSteps, tape, ?_⟩
              rw [startBridge]
              exact complete

end GrammarTerminalDesign

end PNP.Concrete


namespace PNP.Concrete
namespace GrammarTerminalBoundDesign

open FrameTraceDesign
open ClauseLiteralDesign
open ClauseLiteralCostDesign
open GrammarTerminalDesign

set_option maxRecDepth 100000

def literalUnitCharge (n : Nat) : Nat := cnfShiftedWorkSpan n * 12

theorem one_le_literalUnitCharge (n : Nat) :
    1 ≤ literalUnitCharge n := by
  have oneSpan : 1 ≤ cnfShiftedWorkSpan n := by
    unfold cnfShiftedWorkSpan
    change Nat.succ 0 ≤ Nat.succ (Nat.succ n)
    exact Nat.succ_le_succ (Nat.zero_le (Nat.succ n))
  have twelvePositive : 0 < 12 := Nat.zero_lt_succ 11
  unfold literalUnitCharge
  exact Nat.le_trans oneSpan
    (Nat.le_mul_of_pos_right (cnfShiftedWorkSpan n) twelvePositive)

theorem charge_plus_successor_mul (index charge : Nat) :
    charge + (index + 1) * charge =
      (Nat.succ index + 1) * charge := by
  change charge + Nat.succ index * charge =
    Nat.succ (Nat.succ index) * charge
  calc
    charge + Nat.succ index * charge =
        charge + (index * charge + charge) :=
      congrArg (Nat.add charge) (Nat.succ_mul index charge)
    _ = (index * charge + charge) + charge := by
      rw [← Nat.add_assoc]
      rw [Nat.add_comm charge (index * charge)]
    _ = Nat.succ index * charge + charge :=
      congrArg (fun x => x + charge) (Nat.succ_mul index charge).symm
    _ = Nat.succ (Nat.succ index) * charge :=
      (Nat.succ_mul (Nat.succ index) charge).symm

theorem literalMarkOOBMissingSteps_closed (a c r : Nat) :
    literalMarkOOBMissingSteps a c r =
      r + c + a + a + c + r + a + a + r + 10 := by
  unfold literalMarkOOBMissingSteps literalRestoreMissingSteps
  repeat' rw [Nat.add_succ]
  repeat' rw [Nat.succ_add]
  repeat' rw [Nat.add_assoc]
  repeat' rw [Nat.zero_add]
  repeat' rw [Nat.succ_add]
  repeat' rw [Nat.add_succ]
  repeat' rw [Nat.add_assoc]
  repeat' rw [Nat.add_zero]

theorem natAddMulClean (a b c : Nat) :
    (a + b) * c = a * c + b * c := by
  induction c with
  | zero => rfl
  | succ c ih =>
      change (a + b) * c + (a + b) =
        (a * c + a) + (b * c + b)
      rw [ih]
      exact frame_add_four_reorder (a * c) (b * c) a b

theorem nineCopies_normalize (n : Nat) :
    ((((((((n + n) + n) + n) + n) + n) + n) + n) + n) = n * 9 := by
  repeat' rw [Nat.mul_succ]
  rw [Nat.mul_zero, Nat.zero_add]

theorem nineTerms_plus_constant_le_twelveSpan
    (n constant a b c d e f g h i : Nat)
    (aBound : a ≤ n) (bBound : b ≤ n)
    (cBound : c ≤ n) (dBound : d ≤ n)
    (eBound : e ≤ n) (fBound : f ≤ n)
    (gBound : g ≤ n) (hBound : h ≤ n)
    (iBound : i ≤ n) (constantBound : constant ≤ 24) :
    ((((((((a + b) + c) + d) + e) + f) + g) + h) + i) + constant ≤
      literalUnitCharge n := by
  have h0 := Nat.add_le_add aBound bBound
  have h1 := Nat.add_le_add h0 cBound
  have h2 := Nat.add_le_add h1 dBound
  have h3 := Nat.add_le_add h2 eBound
  have h4 := Nat.add_le_add h3 fBound
  have h5 := Nat.add_le_add h4 gBound
  have h6 := Nat.add_le_add h5 hBound
  have h7 := Nat.add_le_add h6 iBound
  have nineTwelve : 9 ≤ 12 := by
    change 9 ≤ 9 + 3
    exact Nat.le_add_right 9 3
  have scaled := Nat.mul_le_mul_left n nineTwelve
  have variables :
      ((((((((a + b) + c) + d) + e) + f) + g) + h) + i) ≤
        n * 12 :=
    Nat.le_trans h7
      (Nat.le_trans (Nat.le_of_eq (nineCopies_normalize n)) scaled)
  have combined := Nat.add_le_add variables constantBound
  have normalize : n * 12 + 24 = (n + 2) * 12 :=
    (natAddMulClean n 2 12).symm
  unfold literalUnitCharge cnfShiftedWorkSpan
  exact Nat.le_trans combined (Nat.le_of_eq normalize)

theorem literalMarkOOBMissingSteps_le_unitCharge
    (n assignmentLength counterLength rawIndexTailLength : Nat)
    (assignmentBound : assignmentLength ≤ n)
    (counterBound : counterLength ≤ n)
    (rawIndexBound : rawIndexTailLength ≤ n) :
    literalMarkOOBMissingSteps assignmentLength counterLength
        rawIndexTailLength ≤ literalUnitCharge n := by
  rw [literalMarkOOBMissingSteps_closed]
  apply nineTerms_plus_constant_le_twelveSpan n 10
  · exact rawIndexBound
  · exact counterBound
  · exact assignmentBound
  · exact assignmentBound
  · exact counterBound
  · exact rawIndexBound
  · exact assignmentBound
  · exact assignmentBound
  · exact rawIndexBound
  · change 10 ≤ 10 + 14
    exact Nat.le_add_right 10 14

def malformedLiteralSymbolStepCount
    (assignmentPrefix remainingAssignment : BitString)
    (counter formulaRest : List WorkSymbol) (bad : WorkSymbol) : Nat → Nat
  | 0 => 1
  | Nat.succ count =>
      match remainingAssignment with
      | [] => literalMarkOOBSteps assignmentPrefix.length counter.length
          formulaRest.length count
      | value :: rest =>
          match count with
          | 0 => literalMarkIterationSteps assignmentPrefix.length
              counter.length (Nat.succ formulaRest.length)
          | Nat.succ count =>
              let laterFormula :=
                List.replicate count cnfT ++ bad :: formulaRest
              literalMarkIterationSteps assignmentPrefix.length
                  counter.length (Nat.succ laterFormula.length) +
                malformedLiteralSymbolStepCount
                  (assignmentPrefix ++ [value]) rest counter formulaRest bad
                  (Nat.succ count)

theorem malformedLiteralSymbol_counted_exact
    (alreadySatisfied positive : Bool)
    (assignmentPrefix remainingAssignment : BitString)
    (count : Nat)
    (counter formulaRest leftBase right : List WorkSymbol)
    (bad : WorkSymbol)
    (counterAllowed : ∀ symbol, List.Mem symbol counter →
      symbol = cnfMarkFalse)
    (formulaAllowed : ∀ symbol, List.Mem symbol formulaRest →
      FormulaScanSymbol symbol)
    (badFormulaAllowed : FormulaScanSymbol bad)
    (badIndexInvalid : ¬ RestoreIndexSymbol bad) :
    ∃ tape,
      workRunExact? cnfWorkMachine
          (malformedLiteralSymbolStepCount assignmentPrefix
            remainingAssignment counter formulaRest bad count)
          (malformedLiteralSymbolStart alreadySatisfied positive
            assignmentPrefix count remainingAssignment counter formulaRest
            leftBase right bad) =
        some ({ state := CNFWorkState.reject, tape := tape } :
          WorkConfiguration) := by
  induction count generalizing assignmentPrefix remainingAssignment with
  | zero =>
      have literalInvalid : ¬ LiteralSignSymbol bad := by
        intro allowed
        cases allowed with
        | f => exact badIndexInvalid .f
        | t => exact badIndexInvalid .t
      let suffix := formulaRest ++
        (cnfBoundaryGuard ::
          (counter ++
            (cnfFinish ::
              (markedAssignmentWorkSymbols assignmentPrefix ++
                (assignmentWorkSymbols remainingAssignment ++
                  (cnfRootGuard :: right))))))
      have hReject := literalIndex_reject_run alreadySatisfied positive
        (pushWorkLeft
          (List.replicate assignmentPrefix.length cnfMarkTrue)
          (cnfBoundaryGuard :: leftBase)) suffix bad literalInvalid
      refine ⟨(workConfigAtWord CNFWorkState.reject
        (pushWorkLeft
          (List.replicate assignmentPrefix.length cnfMarkTrue)
          (cnfBoundaryGuard :: leftBase))
        (bad :: suffix)).tape, ?_⟩
      unfold malformedLiteralSymbolStepCount malformedLiteralSymbolStart
        suffix
      exact hReject
  | succ count ih =>
      cases remainingAssignment with
      | nil =>
          have hReject := literalMark_oob_badFormulaSymbol_exact
            alreadySatisfied positive assignmentPrefix counter formulaRest
            leftBase right bad count counterAllowed formulaAllowed
            badFormulaAllowed badIndexInvalid
          refine ⟨(workConfigAtWord CNFWorkState.reject
            (pushWorkLeft (List.replicate count cnfT)
              (pushWorkLeft
                (List.replicate (Nat.succ assignmentPrefix.length) cnfT)
                ((if positive then cnfT else cnfF) :: leftBase)))
            (bad ::
              (formulaRest ++
                (cnfBoundaryGuard ::
                  (counter ++
                    (cnfFinish ::
                      (assignmentWorkSymbols assignmentPrefix ++
                        (cnfRootGuard :: right)))))))).tape, ?_⟩
          unfold malformedLiteralSymbolStepCount
          unfold malformedLiteralSymbolStart
          rw [show assignmentWorkSymbols ([] : BitString) = [] from rfl]
          exact hReject
      | cons value rest =>
          cases count with
          | zero =>
              let assignmentRight :=
                assignmentWorkSymbols rest ++ cnfRootGuard :: right
              have hReject := literalMark_inRange_badFormulaSymbol_exact
                alreadySatisfied positive value assignmentPrefix counter
                formulaRest leftBase assignmentRight bad counterAllowed
                formulaAllowed badFormulaAllowed badIndexInvalid
              refine ⟨(workConfigAtWord CNFWorkState.reject
                (pushWorkLeft
                  (List.replicate
                    (Nat.succ assignmentPrefix.length) cnfMarkTrue)
                  (cnfBoundaryGuard :: leftBase))
                (bad ::
                  (formulaRest ++
                    (cnfBoundaryGuard ::
                      (counter ++
                        (cnfFinish ::
                          (markedAssignmentWorkSymbols assignmentPrefix ++
                            (markedAssignmentValueWorkSymbol value ::
                              assignmentRight)))))))).tape, ?_⟩
              unfold malformedLiteralSymbolStepCount
              unfold malformedLiteralSymbolStart
              rw [assignmentWorkSymbols_cons]
              unfold assignmentRight at hReject ⊢
              repeat' rw [frameWork_append_assoc] at hReject ⊢
              exact hReject
          | succ count =>
              let laterFormula :=
                List.replicate count cnfT ++ bad :: formulaRest
              have laterAllowed : ∀ symbol,
                  List.Mem symbol laterFormula →
                    FormulaScanSymbol symbol := by
                intro symbol member
                unfold laterFormula at member
                have split := workSymbol_mem_append_cases
                  (List.replicate count cnfT) (bad :: formulaRest)
                  symbol member
                cases split with
                | inl rawMember =>
                    have equal := mem_replicate_workSymbol_eq
                      count cnfT symbol rawMember
                    cases equal
                    exact .t
                | inr tailMember =>
                    cases tailMember with
                    | head => exact badFormulaAllowed
                    | tail _ suffixMember =>
                        exact formulaAllowed symbol suffixMember
              let assignmentRight :=
                assignmentWorkSymbols rest ++ cnfRootGuard :: right
              have iterationRun := literalMark_inRange_iteration_exact
                alreadySatisfied positive value true assignmentPrefix counter
                laterFormula leftBase assignmentRight counterAllowed
                laterAllowed
              let extendedPrefix := assignmentPrefix ++ [value]
              rcases ih extendedPrefix rest with ⟨tape, remainingRun⟩
              have bridge :
                  malformedLiteralSymbolStart alreadySatisfied positive
                      extendedPrefix (Nat.succ count) rest counter formulaRest
                      leftBase right bad =
                    workConfigAtWord
                      (CNFWorkState.literalIndex alreadySatisfied positive)
                      (pushWorkLeft
                        (List.replicate
                          (Nat.succ assignmentPrefix.length) cnfMarkTrue)
                        (cnfBoundaryGuard :: leftBase))
                      (assignmentValueWorkSymbol true ::
                        (laterFormula ++
                          (cnfBoundaryGuard ::
                            (counter ++
                              (cnfFinish ::
                                (markedAssignmentWorkSymbols
                                    assignmentPrefix ++
                                  (markedAssignmentValueWorkSymbol value ::
                                    assignmentRight))))))) := by
                unfold malformedLiteralSymbolStart extendedPrefix
                rw [length_append_value assignmentPrefix value]
                rw [markedAssignment_append_value_tail assignmentPrefix value
                  (assignmentWorkSymbols rest ++ cnfRootGuard :: right)]
                unfold laterFormula assignmentRight
                repeat' rw [frameWork_append_assoc]
                rfl
              rw [bridge] at remainingRun
              have complete := workRunExact?_compose cnfWorkMachine
                (literalMarkIterationSteps assignmentPrefix.length
                  counter.length (Nat.succ laterFormula.length))
                (malformedLiteralSymbolStepCount extendedPrefix rest counter
                  formulaRest bad (Nat.succ count))
                _ _ _ iterationRun remainingRun
              have startBridge :
                  malformedLiteralSymbolStart alreadySatisfied positive
                      assignmentPrefix (Nat.succ (Nat.succ count))
                      (value :: rest) counter formulaRest leftBase right bad =
                    workConfigAtWord
                      (CNFWorkState.literalIndex alreadySatisfied positive)
                      (pushWorkLeft
                        (List.replicate assignmentPrefix.length cnfMarkTrue)
                        (cnfBoundaryGuard :: leftBase))
                      (cnfT ::
                        (assignmentValueWorkSymbol true ::
                          (laterFormula ++
                            (cnfBoundaryGuard ::
                              (counter ++
                                (cnfFinish ::
                                  (markedAssignmentWorkSymbols
                                      assignmentPrefix ++
                                    (assignmentValueWorkSymbol value ::
                                      assignmentRight)))))))) := by
                unfold malformedLiteralSymbolStart
                rw [assignmentWorkSymbols_cons]
                unfold laterFormula assignmentRight
                rw [List.replicate_succ]
                rw [List.replicate_succ]
                repeat' rw [frameWork_append_assoc]
                rfl
              refine ⟨tape, ?_⟩
              unfold malformedLiteralSymbolStepCount
              unfold laterFormula at complete
              rw [startBridge]
              exact complete

theorem malformedLiteralSymbolStepCount_le_charge
    (n : Nat) (assignmentPrefix remainingAssignment : BitString)
    (counter formulaRest : List WorkSymbol) (bad : WorkSymbol)
    (count : Nat)
    (assignmentBound :
      assignmentPrefix.length + remainingAssignment.length ≤ n)
    (counterBound : counter.length ≤ n)
    (formulaBound : count + 1 + formulaRest.length ≤ n) :
    malformedLiteralSymbolStepCount assignmentPrefix remainingAssignment
        counter formulaRest bad count ≤
      (count + 1) * literalUnitCharge n := by
  induction count generalizing assignmentPrefix remainingAssignment with
  | zero =>
      unfold malformedLiteralSymbolStepCount
      rw [Nat.one_mul]
      exact one_le_literalUnitCharge n
  | succ count ih =>
      cases remainingAssignment with
      | nil =>
          unfold malformedLiteralSymbolStepCount
          have prefixBound : assignmentPrefix.length ≤ n :=
            Nat.le_trans
              (Nat.le_add_right assignmentPrefix.length 0)
              assignmentBound
          have formulaRestBound : formulaRest.length ≤ n :=
            Nat.le_trans
              (Nat.le_add_left formulaRest.length (Nat.succ count + 1))
              formulaBound
          have countBound : count ≤ n :=
            Nat.le_trans (Nat.le_succ count)
              (Nat.le_trans
                (Nat.le_add_right (Nat.succ count) 1)
                (Nat.le_trans
                  (Nat.le_add_right (Nat.succ count + 1)
                    formulaRest.length)
                  formulaBound))
          have primitiveBound := literalMarkOOBSteps_le_unitCharge n
            assignmentPrefix.length counter.length formulaRest.length count
            prefixBound counterBound formulaRestBound countBound
          exact Nat.le_trans primitiveBound
            (Nat.le_mul_of_pos_left (literalUnitCharge n)
              (Nat.zero_lt_succ (Nat.succ count)))
      | cons value rest =>
          cases count with
          | zero =>
              unfold malformedLiteralSymbolStepCount
              have prefixBound : assignmentPrefix.length ≤ n :=
                Nat.le_trans
                  (Nat.le_add_right assignmentPrefix.length
                    (value :: rest).length)
                  assignmentBound
              have tailBound : Nat.succ formulaRest.length ≤ n := by
                change 1 + 1 + formulaRest.length ≤ n at formulaBound
                rw [Nat.add_comm (1 + 1) formulaRest.length] at formulaBound
                change Nat.succ (Nat.succ formulaRest.length) ≤ n at formulaBound
                exact Nat.le_trans (Nat.le_succ (Nat.succ formulaRest.length))
                  formulaBound
              have primitiveBound := literalMarkIterationSteps_le_unitCharge
                n assignmentPrefix.length counter.length
                (Nat.succ formulaRest.length) prefixBound counterBound
                tailBound
              exact Nat.le_trans primitiveBound
                (Nat.le_mul_of_pos_left (literalUnitCharge n)
                  (Nat.zero_lt_succ 1))
          | succ count =>
              let laterFormula :=
                List.replicate count cnfT ++ bad :: formulaRest
              have prefixBound : assignmentPrefix.length ≤ n :=
                Nat.le_trans
                  (Nat.le_add_right assignmentPrefix.length
                    (value :: rest).length)
                  assignmentBound
              have extendedAssignmentBound :
                  (assignmentPrefix ++ [value]).length + rest.length ≤
                    n := by
                change assignmentPrefix.length + Nat.succ rest.length ≤ n
                  at assignmentBound
                rw [Nat.add_succ] at assignmentBound
                rw [length_append_value, Nat.succ_add]
                exact assignmentBound
              have recursiveFormulaBound :
                  Nat.succ count + 1 + formulaRest.length ≤ n := by
                apply Nat.le_trans _ formulaBound
                exact Nat.add_le_add_right
                  (Nat.add_le_add_right (Nat.le_succ (Nat.succ count)) 1)
                  formulaRest.length
              have laterFormulaBound : Nat.succ laterFormula.length ≤ n := by
                unfold laterFormula
                rw [workSymbol_length_append, workSymbol_replicate_length,
                  List.length_cons]
                change Nat.succ (count + Nat.succ formulaRest.length) ≤ n
                apply Nat.le_trans _ formulaBound
                rw [Nat.add_succ]
                rw [Nat.succ_add]
                have base : count + formulaRest.length ≤
                    count + formulaRest.length + 1 :=
                  Nat.le_add_right (count + formulaRest.length) 1
                have twice := Nat.succ_le_succ (Nat.succ_le_succ base)
                rw [Nat.add_assoc count 2 formulaRest.length]
                rw [Nat.add_comm 2 formulaRest.length]
                rw [← Nat.add_assoc count formulaRest.length 2]
                exact twice
              have iterationBound := literalMarkIterationSteps_le_unitCharge
                n assignmentPrefix.length counter.length
                (Nat.succ laterFormula.length) prefixBound counterBound
                laterFormulaBound
              have recursiveBound := ih (assignmentPrefix ++ [value]) rest
                extendedAssignmentBound recursiveFormulaBound
              unfold malformedLiteralSymbolStepCount
              exact Nat.le_trans
                (Nat.add_le_add iterationBound recursiveBound)
                (Nat.le_of_eq
                  (charge_plus_successor_mul (Nat.succ count)
                    (literalUnitCharge n)))

def malformedLiteralMissingStepCount
    (assignmentPrefix remainingAssignment : BitString)
    (counter : List WorkSymbol) : Nat → Nat
  | 0 => 1
  | Nat.succ count =>
      match remainingAssignment with
      | [] => literalMarkOOBMissingSteps assignmentPrefix.length
          counter.length count
      | value :: rest =>
          match count with
          | 0 => literalMarkIterationSteps assignmentPrefix.length
              counter.length 0
          | Nat.succ count =>
              let laterFormula := List.replicate count cnfT
              literalMarkIterationSteps assignmentPrefix.length
                  counter.length (Nat.succ laterFormula.length) +
                malformedLiteralMissingStepCount
                  (assignmentPrefix ++ [value]) rest counter
                  (Nat.succ count)

theorem malformedLiteralMissing_counted_exact
    (alreadySatisfied positive : Bool)
    (assignmentPrefix remainingAssignment : BitString)
    (count : Nat) (counter leftBase right : List WorkSymbol)
    (counterAllowed : ∀ symbol, List.Mem symbol counter →
      symbol = cnfMarkFalse) :
    ∃ tape,
      workRunExact? cnfWorkMachine
          (malformedLiteralMissingStepCount assignmentPrefix
            remainingAssignment counter count)
          (malformedLiteralMissingStart alreadySatisfied positive
            assignmentPrefix count remainingAssignment counter leftBase
            right) =
        some ({ state := CNFWorkState.reject, tape := tape } :
          WorkConfiguration) := by
  induction count generalizing assignmentPrefix remainingAssignment with
  | zero =>
      have boundaryInvalid : ¬ LiteralSignSymbol cnfBoundaryGuard := by
        intro allowed
        cases allowed
      let suffix := counter ++
        (cnfFinish ::
          (markedAssignmentWorkSymbols assignmentPrefix ++
            (assignmentWorkSymbols remainingAssignment ++
              (cnfRootGuard :: right))))
      have hReject := literalIndex_reject_run alreadySatisfied positive
        (pushWorkLeft
          (List.replicate assignmentPrefix.length cnfMarkTrue)
          (cnfBoundaryGuard :: leftBase))
        suffix cnfBoundaryGuard boundaryInvalid
      refine ⟨(workConfigAtWord CNFWorkState.reject
        (pushWorkLeft
          (List.replicate assignmentPrefix.length cnfMarkTrue)
          (cnfBoundaryGuard :: leftBase))
        (cnfBoundaryGuard :: suffix)).tape, ?_⟩
      unfold malformedLiteralMissingStepCount malformedLiteralMissingStart
        suffix
      exact hReject
  | succ count ih =>
      cases remainingAssignment with
      | nil =>
          have hReject := literalMark_oob_missingIndex_exact
            alreadySatisfied positive assignmentPrefix counter leftBase right
            count counterAllowed
          refine ⟨(workConfigAtWord CNFWorkState.reject
            (pushWorkLeft (List.replicate count cnfT)
              (pushWorkLeft
                (List.replicate (Nat.succ assignmentPrefix.length) cnfT)
                ((if positive then cnfT else cnfF) :: leftBase)))
            (cnfBoundaryGuard ::
              (counter ++
                (cnfFinish ::
                  (assignmentWorkSymbols assignmentPrefix ++
                    (cnfRootGuard :: right)))))).tape, ?_⟩
          unfold malformedLiteralMissingStepCount
          unfold malformedLiteralMissingStart
          rw [show assignmentWorkSymbols ([] : BitString) = [] from rfl]
          exact hReject
      | cons value rest =>
          cases count with
          | zero =>
              let assignmentRight :=
                assignmentWorkSymbols rest ++ cnfRootGuard :: right
              have hReject := literalMark_inRange_missingIndex_exact
                alreadySatisfied positive value assignmentPrefix counter
                leftBase assignmentRight counterAllowed
              refine ⟨(workConfigAtWord CNFWorkState.reject
                (pushWorkLeft
                  (List.replicate
                    (Nat.succ assignmentPrefix.length) cnfMarkTrue)
                  (cnfBoundaryGuard :: leftBase))
                (cnfBoundaryGuard ::
                  (counter ++
                    (cnfFinish ::
                      (markedAssignmentWorkSymbols assignmentPrefix ++
                        (markedAssignmentValueWorkSymbol value ::
                          assignmentRight)))))).tape, ?_⟩
              unfold malformedLiteralMissingStepCount
              unfold malformedLiteralMissingStart
              rw [assignmentWorkSymbols_cons]
              unfold assignmentRight at hReject ⊢
              repeat' rw [frameWork_append_assoc] at hReject ⊢
              exact hReject
          | succ count =>
              let laterFormula := List.replicate count cnfT
              have laterAllowed : ∀ symbol,
                  List.Mem symbol laterFormula →
                    FormulaScanSymbol symbol := by
                intro symbol member
                unfold laterFormula at member
                have equal := mem_replicate_workSymbol_eq
                  count cnfT symbol member
                cases equal
                exact .t
              let assignmentRight :=
                assignmentWorkSymbols rest ++ cnfRootGuard :: right
              have iterationRun := literalMark_inRange_iteration_exact
                alreadySatisfied positive value true assignmentPrefix counter
                laterFormula leftBase assignmentRight counterAllowed
                laterAllowed
              let extendedPrefix := assignmentPrefix ++ [value]
              rcases ih extendedPrefix rest with ⟨tape, remainingRun⟩
              have bridge :
                  malformedLiteralMissingStart alreadySatisfied positive
                      extendedPrefix (Nat.succ count) rest counter leftBase
                      right =
                    workConfigAtWord
                      (CNFWorkState.literalIndex alreadySatisfied positive)
                      (pushWorkLeft
                        (List.replicate
                          (Nat.succ assignmentPrefix.length) cnfMarkTrue)
                        (cnfBoundaryGuard :: leftBase))
                      (assignmentValueWorkSymbol true ::
                        (laterFormula ++
                          (cnfBoundaryGuard ::
                            (counter ++
                              (cnfFinish ::
                                (markedAssignmentWorkSymbols
                                    assignmentPrefix ++
                                  (markedAssignmentValueWorkSymbol value ::
                                    assignmentRight))))))) := by
                unfold malformedLiteralMissingStart extendedPrefix
                rw [length_append_value assignmentPrefix value]
                rw [markedAssignment_append_value_tail assignmentPrefix value
                  (assignmentWorkSymbols rest ++ cnfRootGuard :: right)]
                unfold laterFormula assignmentRight
                repeat' rw [frameWork_append_assoc]
                rfl
              rw [bridge] at remainingRun
              have complete := workRunExact?_compose cnfWorkMachine
                (literalMarkIterationSteps assignmentPrefix.length
                  counter.length (Nat.succ laterFormula.length))
                (malformedLiteralMissingStepCount extendedPrefix rest counter
                  (Nat.succ count)) _ _ _ iterationRun remainingRun
              have startBridge :
                  malformedLiteralMissingStart alreadySatisfied positive
                      assignmentPrefix (Nat.succ (Nat.succ count))
                      (value :: rest) counter leftBase right =
                    workConfigAtWord
                      (CNFWorkState.literalIndex alreadySatisfied positive)
                      (pushWorkLeft
                        (List.replicate assignmentPrefix.length cnfMarkTrue)
                        (cnfBoundaryGuard :: leftBase))
                      (cnfT ::
                        (assignmentValueWorkSymbol true ::
                          (laterFormula ++
                            (cnfBoundaryGuard ::
                              (counter ++
                                (cnfFinish ::
                                  (markedAssignmentWorkSymbols
                                      assignmentPrefix ++
                                    (assignmentValueWorkSymbol value ::
                                      assignmentRight)))))))) := by
                unfold malformedLiteralMissingStart
                rw [assignmentWorkSymbols_cons]
                unfold laterFormula assignmentRight
                rw [List.replicate_succ]
                rw [List.replicate_succ]
                repeat' rw [frameWork_append_assoc]
                rfl
              refine ⟨tape, ?_⟩
              unfold malformedLiteralMissingStepCount
              unfold laterFormula at complete
              rw [startBridge]
              exact complete

theorem malformedLiteralMissingStepCount_le_charge
    (n : Nat) (assignmentPrefix remainingAssignment : BitString)
    (counter : List WorkSymbol) (count : Nat)
    (assignmentBound :
      assignmentPrefix.length + remainingAssignment.length ≤ n)
    (counterBound : counter.length ≤ n)
    (formulaBound : count ≤ n) :
    malformedLiteralMissingStepCount assignmentPrefix remainingAssignment
        counter count ≤
      (count + 1) * literalUnitCharge n := by
  induction count generalizing assignmentPrefix remainingAssignment with
  | zero =>
      unfold malformedLiteralMissingStepCount
      rw [Nat.one_mul]
      exact one_le_literalUnitCharge n
  | succ count ih =>
      cases remainingAssignment with
      | nil =>
          unfold malformedLiteralMissingStepCount
          have prefixBound : assignmentPrefix.length ≤ n :=
            Nat.le_trans
              (Nat.le_add_right assignmentPrefix.length 0)
              assignmentBound
          have countBound : count ≤ n :=
            Nat.le_trans (Nat.le_succ count) formulaBound
          have primitiveBound := literalMarkOOBMissingSteps_le_unitCharge n
            assignmentPrefix.length counter.length count prefixBound
            counterBound countBound
          exact Nat.le_trans primitiveBound
            (Nat.le_mul_of_pos_left (literalUnitCharge n)
              (Nat.zero_lt_succ (Nat.succ count)))
      | cons value rest =>
          cases count with
          | zero =>
              unfold malformedLiteralMissingStepCount
              have prefixBound : assignmentPrefix.length ≤ n :=
                Nat.le_trans
                  (Nat.le_add_right assignmentPrefix.length
                    (value :: rest).length)
                  assignmentBound
              have zeroBound : 0 ≤ n := Nat.zero_le n
              have primitiveBound := literalMarkIterationSteps_le_unitCharge
                n assignmentPrefix.length counter.length 0 prefixBound
                counterBound zeroBound
              exact Nat.le_trans primitiveBound
                (Nat.le_mul_of_pos_left (literalUnitCharge n)
                  (Nat.zero_lt_succ 1))
          | succ count =>
              let laterFormula := List.replicate count cnfT
              have prefixBound : assignmentPrefix.length ≤ n :=
                Nat.le_trans
                  (Nat.le_add_right assignmentPrefix.length
                    (value :: rest).length)
                  assignmentBound
              have extendedAssignmentBound :
                  (assignmentPrefix ++ [value]).length + rest.length ≤
                    n := by
                change assignmentPrefix.length + Nat.succ rest.length ≤ n
                  at assignmentBound
                rw [Nat.add_succ] at assignmentBound
                rw [length_append_value, Nat.succ_add]
                exact assignmentBound
              have recursiveFormulaBound : Nat.succ count ≤ n :=
                Nat.le_trans (Nat.le_succ (Nat.succ count)) formulaBound
              have laterFormulaBound : Nat.succ laterFormula.length ≤ n := by
                unfold laterFormula
                rw [workSymbol_replicate_length]
                exact Nat.le_trans (Nat.le_succ (Nat.succ count)) formulaBound
              have iterationBound := literalMarkIterationSteps_le_unitCharge
                n assignmentPrefix.length counter.length
                (Nat.succ laterFormula.length) prefixBound counterBound
                laterFormulaBound
              have recursiveBound := ih (assignmentPrefix ++ [value]) rest
                extendedAssignmentBound recursiveFormulaBound
              unfold malformedLiteralMissingStepCount
              exact Nat.le_trans
                (Nat.add_le_add iterationBound recursiveBound)
                (Nat.le_of_eq
                  (charge_plus_successor_mul (Nat.succ count)
                    (literalUnitCharge n)))

end GrammarTerminalBoundDesign
end PNP.Concrete


namespace PNP.Concrete

namespace GrammarClauseDesign

open FrameTraceDesign
open ClauseLiteralDesign
open ClauseLiteralCostDesign
open GrammarFailureDesign
open GrammarTerminalDesign

set_option maxRecDepth 100000

inductive FormulaGrammarControl : FormulaGrammarMode → Type where
  | clauses : FormulaGrammarControl .clauses
  | clauseNeed : FormulaGrammarControl .clause
  | clauseContinue (alreadySatisfied : Bool) :
      FormulaGrammarControl .clause
  | literal (alreadySatisfied positive : Bool) (index : Nat) :
      FormulaGrammarControl (.literal positive index)

def grammarCertificateTail (assignment : BitString)
    (counter right : List WorkSymbol) : List WorkSymbol :=
  cnfBoundaryGuard ::
    (counter ++
      (cnfFinish ::
        (assignmentWorkSymbols assignment ++ (cnfRootGuard :: right))))

def formulaGrammarFailureStart {mode : FormulaGrammarMode}
    (control : FormulaGrammarControl mode) (tokens : List CNFToken)
    (assignment : BitString) (counter left right : List WorkSymbol) :
    WorkConfiguration :=
  match control with
  | .clauses =>
      workConfigAtWord CNFWorkState.clauseStart left
        (cnfTokenWorkSymbols tokens ++
          grammarCertificateTail assignment counter right)
  | .clauseNeed =>
      workConfigAtWord CNFWorkState.clauseNeedLiteral left
        (cnfTokenWorkSymbols tokens ++
          grammarCertificateTail assignment counter right)
  | .clauseContinue alreadySatisfied =>
      workConfigAtWord (CNFWorkState.clauseContinue alreadySatisfied) left
        (cnfTokenWorkSymbols tokens ++
          grammarCertificateTail assignment counter right)
  | .literal alreadySatisfied positive index =>
      workConfigAtWord
        (CNFWorkState.literalIndex alreadySatisfied positive)
        (cnfBoundaryGuard :: left)
        (List.replicate index cnfT ++
          (cnfTokenWorkSymbols tokens ++
            grammarCertificateTail assignment counter right))

theorem formulaGrammarFailure_machine_exact
    {mode : FormulaGrammarMode} {tokens : List CNFToken}
    (failure : FormulaGrammarFailure mode tokens) :
    ∀ (control : FormulaGrammarControl mode)
      (assignment : BitString) (counter left right : List WorkSymbol),
      (∀ symbol, List.Mem symbol counter → symbol = cnfMarkFalse) →
      ∃ steps tape,
        workRunExact? cnfWorkMachine steps
            (formulaGrammarFailureStart control tokens assignment counter
              left right) =
          some
            ({ state := CNFWorkState.reject, tape := tape } :
              WorkConfiguration) := by
  induction failure with
  | headerEmpty count =>
      intro control
      cases control
  | headerSep count rest =>
      intro control
      cases control
  | headerFinish count rest =>
      intro control
      cases control
  | headerT tail ih =>
      intro control
      cases control
  | headerF tail ih =>
      intro control
      cases control
  | clausesEmpty =>
      intro control assignment counter left right counterAllowed
      cases control with
      | clauses =>
          have invalid : ¬ ClauseStartSymbol cnfBoundaryGuard := by
            intro allowed
            cases allowed
          have hReject := clauseStart_reject_run left
            (counter ++
              (cnfFinish ::
                (assignmentWorkSymbols assignment ++
                  (cnfRootGuard :: right))))
            cnfBoundaryGuard invalid
          refine ⟨1, (workConfigAtWord CNFWorkState.reject left
            (grammarCertificateTail assignment counter right)).tape, ?_⟩
          unfold formulaGrammarFailureStart grammarCertificateTail
          exact hReject
  | clausesF rest =>
      intro control assignment counter left right counterAllowed
      cases control with
      | clauses =>
          have invalid : ¬ ClauseStartSymbol cnfF := by
            intro allowed
            cases allowed
          let suffix := cnfTokenWorkSymbols rest ++
            grammarCertificateTail assignment counter right
          have hReject := clauseStart_reject_run left suffix cnfF invalid
          refine ⟨1, (workConfigAtWord CNFWorkState.reject left
            (cnfF :: suffix)).tape, ?_⟩
          unfold formulaGrammarFailureStart
          exact hReject
  | clausesT rest =>
      intro control assignment counter left right counterAllowed
      cases control with
      | clauses =>
          have invalid : ¬ ClauseStartSymbol cnfT := by
            intro allowed
            cases allowed
          let suffix := cnfTokenWorkSymbols rest ++
            grammarCertificateTail assignment counter right
          have hReject := clauseStart_reject_run left suffix cnfT invalid
          refine ⟨1, (workConfigAtWord CNFWorkState.reject left
            (cnfT :: suffix)).tape, ?_⟩
          unfold formulaGrammarFailureStart
          exact hReject
  | @clausesSep rest tail ih =>
      intro control assignment counter left right counterAllowed
      cases control with
      | clauses =>
          let suffix := cnfTokenWorkSymbols rest ++
            grammarCertificateTail assignment counter right
          have separatorRun := workRunExact?_one_of_step cnfWorkMachine _ _
            (clauseStart_separator_step left suffix)
          rcases ih FormulaGrammarControl.clauseNeed assignment counter
              (cnfSep :: left) right counterAllowed with
            ⟨remainingSteps, tape, remainingRun⟩
          unfold formulaGrammarFailureStart at remainingRun
          unfold suffix at separatorRun
          have complete := workRunExact?_compose cnfWorkMachine 1
            remainingSteps _ _ _ separatorRun remainingRun
          refine ⟨1 + remainingSteps, tape, ?_⟩
          unfold formulaGrammarFailureStart
          exact complete
  | clausesFinishTrailing next rest =>
      intro control assignment counter left right counterAllowed
      cases control with
      | clauses =>
          let suffix := cnfTokenWorkSymbols rest ++
            grammarCertificateTail assignment counter right
          have finishRun := workRunExact?_one_of_step cnfWorkMachine _ _
            (clauseStart_formulaFinish_step left
              (next.workSymbol :: suffix))
          have nextInvalid : ¬ BoundarySymbol next.workSymbol := by
            cases next <;> intro allowed <;> cases allowed
          have rejectRun := finalCheck_reject_run (cnfFinish :: left)
            suffix next.workSymbol nextInvalid
          have complete := workRunExact?_compose cnfWorkMachine 1 1
            _ _ _ finishRun rejectRun
          refine ⟨2, (workConfigAtWord CNFWorkState.reject
            (cnfFinish :: left) (next.workSymbol :: suffix)).tape, ?_⟩
          unfold formulaGrammarFailureStart
          unfold suffix at complete
          exact complete
  | clauseEmpty =>
      intro control assignment counter left right counterAllowed
      cases control with
      | clauseNeed =>
          have invalid : ¬ LiteralSignSymbol cnfBoundaryGuard := by
            intro allowed
            cases allowed
          have hReject := clauseNeedLiteral_reject_run left
            (counter ++
              (cnfFinish ::
                (assignmentWorkSymbols assignment ++
                  (cnfRootGuard :: right))))
            cnfBoundaryGuard invalid
          refine ⟨1, (workConfigAtWord CNFWorkState.reject left
            (grammarCertificateTail assignment counter right)).tape, ?_⟩
          unfold formulaGrammarFailureStart grammarCertificateTail
          exact hReject
      | clauseContinue alreadySatisfied =>
          cases alreadySatisfied with
          | false =>
              have invalid : ¬ LiteralSignSymbol cnfBoundaryGuard := by
                intro allowed
                cases allowed
              have hReject := clauseContinueFalse_reject_run left
                (counter ++
                  (cnfFinish ::
                    (assignmentWorkSymbols assignment ++
                      (cnfRootGuard :: right))))
                cnfBoundaryGuard invalid
              refine ⟨1, (workConfigAtWord CNFWorkState.reject left
                (grammarCertificateTail assignment counter right)).tape, ?_⟩
              unfold formulaGrammarFailureStart grammarCertificateTail
              exact hReject
          | true =>
              have invalid : ¬ SatisfiedClauseSymbol cnfBoundaryGuard := by
                intro allowed
                cases allowed
              have hReject := clauseContinueTrue_reject_run left
                (counter ++
                  (cnfFinish ::
                    (assignmentWorkSymbols assignment ++
                      (cnfRootGuard :: right))))
                cnfBoundaryGuard invalid
              refine ⟨1, (workConfigAtWord CNFWorkState.reject left
                (grammarCertificateTail assignment counter right)).tape, ?_⟩
              unfold formulaGrammarFailureStart grammarCertificateTail
              exact hReject
  | clauseSep rest =>
      intro control assignment counter left right counterAllowed
      cases control with
      | clauseNeed =>
          have invalid : ¬ LiteralSignSymbol cnfSep := by
            intro allowed
            cases allowed
          let suffix := cnfTokenWorkSymbols rest ++
            grammarCertificateTail assignment counter right
          have hReject := clauseNeedLiteral_reject_run left suffix cnfSep
            invalid
          refine ⟨1, (workConfigAtWord CNFWorkState.reject left
            (cnfSep :: suffix)).tape, ?_⟩
          unfold formulaGrammarFailureStart
          exact hReject
      | clauseContinue alreadySatisfied =>
          cases alreadySatisfied with
          | false =>
              have invalid : ¬ LiteralSignSymbol cnfSep := by
                intro allowed
                cases allowed
              let suffix := cnfTokenWorkSymbols rest ++
                grammarCertificateTail assignment counter right
              have hReject := clauseContinueFalse_reject_run left suffix
                cnfSep invalid
              refine ⟨1, (workConfigAtWord CNFWorkState.reject left
                (cnfSep :: suffix)).tape, ?_⟩
              unfold formulaGrammarFailureStart
              exact hReject
          | true =>
              have invalid : ¬ SatisfiedClauseSymbol cnfSep := by
                intro allowed
                cases allowed
              let suffix := cnfTokenWorkSymbols rest ++
                grammarCertificateTail assignment counter right
              have hReject := clauseContinueTrue_reject_run left suffix
                cnfSep invalid
              refine ⟨1, (workConfigAtWord CNFWorkState.reject left
                (cnfSep :: suffix)).tape, ?_⟩
              unfold formulaGrammarFailureStart
              exact hReject
  | @clauseF rest tail ih =>
      intro control assignment counter left right counterAllowed
      cases control with
      | clauseNeed =>
          let suffix := cnfTokenWorkSymbols rest ++
            grammarCertificateTail assignment counter right
          have signRun := workRunExact?_one_of_step cnfWorkMachine _ _
            (clauseNeedLiteral_step false left suffix)
          rcases ih (FormulaGrammarControl.literal false false 0)
              assignment counter left right counterAllowed with
            ⟨remainingSteps, tape, remainingRun⟩
          unfold formulaGrammarFailureStart at remainingRun
          unfold suffix at signRun
          have complete := workRunExact?_compose cnfWorkMachine 1
            remainingSteps _ _ _ signRun remainingRun
          refine ⟨1 + remainingSteps, tape, ?_⟩
          unfold formulaGrammarFailureStart
          exact complete
      | clauseContinue alreadySatisfied =>
          let suffix := cnfTokenWorkSymbols rest ++
            grammarCertificateTail assignment counter right
          have signRun := workRunExact?_one_of_step cnfWorkMachine _ _
            (clauseContinue_literal_step alreadySatisfied false left suffix)
          rcases ih
              (FormulaGrammarControl.literal alreadySatisfied false 0)
              assignment counter left right counterAllowed with
            ⟨remainingSteps, tape, remainingRun⟩
          unfold formulaGrammarFailureStart at remainingRun
          unfold suffix at signRun
          have complete := workRunExact?_compose cnfWorkMachine 1
            remainingSteps _ _ _ signRun remainingRun
          refine ⟨1 + remainingSteps, tape, ?_⟩
          unfold formulaGrammarFailureStart
          exact complete
  | @clauseT rest tail ih =>
      intro control assignment counter left right counterAllowed
      cases control with
      | clauseNeed =>
          let suffix := cnfTokenWorkSymbols rest ++
            grammarCertificateTail assignment counter right
          have signRun := workRunExact?_one_of_step cnfWorkMachine _ _
            (clauseNeedLiteral_step true left suffix)
          rcases ih (FormulaGrammarControl.literal false true 0)
              assignment counter left right counterAllowed with
            ⟨remainingSteps, tape, remainingRun⟩
          unfold formulaGrammarFailureStart at remainingRun
          unfold suffix at signRun
          have complete := workRunExact?_compose cnfWorkMachine 1
            remainingSteps _ _ _ signRun remainingRun
          refine ⟨1 + remainingSteps, tape, ?_⟩
          unfold formulaGrammarFailureStart
          exact complete
      | clauseContinue alreadySatisfied =>
          let suffix := cnfTokenWorkSymbols rest ++
            grammarCertificateTail assignment counter right
          have signRun := workRunExact?_one_of_step cnfWorkMachine _ _
            (clauseContinue_literal_step alreadySatisfied true left suffix)
          rcases ih
              (FormulaGrammarControl.literal alreadySatisfied true 0)
              assignment counter left right counterAllowed with
            ⟨remainingSteps, tape, remainingRun⟩
          unfold formulaGrammarFailureStart at remainingRun
          unfold suffix at signRun
          have complete := workRunExact?_compose cnfWorkMachine 1
            remainingSteps _ _ _ signRun remainingRun
          refine ⟨1 + remainingSteps, tape, ?_⟩
          unfold formulaGrammarFailureStart
          exact complete
  | @clauseFinish rest tail ih =>
      intro control assignment counter left right counterAllowed
      cases control with
      | clauseNeed =>
          let suffix := cnfTokenWorkSymbols rest ++
            grammarCertificateTail assignment counter right
          have hReject := emptyClause_reject_run left suffix
          refine ⟨1, (workConfigAtWord CNFWorkState.reject left
            (cnfFinish :: suffix)).tape, ?_⟩
          unfold formulaGrammarFailureStart
          exact hReject
      | clauseContinue alreadySatisfied =>
          cases alreadySatisfied with
          | false =>
              let suffix := cnfTokenWorkSymbols rest ++
                grammarCertificateTail assignment counter right
              have hReject := unsatisfiedClauseFinish_reject_run left suffix
              refine ⟨1, (workConfigAtWord CNFWorkState.reject left
                (cnfFinish :: suffix)).tape, ?_⟩
              unfold formulaGrammarFailureStart
              exact hReject
          | true =>
              let suffix := cnfTokenWorkSymbols rest ++
                grammarCertificateTail assignment counter right
              have finishRun := workRunExact?_one_of_step cnfWorkMachine _ _
                (clauseContinue_true_finish_step left suffix)
              rcases ih FormulaGrammarControl.clauses assignment counter
                  (cnfFinish :: left) right counterAllowed with
                ⟨remainingSteps, tape, remainingRun⟩
              unfold formulaGrammarFailureStart at remainingRun
              unfold suffix at finishRun
              have complete := workRunExact?_compose cnfWorkMachine 1
                remainingSteps _ _ _ finishRun remainingRun
              refine ⟨1 + remainingSteps, tape, ?_⟩
              unfold formulaGrammarFailureStart
              exact complete
  | literalEmpty positive index =>
      intro control assignment counter left right counterAllowed
      cases control with
      | literal alreadySatisfied positive index =>
          rcases malformedLiteralMissing_exact alreadySatisfied positive
              [] assignment index counter left right counterAllowed with
            ⟨steps, tape, hReject⟩
          refine ⟨steps, tape, ?_⟩
          unfold formulaGrammarFailureStart grammarCertificateTail
          unfold malformedLiteralMissingStart at hReject
          repeat' rw [frameWork_append_assoc] at hReject ⊢
          exact hReject
  | literalSep positive index rest =>
      intro control assignment counter left right counterAllowed
      cases control with
      | literal alreadySatisfied positive index =>
          have formulaAllowed : ∀ symbol,
              List.Mem symbol (cnfTokenWorkSymbols rest) →
                FormulaScanSymbol symbol := by
            intro symbol member
            exact cnfTokenWorkSymbols_formulaScan rest symbol member
          rcases malformedLiteralSep_exact alreadySatisfied positive []
              assignment index counter (cnfTokenWorkSymbols rest) left right
              counterAllowed formulaAllowed with
            ⟨steps, tape, hReject⟩
          refine ⟨steps, tape, ?_⟩
          unfold formulaGrammarFailureStart grammarCertificateTail
          unfold malformedLiteralSymbolStart at hReject
          repeat' rw [frameWork_append_assoc] at hReject ⊢
          exact hReject
  | literalFinish positive index rest =>
      intro control assignment counter left right counterAllowed
      cases control with
      | literal alreadySatisfied positive index =>
          have formulaAllowed : ∀ symbol,
              List.Mem symbol (cnfTokenWorkSymbols rest) →
                FormulaScanSymbol symbol := by
            intro symbol member
            exact cnfTokenWorkSymbols_formulaScan rest symbol member
          rcases malformedLiteralFinish_exact alreadySatisfied positive []
              assignment index counter (cnfTokenWorkSymbols rest) left right
              counterAllowed formulaAllowed with
            ⟨steps, tape, hReject⟩
          refine ⟨steps, tape, ?_⟩
          unfold formulaGrammarFailureStart grammarCertificateTail
          unfold malformedLiteralSymbolStart at hReject
          repeat' rw [frameWork_append_assoc] at hReject ⊢
          exact hReject
  | @literalF positive index rest tail ih =>
      intro control assignment counter left right counterAllowed
      cases control with
      | literal alreadySatisfied positive index =>
          have formulaAllowed : ∀ symbol,
              List.Mem symbol (cnfTokenWorkSymbols rest) →
                FormulaScanSymbol symbol := by
            intro symbol member
            exact cnfTokenWorkSymbols_formulaScan rest symbol member
          let result := alreadySatisfied ||
            checkLiteral
              ({ positive := positive, variableIndex := index } : CNFLiteral)
              assignment
          let continuedLeft := cnfF ::
            pushWorkLeft (List.replicate index cnfT)
              ((if positive then cnfT else cnfF) :: left)
          have literalRun := literalIndex_full_count_exact alreadySatisfied
            positive index assignment counter (cnfTokenWorkSymbols rest)
            left right counterAllowed formulaAllowed
          rcases ih (FormulaGrammarControl.clauseContinue result)
              assignment counter continuedLeft right counterAllowed with
            ⟨remainingSteps, tape, remainingRun⟩
          unfold literalSemanticStart literalSemanticFinal at literalRun
          unfold formulaGrammarFailureStart at remainingRun
          unfold result continuedLeft grammarCertificateTail at remainingRun
          have complete := workRunExact?_compose cnfWorkMachine
            (literalSemanticStepCount counter (cnfTokenWorkSymbols rest) []
              assignment index)
            remainingSteps _ _ _ literalRun remainingRun
          refine ⟨literalSemanticStepCount counter
              (cnfTokenWorkSymbols rest) [] assignment index +
            remainingSteps, tape, ?_⟩
          unfold formulaGrammarFailureStart grammarCertificateTail
          repeat' rw [frameWork_append_assoc] at complete ⊢
          exact complete
  | @literalT positive index rest tail ih =>
      intro control assignment counter left right counterAllowed
      cases control with
      | literal alreadySatisfied positive index =>
          rcases ih
              (FormulaGrammarControl.literal alreadySatisfied positive
                (index + 1))
              assignment counter left right counterAllowed with
            ⟨steps, tape, hReject⟩
          refine ⟨steps, tape, ?_⟩
          change workRunExact? cnfWorkMachine steps
              (workConfigAtWord
                (CNFWorkState.literalIndex alreadySatisfied positive)
                (cnfBoundaryGuard :: left)
                (List.replicate (index + 1) cnfT ++
                  (cnfTokenWorkSymbols rest ++
                    grammarCertificateTail assignment counter right))) =
            some ({ state := CNFWorkState.reject, tape := tape } :
              WorkConfiguration) at hReject
          change workRunExact? cnfWorkMachine steps
              (workConfigAtWord
                (CNFWorkState.literalIndex alreadySatisfied positive)
                (cnfBoundaryGuard :: left)
                (List.replicate index cnfT ++
                  ((cnfT :: cnfTokenWorkSymbols rest) ++
                    grammarCertificateTail assignment counter right))) =
            some ({ state := CNFWorkState.reject, tape := tape } :
              WorkConfiguration)
          have startShape :
              List.replicate (index + 1) cnfT ++
                  (cnfTokenWorkSymbols rest ++
                    grammarCertificateTail assignment counter right) =
                List.replicate index cnfT ++
                  ((cnfT :: cnfTokenWorkSymbols rest) ++
                    grammarCertificateTail assignment counter right) := by
            rw [replicate_succ_tail]
            rw [frameWork_append_assoc]
            rfl
          rw [← startShape]
          exact hReject

end GrammarClauseDesign

end PNP.Concrete


namespace PNP.Concrete
namespace GrammarClauseBoundDesign

open FrameTraceDesign
open ClauseLiteralDesign
open ClauseLiteralCostDesign
open GrammarFailureDesign
open GrammarTerminalDesign
open GrammarTerminalBoundDesign
open GrammarClauseDesign

set_option maxRecDepth 100000

def formulaGrammarControlPrefix {mode : FormulaGrammarMode} :
    FormulaGrammarControl mode → Nat
  | .clauses => 0
  | .clauseNeed => 0
  | .clauseContinue _ => 0
  | .literal _ _ index => index

def formulaGrammarControlUnits {mode : FormulaGrammarMode}
    (control : FormulaGrammarControl mode) (tokens : List CNFToken) : Nat :=
  formulaGrammarControlPrefix control + tokens.length + 1

theorem formulaGrammarControlPrefix_clauses :
    formulaGrammarControlPrefix FormulaGrammarControl.clauses = 0 := rfl

theorem formulaGrammarControlPrefix_clauseNeed :
    formulaGrammarControlPrefix FormulaGrammarControl.clauseNeed = 0 := rfl

theorem formulaGrammarControlPrefix_clauseContinue (value : Bool) :
    formulaGrammarControlPrefix
      (FormulaGrammarControl.clauseContinue value) = 0 := rfl

theorem formulaGrammarControlPrefix_literal
    (alreadySatisfied positive : Bool) (index : Nat) :
    formulaGrammarControlPrefix
      (FormulaGrammarControl.literal alreadySatisfied positive index) =
        index := rfl

theorem formulaGrammarControlUnits_clauses (tokens : List CNFToken) :
    formulaGrammarControlUnits FormulaGrammarControl.clauses tokens =
      tokens.length + 1 := by
  unfold formulaGrammarControlUnits
  rw [formulaGrammarControlPrefix_clauses, Nat.zero_add]

theorem formulaGrammarControlUnits_clauseNeed (tokens : List CNFToken) :
    formulaGrammarControlUnits FormulaGrammarControl.clauseNeed tokens =
      tokens.length + 1 := by
  unfold formulaGrammarControlUnits
  rw [formulaGrammarControlPrefix_clauseNeed, Nat.zero_add]

theorem formulaGrammarControlUnits_clauseContinue
    (value : Bool) (tokens : List CNFToken) :
    formulaGrammarControlUnits (FormulaGrammarControl.clauseContinue value)
        tokens = tokens.length + 1 := by
  unfold formulaGrammarControlUnits
  rw [formulaGrammarControlPrefix_clauseContinue, Nat.zero_add]

theorem formulaGrammarControlUnits_literal
    (alreadySatisfied positive : Bool) (index : Nat)
    (tokens : List CNFToken) :
    formulaGrammarControlUnits
        (FormulaGrammarControl.literal alreadySatisfied positive index)
        tokens = index + tokens.length + 1 := rfl

theorem one_le_positive_units_charge (n units : Nat) :
    1 ≤ (units + 1) * literalUnitCharge n := by
  exact Nat.le_trans (one_le_literalUnitCharge n)
    (Nat.le_mul_of_pos_left (literalUnitCharge n)
      (Nat.zero_lt_succ units))

theorem one_add_steps_le_succ_units (n units steps : Nat)
    (bound : steps ≤ units * literalUnitCharge n) :
    1 + steps ≤ Nat.succ units * literalUnitCharge n := by
  have combined := Nat.add_le_add (one_le_literalUnitCharge n) bound
  apply Nat.le_trans combined
  rw [Nat.add_comm (literalUnitCharge n)
    (units * literalUnitCharge n)]
  exact Nat.le_of_eq (Nat.succ_mul units (literalUnitCharge n)).symm

theorem add_charged_blocks (n firstUnits secondUnits firstSteps
    secondSteps : Nat)
    (firstBound : firstSteps ≤ firstUnits * literalUnitCharge n)
    (secondBound : secondSteps ≤ secondUnits * literalUnitCharge n) :
    firstSteps + secondSteps ≤
      (firstUnits + secondUnits) * literalUnitCharge n := by
  have distributed :
      (firstUnits + secondUnits) * literalUnitCharge n =
        firstUnits * literalUnitCharge n +
          secondUnits * literalUnitCharge n := by
    calc
      (firstUnits + secondUnits) * literalUnitCharge n =
          literalUnitCharge n * (firstUnits + secondUnits) :=
        Nat.mul_comm (firstUnits + secondUnits) (literalUnitCharge n)
      _ = literalUnitCharge n * firstUnits +
          literalUnitCharge n * secondUnits :=
        Nat.mul_add (literalUnitCharge n) firstUnits secondUnits
      _ = firstUnits * literalUnitCharge n +
          secondUnits * literalUnitCharge n := by
        rw [Nat.mul_comm (literalUnitCharge n) firstUnits,
          Nat.mul_comm (literalUnitCharge n) secondUnits]
  exact Nat.le_trans (Nat.add_le_add firstBound secondBound)
    (Nat.le_of_eq distributed.symm)

theorem indexRestSucc_eq_succIndexRest (index rest : Nat) :
    (index + rest).succ = (0 + index).succ + rest := by
  rw [Nat.zero_add, Nat.succ_add]

theorem indexRestTwo_eq_indexSuccRestOne (index rest : Nat) :
    ((index + rest).succ + 0).succ = index + (rest + 1) + 1 := by
  rw [Nat.add_zero, Nat.add_succ, Nat.add_succ]
  rw [Nat.add_zero, Nat.add_succ]

theorem indexOneRest_eq_indexRestOne (index rest : Nat) :
    index + (1 + rest).succ = index + (rest + 1) + 1 := by
  rw [Nat.one_add, Nat.add_succ, Nat.add_succ]

theorem indexSuccRest_eq_indexRestOne (index rest : Nat) :
    (index + 1 + rest).succ = index + (rest + 1) + 1 := by
  rw [Nat.add_succ, Nat.succ_add, Nat.add_succ]
  rw [Nat.add_zero, Nat.add_succ]

theorem indexOneRestOne_eq_indexRestOneOne (index rest : Nat) :
    index + 1 + (rest + 1) = index + (rest + 1) + 1 := by
  rw [Nat.add_succ, Nat.succ_add, Nat.add_succ]
  rw [Nat.add_zero, Nat.add_succ]

theorem formulaGrammarFailure_machine_charge
    {mode : FormulaGrammarMode} {tokens : List CNFToken}
    (failure : FormulaGrammarFailure mode tokens) :
    ∀ (control : FormulaGrammarControl mode)
      (assignment : BitString) (counter left right : List WorkSymbol)
      (n : Nat),
      assignment.length ≤ n →
      counter.length ≤ n →
      (∀ symbol, List.Mem symbol counter → symbol = cnfMarkFalse) →
      formulaGrammarControlPrefix control + tokens.length ≤ n →
      ∃ steps tape,
        steps ≤ formulaGrammarControlUnits control tokens *
          literalUnitCharge n ∧
        workRunExact? cnfWorkMachine steps
            (formulaGrammarFailureStart control tokens assignment counter
              left right) =
          some ({ state := CNFWorkState.reject, tape := tape } :
            WorkConfiguration) := by
  induction failure with
  | headerEmpty count =>
      intro control
      cases control
  | headerSep count rest =>
      intro control
      cases control
  | headerFinish count rest =>
      intro control
      cases control
  | headerT tail ih =>
      intro control
      cases control
  | headerF tail ih =>
      intro control
      cases control
  | clausesEmpty =>
      intro control assignment counter left right n assignmentBound
        counterBound counterAllowed formulaBound
      cases control with
      | clauses =>
          have invalid : ¬ ClauseStartSymbol cnfBoundaryGuard := by
            intro allowed
            cases allowed
          have hReject := clauseStart_reject_run left
            (counter ++
              (cnfFinish ::
                (assignmentWorkSymbols assignment ++
                  (cnfRootGuard :: right))))
            cnfBoundaryGuard invalid
          refine ⟨1, (workConfigAtWord CNFWorkState.reject left
            (grammarCertificateTail assignment counter right)).tape, ?_, ?_⟩
          · unfold formulaGrammarControlUnits formulaGrammarControlPrefix
            exact one_le_positive_units_charge n 0
          · unfold formulaGrammarFailureStart grammarCertificateTail
            exact hReject
  | clausesF rest =>
      intro control assignment counter left right n assignmentBound
        counterBound counterAllowed formulaBound
      cases control with
      | clauses =>
          have invalid : ¬ ClauseStartSymbol cnfF := by
            intro allowed
            cases allowed
          let suffix := cnfTokenWorkSymbols rest ++
            grammarCertificateTail assignment counter right
          have hReject := clauseStart_reject_run left suffix cnfF invalid
          refine ⟨1, (workConfigAtWord CNFWorkState.reject left
            (cnfF :: suffix)).tape, ?_, ?_⟩
          · rw [formulaGrammarControlUnits_clauses]
            change 1 ≤ (rest.length + 1 + 1) * literalUnitCharge n
            exact one_le_positive_units_charge n (List.length rest + 1)
          · unfold formulaGrammarFailureStart
            exact hReject
  | clausesT rest =>
      intro control assignment counter left right n assignmentBound
        counterBound counterAllowed formulaBound
      cases control with
      | clauses =>
          have invalid : ¬ ClauseStartSymbol cnfT := by
            intro allowed
            cases allowed
          let suffix := cnfTokenWorkSymbols rest ++
            grammarCertificateTail assignment counter right
          have hReject := clauseStart_reject_run left suffix cnfT invalid
          refine ⟨1, (workConfigAtWord CNFWorkState.reject left
            (cnfT :: suffix)).tape, ?_, ?_⟩
          · rw [formulaGrammarControlUnits_clauses]
            change 1 ≤ (rest.length + 1 + 1) * literalUnitCharge n
            exact one_le_positive_units_charge n (List.length rest + 1)
          · unfold formulaGrammarFailureStart
            exact hReject
  | @clausesSep rest tail ih =>
      intro control assignment counter left right n assignmentBound
        counterBound counterAllowed formulaBound
      cases control with
      | clauses =>
          let suffix := cnfTokenWorkSymbols rest ++
            grammarCertificateTail assignment counter right
          have separatorRun := workRunExact?_one_of_step cnfWorkMachine _ _
            (clauseStart_separator_step left suffix)
          have tailFormulaBound :
              formulaGrammarControlPrefix FormulaGrammarControl.clauseNeed +
                rest.length ≤ n := by
            rw [formulaGrammarControlPrefix_clauseNeed]
            rw [Nat.zero_add]
            rw [formulaGrammarControlPrefix_clauses, Nat.zero_add]
              at formulaBound
            exact Nat.le_trans (Nat.le_succ rest.length) formulaBound
          rcases ih FormulaGrammarControl.clauseNeed assignment counter
              (cnfSep :: left) right n assignmentBound counterBound
              counterAllowed
              tailFormulaBound with
            ⟨remainingSteps, tape, remainingBound, remainingRun⟩
          unfold formulaGrammarFailureStart at remainingRun
          unfold suffix at separatorRun
          have complete := workRunExact?_compose cnfWorkMachine 1
            remainingSteps _ _ _ separatorRun remainingRun
          refine ⟨1 + remainingSteps, tape, ?_, ?_⟩
          · rw [formulaGrammarControlUnits_clauseNeed]
              at remainingBound
            change remainingSteps ≤
                (rest.length + 1) * literalUnitCharge n at remainingBound
            rw [formulaGrammarControlUnits_clauses]
            change 1 + remainingSteps ≤
              (rest.length + 1 + 1) * literalUnitCharge n
            exact one_add_steps_le_succ_units n (rest.length + 1)
              remainingSteps remainingBound
          · unfold formulaGrammarFailureStart
            exact complete
  | clausesFinishTrailing next rest =>
      intro control assignment counter left right n assignmentBound
        counterBound counterAllowed formulaBound
      cases control with
      | clauses =>
          let suffix := cnfTokenWorkSymbols rest ++
            grammarCertificateTail assignment counter right
          have finishRun := workRunExact?_one_of_step cnfWorkMachine _ _
            (clauseStart_formulaFinish_step left
              (next.workSymbol :: suffix))
          have nextInvalid : ¬ BoundarySymbol next.workSymbol := by
            cases next <;> intro allowed <;> cases allowed
          have rejectRun := finalCheck_reject_run (cnfFinish :: left)
            suffix next.workSymbol nextInvalid
          have complete := workRunExact?_compose cnfWorkMachine 1 1
            _ _ _ finishRun rejectRun
          refine ⟨2, (workConfigAtWord CNFWorkState.reject
            (cnfFinish :: left) (next.workSymbol :: suffix)).tape, ?_, ?_⟩
          · rw [formulaGrammarControlUnits_clauses]
            change 2 ≤ (rest.length + 3) * literalUnitCharge n
            have twoChargeRaw := Nat.add_le_add
              (one_le_literalUnitCharge n) (one_le_literalUnitCharge n)
            have twoCharge : 2 ≤ 2 * literalUnitCharge n := by
              rw [Nat.two_mul]
              exact twoChargeRaw
            apply Nat.le_trans twoCharge
            apply Nat.mul_le_mul_right (literalUnitCharge n)
            have twoThree : 2 ≤ 3 := by
              change 2 ≤ 2 + 1
              exact Nat.le_add_right 2 1
            exact Nat.le_trans twoThree
              (Nat.le_add_left 3 rest.length)
          · unfold formulaGrammarFailureStart
            unfold suffix at complete
            exact complete
  | clauseEmpty =>
      intro control assignment counter left right n assignmentBound
        counterBound counterAllowed formulaBound
      cases control with
      | clauseNeed =>
          have invalid : ¬ LiteralSignSymbol cnfBoundaryGuard := by
            intro allowed
            cases allowed
          have hReject := clauseNeedLiteral_reject_run left
            (counter ++
              (cnfFinish ::
                (assignmentWorkSymbols assignment ++
                  (cnfRootGuard :: right))))
            cnfBoundaryGuard invalid
          refine ⟨1, (workConfigAtWord CNFWorkState.reject left
            (grammarCertificateTail assignment counter right)).tape, ?_, ?_⟩
          · rw [formulaGrammarControlUnits_clauseNeed]
            rw [show ([] : List CNFToken).length = 0 from rfl,
              Nat.zero_add, Nat.one_mul]
            exact one_le_literalUnitCharge n
          · unfold formulaGrammarFailureStart grammarCertificateTail
            exact hReject
      | clauseContinue alreadySatisfied =>
          cases alreadySatisfied with
          | false =>
              have invalid : ¬ LiteralSignSymbol cnfBoundaryGuard := by
                intro allowed
                cases allowed
              have hReject := clauseContinueFalse_reject_run left
                (counter ++
                  (cnfFinish ::
                    (assignmentWorkSymbols assignment ++
                      (cnfRootGuard :: right))))
                cnfBoundaryGuard invalid
              refine ⟨1, (workConfigAtWord CNFWorkState.reject left
                (grammarCertificateTail assignment counter right)).tape,
                ?_, ?_⟩
              · rw [formulaGrammarControlUnits_clauseContinue]
                rw [show ([] : List CNFToken).length = 0 from rfl,
                  Nat.zero_add, Nat.one_mul]
                exact one_le_literalUnitCharge n
              · unfold formulaGrammarFailureStart grammarCertificateTail
                exact hReject
          | true =>
              have invalid : ¬ SatisfiedClauseSymbol cnfBoundaryGuard := by
                intro allowed
                cases allowed
              have hReject := clauseContinueTrue_reject_run left
                (counter ++
                  (cnfFinish ::
                    (assignmentWorkSymbols assignment ++
                      (cnfRootGuard :: right))))
                cnfBoundaryGuard invalid
              refine ⟨1, (workConfigAtWord CNFWorkState.reject left
                (grammarCertificateTail assignment counter right)).tape,
                ?_, ?_⟩
              · rw [formulaGrammarControlUnits_clauseContinue]
                rw [show ([] : List CNFToken).length = 0 from rfl,
                  Nat.zero_add, Nat.one_mul]
                exact one_le_literalUnitCharge n
              · unfold formulaGrammarFailureStart grammarCertificateTail
                exact hReject
  | clauseSep rest =>
      intro control assignment counter left right n assignmentBound
        counterBound counterAllowed formulaBound
      cases control with
      | clauseNeed =>
          have invalid : ¬ LiteralSignSymbol cnfSep := by
            intro allowed
            cases allowed
          let suffix := cnfTokenWorkSymbols rest ++
            grammarCertificateTail assignment counter right
          have hReject := clauseNeedLiteral_reject_run left suffix cnfSep
            invalid
          refine ⟨1, (workConfigAtWord CNFWorkState.reject left
            (cnfSep :: suffix)).tape, ?_, ?_⟩
          · rw [formulaGrammarControlUnits_clauseNeed]
            exact one_le_positive_units_charge n (rest.length + 1)
          · unfold formulaGrammarFailureStart
            exact hReject
      | clauseContinue alreadySatisfied =>
          cases alreadySatisfied with
          | false =>
              have invalid : ¬ LiteralSignSymbol cnfSep := by
                intro allowed
                cases allowed
              let suffix := cnfTokenWorkSymbols rest ++
                grammarCertificateTail assignment counter right
              have hReject := clauseContinueFalse_reject_run left suffix
                cnfSep invalid
              refine ⟨1, (workConfigAtWord CNFWorkState.reject left
                (cnfSep :: suffix)).tape, ?_, ?_⟩
              · rw [formulaGrammarControlUnits_clauseContinue]
                exact one_le_positive_units_charge n (rest.length + 1)
              · unfold formulaGrammarFailureStart
                exact hReject
          | true =>
              have invalid : ¬ SatisfiedClauseSymbol cnfSep := by
                intro allowed
                cases allowed
              let suffix := cnfTokenWorkSymbols rest ++
                grammarCertificateTail assignment counter right
              have hReject := clauseContinueTrue_reject_run left suffix
                cnfSep invalid
              refine ⟨1, (workConfigAtWord CNFWorkState.reject left
                (cnfSep :: suffix)).tape, ?_, ?_⟩
              · rw [formulaGrammarControlUnits_clauseContinue]
                exact one_le_positive_units_charge n (rest.length + 1)
              · unfold formulaGrammarFailureStart
                exact hReject
  | @clauseF rest tail ih =>
      intro control assignment counter left right n assignmentBound
        counterBound counterAllowed formulaBound
      cases control with
      | clauseNeed =>
          let suffix := cnfTokenWorkSymbols rest ++
            grammarCertificateTail assignment counter right
          have signRun := workRunExact?_one_of_step cnfWorkMachine _ _
            (clauseNeedLiteral_step false left suffix)
          have tailFormulaBound :
              formulaGrammarControlPrefix
                  (FormulaGrammarControl.literal false false 0) +
                rest.length ≤ n := by
            rw [formulaGrammarControlPrefix_literal, Nat.zero_add]
            rw [formulaGrammarControlPrefix_clauseNeed, Nat.zero_add]
              at formulaBound
            exact Nat.le_trans (Nat.le_succ rest.length) formulaBound
          rcases ih (FormulaGrammarControl.literal false false 0)
              assignment counter left right n assignmentBound counterBound
              counterAllowed
              tailFormulaBound with
            ⟨remainingSteps, tape, remainingBound, remainingRun⟩
          unfold formulaGrammarFailureStart at remainingRun
          unfold suffix at signRun
          have complete := workRunExact?_compose cnfWorkMachine 1
            remainingSteps _ _ _ signRun remainingRun
          refine ⟨1 + remainingSteps, tape, ?_, ?_⟩
          · rw [formulaGrammarControlUnits_literal] at remainingBound
            rw [Nat.zero_add] at remainingBound
            rw [formulaGrammarControlUnits_clauseNeed]
            exact one_add_steps_le_succ_units n (rest.length + 1)
              remainingSteps remainingBound
          · unfold formulaGrammarFailureStart
            exact complete
      | clauseContinue alreadySatisfied =>
          let suffix := cnfTokenWorkSymbols rest ++
            grammarCertificateTail assignment counter right
          have signRun := workRunExact?_one_of_step cnfWorkMachine _ _
            (clauseContinue_literal_step alreadySatisfied false left suffix)
          have tailFormulaBound :
              formulaGrammarControlPrefix
                  (FormulaGrammarControl.literal alreadySatisfied false 0) +
                rest.length ≤ n := by
            rw [formulaGrammarControlPrefix_literal, Nat.zero_add]
            rw [formulaGrammarControlPrefix_clauseContinue, Nat.zero_add]
              at formulaBound
            exact Nat.le_trans (Nat.le_succ rest.length) formulaBound
          rcases ih
              (FormulaGrammarControl.literal alreadySatisfied false 0)
              assignment counter left right n assignmentBound counterBound
              counterAllowed
              tailFormulaBound with
            ⟨remainingSteps, tape, remainingBound, remainingRun⟩
          unfold formulaGrammarFailureStart at remainingRun
          unfold suffix at signRun
          have complete := workRunExact?_compose cnfWorkMachine 1
            remainingSteps _ _ _ signRun remainingRun
          refine ⟨1 + remainingSteps, tape, ?_, ?_⟩
          · rw [formulaGrammarControlUnits_literal] at remainingBound
            rw [Nat.zero_add] at remainingBound
            rw [formulaGrammarControlUnits_clauseContinue]
            exact one_add_steps_le_succ_units n (rest.length + 1)
              remainingSteps remainingBound
          · unfold formulaGrammarFailureStart
            exact complete
  | @clauseT rest tail ih =>
      intro control assignment counter left right n assignmentBound
        counterBound counterAllowed formulaBound
      cases control with
      | clauseNeed =>
          let suffix := cnfTokenWorkSymbols rest ++
            grammarCertificateTail assignment counter right
          have signRun := workRunExact?_one_of_step cnfWorkMachine _ _
            (clauseNeedLiteral_step true left suffix)
          have tailFormulaBound :
              formulaGrammarControlPrefix
                  (FormulaGrammarControl.literal false true 0) +
                rest.length ≤ n := by
            rw [formulaGrammarControlPrefix_literal, Nat.zero_add]
            rw [formulaGrammarControlPrefix_clauseNeed, Nat.zero_add]
              at formulaBound
            exact Nat.le_trans (Nat.le_succ rest.length) formulaBound
          rcases ih (FormulaGrammarControl.literal false true 0)
              assignment counter left right n assignmentBound counterBound
              counterAllowed
              tailFormulaBound with
            ⟨remainingSteps, tape, remainingBound, remainingRun⟩
          unfold formulaGrammarFailureStart at remainingRun
          unfold suffix at signRun
          have complete := workRunExact?_compose cnfWorkMachine 1
            remainingSteps _ _ _ signRun remainingRun
          refine ⟨1 + remainingSteps, tape, ?_, ?_⟩
          · rw [formulaGrammarControlUnits_literal] at remainingBound
            rw [Nat.zero_add] at remainingBound
            rw [formulaGrammarControlUnits_clauseNeed]
            exact one_add_steps_le_succ_units n (rest.length + 1)
              remainingSteps remainingBound
          · unfold formulaGrammarFailureStart
            exact complete
      | clauseContinue alreadySatisfied =>
          let suffix := cnfTokenWorkSymbols rest ++
            grammarCertificateTail assignment counter right
          have signRun := workRunExact?_one_of_step cnfWorkMachine _ _
            (clauseContinue_literal_step alreadySatisfied true left suffix)
          have tailFormulaBound :
              formulaGrammarControlPrefix
                  (FormulaGrammarControl.literal alreadySatisfied true 0) +
                rest.length ≤ n := by
            rw [formulaGrammarControlPrefix_literal, Nat.zero_add]
            rw [formulaGrammarControlPrefix_clauseContinue, Nat.zero_add]
              at formulaBound
            exact Nat.le_trans (Nat.le_succ rest.length) formulaBound
          rcases ih
              (FormulaGrammarControl.literal alreadySatisfied true 0)
              assignment counter left right n assignmentBound counterBound
              counterAllowed
              tailFormulaBound with
            ⟨remainingSteps, tape, remainingBound, remainingRun⟩
          unfold formulaGrammarFailureStart at remainingRun
          unfold suffix at signRun
          have complete := workRunExact?_compose cnfWorkMachine 1
            remainingSteps _ _ _ signRun remainingRun
          refine ⟨1 + remainingSteps, tape, ?_, ?_⟩
          · rw [formulaGrammarControlUnits_literal] at remainingBound
            rw [Nat.zero_add] at remainingBound
            rw [formulaGrammarControlUnits_clauseContinue]
            exact one_add_steps_le_succ_units n (rest.length + 1)
              remainingSteps remainingBound
          · unfold formulaGrammarFailureStart
            exact complete
  | @clauseFinish rest tail ih =>
      intro control assignment counter left right n assignmentBound
        counterBound counterAllowed formulaBound
      cases control with
      | clauseNeed =>
          let suffix := cnfTokenWorkSymbols rest ++
            grammarCertificateTail assignment counter right
          have hReject := emptyClause_reject_run left suffix
          refine ⟨1, (workConfigAtWord CNFWorkState.reject left
            (cnfFinish :: suffix)).tape, ?_, ?_⟩
          · rw [formulaGrammarControlUnits_clauseNeed]
            exact one_le_positive_units_charge n (rest.length + 1)
          · unfold formulaGrammarFailureStart
            exact hReject
      | clauseContinue alreadySatisfied =>
          cases alreadySatisfied with
          | false =>
              let suffix := cnfTokenWorkSymbols rest ++
                grammarCertificateTail assignment counter right
              have hReject := unsatisfiedClauseFinish_reject_run left suffix
              refine ⟨1, (workConfigAtWord CNFWorkState.reject left
                (cnfFinish :: suffix)).tape, ?_, ?_⟩
              · rw [formulaGrammarControlUnits_clauseContinue]
                exact one_le_positive_units_charge n (rest.length + 1)
              · unfold formulaGrammarFailureStart
                exact hReject
          | true =>
              let suffix := cnfTokenWorkSymbols rest ++
                grammarCertificateTail assignment counter right
              have finishRun := workRunExact?_one_of_step cnfWorkMachine _ _
                (clauseContinue_true_finish_step left suffix)
              have tailFormulaBound :
                  formulaGrammarControlPrefix FormulaGrammarControl.clauses +
                    rest.length ≤ n := by
                rw [formulaGrammarControlPrefix_clauses, Nat.zero_add]
                rw [formulaGrammarControlPrefix_clauseContinue, Nat.zero_add]
                  at formulaBound
                exact Nat.le_trans (Nat.le_succ rest.length) formulaBound
              rcases ih FormulaGrammarControl.clauses assignment counter
                  (cnfFinish :: left) right n assignmentBound counterBound
                  counterAllowed
                  tailFormulaBound with
                ⟨remainingSteps, tape, remainingBound, remainingRun⟩
              unfold formulaGrammarFailureStart at remainingRun
              unfold suffix at finishRun
              have complete := workRunExact?_compose cnfWorkMachine 1
                remainingSteps _ _ _ finishRun remainingRun
              refine ⟨1 + remainingSteps, tape, ?_, ?_⟩
              · rw [formulaGrammarControlUnits_clauses]
                  at remainingBound
                rw [formulaGrammarControlUnits_clauseContinue]
                exact one_add_steps_le_succ_units n (rest.length + 1)
                  remainingSteps remainingBound
              · unfold formulaGrammarFailureStart
                exact complete
  | literalEmpty positive index =>
      intro control assignment counter left right n assignmentBound
        counterBound counterAllowed formulaBound
      cases control with
      | literal alreadySatisfied positive index =>
          have indexBound : index ≤ n := by
            rw [formulaGrammarControlPrefix_literal] at formulaBound
            exact Nat.le_trans (Nat.le_add_right index [].length)
              formulaBound
          have combinedAssignmentBound :
              ([] : BitString).length + assignment.length ≤ n := by
            rw [show ([] : BitString).length = 0 from rfl, Nat.zero_add]
            exact assignmentBound
          rcases malformedLiteralMissing_counted_exact alreadySatisfied
              positive [] assignment index counter left right counterAllowed
              with ⟨tape, hReject⟩
          have stepBound := malformedLiteralMissingStepCount_le_charge n []
            assignment counter index combinedAssignmentBound counterBound
            indexBound
          refine ⟨malformedLiteralMissingStepCount [] assignment counter
            index, tape, ?_, ?_⟩
          · rw [formulaGrammarControlUnits_literal]
            change malformedLiteralMissingStepCount [] assignment counter
                index ≤
              (index + 1) * literalUnitCharge n
            exact stepBound
          · unfold formulaGrammarFailureStart grammarCertificateTail
            unfold malformedLiteralMissingStart at hReject
            repeat' rw [frameWork_append_assoc] at hReject ⊢
            exact hReject
  | literalSep positive index rest =>
      intro control assignment counter left right n assignmentBound
        counterBound counterAllowed formulaBound
      cases control with
      | literal alreadySatisfied positive index =>
          have formulaAllowed : ∀ symbol,
              List.Mem symbol (cnfTokenWorkSymbols rest) →
                FormulaScanSymbol symbol := by
            intro symbol member
            exact cnfTokenWorkSymbols_formulaScan rest symbol member
          have combinedAssignmentBound :
              ([] : BitString).length + assignment.length ≤ n := by
            rw [show ([] : BitString).length = 0 from rfl, Nat.zero_add]
            exact assignmentBound
          have terminalFormulaBound :
              index + 1 + (cnfTokenWorkSymbols rest).length ≤ n := by
            rw [cnfTokenWorkSymbols_length]
            rw [formulaGrammarControlPrefix_literal] at formulaBound
            rw [List.length_cons, Nat.add_succ] at formulaBound
            rw [Nat.add_comm index 1, Nat.succ_add]
            rw [Nat.zero_add]
            rw [Nat.succ_add]
            exact formulaBound
          rcases malformedLiteralSymbol_counted_exact alreadySatisfied
              positive [] assignment index counter (cnfTokenWorkSymbols rest)
              left right cnfSep counterAllowed formulaAllowed .sep
              (by intro allowed; cases allowed) with ⟨tape, hReject⟩
          have terminalBound := malformedLiteralSymbolStepCount_le_charge n
            [] assignment counter (cnfTokenWorkSymbols rest) cnfSep index
            combinedAssignmentBound counterBound terminalFormulaBound
          refine ⟨malformedLiteralSymbolStepCount [] assignment counter
              (cnfTokenWorkSymbols rest) cnfSep index,
            tape, ?_, ?_⟩
          · rw [formulaGrammarControlUnits_literal]
            apply Nat.le_trans terminalBound
            apply Nat.mul_le_mul_right (literalUnitCharge n)
            have coefficient : index + 1 ≤
                index + (CNFToken.sep :: rest).length + 1 := by
              calc
                index + 1 ≤ index + 1 + rest.length :=
                  Nat.le_add_right (index + 1) rest.length
                _ ≤ index + 1 + rest.length + 1 :=
                  Nat.le_succ (index + 1 + rest.length)
                _ = index + (CNFToken.sep :: rest).length + 1 := by
                  rw [List.length_cons]
                  exact indexSuccRest_eq_indexRestOne index rest.length
            exact coefficient
          · unfold formulaGrammarFailureStart grammarCertificateTail
            unfold malformedLiteralSymbolStart at hReject
            repeat' rw [frameWork_append_assoc] at hReject ⊢
            exact hReject
  | literalFinish positive index rest =>
      intro control assignment counter left right n assignmentBound
        counterBound counterAllowed formulaBound
      cases control with
      | literal alreadySatisfied positive index =>
          have formulaAllowed : ∀ symbol,
              List.Mem symbol (cnfTokenWorkSymbols rest) →
                FormulaScanSymbol symbol := by
            intro symbol member
            exact cnfTokenWorkSymbols_formulaScan rest symbol member
          have combinedAssignmentBound :
              ([] : BitString).length + assignment.length ≤ n := by
            rw [show ([] : BitString).length = 0 from rfl, Nat.zero_add]
            exact assignmentBound
          have terminalFormulaBound :
              index + 1 + (cnfTokenWorkSymbols rest).length ≤ n := by
            rw [cnfTokenWorkSymbols_length]
            rw [formulaGrammarControlPrefix_literal] at formulaBound
            rw [List.length_cons, Nat.add_succ] at formulaBound
            rw [Nat.add_comm index 1, Nat.succ_add]
            rw [Nat.zero_add]
            rw [Nat.succ_add]
            exact formulaBound
          rcases malformedLiteralSymbol_counted_exact alreadySatisfied
              positive [] assignment index counter (cnfTokenWorkSymbols rest)
              left right cnfFinish counterAllowed formulaAllowed .finish
              (by intro allowed; cases allowed) with ⟨tape, hReject⟩
          have terminalBound := malformedLiteralSymbolStepCount_le_charge n
            [] assignment counter (cnfTokenWorkSymbols rest) cnfFinish index
            combinedAssignmentBound counterBound terminalFormulaBound
          refine ⟨malformedLiteralSymbolStepCount [] assignment counter
              (cnfTokenWorkSymbols rest) cnfFinish index,
            tape, ?_, ?_⟩
          · rw [formulaGrammarControlUnits_literal]
            apply Nat.le_trans terminalBound
            apply Nat.mul_le_mul_right (literalUnitCharge n)
            calc
              index + 1 ≤ index + 1 + rest.length :=
                Nat.le_add_right (index + 1) rest.length
              _ ≤ index + 1 + rest.length + 1 :=
                Nat.le_succ (index + 1 + rest.length)
              _ = index + (CNFToken.finish :: rest).length + 1 := by
                rw [List.length_cons]
                exact indexSuccRest_eq_indexRestOne index rest.length
          · unfold formulaGrammarFailureStart grammarCertificateTail
            unfold malformedLiteralSymbolStart at hReject
            repeat' rw [frameWork_append_assoc] at hReject ⊢
            exact hReject
  | @literalF positive index rest tail ih =>
      intro control assignment counter left right n assignmentBound
        counterBound counterAllowed formulaBound
      cases control with
      | literal alreadySatisfied positive index =>
          have formulaAllowed : ∀ symbol,
              List.Mem symbol (cnfTokenWorkSymbols rest) →
                FormulaScanSymbol symbol := by
            intro symbol member
            exact cnfTokenWorkSymbols_formulaScan rest symbol member
          have literalFormulaBound :
              index + (cnfTokenWorkSymbols rest).length ≤ n := by
            rw [cnfTokenWorkSymbols_length]
            rw [formulaGrammarControlPrefix_literal] at formulaBound
            rw [List.length_cons] at formulaBound
            exact Nat.le_trans
              (Nat.add_le_add_left (Nat.le_succ rest.length) index)
              formulaBound
          have literalBound := literalSemanticStepCount_le_indexCharge n
            counter (cnfTokenWorkSymbols rest) [] assignment index
            (by
              rw [show ([] : BitString).length = 0 from rfl, Nat.zero_add]
              exact assignmentBound)
            counterBound literalFormulaBound
          let result := alreadySatisfied ||
            checkLiteral
              ({ positive := positive, variableIndex := index } : CNFLiteral)
              assignment
          let continuedLeft := cnfF ::
            pushWorkLeft (List.replicate index cnfT)
              ((if positive then cnfT else cnfF) :: left)
          have literalRun := literalIndex_full_count_exact alreadySatisfied
            positive index assignment counter (cnfTokenWorkSymbols rest)
            left right counterAllowed formulaAllowed
          have tailFormulaBound :
              formulaGrammarControlPrefix
                  (FormulaGrammarControl.clauseContinue result) +
                rest.length ≤ n := by
            rw [formulaGrammarControlPrefix_clauseContinue, Nat.zero_add]
            rw [formulaGrammarControlPrefix_literal] at formulaBound
            rw [List.length_cons] at formulaBound
            exact Nat.le_trans (Nat.le_add_left rest.length index)
              (Nat.le_trans
                (Nat.add_le_add_left (Nat.le_succ rest.length) index)
                formulaBound)
          rcases ih (FormulaGrammarControl.clauseContinue result)
              assignment counter continuedLeft right n assignmentBound
              counterBound counterAllowed tailFormulaBound with
            ⟨remainingSteps, tape, remainingBound, remainingRun⟩
          unfold literalSemanticStart literalSemanticFinal at literalRun
          unfold formulaGrammarFailureStart at remainingRun
          unfold result continuedLeft grammarCertificateTail at remainingRun
          have complete := workRunExact?_compose cnfWorkMachine
            (literalSemanticStepCount counter (cnfTokenWorkSymbols rest) []
              assignment index)
            remainingSteps _ _ _ literalRun remainingRun
          refine ⟨literalSemanticStepCount counter
              (cnfTokenWorkSymbols rest) [] assignment index +
            remainingSteps, tape, ?_, ?_⟩
          · rw [formulaGrammarControlUnits_clauseContinue]
              at remainingBound
            rw [formulaGrammarControlUnits_literal]
            have combined := add_charged_blocks n (index + 1)
              (rest.length + 1)
              (literalSemanticStepCount counter
                (cnfTokenWorkSymbols rest) [] assignment index)
              remainingSteps literalBound remainingBound
            apply Nat.le_trans combined
            apply Nat.le_of_eq
            apply congrArg (fun coefficient =>
              coefficient * literalUnitCharge n)
            rw [List.length_cons]
            exact indexOneRestOne_eq_indexRestOneOne index rest.length
          · unfold formulaGrammarFailureStart grammarCertificateTail
            repeat' rw [frameWork_append_assoc] at complete ⊢
            exact complete
  | @literalT positive index rest tail ih =>
      intro control assignment counter left right n assignmentBound
        counterBound counterAllowed formulaBound
      cases control with
      | literal alreadySatisfied positive index =>
          have tailFormulaBound :
              formulaGrammarControlPrefix
                  (FormulaGrammarControl.literal alreadySatisfied positive
                    (index + 1)) +
                rest.length ≤ n := by
            rw [formulaGrammarControlPrefix_literal]
            rw [formulaGrammarControlPrefix_literal] at formulaBound
            rw [List.length_cons, Nat.add_succ] at formulaBound
            rw [Nat.add_comm index 1, Nat.succ_add]
            rw [Nat.zero_add]
            rw [Nat.succ_add]
            exact formulaBound
          rcases ih
              (FormulaGrammarControl.literal alreadySatisfied positive
                (index + 1))
              assignment counter left right n assignmentBound counterBound
              counterAllowed
              tailFormulaBound with
            ⟨steps, tape, stepBound, hReject⟩
          refine ⟨steps, tape, ?_, ?_⟩
          · rw [formulaGrammarControlUnits_literal] at stepBound ⊢
            apply Nat.le_trans stepBound
            apply Nat.le_of_eq
            apply congrArg (fun coefficient =>
              coefficient * literalUnitCharge n)
            rw [List.length_cons]
            exact indexSuccRest_eq_indexRestOne index rest.length
          · change workRunExact? cnfWorkMachine steps
                (workConfigAtWord
                  (CNFWorkState.literalIndex alreadySatisfied positive)
                  (cnfBoundaryGuard :: left)
                  (List.replicate (index + 1) cnfT ++
                    (cnfTokenWorkSymbols rest ++
                      grammarCertificateTail assignment counter right))) =
              some ({ state := CNFWorkState.reject, tape := tape } :
                WorkConfiguration) at hReject
            change workRunExact? cnfWorkMachine steps
                (workConfigAtWord
                  (CNFWorkState.literalIndex alreadySatisfied positive)
                  (cnfBoundaryGuard :: left)
                  (List.replicate index cnfT ++
                    ((cnfT :: cnfTokenWorkSymbols rest) ++
                      grammarCertificateTail assignment counter right))) =
              some ({ state := CNFWorkState.reject, tape := tape } :
                WorkConfiguration)
            have startShape :
                List.replicate (index + 1) cnfT ++
                    (cnfTokenWorkSymbols rest ++
                      grammarCertificateTail assignment counter right) =
                  List.replicate index cnfT ++
                    ((cnfT :: cnfTokenWorkSymbols rest) ++
                      grammarCertificateTail assignment counter right) := by
              rw [replicate_succ_tail]
              rw [frameWork_append_assoc]
              rfl
            rw [← startShape]
            exact hReject

theorem formulaGrammarFailure_machine_withinSinglePhase
    {mode : FormulaGrammarMode} {tokens : List CNFToken}
    (failure : FormulaGrammarFailure mode tokens)
    (control : FormulaGrammarControl mode)
    (assignment : BitString) (counter left right : List WorkSymbol)
    (n : Nat)
    (assignmentBound : assignment.length ≤ n)
    (counterBound : counter.length ≤ n)
    (counterAllowed : ∀ symbol, List.Mem symbol counter →
      symbol = cnfMarkFalse)
    (formulaBound :
      formulaGrammarControlPrefix control + tokens.length ≤ n) :
    ∃ steps tape,
      steps ≤ cnfSinglePhaseBudget n ∧
      workRunExact? cnfWorkMachine steps
          (formulaGrammarFailureStart control tokens assignment counter
            left right) =
        some ({ state := CNFWorkState.reject, tape := tape } :
          WorkConfiguration) := by
  rcases formulaGrammarFailure_machine_charge failure control assignment
      counter left right n assignmentBound counterBound counterAllowed
      formulaBound with ⟨steps, tape, chargeBound, exactRun⟩
  have unitsBound : formulaGrammarControlUnits control tokens ≤
      cnfShiftedWorkSpan n := by
    unfold formulaGrammarControlUnits
    have successorBound := Nat.add_le_add_right formulaBound 1
    have nToSpan : n + 1 ≤ cnfShiftedWorkSpan n := by
      unfold cnfShiftedWorkSpan
      exact Nat.add_le_add_left (Nat.le_succ 1) n
    exact Nat.le_trans successorBound nToSpan
  have phaseBound := clauseLiteral_accumulated_le_singlePhaseBudget n
    (formulaGrammarControlUnits control tokens) (literalUnitCharge n) steps
    unitsBound (Nat.le_refl (literalUnitCharge n)) chargeBound
  exact ⟨steps, tape, phaseBound, exactRun⟩

end GrammarClauseBoundDesign
end PNP.Concrete


namespace PNP.Concrete

namespace GrammarHeaderDesign

open FrameTraceDesign
open ClauseLiteralDesign
open ClauseLiteralCostDesign
open GrammarFailureDesign
open GrammarClauseDesign
open WidthSuccessDesign

set_option maxRecDepth 100000

def widthMalformedTailStart
    (outerCounter counter formulaTail : List WorkSymbol)
    (processed remaining : BitString) (count : Nat)
    (suffix : List WorkSymbol) : WorkConfiguration :=
  workConfigAtWord CNFWorkState.widthFindFormula
    (pushWorkLeft (List.replicate processed.length cnfMarkTrue)
      (cnfFinish :: pushWorkLeft outerCounter [cnfRootGuard]))
    ((List.replicate count cnfT ++ formulaTail) ++
      (cnfBoundaryGuard ::
        (counter ++
          (cnfFinish ::
            (markedAssignmentWorkSymbols processed ++
              (assignmentWorkSymbols remaining ++
                cnfRootGuard :: suffix))))))

def widthMalformedTailStepCount
    (outerCounter counter formulaTail : List WorkSymbol)
    (processed : BitString) : Nat → BitString → Nat
  | 0, _ => 1
  | Nat.succ count, [] =>
      1 + widthTerminalRejectSteps
        (List.replicate count cnfT ++ formulaTail) counter
        (markedAssignmentWorkSymbols processed)
  | Nat.succ count, value :: rest =>
      widthOneUnitSteps outerCounter
          (List.replicate processed.length cnfMarkTrue)
          (List.replicate count cnfT ++ formulaTail)
          counter (markedAssignmentWorkSymbols processed) +
        widthMalformedTailStepCount outerCounter counter formulaTail
          (processed ++ [value]) count rest

theorem replicate_t_append_formula_allowed
    (count : Nat) (formulaTail : List WorkSymbol)
    (formulaAllowed : ∀ symbol, List.Mem symbol formulaTail →
      FormulaScanSymbol symbol) :
    ∀ symbol,
      List.Mem symbol (List.replicate count cnfT ++ formulaTail) →
        FormulaScanSymbol symbol := by
  intro symbol member
  have split := workSymbol_mem_append_cases
    (List.replicate count cnfT) formulaTail symbol member
  cases split with
  | inl inPrefix =>
      have equal := mem_replicate_workSymbol_eq count cnfT symbol inPrefix
      cases equal
      exact .t
  | inr inTail => exact formulaAllowed symbol inTail

theorem widthMalformedTail_exact
    (outerCounter counter formulaTail : List WorkSymbol)
    (processed remaining : BitString) (count : Nat)
    (suffix : List WorkSymbol)
    (outerAllowed : ∀ symbol, List.Mem symbol outerCounter →
      symbol = cnfMarkFalse)
    (counterAllowed : ∀ symbol, List.Mem symbol counter →
      symbol = cnfMarkFalse)
    (formulaAllowed : ∀ symbol, List.Mem symbol formulaTail →
      FormulaScanSymbol symbol)
    (headInvalid : ∀ head rest, formulaTail = head :: rest →
      ¬ WidthHeaderSymbol head) :
    ∃ tape,
      workRunExact? cnfWorkMachine
          (widthMalformedTailStepCount outerCounter counter formulaTail
            processed count remaining)
          (widthMalformedTailStart outerCounter counter formulaTail
            processed remaining count suffix) =
        some
          ({ state := CNFWorkState.reject, tape := tape } :
            WorkConfiguration) := by
  induction count generalizing processed remaining with
  | zero =>
      cases formulaTail with
      | nil =>
          have invalid : ¬ WidthHeaderSymbol cnfBoundaryGuard := by
            intro allowed
            cases allowed
          let right := counter ++
            (cnfFinish ::
              (markedAssignmentWorkSymbols processed ++
                (assignmentWorkSymbols remaining ++
                  cnfRootGuard :: suffix)))
          have hReject := widthFindFormula_reject_run
            (pushWorkLeft (List.replicate processed.length cnfMarkTrue)
              (cnfFinish :: pushWorkLeft outerCounter [cnfRootGuard]))
            right cnfBoundaryGuard invalid
          refine ⟨(workConfigAtWord CNFWorkState.reject
            (pushWorkLeft (List.replicate processed.length cnfMarkTrue)
              (cnfFinish :: pushWorkLeft outerCounter [cnfRootGuard]))
            (cnfBoundaryGuard :: right)).tape, ?_⟩
          unfold widthMalformedTailStepCount widthMalformedTailStart right
          exact hReject
      | cons head rest =>
          have invalid := headInvalid head rest rfl
          let right := rest ++
            (cnfBoundaryGuard ::
              (counter ++
                (cnfFinish ::
                  (markedAssignmentWorkSymbols processed ++
                    (assignmentWorkSymbols remaining ++
                      cnfRootGuard :: suffix)))))
          have hReject := widthFindFormula_reject_run
            (pushWorkLeft (List.replicate processed.length cnfMarkTrue)
              (cnfFinish :: pushWorkLeft outerCounter [cnfRootGuard]))
            right head invalid
          refine ⟨(workConfigAtWord CNFWorkState.reject
            (pushWorkLeft (List.replicate processed.length cnfMarkTrue)
              (cnfFinish :: pushWorkLeft outerCounter [cnfRootGuard]))
            (head :: right)).tape, ?_⟩
          unfold widthMalformedTailStepCount widthMalformedTailStart right
          repeat' rw [frameWork_append_assoc]
          exact hReject
  | succ count ih =>
      cases remaining with
      | nil =>
          let leftBase :=
            pushWorkLeft (List.replicate processed.length cnfMarkTrue)
              (cnfFinish :: pushWorkLeft outerCounter [cnfRootGuard])
          let nextFormulaTail :=
            List.replicate count cnfT ++ formulaTail
          have nextFormulaAllowed : ∀ symbol,
              List.Mem symbol nextFormulaTail →
                FormulaScanSymbol symbol := by
            exact replicate_t_append_formula_allowed count formulaTail
              formulaAllowed
          have hMark := workRunExact?_one_of_step cnfWorkMachine _ _
            (widthFindFormula_mark_step leftBase
              (nextFormulaTail ++
                (cnfBoundaryGuard ::
                  (counter ++
                    (cnfFinish ::
                      (markedAssignmentWorkSymbols processed ++
                        cnfRootGuard :: suffix))))))
          have hShort := width_short_assignment_reject nextFormulaTail
            counter (markedAssignmentWorkSymbols processed)
            (cnfMarkTrue :: leftBase) suffix nextFormulaAllowed
            counterAllowed (markedAssignmentWorkSymbols_allowed processed)
          have complete := workRunExact?_compose cnfWorkMachine 1
            (widthTerminalRejectSteps nextFormulaTail counter
              (markedAssignmentWorkSymbols processed))
            _ _ _ hMark hShort
          refine ⟨(workConfigAtWord CNFWorkState.reject
            (pushWorkLeft (markedAssignmentWorkSymbols processed)
              (cnfFinish :: pushWorkLeft counter
                (cnfBoundaryGuard ::
                  pushWorkLeft nextFormulaTail
                    (cnfMarkTrue :: leftBase))))
            (cnfRootGuard :: suffix)).tape, ?_⟩
          unfold widthMalformedTailStepCount widthMalformedTailStart
          unfold widthTerminalRejectSteps at complete ⊢
          unfold nextFormulaTail leftBase at complete ⊢
          exact complete
      | cons value rest =>
          let nextFormulaTail :=
            List.replicate count cnfT ++ formulaTail
          have nextFormulaAllowed : ∀ symbol,
              List.Mem symbol nextFormulaTail →
                FormulaScanSymbol symbol := by
            exact replicate_t_append_formula_allowed count formulaTail
              formulaAllowed
          have headerAllowed : ∀ symbol,
              List.Mem symbol
                  (List.replicate processed.length cnfMarkTrue) →
                symbol = cnfMarkTrue := by
            intro symbol member
            exact mem_replicate_workSymbol_eq processed.length cnfMarkTrue
              symbol member
          have hUnit := widthOneUnit_run outerCounter
            (List.replicate processed.length cnfMarkTrue) nextFormulaTail
            counter (markedAssignmentWorkSymbols processed)
            (assignmentWorkSymbols rest ++ cnfRootGuard :: suffix) value
            outerAllowed headerAllowed nextFormulaAllowed counterAllowed
            (markedAssignmentWorkSymbols_allowed processed)
          rcases ih (processed ++ [value]) rest with
            ⟨tape, hRest⟩
          unfold widthMalformedTailStart at hRest
          rw [length_append_value] at hRest
          rw [replicate_succ_tail] at hRest
          rw [markedAssignment_append_value_tail processed value
            (assignmentWorkSymbols rest ++ cnfRootGuard :: suffix)] at hRest
          have markedValueShape :
              markedAssignmentValueWorkSymbol value =
                if value then cnfMarkTrue else cnfMarkFalse := by
            cases value <;> rfl
          rw [markedValueShape] at hRest
          have complete := workRunExact?_compose cnfWorkMachine
            (widthOneUnitSteps outerCounter
              (List.replicate processed.length cnfMarkTrue) nextFormulaTail
              counter (markedAssignmentWorkSymbols processed))
            (widthMalformedTailStepCount outerCounter counter formulaTail
              (processed ++ [value]) count rest)
            _ _ _ hUnit hRest
          refine ⟨tape, ?_⟩
          unfold widthMalformedTailStepCount widthMalformedTailStart
          unfold nextFormulaTail at complete
          rw [assignmentWorkSymbols_cons]
          rw [assignmentValueWorkSymbol_eq_if]
          exact complete

def formulaHeaderFailureStart
    (outerCounter counter : List WorkSymbol) (assignment : BitString)
    (count : Nat) (tokens : List CNFToken)
    (suffix : List WorkSymbol) : WorkConfiguration :=
  widthMalformedTailStart outerCounter counter
    (cnfTokenWorkSymbols tokens) [] assignment count suffix

inductive FormulaHeaderControl : FormulaGrammarMode → Type where
  | header (count : Nat) : FormulaHeaderControl (.header count)

def formulaHeaderControlStart {mode : FormulaGrammarMode}
    (control : FormulaHeaderControl mode)
    (outerCounter counter : List WorkSymbol) (assignment : BitString)
    (tokens : List CNFToken) (suffix : List WorkSymbol) :
    WorkConfiguration :=
  match control with
  | .header count =>
      formulaHeaderFailureStart outerCounter counter assignment count tokens
        suffix

theorem formulaHeaderFailure_machine_exact
    (outerCounter counter : List WorkSymbol) (assignment : BitString)
    (suffix : List WorkSymbol)
    (outerAllowed : ∀ symbol, List.Mem symbol outerCounter →
      symbol = cnfMarkFalse)
    (counterAllowed : ∀ symbol, List.Mem symbol counter →
      symbol = cnfMarkFalse)
    {mode : FormulaGrammarMode} {tokens : List CNFToken}
    (failure : FormulaGrammarFailure mode tokens) :
    ∀ control : FormulaHeaderControl mode,
    ∃ steps tape,
      workRunExact? cnfWorkMachine steps
          (formulaHeaderControlStart control outerCounter counter assignment
            tokens suffix) =
        some
          ({ state := CNFWorkState.reject, tape := tape } :
            WorkConfiguration) := by
  induction failure with
  | headerEmpty count =>
      intro control
      cases control
      have formulaAllowed : ∀ symbol,
          List.Mem symbol ([] : List WorkSymbol) →
            FormulaScanSymbol symbol := by
        intro symbol member
        contradiction
      have headInvalid : ∀ head rest,
          ([] : List WorkSymbol) = head :: rest →
            ¬ WidthHeaderSymbol head := by
        intro head rest equal
        contradiction
      rcases widthMalformedTail_exact outerCounter counter [] [] assignment
          count suffix outerAllowed counterAllowed formulaAllowed headInvalid
          with ⟨tape, hReject⟩
      exact ⟨widthMalformedTailStepCount outerCounter counter [] [] count
        assignment, tape, hReject⟩
  | headerSep count rest =>
      intro control
      cases control
      have formulaAllowed : ∀ symbol,
          List.Mem symbol (cnfTokenWorkSymbols (.sep :: rest)) →
            FormulaScanSymbol symbol := by
        intro symbol member
        exact cnfTokenWorkSymbols_formulaScan (.sep :: rest) symbol member
      have headInvalid : ∀ head tail,
          cnfTokenWorkSymbols (.sep :: rest) = head :: tail →
            ¬ WidthHeaderSymbol head := by
        intro head tail equal allowed
        change cnfSep :: cnfTokenWorkSymbols rest = head :: tail at equal
        cases equal
        cases allowed
      rcases widthMalformedTail_exact outerCounter counter
          (cnfTokenWorkSymbols (.sep :: rest)) [] assignment count suffix
          outerAllowed counterAllowed formulaAllowed headInvalid with
        ⟨tape, hReject⟩
      exact ⟨widthMalformedTailStepCount outerCounter counter
        (cnfTokenWorkSymbols (.sep :: rest)) [] count assignment,
        tape, hReject⟩
  | headerFinish count rest =>
      intro control
      cases control
      have formulaAllowed : ∀ symbol,
          List.Mem symbol (cnfTokenWorkSymbols (.finish :: rest)) →
            FormulaScanSymbol symbol := by
        intro symbol member
        exact cnfTokenWorkSymbols_formulaScan (.finish :: rest) symbol member
      have headInvalid : ∀ head tail,
          cnfTokenWorkSymbols (.finish :: rest) = head :: tail →
            ¬ WidthHeaderSymbol head := by
        intro head tail equal allowed
        change cnfFinish :: cnfTokenWorkSymbols rest = head :: tail at equal
        cases equal
        cases allowed
      rcases widthMalformedTail_exact outerCounter counter
          (cnfTokenWorkSymbols (.finish :: rest)) [] assignment count suffix
          outerAllowed counterAllowed formulaAllowed headInvalid with
        ⟨tape, hReject⟩
      exact ⟨widthMalformedTailStepCount outerCounter counter
        (cnfTokenWorkSymbols (.finish :: rest)) [] count assignment,
        tape, hReject⟩
  | @headerT count rest tail ih =>
      intro control
      cases control
      rcases ih (FormulaHeaderControl.header (count + 1)) with
        ⟨steps, tape, hReject⟩
      refine ⟨steps, tape, ?_⟩
      unfold formulaHeaderControlStart at hReject ⊢
      unfold formulaHeaderFailureStart at hReject ⊢
      unfold widthMalformedTailStart at hReject ⊢
      change workRunExact? cnfWorkMachine steps
          (workConfigAtWord CNFWorkState.widthFindFormula
            (pushWorkLeft (List.replicate 0 cnfMarkTrue)
              (cnfFinish :: pushWorkLeft outerCounter [cnfRootGuard]))
            ((List.replicate (count + 1) cnfT ++
                cnfTokenWorkSymbols rest) ++
              (cnfBoundaryGuard ::
                (counter ++
                  (cnfFinish ::
                    (markedAssignmentWorkSymbols [] ++
                      (assignmentWorkSymbols assignment ++
                        cnfRootGuard :: suffix))))))) =
        some ({ state := CNFWorkState.reject, tape := tape } :
          WorkConfiguration) at hReject
      change workRunExact? cnfWorkMachine steps
          (workConfigAtWord CNFWorkState.widthFindFormula
            (pushWorkLeft (List.replicate 0 cnfMarkTrue)
              (cnfFinish :: pushWorkLeft outerCounter [cnfRootGuard]))
            ((List.replicate count cnfT ++
                (cnfT :: cnfTokenWorkSymbols rest)) ++
              (cnfBoundaryGuard ::
                (counter ++
                  (cnfFinish ::
                    (markedAssignmentWorkSymbols [] ++
                      (assignmentWorkSymbols assignment ++
                        cnfRootGuard :: suffix))))))) =
        some ({ state := CNFWorkState.reject, tape := tape } :
          WorkConfiguration)
      have headerShape :
          List.replicate (count + 1) cnfT ++
              cnfTokenWorkSymbols rest =
            List.replicate count cnfT ++
              (cnfT :: cnfTokenWorkSymbols rest) := by
        rw [replicate_succ_tail]
        rw [frameWork_append_assoc]
        rfl
      rw [← headerShape]
      exact hReject
  | @headerF count rest tail ih =>
      intro control
      cases control
      have formulaAllowed : ∀ symbol,
          List.Mem symbol (cnfTokenWorkSymbols rest) →
            FormulaScanSymbol symbol := by
        intro symbol member
        exact cnfTokenWorkSymbols_formulaScan rest symbol member
      cases equalCase : natEqual count assignment.length with
      | false =>
          have different : count ≠ assignment.length := by
            intro equal
            have equalTrue :=
              (natEqual_eq_true_iff count assignment.length).mpr equal
            rw [equalCase] at equalTrue
            contradiction
          rcases widthMismatch_exact outerCounter counter
              (cnfTokenWorkSymbols rest) [] assignment count suffix
              outerAllowed counterAllowed formulaAllowed different with
            ⟨final, hReject, finalReject⟩
          cases final with
          | mk finalState tape =>
              change finalState = CNFWorkState.reject at finalReject
              cases finalReject
              refine ⟨widthMismatchStepCount outerCounter counter
                (cnfTokenWorkSymbols rest) [] count assignment, tape, ?_⟩
              unfold formulaHeaderControlStart
              unfold formulaHeaderFailureStart widthMalformedTailStart
              exact hReject
      | true =>
          have equal :=
            (natEqual_eq_true_iff count assignment.length).mp equalCase
          have widthRun := widthLoop_success_exact outerCounter counter
            (cnfTokenWorkSymbols rest) [] assignment suffix outerAllowed
            counterAllowed formulaAllowed
          rcases formulaGrammarFailure_machine_exact tail
              FormulaGrammarControl.clauses assignment counter
              (cnfF ::
                pushWorkLeft (List.replicate assignment.length cnfT)
                  (cnfFinish :: pushWorkLeft outerCounter [cnfRootGuard]))
              suffix counterAllowed with
            ⟨remainingSteps, tape, remainingRun⟩
          unfold formulaGrammarFailureStart grammarCertificateTail
            at remainingRun
          change workRunExact? cnfWorkMachine remainingSteps
              (workConfigAtWord CNFWorkState.clauseStart
                (cnfF ::
                  pushWorkLeft (List.replicate assignment.length cnfT)
                    (cnfFinish ::
                      pushWorkLeft outerCounter [cnfRootGuard]))
                (cnfTokenWorkSymbols rest ++
                  (cnfBoundaryGuard ::
                    (counter ++
                      (cnfFinish ::
                        (assignmentWorkSymbols assignment ++
                          cnfRootGuard :: suffix)))))) =
            some ({ state := CNFWorkState.reject, tape := tape } :
              WorkConfiguration) at remainingRun
          have emptyLength : ([] : BitString).length = 0 := rfl
          rw [emptyLength] at widthRun
          rw [Nat.zero_add] at widthRun
          change workRunExact? cnfWorkMachine
              (widthLoopStepCount outerCounter counter
                (cnfTokenWorkSymbols rest) [] assignment) _ =
            some (workConfigAtWord CNFWorkState.clauseStart
              (cnfF ::
                pushWorkLeft (List.replicate assignment.length cnfT)
                  (cnfFinish :: pushWorkLeft outerCounter [cnfRootGuard]))
              (cnfTokenWorkSymbols rest ++
                (cnfBoundaryGuard ::
                  (counter ++
                    (cnfFinish ::
                      (assignmentWorkSymbols assignment ++
                        cnfRootGuard :: suffix)))))) at widthRun
          have complete := workRunExact?_compose cnfWorkMachine
            (widthLoopStepCount outerCounter counter
              (cnfTokenWorkSymbols rest) [] assignment)
            remainingSteps _ _ _ widthRun remainingRun
          refine ⟨widthLoopStepCount outerCounter counter
              (cnfTokenWorkSymbols rest) [] assignment + remainingSteps,
            tape, ?_⟩
          unfold formulaHeaderControlStart formulaHeaderFailureStart
            widthMalformedTailStart
          rw [equal]
          repeat' rw [frameWork_append_assoc] at complete ⊢
          exact complete
  | clausesEmpty =>
      intro control
      cases control
  | clausesF rest =>
      intro control
      cases control
  | clausesT rest =>
      intro control
      cases control
  | @clausesSep rest tail ih =>
      intro control
      cases control
  | clausesFinishTrailing next rest =>
      intro control
      cases control
  | clauseEmpty =>
      intro control
      cases control
  | clauseSep rest =>
      intro control
      cases control
  | @clauseF rest tail ih =>
      intro control
      cases control
  | @clauseT rest tail ih =>
      intro control
      cases control
  | @clauseFinish rest tail ih =>
      intro control
      cases control
  | literalEmpty positive index =>
      intro control
      cases control
  | literalSep positive index rest =>
      intro control
      cases control
  | literalFinish positive index rest =>
      intro control
      cases control
  | @literalF positive index rest tail ih =>
      intro control
      cases control
  | @literalT positive index rest tail ih =>
      intro control
      cases control

end GrammarHeaderDesign

end PNP.Concrete


namespace PNP.Concrete
namespace GrammarHeaderBoundDesign

open FrameTraceDesign
open ClauseLiteralDesign
open ClauseLiteralCostDesign
open WidthSuccessDesign
open GrammarFailureDesign
open GrammarClauseDesign
open GrammarClauseBoundDesign
open GrammarHeaderDesign
open GrammarTerminalBoundDesign

set_option maxRecDepth 100000

theorem widthMalformedTailStepCount_le_charges
    (n : Nat) (outerCounter counter formulaTail : List WorkSymbol)
    (processed remaining : BitString) (count : Nat)
    (formulaPartition :
      processed.length + count + formulaTail.length ≤ outerCounter.length)
    (assignmentPartition :
      processed.length + remaining.length ≤ counter.length)
    (outerBound : outerCounter.length ≤ n)
    (counterBound : counter.length ≤ n) :
    widthMalformedTailStepCount outerCounter counter formulaTail processed
        count remaining ≤
      (count + 1) * (cnfShiftedWorkSpan n * 12) := by
  induction count generalizing processed remaining with
  | zero =>
      unfold widthMalformedTailStepCount
      rw [Nat.one_mul]
      have oneSpan : 1 ≤ cnfShiftedWorkSpan n := by
        unfold cnfShiftedWorkSpan
        change Nat.succ 0 ≤ Nat.succ (Nat.succ n)
        exact Nat.succ_le_succ (Nat.zero_le (Nat.succ n))
      exact Nat.le_trans oneSpan
        (Nat.le_mul_of_pos_right (cnfShiftedWorkSpan n)
          (Nat.zero_lt_succ 11))
  | succ count ih =>
      cases remaining with
      | nil =>
          let nextFormulaTail :=
            List.replicate count cnfT ++ formulaTail
          have nextToOuter : nextFormulaTail.length ≤
              outerCounter.length := by
            have withPrefix : processed.length + 1 +
                nextFormulaTail.length ≤ outerCounter.length := by
              unfold nextFormulaTail
              rw [workSymbol_length_append, workSymbol_replicate_length]
              change processed.length + 1 +
                  (count + formulaTail.length) ≤ outerCounter.length
              rw [width_add_succ_swap processed.length count]
                at formulaPartition
              rw [Nat.add_assoc] at formulaPartition
              exact formulaPartition
            exact Nat.le_trans
              (Nat.le_add_left nextFormulaTail.length
                (processed.length + 1)) withPrefix
          have nextBound := Nat.le_trans nextToOuter outerBound
          have processedToCounter : processed.length ≤ counter.length := by
            change processed.length + 0 ≤ counter.length
              at assignmentPartition
            exact assignmentPartition
          have markedBound :
              (markedAssignmentWorkSymbols processed).length ≤ n := by
            rw [markedAssignmentWorkSymbols_length]
            exact Nat.le_trans processedToCounter counterBound
          have rejectBound := widthTerminalRejectSteps_le_fourSpan n
            nextFormulaTail counter (markedAssignmentWorkSymbols processed)
            nextBound counterBound markedBound
          have rejectCharge := widthCost_promote_scaled
            (cnfShiftedWorkSpan n)
            (1 + widthTerminalRejectSteps nextFormulaTail counter
              (markedAssignmentWorkSymbols processed))
            4 12 rejectBound (by
              change 4 ≤ 4 + 8
              exact Nat.le_add_right 4 8)
          unfold widthMalformedTailStepCount
          unfold nextFormulaTail at rejectCharge
          exact Nat.le_trans rejectCharge
            (Nat.le_mul_of_pos_left (cnfShiftedWorkSpan n * 12)
              (Nat.zero_lt_succ (Nat.succ count)))
      | cons value rest =>
          let nextFormulaTail :=
            List.replicate count cnfT ++ formulaTail
          have unitFormulaPartition :
              (List.replicate processed.length cnfMarkTrue).length + 1 +
                  nextFormulaTail.length ≤ outerCounter.length := by
            unfold nextFormulaTail
            rw [workSymbol_replicate_length, workSymbol_length_append,
              workSymbol_replicate_length]
            change processed.length + 1 +
                (count + formulaTail.length) ≤ outerCounter.length
            rw [width_add_succ_swap processed.length count]
              at formulaPartition
            rw [Nat.add_assoc] at formulaPartition
            exact formulaPartition
          have processedToCounter : processed.length ≤ counter.length :=
            Nat.le_trans
              (Nat.le_add_right processed.length (value :: rest).length)
              assignmentPartition
          have markedToCounter :
              (markedAssignmentWorkSymbols processed).length ≤
                counter.length := by
            rw [markedAssignmentWorkSymbols_length]
            exact processedToCounter
          have unitBound := widthOneUnitSteps_le_twelveSpan n outerCounter
            (List.replicate processed.length cnfMarkTrue) nextFormulaTail
            counter (markedAssignmentWorkSymbols processed)
            unitFormulaPartition markedToCounter outerBound counterBound
          have nextFormulaPartition :
              (processed ++ [value]).length + count + formulaTail.length ≤
                outerCounter.length := by
            rw [length_append_value]
            change (processed.length + 1) + count + formulaTail.length ≤
              outerCounter.length
            rw [width_add_succ_swap processed.length count]
              at formulaPartition
            exact formulaPartition
          have nextAssignmentPartition :
              (processed ++ [value]).length + rest.length ≤
                counter.length := by
            rw [length_append_value]
            change (processed.length + 1) + rest.length ≤ counter.length
            change processed.length + (rest.length + 1) ≤ counter.length
              at assignmentPartition
            rw [width_add_succ_swap processed.length rest.length]
              at assignmentPartition
            exact assignmentPartition
          have restBound := ih (processed ++ [value]) rest
            nextFormulaPartition nextAssignmentPartition
          unfold widthMalformedTailStepCount
          exact Nat.le_trans (Nat.add_le_add unitBound restBound)
            (Nat.le_of_eq
              (widthCharge_plus_successor_mul count
                (cnfShiftedWorkSpan n * 12)))

def formulaHeaderControlPrefix {mode : FormulaGrammarMode} :
    FormulaHeaderControl mode → Nat
  | .header count => count

def formulaHeaderControlUnits {mode : FormulaGrammarMode}
    (control : FormulaHeaderControl mode) (tokens : List CNFToken) : Nat :=
  formulaHeaderControlPrefix control + tokens.length + 1

theorem formulaHeaderControlPrefix_header (count : Nat) :
    formulaHeaderControlPrefix (FormulaHeaderControl.header count) =
      count := rfl

theorem formulaHeaderControlUnits_header
    (count : Nat) (tokens : List CNFToken) :
    formulaHeaderControlUnits (FormulaHeaderControl.header count) tokens =
      count + tokens.length + 1 := rfl

theorem formulaHeaderFailure_segmented_atWidth
    (outerCounter counter : List WorkSymbol) (assignment : BitString)
    (suffix : List WorkSymbol) (n : Nat)
    (outerAllowed : ∀ symbol, List.Mem symbol outerCounter →
      symbol = cnfMarkFalse)
    (counterAllowed : ∀ symbol, List.Mem symbol counter →
      symbol = cnfMarkFalse)
    (outerBound : outerCounter.length ≤ n)
    (counterBound : counter.length ≤ n)
    (assignmentBound : assignment.length ≤ n)
    (assignmentPartition : assignment.length ≤ counter.length)
    {mode : FormulaGrammarMode} {tokens : List CNFToken}
    (failure : FormulaGrammarFailure mode tokens) :
    ∀ control : FormulaHeaderControl mode,
      formulaHeaderControlPrefix control + tokens.length ≤
        outerCounter.length →
      ∃ widthSteps middle grammarSteps tape,
        widthSteps ≤ formulaHeaderControlUnits control tokens *
          (cnfShiftedWorkSpan n * 12) ∧
        grammarSteps ≤ cnfSinglePhaseBudget n ∧
        workRunExact? cnfWorkMachine widthSteps
            (formulaHeaderControlStart control outerCounter counter assignment
              tokens suffix) = some middle ∧
        workRunExact? cnfWorkMachine grammarSteps middle =
          some ({ state := CNFWorkState.reject, tape := tape } :
            WorkConfiguration) := by
  induction failure with
  | headerEmpty count =>
      intro control formulaPartition
      cases control
      have formulaAllowed : ∀ symbol,
          List.Mem symbol ([] : List WorkSymbol) →
            FormulaScanSymbol symbol := by
        intro symbol member
        contradiction
      have headInvalid : ∀ head rest,
          ([] : List WorkSymbol) = head :: rest →
            ¬ WidthHeaderSymbol head := by
        intro head rest equal
        contradiction
      rcases widthMalformedTail_exact outerCounter counter [] [] assignment
          count suffix outerAllowed counterAllowed formulaAllowed headInvalid
          with ⟨tape, widthRun⟩
      have rawWidthBound := widthMalformedTailStepCount_le_charges n
        outerCounter counter [] [] assignment count
        (by
          rw [formulaHeaderControlPrefix_header] at formulaPartition
          rw [show ([] : List CNFToken).length = 0 from rfl,
            Nat.add_zero] at formulaPartition
          change 0 + count + 0 ≤ outerCounter.length
          rw [Nat.zero_add, Nat.add_zero]
          exact formulaPartition)
        (by
          change 0 + assignment.length ≤ counter.length
          rw [Nat.zero_add]
          exact assignmentPartition)
        outerBound counterBound
      let middle : WorkConfiguration :=
        { state := CNFWorkState.reject, tape := tape }
      refine ⟨widthMalformedTailStepCount outerCounter counter [] [] count
          assignment, middle, 0, tape, ?_, ?_, ?_, rfl⟩
      · rw [formulaHeaderControlUnits_header]
        exact rawWidthBound
      · exact Nat.zero_le (cnfSinglePhaseBudget n)
      · exact widthRun
  | headerSep count rest =>
      intro control formulaPartition
      cases control
      have formulaAllowed : ∀ symbol,
          List.Mem symbol (cnfTokenWorkSymbols (.sep :: rest)) →
            FormulaScanSymbol symbol := by
        intro symbol member
        exact cnfTokenWorkSymbols_formulaScan (.sep :: rest) symbol member
      have headInvalid : ∀ head tail,
          cnfTokenWorkSymbols (.sep :: rest) = head :: tail →
            ¬ WidthHeaderSymbol head := by
        intro head tail equal allowed
        change cnfSep :: cnfTokenWorkSymbols rest = head :: tail at equal
        cases equal
        cases allowed
      rcases widthMalformedTail_exact outerCounter counter
          (cnfTokenWorkSymbols (.sep :: rest)) [] assignment count suffix
          outerAllowed counterAllowed formulaAllowed headInvalid with
        ⟨tape, widthRun⟩
      have malformedPartition :
          ([] : BitString).length + count +
              (cnfTokenWorkSymbols (.sep :: rest)).length ≤
            outerCounter.length := by
        rw [cnfTokenWorkSymbols_length]
        rw [show ([] : BitString).length = 0 from rfl, Nat.zero_add]
        rw [formulaHeaderControlPrefix_header] at formulaPartition
        exact formulaPartition
      have rawWidthBound := widthMalformedTailStepCount_le_charges n
        outerCounter counter (cnfTokenWorkSymbols (.sep :: rest)) []
        assignment count malformedPartition
        (by
          change 0 + assignment.length ≤ counter.length
          rw [Nat.zero_add]
          exact assignmentPartition)
        outerBound counterBound
      let middle : WorkConfiguration :=
        { state := CNFWorkState.reject, tape := tape }
      refine ⟨widthMalformedTailStepCount outerCounter counter
          (cnfTokenWorkSymbols (.sep :: rest)) [] count assignment,
        middle, 0, tape, ?_, ?_, ?_, rfl⟩
      · rw [formulaHeaderControlUnits_header]
        apply Nat.le_trans rawWidthBound
        apply Nat.mul_le_mul_right (cnfShiftedWorkSpan n * 12)
        exact Nat.add_le_add_right
          (Nat.le_add_right count (.sep :: rest).length) 1
      · exact Nat.zero_le (cnfSinglePhaseBudget n)
      · exact widthRun
  | headerFinish count rest =>
      intro control formulaPartition
      cases control
      have formulaAllowed : ∀ symbol,
          List.Mem symbol (cnfTokenWorkSymbols (.finish :: rest)) →
            FormulaScanSymbol symbol := by
        intro symbol member
        exact cnfTokenWorkSymbols_formulaScan (.finish :: rest) symbol member
      have headInvalid : ∀ head tail,
          cnfTokenWorkSymbols (.finish :: rest) = head :: tail →
            ¬ WidthHeaderSymbol head := by
        intro head tail equal allowed
        change cnfFinish :: cnfTokenWorkSymbols rest = head :: tail at equal
        cases equal
        cases allowed
      rcases widthMalformedTail_exact outerCounter counter
          (cnfTokenWorkSymbols (.finish :: rest)) [] assignment count suffix
          outerAllowed counterAllowed formulaAllowed headInvalid with
        ⟨tape, widthRun⟩
      have malformedPartition :
          ([] : BitString).length + count +
              (cnfTokenWorkSymbols (.finish :: rest)).length ≤
            outerCounter.length := by
        rw [cnfTokenWorkSymbols_length]
        rw [show ([] : BitString).length = 0 from rfl, Nat.zero_add]
        rw [formulaHeaderControlPrefix_header] at formulaPartition
        exact formulaPartition
      have rawWidthBound := widthMalformedTailStepCount_le_charges n
        outerCounter counter (cnfTokenWorkSymbols (.finish :: rest)) []
        assignment count malformedPartition
        (by
          change 0 + assignment.length ≤ counter.length
          rw [Nat.zero_add]
          exact assignmentPartition)
        outerBound counterBound
      let middle : WorkConfiguration :=
        { state := CNFWorkState.reject, tape := tape }
      refine ⟨widthMalformedTailStepCount outerCounter counter
          (cnfTokenWorkSymbols (.finish :: rest)) [] count assignment,
        middle, 0, tape, ?_, ?_, ?_, rfl⟩
      · rw [formulaHeaderControlUnits_header]
        apply Nat.le_trans rawWidthBound
        apply Nat.mul_le_mul_right (cnfShiftedWorkSpan n * 12)
        exact Nat.add_le_add_right
          (Nat.le_add_right count (.finish :: rest).length) 1
      · exact Nat.zero_le (cnfSinglePhaseBudget n)
      · exact widthRun
  | @headerT count rest tail ih =>
      intro control formulaPartition
      cases control
      have tailPartition :
          formulaHeaderControlPrefix
              (FormulaHeaderControl.header (count + 1)) + rest.length ≤
            outerCounter.length := by
        rw [formulaHeaderControlPrefix_header]
        rw [formulaHeaderControlPrefix_header] at formulaPartition
        rw [List.length_cons] at formulaPartition
        rw [width_add_succ_swap count rest.length] at formulaPartition
        exact formulaPartition
      rcases ih (FormulaHeaderControl.header (count + 1)) tailPartition with
        ⟨widthSteps, middle, grammarSteps, tape, widthBound, grammarBound,
          widthRun, grammarRun⟩
      refine ⟨widthSteps, middle, grammarSteps, tape, ?_, grammarBound,
        ?_, grammarRun⟩
      · rw [formulaHeaderControlUnits_header] at widthBound ⊢
        rw [List.length_cons]
        rw [width_add_succ_swap count rest.length]
        exact widthBound
      · have startShape :
            formulaHeaderControlStart (FormulaHeaderControl.header count)
                outerCounter counter assignment (.t :: rest) suffix =
              formulaHeaderControlStart
                (FormulaHeaderControl.header (count + 1)) outerCounter counter
                assignment rest suffix := by
          unfold formulaHeaderControlStart formulaHeaderFailureStart
            widthMalformedTailStart
          change workConfigAtWord CNFWorkState.widthFindFormula
              (pushWorkLeft (List.replicate 0 cnfMarkTrue)
                (cnfFinish :: pushWorkLeft outerCounter [cnfRootGuard]))
              ((List.replicate count cnfT ++
                  (cnfT :: cnfTokenWorkSymbols rest)) ++
                (cnfBoundaryGuard ::
                  (counter ++
                    (cnfFinish ::
                      (markedAssignmentWorkSymbols [] ++
                        (assignmentWorkSymbols assignment ++
                          cnfRootGuard :: suffix)))))) =
            workConfigAtWord CNFWorkState.widthFindFormula
              (pushWorkLeft (List.replicate 0 cnfMarkTrue)
                (cnfFinish :: pushWorkLeft outerCounter [cnfRootGuard]))
              ((List.replicate (count + 1) cnfT ++
                  cnfTokenWorkSymbols rest) ++
                (cnfBoundaryGuard ::
                  (counter ++
                    (cnfFinish ::
                      (markedAssignmentWorkSymbols [] ++
                        (assignmentWorkSymbols assignment ++
                          cnfRootGuard :: suffix))))))
          have headerShape :
              List.replicate (count + 1) cnfT ++
                  cnfTokenWorkSymbols rest =
                List.replicate count cnfT ++
                  (cnfT :: cnfTokenWorkSymbols rest) := by
            rw [replicate_succ_tail]
            rw [frameWork_append_assoc]
            rfl
          rw [headerShape]
        rw [startShape]
        exact widthRun
  | @headerF count rest tail ih =>
      intro control formulaPartition
      cases control
      have formulaAllowed : ∀ symbol,
          List.Mem symbol (cnfTokenWorkSymbols rest) →
            FormulaScanSymbol symbol := by
        intro symbol member
        exact cnfTokenWorkSymbols_formulaScan rest symbol member
      have normalizedFormulaPartition :
          ([] : BitString).length + count + 1 +
              (cnfTokenWorkSymbols rest).length ≤
            outerCounter.length := by
        rw [show ([] : BitString).length = 0 from rfl, Nat.zero_add]
        rw [cnfTokenWorkSymbols_length]
        rw [formulaHeaderControlPrefix_header] at formulaPartition
        rw [List.length_cons] at formulaPartition
        rw [width_add_succ_swap count rest.length] at formulaPartition
        exact formulaPartition
      have normalizedAssignmentPartition :
          ([] : BitString).length + assignment.length ≤ counter.length := by
        rw [show ([] : BitString).length = 0 from rfl, Nat.zero_add]
        exact assignmentPartition
      cases equalCase : natEqual count assignment.length with
      | false =>
          have different : count ≠ assignment.length := by
            intro equal
            have equalTrue :=
              (natEqual_eq_true_iff count assignment.length).mpr equal
            rw [equalCase] at equalTrue
            contradiction
          rcases widthMismatch_exact outerCounter counter
              (cnfTokenWorkSymbols rest) [] assignment count suffix
              outerAllowed counterAllowed formulaAllowed different with
            ⟨final, exactWidth, finalReject⟩
          have rawWidthBound := widthMismatchStepCount_le_charges n
            outerCounter counter (cnfTokenWorkSymbols rest) [] assignment
            count normalizedFormulaPartition normalizedAssignmentPartition
            outerBound counterBound
          cases final with
          | mk finalState tape =>
              change finalState = CNFWorkState.reject at finalReject
              cases finalReject
              let middle : WorkConfiguration :=
                { state := CNFWorkState.reject, tape := tape }
              refine ⟨widthMismatchStepCount outerCounter counter
                  (cnfTokenWorkSymbols rest) [] count assignment,
                middle, 0, tape, ?_, ?_, ?_, rfl⟩
              · rw [formulaHeaderControlUnits_header]
                apply Nat.le_trans rawWidthBound
                apply Nat.mul_le_mul_right (cnfShiftedWorkSpan n * 12)
                exact Nat.add_le_add_right
                  (Nat.le_add_right count (.f :: rest).length) 1
              · exact Nat.zero_le (cnfSinglePhaseBudget n)
              · unfold formulaHeaderControlStart formulaHeaderFailureStart
                  widthMalformedTailStart
                exact exactWidth
      | true =>
          have equal :=
            (natEqual_eq_true_iff count assignment.length).mp equalCase
          have exactWidth := widthLoop_success_exact outerCounter counter
            (cnfTokenWorkSymbols rest) [] assignment suffix outerAllowed
            counterAllowed formulaAllowed
          have loopPartition :
              (([] : BitString).length + assignment.length + 1) +
                  (cnfTokenWorkSymbols rest).length ≤
                outerCounter.length := by
            have normalized := normalizedFormulaPartition
            rw [show ([] : BitString).length = 0 from rfl, Nat.zero_add]
              at normalized
            rw [show ([] : BitString).length = 0 from rfl, Nat.zero_add]
            rw [← equal]
            exact normalized
          have rawWidthBound := widthLoopStepCount_le_charges n outerCounter
            counter (cnfTokenWorkSymbols rest) [] assignment loopPartition
            normalizedAssignmentPartition outerBound counterBound
          let clauseLeft := cnfF ::
            pushWorkLeft (List.replicate assignment.length cnfT)
              (cnfFinish :: pushWorkLeft outerCounter [cnfRootGuard])
          have clauseFormulaBound :
              formulaGrammarControlPrefix FormulaGrammarControl.clauses +
                rest.length ≤ n := by
            rw [formulaGrammarControlPrefix_clauses, Nat.zero_add]
            apply Nat.le_trans _ outerBound
            apply Nat.le_trans
              (Nat.le_add_left rest.length (count + 1))
            rw [← width_add_succ_swap count rest.length]
            rw [formulaHeaderControlPrefix_header] at formulaPartition
            rw [List.length_cons] at formulaPartition
            exact formulaPartition
          rcases formulaGrammarFailure_machine_withinSinglePhase tail
              FormulaGrammarControl.clauses assignment counter clauseLeft
              suffix n assignmentBound counterBound counterAllowed
              clauseFormulaBound with
            ⟨grammarSteps, tape, grammarBound, grammarRun⟩
          let middle := formulaGrammarFailureStart
            FormulaGrammarControl.clauses rest assignment counter clauseLeft
            suffix
          refine ⟨widthLoopStepCount outerCounter counter
              (cnfTokenWorkSymbols rest) [] assignment,
            middle, grammarSteps, tape, ?_, grammarBound, ?_, grammarRun⟩
          · rw [formulaHeaderControlUnits_header]
            apply Nat.le_trans rawWidthBound
            apply Nat.mul_le_mul_right (cnfShiftedWorkSpan n * 12)
            rw [← equal]
            exact Nat.add_le_add_right
              (Nat.le_add_right count (.f :: rest).length) 1
          · unfold middle formulaGrammarFailureStart grammarCertificateTail
            unfold clauseLeft
            change workRunExact? cnfWorkMachine
                (widthLoopStepCount outerCounter counter
                  (cnfTokenWorkSymbols rest) [] assignment)
                (formulaHeaderControlStart
                  (FormulaHeaderControl.header count) outerCounter counter
                  assignment (.f :: rest) suffix) =
              some (workConfigAtWord CNFWorkState.clauseStart clauseLeft
                (cnfTokenWorkSymbols rest ++
                  (cnfBoundaryGuard ::
                    (counter ++
                      (cnfFinish ::
                        (assignmentWorkSymbols assignment ++
                          cnfRootGuard :: suffix))))))
            unfold formulaHeaderControlStart formulaHeaderFailureStart
              widthMalformedTailStart
            rw [equal]
            have emptyLength : ([] : BitString).length = 0 := rfl
            rw [emptyLength, Nat.zero_add] at exactWidth
            change workRunExact? cnfWorkMachine
                (widthLoopStepCount outerCounter counter
                  (cnfTokenWorkSymbols rest) [] assignment) _ =
              some (workConfigAtWord CNFWorkState.clauseStart clauseLeft
                (cnfTokenWorkSymbols rest ++
                  (cnfBoundaryGuard ::
                    (counter ++
                      (cnfFinish ::
                        (assignmentWorkSymbols assignment ++
                          cnfRootGuard :: suffix)))))) at exactWidth
            repeat' rw [frameWork_append_assoc] at exactWidth ⊢
            exact exactWidth
  | clausesEmpty =>
      intro control
      cases control
  | clausesF rest =>
      intro control
      cases control
  | clausesT rest =>
      intro control
      cases control
  | @clausesSep rest tail ih =>
      intro control
      cases control
  | clausesFinishTrailing next rest =>
      intro control
      cases control
  | clauseEmpty =>
      intro control
      cases control
  | clauseSep rest =>
      intro control
      cases control
  | @clauseF rest tail ih =>
      intro control
      cases control
  | @clauseT rest tail ih =>
      intro control
      cases control
  | @clauseFinish rest tail ih =>
      intro control
      cases control
  | literalEmpty positive index =>
      intro control
      cases control
  | literalSep positive index rest =>
      intro control
      cases control
  | literalFinish positive index rest =>
      intro control
      cases control
  | @literalF positive index rest tail ih =>
      intro control
      cases control
  | @literalT positive index rest tail ih =>
      intro control
      cases control

end GrammarHeaderBoundDesign
end PNP.Concrete


namespace PNP.Concrete
namespace UniversalCompositionDesign

open FrameTraceDesign
open ClauseLiteralCostDesign

set_option maxRecDepth 100000

/-- The exact work-level outcome needed by the generic six-step compiler. -/
def CNFWorkOutcome (input certificate : BitString) : Prop :=
  ∃ steps final,
    steps ≤ cnfWorkStepPolynomial.eval
      (BitString.size (BitString.pair input certificate)) ∧
    workRunExact? cnfWorkMachine steps
        (workStartConfiguration cnfWorkMachine
          (pairedWorkTape input certificate)) = some final ∧
    final.state =
      if checkEncodedCertificate input certificate then
        CNFWorkState.accept
      else
        CNFWorkState.reject

/-- The shape already provided by each complete malformed branch. -/
def CNFSinglePhaseReject (input certificate : BitString) : Prop :=
  ∃ steps tape,
    steps ≤ cnfSinglePhaseBudget
      (BitString.size (BitString.pair input certificate)) ∧
    workRunExact? cnfWorkMachine steps
        (workStartConfiguration cnfWorkMachine
          (pairedWorkTape input certificate)) =
      some
        ({ state := CNFWorkState.reject, tape := tape } :
          WorkConfiguration)

theorem cnfWorkOutcome_halted (input certificate : BitString)
    (final : WorkConfiguration)
    (finalState : final.state =
      if checkEncodedCertificate input certificate then
        CNFWorkState.accept
      else
        CNFWorkState.reject) :
    cnfWorkMachine.isHalted final = true := by
  cases checked : checkEncodedCertificate input certificate with
  | false =>
      rw [checked] at finalState
      change final.state = CNFWorkState.reject at finalState
      unfold WorkMachine.isHalted cnfWorkMachine
      rw [finalState]
      rfl
  | true =>
      rw [checked] at finalState
      change final.state = CNFWorkState.accept at finalState
      unfold WorkMachine.isHalted cnfWorkMachine
      rw [finalState]
      rfl

/-- A one-phase malformed rejection is already enough for the full cubic
ledger; the two later phases are zero-step runs of the halted reject state. -/
theorem cnfWorkOutcome_of_singlePhaseReject
    (input certificate : BitString)
    (checkedFalse : checkEncodedCertificate input certificate = false)
    (rejected : CNFSinglePhaseReject input certificate) :
    CNFWorkOutcome input certificate := by
  rcases rejected with ⟨steps, tape, stepBound, exactRun⟩
  let start := workStartConfiguration cnfWorkMachine
    (pairedWorkTape input certificate)
  let final : WorkConfiguration :=
    { state := CNFWorkState.reject, tape := tape }
  have fixedRun : workRunExact? cnfWorkMachine 0 start = some start := rfl
  have finalRun : workRunExact? cnfWorkMachine 0 final = some final := rfl
  have halted : cnfWorkMachine.isHalted final = true := by
    rfl
  rcases cnfWorkExact_phaseLedger
      (BitString.size (BitString.pair input certificate))
      0 steps 0 0 start start final final final
      fixedRun exactRun finalRun finalRun
      (Nat.zero_le 8) stepBound
      (Nat.zero_le (cnfSinglePhaseBudget
        (BitString.size (BitString.pair input certificate))))
      (Nat.zero_le (cnfSinglePhaseBudget
        (BitString.size (BitString.pair input certificate)))) halted with
    ⟨total, totalBound, totalRun, _, _⟩
  refine ⟨total, final, totalBound, totalRun, ?_⟩
  rw [checkedFalse]
  rfl

/-- Name the successful frame endpoint so that the remaining width theorem
can expose a compact, stable signature. -/
def decodedFrameFinal (formula : CNFFormula) (assignment : BitString) :
    WorkConfiguration :=
  workConfigAtLeftWord CNFWorkState.seekLeftRoot
    (pushWorkLeft
      (List.replicate assignment.length cnfMarkFalse)
      (cnfBoundaryGuard ::
        frameFormulaLeftBase (encodeFormulaTokens formula)))
    (cnfFinish ::
      (assignmentWorkSymbols assignment ++
        [cnfRootGuard, cnfBlank]))

/-- The canonical clause-phase input after a successful equal-width pass. -/
def decodedClauseStart (formula : CNFFormula) (assignment : BitString)
    (left : List WorkSymbol) : WorkConfiguration :=
  workConfigAtWord CNFWorkState.clauseStart left
    (cnfTokenWorkSymbols
        (encodeClauseListTokens formula.clauses ++ [.finish]) ++
      (cnfBoundaryGuard ::
        (List.replicate assignment.length cnfMarkFalse ++
          (cnfFinish ::
            (assignmentWorkSymbols assignment ++
              [cnfRootGuard, cnfBlank])))))

/-- Equal-width decoded inputs need only one width trace.  The already-clean
formula prototype supplies the entire clause/literal trace and its phase
bound; this theorem performs the exact phase ledger composition. -/
theorem cnfCanonicalOutcome_of_widthTrace
    (input certificate : BitString) (formula : CNFFormula)
    (assignment : BitString) (widthSteps : Nat)
    (clauseLeft : List WorkSymbol)
    (formulaDecoded : decodeEncodedCNF input = some formula)
    (assignmentDecoded :
      decodeAssignmentCertificate certificate = some assignment)
    (width : assignment.length = formula.variableCount)
    (widthBound : widthSteps ≤ cnfSinglePhaseBudget
      (BitString.size (BitString.pair input certificate)))
    (widthRun : workRunExact? cnfWorkMachine widthSteps
      (decodedFrameFinal formula assignment) =
        some (decodedClauseStart formula assignment clauseLeft)) :
    CNFWorkOutcome input certificate := by
  let n := BitString.size (BitString.pair input certificate)
  let start := workStartConfiguration cnfWorkMachine
    (pairedWorkTape input certificate)
  let afterFrame := decodedFrameFinal formula assignment
  let afterWidth := decodedClauseStart formula assignment clauseLeft
  have frameRun : workRunExact? cnfWorkMachine
      (frameSuccessSteps (encodeFormulaTokens formula) assignment)
      start = some afterFrame := by
    unfold start afterFrame decodedFrameFinal
    exact decoded_frames_success_exact input certificate formula assignment
      formulaDecoded assignmentDecoded
  have frameBound :
      frameSuccessSteps (encodeFormulaTokens formula) assignment ≤
        cnfSinglePhaseBudget n := by
    unfold n
    exact decoded_frameSuccessSteps_le_pair_singlePhase
      input certificate formula assignment formulaDecoded assignmentDecoded
  rcases canonical_formula_semantic_withinPairSinglePhase
      input certificate formula assignment clauseLeft [cnfBlank]
      formulaDecoded assignmentDecoded width with
    ⟨final, grammarBound, grammarRun, finalState⟩
  have halted : cnfWorkMachine.isHalted final = true := by
    cases checked : checkCNF formula assignment with
    | false =>
        rw [checked] at finalState
        change final.state = CNFWorkState.reject at finalState
        unfold WorkMachine.isHalted cnfWorkMachine
        rw [finalState]
        rfl
    | true =>
        rw [checked] at finalState
        change final.state = CNFWorkState.accept at finalState
        unfold WorkMachine.isHalted cnfWorkMachine
        rw [finalState]
        rfl
  have fixedRun : workRunExact? cnfWorkMachine 0 start = some start := rfl
  rcases cnfWorkExact_phaseLedger n 0
      (frameSuccessSteps (encodeFormulaTokens formula) assignment)
      widthSteps
      (formulaSemanticStepCount assignment
        (List.replicate assignment.length cnfMarkFalse) formula.clauses)
      start start afterFrame afterWidth final
      fixedRun frameRun widthRun grammarRun (Nat.zero_le 8)
      frameBound widthBound grammarBound halted with
    ⟨total, totalBound, totalRun, _, _⟩
  have checkedShape :
      checkEncodedCertificate input certificate =
        checkCNF formula assignment := by
    unfold checkEncodedCertificate
    rw [formulaDecoded, assignmentDecoded]
  refine ⟨total, final, totalBound, totalRun, ?_⟩
  rw [checkedShape]
  exact finalState

/-- The raw formula-framing branch is already discharged by the published
malformed-fuel checkpoint. -/
theorem formulaRawContract_available
    (input certificate : BitString)
    (decoded : decodeFormulaTokenPairs input = none) :
    CNFSinglePhaseReject input certificate := by
  unfold CNFSinglePhaseReject
  exact MalformedFuelDesign.formulaRawDecoder_none_rejects_withinPairSinglePhase
    input certificate decoded

/-- The raw assignment-framing branch is likewise already discharged. -/
theorem assignmentRawContract_available
    (input certificate : BitString) (formula : CNFFormula)
    (formulaDecoded : decodeEncodedCNF input = some formula)
    (decoded : decodeTokenPairs certificate = none) :
    CNFSinglePhaseReject input certificate := by
  unfold CNFSinglePhaseReject
  exact
    MalformedFuelDesign.assignmentRawDecoder_none_rejects_withinPairSinglePhase
      input certificate formula formulaDecoded decoded

theorem checkEncodedCertificate_false_of_width_ne
    (input certificate : BitString) (formula : CNFFormula)
    (assignment : BitString)
    (formulaDecoded : decodeEncodedCNF input = some formula)
    (assignmentDecoded :
      decodeAssignmentCertificate certificate = some assignment)
    (widthNe : assignment.length ≠ formula.variableCount) :
    checkEncodedCertificate input certificate = false := by
  have checkFalse : checkCNF formula assignment = false := by
    unfold checkCNF
    cases widthCase : natEqual assignment.length formula.variableCount with
    | false => rfl
    | true =>
        have widthEq :=
          (natEqual_eq_true_iff assignment.length formula.variableCount).mp
            widthCase
        exact False.elim (widthNe widthEq)
  unfold checkEncodedCertificate
  rw [formulaDecoded]
  rw [assignmentDecoded]
  exact checkFalse

/-- A decoded unequal-width rejection consumes the frame and width phases;
the grammar phase is a zero-step run of the halted reject state. -/
theorem cnfWidthMismatchOutcome_of_widthTrace
    (input certificate : BitString) (formula : CNFFormula)
    (assignment : BitString) (widthSteps : Nat) (tape : WorkTape)
    (formulaDecoded : decodeEncodedCNF input = some formula)
    (assignmentDecoded :
      decodeAssignmentCertificate certificate = some assignment)
    (widthNe : assignment.length ≠ formula.variableCount)
    (widthBound : widthSteps ≤ cnfSinglePhaseBudget
      (BitString.size (BitString.pair input certificate)))
    (widthRun : workRunExact? cnfWorkMachine widthSteps
      (decodedFrameFinal formula assignment) =
        some
          ({ state := CNFWorkState.reject, tape := tape } :
            WorkConfiguration)) :
    CNFWorkOutcome input certificate := by
  let n := BitString.size (BitString.pair input certificate)
  let start := workStartConfiguration cnfWorkMachine
    (pairedWorkTape input certificate)
  let afterFrame := decodedFrameFinal formula assignment
  let final : WorkConfiguration :=
    { state := CNFWorkState.reject, tape := tape }
  have frameRun : workRunExact? cnfWorkMachine
      (frameSuccessSteps (encodeFormulaTokens formula) assignment)
      start = some afterFrame := by
    unfold start afterFrame decodedFrameFinal
    exact decoded_frames_success_exact input certificate formula assignment
      formulaDecoded assignmentDecoded
  have frameBound :
      frameSuccessSteps (encodeFormulaTokens formula) assignment ≤
        cnfSinglePhaseBudget n := by
    unfold n
    exact decoded_frameSuccessSteps_le_pair_singlePhase
      input certificate formula assignment formulaDecoded assignmentDecoded
  have fixedRun : workRunExact? cnfWorkMachine 0 start = some start := rfl
  have finalRun : workRunExact? cnfWorkMachine 0 final = some final := rfl
  have halted : cnfWorkMachine.isHalted final = true := by
    rfl
  rcases cnfWorkExact_phaseLedger n 0
      (frameSuccessSteps (encodeFormulaTokens formula) assignment)
      widthSteps 0 start start afterFrame final final
      fixedRun frameRun widthRun finalRun (Nat.zero_le 8)
      frameBound widthBound (Nat.zero_le (cnfSinglePhaseBudget n)) halted with
    ⟨total, totalBound, totalRun, _, _⟩
  have checkedFalse := checkEncodedCertificate_false_of_width_ne
    input certificate formula assignment formulaDecoded assignmentDecoded
      widthNe
  refine ⟨total, final, totalBound, totalRun, ?_⟩
  rw [checkedFalse]
  rfl

/-- These two global width contracts are the only missing semantic bridge on
successfully decoded inputs. -/
theorem cnfCanonicalOutcome_of_widthContracts
    (equalWidth : ∀ input certificate formula assignment,
      decodeEncodedCNF input = some formula →
      decodeAssignmentCertificate certificate = some assignment →
      assignment.length = formula.variableCount →
      ∃ steps left,
        steps ≤ cnfSinglePhaseBudget
          (BitString.size (BitString.pair input certificate)) ∧
        workRunExact? cnfWorkMachine steps
          (decodedFrameFinal formula assignment) =
            some (decodedClauseStart formula assignment left))
    (unequalWidth : ∀ input certificate formula assignment,
      decodeEncodedCNF input = some formula →
      decodeAssignmentCertificate certificate = some assignment →
      assignment.length ≠ formula.variableCount →
      ∃ steps tape,
        steps ≤ cnfSinglePhaseBudget
          (BitString.size (BitString.pair input certificate)) ∧
        workRunExact? cnfWorkMachine steps
          (decodedFrameFinal formula assignment) =
            some
              ({ state := CNFWorkState.reject, tape := tape } :
                WorkConfiguration))
    (input certificate : BitString) (formula : CNFFormula)
    (assignment : BitString)
    (formulaDecoded : decodeEncodedCNF input = some formula)
    (assignmentDecoded :
      decodeAssignmentCertificate certificate = some assignment) :
    CNFWorkOutcome input certificate := by
  cases widthCase : natEqual assignment.length formula.variableCount with
  | false =>
      have widthNe : assignment.length ≠ formula.variableCount := by
        intro widthEq
        have widthTrue :=
          (natEqual_eq_true_iff assignment.length formula.variableCount).mpr
            widthEq
        rw [widthCase] at widthTrue
        contradiction
      rcases unequalWidth input certificate formula assignment formulaDecoded
          assignmentDecoded widthNe with
        ⟨steps, tape, stepBound, exactRun⟩
      exact cnfWidthMismatchOutcome_of_widthTrace input certificate formula
        assignment steps tape formulaDecoded assignmentDecoded widthNe
        stepBound exactRun
  | true =>
      have widthEq :=
        (natEqual_eq_true_iff assignment.length formula.variableCount).mp
          widthCase
      rcases equalWidth input certificate formula assignment formulaDecoded
          assignmentDecoded widthEq with
        ⟨steps, left, stepBound, exactRun⟩
      exact cnfCanonicalOutcome_of_widthTrace input certificate formula
        assignment steps left formulaDecoded assignmentDecoded widthEq
        stepBound exactRun

/-- This is the exact exhaustive dependency split.  Four malformed contracts
plus the decoded canonical contract imply the universal work theorem. -/
theorem cnfWorkOutcome_of_decoderContracts
    (formulaRaw : ∀ input certificate,
      decodeFormulaTokenPairs input = none →
      CNFSinglePhaseReject input certificate)
    (formulaGrammar : ∀ input certificate tokens,
      decodeFormulaTokenPairs input = some tokens →
      decodeCNFTokens tokens = none →
      CNFWorkOutcome input certificate)
    (assignmentRaw : ∀ input certificate formula,
      decodeEncodedCNF input = some formula →
      decodeTokenPairs certificate = none →
      CNFSinglePhaseReject input certificate)
    (assignmentGrammar : ∀ input certificate formula tokens,
      decodeEncodedCNF input = some formula →
      decodeTokenPairs certificate = some tokens →
      decodeAssignmentTokens tokens = none →
      CNFSinglePhaseReject input certificate)
    (canonical : ∀ input certificate formula assignment,
      decodeEncodedCNF input = some formula →
      decodeAssignmentCertificate certificate = some assignment →
      CNFWorkOutcome input certificate) :
    ∀ input certificate, CNFWorkOutcome input certificate := by
  intro input certificate
  cases formulaTokensCase : decodeFormulaTokenPairs input with
  | none =>
      have formulaDecoded : decodeEncodedCNF input = none := by
        unfold decodeEncodedCNF
        rw [formulaTokensCase]
      have checkedFalse := checkEncodedCertificate_false_of_decoder_failure
        input certificate (Or.inl formulaDecoded)
      exact cnfWorkOutcome_of_singlePhaseReject input certificate
        checkedFalse (formulaRaw input certificate formulaTokensCase)
  | some formulaTokens =>
      cases formulaGrammarCase : decodeCNFTokens formulaTokens with
      | none =>
          exact formulaGrammar input certificate formulaTokens
            formulaTokensCase formulaGrammarCase
      | some formula =>
          have formulaDecoded : decodeEncodedCNF input = some formula := by
            unfold decodeEncodedCNF
            rw [formulaTokensCase]
            exact formulaGrammarCase
          cases assignmentTokensCase : decodeTokenPairs certificate with
          | none =>
              have assignmentDecoded :
                  decodeAssignmentCertificate certificate = none := by
                unfold decodeAssignmentCertificate
                rw [assignmentTokensCase]
              have checkedFalse :=
                checkEncodedCertificate_false_of_decoder_failure
                  input certificate (Or.inr assignmentDecoded)
              exact cnfWorkOutcome_of_singlePhaseReject input certificate
                checkedFalse
                (assignmentRaw input certificate formula formulaDecoded
                  assignmentTokensCase)
          | some assignmentTokens =>
              cases assignmentGrammarCase :
                  decodeAssignmentTokens assignmentTokens with
              | none =>
                  have assignmentDecoded :
                      decodeAssignmentCertificate certificate = none := by
                    unfold decodeAssignmentCertificate
                    rw [assignmentTokensCase]
                    exact assignmentGrammarCase
                  have checkedFalse :=
                    checkEncodedCertificate_false_of_decoder_failure
                      input certificate (Or.inr assignmentDecoded)
                  exact cnfWorkOutcome_of_singlePhaseReject input certificate
                    checkedFalse
                    (assignmentGrammar input certificate formula
                      assignmentTokens formulaDecoded assignmentTokensCase
                      assignmentGrammarCase)
              | some assignment =>
                  have assignmentDecoded :
                      decodeAssignmentCertificate certificate =
                        some assignment := by
                    unfold decodeAssignmentCertificate
                    rw [assignmentTokensCase]
                    exact assignmentGrammarCase
                  exact canonical input certificate formula assignment
                    formulaDecoded assignmentDecoded

/-- Universal work correctness immediately becomes direct raw-machine
acceptance at the literal sixfold compiler budget. -/
theorem cnfCompiled_accept_iff_check
    (universal : ∀ input certificate,
      CNFWorkOutcome input certificate)
    (input certificate : BitString) :
    boundedDecide cnfCompiledMachine
        (cnfCompiledStepPolynomial.eval
          (BitString.size (BitString.pair input certificate)))
        (BitString.pair input certificate) = .accept ↔
      checkEncodedCertificate input certificate = true := by
  rcases universal input certificate with
    ⟨steps, final, within, exactRun, finalState⟩
  have halted := cnfWorkOutcome_halted input certificate final finalState
  have bridge := boundedDecide_compileWorkMachine_paired_accept_iff_final
    cnfWorkMachine steps
    (cnfWorkStepPolynomial.eval
      (BitString.size (BitString.pair input certificate)))
    input certificate final exactRun halted within
  change boundedDecide (compileWorkMachine cnfWorkMachine)
      (6 * cnfWorkStepPolynomial.eval
        (BitString.size (BitString.pair input certificate)))
      (BitString.pair input certificate) = .accept ↔
    checkEncodedCertificate input certificate = true
  constructor
  · intro accepted
    have finalAccept := bridge.mp accepted
    cases checked : checkEncodedCertificate input certificate with
    | false =>
        rw [checked] at finalState
        rw [finalState] at finalAccept
        exact False.elim (Nat.noConfusion finalAccept)
    | true => rfl
  · intro checkedTrue
    apply bridge.mpr
    rw [checkedTrue] at finalState
    exact finalState

/-- The same exact outcome excludes raw timeout at the advertised budget. -/
theorem cnfCompiled_ne_timeout
    (universal : ∀ input certificate,
      CNFWorkOutcome input certificate)
    (input certificate : BitString) :
    boundedDecide cnfCompiledMachine
        (cnfCompiledStepPolynomial.eval
          (BitString.size (BitString.pair input certificate)))
      (BitString.pair input certificate) ≠ .timeout := by
  rcases universal input certificate with
    ⟨steps, final, within, exactRun, finalState⟩
  have halted := cnfWorkOutcome_halted input certificate final finalState
  change boundedDecide (compileWorkMachine cnfWorkMachine)
      (6 * cnfWorkStepPolynomial.eval
        (BitString.size (BitString.pair input certificate)))
      (BitString.pair input certificate) ≠ .timeout
  exact boundedDecide_compileWorkMachine_paired_ne_timeout
    cnfWorkMachine steps
    (cnfWorkStepPolynomial.eval
      (BitString.size (BitString.pair input certificate)))
    input certificate final exactRun halted within

theorem cnfCompiled_reject_iff_check_false
    (universal : ∀ input certificate,
      CNFWorkOutcome input certificate)
    (input certificate : BitString) :
    boundedDecide cnfCompiledMachine
        (cnfCompiledStepPolynomial.eval
          (BitString.size (BitString.pair input certificate)))
        (BitString.pair input certificate) = .reject ↔
      checkEncodedCertificate input certificate = false := by
  have acceptIff := cnfCompiled_accept_iff_check universal input certificate
  have noTimeout := cnfCompiled_ne_timeout universal input certificate
  constructor
  · intro rejected
    cases checked : checkEncodedCertificate input certificate with
    | false => rfl
    | true =>
        have accepted := acceptIff.mpr checked
        rw [rejected] at accepted
        contradiction
  · intro checkedFalse
    cases verdictCase : boundedDecide cnfCompiledMachine
        (cnfCompiledStepPolynomial.eval
          (BitString.size (BitString.pair input certificate)))
        (BitString.pair input certificate) with
    | accept =>
        have checkedTrue := acceptIff.mp verdictCase
        rw [checkedFalse] at checkedTrue
        contradiction
    | reject => rfl
    | timeout =>
        exact False.elim (noTimeout verdictCase)

/-- Final direct verifier: paired input mode and literal finite raw machine. -/
def cnfConcreteVerifier
    (universal : ∀ input certificate,
      CNFWorkOutcome input certificate) :
    PolynomialTimeVerifier CNFSAT :=
  cnfVerifierOfRawMachine cnfCompiledMachine cnfCompiledStepPolynomial
    (fun input certificate _ =>
      cnfCompiled_ne_timeout universal input certificate)
    (cnfCompiled_accept_iff_check universal)

theorem cnfConcreteVerifier_inputMode
    (universal : ∀ input certificate,
      CNFWorkOutcome input certificate) :
    (cnfConcreteVerifier universal).program.inputMode = .paired := by
  rfl

theorem cnfConcreteVerifier_decision
    (universal : ∀ input certificate,
      CNFWorkOutcome input certificate) :
    (cnfConcreteVerifier universal).program.decision =
      .machine cnfCompiledMachine cnfCompiledStepPolynomial := by
  rfl

theorem cnfSATInNP_of_universalWorkOutcome
    (universal : ∀ input certificate,
      CNFWorkOutcome input certificate) :
    InNP CNFSAT := by
  exact ⟨cnfConcreteVerifier universal⟩

end UniversalCompositionDesign
end PNP.Concrete



namespace PNP.Concrete
namespace UniversalHandoff

open UniversalCompositionDesign
open WidthSuccessDesign
open FrameTraceDesign

theorem cnfEqualWidthContract_available
    (input certificate : BitString) (formula : CNFFormula)
    (assignment : BitString)
    (formulaDecoded : decodeEncodedCNF input = some formula)
    (assignmentDecoded :
      decodeAssignmentCertificate certificate = some assignment)
    (width : assignment.length = formula.variableCount) :
    ∃ steps left,
      steps ≤ cnfSinglePhaseBudget
        (BitString.size (BitString.pair input certificate)) ∧
      workRunExact? cnfWorkMachine steps
        (decodedFrameFinal formula assignment) =
          some (decodedClauseStart formula assignment left) := by
  let left := cnfF ::
    pushWorkLeft
      (List.replicate assignment.length cnfT)
      (cnfFinish ::
        pushWorkLeft
          (List.replicate (encodeFormulaTokens formula).length
            cnfMarkFalse)
          [cnfRootGuard])
  have exactRun := decodedWidth_equal_exact formula assignment width
  have stepBound := decodedWidthSuccessSteps_le_pairSinglePhase
    input certificate formula assignment formulaDecoded assignmentDecoded width
  refine ⟨decodedWidthSuccessSteps formula assignment, left, stepBound, ?_⟩
  unfold decodedFrameFinal decodedClauseStart left
  exact exactRun

theorem cnfUnequalWidthContract_available
    (input certificate : BitString) (formula : CNFFormula)
    (assignment : BitString)
    (formulaDecoded : decodeEncodedCNF input = some formula)
    (assignmentDecoded :
      decodeAssignmentCertificate certificate = some assignment)
    (width : assignment.length ≠ formula.variableCount) :
    ∃ steps tape,
      steps ≤ cnfSinglePhaseBudget
        (BitString.size (BitString.pair input certificate)) ∧
      workRunExact? cnfWorkMachine steps
        (decodedFrameFinal formula assignment) =
          some
            ({ state := CNFWorkState.reject, tape := tape } :
              WorkConfiguration) := by
  have reversedWidth : formula.variableCount ≠ assignment.length := by
    intro equal
    exact width equal.symm
  rcases decodedWidth_unequal_exact formula assignment reversedWidth with
    ⟨final, exactRun, finalReject⟩
  have stepBound := decodedWidthMismatchSteps_le_pairSinglePhase
    input certificate formula assignment formulaDecoded assignmentDecoded
  refine ⟨decodedWidthMismatchSteps formula assignment, final.tape,
    stepBound, ?_⟩
  unfold decodedFrameFinal
  rw [← finalReject]
  exact exactRun

/-- After the raw-decoder and assignment-grammar checkpoints, the universal
work theorem has exactly three remaining inputs: the full formula-grammar
outcome and the equal/unequal decoded width traces. -/
theorem cnfUniversalWorkOutcome_of_formulaGrammar_widthContracts
    (formulaGrammar : ∀ input certificate tokens,
      decodeFormulaTokenPairs input = some tokens →
      decodeCNFTokens tokens = none →
      CNFWorkOutcome input certificate)
    (equalWidth : ∀ input certificate formula assignment,
      decodeEncodedCNF input = some formula →
      decodeAssignmentCertificate certificate = some assignment →
      assignment.length = formula.variableCount →
      ∃ steps left,
        steps ≤ cnfSinglePhaseBudget
          (BitString.size (BitString.pair input certificate)) ∧
        workRunExact? cnfWorkMachine steps
          (decodedFrameFinal formula assignment) =
            some (decodedClauseStart formula assignment left))
    (unequalWidth : ∀ input certificate formula assignment,
      decodeEncodedCNF input = some formula →
      decodeAssignmentCertificate certificate = some assignment →
      assignment.length ≠ formula.variableCount →
      ∃ steps tape,
        steps ≤ cnfSinglePhaseBudget
          (BitString.size (BitString.pair input certificate)) ∧
        workRunExact? cnfWorkMachine steps
          (decodedFrameFinal formula assignment) =
            some
              ({ state := CNFWorkState.reject, tape := tape } :
                WorkConfiguration)) :
    ∀ input certificate, CNFWorkOutcome input certificate := by
  exact cnfWorkOutcome_of_decoderContracts
    formulaRawContract_available formulaGrammar
    assignmentRawContract_available
    PNP.Concrete.AssignmentGrammarFailureDesign.assignmentGrammarFailure_rejects_withinPairSinglePhase
    (fun input certificate formula assignment formulaDecoded
        assignmentDecoded =>
      cnfCanonicalOutcome_of_widthContracts equalWidth unequalWidth
        input certificate formula assignment formulaDecoded
        assignmentDecoded)

/-- The sole unresolved contract after importing the complete decoded-width
and assignment-grammar checkpoints. -/
def FormulaGrammarOutcomeContract : Prop :=
  ∀ input certificate tokens,
    decodeFormulaTokenPairs input = some tokens →
    decodeCNFTokens tokens = none →
    CNFWorkOutcome input certificate

theorem cnfUniversalWorkOutcome_of_formulaGrammar
    (formulaGrammar : FormulaGrammarOutcomeContract) :
    ∀ input certificate, CNFWorkOutcome input certificate := by
  exact cnfUniversalWorkOutcome_of_formulaGrammar_widthContracts
    formulaGrammar cnfEqualWidthContract_available
    cnfUnequalWidthContract_available

theorem cnfCompiled_accept_iff_check_of_formulaGrammar
    (formulaGrammar : FormulaGrammarOutcomeContract)
    (input certificate : BitString) :
    boundedDecide cnfCompiledMachine
        (cnfCompiledStepPolynomial.eval
          (BitString.size (BitString.pair input certificate)))
        (BitString.pair input certificate) = .accept ↔
      checkEncodedCertificate input certificate = true := by
  exact cnfCompiled_accept_iff_check
    (cnfUniversalWorkOutcome_of_formulaGrammar formulaGrammar)
    input certificate

theorem cnfCompiled_reject_iff_check_false_of_formulaGrammar
    (formulaGrammar : FormulaGrammarOutcomeContract)
    (input certificate : BitString) :
    boundedDecide cnfCompiledMachine
        (cnfCompiledStepPolynomial.eval
          (BitString.size (BitString.pair input certificate)))
        (BitString.pair input certificate) = .reject ↔
      checkEncodedCertificate input certificate = false := by
  exact cnfCompiled_reject_iff_check_false
    (cnfUniversalWorkOutcome_of_formulaGrammar formulaGrammar)
    input certificate

theorem cnfCompiled_ne_timeout_of_formulaGrammar
    (formulaGrammar : FormulaGrammarOutcomeContract)
    (input certificate : BitString) :
    boundedDecide cnfCompiledMachine
        (cnfCompiledStepPolynomial.eval
          (BitString.size (BitString.pair input certificate)))
        (BitString.pair input certificate) ≠ .timeout := by
  exact cnfCompiled_ne_timeout
    (cnfUniversalWorkOutcome_of_formulaGrammar formulaGrammar)
    input certificate

def cnfConcreteVerifier_of_formulaGrammar
    (formulaGrammar : FormulaGrammarOutcomeContract) :
    PolynomialTimeVerifier CNFSAT :=
  cnfConcreteVerifier
    (cnfUniversalWorkOutcome_of_formulaGrammar formulaGrammar)

theorem cnfConcreteVerifier_of_formulaGrammar_inputMode
    (formulaGrammar : FormulaGrammarOutcomeContract) :
    (cnfConcreteVerifier_of_formulaGrammar formulaGrammar).program.inputMode =
      .paired := by
  exact cnfConcreteVerifier_inputMode
    (cnfUniversalWorkOutcome_of_formulaGrammar formulaGrammar)

theorem cnfConcreteVerifier_of_formulaGrammar_decision
    (formulaGrammar : FormulaGrammarOutcomeContract) :
    (cnfConcreteVerifier_of_formulaGrammar formulaGrammar).program.decision =
      .machine cnfCompiledMachine cnfCompiledStepPolynomial := by
  exact cnfConcreteVerifier_decision
    (cnfUniversalWorkOutcome_of_formulaGrammar formulaGrammar)

theorem cnfSATInNP_of_formulaGrammar
    (formulaGrammar : FormulaGrammarOutcomeContract) : InNP CNFSAT := by
  exact ⟨cnfConcreteVerifier_of_formulaGrammar formulaGrammar⟩

theorem cnfCompiled_accept_iff_check_of_formulaGrammar_widthContracts
    (formulaGrammar : ∀ input certificate tokens,
      decodeFormulaTokenPairs input = some tokens →
      decodeCNFTokens tokens = none →
      CNFWorkOutcome input certificate)
    (equalWidth : ∀ input certificate formula assignment,
      decodeEncodedCNF input = some formula →
      decodeAssignmentCertificate certificate = some assignment →
      assignment.length = formula.variableCount →
      ∃ steps left,
        steps ≤ cnfSinglePhaseBudget
          (BitString.size (BitString.pair input certificate)) ∧
        workRunExact? cnfWorkMachine steps
          (decodedFrameFinal formula assignment) =
            some (decodedClauseStart formula assignment left))
    (unequalWidth : ∀ input certificate formula assignment,
      decodeEncodedCNF input = some formula →
      decodeAssignmentCertificate certificate = some assignment →
      assignment.length ≠ formula.variableCount →
      ∃ steps tape,
        steps ≤ cnfSinglePhaseBudget
          (BitString.size (BitString.pair input certificate)) ∧
        workRunExact? cnfWorkMachine steps
          (decodedFrameFinal formula assignment) =
            some
              ({ state := CNFWorkState.reject, tape := tape } :
                WorkConfiguration))
    (input certificate : BitString) :
    boundedDecide cnfCompiledMachine
        (cnfCompiledStepPolynomial.eval
          (BitString.size (BitString.pair input certificate)))
        (BitString.pair input certificate) = .accept ↔
      checkEncodedCertificate input certificate = true := by
  exact cnfCompiled_accept_iff_check
    (cnfUniversalWorkOutcome_of_formulaGrammar_widthContracts
      formulaGrammar equalWidth unequalWidth) input certificate

theorem cnfSATInNP_of_formulaGrammar_widthContracts
    (formulaGrammar : ∀ input certificate tokens,
      decodeFormulaTokenPairs input = some tokens →
      decodeCNFTokens tokens = none →
      CNFWorkOutcome input certificate)
    (equalWidth : ∀ input certificate formula assignment,
      decodeEncodedCNF input = some formula →
      decodeAssignmentCertificate certificate = some assignment →
      assignment.length = formula.variableCount →
      ∃ steps left,
        steps ≤ cnfSinglePhaseBudget
          (BitString.size (BitString.pair input certificate)) ∧
        workRunExact? cnfWorkMachine steps
          (decodedFrameFinal formula assignment) =
            some (decodedClauseStart formula assignment left))
    (unequalWidth : ∀ input certificate formula assignment,
      decodeEncodedCNF input = some formula →
      decodeAssignmentCertificate certificate = some assignment →
      assignment.length ≠ formula.variableCount →
      ∃ steps tape,
        steps ≤ cnfSinglePhaseBudget
          (BitString.size (BitString.pair input certificate)) ∧
        workRunExact? cnfWorkMachine steps
          (decodedFrameFinal formula assignment) =
            some
              ({ state := CNFWorkState.reject, tape := tape } :
                WorkConfiguration)) :
    InNP CNFSAT := by
  exact cnfSATInNP_of_universalWorkOutcome
    (cnfUniversalWorkOutcome_of_formulaGrammar_widthContracts
      formulaGrammar equalWidth unequalWidth)

end UniversalHandoff
end PNP.Concrete



namespace PNP.Concrete
namespace FormulaOutcomeBridgeDesign

open FrameTraceDesign
open MalformedFuelDesign
open UniversalCompositionDesign
open UniversalHandoff

set_option maxRecDepth 100000

/-- The successful frame endpoint depends only on the decoded token stream,
not on a successful strict formula parse. -/
def tokenDecodedFrameFinal (tokens : List CNFToken)
    (assignment : BitString) : WorkConfiguration :=
  workConfigAtLeftWord CNFWorkState.seekLeftRoot
    (pushWorkLeft
      (List.replicate assignment.length cnfMarkFalse)
      (cnfBoundaryGuard :: frameFormulaLeftBase tokens))
    (cnfFinish ::
      (assignmentWorkSymbols assignment ++
        [cnfRootGuard, cnfBlank]))

theorem pairedWorkTape_of_token_decoders_some
    (input certificate : BitString) (tokens : List CNFToken)
    (assignment : BitString)
    (formulaTokensDecoded : decodeFormulaTokenPairs input = some tokens)
    (assignmentDecoded :
      decodeAssignmentCertificate certificate = some assignment) :
    pairedWorkTape input certificate =
      WorkTape.ofSymbols
        (pairedTokenLayout tokens (assignmentValueTokens assignment)) := by
  have formulaShape := encodeFormulaTokenPairs_of_decode input tokens
    formulaTokensDecoded
  have assignmentShape := encodeAssignmentCertificate_of_decode
    certificate assignment assignmentDecoded
  rw [← formulaShape, ← assignmentShape]
  rw [encodeAssignmentCertificate_eq_token_bits]
  change pairedWorkTape (paddedFormulaTokenBits tokens)
      (assignmentCertificateTokenBits (assignmentValueTokens assignment)) =
    WorkTape.ofSymbols
      (pairedTokenLayout tokens (assignmentValueTokens assignment))
  unfold pairedWorkTape
  change WorkTape.ofSymbols
      (packWorkSymbols
        ((BitString.pair (paddedFormulaTokenBits tokens)
          (assignmentCertificateTokenBits
            (assignmentValueTokens assignment))).map TapeSymbol.ofBool)) = _
  rw [packWorkSymbols_paired_flat_tokens]

theorem token_decoded_frames_success_exact
    (input certificate : BitString) (first : CNFToken)
    (rest : List CNFToken) (assignment : BitString)
    (formulaTokensDecoded :
      decodeFormulaTokenPairs input = some (first :: rest))
    (assignmentDecoded :
      decodeAssignmentCertificate certificate = some assignment) :
    workRunExact? cnfWorkMachine
        (frameSuccessSteps (first :: rest) assignment)
        (workStartConfiguration cnfWorkMachine
          (pairedWorkTape input certificate)) =
      some (tokenDecodedFrameFinal (first :: rest) assignment) := by
  rw [pairedWorkTape_of_token_decoders_some input certificate
    (first :: rest) assignment formulaTokensDecoded assignmentDecoded]
  unfold tokenDecodedFrameFinal
  exact frames_success_exact first rest assignment

theorem token_decoded_frame_payload_le_pair_size
    (input certificate : BitString) (tokens : List CNFToken)
    (assignment : BitString)
    (formulaTokensDecoded : decodeFormulaTokenPairs input = some tokens)
    (assignmentDecoded :
      decodeAssignmentCertificate certificate = some assignment) :
    tokens.length + assignment.length ≤
      BitString.size (BitString.pair input certificate) := by
  have formulaShape := encodeFormulaTokenPairs_of_decode input tokens
    formulaTokensDecoded
  have assignmentShape := encodeAssignmentCertificate_of_decode
    certificate assignment assignmentDecoded
  have tokenToInput : tokens.length ≤ BitString.size input := by
    rw [← formulaShape]
    exact tokenLength_le_encodedPairsBitSize tokens false
  have assignmentToCertificate : assignment.length ≤
      BitString.size certificate := by
    rw [← assignmentShape]
    unfold BitString.size
    rw [encodeAssignmentCertificate_eq_token_bits]
    rw [assignmentCertificateTokenBits_length]
    rw [assignmentValueTokens_length]
    have oneTwo : 0 < 2 := Nat.zero_lt_succ 1
    exact Nat.le_trans
      (Nat.le_mul_of_pos_left assignment.length oneTwo)
      (Nat.le_add_right (2 * assignment.length) 2)
  exact Nat.le_trans (Nat.add_le_add tokenToInput assignmentToCertificate)
    (componentSizes_le_pairSize input certificate)

theorem token_decoded_frameSuccessSteps_le_pairSinglePhase
    (input certificate : BitString) (tokens : List CNFToken)
    (assignment : BitString)
    (formulaTokensDecoded : decodeFormulaTokenPairs input = some tokens)
    (assignmentDecoded :
      decodeAssignmentCertificate certificate = some assignment) :
    frameSuccessSteps tokens assignment ≤
      cnfSinglePhaseBudget
        (BitString.size (BitString.pair input certificate)) := by
  have combinedBound := token_decoded_frame_payload_le_pair_size
    input certificate tokens assignment formulaTokensDecoded
    assignmentDecoded
  have inputPos : 1 ≤ BitString.size input := by
    have formulaShape := encodeFormulaTokenPairs_of_decode input tokens
      formulaTokensDecoded
    rw [← formulaShape]
    exact one_le_encodedPairsBitSize tokens false
  have fiveSpan := five_le_shiftedPairSpan_of_inputPos input certificate
    inputPos
  exact frameSuccessSteps_le_singlePhase
    (BitString.size (BitString.pair input certificate)) tokens assignment
    combinedBound fiveSpan

/-- The only frame-level fact absent from the current canonical checkpoints.
It covers both the empty formula-token stream and any malformed certificate
encountered before formula semantics can begin. -/
def FormulaFrameFailureContract : Prop :=
  ∀ input certificate tokens,
    decodeFormulaTokenPairs input = some tokens →
    (tokens = [] ∨ decodeAssignmentCertificate certificate = none) →
    CNFSinglePhaseReject input certificate

/-- A deliberately segmented post-frame contract.  Keeping the width and
grammar runs separate is necessary because each has its own single-phase
allowance in the cubic phase ledger. -/
def FormulaPostFrameRejectContract : Prop :=
  ∀ input certificate first rest assignment,
    decodeFormulaTokenPairs input = some (first :: rest) →
    decodeAssignmentCertificate certificate = some assignment →
    decodeCNFTokens (first :: rest) = none →
    ∃ widthSteps middle grammarSteps tape,
      widthSteps ≤ cnfSinglePhaseBudget
        (BitString.size (BitString.pair input certificate)) ∧
      grammarSteps ≤ cnfSinglePhaseBudget
        (BitString.size (BitString.pair input certificate)) ∧
      workRunExact? cnfWorkMachine widthSteps
          (tokenDecodedFrameFinal (first :: rest) assignment) =
        some middle ∧
      workRunExact? cnfWorkMachine grammarSteps middle =
        some
          ({ state := CNFWorkState.reject, tape := tape } :
            WorkConfiguration)

theorem formulaGrammarOutcome_of_frame_postContracts
    (frameFailure : FormulaFrameFailureContract)
    (postFrame : FormulaPostFrameRejectContract) :
    FormulaGrammarOutcomeContract := by
  intro input certificate tokens formulaTokensDecoded grammarFailed
  have formulaDecodedNone : decodeEncodedCNF input = none := by
    unfold decodeEncodedCNF
    rw [formulaTokensDecoded]
    exact grammarFailed
  have checkedFalse : checkEncodedCertificate input certificate = false :=
    checkEncodedCertificate_false_of_decoder_failure input certificate
      (Or.inl formulaDecodedNone)
  cases tokens with
  | nil =>
      exact cnfWorkOutcome_of_singlePhaseReject input certificate
        checkedFalse
        (frameFailure input certificate [] formulaTokensDecoded (Or.inl rfl))
  | cons first rest =>
      cases assignmentCase : decodeAssignmentCertificate certificate with
      | none =>
          exact cnfWorkOutcome_of_singlePhaseReject input certificate
            checkedFalse
            (frameFailure input certificate (first :: rest)
              formulaTokensDecoded (Or.inr assignmentCase))
      | some assignment =>
          rcases postFrame input certificate first rest assignment
              formulaTokensDecoded assignmentCase grammarFailed with
            ⟨widthSteps, middle, grammarSteps, tape, widthBound,
              grammarBound, widthRun, grammarRun⟩
          let n := BitString.size (BitString.pair input certificate)
          let start := workStartConfiguration cnfWorkMachine
            (pairedWorkTape input certificate)
          let afterFrame := tokenDecodedFrameFinal (first :: rest) assignment
          let final : WorkConfiguration :=
            { state := CNFWorkState.reject, tape := tape }
          have frameRun : workRunExact? cnfWorkMachine
              (frameSuccessSteps (first :: rest) assignment) start =
                some afterFrame := by
            unfold start afterFrame
            exact token_decoded_frames_success_exact input certificate first
              rest assignment formulaTokensDecoded assignmentCase
          have frameBound :
              frameSuccessSteps (first :: rest) assignment ≤
                cnfSinglePhaseBudget n := by
            unfold n
            exact token_decoded_frameSuccessSteps_le_pairSinglePhase
              input certificate (first :: rest) assignment
              formulaTokensDecoded assignmentCase
          have initialRun : workRunExact? cnfWorkMachine 0 start =
              some start := rfl
          have halted : cnfWorkMachine.isHalted final = true := by
            rfl
          change workRunExact? cnfWorkMachine grammarSteps middle =
              some final at grammarRun
          rcases cnfWorkExact_phaseLedger n 0
              (frameSuccessSteps (first :: rest) assignment)
              widthSteps grammarSteps start start afterFrame middle final
              initialRun frameRun widthRun grammarRun (Nat.zero_le 8)
              frameBound widthBound grammarBound halted with
            ⟨total, totalBound, totalRun, _, _⟩
          refine ⟨total, final, totalBound, totalRun, ?_⟩
          rw [checkedFalse]
          rfl

end FormulaOutcomeBridgeDesign
end PNP.Concrete



namespace PNP.Concrete
namespace FormulaFrameFailureDesign

open FrameTraceDesign
open MalformedFuelDesign
open UniversalCompositionDesign
open FormulaOutcomeBridgeDesign
open AssignmentGrammarFailureDesign

set_option maxRecDepth 100000

/-- A malformed raw certificate is rejected during frame two even when the
formula token stream is only pair-decoded, not grammar-decoded. -/
theorem tokenDecoded_assignmentRaw_none_rejects_withinPairSinglePhase
    (input certificate : BitString) (first : CNFToken)
    (formulaRest : List CNFToken)
    (formulaTokensDecoded :
      decodeFormulaTokenPairs input = some (first :: formulaRest))
    (decoded : decodeTokenPairs certificate = none) :
    ∃ steps tape,
      steps ≤ cnfSinglePhaseBudget
        (BitString.size (BitString.pair input certificate)) ∧
      workRunExact? cnfWorkMachine steps
          (workStartConfiguration cnfWorkMachine
            (pairedWorkTape input certificate)) =
        some
          ({ state := CNFWorkState.reject, tape := tape } :
            WorkConfiguration) := by
  have inputShape := encodeFormulaTokenPairs_of_decode input
    (first :: formulaRest) formulaTokensDecoded
  rcases decodeTokenPairs_none_shape certificate decoded with
    ⟨certificateTokens, last, certificateShape⟩
  rcases pairedWorkTape_assignmentOdd_shape
      (first :: formulaRest) certificateTokens last with
    ⟨bit, suffix, tapeShape⟩
  have hBoot := boot_t_exact
    (List.replicate formulaRest.length cnfT ++ cnfFinish ::
      (first.workSymbol ::
        (cnfTokenWorkSymbols formulaRest ++ cnfSep ::
          (List.replicate certificateTokens.length cnfT ++
            leadingZeroWorkSymbol bit :: suffix))))
  have hFrameOne := frameOne_complete_exact (first :: formulaRest)
    (List.replicate certificateTokens.length cnfT ++
      leadingZeroWorkSymbol bit :: suffix)
  rw [frameOneFoldStart_empty_cons] at hFrameOne
  let leftBase :=
    pushWorkLeft (cnfTokenWorkSymbols (first :: formulaRest))
      (cnfFinish ::
        pushWorkLeft
          (List.replicate (first :: formulaRest).length cnfMarkFalse)
          [cnfRootGuard])
  rcases frameTwoMalformedHeader_reject certificateTokens.length bit
      (cnfBoundaryGuard :: leftBase) suffix with ⟨finalLeft, hReject⟩
  have hBootFrameOne := workRunExact?_compose cnfWorkMachine 2
    (frameOneFoldSteps [] [] (first :: formulaRest) +
      frameOneTerminalSteps (first :: formulaRest))
    _ _ _ hBoot hFrameOne
  have hComplete := workRunExact?_compose cnfWorkMachine
    (2 + (frameOneFoldSteps [] [] (first :: formulaRest) +
      frameOneTerminalSteps (first :: formulaRest)))
    (certificateTokens.length + 1) _ _ _ hBootFrameOne hReject
  let steps :=
    (2 + (frameOneFoldSteps [] [] (first :: formulaRest) +
      frameOneTerminalSteps (first :: formulaRest))) +
      (certificateTokens.length + 1)
  let dummyAssignment : BitString :=
    List.replicate certificateTokens.length false
  have dummyLength : dummyAssignment.length = certificateTokens.length := by
    unfold dummyAssignment
    exact BitString.length_replicate_constructive
      certificateTokens.length false
  have malformedCounterToTerminal : certificateTokens.length + 1 ≤
      frameTwoTerminalSteps dummyAssignment := by
    have bound := frameTwoMalformedCounterSteps_le_terminal dummyAssignment
    rw [dummyLength] at bound
    exact bound
  have malformedCounterToFrameTwo : certificateTokens.length + 1 ≤
      frameTwoFoldSteps [] [] dummyAssignment +
        frameTwoTerminalSteps dummyAssignment :=
    Nat.le_trans malformedCounterToTerminal
      (Nat.le_add_left (frameTwoTerminalSteps dummyAssignment)
        (frameTwoFoldSteps [] [] dummyAssignment))
  have costToSuccess : steps ≤
      frameSuccessSteps (first :: formulaRest) dummyAssignment := by
    unfold steps frameSuccessSteps
    exact Nat.add_le_add_left malformedCounterToFrameTwo
      (2 + (frameOneFoldSteps [] [] (first :: formulaRest) +
        frameOneTerminalSteps (first :: formulaRest)))
  have formulaTokenToInput : (first :: formulaRest).length ≤
      BitString.size input := by
    rw [← inputShape]
    exact tokenLength_le_encodedPairsBitSize (first :: formulaRest) false
  have certificateTokenToCertificate : certificateTokens.length ≤
      BitString.size certificate := by
    rw [certificateShape]
    exact tokenLength_le_encodedPairsBitSize certificateTokens last
  have dummyToCertificate : dummyAssignment.length ≤
      BitString.size certificate := by
    rw [dummyLength]
    exact certificateTokenToCertificate
  have combinedToComponents :
      (first :: formulaRest).length + dummyAssignment.length ≤
        BitString.size input + BitString.size certificate :=
    Nat.add_le_add formulaTokenToInput dummyToCertificate
  have combinedBound :
      (first :: formulaRest).length + dummyAssignment.length ≤
        BitString.size (BitString.pair input certificate) :=
    Nat.le_trans combinedToComponents
      (componentSizes_le_pairSize input certificate)
  have inputPos : 1 ≤ BitString.size input := by
    rw [← inputShape]
    exact one_le_encodedPairsBitSize (first :: formulaRest) false
  have fiveSpan := five_le_shiftedPairSpan_of_inputPos input certificate
    inputPos
  have successBound := frameSuccessSteps_le_singlePhase
    (BitString.size (BitString.pair input certificate))
    (first :: formulaRest) dummyAssignment combinedBound fiveSpan
  have phaseBound : steps ≤ cnfSinglePhaseBudget
      (BitString.size (BitString.pair input certificate)) :=
    Nat.le_trans costToSuccess successBound
  refine ⟨steps,
    (workConfigAtWord CNFWorkState.reject finalLeft
      (leadingZeroWorkSymbol bit :: suffix)).tape,
    phaseBound, ?_⟩
  rw [← inputShape]
  rw [certificateShape]
  rw [tapeShape]
  unfold steps
  exact hComplete

theorem pairedWorkTape_token_terminal_shape
    (input certificate : BitString) (first : CNFToken)
    (formulaRest assignmentPrefix : List CNFToken) (terminal : CNFToken)
    (formulaTokensDecoded :
      decodeFormulaTokenPairs input = some (first :: formulaRest))
    (certificateShape : certificate =
      encodeTokenPairs assignmentPrefix ++ terminal.bits) :
    pairedWorkTape input certificate =
      WorkTape.ofSymbols
        (pairedTokenLayoutTerminal (first :: formulaRest)
          assignmentPrefix terminal) := by
  have formulaShape := encodeFormulaTokenPairs_of_decode input
    (first :: formulaRest) formulaTokensDecoded
  rw [← formulaShape, certificateShape]
  unfold pairedWorkTape
  change WorkTape.ofSymbols
      (packWorkSymbols
        ((BitString.pair
          (paddedFormulaTokenBits (first :: formulaRest))
          (encodeTokenPairs assignmentPrefix ++ terminal.bits)).map
            TapeSymbol.ofBool)) = _
  rw [packWorkSymbols_pairedTokenLayoutTerminal]

theorem tokenDecoded_assignment_terminal_full_exact
    (input certificate : BitString) (first : CNFToken)
    (formulaRest : List CNFToken) (assignment : BitString)
    (bad : CNFToken)
    (formulaTokensDecoded :
      decodeFormulaTokenPairs input = some (first :: formulaRest))
    (certificateShape : certificate =
      encodeTokenPairs (assignmentValueTokens assignment) ++ bad.bits)
    (badCase : bad = .f ∨ bad = .t ∨ bad = .sep) :
    ∃ tape,
      workRunExact? cnfWorkMachine
          (assignmentTerminalRejectSteps
            (first :: formulaRest) assignment)
          (workStartConfiguration cnfWorkMachine
            (pairedWorkTape input certificate)) =
        some
          ({ state := CNFWorkState.reject, tape := tape } :
            WorkConfiguration) := by
  have tapeShape := pairedWorkTape_token_terminal_shape input certificate
    first formulaRest (assignmentValueTokens assignment) bad
    formulaTokensDecoded certificateShape
  let assignmentSuffix :=
    List.replicate assignment.length cnfT ++
      cnfFinish :: (assignmentWorkSymbols assignment ++ [bad.workSymbol])
  have bootRun := boot_t_exact
    (List.replicate formulaRest.length cnfT ++
      cnfFinish ::
        (first.workSymbol ::
          (cnfTokenWorkSymbols formulaRest ++ cnfSep :: assignmentSuffix)))
  have frameOneRun := frameOne_complete_exact (first :: formulaRest)
    assignmentSuffix
  rw [frameOneFoldStart_empty_cons] at frameOneRun
  let leftBase := frameFormulaLeftBase (first :: formulaRest)
  have invalid : ¬ FrameTwoCheckSymbol bad.workSymbol := by
    intro allowed
    cases badCase with
    | inl equal => cases equal; cases allowed
    | inr remaining =>
        cases remaining with
        | inl equal => cases equal; cases allowed
        | inr equal => cases equal; cases allowed
  rcases frameTwo_terminal_bad_exact assignment leftBase bad.workSymbol
      invalid with ⟨tape, badRun⟩
  unfold frameTwoPrefixStart at badRun
  repeat' rw [FrameTraceDesign.frameWork_append_assoc] at badRun
  have throughFrame := workRunExact?_compose cnfWorkMachine 2
    (frameOneFoldSteps [] [] (first :: formulaRest) +
      frameOneTerminalSteps (first :: formulaRest))
    _ _ _ bootRun frameOneRun
  have complete := workRunExact?_compose cnfWorkMachine
    (2 + (frameOneFoldSteps [] [] (first :: formulaRest) +
      frameOneTerminalSteps (first :: formulaRest)))
    (frameTwoTerminalBadSteps assignment)
    _ _ _ throughFrame badRun
  refine ⟨tape, ?_⟩
  rw [tapeShape]
  unfold pairedTokenLayoutTerminal
  rw [assignmentValueTokens_length]
  rw [assignmentValueTokens_workSymbols]
  unfold assignmentTerminalRejectSteps
  exact complete

theorem formulaFrameReplicate_add {alpha : Type}
    (first second : Nat) (item : alpha) :
    List.replicate (first + second) item =
      List.replicate first item ++ List.replicate second item := by
  induction first with
  | zero =>
      rw [Nat.zero_add]
      rfl
  | succ first ih =>
      rw [Nat.succ_add]
      change item :: List.replicate (first + second) item =
        item ::
          (List.replicate first item ++ List.replicate second item)
      exact congrArg (List.cons item) ih

theorem formulaFrameReplicate_cons_length {alpha beta : Type}
    (head : alpha) (tail : List alpha) (item : beta) :
    List.replicate (head :: tail).length item =
      item :: List.replicate tail.length item := rfl

theorem formulaFrameTokenWorkSymbols_cons
    (head : CNFToken) (tail : List CNFToken) :
    cnfTokenWorkSymbols (head :: tail) =
      head.workSymbol :: cnfTokenWorkSymbols tail := rfl

theorem formulaFrameList_length_append {alpha : Type}
    (left right : List alpha) :
    (left ++ right).length = left.length + right.length := by
  induction left with
  | nil => exact (Nat.zero_add right.length).symm
  | cons item rest ih =>
      change Nat.succ (rest ++ right).length =
        Nat.succ rest.length + right.length
      rw [Nat.succ_add]
      exact congrArg Nat.succ ih

theorem formulaFrameList_append_assoc {alpha : Type}
    (left middle right : List alpha) :
    (left ++ middle) ++ right = left ++ (middle ++ right) := by
  induction left with
  | nil => rfl
  | cons item rest ih => exact congrArg (List.cons item) ih

theorem formulaFrameEncodeTokenPairs_singleton (token : CNFToken) :
    encodeTokenPairs [token] = token.bits := by
  cases token <;> rfl

theorem tokenDecoded_assignment_interior_full_exact
    (input certificate : BitString) (first : CNFToken)
    (formulaRest : List CNFToken) (assignment : BitString)
    (bad : CNFToken) (suffixPrefix : List CNFToken)
    (terminal : CNFToken)
    (formulaTokensDecoded :
      decodeFormulaTokenPairs input = some (first :: formulaRest))
    (certificateShape : certificate =
      encodeTokenPairs
          (assignmentValueTokens assignment ++ bad :: suffixPrefix) ++
        terminal.bits)
    (badCase : bad = .sep ∨ bad = .finish) :
    ∃ tape,
      workRunExact? cnfWorkMachine
          (assignmentInteriorRejectSteps
            (first :: formulaRest) assignment suffixPrefix.length)
          (workStartConfiguration cnfWorkMachine
            (pairedWorkTape input certificate)) =
        some
          ({ state := CNFWorkState.reject, tape := tape } :
            WorkConfiguration) := by
  let assignmentPrefix :=
    assignmentValueTokens assignment ++ bad :: suffixPrefix
  have tapeShape := pairedWorkTape_token_terminal_shape input certificate
    first formulaRest assignmentPrefix terminal formulaTokensDecoded
    certificateShape
  let restCounter :=
    List.replicate (Nat.succ suffixPrefix.length) cnfT
  let payloadTail := bad.workSymbol ::
    (cnfTokenWorkSymbols suffixPrefix ++ [terminal.workSymbol])
  let assignmentSuffix :=
    (List.replicate assignment.length cnfT ++ restCounter) ++
      cnfFinish :: (assignmentWorkSymbols assignment ++ payloadTail)
  have bootRun := boot_t_exact
    (List.replicate formulaRest.length cnfT ++
      cnfFinish ::
        (first.workSymbol ::
          (cnfTokenWorkSymbols formulaRest ++ cnfSep :: assignmentSuffix)))
  have frameOneRun := frameOne_complete_exact (first :: formulaRest)
    assignmentSuffix
  rw [frameOneFoldStart_empty_cons] at frameOneRun
  let leftBase := frameFormulaLeftBase (first :: formulaRest)
  have badWorkCase : bad.workSymbol = cnfSep ∨
      bad.workSymbol = cnfFinish := by
    cases badCase with
    | inl equal => cases equal; exact Or.inl rfl
    | inr equal => cases equal; exact Or.inr rfl
  rcases frameTwo_interior_bad_exact assignment suffixPrefix terminal
      leftBase bad.workSymbol badWorkCase with ⟨tape, badRun⟩
  unfold frameTwoPrefixStart at badRun
  repeat' rw [FrameTraceDesign.frameWork_append_assoc] at badRun
  have throughFrame := workRunExact?_compose cnfWorkMachine 2
    (frameOneFoldSteps [] [] (first :: formulaRest) +
      frameOneTerminalSteps (first :: formulaRest))
    _ _ _ bootRun frameOneRun
  unfold leftBase frameFormulaLeftBase at badRun
  unfold assignmentSuffix restCounter payloadTail at throughFrame
  repeat' rw [FrameTraceDesign.frameWork_append_assoc] at badRun throughFrame
  have badStartShape :
      ([] ++
        (List.replicate assignment.length cnfT ++
          (List.replicate (Nat.succ suffixPrefix.length) cnfT ++
            cnfFinish ::
              ([] ++
                (assignmentWorkSymbols assignment ++
                  bad.workSymbol ::
                    (cnfTokenWorkSymbols suffixPrefix ++
                      [terminal.workSymbol])))))) =
        (List.replicate assignment.length cnfT ++
          List.replicate (Nat.succ suffixPrefix.length) cnfT) ++
            cnfFinish ::
              (assignmentWorkSymbols assignment ++
                bad.workSymbol ::
                  (cnfTokenWorkSymbols suffixPrefix ++
                    [terminal.workSymbol])) := by
    exact (FrameTraceDesign.frameWork_append_assoc
      (List.replicate assignment.length cnfT)
      (List.replicate (Nat.succ suffixPrefix.length) cnfT)
      (cnfFinish ::
        (assignmentWorkSymbols assignment ++
          bad.workSymbol ::
            (cnfTokenWorkSymbols suffixPrefix ++
              [terminal.workSymbol])))).symm
  rw [badStartShape] at badRun
  have complete := workRunExact?_compose cnfWorkMachine
    (2 + (frameOneFoldSteps [] [] (first :: formulaRest) +
      frameOneTerminalSteps (first :: formulaRest)))
    (frameTwoInteriorBadSteps assignment suffixPrefix.length)
    _ _ _ throughFrame badRun
  refine ⟨tape, ?_⟩
  rw [tapeShape]
  unfold pairedTokenLayoutTerminal assignmentPrefix
  rw [token_length_append_constructive]
  rw [assignmentValueTokens_length]
  rw [formulaFrameReplicate_add]
  rw [cnfTokenWorkSymbols_append]
  rw [assignmentValueTokens_workSymbols]
  unfold assignmentInteriorRejectSteps
  rw [formulaFrameReplicate_cons_length first formulaRest cnfT]
  rw [formulaFrameTokenWorkSymbols_cons first formulaRest]
  rw [formulaFrameTokenWorkSymbols_cons bad suffixPrefix]
  repeat' rw [FrameTraceDesign.frameWork_append_assoc]
  repeat' rw [assignmentTape_cons_append]
  repeat' rw [FrameTraceDesign.frameWork_append_assoc]
  have badLength : (bad :: suffixPrefix).length =
      Nat.succ suffixPrefix.length := rfl
  rw [badLength]
  rw [FrameTraceDesign.frameWork_append_assoc
    (List.replicate assignment.length cnfT)
    (List.replicate (Nat.succ suffixPrefix.length) cnfT)
    (cnfFinish ::
      (assignmentWorkSymbols assignment ++
        bad.workSymbol ::
          (cnfTokenWorkSymbols suffixPrefix ++ [terminal.workSymbol])))]
    at complete
  exact complete

theorem pairedWorkTape_token_empty_certificate_shape
    (input : BitString) (first : CNFToken) (formulaRest : List CNFToken)
    (formulaTokensDecoded :
      decodeFormulaTokenPairs input = some (first :: formulaRest)) :
    pairedWorkTape input [] =
      WorkTape.ofSymbols
        (pairedEmptyCertificateLayout (first :: formulaRest)) := by
  have formulaShape := encodeFormulaTokenPairs_of_decode input
    (first :: formulaRest) formulaTokensDecoded
  rw [← formulaShape]
  unfold pairedWorkTape
  change WorkTape.ofSymbols
      (packWorkSymbols
        ((BitString.pair
          (paddedFormulaTokenBits (first :: formulaRest)) []).map
            TapeSymbol.ofBool)) = _
  rw [packWorkSymbols_pairedEmptyCertificateLayout]

theorem tokenDecoded_assignment_empty_full_exact
    (input : BitString) (first : CNFToken) (formulaRest : List CNFToken)
    (formulaTokensDecoded :
      decodeFormulaTokenPairs input = some (first :: formulaRest)) :
    ∃ steps tape,
      steps ≤ frameSuccessSteps (first :: formulaRest) [] ∧
      workRunExact? cnfWorkMachine steps
          (workStartConfiguration cnfWorkMachine
            (pairedWorkTape input [])) =
        some
          ({ state := CNFWorkState.reject, tape := tape } :
            WorkConfiguration) := by
  have tapeShape := pairedWorkTape_token_empty_certificate_shape input
    first formulaRest formulaTokensDecoded
  let tokens := first :: formulaRest
  have bootRun := boot_t_exact
    (List.replicate formulaRest.length cnfT ++
      cnfFinish ::
        (first.workSymbol ::
          (cnfTokenWorkSymbols formulaRest ++ [cnfF])))
  have rejectRun := frameOne_fBoundary_exact tokens []
  rw [frameOneBoundaryFoldStart_cons] at rejectRun
  have complete := workRunExact?_compose cnfWorkMachine 2
    (frameOneFoldSteps [] [] tokens + frameOneBadBoundarySteps tokens)
    _ _ _ bootRun rejectRun
  let steps := 2 +
    (frameOneFoldSteps [] [] tokens + frameOneBadBoundarySteps tokens)
  have terminalBound := frameOneBadBoundarySteps_le_terminal tokens
  have firstBound : steps ≤
      2 + (frameOneFoldSteps [] [] tokens +
        frameOneTerminalSteps tokens) :=
    Nat.add_le_add_left
      (Nat.add_le_add_left terminalBound
        (frameOneFoldSteps [] [] tokens)) 2
  have secondBound :
      2 + (frameOneFoldSteps [] [] tokens + frameOneTerminalSteps tokens) ≤
        frameSuccessSteps tokens [] := by
    unfold frameSuccessSteps
    exact Nat.le_add_right _
      (frameTwoFoldSteps [] [] [] + frameTwoTerminalSteps [])
  refine ⟨steps,
    (workConfigAtWord CNFWorkState.reject
      (pushWorkLeft (frameOneMarkedTokens tokens)
        (cnfFinish ::
          pushWorkLeft (List.replicate tokens.length cnfMarkFalse)
            [cnfRootGuard])) [cnfF]).tape,
    Nat.le_trans firstBound secondBound, ?_⟩
  rw [tapeShape]
  unfold pairedEmptyCertificateLayout tokens steps
  exact complete

theorem frameSuccessSteps_withinPair_of_tokenDecoded_components
    (input certificate : BitString) (first : CNFToken)
    (formulaRest tokens : List CNFToken) (dummyAssignment : BitString)
    (formulaTokensDecoded :
      decodeFormulaTokenPairs input = some (first :: formulaRest))
    (tokensDecoded : decodeTokenPairs certificate = some tokens)
    (dummyToTokens : dummyAssignment.length ≤ tokens.length) :
    frameSuccessSteps (first :: formulaRest) dummyAssignment ≤
      cnfSinglePhaseBudget
        (BitString.size (BitString.pair input certificate)) := by
  have inputShape := encodeFormulaTokenPairs_of_decode input
    (first :: formulaRest) formulaTokensDecoded
  have certificateShape := encodeTokenPairs_of_decode certificate tokens
    tokensDecoded
  have formulaTokenToInput : (first :: formulaRest).length ≤
      BitString.size input := by
    rw [← inputShape]
    exact tokenLength_le_encodedPairsBitSize (first :: formulaRest) false
  have certificateTokenToCertificate : tokens.length ≤
      BitString.size certificate := by
    rw [← certificateShape]
    exact tokenLength_le_encodedPairsSize tokens
  have dummyToCertificate : dummyAssignment.length ≤
      BitString.size certificate :=
    Nat.le_trans dummyToTokens certificateTokenToCertificate
  have combinedToComponents :
      (first :: formulaRest).length + dummyAssignment.length ≤
        BitString.size input + BitString.size certificate :=
    Nat.add_le_add formulaTokenToInput dummyToCertificate
  have combinedBound :
      (first :: formulaRest).length + dummyAssignment.length ≤
        BitString.size (BitString.pair input certificate) :=
    Nat.le_trans combinedToComponents
      (componentSizes_le_pairSize input certificate)
  have inputPos : 1 ≤ BitString.size input := by
    rw [← inputShape]
    exact one_le_encodedPairsBitSize (first :: formulaRest) false
  have fiveSpan := five_le_shiftedPairSpan_of_inputPos input certificate
    inputPos
  exact frameSuccessSteps_le_singlePhase
    (BitString.size (BitString.pair input certificate))
    (first :: formulaRest) dummyAssignment combinedBound fiveSpan

theorem tokenDecoded_assignmentGrammarFailure_rejects_withinPairSinglePhase
    (input certificate : BitString) (first : CNFToken)
    (formulaRest assignmentTokens : List CNFToken)
    (formulaTokensDecoded :
      decodeFormulaTokenPairs input = some (first :: formulaRest))
    (tokensDecoded :
      decodeTokenPairs certificate = some assignmentTokens)
    (grammarFailed : decodeAssignmentTokens assignmentTokens = none) :
    ∃ steps tape,
      steps ≤ cnfSinglePhaseBudget
        (BitString.size (BitString.pair input certificate)) ∧
      workRunExact? cnfWorkMachine steps
          (workStartConfiguration cnfWorkMachine
            (pairedWorkTape input certificate)) =
        some
          ({ state := CNFWorkState.reject, tape := tape } :
            WorkConfiguration) := by
  have bitsShape := encodeTokenPairs_of_decode certificate assignmentTokens
    tokensDecoded
  have failure := assignmentGrammarFailure_of_decode_none assignmentTokens
    grammarFailed
  have normal := assignmentGrammarFailure_normal failure
  cases normal with
  | empty =>
      have certificateEmpty : certificate = [] := bitsShape.symm
      have emptyTokensDecoded : decodeTokenPairs [] =
          some ([] : List CNFToken) := by
        rw [← certificateEmpty]
        exact tokensDecoded
      rw [certificateEmpty]
      rcases tokenDecoded_assignment_empty_full_exact input first
          formulaRest formulaTokensDecoded with
        ⟨steps, tape, successCost, exactRun⟩
      have successBound :=
        frameSuccessSteps_withinPair_of_tokenDecoded_components
          input [] first formulaRest [] [] formulaTokensDecoded
          emptyTokensDecoded (Nat.zero_le _)
      exact ⟨steps, tape, Nat.le_trans successCost successBound, exactRun⟩
  | terminalF values =>
      have certificateShape : certificate =
          encodeTokenPairs (assignmentValueTokens values) ++
            CNFToken.f.bits := by
        rw [encodeTokenPairs_append] at bitsShape
        exact bitsShape.symm
      rcases tokenDecoded_assignment_terminal_full_exact input certificate
          first formulaRest values .f formulaTokensDecoded certificateShape
          (Or.inl rfl) with ⟨tape, exactRun⟩
      have dummyToTokens : values.length ≤
          (assignmentValueTokens values ++ [CNFToken.f]).length := by
        rw [formulaFrameList_length_append]
        rw [assignmentValueTokens_length]
        exact Nat.le_add_right values.length 1
      have successBound :=
        frameSuccessSteps_withinPair_of_tokenDecoded_components
          input certificate first formulaRest
          (assignmentValueTokens values ++ [CNFToken.f]) values
          formulaTokensDecoded tokensDecoded dummyToTokens
      exact ⟨assignmentTerminalRejectSteps
          (first :: formulaRest) values, tape,
        Nat.le_trans
          (assignmentTerminalRejectSteps_le_success
            (first :: formulaRest) values) successBound,
        exactRun⟩
  | terminalT values =>
      have certificateShape : certificate =
          encodeTokenPairs (assignmentValueTokens values) ++
            CNFToken.t.bits := by
        rw [encodeTokenPairs_append] at bitsShape
        exact bitsShape.symm
      rcases tokenDecoded_assignment_terminal_full_exact input certificate
          first formulaRest values .t formulaTokensDecoded certificateShape
          (Or.inr (Or.inl rfl)) with ⟨tape, exactRun⟩
      have dummyToTokens : values.length ≤
          (assignmentValueTokens values ++ [CNFToken.t]).length := by
        rw [formulaFrameList_length_append]
        rw [assignmentValueTokens_length]
        exact Nat.le_add_right values.length 1
      have successBound :=
        frameSuccessSteps_withinPair_of_tokenDecoded_components
          input certificate first formulaRest
          (assignmentValueTokens values ++ [CNFToken.t]) values
          formulaTokensDecoded tokensDecoded dummyToTokens
      exact ⟨assignmentTerminalRejectSteps
          (first :: formulaRest) values, tape,
        Nat.le_trans
          (assignmentTerminalRejectSteps_le_success
            (first :: formulaRest) values) successBound,
        exactRun⟩
  | terminalSep values =>
      have certificateShape : certificate =
          encodeTokenPairs (assignmentValueTokens values) ++
            CNFToken.sep.bits := by
        rw [encodeTokenPairs_append] at bitsShape
        exact bitsShape.symm
      rcases tokenDecoded_assignment_terminal_full_exact input certificate
          first formulaRest values .sep formulaTokensDecoded certificateShape
          (Or.inr (Or.inr rfl)) with ⟨tape, exactRun⟩
      have dummyToTokens : values.length ≤
          (assignmentValueTokens values ++ [CNFToken.sep]).length := by
        rw [formulaFrameList_length_append]
        rw [assignmentValueTokens_length]
        exact Nat.le_add_right values.length 1
      have successBound :=
        frameSuccessSteps_withinPair_of_tokenDecoded_components
          input certificate first formulaRest
          (assignmentValueTokens values ++ [CNFToken.sep]) values
          formulaTokensDecoded tokensDecoded dummyToTokens
      exact ⟨assignmentTerminalRejectSteps
          (first :: formulaRest) values, tape,
        Nat.le_trans
          (assignmentTerminalRejectSteps_le_success
            (first :: formulaRest) values) successBound,
        exactRun⟩
  | interiorSep values next rest =>
      rcases tokenList_snoc next rest with
        ⟨suffixPrefix, terminal, tailShape⟩
      have tokenShape :
          assignmentValueTokens values ++ .sep :: next :: rest =
            (assignmentValueTokens values ++ .sep :: suffixPrefix) ++
              [terminal] := by
        rw [tailShape]
        exact (formulaFrameList_append_assoc
          (assignmentValueTokens values) (.sep :: suffixPrefix)
          [terminal]).symm
      have encodedShape := bitsShape
      rw [tokenShape, encodeTokenPairs_append] at encodedShape
      rw [formulaFrameEncodeTokenPairs_singleton] at encodedShape
      have certificateShape : certificate =
          encodeTokenPairs
              (assignmentValueTokens values ++ .sep :: suffixPrefix) ++
            terminal.bits := encodedShape.symm
      rcases tokenDecoded_assignment_interior_full_exact input certificate
          first formulaRest values .sep suffixPrefix terminal
          formulaTokensDecoded certificateShape (Or.inl rfl) with
        ⟨tape, exactRun⟩
      have dummyToTokens :
          (assignmentInteriorDummy values suffixPrefix.length).length ≤
            (assignmentValueTokens values ++ .sep :: next :: rest).length := by
        rw [tokenShape]
        rw [assignmentInteriorDummy_length]
        rw [formulaFrameList_length_append, formulaFrameList_length_append]
        rw [assignmentValueTokens_length]
        exact Nat.le_add_right
          (values.length + Nat.succ suffixPrefix.length) 1
      have successBound :=
        frameSuccessSteps_withinPair_of_tokenDecoded_components
          input certificate first formulaRest
          (assignmentValueTokens values ++ .sep :: next :: rest)
          (assignmentInteriorDummy values suffixPrefix.length)
          formulaTokensDecoded tokensDecoded dummyToTokens
      exact ⟨assignmentInteriorRejectSteps
          (first :: formulaRest) values suffixPrefix.length, tape,
        Nat.le_trans
          (assignmentInteriorRejectSteps_le_success
            (first :: formulaRest) values suffixPrefix.length)
          successBound,
        exactRun⟩
  | interiorFinish values next rest =>
      rcases tokenList_snoc next rest with
        ⟨suffixPrefix, terminal, tailShape⟩
      have tokenShape :
          assignmentValueTokens values ++ .finish :: next :: rest =
            (assignmentValueTokens values ++ .finish :: suffixPrefix) ++
              [terminal] := by
        rw [tailShape]
        exact (formulaFrameList_append_assoc
          (assignmentValueTokens values) (.finish :: suffixPrefix)
          [terminal]).symm
      have encodedShape := bitsShape
      rw [tokenShape, encodeTokenPairs_append] at encodedShape
      rw [formulaFrameEncodeTokenPairs_singleton] at encodedShape
      have certificateShape : certificate =
          encodeTokenPairs
              (assignmentValueTokens values ++ .finish :: suffixPrefix) ++
            terminal.bits := encodedShape.symm
      rcases tokenDecoded_assignment_interior_full_exact input certificate
          first formulaRest values .finish suffixPrefix terminal
          formulaTokensDecoded certificateShape (Or.inr rfl) with
        ⟨tape, exactRun⟩
      have dummyToTokens :
          (assignmentInteriorDummy values suffixPrefix.length).length ≤
            (assignmentValueTokens values ++ .finish :: next :: rest).length := by
        rw [tokenShape]
        rw [assignmentInteriorDummy_length]
        rw [formulaFrameList_length_append, formulaFrameList_length_append]
        rw [assignmentValueTokens_length]
        exact Nat.le_add_right
          (values.length + Nat.succ suffixPrefix.length) 1
      have successBound :=
        frameSuccessSteps_withinPair_of_tokenDecoded_components
          input certificate first formulaRest
          (assignmentValueTokens values ++ .finish :: next :: rest)
          (assignmentInteriorDummy values suffixPrefix.length)
          formulaTokensDecoded tokensDecoded dummyToTokens
      exact ⟨assignmentInteriorRejectSteps
          (first :: formulaRest) values suffixPrefix.length, tape,
        Nat.le_trans
          (assignmentInteriorRejectSteps_le_success
            (first :: formulaRest) values suffixPrefix.length)
          successBound,
        exactRun⟩

theorem tokenDecoded_assignment_none_rejects_withinPairSinglePhase
    (input certificate : BitString) (first : CNFToken)
    (formulaRest : List CNFToken)
    (formulaTokensDecoded :
      decodeFormulaTokenPairs input = some (first :: formulaRest))
    (assignmentDecoded :
      decodeAssignmentCertificate certificate = none) :
    CNFSinglePhaseReject input certificate := by
  unfold CNFSinglePhaseReject
  cases tokensCase : decodeTokenPairs certificate with
  | none =>
      exact tokenDecoded_assignmentRaw_none_rejects_withinPairSinglePhase
        input certificate first formulaRest formulaTokensDecoded tokensCase
  | some assignmentTokens =>
      have grammarFailed : decodeAssignmentTokens assignmentTokens = none := by
        unfold decodeAssignmentCertificate at assignmentDecoded
        rw [tokensCase] at assignmentDecoded
        exact assignmentDecoded
      exact
        tokenDecoded_assignmentGrammarFailure_rejects_withinPairSinglePhase
          input certificate first formulaRest assignmentTokens
          formulaTokensDecoded tokensCase grammarFailed

theorem one_le_cnfSinglePhaseBudget (n : Nat) :
    1 ≤ cnfSinglePhaseBudget n := by
  have oneSpan : 1 ≤ cnfShiftedWorkSpan n := by
    unfold cnfShiftedWorkSpan
    change Nat.succ 0 ≤ Nat.succ (Nat.succ n)
    exact Nat.succ_le_succ (Nat.zero_le (Nat.succ n))
  have coefficient : 1 ≤ 16 := by
    change 1 ≤ 1 + 15
    exact Nat.le_add_right 1 15
  have scaled := cnfScaledLinear_le_singlePhaseBudget n 1 coefficient
  rw [Nat.mul_one] at scaled
  exact Nat.le_trans oneSpan scaled

theorem emptyFormulaTokens_rejects_withinPairSinglePhase
    (input certificate : BitString)
    (formulaTokensDecoded :
      decodeFormulaTokenPairs input = some ([] : List CNFToken)) :
    CNFSinglePhaseReject input certificate := by
  unfold CNFSinglePhaseReject
  have inputShape := encodeFormulaTokenPairs_of_decode input []
    formulaTokensDecoded
  let tape := pairedWorkTape input certificate
  refine ⟨1, tape,
    one_le_cnfSinglePhaseBudget
      (BitString.size (BitString.pair input certificate)), ?_⟩
  unfold tape
  rw [← inputShape]
  rfl

theorem formulaFrameFailureContract_available :
    FormulaFrameFailureContract := by
  intro input certificate tokens formulaTokensDecoded failure
  cases tokens with
  | nil =>
      exact emptyFormulaTokens_rejects_withinPairSinglePhase
        input certificate formulaTokensDecoded
  | cons first rest =>
      cases failure with
      | inl impossible => contradiction
      | inr assignmentDecoded =>
          exact tokenDecoded_assignment_none_rejects_withinPairSinglePhase
            input certificate first rest formulaTokensDecoded
            assignmentDecoded

end FormulaFrameFailureDesign
end PNP.Concrete



namespace PNP.Concrete
namespace FormulaPostFrameDesign

open FrameTraceDesign
open ClauseLiteralDesign
open MalformedFuelDesign
open WidthSuccessDesign
open GrammarFailureDesign
open GrammarHeaderDesign
open GrammarHeaderBoundDesign
open GrammarTerminalBoundDesign
open UniversalCompositionDesign
open FormulaOutcomeBridgeDesign

set_option maxRecDepth 100000

theorem formulaPostFrameRejectContract_available :
    FormulaPostFrameRejectContract := by
  intro input certificate first rest assignment formulaTokensDecoded
    assignmentDecoded grammarFailed
  let tokens := first :: rest
  let n := BitString.size (BitString.pair input certificate)
  let outerCounter := List.replicate tokens.length cnfMarkFalse
  let counter := List.replicate assignment.length cnfMarkFalse
  have payloadBound := token_decoded_frame_payload_le_pair_size
    input certificate tokens assignment formulaTokensDecoded
    assignmentDecoded
  have tokenBound : tokens.length ≤ n := by
    unfold n
    exact Nat.le_trans
      (Nat.le_add_right tokens.length assignment.length) payloadBound
  have assignmentBound : assignment.length ≤ n := by
    unfold n
    exact Nat.le_trans
      (Nat.le_add_left assignment.length tokens.length) payloadBound
  have outerBound : outerCounter.length ≤ n := by
    unfold outerCounter
    rw [length_replicate_workSymbol]
    exact tokenBound
  have counterBound : counter.length ≤ n := by
    unfold counter
    rw [length_replicate_workSymbol]
    exact assignmentBound
  have outerAllowed : ∀ symbol, List.Mem symbol outerCounter →
      symbol = cnfMarkFalse := by
    intro symbol member
    unfold outerCounter at member
    exact mem_replicate_workSymbol_eq tokens.length cnfMarkFalse symbol
      member
  have counterAllowed : ∀ symbol, List.Mem symbol counter →
      symbol = cnfMarkFalse := by
    intro symbol member
    unfold counter at member
    exact mem_replicate_workSymbol_eq assignment.length cnfMarkFalse symbol
      member
  have formulaAllowed : ∀ symbol,
      List.Mem symbol (cnfTokenWorkSymbols tokens) →
        FormulaScanSymbol symbol := by
    intro symbol member
    exact cnfTokenWorkSymbols_formulaScan tokens symbol member
  have formulaWordBound : (cnfTokenWorkSymbols tokens).length ≤ n := by
    rw [cnfTokenWorkSymbols_length]
    exact tokenBound
  have assignmentPartition : assignment.length ≤ counter.length := by
    unfold counter
    rw [length_replicate_workSymbol]
    exact Nat.le_refl assignment.length
  have failure := decodeCNFTokens_none_to_failure tokens grammarFailed
  have preludeRun := widthSeekPrelude_exact outerCounter
    (cnfTokenWorkSymbols tokens) counter
    (cnfFinish ::
      (assignmentWorkSymbols assignment ++ [cnfRootGuard, cnfBlank]))
    outerAllowed formulaAllowed counterAllowed
  have formulaPartition :
      formulaHeaderControlPrefix (FormulaHeaderControl.header 0) +
          tokens.length ≤ outerCounter.length := by
    rw [formulaHeaderControlPrefix_header, Nat.zero_add]
    unfold outerCounter
    rw [length_replicate_workSymbol]
    exact Nat.le_refl tokens.length
  rcases formulaHeaderFailure_segmented_atWidth outerCounter counter
      assignment [cnfBlank] n outerAllowed counterAllowed outerBound
      counterBound assignmentBound assignmentPartition failure
      (FormulaHeaderControl.header 0) formulaPartition with
    ⟨headerSteps, middle, grammarSteps, tape, headerBound,
      grammarBound, headerRun, grammarRun⟩
  have preludeStart :
      workRunExact? cnfWorkMachine
          (widthSeekPreludeSteps outerCounter
            (cnfTokenWorkSymbols tokens) counter)
          (tokenDecodedFrameFinal tokens assignment) =
        some
          (formulaHeaderControlStart (FormulaHeaderControl.header 0)
            outerCounter counter assignment tokens [cnfBlank]) := by
    unfold tokenDecodedFrameFinal frameFormulaLeftBase
    unfold formulaHeaderControlStart formulaHeaderFailureStart
      widthMalformedTailStart
    unfold tokens outerCounter counter at preludeRun ⊢
    exact preludeRun
  have totalRun := workRunExact?_compose cnfWorkMachine
    (widthSeekPreludeSteps outerCounter
      (cnfTokenWorkSymbols tokens) counter)
    headerSteps _ _ _ preludeStart headerRun
  have preludeFour := widthSeekPreludeSteps_le_fourSpan n outerCounter
    (cnfTokenWorkSymbols tokens) counter outerBound formulaWordBound
    counterBound
  have fourTwelve : 4 ≤ 12 := by
    change 4 ≤ 4 + 8
    exact Nat.le_add_right 4 8
  have preludeTwelve := widthCost_promote_scaled
    (cnfShiftedWorkSpan n)
    (widthSeekPreludeSteps outerCounter
      (cnfTokenWorkSymbols tokens) counter)
    4 12 preludeFour fourTwelve
  rw [formulaHeaderControlUnits_header, Nat.zero_add] at headerBound
  have accumulated := Nat.add_le_add preludeTwelve headerBound
  have accumulatedBound :
      widthSeekPreludeSteps outerCounter
          (cnfTokenWorkSymbols tokens) counter + headerSteps ≤
        (tokens.length + 2) * (cnfShiftedWorkSpan n * 12) := by
    exact Nat.le_trans accumulated
      (Nat.le_of_eq
        (charge_plus_successor_mul tokens.length
          (cnfShiftedWorkSpan n * 12)))
  have unitsBound : tokens.length + 2 ≤ cnfShiftedWorkSpan n := by
    unfold cnfShiftedWorkSpan
    exact Nat.add_le_add_right tokenBound 2
  have totalBound := clauseLiteral_accumulated_le_singlePhaseBudget n
    (tokens.length + 2) (cnfShiftedWorkSpan n * 12)
    (widthSeekPreludeSteps outerCounter
      (cnfTokenWorkSymbols tokens) counter + headerSteps)
    unitsBound (Nat.le_refl (cnfShiftedWorkSpan n * 12))
    accumulatedBound
  exact ⟨widthSeekPreludeSteps outerCounter
      (cnfTokenWorkSymbols tokens) counter + headerSteps,
    middle, grammarSteps, tape, totalBound, grammarBound, totalRun,
    grammarRun⟩

end FormulaPostFrameDesign
end PNP.Concrete



namespace PNP.Concrete
namespace FinalUniversalDesign

open UniversalCompositionDesign
open UniversalHandoff
open FormulaOutcomeBridgeDesign
open FormulaFrameFailureDesign
open FormulaPostFrameDesign

/-- The now-closed formula-grammar outcome used by the universal decoder
split. -/
theorem formulaGrammarOutcome : FormulaGrammarOutcomeContract := by
  exact formulaGrammarOutcome_of_frame_postContracts
    formulaFrameFailureContract_available
    formulaPostFrameRejectContract_available

/-- The complete universal work theorem has no residual contract inputs. -/
theorem cnfUniversalWorkOutcome :
    ∀ input certificate, CNFWorkOutcome input certificate := by
  exact cnfUniversalWorkOutcome_of_formulaGrammar
    formulaGrammarOutcome

theorem cnfCompiled_accept_iff_check
    (input certificate : BitString) :
    boundedDecide cnfCompiledMachine
        (cnfCompiledStepPolynomial.eval
          (BitString.size (BitString.pair input certificate)))
        (BitString.pair input certificate) = .accept ↔
      checkEncodedCertificate input certificate = true := by
  exact cnfCompiled_accept_iff_check_of_formulaGrammar
    formulaGrammarOutcome input certificate

theorem cnfCompiled_reject_iff_check_false
    (input certificate : BitString) :
    boundedDecide cnfCompiledMachine
        (cnfCompiledStepPolynomial.eval
          (BitString.size (BitString.pair input certificate)))
        (BitString.pair input certificate) = .reject ↔
      checkEncodedCertificate input certificate = false := by
  exact cnfCompiled_reject_iff_check_false_of_formulaGrammar
    formulaGrammarOutcome input certificate

theorem cnfCompiled_ne_timeout
    (input certificate : BitString) :
    boundedDecide cnfCompiledMachine
        (cnfCompiledStepPolynomial.eval
          (BitString.size (BitString.pair input certificate)))
        (BitString.pair input certificate) ≠ .timeout := by
  exact cnfCompiled_ne_timeout_of_formulaGrammar
    formulaGrammarOutcome input certificate

def cnfConcreteVerifier : PolynomialTimeVerifier CNFSAT :=
  cnfConcreteVerifier_of_formulaGrammar formulaGrammarOutcome

theorem cnfConcreteVerifier_inputMode :
    cnfConcreteVerifier.program.inputMode =
      .paired := by
  exact cnfConcreteVerifier_of_formulaGrammar_inputMode
    formulaGrammarOutcome

theorem cnfConcreteVerifier_decision :
    cnfConcreteVerifier.program.decision =
      .machine cnfCompiledMachine cnfCompiledStepPolynomial := by
  exact cnfConcreteVerifier_of_formulaGrammar_decision
    formulaGrammarOutcome

theorem cnfSATInNP : InNP CNFSAT := by
  exact ⟨cnfConcreteVerifier⟩

end FinalUniversalDesign
end PNP.Concrete
