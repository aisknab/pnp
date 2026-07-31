/-
Copyright (c) 2026 PNP Labs.

Exact operational correctness of the standalone strict canonical-CNF parser.

The proof stays at the literal nine-symbol work-machine boundary.  Canonical
formulae are scanned and restored byte-for-byte.  Malformed formula framing
or grammar enters the machine's guarded cleanup path, which erases the source
word and reaches the rejecting halt.
-/

import PNP.Concrete.CNFSourceParserMachine
import PNP.Concrete.CNFSourceParserSpec
import PNP.Concrete.CNFWorkUniversalCorrectness
import PNP.Concrete.TapeBlankEquivalence
import PNP.Concrete.WorkMachineBlankEquivalence

namespace PNP.Concrete.CNFSourceParser

open PNP.Concrete
open PNP.Concrete.FrameTraceDesign
open PNP.Concrete.GrammarFailureDesign

set_option maxRecDepth 100000

/-! ### Raw canonical-input bridge -/

/-- Packing a complete token stream followed by the unique formula pad
produces exactly the corresponding token work symbols and one `zeroBlank`
pad symbol. -/
theorem packWorkSymbols_encodeTokenPairs_formulaPad
    (tokens : List CNFToken) :
    packWorkSymbols
        ((encodeTokenPairs tokens ++ [false]).map TapeSymbol.ofBool) =
      cnfTokenWorkSymbols tokens ++ [formulaPad] := by
  induction tokens with
  | nil => rfl
  | cons token rest ih =>
      cases token <;>
        change _ :: packWorkSymbols
            ((encodeTokenPairs rest ++ [false]).map TapeSymbol.ofBool) =
          _ :: (cnfTokenWorkSymbols rest ++ [formulaPad]) <;>
        exact congrArg (List.cons _) ih

/-- The arbitrary-input work bridge is exact on a framed token stream. -/
theorem rawInputWorkTape_encodeTokenPairs_formulaPad
    (tokens : List CNFToken) :
    rawInputWorkTape (encodeTokenPairs tokens ++ [false]) =
      WorkTape.ofSymbols
        (cnfTokenWorkSymbols tokens ++ [formulaPad]) := by
  unfold rawInputWorkTape
  rw [packWorkSymbols_encodeTokenPairs_formulaPad]

theorem packWorkSymbols_encodeTokenPairs
    (tokens : List CNFToken) :
    packWorkSymbols
        ((encodeTokenPairs tokens).map TapeSymbol.ofBool) =
      cnfTokenWorkSymbols tokens := by
  rw [← encodeWorkRight_cnfTokenWorkSymbols]
  exact packWorkSymbols_encodeWorkRight
    (cnfTokenWorkSymbols tokens)

theorem rawInputWorkTape_encodeTokenPairs
    (tokens : List CNFToken) :
    rawInputWorkTape (encodeTokenPairs tokens) =
      WorkTape.ofSymbols (cnfTokenWorkSymbols tokens) := by
  unfold rawInputWorkTape
  rw [packWorkSymbols_encodeTokenPairs]

theorem packWorkSymbols_encodeTokenPairs_wrongPad
    (tokens : List CNFToken) :
    packWorkSymbols
        ((encodeTokenPairs tokens ++ [true]).map TapeSymbol.ofBool) =
      cnfTokenWorkSymbols tokens ++ [WorkSymbol.oneBlank] := by
  induction tokens with
  | nil => rfl
  | cons token rest ih =>
      cases token <;>
        change _ :: packWorkSymbols
            ((encodeTokenPairs rest ++ [true]).map TapeSymbol.ofBool) =
          _ :: (cnfTokenWorkSymbols rest ++
            [WorkSymbol.oneBlank]) <;>
        exact congrArg (List.cons _) ih

theorem rawInputWorkTape_encodeTokenPairs_wrongPad
    (tokens : List CNFToken) :
    rawInputWorkTape (encodeTokenPairs tokens ++ [true]) =
      WorkTape.ofSymbols
        (cnfTokenWorkSymbols tokens ++
          [WorkSymbol.oneBlank]) := by
  unfold rawInputWorkTape
  rw [packWorkSymbols_encodeTokenPairs_wrongPad]

/-- Canonical formula bytes expose the exact formula-token work word and
its unique final pad. -/
theorem rawInputWorkTape_encodeFormula (formula : CNFFormula) :
    rawInputWorkTape (encodeFormula formula) =
      WorkTape.ofSymbols
        (cnfTokenWorkSymbols (encodeFormulaTokens formula) ++
          [formulaPad]) := by
  unfold encodeFormula encodeCNF
  exact rawInputWorkTape_encodeTokenPairs_formulaPad
    (encodeFormulaTokens formula)

/-! ### Canonical work words -/

def unaryWord (count : Nat) : List WorkSymbol :=
  List.replicate count tokenT ++ [tokenF]

def literalWord (literal : CNFLiteral) : List WorkSymbol :=
  (if literal.positive then tokenT else tokenF) ::
    unaryWord literal.variableIndex

def literalListWord : List CNFLiteral → List WorkSymbol
  | [] => []
  | literal :: rest => literalWord literal ++ literalListWord rest

def clauseListWord : List (List CNFLiteral) → List WorkSymbol
  | [] => []
  | clause :: rest =>
      tokenSep ::
        (literalListWord clause ++ tokenFinish :: clauseListWord rest)

def formulaWord (formula : CNFFormula) : List WorkSymbol :=
  unaryWord formula.variableCount ++
    clauseListWord formula.clauses ++ [tokenFinish]

theorem unaryWord_eq_token_work_symbols (count : Nat) :
    unaryWord count =
      cnfTokenWorkSymbols (encodeUnaryTokens count) := by
  unfold unaryWord
  exact (cnfTokenWorkSymbols_encodeUnaryTokens count).symm

theorem literalWord_eq_token_work_symbols (literal : CNFLiteral) :
    literalWord literal =
      cnfTokenWorkSymbols (encodeLiteralTokens literal) := by
  unfold literalWord encodeLiteralTokens
  rw [unaryWord_eq_token_work_symbols]
  cases literal.positive <;> rfl

theorem literalListWord_eq_token_work_symbols
    (literals : List CNFLiteral) :
    literalListWord literals =
      cnfTokenWorkSymbols (encodeLiteralListTokens literals) := by
  induction literals with
  | nil => rfl
  | cons literal rest ih =>
      unfold literalListWord encodeLiteralListTokens
      rw [cnfTokenWorkSymbols_append, ← literalWord_eq_token_work_symbols,
        ← ih]

theorem clauseListWord_eq_token_work_symbols
    (clauses : List (List CNFLiteral)) :
    clauseListWord clauses =
      cnfTokenWorkSymbols (encodeClauseListTokens clauses) := by
  induction clauses with
  | nil => rfl
  | cons clause rest ih =>
      unfold clauseListWord encodeClauseListTokens encodeClauseTokens
      rw [cnfTokenWorkSymbols_append]
      change
        tokenSep ::
            (literalListWord clause ++ tokenFinish :: clauseListWord rest) =
          (tokenSep ::
            cnfTokenWorkSymbols
              (encodeLiteralListTokens clause ++ [.finish])) ++
            cnfTokenWorkSymbols (encodeClauseListTokens rest)
      rw [cnfTokenWorkSymbols_append,
        ← literalListWord_eq_token_work_symbols, ← ih]
      simp [cnfTokenWorkSymbols, CNFToken.workSymbol,
        tokenFinish, cnfFinish, List.append_assoc]

theorem formulaWord_eq_token_work_symbols (formula : CNFFormula) :
    formulaWord formula =
      cnfTokenWorkSymbols (encodeFormulaTokens formula) := by
  unfold formulaWord encodeFormulaTokens encodeCNFTokens
  rw [cnfTokenWorkSymbols_append, cnfTokenWorkSymbols_append,
    ← unaryWord_eq_token_work_symbols,
    ← clauseListWord_eq_token_work_symbols]
  rfl

theorem formulaWord_ne_nil (formula : CNFFormula) :
    formulaWord formula ≠ [] := by
  unfold formulaWord unaryWord
  cases formula.variableCount <;> simp

/-! ### Exact canonical grammar scan -/

theorem headerUnary_exact
    (count : Nat) (left suffix : List WorkSymbol) :
    workRunExact? machine (unaryWord count).length
        (workConfigAtWord State.header left
          (unaryWord count ++ suffix)) =
      some
        (workConfigAtWord State.clauses
          (pushWorkLeft (unaryWord count) left) suffix) := by
  induction count generalizing left with
  | zero =>
      change
        workRunExact? machine 1
            (focusedConfiguration State.header left tokenF suffix) =
          some
            (workConfigAtWord State.clauses
              (tokenF :: left) suffix)
      exact workRunExact?_one_of_step machine _ _
        (header_f_step left suffix)
  | succ count ih =>
      change
        (match workStep? machine
            (focusedConfiguration State.header left tokenT
              (unaryWord count ++ suffix)) with
         | none => none
         | some next =>
             workRunExact? machine (unaryWord count).length next) =
          some
            (workConfigAtWord State.clauses
              (pushWorkLeft (unaryWord count) (tokenT :: left))
              suffix)
      rw [header_t_step]
      exact ih (tokenT :: left)

theorem literalUnary_exact
    (count : Nat) (left suffix : List WorkSymbol) :
    workRunExact? machine (unaryWord count).length
        (workConfigAtWord State.literal left
          (unaryWord count ++ suffix)) =
      some
        (workConfigAtWord State.clause
          (pushWorkLeft (unaryWord count) left) suffix) := by
  induction count generalizing left with
  | zero =>
      change
        workRunExact? machine 1
            (focusedConfiguration State.literal left tokenF suffix) =
          some
            (workConfigAtWord State.clause
              (tokenF :: left) suffix)
      exact workRunExact?_one_of_step machine _ _
        (literal_f_step left suffix)
  | succ count ih =>
      change
        (match workStep? machine
            (focusedConfiguration State.literal left tokenT
              (unaryWord count ++ suffix)) with
         | none => none
         | some next =>
             workRunExact? machine (unaryWord count).length next) =
          some
            (workConfigAtWord State.clause
              (pushWorkLeft (unaryWord count) (tokenT :: left))
              suffix)
      rw [literal_t_step]
      exact ih (tokenT :: left)

theorem literal_exact
    (literal : CNFLiteral) (left suffix : List WorkSymbol) :
    workRunExact? machine (literalWord literal).length
        (workConfigAtWord State.clause left
          (literalWord literal ++ suffix)) =
      some
        (workConfigAtWord State.clause
          (pushWorkLeft (literalWord literal) left) suffix) := by
  rcases literal with ⟨positive, index⟩
  cases positive with
  | false =>
      change
        (match workStep? machine
            (focusedConfiguration State.clause left tokenF
              (unaryWord index ++ suffix)) with
         | none => none
         | some next =>
             workRunExact? machine (unaryWord index).length next) =
          some
            (workConfigAtWord State.clause
              (pushWorkLeft (unaryWord index) (tokenF :: left))
              suffix)
      rw [clause_f_step]
      exact literalUnary_exact index (tokenF :: left) suffix
  | true =>
      change
        (match workStep? machine
            (focusedConfiguration State.clause left tokenT
              (unaryWord index ++ suffix)) with
         | none => none
         | some next =>
             workRunExact? machine (unaryWord index).length next) =
          some
            (workConfigAtWord State.clause
              (pushWorkLeft (unaryWord index) (tokenT :: left))
              suffix)
      rw [clause_t_step]
      exact literalUnary_exact index (tokenT :: left) suffix

theorem literalList_exact
    (literals : List CNFLiteral) (left suffix : List WorkSymbol) :
    workRunExact? machine (literalListWord literals).length
        (workConfigAtWord State.clause left
          (literalListWord literals ++ suffix)) =
      some
        (workConfigAtWord State.clause
          (pushWorkLeft (literalListWord literals) left) suffix) := by
  induction literals generalizing left with
  | nil => rfl
  | cons literal rest ih =>
      unfold literalListWord
      have first := literal_exact literal left
        (literalListWord rest ++ suffix)
      have tail := ih
        (pushWorkLeft (literalWord literal) left)
      have combined := workRunExact?_compose machine
        (literalWord literal).length
        (literalListWord rest).length _ _ _ first tail
      rw [List.length_append,
        pushWorkLeft_append]
      simpa [List.append_assoc] using combined

theorem oneClauseBody_exact
    (clause : List CNFLiteral) (left suffix : List WorkSymbol) :
    workRunExact? machine
        (literalListWord clause).length
        (workConfigAtWord State.clause left
          (literalListWord clause ++ tokenFinish :: suffix)) =
      some
        (workConfigAtWord State.clause
          (pushWorkLeft (literalListWord clause) left)
          (tokenFinish :: suffix)) :=
  literalList_exact clause left (tokenFinish :: suffix)

theorem clauseBody_exact
    (clause : List CNFLiteral) (left suffix : List WorkSymbol) :
    workRunExact? machine ((literalListWord clause).length + 1)
        (workConfigAtWord State.clause left
          (literalListWord clause ++ tokenFinish :: suffix)) =
      some
        (workConfigAtWord State.clauses
          (tokenFinish ::
            pushWorkLeft (literalListWord clause) left) suffix) := by
  have scanned := oneClauseBody_exact clause left suffix
  have finish := workRunExact?_one_of_step machine _ _
    (clause_finish_step
      (pushWorkLeft (literalListWord clause) left) suffix)
  exact workRunExact?_compose machine
    (literalListWord clause).length 1 _ _ _ scanned finish

theorem clauseList_exact
    (clauses : List (List CNFLiteral))
    (left suffix : List WorkSymbol) :
    workRunExact? machine (clauseListWord clauses).length
        (workConfigAtWord State.clauses left
          (clauseListWord clauses ++ suffix)) =
      some
        (workConfigAtWord State.clauses
          (pushWorkLeft (clauseListWord clauses) left) suffix) := by
  induction clauses generalizing left with
  | nil => rfl
  | cons clause rest ih =>
      unfold clauseListWord
      have separator := workRunExact?_one_of_step machine _ _
        (clauses_sep_step left
          (literalListWord clause ++
            tokenFinish :: (clauseListWord rest ++ suffix)))
      have body := clauseBody_exact clause (tokenSep :: left)
        (clauseListWord rest ++ suffix)
      have throughBody := workRunExact?_compose machine 1
        ((literalListWord clause).length + 1) _ _ _
        separator body
      have tail := ih
        (tokenFinish ::
          pushWorkLeft (literalListWord clause) (tokenSep :: left))
      have combined := workRunExact?_compose machine
        (1 + ((literalListWord clause).length + 1))
        (clauseListWord rest).length _ _ _
        throughBody tail
      simpa [List.length_append, List.append_assoc,
        pushWorkLeft, pushWorkLeft_append,
        workConfigAtWord, WorkTape.atWord, focusedConfiguration,
        WorkTape.focus,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using combined

theorem formulaScan_exact
    (formula : CNFFormula) (left suffix : List WorkSymbol) :
    workRunExact? machine (formulaWord formula).length
        (workConfigAtWord State.header left
          (formulaWord formula ++ suffix)) =
      some
        (workConfigAtWord State.expectPad
          (pushWorkLeft (formulaWord formula) left) suffix) := by
  unfold formulaWord
  have header := headerUnary_exact formula.variableCount left
    (clauseListWord formula.clauses ++ tokenFinish :: suffix)
  have clauses := clauseList_exact formula.clauses
    (pushWorkLeft (unaryWord formula.variableCount) left)
    (tokenFinish :: suffix)
  have throughClauses := workRunExact?_compose machine
    (unaryWord formula.variableCount).length
    (clauseListWord formula.clauses).length _ _ _
    header clauses
  have finish := workRunExact?_one_of_step machine _ _
    (clauses_finish_step
      (pushWorkLeft (clauseListWord formula.clauses)
        (pushWorkLeft (unaryWord formula.variableCount) left))
      suffix)
  have combined := workRunExact?_compose machine
    ((unaryWord formula.variableCount).length +
      (clauseListWord formula.clauses).length)
    1 _ _ _ throughClauses finish
  rw [List.length_append, List.length_append,
    pushWorkLeft_append, pushWorkLeft_append]
  cases suffix <;>
    simpa [Nat.add_assoc, pushWorkLeft, workConfigAtWord,
      WorkTape.atWord, WorkTape.moveRight,
      WorkTape.focus, focusedConfiguration] using combined

/-! ### Exact successful restoration -/

inductive RestorableSourceSymbol : WorkSymbol → Prop where
  | f : RestorableSourceSymbol tokenF
  | t : RestorableSourceSymbol tokenT
  | sep : RestorableSourceSymbol tokenSep
  | finish : RestorableSourceSymbol tokenFinish
  | pad : RestorableSourceSymbol formulaPad

theorem formulaWord_restorable
    (formula : CNFFormula) (symbol : WorkSymbol)
    (member : symbol ∈ formulaWord formula) :
    RestorableSourceSymbol symbol := by
  rw [formulaWord_eq_token_work_symbols] at member
  have raw := cnfTokenWorkSymbols_raw
    (encodeFormulaTokens formula) symbol member
  cases raw with
  | f => exact .f
  | t => exact .t
  | sep => exact .sep
  | finish => exact .finish

theorem successRestore_source_step
    (head : WorkSymbol) (leftTail rightSide : List WorkSymbol)
    (allowed : RestorableSourceSymbol head) :
    workStep? machine
        (workConfigAtLeftWord State.successRestoreLeft
          (head :: leftTail) rightSide) =
      some
        (workConfigAtLeftWord State.successRestoreLeft
          leftTail (head :: rightSide)) := by
  cases allowed <;> rfl

def restoreWord (formula : CNFFormula) : List WorkSymbol :=
  formulaPad :: pushWorkLeft (formulaWord formula) []

theorem restoreWord_restorable
    (formula : CNFFormula) (symbol : WorkSymbol)
    (member : symbol ∈ restoreWord formula) :
    RestorableSourceSymbol symbol := by
  unfold restoreWord at member
  cases member with
  | head => exact .pad
  | tail _ tailMember =>
      exact pushWorkLeft_members_allowed RestorableSourceSymbol
        (formulaWord formula) []
        (formulaWord_restorable formula)
        (by intro found impossible; contradiction)
        symbol tailMember

theorem restoreWord_length (formula : CNFFormula) :
    (restoreWord formula).length =
      (formulaWord formula).length + 1 := by
  unfold restoreWord
  rw [List.length_cons, pushWorkLeft_length]
  simp

theorem pushWorkLeft_restoreWord (formula : CNFFormula) :
    pushWorkLeft (restoreWord formula) [cellBlank] =
      formulaWord formula ++ [formulaPad, cellBlank] := by
  unfold restoreWord
  change
    pushWorkLeft (pushWorkLeft (formulaWord formula) [])
        (formulaPad :: [cellBlank]) =
      formulaWord formula ++ [formulaPad, cellBlank]
  exact pushWorkLeft_cancel (formulaWord formula)
    [formulaPad, cellBlank]

def acceptedConfiguration (formula : CNFFormula) :
    WorkConfiguration :=
  workConfigAtWord State.accept [cellBlank]
    (formulaWord formula ++ [formulaPad, cellBlank])

theorem acceptedConfiguration_state (formula : CNFFormula) :
    (acceptedConfiguration formula).state = machine.acceptState := by
  rfl

theorem acceptedConfiguration_halted (formula : CNFFormula) :
    machine.isHalted (acceptedConfiguration formula) = true := by
  rfl

theorem boot_formula_exact (formula : CNFFormula) :
    workRunExact? machine 2
        (workStartConfiguration machine
          (WorkTape.ofSymbols
            (formulaWord formula ++ [formulaPad]))) =
      some
        (workConfigAtWord State.header [leftGuard]
          (formulaWord formula ++ [formulaPad])) := by
  cases wordEq : formulaWord formula with
  | nil =>
      exact False.elim (formulaWord_ne_nil formula wordEq)
  | cons first rest =>
      have boot := workRunExact?_one_of_step machine _ _
        (boot_step [] (rest ++ [formulaPad]) first)
      have install := workRunExact?_one_of_step machine _ _
        (installGuard_step [] (first :: rest ++ [formulaPad]) cellBlank)
      have combined := workRunExact?_compose machine 1 1 _ _ _
        boot install
      simpa [machine, workStartConfiguration, WorkTape.ofSymbols,
        workConfigAtWord, WorkTape.atWord,
        WorkTape.focus, WorkTape.write, WorkTape.moveRight,
        focusedConfiguration] using combined

theorem boot_nonempty_word_exact
    (word : List WorkSymbol) (nonempty : word ≠ []) :
    workRunExact? machine 2
        (workStartConfiguration machine
          (WorkTape.ofSymbols word)) =
      some
        (workConfigAtWord State.header [leftGuard] word) := by
  cases word with
  | nil => contradiction
  | cons first rest =>
      have boot := workRunExact?_one_of_step machine _ _
        (boot_step [] rest first)
      have install := workRunExact?_one_of_step machine _ _
        (installGuard_step [] (first :: rest) cellBlank)
      have combined := workRunExact?_compose machine 1 1 _ _ _
        boot install
      simpa [machine, workStartConfiguration, WorkTape.ofSymbols,
        workConfigAtWord, WorkTape.atWord,
        WorkTape.focus, WorkTape.write, WorkTape.moveRight,
        focusedConfiguration] using combined

theorem padAndEOF_exact
    (left : List WorkSymbol) :
    workRunExact? machine 2
        (workConfigAtWord State.expectPad left [formulaPad]) =
      some
        (workConfigAtLeftWord State.successRestoreLeft
          (formulaPad :: left) [cellBlank]) := by
  have pad := workRunExact?_one_of_step machine _ _
    (expectPad_step left [])
  have eof := workRunExact?_one_of_step machine _ _
    (finalEOF_blank_step (formulaPad :: left) [])
  exact workRunExact?_compose machine 1 1 _ _ _ pad eof

theorem canonical_restore_start
    (formula : CNFFormula) :
    workConfigAtLeftWord State.successRestoreLeft
        (formulaPad ::
          pushWorkLeft (formulaWord formula) [leftGuard])
        [cellBlank] =
      workConfigAtLeftWord State.successRestoreLeft
        (restoreWord formula ++ [leftGuard]) [cellBlank] := by
  unfold restoreWord
  rw [pushWorkLeft_split_far]
  rfl

theorem restoreAndAccept_exact (formula : CNFFormula) :
    workRunExact? machine ((restoreWord formula).length + 1)
        (workConfigAtLeftWord State.successRestoreLeft
          (restoreWord formula ++ [leftGuard]) [cellBlank]) =
      some (acceptedConfiguration formula) := by
  have scan := workRunExact?_scanLeft machine
    State.successRestoreLeft RestorableSourceSymbol
    successRestore_source_step
    (restoreWord formula) [leftGuard] [cellBlank]
    (restoreWord_restorable formula)
  rw [pushWorkLeft_restoreWord] at scan
  have guard :
      workRunExact? machine 1
          (workConfigAtLeftWord State.successRestoreLeft [leftGuard]
            (formulaWord formula ++ [formulaPad, cellBlank])) =
        some (acceptedConfiguration formula) := by
    cases wordEq : formulaWord formula with
    | nil =>
        exact False.elim (formulaWord_ne_nil formula wordEq)
    | cons first rest =>
        have step := workRunExact?_one_of_step machine _ _
          (successRestore_guard_step []
            (first :: rest ++ [formulaPad, cellBlank]))
        simpa [acceptedConfiguration, wordEq, workConfigAtWord,
          workConfigAtLeftWord, WorkTape.atWord, WorkTape.atLeftWord,
          WorkTape.focus, WorkTape.write, WorkTape.moveRight,
          focusedConfiguration] using step
  have complete := workRunExact?_compose machine
    (restoreWord formula).length 1 _ _ _ scan guard
  simpa [acceptedConfiguration] using complete

def validWorkSteps (formula : CNFFormula) : Nat :=
  2 * (formulaWord formula).length + 6

/-- Canonical formula bytes take one exact, fully explicit work trace to the
accepting halt. -/
theorem encodeFormula_exact (formula : CNFFormula) :
    workRunExact? machine (validWorkSteps formula)
        (workStartConfiguration machine
          (rawInputWorkTape (encodeFormula formula))) =
      some (acceptedConfiguration formula) := by
  rw [rawInputWorkTape_encodeFormula,
    ← formulaWord_eq_token_work_symbols]
  have boot := boot_formula_exact formula
  have scan := formulaScan_exact formula [leftGuard] [formulaPad]
  have throughScan := workRunExact?_compose machine
    2 (formulaWord formula).length _ _ _ boot scan
  have boundary := padAndEOF_exact
    (pushWorkLeft (formulaWord formula) [leftGuard])
  have throughBoundary := workRunExact?_compose machine
    (2 + (formulaWord formula).length) 2 _ _ _
    throughScan boundary
  rw [canonical_restore_start formula] at throughBoundary
  have restore := restoreAndAccept_exact formula
  have complete := workRunExact?_compose machine
    (2 + (formulaWord formula).length + 2)
    ((restoreWord formula).length + 1) _ _ _
    throughBoundary restore
  have stepsEq :
      (2 + (formulaWord formula).length + 2) +
          ((restoreWord formula).length + 1) =
        validWorkSteps formula := by
    rw [restoreWord_length]
    unfold validWorkSteps
    omega
  rw [← stepsEq]
  exact complete

theorem acceptedConfiguration_outputBits (formula : CNFFormula) :
    (encodeWorkTape (acceptedConfiguration formula).tape).outputBits =
      encodeFormula formula := by
  cases wordEq : formulaWord formula with
  | nil =>
      exact False.elim (formulaWord_ne_nil formula wordEq)
  | cons first rest =>
      have encoded :=
        encodeWorkRight_cnfTokenWorkSymbols
          (encodeFormulaTokens formula)
      rw [← formulaWord_eq_token_work_symbols, wordEq] at encoded
      unfold acceptedConfiguration
      rw [wordEq]
      change
        Tape.decodeOutputCells
            (first.first :: first.second ::
              encodeWorkRight
                (rest ++ [formulaPad, cellBlank])) =
          encodeFormula formula
      change
        encodeWorkRight (first :: rest) =
          (encodeTokenPairs
            (encodeFormulaTokens formula)).map TapeSymbol.ofBool
        at encoded
      rw [encodeWorkRight_append]
      change
        Tape.decodeOutputCells
            (encodeWorkRight (first :: rest) ++
              [TapeSymbol.zero, TapeSymbol.blank,
                TapeSymbol.blank, TapeSymbol.blank]) =
          encodeFormula formula
      rw [encoded]
      unfold encodeFormula encodeCNF
      have decoded := Tape.decodeOutputCells_append_blank
        (encodeTokenPairs (encodeFormulaTokens formula) ++ [false])
        [TapeSymbol.blank, TapeSymbol.blank]
      simpa [List.map_append, TapeSymbol.ofBool,
        encodeFormulaTokens] using decoded

/-! ### Exact fail-closed cleanup -/

theorem cleanupSeekGuard_workStep (tape : WorkTape) :
    workStep? machine
        ({ state := State.cleanupSeekGuard, tape := tape } :
          WorkConfiguration) =
      if tape.head == leftGuard then
        some
          { state := State.cleanupRight
            tape := (tape.write cellBlank).move .right }
      else
        some
          { state := State.cleanupSeekGuard
            tape := tape.move .left } := by
  rcases tape with ⟨left, ⟨first, second⟩, right⟩
  cases first <;> cases second <;> rfl

theorem cleanupRight_workStep (tape : WorkTape) :
    workStep? machine
        ({ state := State.cleanupRight, tape := tape } :
          WorkConfiguration) =
      if tape.head == cellBlank then
        some
          { state := State.reject
            tape := tape }
      else
        some
          { state := State.cleanupRight
            tape := (tape.write cellBlank).move .right } := by
  rcases tape with ⟨left, ⟨first, second⟩, right⟩
  cases first <;> cases second <;> rfl

private theorem workSymbol_beq_false_of_ne
    (first second : WorkSymbol) (different : first ≠ second) :
    (first == second) = false := by
  rcases first with ⟨firstLeft, firstRight⟩
  rcases second with ⟨secondLeft, secondRight⟩
  cases firstLeft <;> cases firstRight <;>
    cases secondLeft <;> cases secondRight <;>
    first | rfl | exact False.elim (different rfl)

def pushCleanupScan : List WorkSymbol → List WorkSymbol →
    List WorkSymbol
  | [], right => right
  | symbol :: rest, right =>
      pushCleanupScan rest (symbol :: right)

def cleanupSeekConfiguration
    (outsideLeft scan right : List WorkSymbol) :
    WorkConfiguration :=
  match scan with
  | [] =>
      { state := State.cleanupSeekGuard
        tape :=
          { left := outsideLeft
            head := leftGuard
            right := right } }
  | symbol :: rest =>
      { state := State.cleanupSeekGuard
        tape :=
          { left := rest ++ leftGuard :: outsideLeft
            head := symbol
            right := right } }

private theorem cleanupSeekConfiguration_step
    (outsideLeft : List WorkSymbol) (symbol : WorkSymbol)
    (rest right : List WorkSymbol)
    (notGuard : symbol ≠ leftGuard) :
    workStep? machine
        (cleanupSeekConfiguration outsideLeft
          (symbol :: rest) right) =
      some
        (cleanupSeekConfiguration outsideLeft rest
          (symbol :: right)) := by
  unfold cleanupSeekConfiguration
  have compared :
      (symbol == leftGuard) = false :=
    workSymbol_beq_false_of_ne symbol leftGuard notGuard
  rw [cleanupSeekGuard_workStep]
  change
    (if symbol == leftGuard then _ else _) =
      some
        (cleanupSeekConfiguration outsideLeft rest
          (symbol :: right))
  rw [compared]
  cases rest <;> rfl

theorem cleanupSeekGuard_exact
    (outsideLeft scan right : List WorkSymbol)
    (noInnerGuard :
      ∀ symbol, symbol ∈ scan → symbol ≠ leftGuard) :
    workRunExact? machine scan.length
        (cleanupSeekConfiguration outsideLeft scan right) =
      some
        (cleanupSeekConfiguration outsideLeft []
          (pushCleanupScan scan right)) := by
  induction scan generalizing right with
  | nil => rfl
  | cons symbol rest ih =>
      have headNotGuard :
          symbol ≠ leftGuard :=
        noInnerGuard symbol (List.Mem.head rest)
      have restNoGuard :
          ∀ found, found ∈ rest → found ≠ leftGuard := by
        intro found member
        exact noInnerGuard found (List.Mem.tail symbol member)
      change
        (match workStep? machine
            (cleanupSeekConfiguration outsideLeft
              (symbol :: rest) right) with
         | none => none
         | some next =>
             workRunExact? machine rest.length next) =
          some
            (cleanupSeekConfiguration outsideLeft []
              (pushCleanupScan (symbol :: rest) right))
      rw [cleanupSeekConfiguration_step outsideLeft symbol rest right
        headNotGuard]
      exact ih (symbol :: right) restNoGuard

theorem pushCleanupScan_length
    (scan right : List WorkSymbol) :
    (pushCleanupScan scan right).length =
      scan.length + right.length := by
  induction scan generalizing right with
  | nil => simp [pushCleanupScan]
  | cons symbol rest ih =>
      change
        (pushCleanupScan rest (symbol :: right)).length =
          (symbol :: rest).length + right.length
      rw [ih]
      simp only [List.length_cons]
      omega

def pushCleanupBlanks : List WorkSymbol → List WorkSymbol →
    List WorkSymbol
  | [], left => left
  | _ :: rest, left =>
      pushCleanupBlanks rest (cellBlank :: left)

def cleanupRightFiniteConfiguration
    (left word : List WorkSymbol) : WorkConfiguration :=
  match word with
  | [] =>
      { state := State.cleanupRight
        tape :=
          { left := left
            head := cellBlank
            right := [] } }
  | symbol :: rest =>
      { state := State.cleanupRight
        tape :=
          { left := left
            head := symbol
            right := rest } }

private theorem cleanupRightFiniteConfiguration_step
    (left : List WorkSymbol) (symbol : WorkSymbol)
    (rest : List WorkSymbol)
    (notBlank : symbol ≠ cellBlank) :
    workStep? machine
        (cleanupRightFiniteConfiguration left
          (symbol :: rest)) =
      some
        (cleanupRightFiniteConfiguration
          (cellBlank :: left) rest) := by
  unfold cleanupRightFiniteConfiguration
  have compared :
      (symbol == cellBlank) = false :=
    workSymbol_beq_false_of_ne symbol cellBlank notBlank
  rw [cleanupRight_workStep]
  change
    (if symbol == cellBlank then _ else _) =
      some
        (cleanupRightFiniteConfiguration
          (cellBlank :: left) rest)
  rw [compared]
  cases rest <;> rfl

theorem cleanupRightFinite_erase_exact
    (left word : List WorkSymbol)
    (nonblank :
      ∀ symbol, symbol ∈ word → symbol ≠ cellBlank) :
    workRunExact? machine word.length
        (cleanupRightFiniteConfiguration left word) =
      some
        (cleanupRightFiniteConfiguration
          (pushCleanupBlanks word left) []) := by
  induction word generalizing left with
  | nil => rfl
  | cons symbol rest ih =>
      have headNotBlank :
          symbol ≠ cellBlank :=
        nonblank symbol (List.Mem.head rest)
      have restNonblank :
          ∀ found, found ∈ rest → found ≠ cellBlank := by
        intro found member
        exact nonblank found (List.Mem.tail symbol member)
      change
        (match workStep? machine
            (cleanupRightFiniteConfiguration left
              (symbol :: rest)) with
         | none => none
         | some next =>
             workRunExact? machine rest.length next) =
          some
            (cleanupRightFiniteConfiguration
              (pushCleanupBlanks (symbol :: rest) left) [])
      rw [cleanupRightFiniteConfiguration_step
        left symbol rest headNotBlank]
      exact ih (cellBlank :: left) restNonblank

theorem cleanupRightFinite_reject_exact
    (left : List WorkSymbol) :
    workRunExact? machine 1
        (cleanupRightFiniteConfiguration left []) =
      some
        { state := State.reject
          tape :=
            { left := left
              head := cellBlank
              right := [] } } := by
  change
    (match workStep? machine
        ({ state := State.cleanupRight
           tape :=
             { left := left
               head := cellBlank
               right := [] } } : WorkConfiguration) with
     | none => none
     | some next => some next) =
      some
        { state := State.reject
          tape :=
            { left := left
              head := cellBlank
              right := [] } }
  rw [cleanupRight_workStep]
  rfl

theorem cleanupRightFinite_exact
    (left word : List WorkSymbol)
    (nonblank :
      ∀ symbol, symbol ∈ word → symbol ≠ cellBlank) :
    workRunExact? machine (word.length + 1)
        (cleanupRightFiniteConfiguration left word) =
      some
        { state := State.reject
          tape :=
            { left := pushCleanupBlanks word left
              head := cellBlank
              right := [] } } := by
  exact workRunExact?_compose machine word.length 1 _ _ _
    (cleanupRightFinite_erase_exact left word nonblank)
    (cleanupRightFinite_reject_exact
      (pushCleanupBlanks word left))

def guardedCleanupSteps
    (leftScan rightWord : List WorkSymbol) : Nat :=
  leftScan.length + 1 +
    (pushCleanupScan leftScan rightWord).length + 1

theorem guardedCleanupSteps_eq
    (leftScan rightWord : List WorkSymbol) :
    guardedCleanupSteps leftScan rightWord =
      2 * leftScan.length + rightWord.length + 2 := by
  unfold guardedCleanupSteps
  rw [pushCleanupScan_length]
  omega

def cleanupRejectConfiguration
    (outsideLeft leftScan rightWord : List WorkSymbol) :
    WorkConfiguration :=
  { state := State.reject
    tape :=
      { left :=
          pushCleanupBlanks
            (pushCleanupScan leftScan rightWord)
            (cellBlank :: outsideLeft)
        head := cellBlank
        right := [] } }

theorem guardedCleanupFinite_exact
    (outsideLeft leftScan rightWord : List WorkSymbol)
    (noInnerGuard :
      ∀ symbol, symbol ∈ leftScan → symbol ≠ leftGuard)
    (nonblank :
      ∀ symbol,
        symbol ∈ pushCleanupScan leftScan rightWord →
          symbol ≠ cellBlank) :
    workRunExact? machine
        (guardedCleanupSteps leftScan rightWord)
        (cleanupSeekConfiguration
          outsideLeft leftScan rightWord) =
      some
        (cleanupRejectConfiguration
          outsideLeft leftScan rightWord) := by
  let forwardWord := pushCleanupScan leftScan rightWord
  let atGuard :=
    cleanupSeekConfiguration outsideLeft [] forwardWord
  let atErase :=
    cleanupRightFiniteConfiguration
      (cellBlank :: outsideLeft) forwardWord
  have seek :
      workRunExact? machine leftScan.length
          (cleanupSeekConfiguration
            outsideLeft leftScan rightWord) =
        some atGuard := by
    exact cleanupSeekGuard_exact
      outsideLeft leftScan rightWord noInnerGuard
  have crossGuard :
      workRunExact? machine 1 atGuard = some atErase := by
    dsimp [atGuard, atErase, forwardWord]
    change
      (match workStep? machine
          ({ state := State.cleanupSeekGuard
             tape :=
               { left := outsideLeft
                 head := leftGuard
                 right :=
                   pushCleanupScan leftScan rightWord } } :
            WorkConfiguration) with
       | none => none
       | some next => some next) =
        some
          (cleanupRightFiniteConfiguration
            (cellBlank :: outsideLeft)
            (pushCleanupScan leftScan rightWord))
    rw [cleanupSeekGuard_workStep]
    cases pushCleanupScan leftScan rightWord <;> rfl
  have erase :
      workRunExact? machine (forwardWord.length + 1)
          atErase =
        some
          (cleanupRejectConfiguration
            outsideLeft leftScan rightWord) := by
    dsimp [atErase, forwardWord, cleanupRejectConfiguration]
    exact cleanupRightFinite_exact
      (cellBlank :: outsideLeft)
      (pushCleanupScan leftScan rightWord) nonblank
  have throughGuard := workRunExact?_compose machine
    leftScan.length 1 _ _ _ seek crossGuard
  have complete := workRunExact?_compose machine
    (leftScan.length + 1) (forwardWord.length + 1)
    _ _ _ throughGuard erase
  simpa [guardedCleanupSteps, forwardWord,
    Nat.add_assoc] using complete

theorem cleanupRejectConfiguration_output_empty
    (outsideLeft leftScan rightWord : List WorkSymbol) :
    (encodeWorkTape
      (cleanupRejectConfiguration
        outsideLeft leftScan rightWord).tape).outputBits = [] := by
  rfl

theorem cleanupRejectConfiguration_halted
    (outsideLeft leftScan rightWord : List WorkSymbol) :
    machine.isHalted
      (cleanupRejectConfiguration
        outsideLeft leftScan rightWord) = true := by
  rfl

/-! ### Token-grammar failure reaches cleanup -/

def grammarState : FormulaGrammarMode → Nat
  | .header _ => State.header
  | .clauses => State.clauses
  | .clause => State.clause
  | .literal _ _ => State.literal

inductive GrammarBoundary : WorkSymbol → Prop where
  | blank : GrammarBoundary cellBlank
  | formulaPad : GrammarBoundary formulaPad
  | wrongPad : GrammarBoundary WorkSymbol.oneBlank

theorem pushCleanupScan_eq_pushWorkLeft
    (scan right : List WorkSymbol) :
    pushCleanupScan scan right = pushWorkLeft scan right := by
  induction scan generalizing right with
  | nil => rfl
  | cons symbol rest ih =>
      exact ih (symbol :: right)

theorem pushCleanupScan_consumed
    (consumed right : List WorkSymbol) (bad : WorkSymbol) :
    pushCleanupScan (bad :: pushWorkLeft consumed []) right =
      consumed ++ bad :: right := by
  change
    pushCleanupScan (pushWorkLeft consumed []) (bad :: right) =
      consumed ++ bad :: right
  rw [pushCleanupScan_eq_pushWorkLeft]
  exact pushWorkLeft_cancel consumed (bad :: right)

theorem cleanupSeekConfiguration_of_consumed
    (consumed right : List WorkSymbol) (bad : WorkSymbol) :
    cleanupSeekConfiguration []
        (bad :: pushWorkLeft consumed []) right =
      focusedConfiguration State.cleanupSeekGuard
        (pushWorkLeft consumed [leftGuard]) bad right := by
  unfold cleanupSeekConfiguration
  change
    focusedConfiguration State.cleanupSeekGuard
        (pushWorkLeft consumed [] ++ [leftGuard]) bad right =
      focusedConfiguration State.cleanupSeekGuard
        (pushWorkLeft consumed [leftGuard]) bad right
  exact congrArg
    (fun left => focusedConfiguration State.cleanupSeekGuard
      left bad right)
    (pushWorkLeft_split_far consumed [leftGuard]).symm

private theorem mismatch_entry_exact
    (state : Nat) (consumed right : List WorkSymbol)
    (bad : WorkSymbol)
    (step :
      workStep? machine
          (focusedConfiguration state
            (pushWorkLeft consumed [leftGuard]) bad right) =
        some
          (focusedConfiguration State.cleanupSeekGuard
            (pushWorkLeft consumed [leftGuard]) bad right)) :
    workRunExact? machine 1
        (workConfigAtWord state
          (pushWorkLeft consumed [leftGuard]) (bad :: right)) =
      some
        (cleanupSeekConfiguration []
          (bad :: pushWorkLeft consumed []) right) := by
  rw [cleanupSeekConfiguration_of_consumed]
  exact workRunExact?_one_of_step machine _ _ step

theorem header_boundary_enters_cleanup
    (left right : List WorkSymbol) (bad : WorkSymbol)
    (boundary : GrammarBoundary bad) :
    workStep? machine
        (focusedConfiguration State.header left bad right) =
      some
        (focusedConfiguration State.cleanupSeekGuard
          left bad right) := by
  cases boundary <;> rfl

theorem header_finish_enters_cleanup
    (left right : List WorkSymbol) :
    workStep? machine
        (focusedConfiguration State.header left tokenFinish right) =
      some
        (focusedConfiguration State.cleanupSeekGuard
          left tokenFinish right) := by
  rfl

theorem clauses_boundary_enters_cleanup
    (left right : List WorkSymbol) (bad : WorkSymbol)
    (boundary : GrammarBoundary bad) :
    workStep? machine
        (focusedConfiguration State.clauses left bad right) =
      some
        (focusedConfiguration State.cleanupSeekGuard
          left bad right) := by
  cases boundary <;> rfl

theorem clauses_f_enters_cleanup
    (left right : List WorkSymbol) :
    workStep? machine
        (focusedConfiguration State.clauses left tokenF right) =
      some
        (focusedConfiguration State.cleanupSeekGuard
          left tokenF right) := by
  rfl

theorem clauses_t_enters_cleanup
    (left right : List WorkSymbol) :
    workStep? machine
        (focusedConfiguration State.clauses left tokenT right) =
      some
        (focusedConfiguration State.cleanupSeekGuard
          left tokenT right) := by
  rfl

theorem clause_boundary_enters_cleanup
    (left right : List WorkSymbol) (bad : WorkSymbol)
    (boundary : GrammarBoundary bad) :
    workStep? machine
        (focusedConfiguration State.clause left bad right) =
      some
        (focusedConfiguration State.cleanupSeekGuard
          left bad right) := by
  cases boundary <;> rfl

theorem clause_sep_enters_cleanup
    (left right : List WorkSymbol) :
    workStep? machine
        (focusedConfiguration State.clause left tokenSep right) =
      some
        (focusedConfiguration State.cleanupSeekGuard
          left tokenSep right) := by
  rfl

theorem literal_boundary_enters_cleanup
    (left right : List WorkSymbol) (bad : WorkSymbol)
    (boundary : GrammarBoundary bad) :
    workStep? machine
        (focusedConfiguration State.literal left bad right) =
      some
        (focusedConfiguration State.cleanupSeekGuard
          left bad right) := by
  cases boundary <;> rfl

theorem literal_sep_enters_cleanup
    (left right : List WorkSymbol) :
    workStep? machine
        (focusedConfiguration State.literal left tokenSep right) =
      some
        (focusedConfiguration State.cleanupSeekGuard
          left tokenSep right) := by
  rfl

theorem expectPad_token_enters_cleanup
    (left right : List WorkSymbol) (token : CNFToken) :
    workStep? machine
        (focusedConfiguration State.expectPad left
          token.workSymbol right) =
      some
        (focusedConfiguration State.cleanupSeekGuard left
          token.workSymbol right) := by
  cases token <;> rfl

theorem expectPad_wrongPad_enters_cleanup
    (left right : List WorkSymbol) :
    workStep? machine
        (focusedConfiguration State.expectPad left
          WorkSymbol.oneBlank right) =
      some
        (focusedConfiguration State.cleanupSeekGuard left
          WorkSymbol.oneBlank right) := by
  rfl

theorem expectPad_blank_enters_cleanup
    (left right : List WorkSymbol) :
    workStep? machine
        (focusedConfiguration State.expectPad left
          cellBlank right) =
      some
        (focusedConfiguration State.cleanupSeekGuard left
          cellBlank right) := by
  rfl

def GrammarFailureTrace
    (mode : FormulaGrammarMode) (tokens : List CNFToken)
    (consumed : List WorkSymbol) (boundary : WorkSymbol)
    (suffix : List WorkSymbol) : Prop :=
  ∃ steps scan right,
    steps ≤ tokens.length + 1 ∧
    workRunExact? machine steps
          (workConfigAtWord (grammarState mode)
            (pushWorkLeft consumed [leftGuard])
            (cnfTokenWorkSymbols tokens ++ boundary :: suffix)) =
        some (cleanupSeekConfiguration [] scan right) ∧
    pushCleanupScan scan right =
      consumed ++ cnfTokenWorkSymbols tokens ++ boundary :: suffix

private theorem grammarFailureTrace_of_mismatch
    (mode : FormulaGrammarMode) (tokens : List CNFToken)
    (consumed : List WorkSymbol) (boundary : WorkSymbol)
    (suffix : List WorkSymbol) (bad : WorkSymbol)
    (right : List WorkSymbol)
    (sourceShape :
      cnfTokenWorkSymbols tokens ++ boundary :: suffix =
        bad :: right)
    (step :
      workStep? machine
          (focusedConfiguration (grammarState mode)
            (pushWorkLeft consumed [leftGuard]) bad right) =
        some
          (focusedConfiguration State.cleanupSeekGuard
            (pushWorkLeft consumed [leftGuard]) bad right)) :
    GrammarFailureTrace mode tokens consumed boundary suffix :=
  ⟨1, bad :: pushWorkLeft consumed [], right, by omega, by
      rw [sourceShape]
      exact mismatch_entry_exact
        (grammarState mode) consumed right bad step, by
      rw [pushCleanupScan_consumed]
      calc
        consumed ++ bad :: right =
            consumed ++
              (cnfTokenWorkSymbols tokens ++ boundary :: suffix) :=
          congrArg (fun word => consumed ++ word)
            sourceShape.symm
        _ = consumed ++ cnfTokenWorkSymbols tokens ++
              boundary :: suffix :=
          (List.append_assoc consumed
            (cnfTokenWorkSymbols tokens)
            (boundary :: suffix)).symm⟩

private theorem grammarFailureTrace_of_consume
    (mode nextMode : FormulaGrammarMode)
    (token : CNFToken) (rest : List CNFToken)
    (consumed : List WorkSymbol) (boundary : WorkSymbol)
    (suffix : List WorkSymbol)
    (step :
      workStep? machine
          (focusedConfiguration (grammarState mode)
            (pushWorkLeft consumed [leftGuard])
            token.workSymbol
            (cnfTokenWorkSymbols rest ++ boundary :: suffix)) =
        some
          (workConfigAtWord (grammarState nextMode)
            (token.workSymbol ::
              pushWorkLeft consumed [leftGuard])
            (cnfTokenWorkSymbols rest ++ boundary :: suffix)))
    (tail :
      GrammarFailureTrace nextMode rest
        (consumed ++ [token.workSymbol]) boundary suffix) :
    GrammarFailureTrace mode (token :: rest)
      consumed boundary suffix := by
  rcases tail with
    ⟨tailSteps, tailScan, tailRight, tailBound,
      tailExact, tailForward⟩
  have leftShape :
      pushWorkLeft (consumed ++ [token.workSymbol]) [leftGuard] =
        token.workSymbol :: pushWorkLeft consumed [leftGuard] := by
    rw [pushWorkLeft_append]
    rfl
  have one :
      workRunExact? machine 1
          (workConfigAtWord (grammarState mode)
            (pushWorkLeft consumed [leftGuard])
            (token.workSymbol ::
              (cnfTokenWorkSymbols rest ++ boundary :: suffix))) =
        some
          (workConfigAtWord (grammarState nextMode)
            (pushWorkLeft (consumed ++ [token.workSymbol])
              [leftGuard])
            (cnfTokenWorkSymbols rest ++ boundary :: suffix)) := by
    have raw := workRunExact?_one_of_step machine _ _ step
    rw [leftShape]
    exact raw
  have complete := workRunExact?_compose machine 1 tailSteps
    _ _ _ one tailExact
  exact
    ⟨1 + tailSteps, tailScan, tailRight, by
        have bound := tailBound
        simp only [List.length_cons]
        omega, by
        simpa [cnfTokenWorkSymbols] using complete
      , by
        simpa [cnfTokenWorkSymbols, List.append_assoc]
          using tailForward⟩

private theorem movedRight_eq_workConfigAtWord
    (state : Nat) (left : List WorkSymbol)
    (head : WorkSymbol) (right : List WorkSymbol) :
    ({ state := state
       tape :=
         (focusedConfiguration state left head right).tape.moveRight } :
        WorkConfiguration) =
      workConfigAtWord state (head :: left) right := by
  cases right <;> rfl

private theorem header_t_consume
    (left right : List WorkSymbol) :
    workStep? machine
        (focusedConfiguration State.header left tokenT right) =
      some
        (workConfigAtWord State.header
          (tokenT :: left) right) := by
  rw [header_t_step]
  exact congrArg some
    (movedRight_eq_workConfigAtWord
      State.header left tokenT right)

private theorem header_f_consume
    (left right : List WorkSymbol) :
    workStep? machine
        (focusedConfiguration State.header left tokenF right) =
      some
        (workConfigAtWord State.clauses
          (tokenF :: left) right) := by
  rw [header_f_step]
  exact congrArg some
    (movedRight_eq_workConfigAtWord
      State.clauses left tokenF right)

private theorem clauses_sep_consume
    (left right : List WorkSymbol) :
    workStep? machine
        (focusedConfiguration State.clauses left tokenSep right) =
      some
        (workConfigAtWord State.clause
          (tokenSep :: left) right) := by
  rw [clauses_sep_step]
  exact congrArg some
    (movedRight_eq_workConfigAtWord
      State.clause left tokenSep right)

private theorem clauses_finish_consume
    (left right : List WorkSymbol) :
    workStep? machine
        (focusedConfiguration State.clauses left tokenFinish right) =
      some
        (workConfigAtWord State.expectPad
          (tokenFinish :: left) right) := by
  rw [clauses_finish_step]
  exact congrArg some
    (movedRight_eq_workConfigAtWord
      State.expectPad left tokenFinish right)

private theorem clause_f_consume
    (left right : List WorkSymbol) :
    workStep? machine
        (focusedConfiguration State.clause left tokenF right) =
      some
        (workConfigAtWord State.literal
          (tokenF :: left) right) := by
  rw [clause_f_step]
  exact congrArg some
    (movedRight_eq_workConfigAtWord
      State.literal left tokenF right)

private theorem clause_t_consume
    (left right : List WorkSymbol) :
    workStep? machine
        (focusedConfiguration State.clause left tokenT right) =
      some
        (workConfigAtWord State.literal
          (tokenT :: left) right) := by
  rw [clause_t_step]
  exact congrArg some
    (movedRight_eq_workConfigAtWord
      State.literal left tokenT right)

private theorem clause_finish_consume
    (left right : List WorkSymbol) :
    workStep? machine
        (focusedConfiguration State.clause left tokenFinish right) =
      some
        (workConfigAtWord State.clauses
          (tokenFinish :: left) right) := by
  rw [clause_finish_step]
  exact congrArg some
    (movedRight_eq_workConfigAtWord
      State.clauses left tokenFinish right)

private theorem literal_f_consume
    (left right : List WorkSymbol) :
    workStep? machine
        (focusedConfiguration State.literal left tokenF right) =
      some
        (workConfigAtWord State.clause
          (tokenF :: left) right) := by
  rw [literal_f_step]
  exact congrArg some
    (movedRight_eq_workConfigAtWord
      State.clause left tokenF right)

private theorem literal_t_consume
    (left right : List WorkSymbol) :
    workStep? machine
        (focusedConfiguration State.literal left tokenT right) =
      some
        (workConfigAtWord State.literal
          (tokenT :: left) right) := by
  rw [literal_t_step]
  exact congrArg some
    (movedRight_eq_workConfigAtWord
      State.literal left tokenT right)

theorem formulaGrammarFailure_exact
    {mode : FormulaGrammarMode} {tokens : List CNFToken}
    (failure : FormulaGrammarFailure mode tokens)
    (consumed : List WorkSymbol) (boundary : WorkSymbol)
    (suffix : List WorkSymbol)
    (boundaryAllowed : GrammarBoundary boundary) :
    GrammarFailureTrace mode tokens consumed boundary suffix := by
  induction failure generalizing consumed suffix with
  | headerEmpty count =>
      exact grammarFailureTrace_of_mismatch
        (.header count) [] consumed boundary suffix boundary suffix rfl
        (header_boundary_enters_cleanup
          (pushWorkLeft consumed [leftGuard]) suffix
          boundary boundaryAllowed)
  | headerSep count rest =>
      exact grammarFailureTrace_of_mismatch
        (.header count) (.sep :: rest) consumed boundary suffix
        tokenSep
        (cnfTokenWorkSymbols rest ++ boundary :: suffix) rfl
        (header_sep_enters_cleanup
          (pushWorkLeft consumed [leftGuard])
          (cnfTokenWorkSymbols rest ++ boundary :: suffix))
  | headerFinish count rest =>
      exact grammarFailureTrace_of_mismatch
        (.header count) (.finish :: rest) consumed boundary suffix
        tokenFinish
        (cnfTokenWorkSymbols rest ++ boundary :: suffix) rfl
        (header_finish_enters_cleanup
          (pushWorkLeft consumed [leftGuard])
          (cnfTokenWorkSymbols rest ++ boundary :: suffix))
  | headerT tail ih =>
      exact grammarFailureTrace_of_consume
        (.header _) (.header _) .t _ consumed boundary suffix
        (header_t_consume
          (pushWorkLeft consumed [leftGuard])
          (cnfTokenWorkSymbols _ ++ boundary :: suffix))
        (ih (consumed ++ [tokenT]) suffix)
  | headerF tail ih =>
      exact grammarFailureTrace_of_consume
        (.header _) .clauses .f _ consumed boundary suffix
        (header_f_consume
          (pushWorkLeft consumed [leftGuard])
          (cnfTokenWorkSymbols _ ++ boundary :: suffix))
        (ih (consumed ++ [tokenF]) suffix)
  | clausesEmpty =>
      exact grammarFailureTrace_of_mismatch
        .clauses [] consumed boundary suffix boundary suffix rfl
        (clauses_boundary_enters_cleanup
          (pushWorkLeft consumed [leftGuard]) suffix
          boundary boundaryAllowed)
  | clausesF rest =>
      exact grammarFailureTrace_of_mismatch
        .clauses (.f :: rest) consumed boundary suffix
        tokenF
        (cnfTokenWorkSymbols rest ++ boundary :: suffix) rfl
        (clauses_f_enters_cleanup
          (pushWorkLeft consumed [leftGuard])
          (cnfTokenWorkSymbols rest ++ boundary :: suffix))
  | clausesT rest =>
      exact grammarFailureTrace_of_mismatch
        .clauses (.t :: rest) consumed boundary suffix
        tokenT
        (cnfTokenWorkSymbols rest ++ boundary :: suffix) rfl
        (clauses_t_enters_cleanup
          (pushWorkLeft consumed [leftGuard])
          (cnfTokenWorkSymbols rest ++ boundary :: suffix))
  | clausesSep tail ih =>
      exact grammarFailureTrace_of_consume
        .clauses .clause .sep _ consumed boundary suffix
        (clauses_sep_consume
          (pushWorkLeft consumed [leftGuard])
          (cnfTokenWorkSymbols _ ++ boundary :: suffix))
        (ih (consumed ++ [tokenSep]) suffix)
  | clausesFinishTrailing next rest =>
      let afterFinish := consumed ++ [tokenFinish]
      let right := cnfTokenWorkSymbols rest ++ boundary :: suffix
      let atNext :=
        workConfigAtWord State.expectPad
          (pushWorkLeft afterFinish [leftGuard])
          (next.workSymbol :: right)
      have leftShape :
          pushWorkLeft afterFinish [leftGuard] =
            tokenFinish :: pushWorkLeft consumed [leftGuard] := by
        dsimp [afterFinish]
        rw [pushWorkLeft_append]
        rfl
      have finish :
          workRunExact? machine 1
              (workConfigAtWord State.clauses
                (pushWorkLeft consumed [leftGuard])
                (tokenFinish :: next.workSymbol :: right)) =
            some atNext := by
        have raw := workRunExact?_one_of_step machine _ _
          (clauses_finish_consume
            (pushWorkLeft consumed [leftGuard])
            (next.workSymbol :: right))
        dsimp [atNext]
        rw [leftShape]
        exact raw
      have mismatch :
          workRunExact? machine 1 atNext =
            some
              (cleanupSeekConfiguration []
                (next.workSymbol ::
                  pushWorkLeft afterFinish []) right) := by
        apply mismatch_entry_exact
        exact expectPad_token_enters_cleanup
          (pushWorkLeft afterFinish [leftGuard]) right next
      have complete := workRunExact?_compose machine
        1 1 _ _ _ finish mismatch
      exact
        ⟨2,
          next.workSymbol ::
            pushWorkLeft afterFinish [],
          right, by simp, by
            simpa [cnfTokenWorkSymbols, afterFinish, right,
              grammarState, tokenFinish, cnfFinish,
              CNFToken.workSymbol]
              using complete, by
            have restored :=
              pushCleanupScan_consumed afterFinish right
                next.workSymbol
            simpa [cnfTokenWorkSymbols, afterFinish, right,
              List.append_assoc, tokenFinish, cnfFinish,
              CNFToken.workSymbol] using restored⟩
  | clauseEmpty =>
      exact grammarFailureTrace_of_mismatch
        .clause [] consumed boundary suffix boundary suffix rfl
        (clause_boundary_enters_cleanup
          (pushWorkLeft consumed [leftGuard]) suffix
          boundary boundaryAllowed)
  | clauseSep rest =>
      exact grammarFailureTrace_of_mismatch
        .clause (.sep :: rest) consumed boundary suffix
        tokenSep
        (cnfTokenWorkSymbols rest ++ boundary :: suffix) rfl
        (clause_sep_enters_cleanup
          (pushWorkLeft consumed [leftGuard])
          (cnfTokenWorkSymbols rest ++ boundary :: suffix))
  | clauseF tail ih =>
      exact grammarFailureTrace_of_consume
        .clause (.literal false 0) .f _ consumed boundary suffix
        (clause_f_consume
          (pushWorkLeft consumed [leftGuard])
          (cnfTokenWorkSymbols _ ++ boundary :: suffix))
        (ih (consumed ++ [tokenF]) suffix)
  | clauseT tail ih =>
      exact grammarFailureTrace_of_consume
        .clause (.literal true 0) .t _ consumed boundary suffix
        (clause_t_consume
          (pushWorkLeft consumed [leftGuard])
          (cnfTokenWorkSymbols _ ++ boundary :: suffix))
        (ih (consumed ++ [tokenT]) suffix)
  | clauseFinish tail ih =>
      exact grammarFailureTrace_of_consume
        .clause .clauses .finish _ consumed boundary suffix
        (clause_finish_consume
          (pushWorkLeft consumed [leftGuard])
          (cnfTokenWorkSymbols _ ++ boundary :: suffix))
        (ih (consumed ++ [tokenFinish]) suffix)
  | literalEmpty positive index =>
      exact grammarFailureTrace_of_mismatch
        (.literal positive index) [] consumed boundary suffix
        boundary suffix rfl
        (literal_boundary_enters_cleanup
          (pushWorkLeft consumed [leftGuard]) suffix
          boundary boundaryAllowed)
  | literalSep positive index rest =>
      exact grammarFailureTrace_of_mismatch
        (.literal positive index) (.sep :: rest)
        consumed boundary suffix tokenSep
        (cnfTokenWorkSymbols rest ++ boundary :: suffix) rfl
        (literal_sep_enters_cleanup
          (pushWorkLeft consumed [leftGuard])
          (cnfTokenWorkSymbols rest ++ boundary :: suffix))
  | literalFinish positive index rest =>
      exact grammarFailureTrace_of_mismatch
        (.literal positive index) (.finish :: rest)
        consumed boundary suffix tokenFinish
        (cnfTokenWorkSymbols rest ++ boundary :: suffix) rfl
        (literal_finish_enters_cleanup
          (pushWorkLeft consumed [leftGuard])
          (cnfTokenWorkSymbols rest ++ boundary :: suffix))
  | literalF tail ih =>
      exact grammarFailureTrace_of_consume
        (.literal _ _) .clause .f _ consumed boundary suffix
        (literal_f_consume
          (pushWorkLeft consumed [leftGuard])
          (cnfTokenWorkSymbols _ ++ boundary :: suffix))
        (ih (consumed ++ [tokenF]) suffix)
  | literalT tail ih =>
      exact grammarFailureTrace_of_consume
        (.literal _ _) (.literal _ _) .t _
        consumed boundary suffix
        (literal_t_consume
          (pushWorkLeft consumed [leftGuard])
          (cnfTokenWorkSymbols _ ++ boundary :: suffix))
        (ih (consumed ++ [tokenT]) suffix)

/-! ### Cleanup at a materialized blank delimiter -/

def cleanupRightConfiguration
    (left word suffix : List WorkSymbol) :
    WorkConfiguration :=
  match word with
  | [] =>
      { state := State.cleanupRight
        tape :=
          { left := left
            head := cellBlank
            right := suffix } }
  | symbol :: rest =>
      { state := State.cleanupRight
        tape :=
          { left := left
            head := symbol
            right := rest ++ cellBlank :: suffix } }

private theorem cleanupRightConfiguration_step
    (left : List WorkSymbol) (symbol : WorkSymbol)
    (rest suffix : List WorkSymbol)
    (notBlank : symbol ≠ cellBlank) :
    workStep? machine
        (cleanupRightConfiguration left
          (symbol :: rest) suffix) =
      some
        (cleanupRightConfiguration
          (cellBlank :: left) rest suffix) := by
  unfold cleanupRightConfiguration
  have compared :
      (symbol == cellBlank) = false :=
    workSymbol_beq_false_of_ne symbol cellBlank notBlank
  rw [cleanupRight_workStep]
  change
    (if symbol == cellBlank then _ else _) =
      some
        (cleanupRightConfiguration
          (cellBlank :: left) rest suffix)
  rw [compared]
  cases rest <;> rfl

theorem cleanupRight_erase_exact
    (left word suffix : List WorkSymbol)
    (nonblank :
      ∀ symbol, symbol ∈ word → symbol ≠ cellBlank) :
    workRunExact? machine word.length
        (cleanupRightConfiguration left word suffix) =
      some
        (cleanupRightConfiguration
          (pushCleanupBlanks word left) [] suffix) := by
  induction word generalizing left with
  | nil => rfl
  | cons symbol rest ih =>
      have headNotBlank :
          symbol ≠ cellBlank :=
        nonblank symbol (List.Mem.head rest)
      have restNonblank :
          ∀ found, found ∈ rest → found ≠ cellBlank := by
        intro found member
        exact nonblank found (List.Mem.tail symbol member)
      change
        (match workStep? machine
            (cleanupRightConfiguration left
              (symbol :: rest) suffix) with
         | none => none
         | some next =>
             workRunExact? machine rest.length next) =
          some
            (cleanupRightConfiguration
              (pushCleanupBlanks (symbol :: rest) left)
              [] suffix)
      rw [cleanupRightConfiguration_step
        left symbol rest suffix headNotBlank]
      exact ih (cellBlank :: left) restNonblank

theorem cleanupRight_reject_exact
    (left suffix : List WorkSymbol) :
    workRunExact? machine 1
        (cleanupRightConfiguration left [] suffix) =
      some
        { state := State.reject
          tape :=
            { left := left
              head := cellBlank
              right := suffix } } := by
  change
    (match workStep? machine
        ({ state := State.cleanupRight
           tape :=
             { left := left
               head := cellBlank
               right := suffix } } : WorkConfiguration) with
     | none => none
     | some next => some next) =
      some
        { state := State.reject
          tape :=
            { left := left
              head := cellBlank
              right := suffix } }
  rw [cleanupRight_workStep]
  rfl

theorem cleanupRight_exact
    (left word suffix : List WorkSymbol)
    (nonblank :
      ∀ symbol, symbol ∈ word → symbol ≠ cellBlank) :
    workRunExact? machine (word.length + 1)
        (cleanupRightConfiguration left word suffix) =
      some
        { state := State.reject
          tape :=
            { left := pushCleanupBlanks word left
              head := cellBlank
              right := suffix } } := by
  exact workRunExact?_compose machine word.length 1 _ _ _
    (cleanupRight_erase_exact left word suffix nonblank)
    (cleanupRight_reject_exact
      (pushCleanupBlanks word left) suffix)

def guardedCleanupExplicitSteps
    (leftScan eraseWord : List WorkSymbol) : Nat :=
  leftScan.length + 1 + eraseWord.length + 1

def cleanupExplicitRejectConfiguration
    (outsideLeft eraseWord suffix : List WorkSymbol) :
    WorkConfiguration :=
  { state := State.reject
    tape :=
      { left :=
          pushCleanupBlanks eraseWord
            (cellBlank :: outsideLeft)
        head := cellBlank
        right := suffix } }

theorem guardedCleanupExplicit_exact
    (outsideLeft leftScan right eraseWord suffix :
      List WorkSymbol)
    (noInnerGuard :
      ∀ symbol, symbol ∈ leftScan → symbol ≠ leftGuard)
    (forwardShape :
      pushCleanupScan leftScan right =
        eraseWord ++ cellBlank :: suffix)
    (nonblank :
      ∀ symbol, symbol ∈ eraseWord →
        symbol ≠ cellBlank) :
    workRunExact? machine
        (guardedCleanupExplicitSteps leftScan eraseWord)
        (cleanupSeekConfiguration
          outsideLeft leftScan right) =
      some
        (cleanupExplicitRejectConfiguration
          outsideLeft eraseWord suffix) := by
  let atGuard :=
    cleanupSeekConfiguration outsideLeft []
      (eraseWord ++ cellBlank :: suffix)
  let atErase :=
    cleanupRightConfiguration
      (cellBlank :: outsideLeft) eraseWord suffix
  have seek :
      workRunExact? machine leftScan.length
          (cleanupSeekConfiguration
            outsideLeft leftScan right) =
        some atGuard := by
    have run := cleanupSeekGuard_exact
      outsideLeft leftScan right noInnerGuard
    rw [forwardShape] at run
    exact run
  have crossGuard :
      workRunExact? machine 1 atGuard = some atErase := by
    dsimp [atGuard, atErase]
    change
      (match workStep? machine
          ({ state := State.cleanupSeekGuard
             tape :=
               { left := outsideLeft
                 head := leftGuard
                 right :=
                   eraseWord ++ cellBlank :: suffix } } :
            WorkConfiguration) with
       | none => none
       | some next => some next) =
        some
          (cleanupRightConfiguration
            (cellBlank :: outsideLeft) eraseWord suffix)
    rw [cleanupSeekGuard_workStep]
    cases eraseWord <;> rfl
  have erase :
      workRunExact? machine (eraseWord.length + 1)
          atErase =
        some
          (cleanupExplicitRejectConfiguration
            outsideLeft eraseWord suffix) := by
    dsimp [atErase, cleanupExplicitRejectConfiguration]
    exact cleanupRight_exact
      (cellBlank :: outsideLeft)
      eraseWord suffix nonblank
  have throughGuard := workRunExact?_compose machine
    leftScan.length 1 _ _ _ seek crossGuard
  have complete := workRunExact?_compose machine
    (leftScan.length + 1) (eraseWord.length + 1)
    _ _ _ throughGuard erase
  simpa [guardedCleanupExplicitSteps,
    Nat.add_assoc] using complete

theorem cleanupExplicitRejectConfiguration_output_empty
    (outsideLeft eraseWord : List WorkSymbol) :
    (encodeWorkTape
      (cleanupExplicitRejectConfiguration
        outsideLeft eraseWord []).tape).outputBits = [] := by
  rfl

theorem cleanupExplicitRejectConfiguration_halted
    (outsideLeft eraseWord suffix : List WorkSymbol) :
    machine.isHalted
      (cleanupExplicitRejectConfiguration
        outsideLeft eraseWord suffix) = true := by
  rfl

/-! ### Closed malformed-grammar traces -/

theorem tokenWorkSymbol_ne_blank (token : CNFToken) :
    token.workSymbol ≠ cellBlank := by
  cases token <;> decide

theorem tokenWorkSymbol_ne_leftGuard (token : CNFToken) :
    token.workSymbol ≠ leftGuard := by
  cases token <;> decide

theorem cnfTokenWorkSymbols_ne_blank
    (tokens : List CNFToken) (symbol : WorkSymbol)
    (member : symbol ∈ cnfTokenWorkSymbols tokens) :
    symbol ≠ cellBlank := by
  induction tokens with
  | nil => contradiction
  | cons token rest ih =>
      cases member with
      | head => exact tokenWorkSymbol_ne_blank token
      | tail _ tailMember => exact ih tailMember

theorem cnfTokenWorkSymbols_ne_leftGuard
    (tokens : List CNFToken) (symbol : WorkSymbol)
    (member : symbol ∈ cnfTokenWorkSymbols tokens) :
    symbol ≠ leftGuard := by
  induction tokens with
  | nil => contradiction
  | cons token rest ih =>
      cases member with
      | head => exact tokenWorkSymbol_ne_leftGuard token
      | tail _ tailMember => exact ih tailMember

theorem formulaWord_ne_blank
    (formula : CNFFormula) (symbol : WorkSymbol)
    (member : symbol ∈ formulaWord formula) :
    symbol ≠ cellBlank := by
  rw [formulaWord_eq_token_work_symbols] at member
  exact cnfTokenWorkSymbols_ne_blank
    (encodeFormulaTokens formula) symbol member

theorem formulaWord_ne_leftGuard
    (formula : CNFFormula) (symbol : WorkSymbol)
    (member : symbol ∈ formulaWord formula) :
    symbol ≠ leftGuard := by
  rw [formulaWord_eq_token_work_symbols] at member
  exact cnfTokenWorkSymbols_ne_leftGuard
    (encodeFormulaTokens formula) symbol member

theorem pushCleanupScan_eq_reverse_append
    (scan right : List WorkSymbol) :
    pushCleanupScan scan right = scan.reverse ++ right := by
  induction scan generalizing right with
  | nil => rfl
  | cons head rest ih =>
      change pushCleanupScan rest (head :: right) =
        (head :: rest).reverse ++ right
      rw [ih]
      simp [List.reverse_cons, List.append_assoc]

theorem mem_pushCleanupScan_of_mem
    (scan right : List WorkSymbol) (symbol : WorkSymbol)
    (member : symbol ∈ scan) :
    symbol ∈ pushCleanupScan scan right := by
  rw [pushCleanupScan_eq_reverse_append]
  exact List.mem_append.mpr
    (Or.inl (List.mem_reverse.mpr member))

theorem formulaGrammarFailure_nonblank_exact
    {tokens : List CNFToken}
    (failure : FormulaGrammarFailure (.header 0) tokens)
    (boundary : WorkSymbol)
    (boundaryAllowed : GrammarBoundary boundary)
    (boundaryNonblank : boundary ≠ cellBlank)
    (boundaryNotGuard : boundary ≠ leftGuard) :
    ∃ steps final,
      steps ≤ 3 * tokens.length + 5 ∧
      workRunExact? machine steps
          (workConfigAtWord State.header [leftGuard]
            (cnfTokenWorkSymbols tokens ++ [boundary])) =
        some final ∧
      final.state = State.reject ∧
      (encodeWorkTape final.tape).outputBits = [] := by
  rcases formulaGrammarFailure_exact failure []
      boundary [] boundaryAllowed with
    ⟨scanSteps, scan, right, scanBound,
      scanExact, forward⟩
  have forwardShape :
      pushCleanupScan scan right =
        cnfTokenWorkSymbols tokens ++ [boundary] := by
    simpa using forward
  have noGuardWhole :
      ∀ symbol,
        symbol ∈ cnfTokenWorkSymbols tokens ++ [boundary] →
          symbol ≠ leftGuard := by
    intro symbol member
    rcases List.mem_append.mp member with tokenMember | boundaryMember
    · exact cnfTokenWorkSymbols_ne_leftGuard
        tokens symbol tokenMember
    · simp only [List.mem_singleton] at boundaryMember
      subst symbol
      exact boundaryNotGuard
  have noInnerGuard :
      ∀ symbol, symbol ∈ scan → symbol ≠ leftGuard := by
    intro symbol member
    apply noGuardWhole symbol
    rw [← forwardShape]
    exact mem_pushCleanupScan_of_mem scan right symbol member
  have nonblank :
      ∀ symbol,
        symbol ∈ pushCleanupScan scan right →
          symbol ≠ cellBlank := by
    intro symbol member
    apply (show
      ∀ found,
        found ∈ cnfTokenWorkSymbols tokens ++ [boundary] →
          found ≠ cellBlank by
      intro found wholeMember
      rcases List.mem_append.mp wholeMember with
        tokenMember | boundaryMember
      · exact cnfTokenWorkSymbols_ne_blank
          tokens found tokenMember
      · simp only [List.mem_singleton] at boundaryMember
        subst found
        exact boundaryNonblank)
    rw [← forwardShape]
    exact member
  have cleanup := guardedCleanupFinite_exact
    [] scan right noInnerGuard nonblank
  have complete := workRunExact?_compose machine
    scanSteps (guardedCleanupSteps scan right)
    _ _ _ scanExact cleanup
  have forwardLengths := congrArg List.length forwardShape
  rw [pushCleanupScan_length, List.length_append,
    cnfTokenWorkSymbols_length] at forwardLengths
  refine
    ⟨scanSteps + guardedCleanupSteps scan right,
      cleanupRejectConfiguration [] scan right, ?_,
      complete, rfl, ?_⟩
  · rw [guardedCleanupSteps_eq]
    simp at forwardLengths
    omega
  · exact cleanupRejectConfiguration_output_empty [] scan right

theorem formulaGrammarFailure_blank_exact
    {tokens : List CNFToken}
    (failure : FormulaGrammarFailure (.header 0) tokens) :
    ∃ steps final,
      steps ≤ 3 * tokens.length + 4 ∧
      workRunExact? machine steps
          (workConfigAtWord State.header [leftGuard]
            (cnfTokenWorkSymbols tokens ++ [cellBlank])) =
        some final ∧
      final.state = State.reject ∧
      (encodeWorkTape final.tape).outputBits = [] := by
  rcases formulaGrammarFailure_exact failure []
      cellBlank [] .blank with
    ⟨scanSteps, scan, right, scanBound,
      scanExact, forward⟩
  have forwardShape :
      pushCleanupScan scan right =
        cnfTokenWorkSymbols tokens ++ [cellBlank] := by
    simpa using forward
  have noGuardWhole :
      ∀ symbol,
        symbol ∈ cnfTokenWorkSymbols tokens ++ [cellBlank] →
          symbol ≠ leftGuard := by
    intro symbol member
    rcases List.mem_append.mp member with tokenMember | blankMember
    · exact cnfTokenWorkSymbols_ne_leftGuard
        tokens symbol tokenMember
    · simp only [List.mem_singleton] at blankMember
      subst symbol
      decide
  have noInnerGuard :
      ∀ symbol, symbol ∈ scan → symbol ≠ leftGuard := by
    intro symbol member
    apply noGuardWhole symbol
    rw [← forwardShape]
    exact mem_pushCleanupScan_of_mem scan right symbol member
  have cleanup := guardedCleanupExplicit_exact
    [] scan right (cnfTokenWorkSymbols tokens) []
    noInnerGuard forwardShape
    (cnfTokenWorkSymbols_ne_blank tokens)
  have complete := workRunExact?_compose machine
    scanSteps
    (guardedCleanupExplicitSteps scan
      (cnfTokenWorkSymbols tokens))
    _ _ _ scanExact cleanup
  have forwardLengths := congrArg List.length forwardShape
  rw [pushCleanupScan_length, List.length_append,
    cnfTokenWorkSymbols_length] at forwardLengths
  refine
    ⟨scanSteps +
        guardedCleanupExplicitSteps scan
          (cnfTokenWorkSymbols tokens),
      cleanupExplicitRejectConfiguration []
        (cnfTokenWorkSymbols tokens) [], ?_,
      complete, rfl, ?_⟩
  · unfold guardedCleanupExplicitSteps
    rw [cnfTokenWorkSymbols_length]
    simp at forwardLengths
    omega
  · exact cleanupExplicitRejectConfiguration_output_empty
      [] (cnfTokenWorkSymbols tokens)

/-! ### Valid grammar with malformed outer framing -/

theorem decodedTokenWorkShape
    (tokens : List CNFToken) (formula : CNFFormula)
    (decoded : decodeCNFTokens tokens = some formula) :
    cnfTokenWorkSymbols tokens = formulaWord formula := by
  have canonical :=
    encodeCNFTokens_of_decode tokens formula decoded
  exact
    (congrArg cnfTokenWorkSymbols canonical).symm.trans
      (formulaWord_eq_token_work_symbols formula).symm

theorem decodedTokens_wrongPad_exact
    (tokens : List CNFToken) (formula : CNFFormula)
    (decoded : decodeCNFTokens tokens = some formula) :
    ∃ steps final,
      steps ≤ 3 * tokens.length + 5 ∧
      workRunExact? machine steps
          (workConfigAtWord State.header [leftGuard]
            (cnfTokenWorkSymbols tokens ++
              [WorkSymbol.oneBlank])) =
        some final ∧
      final.state = State.reject ∧
      (encodeWorkTape final.tape).outputBits = [] := by
  let word := formulaWord formula
  let scan :=
    WorkSymbol.oneBlank :: pushWorkLeft word []
  have grammar := formulaScan_exact formula [leftGuard]
    [WorkSymbol.oneBlank]
  have mismatch :
      workRunExact? machine 1
          (workConfigAtWord State.expectPad
            (pushWorkLeft word [leftGuard])
            [WorkSymbol.oneBlank]) =
        some (cleanupSeekConfiguration [] scan []) := by
    apply mismatch_entry_exact
    exact expectPad_wrongPad_enters_cleanup
      (pushWorkLeft word [leftGuard]) []
  have throughMismatch := workRunExact?_compose machine
    word.length 1 _ _ _ grammar mismatch
  have forwardShape :
      pushCleanupScan scan [] =
        word ++ [WorkSymbol.oneBlank] := by
    exact pushCleanupScan_consumed word []
      WorkSymbol.oneBlank
  have noInnerGuard :
      ∀ symbol, symbol ∈ scan → symbol ≠ leftGuard := by
    intro symbol member
    have wholeMember :
        symbol ∈ word ++ [WorkSymbol.oneBlank] := by
      rw [← forwardShape]
      exact mem_pushCleanupScan_of_mem scan [] symbol member
    rcases List.mem_append.mp wholeMember with
      wordMember | padMember
    · exact formulaWord_ne_leftGuard formula symbol wordMember
    · simp only [List.mem_singleton] at padMember
      subst symbol
      decide
  have nonblank :
      ∀ symbol,
        symbol ∈ pushCleanupScan scan [] →
          symbol ≠ cellBlank := by
    intro symbol member
    rw [forwardShape] at member
    rcases List.mem_append.mp member with
      wordMember | padMember
    · exact formulaWord_ne_blank formula symbol wordMember
    · simp only [List.mem_singleton] at padMember
      subst symbol
      decide
  have cleanup := guardedCleanupFinite_exact
    [] scan [] noInnerGuard nonblank
  have complete := workRunExact?_compose machine
    (word.length + 1)
    (guardedCleanupSteps scan []) _ _ _
    throughMismatch cleanup
  have wordShape := decodedTokenWorkShape
    tokens formula decoded
  have wordLength :
      word.length = tokens.length := by
    dsimp [word]
    rw [← wordShape, cnfTokenWorkSymbols_length]
  have scanLength :
      scan.length = word.length + 1 := by
    dsimp [scan]
    rw [pushWorkLeft_length]
    simp
  refine
    ⟨word.length + 1 + guardedCleanupSteps scan [],
      cleanupRejectConfiguration [] scan [], ?_, ?_,
      rfl, cleanupRejectConfiguration_output_empty [] scan []⟩
  · rw [guardedCleanupSteps_eq, scanLength]
    simp [wordLength]
    omega
  · simpa [word, wordShape] using complete

theorem decodedTokens_blank_exact
    (tokens : List CNFToken) (formula : CNFFormula)
    (decoded : decodeCNFTokens tokens = some formula) :
    ∃ steps final,
      steps ≤ 3 * tokens.length + 4 ∧
      workRunExact? machine steps
          (workConfigAtWord State.header [leftGuard]
            (cnfTokenWorkSymbols tokens ++ [cellBlank])) =
        some final ∧
      final.state = State.reject ∧
      (encodeWorkTape final.tape).outputBits = [] := by
  let word := formulaWord formula
  let scan := cellBlank :: pushWorkLeft word []
  have grammar := formulaScan_exact formula [leftGuard] [cellBlank]
  have mismatch :
      workRunExact? machine 1
          (workConfigAtWord State.expectPad
            (pushWorkLeft word [leftGuard]) [cellBlank]) =
        some (cleanupSeekConfiguration [] scan []) := by
    apply mismatch_entry_exact
    exact expectPad_blank_enters_cleanup
      (pushWorkLeft word [leftGuard]) []
  have throughMismatch := workRunExact?_compose machine
    word.length 1 _ _ _ grammar mismatch
  have forwardShape :
      pushCleanupScan scan [] = word ++ [cellBlank] := by
    exact pushCleanupScan_consumed word [] cellBlank
  have noInnerGuard :
      ∀ symbol, symbol ∈ scan → symbol ≠ leftGuard := by
    intro symbol member
    have wholeMember :
        symbol ∈ word ++ [cellBlank] := by
      rw [← forwardShape]
      exact mem_pushCleanupScan_of_mem scan [] symbol member
    rcases List.mem_append.mp wholeMember with
      wordMember | blankMember
    · exact formulaWord_ne_leftGuard formula symbol wordMember
    · simp only [List.mem_singleton] at blankMember
      subst symbol
      decide
  have cleanup := guardedCleanupExplicit_exact
    [] scan [] word [] noInnerGuard forwardShape
    (formulaWord_ne_blank formula)
  have complete := workRunExact?_compose machine
    (word.length + 1)
    (guardedCleanupExplicitSteps scan word)
    _ _ _ throughMismatch cleanup
  have wordShape := decodedTokenWorkShape
    tokens formula decoded
  have wordLength :
      word.length = tokens.length := by
    dsimp [word]
    rw [← wordShape, cnfTokenWorkSymbols_length]
  have scanLength :
      scan.length = word.length + 1 := by
    dsimp [scan]
    rw [pushWorkLeft_length]
    simp
  refine
    ⟨word.length + 1 +
        guardedCleanupExplicitSteps scan word,
      cleanupExplicitRejectConfiguration [] word [],
      ?_, ?_, rfl,
      cleanupExplicitRejectConfiguration_output_empty [] word⟩
  · unfold guardedCleanupExplicitSteps
    rw [scanLength, wordLength]
    omega
  · simpa [word, wordShape] using complete

/-! ### Arbitrary raw-input totality -/

def parserWorkBound (inputLength : Nat) : Nat :=
  8 * inputLength + 32

def RejectingTrace (bits : BitString) : Prop :=
  ∃ steps final,
    steps ≤ parserWorkBound bits.length ∧
    workRunExact? machine steps
        (workStartConfiguration machine
          (rawInputWorkTape bits)) =
      some final ∧
    final.state = State.reject ∧
    (encodeWorkTape final.tape).outputBits = []

theorem ofSymbols_append_blank_blankEquivalent
    (word : List WorkSymbol) :
    WorkTape.BlankEquivalent
      (WorkTape.ofSymbols word)
      (WorkTape.ofSymbols (word ++ [cellBlank])) := by
  cases word with
  | nil =>
      exact WorkTape.blankEquivalent_refl WorkTape.blank
  | cons head rest =>
      have padded := WorkTape.blankEquivalent_of_padding
        (WorkTape.ofSymbols (head :: rest)) 0 1
      exact WorkTape.blankEquivalent_symm (by
        simpa [WorkTape.ofSymbols, cellBlank, cnfBlank] using padded)

theorem evenRawStart_blankEquivalent
    (tokens : List CNFToken) :
    WorkConfiguration.BlankEquivalent
      (workStartConfiguration machine
        (rawInputWorkTape (encodeTokenPairs tokens)))
      (workStartConfiguration machine
        (WorkTape.ofSymbols
          (cnfTokenWorkSymbols tokens ++ [cellBlank]))) := by
  rw [rawInputWorkTape_encodeTokenPairs]
  exact
    ⟨rfl,
      ofSymbols_append_blank_blankEquivalent
        (cnfTokenWorkSymbols tokens)⟩

theorem output_empty_of_workBlankEquivalent
    {actual canonical : WorkTape}
    (equivalent : WorkTape.BlankEquivalent actual canonical)
    (canonicalEmpty :
      (encodeWorkTape canonical).outputBits = []) :
    (encodeWorkTape actual).outputBits = [] := by
  have canonicalHeadBlank :
      canonical.head.first = TapeSymbol.blank := by
    cases headCase : canonical.head.first with
    | blank => rfl
    | zero =>
        unfold Tape.outputBits encodeWorkTape at canonicalEmpty
        rw [headCase] at canonicalEmpty
        contradiction
    | one =>
        unfold Tape.outputBits encodeWorkTape at canonicalEmpty
        rw [headCase] at canonicalEmpty
        contradiction
  have actualHeadBlank :
      actual.head.first = TapeSymbol.blank := by
    exact
      (congrArg WorkSymbol.first equivalent.head).trans
        canonicalHeadBlank
  unfold Tape.outputBits encodeWorkTape
  rw [actualHeadBlank]
  rfl

private theorem rejectingTrace_of_materialized_blank
    (bits : BitString) (tokens : List CNFToken)
    (bitsShape : bits = encodeTokenPairs tokens)
    (headerTrace :
      ∃ steps final,
        steps ≤ 3 * tokens.length + 4 ∧
        workRunExact? machine steps
            (workConfigAtWord State.header [leftGuard]
              (cnfTokenWorkSymbols tokens ++ [cellBlank])) =
          some final ∧
        final.state = State.reject ∧
        (encodeWorkTape final.tape).outputBits = []) :
    RejectingTrace bits := by
  rcases headerTrace with
    ⟨headerSteps, canonicalFinal, headerBound,
      headerExact, canonicalReject, canonicalOutput⟩
  have boot := boot_nonempty_word_exact
    (cnfTokenWorkSymbols tokens ++ [cellBlank])
    (by simp)
  have canonicalRun := workRunExact?_compose machine
    2 headerSteps _ _ _ boot headerExact
  have startEquivalent :
      WorkConfiguration.BlankEquivalent
        (workStartConfiguration machine
          (rawInputWorkTape bits))
        (workStartConfiguration machine
          (WorkTape.ofSymbols
            (cnfTokenWorkSymbols tokens ++ [cellBlank]))) := by
    rw [bitsShape]
    exact evenRawStart_blankEquivalent tokens
  rcases workRunExact?_transport machine
      (2 + headerSteps) startEquivalent canonicalRun with
    ⟨actualFinal, actualRun, finalEquivalent⟩
  have bitLength :
      bits.length = 2 * tokens.length := by
    rw [bitsShape, encodeTokenPairs_length]
  refine
    ⟨2 + headerSteps, actualFinal, ?_, actualRun, ?_, ?_⟩
  · unfold parserWorkBound
    omega
  · exact finalEquivalent.state.trans canonicalReject
  · exact output_empty_of_workBlankEquivalent
      finalEquivalent.tape canonicalOutput

private theorem rejectingTrace_of_nonblank_boundary
    (bits : BitString) (tokens : List CNFToken)
    (boundary : WorkSymbol)
    (bitsShape :
      rawInputWorkTape bits =
        WorkTape.ofSymbols
          (cnfTokenWorkSymbols tokens ++ [boundary]))
    (bitLengthLower : tokens.length ≤ bits.length)
    (headerTrace :
      ∃ steps final,
        steps ≤ 3 * tokens.length + 5 ∧
        workRunExact? machine steps
            (workConfigAtWord State.header [leftGuard]
              (cnfTokenWorkSymbols tokens ++ [boundary])) =
          some final ∧
        final.state = State.reject ∧
        (encodeWorkTape final.tape).outputBits = []) :
    RejectingTrace bits := by
  rcases headerTrace with
    ⟨headerSteps, final, headerBound, headerExact,
      reject, output⟩
  have boot := boot_nonempty_word_exact
    (cnfTokenWorkSymbols tokens ++ [boundary])
    (by simp)
  have complete := workRunExact?_compose machine
    2 headerSteps _ _ _ boot headerExact
  refine ⟨2 + headerSteps, final, ?_, ?_, reject, output⟩
  · unfold parserWorkBound
    omega
  · rw [bitsShape]
    exact complete

/-- Every malformed raw word has one exact fail-closed work trace within the
single recorded linear bound. -/
theorem malformed_rejectingTrace
    (bits : BitString)
    (malformed : decodeEncodedCNF bits = none) :
    RejectingTrace bits := by
  rcases decodeEncodedCNF_none_cases bits malformed with
    framing | grammar
  · rcases framing with ⟨tokens, even | wrongPad⟩
    · cases decoded : decodeCNFTokens tokens with
      | none =>
          have failure :=
            decodeCNFTokens_none_to_failure tokens decoded
          exact rejectingTrace_of_materialized_blank
            bits tokens even
            (formulaGrammarFailure_blank_exact failure)
      | some formula =>
          exact rejectingTrace_of_materialized_blank
            bits tokens even
            (decodedTokens_blank_exact tokens formula decoded)
    · have tapeShape :
          rawInputWorkTape bits =
            WorkTape.ofSymbols
              (cnfTokenWorkSymbols tokens ++
                [WorkSymbol.oneBlank]) := by
          rw [wrongPad]
          exact rawInputWorkTape_encodeTokenPairs_wrongPad tokens
      have tokenLengthLower :
          tokens.length ≤ bits.length := by
        rw [wrongPad, BitString.length_append_constructive,
          encodeTokenPairs_length]
        omega
      cases decoded : decodeCNFTokens tokens with
      | none =>
          have failure :=
            decodeCNFTokens_none_to_failure tokens decoded
          exact rejectingTrace_of_nonblank_boundary
            bits tokens WorkSymbol.oneBlank tapeShape
            tokenLengthLower
            (formulaGrammarFailure_nonblank_exact
              failure WorkSymbol.oneBlank .wrongPad
              (by decide) (by decide))
      | some formula =>
          exact rejectingTrace_of_nonblank_boundary
            bits tokens WorkSymbol.oneBlank tapeShape
            tokenLengthLower
            (decodedTokens_wrongPad_exact
              tokens formula decoded)
  · rcases grammar with
      ⟨tokens, tokenDecode, grammarDecode⟩
    have bitsShape :=
      encodeFormulaTokenPairs_of_decode bits tokens tokenDecode
    have tapeShape :
        rawInputWorkTape bits =
          WorkTape.ofSymbols
            (cnfTokenWorkSymbols tokens ++ [formulaPad]) := by
      rw [← bitsShape]
      exact rawInputWorkTape_encodeTokenPairs_formulaPad tokens
    have tokenLengthLower :
        tokens.length ≤ bits.length := by
      rw [← bitsShape, BitString.length_append_constructive,
        encodeTokenPairs_length]
      omega
    have failure :=
      decodeCNFTokens_none_to_failure tokens grammarDecode
    exact rejectingTrace_of_nonblank_boundary
      bits tokens formulaPad tapeShape tokenLengthLower
      (formulaGrammarFailure_nonblank_exact
        failure formulaPad .formulaPad
        (by decide) (by decide))

def ExactParserTrace (bits : BitString) : Prop :=
  ∃ steps final,
    steps ≤ parserWorkBound bits.length ∧
    workRunExact? machine steps
        (workStartConfiguration machine
          (rawInputWorkTape bits)) =
      some final ∧
    machine.isHalted final = true ∧
    (encodeWorkTape final.tape).outputBits =
      validatedCNFBytes bits ∧
    (final.state = State.accept ↔ ValidEncodedCNF bits)

/-- Every raw word follows one exact bounded trace.  The same endpoint
simultaneously records halting, fail-closed output, and acceptance iff strict
whole-word decoding succeeds. -/
theorem allInput_exact (bits : BitString) :
    ExactParserTrace bits := by
  cases decoded : decodeEncodedCNF bits with
  | none =>
      rcases malformed_rejectingTrace bits decoded with
        ⟨steps, final, bound, run, reject, output⟩
      refine
        ⟨steps, final, bound, run, ?_, ?_, ?_⟩
      · unfold WorkMachine.isHalted machine
        rw [reject]
        rfl
      · rw [validatedCNFBytes_of_decode_none bits decoded]
        exact output
      · constructor
        · intro accepted
          rw [reject] at accepted
          contradiction
        · intro valid
          exact False.elim
            (not_valid_of_decode_none decoded valid)
  | some formula =>
      have sourceShape :=
        encodeFormula_of_decode bits formula decoded
      have run := encodeFormula_exact formula
      rw [sourceShape] at run
      have output := acceptedConfiguration_outputBits formula
      rw [sourceShape] at output
      have bitLength :
          bits.length =
            2 * (formulaWord formula).length + 1 := by
        have tokenLength :
            (encodeFormulaTokens formula).length =
              (formulaWord formula).length := by
          have lengths := congrArg List.length
            (formulaWord_eq_token_work_symbols formula)
          rw [cnfTokenWorkSymbols_length] at lengths
          exact lengths.symm
        change
          (encodeCNFTokens formula).length =
            (formulaWord formula).length at tokenLength
        rw [← sourceShape]
        unfold encodeFormula encodeCNF
        rw [BitString.length_append_constructive,
          encodeTokenPairs_length, tokenLength]
        rfl
      have bound :
          validWorkSteps formula ≤
            parserWorkBound bits.length := by
        unfold validWorkSteps parserWorkBound
        omega
      refine
        ⟨validWorkSteps formula,
          acceptedConfiguration formula,
          bound, run, acceptedConfiguration_halted formula,
          ?_, ?_⟩
      · rw [validatedCNFBytes_of_decoded bits formula decoded]
        exact output
      · constructor
        · intro _
          exact valid_of_decoded decoded
        · intro _
          rfl

theorem allInput_exact_trace
    (bits : BitString) :
    ∃ steps final,
      steps ≤ parserWorkBound bits.length ∧
      workRunExact? machine steps
          (workStartConfiguration machine
            (rawInputWorkTape bits)) =
        some final ∧
      machine.isHalted final = true := by
  rcases allInput_exact bits with
    ⟨steps, final, bound, run, halted, _output, _accept⟩
  exact ⟨steps, final, bound, run, halted⟩

theorem allInput_exact_output
    (bits : BitString) :
    ∃ steps final,
      steps ≤ parserWorkBound bits.length ∧
      workRunExact? machine steps
          (workStartConfiguration machine
            (rawInputWorkTape bits)) =
        some final ∧
      (encodeWorkTape final.tape).outputBits =
        validatedCNFBytes bits := by
  rcases allInput_exact bits with
    ⟨steps, final, bound, run, _halted, output, _accept⟩
  exact ⟨steps, final, bound, run, output⟩

theorem allInput_exact_accept_iff
    (bits : BitString) :
    ∃ steps final,
      steps ≤ parserWorkBound bits.length ∧
      workRunExact? machine steps
          (workStartConfiguration machine
            (rawInputWorkTape bits)) =
        some final ∧
      (final.state = machine.acceptState ↔
        ValidEncodedCNF bits) := by
  rcases allInput_exact bits with
    ⟨steps, final, bound, run, _halted, _output, accept⟩
  exact ⟨steps, final, bound, run, accept⟩

theorem workRun_parserWorkBound
    (bits : BitString) :
    ∃ final,
      workRun machine (parserWorkBound bits.length)
          (workStartConfiguration machine
            (rawInputWorkTape bits)) =
        final ∧
      machine.isHalted final = true ∧
      (encodeWorkTape final.tape).outputBits =
        validatedCNFBytes bits ∧
      (final.state = machine.acceptState ↔
        ValidEncodedCNF bits) := by
  rcases allInput_exact bits with
    ⟨steps, final, bound, exact, halted, output, accept⟩
  have run := workRun_pad_exact_halted machine
    steps (parserWorkBound bits.length) _ _
    exact halted bound
  exact ⟨final, run, halted, output, accept⟩

theorem workBoundedDecide_accept_iff
    (bits : BitString) :
    workBoundedDecide machine
        (parserWorkBound bits.length)
        (rawInputWorkTape bits) = .accept ↔
      ValidEncodedCNF bits := by
  rcases workRun_parserWorkBound bits with
    ⟨final, run, _halted, _output, accept⟩
  rw [workBoundedDecide_accept_iff_final]
  rw [run]
  exact accept

theorem workBoundedDecide_ne_timeout
    (bits : BitString) :
    workBoundedDecide machine
        (parserWorkBound bits.length)
        (rawInputWorkTape bits) ≠ .timeout := by
  rw [workBoundedDecide_ne_timeout_iff_final_isHalted]
  rcases workRun_parserWorkBound bits with
    ⟨final, run, halted, _output, _accept⟩
  rw [run]
  exact halted

theorem workBoundedDecide_reject_iff
    (bits : BitString) :
    workBoundedDecide machine
        (parserWorkBound bits.length)
        (rawInputWorkTape bits) = .reject ↔
      ¬ ValidEncodedCNF bits := by
  constructor
  · intro rejected valid
    have accepted :=
      (workBoundedDecide_accept_iff bits).mpr valid
    rw [rejected] at accepted
    contradiction
  · intro invalid
    cases verdict :
        workBoundedDecide machine
          (parserWorkBound bits.length)
          (rawInputWorkTape bits) with
    | accept =>
        exact False.elim
          (invalid ((workBoundedDecide_accept_iff bits).mp verdict))
    | reject => rfl
    | timeout =>
        exact False.elim
          (workBoundedDecide_ne_timeout bits verdict)

end PNP.Concrete.CNFSourceParser
