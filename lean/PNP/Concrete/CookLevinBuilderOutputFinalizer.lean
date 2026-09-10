/-
Copyright (c) 2026 PNP Labs.

Literal external-output finalization for the complete Cook-Levin builder.
The emitted CNF tokens already occupy their exact two raw bit cells. This
fixed machine scans past the represented input and tally, appends the single
false framing bit, and returns to the first output token. Its ordinary compiled
output excludes the retained input, counters and all left-hand workspace.

The full builder composition, polynomial-time function and reduction still
require their own integration. No supplied output-correctness premise is used.
-/
import PNP.Concrete.CookLevinBuilderCanonicalOutput
import PNP.Concrete.TapeBlankEquivalence

namespace PNP.Concrete.CookLevin.BuilderOutputFinalizer

open PipelineTape
open BuilderTokenAppender (tokenSymbol tokenSymbols outputBoundarySymbol workspaceTape sourceCellCount)
open BuilderInputLength (tallySymbol)

def keepRule (source : Nat) (read : WorkSymbol) (target : Nat)
    (move : HeadMove) : WorkRule :=
  {sourceState := source, readSymbol := read, targetState := target,
   writeSymbol := read, move := move}

def writeRule (source : Nat) (read : WorkSymbol) (target : Nat)
    (write : WorkSymbol) (move : HeadMove) : WorkRule :=
  {sourceState := source, readSymbol := read, targetState := target,
   writeSymbol := write, move := move}

/-- Input scan, tally scan, output scan, rewind, accept, reject. -/
def machine : WorkMachine :=
  {rules :=
    [keepRule 0 .blank 0 .right,
     keepRule 0 .zeroBlank 0 .right,
     keepRule 0 .oneBlank 0 .right,
     keepRule 0 rightMarker 1 .right,
     keepRule 1 tallySymbol 1 .right,
     keepRule 1 outputBoundarySymbol 2 .right,
     writeRule 1 .blank 2 outputBoundarySymbol .right,
     keepRule 2 (tokenSymbol .f) 2 .right,
     keepRule 2 (tokenSymbol .t) 2 .right,
     keepRule 2 (tokenSymbol .sep) 2 .right,
     keepRule 2 (tokenSymbol .finish) 2 .right,
     writeRule 2 .blank 3 .zeroBlank .left,
     keepRule 3 (tokenSymbol .f) 3 .left,
     keepRule 3 (tokenSymbol .t) 3 .left,
     keepRule 3 (tokenSymbol .sep) 3 .left,
     keepRule 3 (tokenSymbol .finish) 3 .left,
     keepRule 3 outputBoundarySymbol 4 .right],
   startState := 0, acceptState := 4, rejectState := 5}

theorem rules_pairwise_query_distinct :
    machine.rules.Pairwise WorkMachineChain.QueryDistinct := by
  unfold WorkMachineChain.QueryDistinct
  decide

theorem noRuleAtAccept : WorkMachineChain.NoRuleAtAccept machine := by
  intro rule member
  decide +revert

theorem acceptState_ne_rejectState : machine.acceptState ≠ machine.rejectState := by decide

private def atWord (left : List WorkSymbol) : List WorkSymbol → WorkTape
  | [] => {left := left, head := .blank, right := []}
  | head :: right => {left := left, head := head, right := right}

private def atLeft (right : List WorkSymbol) : List WorkSymbol → WorkTape
  | [] => {left := [], head := .blank, right := right}
  | head :: left => {left := left, head := head, right := right}

private def sourceCells : BitString → List TapeSymbol
  | [] => [.blank]
  | bit :: rest => (bit :: rest).map TapeSymbol.ofBool

private def sourceWord (input : BitString) : List WorkSymbol :=
  (sourceCells input).map dataSymbol

private def leftOfBoundary (input : BitString) (outside : List WorkSymbol) : List WorkSymbol :=
  List.replicate input.length tallySymbol ++
    rightMarker :: ((sourceWord input).reverse ++ leftMarker :: outside)

def finalTape (input : BitString) (outside : List WorkSymbol)
    (output : List CNFToken) : WorkTape :=
  atWord (outputBoundarySymbol :: leftOfBoundary input outside)
    (tokenSymbols output ++ [WorkSymbol.zeroBlank])

def finalConfiguration (input : BitString) (outside : List WorkSymbol)
    (output : List CNFToken) : WorkConfiguration :=
  {state := machine.acceptState, tape := finalTape input outside output}

def workSteps (input : BitString) (output : List CNFToken) : Nat :=
  sourceCellCount input + input.length + 2 * output.length + 4

private theorem sourceWord_length (input : BitString) :
    (sourceWord input).length = sourceCellCount input := by
  cases input <;> simp [sourceWord, sourceCells, sourceCellCount]

private theorem workspace_layout (input : BitString) (outside : List WorkSymbol)
    (output : List CNFToken) :
    workspaceTape input outside output =
      atWord (leftMarker :: outside)
        (sourceWord input ++ rightMarker ::
          (List.replicate input.length tallySymbol ++ BuilderTokenAppender.outputRegion output)) := by
  cases input with
  | nil => rfl
  | cons bit rest =>
      cases bit <;>
        simp [workspaceTape, frameWithGarbage, Tape.ofInput,
          sourceWord, sourceCells, atWord, List.map_map, Function.comp_def, dataSymbol]

private theorem step_input (symbol : TapeSymbol) (left right : List WorkSymbol) :
    workStep? machine {state := 0, tape := {left := left, head := dataSymbol symbol, right := right}} =
      some {state := 0, tape := atWord (dataSymbol symbol :: left) right} := by
  cases symbol <;> cases right <;> rfl

private theorem step_tally (left right : List WorkSymbol) :
    workStep? machine {state := 1, tape := {left := left, head := tallySymbol, right := right}} =
      some {state := 1, tape := atWord (tallySymbol :: left) right} := by
  cases right <;> rfl

private theorem step_token (token : CNFToken) (left right : List WorkSymbol) :
    workStep? machine {state := 2, tape := {left := left, head := tokenSymbol token, right := right}} =
      some {state := 2, tape := atWord (tokenSymbol token :: left) right} := by
  cases token <;> cases right <;> rfl

private theorem step_rewind (token : CNFToken) (left right : List WorkSymbol) :
    workStep? machine {state := 3, tape := {left := left, head := tokenSymbol token, right := right}} =
      some {state := 3, tape := atLeft (tokenSymbol token :: right) left} := by
  cases token <;> cases left <;> rfl

private theorem scan_right (state : Nat) (word left right : List WorkSymbol)
    (step : ∀ symbol ∈ word, ∀ near far,
      workStep? machine {state := state, tape := {left := near, head := symbol, right := far}} =
        some {state := state, tape := atWord (symbol :: near) far}) :
    workRunExact? machine word.length
      {state := state, tape := atWord left (word ++ right)} =
        some {state := state, tape := atWord (word.reverse ++ left) right} := by
  induction word generalizing left with
  | nil => rfl
  | cons symbol rest ih =>
      change (match workStep? machine
        {state := state, tape := {left := left, head := symbol, right := rest ++ right}} with
        | none => none
        | some next => workRunExact? machine rest.length next) = _
      rw [step symbol (by simp only [List.mem_cons, true_or]) left (rest ++ right)]
      simpa only [List.reverse_cons, List.append_assoc, List.singleton_append] using
        ih (symbol :: left) (fun s member => step s (List.mem_cons_of_mem _ member))

private theorem scan_left (word left right : List WorkSymbol)
    (step : ∀ symbol ∈ word, ∀ near far,
      workStep? machine {state := 3, tape := {left := near, head := symbol, right := far}} =
        some {state := 3, tape := atLeft (symbol :: far) near}) :
    workRunExact? machine word.length
      {state := 3, tape := atLeft right (word ++ left)} =
        some {state := 3, tape := atLeft (word.reverse ++ right) left} := by
  induction word generalizing right with
  | nil => rfl
  | cons symbol rest ih =>
      change (match workStep? machine
        {state := 3, tape := {left := rest ++ left, head := symbol, right := right}} with
        | none => none
        | some next => workRunExact? machine rest.length next) = _
      rw [step symbol (by simp only [List.mem_cons, true_or]) (rest ++ left) right]
      simpa only [List.reverse_cons, List.append_assoc, List.singleton_append] using
        ih (symbol :: right) (fun s member => step s (List.mem_cons_of_mem _ member))

private theorem scan_input (input : BitString) (left right : List WorkSymbol) :
    workRunExact? machine (sourceCellCount input)
      {state := 0, tape := atWord left (sourceWord input ++ right)} =
        some {state := 0, tape := atWord ((sourceWord input).reverse ++ left) right} := by
  rw [← sourceWord_length]
  apply scan_right
  intro symbol member
  obtain ⟨raw, _, rfl⟩ := List.mem_map.mp member
  exact step_input raw

private theorem scan_tally (count : Nat) (left right : List WorkSymbol) :
    workRunExact? machine count
      {state := 1, tape := atWord left (List.replicate count tallySymbol ++ right)} =
        some {state := 1, tape := atWord (List.replicate count tallySymbol ++ left) right} := by
  have h := scan_right 1 (List.replicate count tallySymbol) left right (by
    intro symbol member
    have equal : symbol = tallySymbol := (List.mem_replicate.mp member).2
    subst symbol
    exact step_tally)
  simpa only [List.length_replicate, List.reverse_replicate] using h

private theorem scan_output (output : List CNFToken) (left : List WorkSymbol) :
    workRunExact? machine output.length
      {state := 2, tape := atWord left (tokenSymbols output)} =
        some {state := 2, tape := atWord ((tokenSymbols output).reverse ++ left) []} := by
  have h := scan_right 2 (tokenSymbols output) left [] (by
    intro symbol member
    obtain ⟨token, _, rfl⟩ := List.mem_map.mp member
    exact step_token token)
  simpa only [BuilderTokenAppender.tokenSymbols_length, List.append_nil] using h

private theorem rewind_output (output : List CNFToken) (left : List WorkSymbol) :
    workRunExact? machine output.length
      {state := 3, tape := atLeft [WorkSymbol.zeroBlank]
        ((tokenSymbols output).reverse ++ outputBoundarySymbol :: left)} =
        some {state := 3, tape := {left := left, head := outputBoundarySymbol, right := tokenSymbols output ++ [WorkSymbol.zeroBlank]}} := by
  have h := scan_left (tokenSymbols output).reverse (outputBoundarySymbol :: left) [.zeroBlank] (by
    intro symbol member
    have original := List.mem_reverse.mp member
    obtain ⟨token, _, rfl⟩ := List.mem_map.mp original
    exact step_rewind token)
  simpa only [List.length_reverse, BuilderTokenAppender.tokenSymbols_length,
    List.reverse_reverse, atLeft] using h

private theorem enter_tally (left right : List WorkSymbol) :
    workRunExact? machine 1 {state := 0, tape := atWord left (rightMarker :: right)} =
      some {state := 1, tape := atWord (rightMarker :: left) right} := by
  cases right <;> rfl

private theorem enter_output (output : List CNFToken) (left : List WorkSymbol) :
    workRunExact? machine 1
      {state := 1, tape := atWord left (BuilderTokenAppender.outputRegion output)} =
        some {state := 2, tape := atWord (outputBoundarySymbol :: left) (tokenSymbols output)} := by
  cases output <;> rfl

private theorem append_frame (left : List WorkSymbol) :
    workRunExact? machine 1 {state := 2, tape := atWord left []} =
      some {state := 3, tape := atLeft [WorkSymbol.zeroBlank] left} := by
  cases left <;> rfl

private theorem focus_output (output : List CNFToken) (left : List WorkSymbol) :
    workRunExact? machine 1
      {state := 3, tape := {left := left, head := outputBoundarySymbol, right := tokenSymbols output ++ [WorkSymbol.zeroBlank]}} =
      some {state := machine.acceptState, tape := atWord (outputBoundarySymbol :: left) (tokenSymbols output ++ [WorkSymbol.zeroBlank])} := by
  cases output <;> rfl

/-- Every input length, arbitrary retained left workspace, and complete output
word use the same finite machine, including empty input and empty output. -/
theorem workRun_exact (input : BitString) (outside : List WorkSymbol)
    (output : List CNFToken) :
    workRunExact? machine (workSteps input output)
      (workStartConfiguration machine (workspaceTape input outside output)) =
        some (finalConfiguration input outside output) := by
  let sourceLeft := (sourceWord input).reverse ++ leftMarker :: outside
  let tallyLeft := rightMarker :: sourceLeft
  let boundaryLeft := leftOfBoundary input outside
  have h1 := scan_input input (leftMarker :: outside)
    (rightMarker :: (List.replicate input.length tallySymbol ++ BuilderTokenAppender.outputRegion output))
  have h2 := enter_tally sourceLeft
    (List.replicate input.length tallySymbol ++ BuilderTokenAppender.outputRegion output)
  have h3 := scan_tally input.length tallyLeft (BuilderTokenAppender.outputRegion output)
  have h4 := enter_output output boundaryLeft
  have h5 := scan_output output (outputBoundarySymbol :: boundaryLeft)
  have h6 := append_frame ((tokenSymbols output).reverse ++ outputBoundarySymbol :: boundaryLeft)
  have h7 := rewind_output output boundaryLeft
  have h8 := focus_output output boundaryLeft
  have h12 := PipelineMachineSimulation.workRunExact?_compose machine _ _ _ _ _ h1 h2
  have h123 := PipelineMachineSimulation.workRunExact?_compose machine _ _ _ _ _ h12 h3
  have h1234 := PipelineMachineSimulation.workRunExact?_compose machine _ _ _ _ _ h123 h4
  have h12345 := PipelineMachineSimulation.workRunExact?_compose machine _ _ _ _ _ h1234 h5
  have h123456 := PipelineMachineSimulation.workRunExact?_compose machine _ _ _ _ _ h12345 h6
  have h1234567 := PipelineMachineSimulation.workRunExact?_compose machine _ _ _ _ _ h123456 h7
  have hAll := PipelineMachineSimulation.workRunExact?_compose machine _ _ _ _ _ h1234567 h8
  have hCount : sourceCellCount input + 1 + input.length + 1 + output.length + 1 + output.length + 1 =
      workSteps input output := by unfold workSteps; omega
  rw [hCount] at hAll
  rw [workspace_layout]
  exact hAll

private theorem encoded_tokens (output : List CNFToken) :
    encodeWorkRight (tokenSymbols output) =
      (encodeTokenPairs output).map TapeSymbol.ofBool := by
  induction output with
  | nil => rfl
  | cons token rest ih =>
      cases token <;> simp only [tokenSymbols, List.map_cons, encodeWorkRight,
        tokenSymbol, CNFToken.bits, encodeTokenPairs, List.map_cons] at * <;>
        exact congrArg _ (congrArg _ ih)

private theorem observable_word (left word : List WorkSymbol) :
    (encodeWorkTape (atWord left word)).outputBits =
      Tape.decodeOutputCells (encodeWorkRight word) := by
  cases word <;> rfl

/-- The framing false is a real output bit, followed by a blank delimiter.
No input, tally, counter, or retained left-hand symbol is observable. -/
theorem output_eq (input : BitString) (outside : List WorkSymbol)
    (output : List CNFToken) :
    (encodeWorkTape (finalTape input outside output)).outputBits =
      encodeTokenPairs output ++ [false] := by
  rw [finalTape, observable_word, encodeWorkRight_append, encoded_tokens]
  change Tape.decodeOutputCells
    ((encodeTokenPairs output).map TapeSymbol.ofBool ++ [.zero, .blank]) =
      encodeTokenPairs output ++ [false]
  have h := Tape.decodeOutputCells_append_blank (encodeTokenPairs output ++ [false]) []
  simpa only [List.map_append, List.map_cons, List.map_nil, List.append_assoc,
    List.nil_append, List.cons_append, TapeSymbol.ofBool] using h

theorem final_isHalted (input : BitString) (outside : List WorkSymbol)
    (output : List CNFToken) :
    machine.isHalted (finalConfiguration input outside output) = true := by rfl

/-- Linear adapter cost in input and output lengths, with no cost depending
on the size or contents of the untouched retained left workspace. -/
theorem rawTime_le (input : BitString) (output : List CNFToken) :
    6 * workSteps input output ≤ 12 * input.length + 12 * output.length + 30 := by
  have hSource := BuilderTokenAppender.sourceCellCount_le input
  unfold workSteps
  omega

def canonicalOutside {language : Language} (problem : VerifierTableauProblem language) : List WorkSymbol :=
  BuilderBalancedCursor.outside (BuilderCursorSource.registerPrefix problem)
    (BuilderFullScheduleCursorController.bodySlotCount problem) 0 (BuilderCursorSource.preservedTail problem)

def rawTimeBound {language : Language} (verifier : PolynomialTimeVerifier language) : NatPolynomial :=
  .add (.linear 12 30) (.mul (.constant 12) (BuilderRawInputLoop.outputBound verifier))

theorem canonical_workRun_exact {language : Language} (problem : VerifierTableauProblem language) :
    workRunExact? machine (workSteps problem.input (encodeCNFTokens problem.formula))
      (workStartConfiguration machine
        (BuilderCursorSource.cursorTape problem (BuilderFullScheduleCursorController.bodySlotCount problem) 0
          (encodeCNFTokens problem.formula))) =
      some (finalConfiguration problem.input (canonicalOutside problem) (encodeCNFTokens problem.formula)) := by
  rw [BuilderCursorSource.cursorTape_eq_workspace]
  exact workRun_exact problem.input (canonicalOutside problem) (encodeCNFTokens problem.formula)

theorem canonical_output_eq {language : Language} (problem : VerifierTableauProblem language) :
    (encodeWorkTape (finalTape problem.input (canonicalOutside problem) (encodeCNFTokens problem.formula))).outputBits =
      problem.encodedFormula := by
  rw [output_eq, ← BuilderCanonicalOutput.outputTokens_eq_encodeCNFTokens problem]
  exact BuilderCanonicalOutput.encoded_output_eq_encodedFormula problem

theorem canonical_rawTime_le {language : Language} (problem : VerifierTableauProblem language) :
    6 * workSteps problem.input (encodeCNFTokens problem.formula) ≤
      (rawTimeBound problem.verifier).eval problem.input.length := by
  have h := rawTime_le problem.input (encodeCNFTokens problem.formula)
  have hOutput := BuilderRawInputLoop.outputTokens_length_le problem
  rw [BuilderCanonicalOutput.outputTokens_eq_encodeCNFTokens problem] at hOutput
  simp only [rawTimeBound, NatPolynomial.linear, NatPolynomial.eval]
  omega

end PNP.Concrete.CookLevin.BuilderOutputFinalizer
