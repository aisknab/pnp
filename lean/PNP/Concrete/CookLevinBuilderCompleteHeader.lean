/-
Copyright (c) 2026 PNP Labs.

Literal composition of the raw-input/first-token prefix, a structurally
compiled unary polynomial evaluator, and a finite header controller.  For a
fixed verifier problem the resulting finite work machine emits the complete
canonical unary formula-width header: exactly `FormulaWidth` copies of `T`
followed by `F`.

This is still only the answer-independent width header.  It does not run the
formula cursor, emit clauses, construct the complete encoded formula, provide
a RawRefinement or reduction, decide CNF-SAT, or establish P = NP.
-/

import PNP.Concrete.CookLevinBuilderUnaryPolynomial

namespace PNP.Concrete

namespace CookLevin

namespace BuilderCompleteHeader

open PipelineTape PipelineStateNamespace PipelineStageBridges

/-! ### Exact width parameter -/

def widthPolynomial {language : Language}
    (problem : VerifierTableauProblem language) : NatPolynomial :=
  formulaWidthPolynomial problem.verifier

def width {language : Language}
    (problem : VerifierTableauProblem language) : Nat :=
  (widthPolynomial problem).eval problem.input.length

theorem width_eq_FormulaWidth {language : Language}
    (problem : VerifierTableauProblem language) :
    width problem = problem.FormulaWidth := by
  exact problem.formulaWidthPolynomial_eval

theorem width_positive {language : Language}
    (problem : VerifierTableauProblem language) : 0 < width problem := by
  rw [width_eq_FormulaWidth]
  exact BuilderTokenAppender.formulaWidth_positive problem

/-! ### Sixteen-rule unary-root controller -/

namespace HeaderController

def startState : Nat := 0
def enterScratchState : Nat := 1
def seekEndState : Nat := 2
def consumeState : Nat := 3
def decideState : Nat := 4
def moreRewindState : Nat := 5
def doneRewindState : Nat := 6
def moreExitState : Nat := 7
def doneExitState : Nat := 8
def rejectState : Nat := 9

private def keepRule (source : Nat) (read : WorkSymbol) (target : Nat)
    (move : HeadMove) : WorkRule :=
  { sourceState := source
    readSymbol := read
    targetState := target
    writeSymbol := read
    move := move }

private def writeRule (source : Nat) (read : WorkSymbol) (target : Nat)
    (write : WorkSymbol) (move : HeadMove) : WorkRule :=
  { sourceState := source
    readSymbol := read
    targetState := target
    writeSymbol := write
    move := move }

/-- The controller consumes one unit from the far end of the root register.
It exits through `moreExitState` when another unit remains and through
`doneExitState` when the consumed unit was the last one. -/
def rules : List WorkRule :=
  [keepRule startState WorkSymbol.blank enterScratchState .left,
   keepRule startState WorkSymbol.zeroBlank enterScratchState .left,
   keepRule startState WorkSymbol.oneBlank enterScratchState .left,
   keepRule enterScratchState leftMarker seekEndState .left,
   keepRule seekEndState BuilderUnaryPolynomial.unitSymbol seekEndState .left,
   keepRule seekEndState BuilderUnaryPolynomial.separatorSymbol seekEndState
     .left,
   keepRule seekEndState BuilderUnaryPolynomial.scratchEndSymbol consumeState
     .right,
   writeRule consumeState BuilderUnaryPolynomial.unitSymbol decideState
     BuilderUnaryPolynomial.scratchEndSymbol .right,
   keepRule decideState BuilderUnaryPolynomial.unitSymbol moreRewindState
     .right,
   keepRule decideState BuilderUnaryPolynomial.separatorSymbol doneRewindState
     .right,
   keepRule moreRewindState BuilderUnaryPolynomial.unitSymbol moreRewindState
     .right,
   keepRule moreRewindState BuilderUnaryPolynomial.separatorSymbol
     moreRewindState .right,
   keepRule moreRewindState leftMarker moreExitState .right,
   keepRule doneRewindState BuilderUnaryPolynomial.unitSymbol doneRewindState
     .right,
   keepRule doneRewindState BuilderUnaryPolynomial.separatorSymbol
     doneRewindState .right,
   keepRule doneRewindState leftMarker doneExitState .right]

def machine : WorkMachine :=
  { rules := rules
    startState := startState
    acceptState := moreExitState
    rejectState := doneExitState }

theorem rules_length : rules.length = 16 := by rfl

theorem rules_pairwise_query_distinct :
    rules.Pairwise (fun left right =>
      (left.sourceState, left.readSymbol) ≠
        (right.sourceState, right.readSymbol)) := by
  decide

theorem machine_acceptState_ne_rejectState :
    machine.acceptState ≠ machine.rejectState := by decide

/-- Exterior-left shape expected by one controller invocation.  The first
argument is the scratch prefix preceding the root register; `remaining + 1`
is the positive root payload about to be decremented. -/
def outsideBefore (wordPrefix : List WorkSymbol) (remaining : Nat)
    (tail : List WorkSymbol) : List WorkSymbol :=
  wordPrefix ++ BuilderUnaryPolynomial.separatorSymbol ::
    (List.replicate remaining BuilderUnaryPolynomial.unitSymbol ++
      [BuilderUnaryPolynomial.unitSymbol]) ++
      BuilderUnaryPolynomial.scratchEndSymbol :: tail

/-- Exterior-left shape after the farthest root unit has become the new
active scratch end.  The previous end marker becomes harmless garbage. -/
def outsideAfter (wordPrefix : List WorkSymbol) (remaining : Nat)
    (tail : List WorkSymbol) : List WorkSymbol :=
  wordPrefix ++ BuilderUnaryPolynomial.separatorSymbol ::
    List.replicate remaining BuilderUnaryPolynomial.unitSymbol ++
      BuilderUnaryPolynomial.scratchEndSymbol ::
        BuilderUnaryPolynomial.scratchEndSymbol :: tail

def steps (prefixLength remaining : Nat) : Nat :=
  2 * prefixLength + 2 * remaining + 8

def initialConfiguration (input : BitString) (wordPrefix : List WorkSymbol)
    (remaining : Nat) (tail : List WorkSymbol)
    (output : List CNFToken) : WorkConfiguration :=
  { state := startState
    tape := BuilderTokenAppender.workspaceTape input
      (outsideBefore wordPrefix remaining tail) output }

def finalConfiguration (input : BitString) (wordPrefix : List WorkSymbol)
    (remaining : Nat) (tail : List WorkSymbol)
    (output : List CNFToken) : WorkConfiguration :=
  { state := if remaining = 0 then doneExitState else moreExitState
    tape := BuilderTokenAppender.workspaceTape input
      (outsideAfter wordPrefix remaining tail) output }

private def sourceWord : BitString -> List WorkSymbol
  | [] => [WorkSymbol.blank]
  | bits => bits.map (fun bit => dataSymbol (TapeSymbol.ofBool bit))

private def workspaceSuffix (input : BitString)
    (output : List CNFToken) : List WorkSymbol :=
  List.replicate input.length BuilderInputLength.tallySymbol ++
    BuilderTokenAppender.outputRegion output

private def insideWord (input : BitString)
    (output : List CNFToken) : List WorkSymbol :=
  leftMarker :: sourceWord input ++ rightMarker :: workspaceSuffix input output

private def outwardTape (tail inward : List WorkSymbol) :
    List WorkSymbol -> WorkTape
  | [] =>
      { left := tail
        head := BuilderUnaryPolynomial.scratchEndSymbol
        right := inward }
  | head :: rest =>
      { left := rest ++ BuilderUnaryPolynomial.scratchEndSymbol :: tail
        head := head
        right := inward }

private def inwardTape (leftSide : List WorkSymbol) :
    List WorkSymbol -> WorkTape
  | [] => { left := leftSide, head := leftMarker, right := [] }
  | head :: rest => { left := leftSide, head := head, right := rest }

private theorem replicate_succ_append {α : Type} (count : Nat) (item : α) :
    List.replicate (count + 1) item =
      List.replicate count item ++ [item] := by
  induction count with
  | zero => rfl
  | succ count ih =>
      change item :: List.replicate (count + 1) item =
        (item :: List.replicate count item) ++ [item]
      rw [ih]
      simp only [List.cons_append]

private theorem workRunExact_compose (machine : WorkMachine)
    (first second : Nat) (start middle final : WorkConfiguration)
    (hFirst : workRunExact? machine first start = some middle)
    (hSecond : workRunExact? machine second middle = some final) :
    workRunExact? machine (first + second) start = some final := by
  exact PipelineMachineSimulation.workRunExact?_compose machine first second
    start middle final hFirst hSecond

private theorem workRunExact_one (machine : WorkMachine)
    (start next : WorkConfiguration)
    (hStep : workStep? machine start = some next) :
    workRunExact? machine 1 start = some next := by
  change
    (match workStep? machine start with
     | none => none
     | some result => some result) = some next
  rw [hStep]

private theorem start_step (tape : WorkTape)
    (hHead : tape.head = WorkSymbol.blank \/
      tape.head = WorkSymbol.zeroBlank \/
      tape.head = WorkSymbol.oneBlank) :
    workStep? machine { state := startState, tape := tape } =
      some { state := enterScratchState, tape := tape.moveLeft } := by
  rcases hHead with hBlank | hZero | hOne
  · cases tape with
    | mk left head right =>
      dsimp at hBlank
      subst head
      rfl
  · cases tape with
    | mk left head right =>
      dsimp at hZero
      subst head
      rfl
  · cases tape with
    | mk left head right =>
      dsimp at hOne
      subst head
      rfl

private theorem enter_step (tape : WorkTape) (hHead : tape.head = leftMarker) :
    workStep? machine { state := enterScratchState, tape := tape } =
      some { state := seekEndState, tape := tape.moveLeft } := by
  cases tape with
  | mk left head right =>
    dsimp at hHead
    subst head
    rfl

private theorem enter_exact (input : BitString)
    (wordPrefix : List WorkSymbol) (remaining : Nat)
    (tail : List WorkSymbol) (output : List CNFToken) :
    workRunExact? machine 2
        (initialConfiguration input wordPrefix remaining tail output) =
      some
        { state := seekEndState
          tape := outwardTape tail (insideWord input output)
            ((wordPrefix ++ BuilderUnaryPolynomial.separatorSymbol ::
              List.replicate remaining
                BuilderUnaryPolynomial.unitSymbol) ++
              [BuilderUnaryPolynomial.unitSymbol]) } := by
  let outside := outsideBefore wordPrefix remaining tail
  let tape0 := BuilderTokenAppender.workspaceTape input outside output
  let tape1 : WorkTape :=
    { left := outside
      head := leftMarker
      right := sourceWord input ++ rightMarker :: workspaceSuffix input output }
  let tape2 := outwardTape tail (insideWord input output)
    ((wordPrefix ++ BuilderUnaryPolynomial.separatorSymbol ::
      List.replicate remaining BuilderUnaryPolynomial.unitSymbol) ++
      [BuilderUnaryPolynomial.unitSymbol])
  have hHead : tape0.head = WorkSymbol.blank \/
      tape0.head = WorkSymbol.zeroBlank \/
      tape0.head = WorkSymbol.oneBlank := by
    cases input with
    | nil =>
        exact Or.inl (by
          simp [tape0, BuilderTokenAppender.workspaceTape,
            frameWithGarbage, Tape.ofInput, Tape.blank, dataSymbol,
            WorkSymbol.blank])
    | cons first rest =>
        cases first
        · exact Or.inr (Or.inl (by
            simp [tape0, BuilderTokenAppender.workspaceTape,
              frameWithGarbage, Tape.ofInput, dataSymbol,
              TapeSymbol.ofBool, WorkSymbol.zeroBlank]))
        · exact Or.inr (Or.inr (by
            simp [tape0, BuilderTokenAppender.workspaceTape,
              frameWithGarbage, Tape.ofInput, dataSymbol,
              TapeSymbol.ofBool, WorkSymbol.oneBlank]))
  have hTape1 : tape0.moveLeft = tape1 := by
    cases input with
    | nil =>
        simp [tape0, tape1, BuilderTokenAppender.workspaceTape,
          frameWithGarbage, Tape.ofInput, Tape.blank, dataSymbol,
          sourceWord, workspaceSuffix, WorkTape.moveLeft,
          WorkSymbol.blank]
    | cons first rest =>
        cases first <;>
          simp [tape0, tape1, BuilderTokenAppender.workspaceTape,
            frameWithGarbage, Tape.ofInput, dataSymbol,
            TapeSymbol.ofBool, sourceWord, workspaceSuffix,
            WorkTape.moveLeft, Function.comp_def]
  have hFirstStep := start_step tape0 hHead
  rw [hTape1] at hFirstStep
  have hFirst := workRunExact_one machine
    { state := startState, tape := tape0 }
    { state := enterScratchState, tape := tape1 } hFirstStep
  have hTape2 : tape1.moveLeft = tape2 := by
    cases wordPrefix with
    | nil =>
        simp [tape1, tape2, outside, outsideBefore, insideWord,
          outwardTape, WorkTape.moveLeft, List.append_assoc]
    | cons first rest =>
        simp [tape1, tape2, outside, outsideBefore, insideWord,
          outwardTape, WorkTape.moveLeft, List.append_assoc]
  have hSecondStep := enter_step tape1 (by simp [tape1])
  rw [hTape2] at hSecondStep
  have hSecond := workRunExact_one machine
    { state := enterScratchState, tape := tape1 }
    { state := seekEndState, tape := tape2 } hSecondStep
  have hAll := workRunExact_compose machine 1 1
    { state := startState, tape := tape0 }
    { state := enterScratchState, tape := tape1 }
    { state := seekEndState, tape := tape2 } hFirst hSecond
  simpa [initialConfiguration, tape0, tape2] using hAll

private theorem marker_move_eq_workspace (input : BitString)
    (outside : List WorkSymbol) (output : List CNFToken) :
    ({ left := outside
       head := leftMarker
       right := sourceWord input ++
         rightMarker :: workspaceSuffix input output } : WorkTape).moveRight =
      BuilderTokenAppender.workspaceTape input outside output := by
  cases input with
  | nil =>
      simp [sourceWord, workspaceSuffix,
        BuilderTokenAppender.workspaceTape, frameWithGarbage,
        Tape.ofInput, Tape.blank, dataSymbol, WorkTape.moveRight,
        WorkSymbol.blank]
  | cons first rest =>
      cases first <;>
        simp [sourceWord, workspaceSuffix,
          BuilderTokenAppender.workspaceTape, frameWithGarbage,
          Tape.ofInput, dataSymbol, TapeSymbol.ofBool, WorkTape.moveRight,
          Function.comp_def]

private theorem more_exit_step (input : BitString)
    (outside : List WorkSymbol) (output : List CNFToken) :
    workStep? machine
        { state := moreRewindState
          tape := inwardTape outside
            (leftMarker :: sourceWord input ++
              rightMarker :: workspaceSuffix input output) } =
      some
        { state := moreExitState
          tape := BuilderTokenAppender.workspaceTape input outside output } := by
  have hStep : workStep? machine
      { state := moreRewindState
        tape :=
          { left := outside
            head := leftMarker
            right := sourceWord input ++
              rightMarker :: workspaceSuffix input output } } =
    some
      { state := moreExitState
        tape :=
          ({ left := outside
             head := leftMarker
             right := sourceWord input ++
               rightMarker :: workspaceSuffix input output } :
            WorkTape).moveRight } := by
    rfl
  simpa [inwardTape, marker_move_eq_workspace] using hStep

private theorem done_exit_step (input : BitString)
    (outside : List WorkSymbol) (output : List CNFToken) :
    workStep? machine
        { state := doneRewindState
          tape := inwardTape outside
            (leftMarker :: sourceWord input ++
              rightMarker :: workspaceSuffix input output) } =
      some
        { state := doneExitState
          tape := BuilderTokenAppender.workspaceTape input outside output } := by
  have hStep : workStep? machine
      { state := doneRewindState
        tape :=
          { left := outside
            head := leftMarker
            right := sourceWord input ++
              rightMarker :: workspaceSuffix input output } } =
    some
      { state := doneExitState
        tape :=
          ({ left := outside
             head := leftMarker
             right := sourceWord input ++
               rightMarker :: workspaceSuffix input output } :
            WorkTape).moveRight } := by
    rfl
  simpa [inwardTape, marker_move_eq_workspace] using hStep

private theorem seekEnd_end_step (tail rightSide : List WorkSymbol) :
    workStep? machine
        { state := seekEndState
          tape :=
            { left := tail
              head := BuilderUnaryPolynomial.scratchEndSymbol
              right := rightSide } } =
      some
        { state := consumeState
          tape :=
            ({ left := tail
               head := BuilderUnaryPolynomial.scratchEndSymbol
               right := rightSide } : WorkTape).moveRight } := by
  rfl

private theorem consume_unit_step (tape : WorkTape)
    (hHead : tape.head = BuilderUnaryPolynomial.unitSymbol) :
    workStep? machine { state := consumeState, tape := tape } =
      some
        { state := decideState
          tape :=
            (tape.write BuilderUnaryPolynomial.scratchEndSymbol).moveRight } := by
  cases tape with
  | mk left head right =>
    dsimp at hHead
    subst head
    rfl

private theorem decide_unit_step (tape : WorkTape)
    (hHead : tape.head = BuilderUnaryPolynomial.unitSymbol) :
    workStep? machine { state := decideState, tape := tape } =
      some { state := moreRewindState, tape := tape.moveRight } := by
  cases tape with
  | mk left head right =>
    dsimp at hHead
    subst head
    rfl

private theorem decide_separator_step (tape : WorkTape)
    (hHead : tape.head = BuilderUnaryPolynomial.separatorSymbol) :
    workStep? machine { state := decideState, tape := tape } =
      some { state := doneRewindState, tape := tape.moveRight } := by
  cases tape with
  | mk left head right =>
    dsimp at hHead
    subst head
    rfl

private def ScratchSymbol (symbol : WorkSymbol) : Prop :=
  symbol = BuilderUnaryPolynomial.unitSymbol \/
    symbol = BuilderUnaryPolynomial.separatorSymbol

private theorem seekEnd_step (tape : WorkTape)
    (hScratch : ScratchSymbol tape.head) :
    workStep? machine { state := seekEndState, tape := tape } =
      some { state := seekEndState, tape := tape.moveLeft } := by
  rcases hScratch with hUnit | hSeparator
  · cases tape with
    | mk left head right =>
      dsimp at hUnit
      subst head
      rfl
  · cases tape with
    | mk left head right =>
      dsimp at hSeparator
      subst head
      rfl

private theorem seekEnd_exact (symbols : List WorkSymbol)
    (tail inward : List WorkSymbol)
    (hScratch : ∀ symbol ∈ symbols, ScratchSymbol symbol) :
    workRunExact? machine symbols.length
        { state := seekEndState, tape := outwardTape tail inward symbols } =
      some
        { state := seekEndState
          tape := outwardTape tail (symbols.reverse ++ inward) [] } := by
  induction symbols generalizing inward with
  | nil => rfl
  | cons first rest ih =>
      have hFirst := hScratch first (List.Mem.head rest)
      have hRest : ∀ symbol ∈ rest, ScratchSymbol symbol := by
        intro symbol hMem
        exact hScratch symbol (List.Mem.tail first hMem)
      have hStep := seekEnd_step
        (outwardTape tail inward (first :: rest)) hFirst
      have hOne := workRunExact_one machine
        { state := seekEndState
          tape := outwardTape tail inward (first :: rest) }
        { state := seekEndState
          tape := outwardTape tail (first :: inward) rest }
        (by
          cases rest <;>
            simpa [outwardTape, WorkTape.moveLeft, List.append_assoc]
              using hStep)
      have hTail := ih (first :: inward) hRest
      have hAll := workRunExact_compose machine 1 rest.length
        { state := seekEndState
          tape := outwardTape tail inward (first :: rest) }
        { state := seekEndState
          tape := outwardTape tail (first :: inward) rest }
        { state := seekEndState
          tape := outwardTape tail (rest.reverse ++ first :: inward) [] }
        hOne hTail
      simpa [List.reverse_cons, List.append_assoc, Nat.add_comm] using hAll

private theorem rewind_step (state : Nat) (tape : WorkTape)
    (hState : state = moreRewindState \/ state = doneRewindState)
    (hScratch : ScratchSymbol tape.head) :
    workStep? machine { state := state, tape := tape } =
      some { state := state, tape := tape.moveRight } := by
  rcases hState with rfl | rfl
  · rcases hScratch with hUnit | hSeparator
    · cases tape with
      | mk left head right =>
        dsimp at hUnit
        subst head
        rfl
    · cases tape with
      | mk left head right =>
        dsimp at hSeparator
        subst head
        rfl
  · rcases hScratch with hUnit | hSeparator
    · cases tape with
      | mk left head right =>
        dsimp at hUnit
        subst head
        rfl
    · cases tape with
      | mk left head right =>
        dsimp at hSeparator
        subst head
        rfl

private theorem rewind_exact (state : Nat) (symbols : List WorkSymbol)
    (leftSide rightSide : List WorkSymbol)
    (hState : state = moreRewindState \/ state = doneRewindState)
    (hScratch : ∀ symbol ∈ symbols, ScratchSymbol symbol) :
    workRunExact? machine symbols.length
        { state := state
          tape := inwardTape leftSide (symbols ++ leftMarker :: rightSide) } =
      some
        { state := state
          tape := inwardTape (symbols.reverse ++ leftSide)
            (leftMarker :: rightSide) } := by
  induction symbols generalizing leftSide with
  | nil => rfl
  | cons first rest ih =>
      have hFirst := hScratch first (List.Mem.head rest)
      have hRest : ∀ symbol ∈ rest, ScratchSymbol symbol := by
        intro symbol hMem
        exact hScratch symbol (List.Mem.tail first hMem)
      have hStep := rewind_step state
        (inwardTape leftSide (first :: rest ++ leftMarker :: rightSide))
        hState hFirst
      have hOne := workRunExact_one machine
        { state := state
          tape := inwardTape leftSide
            (first :: rest ++ leftMarker :: rightSide) }
        { state := state
          tape := inwardTape (first :: leftSide)
            (rest ++ leftMarker :: rightSide) }
        (by
          cases rest <;>
            simp [inwardTape, WorkTape.moveRight] at hStep ⊢
          all_goals exact hStep)
      have hTail := ih (first :: leftSide) hRest
      have hAll := workRunExact_compose machine 1 rest.length
        { state := state
          tape := inwardTape leftSide
            (first :: rest ++ leftMarker :: rightSide) }
        { state := state
          tape := inwardTape (first :: leftSide)
            (rest ++ leftMarker :: rightSide) }
        { state := state
          tape := inwardTape (rest.reverse ++ first :: leftSide)
            (leftMarker :: rightSide) }
        hOne hTail
      simpa [List.reverse_cons, List.append_assoc, Nat.add_comm] using hAll

/-- One exact decrement of a positive unary root register. -/
theorem workRunExact (input : BitString) (wordPrefix : List WorkSymbol)
    (remaining : Nat) (tail : List WorkSymbol) (output : List CNFToken)
    (hPrefix : ∀ symbol ∈ wordPrefix, ScratchSymbol symbol) :
    workRunExact? machine (steps wordPrefix.length remaining)
        (initialConfiguration input wordPrefix remaining tail output) =
      some (finalConfiguration input wordPrefix remaining tail output) := by
  cases remaining with
  | zero =>
      let inside := insideWord input output
      let word :=
        (wordPrefix ++ [BuilderUnaryPolynomial.separatorSymbol]) ++
          [BuilderUnaryPolynomial.unitSymbol]
      let c0 := initialConfiguration input wordPrefix 0 tail output
      let c2 : WorkConfiguration :=
        { state := seekEndState
          tape := outwardTape tail inside word }
      let cEnd : WorkConfiguration :=
        { state := seekEndState
          tape := outwardTape tail (word.reverse ++ inside) [] }
      let cConsume : WorkConfiguration :=
        { state := consumeState
          tape :=
            { left := BuilderUnaryPolynomial.scratchEndSymbol :: tail
              head := BuilderUnaryPolynomial.unitSymbol
              right := BuilderUnaryPolynomial.separatorSymbol ::
                wordPrefix.reverse ++ inside } }
      let cDecide : WorkConfiguration :=
        { state := decideState
          tape :=
            { left := BuilderUnaryPolynomial.scratchEndSymbol ::
                BuilderUnaryPolynomial.scratchEndSymbol :: tail
              head := BuilderUnaryPolynomial.separatorSymbol
              right := wordPrefix.reverse ++ inside } }
      let rewindLeft := BuilderUnaryPolynomial.separatorSymbol ::
        BuilderUnaryPolynomial.scratchEndSymbol ::
          BuilderUnaryPolynomial.scratchEndSymbol :: tail
      let cRewind : WorkConfiguration :=
        { state := doneRewindState
          tape := inwardTape rewindLeft
            (wordPrefix.reverse ++ inside) }
      let cMarker : WorkConfiguration :=
        { state := doneRewindState
          tape := inwardTape (wordPrefix ++ rewindLeft) inside }
      let final := finalConfiguration input wordPrefix 0 tail output
      have hEnter : workRunExact? machine 2 c0 = some c2 := by
        simpa [c0, c2, word, inside] using
          (enter_exact input wordPrefix 0 tail output)
      have hWord : ∀ symbol ∈ word, ScratchSymbol symbol := by
        intro symbol hMem
        simp only [word, List.mem_append, List.mem_singleton] at hMem
        rcases hMem with (hPrefixMem | hSeparator) | hUnit
        · exact hPrefix symbol hPrefixMem
        · exact Or.inr hSeparator
        · exact Or.inl hUnit
      have hSeek : workRunExact? machine word.length c2 = some cEnd := by
        simpa [c2, cEnd] using seekEnd_exact word tail inside hWord
      have hEndStep := seekEnd_end_step tail
        (BuilderUnaryPolynomial.unitSymbol ::
          BuilderUnaryPolynomial.separatorSymbol ::
            wordPrefix.reverse ++ inside)
      have hEnd : workRunExact? machine 1 cEnd = some cConsume := by
        apply workRunExact_one
        simpa [cEnd, cConsume, word, outwardTape, List.reverse_append,
          List.append_assoc, WorkTape.moveRight] using hEndStep
      have hConsumeStep := consume_unit_step cConsume.tape (by
        simp [cConsume])
      have hConsume : workRunExact? machine 1 cConsume = some cDecide := by
        apply workRunExact_one
        simpa [cConsume, cDecide, WorkTape.write, WorkTape.moveRight]
          using hConsumeStep
      have hDecideStep := decide_separator_step cDecide.tape (by
        simp [cDecide])
      have hDecide : workRunExact? machine 1 cDecide = some cRewind := by
        apply workRunExact_one
        cases hReverse : wordPrefix.reverse with
        | nil =>
            simpa [cDecide, cRewind, rewindLeft, inside, insideWord,
              inwardTape, WorkTape.moveRight, hReverse] using hDecideStep
        | cons first rest =>
            simpa [cDecide, cRewind, rewindLeft, inside, insideWord,
              inwardTape, WorkTape.moveRight, hReverse] using hDecideStep
      have hPrefixReverse :
          ∀ symbol ∈ wordPrefix.reverse, ScratchSymbol symbol := by
        intro symbol hMem
        exact hPrefix symbol (List.mem_reverse.mp hMem)
      have hRewind : workRunExact? machine wordPrefix.length cRewind =
          some cMarker := by
        have hExact := rewind_exact doneRewindState wordPrefix.reverse
          rewindLeft
          (sourceWord input ++ rightMarker :: workspaceSuffix input output)
          (Or.inr rfl) hPrefixReverse
        simpa [cRewind, cMarker, inside, insideWord,
          List.reverse_reverse, List.append_assoc] using hExact
      have hExitStep := done_exit_step input
        (wordPrefix ++ rewindLeft) output
      have hExit : workRunExact? machine 1 cMarker = some final := by
        apply workRunExact_one
        simpa [cMarker, final, finalConfiguration, outsideAfter,
          rewindLeft, inside, insideWord, List.append_assoc] using hExitStep
      have h02 := workRunExact_compose machine 2 word.length
        c0 c2 cEnd hEnter hSeek
      have h03 := workRunExact_compose machine (2 + word.length) 1
        c0 cEnd cConsume h02 hEnd
      have h04 := workRunExact_compose machine (2 + word.length + 1) 1
        c0 cConsume cDecide h03 hConsume
      have h05 := workRunExact_compose machine (2 + word.length + 1 + 1) 1
        c0 cDecide cRewind h04 hDecide
      have h06 := workRunExact_compose machine
        (2 + word.length + 1 + 1 + 1) wordPrefix.length
        c0 cRewind cMarker h05 hRewind
      have h07 := workRunExact_compose machine
        (2 + word.length + 1 + 1 + 1 + wordPrefix.length) 1
        c0 cMarker final h06 hExit
      have hSteps :
          2 + word.length + 1 + 1 + 1 + wordPrefix.length + 1 =
            steps wordPrefix.length 0 := by
        simp [word, steps]
        omega
      rw [← hSteps]
      simpa [c0, final] using h07
  | succ rest =>
      let inside := insideWord input output
      let rewindWord :=
        wordPrefix ++ BuilderUnaryPolynomial.separatorSymbol ::
          List.replicate rest BuilderUnaryPolynomial.unitSymbol
      let word := rewindWord ++
        [BuilderUnaryPolynomial.unitSymbol,
          BuilderUnaryPolynomial.unitSymbol]
      let c0 := initialConfiguration input wordPrefix (rest + 1) tail output
      let c2 : WorkConfiguration :=
        { state := seekEndState
          tape := outwardTape tail inside word }
      let cEnd : WorkConfiguration :=
        { state := seekEndState
          tape := outwardTape tail (word.reverse ++ inside) [] }
      let cConsume : WorkConfiguration :=
        { state := consumeState
          tape :=
            { left := BuilderUnaryPolynomial.scratchEndSymbol :: tail
              head := BuilderUnaryPolynomial.unitSymbol
              right := BuilderUnaryPolynomial.unitSymbol ::
                rewindWord.reverse ++ inside } }
      let cDecide : WorkConfiguration :=
        { state := decideState
          tape :=
            { left := BuilderUnaryPolynomial.scratchEndSymbol ::
                BuilderUnaryPolynomial.scratchEndSymbol :: tail
              head := BuilderUnaryPolynomial.unitSymbol
              right := rewindWord.reverse ++ inside } }
      let rewindLeft := BuilderUnaryPolynomial.unitSymbol ::
        BuilderUnaryPolynomial.scratchEndSymbol ::
          BuilderUnaryPolynomial.scratchEndSymbol :: tail
      let cRewind : WorkConfiguration :=
        { state := moreRewindState
          tape := inwardTape rewindLeft (rewindWord.reverse ++ inside) }
      let cMarker : WorkConfiguration :=
        { state := moreRewindState
          tape := inwardTape (rewindWord ++ rewindLeft) inside }
      let final := finalConfiguration input wordPrefix (rest + 1) tail output
      have hEnter : workRunExact? machine 2 c0 = some c2 := by
        simpa [c0, c2, word, rewindWord, inside,
          replicate_succ_append, List.append_assoc] using
          (enter_exact input wordPrefix (rest + 1) tail output)
      have hRewindWord :
          ∀ symbol ∈ rewindWord, ScratchSymbol symbol := by
        intro symbol hMem
        simp only [rewindWord, List.mem_append, List.mem_cons,
          List.mem_replicate] at hMem
        rcases hMem with hPrefixMem | hSeparator | hUnit
        · exact hPrefix symbol hPrefixMem
        · exact Or.inr hSeparator
        · exact Or.inl hUnit.2
      have hWord : ∀ symbol ∈ word, ScratchSymbol symbol := by
        intro symbol hMem
        simp only [word, List.mem_append, List.mem_cons,
          List.not_mem_nil, or_false] at hMem
        rcases hMem with hRewindMem | hUnit | hUnit
        · exact hRewindWord symbol hRewindMem
        · exact Or.inl hUnit
        · exact Or.inl hUnit
      have hSeek : workRunExact? machine word.length c2 = some cEnd := by
        simpa [c2, cEnd] using seekEnd_exact word tail inside hWord
      have hEndStep := seekEnd_end_step tail
        (BuilderUnaryPolynomial.unitSymbol ::
          BuilderUnaryPolynomial.unitSymbol :: rewindWord.reverse ++ inside)
      have hEnd : workRunExact? machine 1 cEnd = some cConsume := by
        apply workRunExact_one
        simpa [cEnd, cConsume, word, outwardTape, List.reverse_append,
          List.append_assoc, WorkTape.moveRight] using hEndStep
      have hConsumeStep := consume_unit_step cConsume.tape (by
        simp [cConsume])
      have hConsume : workRunExact? machine 1 cConsume = some cDecide := by
        apply workRunExact_one
        simpa [cConsume, cDecide, WorkTape.write, WorkTape.moveRight]
          using hConsumeStep
      have hDecideStep := decide_unit_step cDecide.tape (by
        simp [cDecide])
      have hDecide : workRunExact? machine 1 cDecide = some cRewind := by
        apply workRunExact_one
        cases rest with
        | zero =>
            simpa [cDecide, cRewind, rewindLeft, rewindWord, inside,
              insideWord, inwardTape, WorkTape.moveRight,
              List.reverse_append] using hDecideStep
        | succ count =>
            simpa [cDecide, cRewind, rewindLeft, rewindWord, inside,
              insideWord, inwardTape, WorkTape.moveRight,
              List.reverse_append, List.append_assoc,
              replicate_succ_append] using hDecideStep
      have hRewindReverse :
          ∀ symbol ∈ rewindWord.reverse, ScratchSymbol symbol := by
        intro symbol hMem
        exact hRewindWord symbol (List.mem_reverse.mp hMem)
      have hRewind : workRunExact? machine rewindWord.length cRewind =
          some cMarker := by
        have hExact := rewind_exact moreRewindState rewindWord.reverse
          rewindLeft
          (sourceWord input ++ rightMarker :: workspaceSuffix input output)
          (Or.inl rfl) hRewindReverse
        simpa [cRewind, cMarker, inside, insideWord,
          List.reverse_reverse, List.append_assoc] using hExact
      have hExitStep := more_exit_step input
        (rewindWord ++ rewindLeft) output
      have hExit : workRunExact? machine 1 cMarker = some final := by
        apply workRunExact_one
        simpa [cMarker, final, finalConfiguration, outsideAfter,
          rewindLeft, rewindWord, inside, insideWord,
          replicate_succ_append, List.append_assoc] using hExitStep
      have h02 := workRunExact_compose machine 2 word.length
        c0 c2 cEnd hEnter hSeek
      have h03 := workRunExact_compose machine (2 + word.length) 1
        c0 cEnd cConsume h02 hEnd
      have h04 := workRunExact_compose machine (2 + word.length + 1) 1
        c0 cConsume cDecide h03 hConsume
      have h05 := workRunExact_compose machine (2 + word.length + 1 + 1) 1
        c0 cDecide cRewind h04 hDecide
      have h06 := workRunExact_compose machine
        (2 + word.length + 1 + 1 + 1) rewindWord.length
        c0 cRewind cMarker h05 hRewind
      have h07 := workRunExact_compose machine
        (2 + word.length + 1 + 1 + 1 + rewindWord.length) 1
        c0 cMarker final h06 hExit
      have hSteps :
          2 + word.length + 1 + 1 + 1 + rewindWord.length + 1 =
            steps wordPrefix.length (rest + 1) := by
        simp [word, rewindWord, steps]
        omega
      rw [← hSteps]
      simpa [c0, final] using h07

end HeaderController

/-! ### Collision-free five-component namespace and literal table -/

def prefixState (state : Nat) : Nat := 5 * state
def evaluatorState (state : Nat) : Nat := 5 * state + 1
def controllerState (state : Nat) : Nat := 5 * state + 2
def tAppenderState (state : Nat) : Nat := 5 * state + 3
def fAppenderState (state : Nat) : Nat := 5 * state + 4

theorem prefixState_injective : Function.Injective prefixState := by
  intro left right h
  simp [prefixState] at h
  omega

theorem evaluatorState_injective : Function.Injective evaluatorState := by
  intro left right h
  simp [evaluatorState] at h
  omega

theorem controllerState_injective : Function.Injective controllerState := by
  intro left right h
  simp [controllerState] at h
  omega

theorem tAppenderState_injective : Function.Injective tAppenderState := by
  intro left right h
  simp [tAppenderState] at h
  omega

theorem fAppenderState_injective : Function.Injective fAppenderState := by
  intro left right h
  simp [fAppenderState] at h
  omega

private theorem prefixState_ne_evaluatorState (left right : Nat) :
    prefixState left ≠ evaluatorState right := by
  simp [prefixState, evaluatorState]
  omega

private theorem prefixState_ne_controllerState (left right : Nat) :
    prefixState left ≠ controllerState right := by
  simp [prefixState, controllerState]
  omega

private theorem prefixState_ne_tAppenderState (left right : Nat) :
    prefixState left ≠ tAppenderState right := by
  simp [prefixState, tAppenderState]
  omega

private theorem prefixState_ne_fAppenderState (left right : Nat) :
    prefixState left ≠ fAppenderState right := by
  simp [prefixState, fAppenderState]
  omega

private theorem evaluatorState_ne_controllerState (left right : Nat) :
    evaluatorState left ≠ controllerState right := by
  simp [evaluatorState, controllerState]
  omega

private theorem evaluatorState_ne_tAppenderState (left right : Nat) :
    evaluatorState left ≠ tAppenderState right := by
  simp [evaluatorState, tAppenderState]
  omega

private theorem evaluatorState_ne_fAppenderState (left right : Nat) :
    evaluatorState left ≠ fAppenderState right := by
  simp [evaluatorState, fAppenderState]
  omega

private theorem controllerState_ne_tAppenderState (left right : Nat) :
    controllerState left ≠ tAppenderState right := by
  simp [controllerState, tAppenderState]
  omega

private theorem controllerState_ne_fAppenderState (left right : Nat) :
    controllerState left ≠ fAppenderState right := by
  simp [controllerState, fAppenderState]
  omega

private theorem tAppenderState_ne_fAppenderState (left right : Nat) :
    tAppenderState left ≠ fAppenderState right := by
  simp [tAppenderState, fAppenderState]
  omega

def prefixEvaluatorBridge {language : Language}
    (problem : VerifierTableauProblem language) : List WorkRule :=
  launchRules
    (prefixState BuilderFirstTokenPrefix.machine.acceptState)
    (evaluatorState
      (BuilderUnaryPolynomial.machine (widthPolynomial problem)).startState)

def evaluatorControllerBridge {language : Language}
    (problem : VerifierTableauProblem language) : List WorkRule :=
  launchRules
    (evaluatorState
      (BuilderUnaryPolynomial.machine (widthPolynomial problem)).acceptState)
    (controllerState HeaderController.machine.startState)

def controllerTBridge : List WorkRule :=
  launchRules (controllerState HeaderController.moreExitState)
    (tAppenderState (BuilderTokenAppender.seekInputState .t))

def tControllerBridge : List WorkRule :=
  launchRules
    (tAppenderState BuilderTokenAppender.machine.acceptState)
    (controllerState HeaderController.machine.startState)

def controllerFBridge : List WorkRule :=
  launchRules (controllerState HeaderController.doneExitState)
    (fAppenderState (BuilderTokenAppender.seekInputState .f))

def bridgeRules {language : Language}
    (problem : VerifierTableauProblem language) : List WorkRule :=
  prefixEvaluatorBridge problem ++
    (evaluatorControllerBridge problem ++
      (controllerTBridge ++ (tControllerBridge ++ controllerFBridge)))

/-- One bridge-first literal table.  The polynomial syntax is fixed by the
verifier, so this is a finite table for every concrete problem. -/
def rules {language : Language}
    (problem : VerifierTableauProblem language) : List WorkRule :=
  bridgeRules problem ++
    (BuilderFirstTokenPrefix.machine.rules.map (renameRule prefixState) ++
      ((BuilderUnaryPolynomial.machine
          (widthPolynomial problem)).rules.map (renameRule evaluatorState) ++
        (HeaderController.machine.rules.map (renameRule controllerState) ++
          (BuilderTokenAppender.machine.rules.map
              (renameRule tAppenderState) ++
            BuilderTokenAppender.machine.rules.map
              (renameRule fAppenderState)))))

/-- Only the `F`-appender copy contributes global halts. -/
def machine {language : Language}
    (problem : VerifierTableauProblem language) : WorkMachine :=
  { rules := rules problem
    startState := prefixState BuilderFirstTokenPrefix.machine.startState
    acceptState := fAppenderState BuilderTokenAppender.machine.acceptState
    rejectState := fAppenderState BuilderTokenAppender.machine.rejectState }

theorem rules_length {language : Language}
    (problem : VerifierTableauProblem language) :
    (rules problem).length =
      363 + BuilderUnaryPolynomial.ruleCount (widthPolynomial problem) := by
  have hPrefix : BuilderFirstTokenPrefix.machine.rules.length = 184 := by
    exact BuilderFirstTokenPrefix.rules_length
  have hEvaluator :
      (BuilderUnaryPolynomial.machine
        (widthPolynomial problem)).rules.length =
        BuilderUnaryPolynomial.ruleCount (widthPolynomial problem) := by
    exact BuilderUnaryPolynomial.rules_length (widthPolynomial problem)
  have hController : HeaderController.machine.rules.length = 16 := by
    exact HeaderController.rules_length
  have hAppender : BuilderTokenAppender.machine.rules.length = 59 := by
    exact BuilderTokenAppender.rules_length
  have hBridgeOne : (prefixEvaluatorBridge problem).length = 9 := by rfl
  have hBridgeTwo : (evaluatorControllerBridge problem).length = 9 := by rfl
  have hBridgeThree : controllerTBridge.length = 9 := by rfl
  have hBridgeFour : tControllerBridge.length = 9 := by rfl
  have hBridgeFive : controllerFBridge.length = 9 := by rfl
  simp only [rules, bridgeRules, List.length_append, List.length_map]
  rw [hPrefix, hEvaluator, hController, hAppender,
    hBridgeOne, hBridgeTwo, hBridgeThree, hBridgeFour, hBridgeFive]
  omega

theorem machine_acceptState_ne_rejectState {language : Language}
    (problem : VerifierTableauProblem language) :
    (machine problem).acceptState ≠ (machine problem).rejectState := by
  intro h
  exact BuilderTokenAppender.machine_acceptState_ne_rejectState
    (fAppenderState_injective h)

/-! ### Literal-table determinism audit -/

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

private theorem prefix_rule_source_ne_accept (rule : WorkRule)
    (hMem : rule ∈ BuilderFirstTokenPrefix.machine.rules) :
    rule.sourceState ≠ BuilderFirstTokenPrefix.machine.acceptState := by
  set_option maxRecDepth 10000 in
    decide +revert

private theorem controller_rule_source_ne_more (rule : WorkRule)
    (hMem : rule ∈ HeaderController.machine.rules) :
    rule.sourceState ≠ HeaderController.moreExitState := by
  decide +revert

private theorem controller_rule_source_ne_done (rule : WorkRule)
    (hMem : rule ∈ HeaderController.machine.rules) :
    rule.sourceState ≠ HeaderController.doneExitState := by
  decide +revert

private theorem appender_rule_source_ne_accept (rule : WorkRule)
    (hMem : rule ∈ BuilderTokenAppender.machine.rules) :
    rule.sourceState ≠ BuilderTokenAppender.machine.acceptState := by
  decide +revert

private def componentRules {language : Language}
    (problem : VerifierTableauProblem language) : List WorkRule :=
  BuilderFirstTokenPrefix.machine.rules.map (renameRule prefixState) ++
    ((BuilderUnaryPolynomial.machine
        (widthPolynomial problem)).rules.map (renameRule evaluatorState) ++
      (HeaderController.machine.rules.map (renameRule controllerState) ++
        (BuilderTokenAppender.machine.rules.map (renameRule tAppenderState) ++
          BuilderTokenAppender.machine.rules.map
            (renameRule fAppenderState))))

private theorem componentRules_pairwise {language : Language}
    (problem : VerifierTableauProblem language) :
    (componentRules problem).Pairwise QueryDistinct := by
  let prefixRules := BuilderFirstTokenPrefix.machine.rules.map
    (renameRule prefixState)
  let evaluatorRules :=
    (BuilderUnaryPolynomial.machine
      (widthPolynomial problem)).rules.map (renameRule evaluatorState)
  let controllerRules := HeaderController.machine.rules.map
    (renameRule controllerState)
  let tRules := BuilderTokenAppender.machine.rules.map
    (renameRule tAppenderState)
  let fRules := BuilderTokenAppender.machine.rules.map
    (renameRule fAppenderState)
  have hPrefix := renameRules_pairwise prefixState prefixState_injective
    BuilderFirstTokenPrefix.machine.rules
    BuilderFirstTokenPrefix.rules_pairwise_query_distinct
  have hEvaluator := renameRules_pairwise evaluatorState
    evaluatorState_injective
    (BuilderUnaryPolynomial.machine (widthPolynomial problem)).rules
    (BuilderUnaryPolynomial.rules_pairwise_query_distinct
      (widthPolynomial problem))
  have hController := renameRules_pairwise controllerState
    controllerState_injective HeaderController.machine.rules
    HeaderController.rules_pairwise_query_distinct
  have hT := renameRules_pairwise tAppenderState tAppenderState_injective
    BuilderTokenAppender.machine.rules
    BuilderTokenAppender.rules_pairwise_query_distinct
  have hF := renameRules_pairwise fAppenderState fAppenderState_injective
    BuilderTokenAppender.machine.rules
    BuilderTokenAppender.rules_pairwise_query_distinct
  have hPE := renamedRules_cross prefixState evaluatorState
    BuilderFirstTokenPrefix.machine.rules
    (BuilderUnaryPolynomial.machine (widthPolynomial problem)).rules
    prefixState_ne_evaluatorState
  have hPC := renamedRules_cross prefixState controllerState
    BuilderFirstTokenPrefix.machine.rules HeaderController.machine.rules
    prefixState_ne_controllerState
  have hPT := renamedRules_cross prefixState tAppenderState
    BuilderFirstTokenPrefix.machine.rules BuilderTokenAppender.machine.rules
    prefixState_ne_tAppenderState
  have hPF := renamedRules_cross prefixState fAppenderState
    BuilderFirstTokenPrefix.machine.rules BuilderTokenAppender.machine.rules
    prefixState_ne_fAppenderState
  have hEC := renamedRules_cross evaluatorState controllerState
    (BuilderUnaryPolynomial.machine (widthPolynomial problem)).rules
    HeaderController.machine.rules evaluatorState_ne_controllerState
  have hET := renamedRules_cross evaluatorState tAppenderState
    (BuilderUnaryPolynomial.machine (widthPolynomial problem)).rules
    BuilderTokenAppender.machine.rules evaluatorState_ne_tAppenderState
  have hEF := renamedRules_cross evaluatorState fAppenderState
    (BuilderUnaryPolynomial.machine (widthPolynomial problem)).rules
    BuilderTokenAppender.machine.rules evaluatorState_ne_fAppenderState
  have hCT := renamedRules_cross controllerState tAppenderState
    HeaderController.machine.rules BuilderTokenAppender.machine.rules
    controllerState_ne_tAppenderState
  have hCF := renamedRules_cross controllerState fAppenderState
    HeaderController.machine.rules BuilderTokenAppender.machine.rules
    controllerState_ne_fAppenderState
  have hTF := renamedRules_cross tAppenderState fAppenderState
    BuilderTokenAppender.machine.rules BuilderTokenAppender.machine.rules
    tAppenderState_ne_fAppenderState
  unfold componentRules
  rw [List.pairwise_append]
  refine ⟨hPrefix, ?_, ?_⟩
  · rw [List.pairwise_append]
    refine ⟨hEvaluator, ?_, ?_⟩
    · rw [List.pairwise_append]
      refine ⟨hController, ?_, ?_⟩
      · rw [List.pairwise_append]
        exact ⟨hT, hF, hTF⟩
      · intro left hLeft right hRight
        simp only [List.mem_append] at hRight
        rcases hRight with hRight | hRight
        · exact hCT left hLeft right hRight
        · exact hCF left hLeft right hRight
    · intro left hLeft right hRight
      simp only [List.mem_append] at hRight
      rcases hRight with hRight | hRight
      · exact hEC left hLeft right hRight
      · rcases hRight with hRight | hRight
        · exact hET left hLeft right hRight
        · exact hEF left hLeft right hRight
  · intro left hLeft right hRight
    simp only [List.mem_append] at hRight
    rcases hRight with hRight | hRight
    · exact hPE left hLeft right hRight
    · rcases hRight with hRight | hRight
      · exact hPC left hLeft right hRight
      · rcases hRight with hRight | hRight
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
  let b1s := prefixState BuilderFirstTokenPrefix.machine.acceptState
  let b1t := evaluatorState
    (BuilderUnaryPolynomial.machine (widthPolynomial problem)).startState
  let b2s := evaluatorState
    (BuilderUnaryPolynomial.machine (widthPolynomial problem)).acceptState
  let b2t := controllerState HeaderController.machine.startState
  let b3s := controllerState HeaderController.moreExitState
  let b3t := tAppenderState (BuilderTokenAppender.seekInputState .t)
  let b4s := tAppenderState BuilderTokenAppender.machine.acceptState
  let b4t := controllerState HeaderController.machine.startState
  let b5s := controllerState HeaderController.doneExitState
  let b5t := fAppenderState (BuilderTokenAppender.seekInputState .f)
  have h1 := launchRules_pairwise b1s b1t
  have h2 := launchRules_pairwise b2s b2t
  have h3 := launchRules_pairwise b3s b3t
  have h4 := launchRules_pairwise b4s b4t
  have h5 := launchRules_pairwise b5s b5t
  have h12 := launchRules_cross b1s b1t b2s b2t
    (prefixState_ne_evaluatorState _ _)
  have h13 := launchRules_cross b1s b1t b3s b3t
    (prefixState_ne_controllerState _ _)
  have h14 := launchRules_cross b1s b1t b4s b4t
    (prefixState_ne_tAppenderState _ _)
  have h15 := launchRules_cross b1s b1t b5s b5t
    (prefixState_ne_controllerState _ _)
  have h23 := launchRules_cross b2s b2t b3s b3t
    (evaluatorState_ne_controllerState _ _)
  have h24 := launchRules_cross b2s b2t b4s b4t
    (evaluatorState_ne_tAppenderState _ _)
  have h25 := launchRules_cross b2s b2t b5s b5t
    (evaluatorState_ne_controllerState _ _)
  have h34 := launchRules_cross b3s b3t b4s b4t
    (controllerState_ne_tAppenderState _ _)
  have h35 : b3s ≠ b5s := by
    intro h
    exact HeaderController.machine_acceptState_ne_rejectState
      (controllerState_injective h)
  have h35' := launchRules_cross b3s b3t b5s b5t h35
  have h45 := launchRules_cross b4s b4t b5s b5t
    (Ne.symm (controllerState_ne_tAppenderState _ _))
  unfold bridgeRules prefixEvaluatorBridge evaluatorControllerBridge
    controllerTBridge tControllerBridge controllerFBridge
  rw [List.pairwise_append]
  refine ⟨h1, ?_, ?_⟩
  · rw [List.pairwise_append]
    refine ⟨h2, ?_, ?_⟩
    · rw [List.pairwise_append]
      refine ⟨h3, ?_, ?_⟩
      · rw [List.pairwise_append]
        exact ⟨h4, h5, h45⟩
      · intro left hLeft right hRight
        simp only [List.mem_append] at hRight
        rcases hRight with hRight | hRight
        · exact h34 left hLeft right hRight
        · exact h35' left hLeft right hRight
    · intro left hLeft right hRight
      simp only [List.mem_append] at hRight
      rcases hRight with hRight | hRight
      · exact h23 left hLeft right hRight
      · rcases hRight with hRight | hRight
        · exact h24 left hLeft right hRight
        · exact h25 left hLeft right hRight
  · intro left hLeft right hRight
    simp only [List.mem_append] at hRight
    rcases hRight with hRight | hRight
    · exact h12 left hLeft right hRight
    · rcases hRight with hRight | hRight
      · exact h13 left hLeft right hRight
      · rcases hRight with hRight | hRight
        · exact h14 left hLeft right hRight
        · exact h15 left hLeft right hRight

private theorem bridgeOne_component_cross {language : Language}
    (problem : VerifierTableauProblem language) :
    ∀ bridge ∈ prefixEvaluatorBridge problem,
      ∀ component ∈ componentRules problem,
        QueryDistinct bridge component := by
  have hP := launchRenamed_cross
    (prefixState BuilderFirstTokenPrefix.machine.acceptState)
    (evaluatorState
      (BuilderUnaryPolynomial.machine
        (widthPolynomial problem)).startState)
    prefixState BuilderFirstTokenPrefix.machine.rules (by
      intro localRule hLocal hEqual
      exact prefix_rule_source_ne_accept localRule hLocal
        (prefixState_injective hEqual).symm)
  have hE := launchRenamed_cross
    (prefixState BuilderFirstTokenPrefix.machine.acceptState)
    (evaluatorState
      (BuilderUnaryPolynomial.machine
        (widthPolynomial problem)).startState)
    evaluatorState
    (BuilderUnaryPolynomial.machine (widthPolynomial problem)).rules (by
      intro localRule _hLocal
      exact prefixState_ne_evaluatorState _ _)
  have hC := launchRenamed_cross
    (prefixState BuilderFirstTokenPrefix.machine.acceptState)
    (evaluatorState
      (BuilderUnaryPolynomial.machine
        (widthPolynomial problem)).startState)
    controllerState HeaderController.machine.rules (by
      intro localRule _hLocal
      exact prefixState_ne_controllerState _ _)
  have hT := launchRenamed_cross
    (prefixState BuilderFirstTokenPrefix.machine.acceptState)
    (evaluatorState
      (BuilderUnaryPolynomial.machine
        (widthPolynomial problem)).startState)
    tAppenderState BuilderTokenAppender.machine.rules (by
      intro localRule _hLocal
      exact prefixState_ne_tAppenderState _ _)
  have hF := launchRenamed_cross
    (prefixState BuilderFirstTokenPrefix.machine.acceptState)
    (evaluatorState
      (BuilderUnaryPolynomial.machine
        (widthPolynomial problem)).startState)
    fAppenderState BuilderTokenAppender.machine.rules (by
      intro localRule _hLocal
      exact prefixState_ne_fAppenderState _ _)
  intro bridge hBridge component hComponent
  simp only [componentRules, List.mem_append] at hComponent
  rcases hComponent with hComponent | hComponent | hComponent |
    hComponent | hComponent
  · exact hP bridge hBridge component hComponent
  · exact hE bridge hBridge component hComponent
  · exact hC bridge hBridge component hComponent
  · exact hT bridge hBridge component hComponent
  · exact hF bridge hBridge component hComponent

private theorem bridgeTwo_component_cross {language : Language}
    (problem : VerifierTableauProblem language) :
    ∀ bridge ∈ evaluatorControllerBridge problem,
      ∀ component ∈ componentRules problem,
        QueryDistinct bridge component := by
  let evaluator := BuilderUnaryPolynomial.machine (widthPolynomial problem)
  have hP := launchRenamed_cross
    (evaluatorState evaluator.acceptState)
    (controllerState HeaderController.machine.startState) prefixState
    BuilderFirstTokenPrefix.machine.rules (by
      intro localRule _hLocal
      exact Ne.symm (prefixState_ne_evaluatorState _ _))
  have hE := launchRenamed_cross
    (evaluatorState evaluator.acceptState)
    (controllerState HeaderController.machine.startState) evaluatorState
    evaluator.rules (by
      intro localRule hLocal hEqual
      have hState := evaluatorState_injective hEqual
      have hLt := BuilderUnaryPolynomial.rule_source_lt_acceptState
        (widthPolynomial problem) localRule hLocal
      change localRule.sourceState < evaluator.acceptState at hLt
      omega)
  have hC := launchRenamed_cross
    (evaluatorState evaluator.acceptState)
    (controllerState HeaderController.machine.startState) controllerState
    HeaderController.machine.rules (by
      intro localRule _hLocal
      exact evaluatorState_ne_controllerState _ _)
  have hT := launchRenamed_cross
    (evaluatorState evaluator.acceptState)
    (controllerState HeaderController.machine.startState) tAppenderState
    BuilderTokenAppender.machine.rules (by
      intro localRule _hLocal
      exact evaluatorState_ne_tAppenderState _ _)
  have hF := launchRenamed_cross
    (evaluatorState evaluator.acceptState)
    (controllerState HeaderController.machine.startState) fAppenderState
    BuilderTokenAppender.machine.rules (by
      intro localRule _hLocal
      exact evaluatorState_ne_fAppenderState _ _)
  intro bridge hBridge component hComponent
  simp only [componentRules, List.mem_append] at hComponent
  rcases hComponent with hComponent | hComponent | hComponent |
    hComponent | hComponent
  · exact hP bridge hBridge component hComponent
  · exact hE bridge hBridge component hComponent
  · exact hC bridge hBridge component hComponent
  · exact hT bridge hBridge component hComponent
  · exact hF bridge hBridge component hComponent

private theorem bridgeThree_component_cross {language : Language}
    (problem : VerifierTableauProblem language) :
    ∀ bridge ∈ controllerTBridge,
      ∀ component ∈ componentRules problem,
        QueryDistinct bridge component := by
  have hP := launchRenamed_cross
    (controllerState HeaderController.moreExitState)
    (tAppenderState (BuilderTokenAppender.seekInputState .t)) prefixState
    BuilderFirstTokenPrefix.machine.rules (by
      intro localRule _hLocal
      exact Ne.symm (prefixState_ne_controllerState _ _))
  have hE := launchRenamed_cross
    (controllerState HeaderController.moreExitState)
    (tAppenderState (BuilderTokenAppender.seekInputState .t)) evaluatorState
    (BuilderUnaryPolynomial.machine (widthPolynomial problem)).rules (by
      intro localRule _hLocal
      exact Ne.symm (evaluatorState_ne_controllerState _ _))
  have hC := launchRenamed_cross
    (controllerState HeaderController.moreExitState)
    (tAppenderState (BuilderTokenAppender.seekInputState .t)) controllerState
    HeaderController.machine.rules (by
      intro localRule hLocal hEqual
      exact controller_rule_source_ne_more localRule hLocal
        (controllerState_injective hEqual).symm)
  have hT := launchRenamed_cross
    (controllerState HeaderController.moreExitState)
    (tAppenderState (BuilderTokenAppender.seekInputState .t)) tAppenderState
    BuilderTokenAppender.machine.rules (by
      intro localRule _hLocal
      exact controllerState_ne_tAppenderState _ _)
  have hF := launchRenamed_cross
    (controllerState HeaderController.moreExitState)
    (tAppenderState (BuilderTokenAppender.seekInputState .t)) fAppenderState
    BuilderTokenAppender.machine.rules (by
      intro localRule _hLocal
      exact controllerState_ne_fAppenderState _ _)
  intro bridge hBridge component hComponent
  simp only [componentRules, List.mem_append] at hComponent
  rcases hComponent with hComponent | hComponent | hComponent |
    hComponent | hComponent
  · exact hP bridge hBridge component hComponent
  · exact hE bridge hBridge component hComponent
  · exact hC bridge hBridge component hComponent
  · exact hT bridge hBridge component hComponent
  · exact hF bridge hBridge component hComponent

private theorem bridgeFour_component_cross {language : Language}
    (problem : VerifierTableauProblem language) :
    ∀ bridge ∈ tControllerBridge,
      ∀ component ∈ componentRules problem,
        QueryDistinct bridge component := by
  have hP := launchRenamed_cross
    (tAppenderState BuilderTokenAppender.machine.acceptState)
    (controllerState HeaderController.machine.startState) prefixState
    BuilderFirstTokenPrefix.machine.rules (by
      intro localRule _hLocal
      exact Ne.symm (prefixState_ne_tAppenderState _ _))
  have hE := launchRenamed_cross
    (tAppenderState BuilderTokenAppender.machine.acceptState)
    (controllerState HeaderController.machine.startState) evaluatorState
    (BuilderUnaryPolynomial.machine (widthPolynomial problem)).rules (by
      intro localRule _hLocal
      exact Ne.symm (evaluatorState_ne_tAppenderState _ _))
  have hC := launchRenamed_cross
    (tAppenderState BuilderTokenAppender.machine.acceptState)
    (controllerState HeaderController.machine.startState) controllerState
    HeaderController.machine.rules (by
      intro localRule _hLocal
      exact Ne.symm (controllerState_ne_tAppenderState _ _))
  have hT := launchRenamed_cross
    (tAppenderState BuilderTokenAppender.machine.acceptState)
    (controllerState HeaderController.machine.startState) tAppenderState
    BuilderTokenAppender.machine.rules (by
      intro localRule hLocal hEqual
      exact appender_rule_source_ne_accept localRule hLocal
        (tAppenderState_injective hEqual).symm)
  have hF := launchRenamed_cross
    (tAppenderState BuilderTokenAppender.machine.acceptState)
    (controllerState HeaderController.machine.startState) fAppenderState
    BuilderTokenAppender.machine.rules (by
      intro localRule _hLocal
      exact tAppenderState_ne_fAppenderState _ _)
  intro bridge hBridge component hComponent
  simp only [componentRules, List.mem_append] at hComponent
  rcases hComponent with hComponent | hComponent | hComponent |
    hComponent | hComponent
  · exact hP bridge hBridge component hComponent
  · exact hE bridge hBridge component hComponent
  · exact hC bridge hBridge component hComponent
  · exact hT bridge hBridge component hComponent
  · exact hF bridge hBridge component hComponent

private theorem bridgeFive_component_cross {language : Language}
    (problem : VerifierTableauProblem language) :
    ∀ bridge ∈ controllerFBridge,
      ∀ component ∈ componentRules problem,
        QueryDistinct bridge component := by
  have hP := launchRenamed_cross
    (controllerState HeaderController.doneExitState)
    (fAppenderState (BuilderTokenAppender.seekInputState .f)) prefixState
    BuilderFirstTokenPrefix.machine.rules (by
      intro localRule _hLocal
      exact Ne.symm (prefixState_ne_controllerState _ _))
  have hE := launchRenamed_cross
    (controllerState HeaderController.doneExitState)
    (fAppenderState (BuilderTokenAppender.seekInputState .f)) evaluatorState
    (BuilderUnaryPolynomial.machine (widthPolynomial problem)).rules (by
      intro localRule _hLocal
      exact Ne.symm (evaluatorState_ne_controllerState _ _))
  have hC := launchRenamed_cross
    (controllerState HeaderController.doneExitState)
    (fAppenderState (BuilderTokenAppender.seekInputState .f)) controllerState
    HeaderController.machine.rules (by
      intro localRule hLocal hEqual
      exact controller_rule_source_ne_done localRule hLocal
        (controllerState_injective hEqual).symm)
  have hT := launchRenamed_cross
    (controllerState HeaderController.doneExitState)
    (fAppenderState (BuilderTokenAppender.seekInputState .f)) tAppenderState
    BuilderTokenAppender.machine.rules (by
      intro localRule _hLocal
      exact controllerState_ne_tAppenderState _ _)
  have hF := launchRenamed_cross
    (controllerState HeaderController.doneExitState)
    (fAppenderState (BuilderTokenAppender.seekInputState .f)) fAppenderState
    BuilderTokenAppender.machine.rules (by
      intro localRule _hLocal
      exact controllerState_ne_fAppenderState _ _)
  intro bridge hBridge component hComponent
  simp only [componentRules, List.mem_append] at hComponent
  rcases hComponent with hComponent | hComponent | hComponent |
    hComponent | hComponent
  · exact hP bridge hBridge component hComponent
  · exact hE bridge hBridge component hComponent
  · exact hC bridge hBridge component hComponent
  · exact hT bridge hBridge component hComponent
  · exact hF bridge hBridge component hComponent

private theorem bridgeRules_componentRules_cross {language : Language}
    (problem : VerifierTableauProblem language) :
    ∀ bridge ∈ bridgeRules problem,
      ∀ component ∈ componentRules problem,
        QueryDistinct bridge component := by
  intro bridge hBridge component hComponent
  simp only [bridgeRules, List.mem_append] at hBridge
  rcases hBridge with hBridge | hBridge | hBridge | hBridge | hBridge
  · exact bridgeOne_component_cross problem bridge hBridge component hComponent
  · exact bridgeTwo_component_cross problem bridge hBridge component hComponent
  · exact bridgeThree_component_cross problem bridge hBridge component hComponent
  · exact bridgeFour_component_cross problem bridge hBridge component hComponent
  · exact bridgeFive_component_cross problem bridge hBridge component hComponent

theorem rules_pairwise_query_distinct {language : Language}
    (problem : VerifierTableauProblem language) :
    (rules problem).Pairwise (fun left right =>
      (left.sourceState, left.readSymbol) ≠
        (right.sourceState, right.readSymbol)) := by
  change (rules problem).Pairwise QueryDistinct
  have hBridges := bridgeRules_pairwise problem
  have hComponents := componentRules_pairwise problem
  have hCross := bridgeRules_componentRules_cross problem
  have hRules : rules problem = bridgeRules problem ++ componentRules problem :=
    rfl
  rw [hRules, List.pairwise_append]
  exact ⟨hBridges, hComponents, hCross⟩

/-! ### Halt separation and first-match lookup isolation -/

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
  cases hAccept : (source.rejectState == source.acceptState) <;>
    rw [hAccept, hRefl] at hHalted <;> contradiction

private theorem machine_isHalted_prefix_false {language : Language}
    (problem : VerifierTableauProblem language)
    (config : WorkConfiguration) :
    (machine problem).isHalted (renameConfiguration prefixState config) =
      false := by
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

private theorem machine_isHalted_controller_false {language : Language}
    (problem : VerifierTableauProblem language)
    (config : WorkConfiguration) :
    (machine problem).isHalted
        (renameConfiguration controllerState config) = false := by
  unfold WorkMachine.isHalted machine renameConfiguration
  rw [nat_beq_false_of_ne _ _
      (controllerState_ne_fAppenderState config.state
        BuilderTokenAppender.machine.acceptState),
    nat_beq_false_of_ne _ _
      (controllerState_ne_fAppenderState config.state
        BuilderTokenAppender.machine.rejectState)]
  rfl

private theorem machine_isHalted_tAppender_false {language : Language}
    (problem : VerifierTableauProblem language)
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

private theorem findWorkRule_bridgeRules_none {language : Language}
    (problem : VerifierTableauProblem language) (state : Nat)
    (symbol : WorkSymbol)
    (hOne : prefixState BuilderFirstTokenPrefix.machine.acceptState ≠ state)
    (hTwo : evaluatorState
      (BuilderUnaryPolynomial.machine
        (widthPolynomial problem)).acceptState ≠ state)
    (hThree : controllerState HeaderController.moreExitState ≠ state)
    (hFour : tAppenderState BuilderTokenAppender.machine.acceptState ≠ state)
    (hFive : controllerState HeaderController.doneExitState ≠ state) :
    findWorkRule (bridgeRules problem) state symbol = none := by
  have h1 := findWorkRule_launchRules_none_of_source_ne
    (prefixState BuilderFirstTokenPrefix.machine.acceptState)
    (evaluatorState
      (BuilderUnaryPolynomial.machine
        (widthPolynomial problem)).startState) state symbol hOne
  have h2 := findWorkRule_launchRules_none_of_source_ne
    (evaluatorState
      (BuilderUnaryPolynomial.machine
        (widthPolynomial problem)).acceptState)
    (controllerState HeaderController.machine.startState) state symbol hTwo
  have h3 := findWorkRule_launchRules_none_of_source_ne
    (controllerState HeaderController.moreExitState)
    (tAppenderState (BuilderTokenAppender.seekInputState .t)) state symbol hThree
  have h4 := findWorkRule_launchRules_none_of_source_ne
    (tAppenderState BuilderTokenAppender.machine.acceptState)
    (controllerState HeaderController.machine.startState) state symbol hFour
  have h5 := findWorkRule_launchRules_none_of_source_ne
    (controllerState HeaderController.doneExitState)
    (fAppenderState (BuilderTokenAppender.seekInputState .f)) state symbol hFive
  unfold bridgeRules prefixEvaluatorBridge evaluatorControllerBridge
    controllerTBridge tControllerBridge controllerFBridge
  rw [findWorkRule_append_of_none _ _ _ _ h1,
    findWorkRule_append_of_none _ _ _ _ h2,
    findWorkRule_append_of_none _ _ _ _ h3,
    findWorkRule_append_of_none _ _ _ _ h4]
  exact h5

theorem findWorkRule_prefix_of_some {language : Language}
    (problem : VerifierTableauProblem language)
    (state : Nat) (symbol : WorkSymbol) (rule : WorkRule)
    (hAccept : state ≠ BuilderFirstTokenPrefix.machine.acceptState)
    (hFind : findWorkRule BuilderFirstTokenPrefix.machine.rules state symbol =
      some rule) :
    findWorkRule (machine problem).rules (prefixState state) symbol =
      some (renameRule prefixState rule) := by
  have hBridge := findWorkRule_bridgeRules_none problem (prefixState state)
    symbol
    (by intro h; exact hAccept (prefixState_injective h).symm)
    (by exact Ne.symm (prefixState_ne_evaluatorState _ _))
    (by exact Ne.symm (prefixState_ne_controllerState _ _))
    (by exact Ne.symm (prefixState_ne_tAppenderState _ _))
    (by exact Ne.symm (prefixState_ne_controllerState _ _))
  have hRenamed := findWorkRule_rename prefixState prefixState_injective
    BuilderFirstTokenPrefix.machine.rules state symbol
  rw [hFind] at hRenamed
  change findWorkRule (rules problem) (prefixState state) symbol = _
  unfold rules
  rw [findWorkRule_append_of_none _ _ _ _ hBridge]
  exact findWorkRule_append_of_some _ _ _ _ _ (by simpa using hRenamed)

theorem findWorkRule_evaluator_of_some {language : Language}
    (problem : VerifierTableauProblem language)
    (state : Nat) (symbol : WorkSymbol) (rule : WorkRule)
    (hAccept : state ≠
      (BuilderUnaryPolynomial.machine
        (widthPolynomial problem)).acceptState)
    (hFind : findWorkRule
      (BuilderUnaryPolynomial.machine (widthPolynomial problem)).rules
        state symbol = some rule) :
    findWorkRule (machine problem).rules (evaluatorState state) symbol =
      some (renameRule evaluatorState rule) := by
  have hBridge := findWorkRule_bridgeRules_none problem
    (evaluatorState state) symbol
    (by exact fun h => prefixState_ne_evaluatorState _ _ h)
    (by intro h; exact hAccept (evaluatorState_injective h).symm)
    (by exact Ne.symm (evaluatorState_ne_controllerState _ _))
    (by exact Ne.symm (evaluatorState_ne_tAppenderState _ _))
    (by exact Ne.symm (evaluatorState_ne_controllerState _ _))
  have hPrefix : findWorkRule
      (BuilderFirstTokenPrefix.machine.rules.map (renameRule prefixState))
      (evaluatorState state) symbol = none := by
    apply findWorkRule_renamedRules_none
    intro source
    exact prefixState_ne_evaluatorState source state
  have hRenamed := findWorkRule_rename evaluatorState evaluatorState_injective
    (BuilderUnaryPolynomial.machine (widthPolynomial problem)).rules
    state symbol
  rw [hFind] at hRenamed
  change findWorkRule (rules problem) (evaluatorState state) symbol = _
  unfold rules
  rw [findWorkRule_append_of_none _ _ _ _ hBridge,
    findWorkRule_append_of_none _ _ _ _ hPrefix]
  exact findWorkRule_append_of_some _ _ _ _ _ (by simpa using hRenamed)

theorem findWorkRule_controller_of_some {language : Language}
    (problem : VerifierTableauProblem language)
    (state : Nat) (symbol : WorkSymbol) (rule : WorkRule)
    (hMore : state ≠ HeaderController.moreExitState)
    (hDone : state ≠ HeaderController.doneExitState)
    (hFind : findWorkRule HeaderController.machine.rules state symbol =
      some rule) :
    findWorkRule (machine problem).rules (controllerState state) symbol =
      some (renameRule controllerState rule) := by
  have hBridge := findWorkRule_bridgeRules_none problem
    (controllerState state) symbol
    (prefixState_ne_controllerState _ _)
    (evaluatorState_ne_controllerState _ _)
    (by intro h; exact hMore (controllerState_injective h).symm)
    (Ne.symm (controllerState_ne_tAppenderState _ _))
    (by intro h; exact hDone (controllerState_injective h).symm)
  have hPrefix : findWorkRule
      (BuilderFirstTokenPrefix.machine.rules.map (renameRule prefixState))
      (controllerState state) symbol = none := by
    apply findWorkRule_renamedRules_none
    intro source
    exact prefixState_ne_controllerState source state
  have hEvaluator : findWorkRule
      ((BuilderUnaryPolynomial.machine
        (widthPolynomial problem)).rules.map (renameRule evaluatorState))
      (controllerState state) symbol = none := by
    apply findWorkRule_renamedRules_none
    intro source
    exact evaluatorState_ne_controllerState source state
  have hRenamed := findWorkRule_rename controllerState
    controllerState_injective HeaderController.machine.rules state symbol
  rw [hFind] at hRenamed
  change findWorkRule (rules problem) (controllerState state) symbol = _
  unfold rules
  rw [findWorkRule_append_of_none _ _ _ _ hBridge,
    findWorkRule_append_of_none _ _ _ _ hPrefix,
    findWorkRule_append_of_none _ _ _ _ hEvaluator]
  exact findWorkRule_append_of_some _ _ _ _ _ (by simpa using hRenamed)

theorem findWorkRule_tAppender_of_some {language : Language}
    (problem : VerifierTableauProblem language)
    (state : Nat) (symbol : WorkSymbol) (rule : WorkRule)
    (hAccept : state ≠ BuilderTokenAppender.machine.acceptState)
    (hFind : findWorkRule BuilderTokenAppender.machine.rules state symbol =
      some rule) :
    findWorkRule (machine problem).rules (tAppenderState state) symbol =
      some (renameRule tAppenderState rule) := by
  have hBridge := findWorkRule_bridgeRules_none problem
    (tAppenderState state) symbol
    (prefixState_ne_tAppenderState _ _)
    (evaluatorState_ne_tAppenderState _ _)
    (controllerState_ne_tAppenderState _ _)
    (by intro h; exact hAccept (tAppenderState_injective h).symm)
    (controllerState_ne_tAppenderState _ _)
  have hPrefix : findWorkRule
      (BuilderFirstTokenPrefix.machine.rules.map (renameRule prefixState))
      (tAppenderState state) symbol = none := by
    apply findWorkRule_renamedRules_none
    intro source
    exact prefixState_ne_tAppenderState source state
  have hEvaluator : findWorkRule
      ((BuilderUnaryPolynomial.machine
        (widthPolynomial problem)).rules.map (renameRule evaluatorState))
      (tAppenderState state) symbol = none := by
    apply findWorkRule_renamedRules_none
    intro source
    exact evaluatorState_ne_tAppenderState source state
  have hController : findWorkRule
      (HeaderController.machine.rules.map (renameRule controllerState))
      (tAppenderState state) symbol = none := by
    apply findWorkRule_renamedRules_none
    intro source
    exact controllerState_ne_tAppenderState source state
  have hRenamed := findWorkRule_rename tAppenderState
    tAppenderState_injective BuilderTokenAppender.machine.rules state symbol
  rw [hFind] at hRenamed
  change findWorkRule (rules problem) (tAppenderState state) symbol = _
  unfold rules
  rw [findWorkRule_append_of_none _ _ _ _ hBridge,
    findWorkRule_append_of_none _ _ _ _ hPrefix,
    findWorkRule_append_of_none _ _ _ _ hEvaluator,
    findWorkRule_append_of_none _ _ _ _ hController]
  exact findWorkRule_append_of_some _ _ _ _ _ (by simpa using hRenamed)

theorem findWorkRule_fAppender_of_some {language : Language}
    (problem : VerifierTableauProblem language)
    (state : Nat) (symbol : WorkSymbol) (rule : WorkRule)
    (hFind : findWorkRule BuilderTokenAppender.machine.rules state symbol =
      some rule) :
    findWorkRule (machine problem).rules (fAppenderState state) symbol =
      some (renameRule fAppenderState rule) := by
  have hBridge := findWorkRule_bridgeRules_none problem
    (fAppenderState state) symbol
    (prefixState_ne_fAppenderState _ _)
    (evaluatorState_ne_fAppenderState _ _)
    (controllerState_ne_fAppenderState _ _)
    (tAppenderState_ne_fAppenderState _ _)
    (controllerState_ne_fAppenderState _ _)
  have hPrefix : findWorkRule
      (BuilderFirstTokenPrefix.machine.rules.map (renameRule prefixState))
      (fAppenderState state) symbol = none := by
    apply findWorkRule_renamedRules_none
    intro source
    exact prefixState_ne_fAppenderState source state
  have hEvaluator : findWorkRule
      ((BuilderUnaryPolynomial.machine
        (widthPolynomial problem)).rules.map (renameRule evaluatorState))
      (fAppenderState state) symbol = none := by
    apply findWorkRule_renamedRules_none
    intro source
    exact evaluatorState_ne_fAppenderState source state
  have hController : findWorkRule
      (HeaderController.machine.rules.map (renameRule controllerState))
      (fAppenderState state) symbol = none := by
    apply findWorkRule_renamedRules_none
    intro source
    exact controllerState_ne_fAppenderState source state
  have hTAppender : findWorkRule
      (BuilderTokenAppender.machine.rules.map (renameRule tAppenderState))
      (fAppenderState state) symbol = none := by
    apply findWorkRule_renamedRules_none
    intro source
    exact tAppenderState_ne_fAppenderState source state
  have hRenamed := findWorkRule_rename fAppenderState
    fAppenderState_injective BuilderTokenAppender.machine.rules state symbol
  rw [hFind] at hRenamed
  change findWorkRule (rules problem) (fAppenderState state) symbol = _
  unfold rules
  rw [findWorkRule_append_of_none _ _ _ _ hBridge,
    findWorkRule_append_of_none _ _ _ _ hPrefix,
    findWorkRule_append_of_none _ _ _ _ hEvaluator,
    findWorkRule_append_of_none _ _ _ _ hController,
    findWorkRule_append_of_none _ _ _ _ hTAppender]
  simpa using hRenamed

private theorem prefix_workStep_of_some {language : Language}
    (problem : VerifierTableauProblem language)
    (config next : WorkConfiguration)
    (hStep : workStep? BuilderFirstTokenPrefix.machine config = some next) :
    workStep? (machine problem) (renameConfiguration prefixState config) =
      some (renameConfiguration prefixState next) := by
  rcases workStep?_some_exists BuilderFirstTokenPrefix.machine config next
      hStep with ⟨rule, hHalted, hFind, hNext⟩
  have hAccept := state_ne_accept_of_not_halted
    BuilderFirstTokenPrefix.machine config hHalted
  have hGlobalFind := findWorkRule_prefix_of_some problem config.state
    config.tape.head rule hAccept hFind
  have hGlobalStep := workStep?_eq_apply_of_find (machine problem)
    (renameConfiguration prefixState config) (renameRule prefixState rule)
    (machine_isHalted_prefix_false problem config) hGlobalFind
  calc
    workStep? (machine problem) (renameConfiguration prefixState config) =
        some (applyWorkRule (renameRule prefixState rule)
          (renameConfiguration prefixState config)) := hGlobalStep
    _ = some (renameConfiguration prefixState (applyWorkRule rule config)) :=
      congrArg Option.some (applyWorkRule_rename prefixState rule config)
    _ = some (renameConfiguration prefixState next) :=
      congrArg (fun value => some (renameConfiguration prefixState value))
        hNext.symm

private theorem evaluator_workStep_of_some {language : Language}
    (problem : VerifierTableauProblem language)
    (config next : WorkConfiguration)
    (hStep : workStep?
      (BuilderUnaryPolynomial.machine (widthPolynomial problem)) config =
        some next) :
    workStep? (machine problem) (renameConfiguration evaluatorState config) =
      some (renameConfiguration evaluatorState next) := by
  rcases workStep?_some_exists
      (BuilderUnaryPolynomial.machine (widthPolynomial problem)) config next
      hStep with ⟨rule, hHalted, hFind, hNext⟩
  have hAccept := state_ne_accept_of_not_halted
    (BuilderUnaryPolynomial.machine (widthPolynomial problem)) config hHalted
  have hGlobalFind := findWorkRule_evaluator_of_some problem config.state
    config.tape.head rule hAccept hFind
  have hGlobalStep := workStep?_eq_apply_of_find (machine problem)
    (renameConfiguration evaluatorState config)
    (renameRule evaluatorState rule)
    (machine_isHalted_evaluator_false problem config) hGlobalFind
  calc
    workStep? (machine problem) (renameConfiguration evaluatorState config) =
        some (applyWorkRule (renameRule evaluatorState rule)
          (renameConfiguration evaluatorState config)) := hGlobalStep
    _ = some (renameConfiguration evaluatorState (applyWorkRule rule config)) :=
      congrArg Option.some (applyWorkRule_rename evaluatorState rule config)
    _ = some (renameConfiguration evaluatorState next) :=
      congrArg (fun value => some (renameConfiguration evaluatorState value))
        hNext.symm

private theorem controller_workStep_of_some {language : Language}
    (problem : VerifierTableauProblem language)
    (config next : WorkConfiguration)
    (hStep : workStep? HeaderController.machine config = some next) :
    workStep? (machine problem) (renameConfiguration controllerState config) =
      some (renameConfiguration controllerState next) := by
  rcases workStep?_some_exists HeaderController.machine config next hStep with
    ⟨rule, hHalted, hFind, hNext⟩
  have hMore := state_ne_accept_of_not_halted
    HeaderController.machine config hHalted
  have hDone := state_ne_reject_of_not_halted
    HeaderController.machine config hHalted
  have hGlobalFind := findWorkRule_controller_of_some problem config.state
    config.tape.head rule hMore hDone hFind
  have hGlobalStep := workStep?_eq_apply_of_find (machine problem)
    (renameConfiguration controllerState config)
    (renameRule controllerState rule)
    (machine_isHalted_controller_false problem config) hGlobalFind
  calc
    workStep? (machine problem) (renameConfiguration controllerState config) =
        some (applyWorkRule (renameRule controllerState rule)
          (renameConfiguration controllerState config)) := hGlobalStep
    _ = some (renameConfiguration controllerState (applyWorkRule rule config)) :=
      congrArg Option.some (applyWorkRule_rename controllerState rule config)
    _ = some (renameConfiguration controllerState next) :=
      congrArg (fun value => some (renameConfiguration controllerState value))
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
  have hGlobalFind := findWorkRule_tAppender_of_some problem config.state
    config.tape.head rule hAccept hFind
  have hGlobalStep := workStep?_eq_apply_of_find (machine problem)
    (renameConfiguration tAppenderState config)
    (renameRule tAppenderState rule)
    (machine_isHalted_tAppender_false problem config) hGlobalFind
  calc
    workStep? (machine problem) (renameConfiguration tAppenderState config) =
        some (applyWorkRule (renameRule tAppenderState rule)
          (renameConfiguration tAppenderState config)) := hGlobalStep
    _ = some (renameConfiguration tAppenderState (applyWorkRule rule config)) :=
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
  have hGlobalFind := findWorkRule_fAppender_of_some problem config.state
    config.tape.head rule hFind
  have hGlobalStep := workStep?_eq_apply_of_find (machine problem)
    (renameConfiguration fAppenderState config)
    (renameRule fAppenderState rule)
    (machine_isHalted_fAppender_false_of_local problem config hHalted)
    hGlobalFind
  calc
    workStep? (machine problem) (renameConfiguration fAppenderState config) =
        some (applyWorkRule (renameRule fAppenderState rule)
          (renameConfiguration fAppenderState config)) := hGlobalStep
    _ = some (renameConfiguration fAppenderState (applyWorkRule rule config)) :=
      congrArg Option.some (applyWorkRule_rename fAppenderState rule config)
    _ = some (renameConfiguration fAppenderState next) :=
      congrArg (fun value => some (renameConfiguration fAppenderState value))
        hNext.symm

private theorem find_prefixEvaluatorBridge {language : Language}
    (problem : VerifierTableauProblem language) (symbol : WorkSymbol) :
    findWorkRule (bridgeRules problem)
        (prefixState BuilderFirstTokenPrefix.machine.acceptState) symbol =
      some (launchRule
        (prefixState BuilderFirstTokenPrefix.machine.acceptState)
        (evaluatorState
          (BuilderUnaryPolynomial.machine
            (widthPolynomial problem)).startState) symbol) := by
  have hLaunch := findWorkRule_launchRules
    (prefixState BuilderFirstTokenPrefix.machine.acceptState)
    (evaluatorState
      (BuilderUnaryPolynomial.machine
        (widthPolynomial problem)).startState) symbol
  unfold bridgeRules prefixEvaluatorBridge
  exact findWorkRule_append_of_some _ _ _ _ _ hLaunch

private theorem find_evaluatorControllerBridge {language : Language}
    (problem : VerifierTableauProblem language) (symbol : WorkSymbol) :
    findWorkRule (bridgeRules problem)
        (evaluatorState
          (BuilderUnaryPolynomial.machine
            (widthPolynomial problem)).acceptState) symbol =
      some (launchRule
        (evaluatorState
          (BuilderUnaryPolynomial.machine
            (widthPolynomial problem)).acceptState)
        (controllerState HeaderController.machine.startState) symbol) := by
  have hFirst := findWorkRule_launchRules_none_of_source_ne
    (prefixState BuilderFirstTokenPrefix.machine.acceptState)
    (evaluatorState
      (BuilderUnaryPolynomial.machine
        (widthPolynomial problem)).startState)
    (evaluatorState
      (BuilderUnaryPolynomial.machine
        (widthPolynomial problem)).acceptState) symbol
    (prefixState_ne_evaluatorState _ _)
  have hLaunch := findWorkRule_launchRules
    (evaluatorState
      (BuilderUnaryPolynomial.machine
        (widthPolynomial problem)).acceptState)
    (controllerState HeaderController.machine.startState) symbol
  unfold bridgeRules prefixEvaluatorBridge evaluatorControllerBridge
  rw [findWorkRule_append_of_none _ _ _ _ hFirst]
  exact findWorkRule_append_of_some _ _ _ _ _ hLaunch

private theorem find_controllerTBridge {language : Language}
    (problem : VerifierTableauProblem language) (symbol : WorkSymbol) :
    findWorkRule (bridgeRules problem)
        (controllerState HeaderController.moreExitState) symbol =
      some (launchRule
        (controllerState HeaderController.moreExitState)
        (tAppenderState (BuilderTokenAppender.seekInputState .t)) symbol) := by
  have hFirst := findWorkRule_launchRules_none_of_source_ne
    (prefixState BuilderFirstTokenPrefix.machine.acceptState)
    (evaluatorState
      (BuilderUnaryPolynomial.machine
        (widthPolynomial problem)).startState)
    (controllerState HeaderController.moreExitState) symbol
    (prefixState_ne_controllerState _ _)
  have hSecond := findWorkRule_launchRules_none_of_source_ne
    (evaluatorState
      (BuilderUnaryPolynomial.machine
        (widthPolynomial problem)).acceptState)
    (controllerState HeaderController.machine.startState)
    (controllerState HeaderController.moreExitState) symbol
    (evaluatorState_ne_controllerState _ _)
  have hLaunch := findWorkRule_launchRules
    (controllerState HeaderController.moreExitState)
    (tAppenderState (BuilderTokenAppender.seekInputState .t)) symbol
  unfold bridgeRules prefixEvaluatorBridge evaluatorControllerBridge
    controllerTBridge
  rw [findWorkRule_append_of_none _ _ _ _ hFirst,
    findWorkRule_append_of_none _ _ _ _ hSecond]
  exact findWorkRule_append_of_some _ _ _ _ _ hLaunch

private theorem find_tControllerBridge {language : Language}
    (problem : VerifierTableauProblem language) (symbol : WorkSymbol) :
    findWorkRule (bridgeRules problem)
        (tAppenderState BuilderTokenAppender.machine.acceptState) symbol =
      some (launchRule
        (tAppenderState BuilderTokenAppender.machine.acceptState)
        (controllerState HeaderController.machine.startState) symbol) := by
  have hFirst := findWorkRule_launchRules_none_of_source_ne
    (prefixState BuilderFirstTokenPrefix.machine.acceptState)
    (evaluatorState
      (BuilderUnaryPolynomial.machine
        (widthPolynomial problem)).startState)
    (tAppenderState BuilderTokenAppender.machine.acceptState) symbol
    (prefixState_ne_tAppenderState _ _)
  have hSecond := findWorkRule_launchRules_none_of_source_ne
    (evaluatorState
      (BuilderUnaryPolynomial.machine
        (widthPolynomial problem)).acceptState)
    (controllerState HeaderController.machine.startState)
    (tAppenderState BuilderTokenAppender.machine.acceptState) symbol
    (evaluatorState_ne_tAppenderState _ _)
  have hThird := findWorkRule_launchRules_none_of_source_ne
    (controllerState HeaderController.moreExitState)
    (tAppenderState (BuilderTokenAppender.seekInputState .t))
    (tAppenderState BuilderTokenAppender.machine.acceptState) symbol
    (controllerState_ne_tAppenderState _ _)
  have hLaunch := findWorkRule_launchRules
    (tAppenderState BuilderTokenAppender.machine.acceptState)
    (controllerState HeaderController.machine.startState) symbol
  unfold bridgeRules prefixEvaluatorBridge evaluatorControllerBridge
    controllerTBridge tControllerBridge
  rw [findWorkRule_append_of_none _ _ _ _ hFirst,
    findWorkRule_append_of_none _ _ _ _ hSecond,
    findWorkRule_append_of_none _ _ _ _ hThird]
  exact findWorkRule_append_of_some _ _ _ _ _ hLaunch

private theorem find_controllerFBridge {language : Language}
    (problem : VerifierTableauProblem language) (symbol : WorkSymbol) :
    findWorkRule (bridgeRules problem)
        (controllerState HeaderController.doneExitState) symbol =
      some (launchRule
        (controllerState HeaderController.doneExitState)
        (fAppenderState (BuilderTokenAppender.seekInputState .f)) symbol) := by
  have hFirst := findWorkRule_launchRules_none_of_source_ne
    (prefixState BuilderFirstTokenPrefix.machine.acceptState)
    (evaluatorState
      (BuilderUnaryPolynomial.machine
        (widthPolynomial problem)).startState)
    (controllerState HeaderController.doneExitState) symbol
    (prefixState_ne_controllerState _ _)
  have hSecond := findWorkRule_launchRules_none_of_source_ne
    (evaluatorState
      (BuilderUnaryPolynomial.machine
        (widthPolynomial problem)).acceptState)
    (controllerState HeaderController.machine.startState)
    (controllerState HeaderController.doneExitState) symbol
    (evaluatorState_ne_controllerState _ _)
  have hThird := findWorkRule_launchRules_none_of_source_ne
    (controllerState HeaderController.moreExitState)
    (tAppenderState (BuilderTokenAppender.seekInputState .t))
    (controllerState HeaderController.doneExitState) symbol (by
      intro h
      exact HeaderController.machine_acceptState_ne_rejectState
        (controllerState_injective h))
  have hFourth := findWorkRule_launchRules_none_of_source_ne
    (tAppenderState BuilderTokenAppender.machine.acceptState)
    (controllerState HeaderController.machine.startState)
    (controllerState HeaderController.doneExitState) symbol
    (Ne.symm (controllerState_ne_tAppenderState _ _))
  have hLaunch := findWorkRule_launchRules
    (controllerState HeaderController.doneExitState)
    (fAppenderState (BuilderTokenAppender.seekInputState .f)) symbol
  unfold bridgeRules prefixEvaluatorBridge evaluatorControllerBridge
    controllerTBridge tControllerBridge controllerFBridge
  rw [findWorkRule_append_of_none _ _ _ _ hFirst,
    findWorkRule_append_of_none _ _ _ _ hSecond,
    findWorkRule_append_of_none _ _ _ _ hThird,
    findWorkRule_append_of_none _ _ _ _ hFourth]
  exact hLaunch

private theorem global_bridge_step {language : Language}
    (problem : VerifierTableauProblem language)
    (source target : Nat) (tape : WorkTape)
    (hHalted : (machine problem).isHalted
      { state := source, tape := tape } = false)
    (hFind : findWorkRule (bridgeRules problem) source tape.head =
      some (launchRule source target tape.head)) :
    workStep? (machine problem) { state := source, tape := tape } =
      some { state := target, tape := tape } := by
  have hGlobalFind : findWorkRule (machine problem).rules source tape.head =
      some (launchRule source target tape.head) := by
    change findWorkRule (rules problem) source tape.head = _
    unfold rules
    exact findWorkRule_append_of_some _ _ _ _ _ hFind
  have hStep := workStep?_eq_apply_of_find (machine problem)
    { state := source, tape := tape }
    (launchRule source target tape.head) hHalted hGlobalFind
  cases tape
  simpa [launchRule, applyWorkRule, WorkTape.write, WorkTape.move] using hStep

theorem prefixEvaluator_launch_workStep {language : Language}
    (problem : VerifierTableauProblem language) (tape : WorkTape) :
    workStep? (machine problem)
        { state := prefixState BuilderFirstTokenPrefix.machine.acceptState
          tape := tape } =
      some
        { state := evaluatorState
            (BuilderUnaryPolynomial.machine
              (widthPolynomial problem)).startState
          tape := tape } := by
  exact global_bridge_step problem _ _ tape
    (machine_isHalted_prefix_false problem
      { state := BuilderFirstTokenPrefix.machine.acceptState, tape := tape })
    (find_prefixEvaluatorBridge problem tape.head)

theorem evaluatorController_launch_workStep {language : Language}
    (problem : VerifierTableauProblem language) (tape : WorkTape) :
    workStep? (machine problem)
        { state := evaluatorState
            (BuilderUnaryPolynomial.machine
              (widthPolynomial problem)).acceptState
          tape := tape } =
      some
        { state := controllerState HeaderController.machine.startState
          tape := tape } := by
  exact global_bridge_step problem _ _ tape
    (machine_isHalted_evaluator_false problem
      { state :=
          (BuilderUnaryPolynomial.machine
            (widthPolynomial problem)).acceptState
        tape := tape })
    (find_evaluatorControllerBridge problem tape.head)

theorem controllerT_launch_workStep {language : Language}
    (problem : VerifierTableauProblem language) (tape : WorkTape) :
    workStep? (machine problem)
        { state := controllerState HeaderController.moreExitState
          tape := tape } =
      some
        { state := tAppenderState
            (BuilderTokenAppender.seekInputState .t)
          tape := tape } := by
  exact global_bridge_step problem _ _ tape
    (machine_isHalted_controller_false problem
      { state := HeaderController.moreExitState, tape := tape })
    (find_controllerTBridge problem tape.head)

theorem tController_launch_workStep {language : Language}
    (problem : VerifierTableauProblem language) (tape : WorkTape) :
    workStep? (machine problem)
        { state := tAppenderState BuilderTokenAppender.machine.acceptState
          tape := tape } =
      some
        { state := controllerState HeaderController.machine.startState
          tape := tape } := by
  exact global_bridge_step problem _ _ tape
    (machine_isHalted_tAppender_false problem
      { state := BuilderTokenAppender.machine.acceptState, tape := tape })
    (find_tControllerBridge problem tape.head)

theorem controllerF_launch_workStep {language : Language}
    (problem : VerifierTableauProblem language) (tape : WorkTape) :
    workStep? (machine problem)
        { state := controllerState HeaderController.doneExitState
          tape := tape } =
      some
        { state := fAppenderState
            (BuilderTokenAppender.seekInputState .f)
          tape := tape } := by
  exact global_bridge_step problem _ _ tape
    (machine_isHalted_controller_false problem
      { state := HeaderController.doneExitState, tape := tape })
    (find_controllerFBridge problem tape.head)

private theorem prefix_workRunExact {language : Language}
    (problem : VerifierTableauProblem language) :
    workRunExact? (machine problem)
        (BuilderFirstTokenPrefix.workSteps problem.input)
        (workStartConfiguration (machine problem)
          (rawInputWorkTape problem.input)) =
      some (renameConfiguration prefixState
        (BuilderFirstTokenPrefix.finalConfiguration problem.input)) := by
  have hTransport := workRunExact?_transport
    BuilderFirstTokenPrefix.machine (machine problem) prefixState
    (prefix_workStep_of_some problem)
    (BuilderFirstTokenPrefix.workSteps problem.input)
    (workStartConfiguration BuilderFirstTokenPrefix.machine
      (rawInputWorkTape problem.input))
    (BuilderFirstTokenPrefix.finalConfiguration problem.input)
    (BuilderFirstTokenPrefix.workRunExact problem.input)
  simpa [machine, workStartConfiguration, renameConfiguration] using hTransport

private theorem evaluator_workRunExact {language : Language}
    (problem : VerifierTableauProblem language) (outside : List WorkSymbol)
    (output : List CNFToken) :
    workRunExact? (machine problem)
        (BuilderUnaryPolynomial.workSteps
          (widthPolynomial problem) problem.input)
        (renameConfiguration evaluatorState
          (BuilderUnaryPolynomial.initialConfiguration
            (widthPolynomial problem) problem.input outside output)) =
      some (renameConfiguration evaluatorState
        (BuilderUnaryPolynomial.finalConfiguration
          (widthPolynomial problem) problem.input outside output)) := by
  exact workRunExact?_transport
    (BuilderUnaryPolynomial.machine (widthPolynomial problem))
    (machine problem) evaluatorState (evaluator_workStep_of_some problem)
    (BuilderUnaryPolynomial.workSteps
      (widthPolynomial problem) problem.input)
    (BuilderUnaryPolynomial.initialConfiguration
      (widthPolynomial problem) problem.input outside output)
    (BuilderUnaryPolynomial.finalConfiguration
      (widthPolynomial problem) problem.input outside output)
    (BuilderUnaryPolynomial.workRunExact
      (widthPolynomial problem) problem.input outside output)

private theorem controller_workRunExact {language : Language}
    (problem : VerifierTableauProblem language)
    (wordPrefix : List WorkSymbol) (remaining : Nat)
    (tail : List WorkSymbol) (output : List CNFToken)
    (hPrefix : ∀ symbol ∈ wordPrefix,
      HeaderController.ScratchSymbol symbol) :
    workRunExact? (machine problem)
        (HeaderController.steps wordPrefix.length remaining)
        (renameConfiguration controllerState
          (HeaderController.initialConfiguration problem.input wordPrefix
            remaining tail output)) =
      some (renameConfiguration controllerState
        (HeaderController.finalConfiguration problem.input wordPrefix
          remaining tail output)) := by
  exact workRunExact?_transport HeaderController.machine (machine problem)
    controllerState (controller_workStep_of_some problem)
    (HeaderController.steps wordPrefix.length remaining)
    (HeaderController.initialConfiguration problem.input wordPrefix
      remaining tail output)
    (HeaderController.finalConfiguration problem.input wordPrefix
      remaining tail output)
    (HeaderController.workRunExact problem.input wordPrefix remaining tail
      output hPrefix)

private theorem tAppender_workRunExact {language : Language}
    (problem : VerifierTableauProblem language) (outside : List WorkSymbol)
    (output : List CNFToken) :
    workRunExact? (machine problem)
        (BuilderTokenAppender.workSteps problem.input output)
        (renameConfiguration tAppenderState
          (BuilderTokenAppender.entryConfiguration .t
            (BuilderTokenAppender.workspaceTape problem.input outside output))) =
      some (renameConfiguration tAppenderState
        (BuilderTokenAppender.finalConfiguration problem.input outside
          (output ++ [.t]))) := by
  exact workRunExact?_transport BuilderTokenAppender.machine
    (machine problem) tAppenderState (tAppender_workStep_of_some problem)
    (BuilderTokenAppender.workSteps problem.input output)
    (BuilderTokenAppender.entryConfiguration .t
      (BuilderTokenAppender.workspaceTape problem.input outside output))
    (BuilderTokenAppender.finalConfiguration problem.input outside
      (output ++ [.t]))
    (BuilderTokenAppender.appendToken_workRunExact problem.input outside
      output .t)

private theorem fAppender_workRunExact {language : Language}
    (problem : VerifierTableauProblem language) (outside : List WorkSymbol)
    (output : List CNFToken) :
    workRunExact? (machine problem)
        (BuilderTokenAppender.workSteps problem.input output)
        (renameConfiguration fAppenderState
          (BuilderTokenAppender.entryConfiguration .f
            (BuilderTokenAppender.workspaceTape problem.input outside output))) =
      some (renameConfiguration fAppenderState
        (BuilderTokenAppender.finalConfiguration problem.input outside
          (output ++ [.f]))) := by
  exact workRunExact?_transport BuilderTokenAppender.machine
    (machine problem) fAppenderState (fAppender_workStep_of_some problem)
    (BuilderTokenAppender.workSteps problem.input output)
    (BuilderTokenAppender.entryConfiguration .f
      (BuilderTokenAppender.workspaceTape problem.input outside output))
    (BuilderTokenAppender.finalConfiguration problem.input outside
      (output ++ [.f]))
    (BuilderTokenAppender.appendToken_workRunExact problem.input outside
      output .f)

/-! ### Exact repeated header loop -/

def headerLoopSteps (input : BitString) (prefixLength : Nat) :
    Nat -> List CNFToken -> Nat
  | 0, output =>
      HeaderController.steps prefixLength 0 + 1 +
        BuilderTokenAppender.workSteps input output
  | remaining + 1, output =>
      HeaderController.steps prefixLength (remaining + 1) + 1 +
        BuilderTokenAppender.workSteps input output + 1 +
          headerLoopSteps input prefixLength remaining (output ++ [.t])

private theorem replicate_succ_append_global {α : Type}
    (count : Nat) (item : α) :
    List.replicate (count + 1) item =
      List.replicate count item ++ [item] := by
  induction count with
  | zero => rfl
  | succ count ih =>
      change item :: List.replicate (count + 1) item =
        (item :: List.replicate count item) ++ [item]
      rw [ih]
      simp only [List.cons_append]

def loopFinalOutside (wordPrefix : List WorkSymbol) (remaining : Nat)
    (tail : List WorkSymbol) : List WorkSymbol :=
  wordPrefix ++ BuilderUnaryPolynomial.separatorSymbol ::
    List.replicate (remaining + 2)
      BuilderUnaryPolynomial.scratchEndSymbol ++ tail

def loopFinalConfiguration {language : Language}
    (problem : VerifierTableauProblem language)
    (wordPrefix : List WorkSymbol) (remaining : Nat)
    (tail : List WorkSymbol) (output : List CNFToken) : WorkConfiguration :=
  { state := (machine problem).acceptState
    tape := BuilderTokenAppender.workspaceTape problem.input
      (loopFinalOutside wordPrefix remaining tail)
      (output ++ List.replicate remaining CNFToken.t ++ [.f]) }

private theorem global_workRunExact_one {language : Language}
    (problem : VerifierTableauProblem language)
    (start next : WorkConfiguration)
    (hStep : workStep? (machine problem) start = some next) :
    workRunExact? (machine problem) 1 start = some next := by
  change
    (match workStep? (machine problem) start with
     | none => none
     | some result => some result) = some next
  rw [hStep]

private theorem headerLoop_workRunExact {language : Language}
    (problem : VerifierTableauProblem language)
    (wordPrefix : List WorkSymbol) (remaining : Nat)
    (tail : List WorkSymbol) (output : List CNFToken)
    (hPrefix : ∀ symbol ∈ wordPrefix,
      HeaderController.ScratchSymbol symbol) :
    workRunExact? (machine problem)
        (headerLoopSteps problem.input wordPrefix.length remaining output)
        (renameConfiguration controllerState
          (HeaderController.initialConfiguration problem.input wordPrefix
            remaining tail output)) =
      some (loopFinalConfiguration problem wordPrefix remaining tail output) := by
  induction remaining generalizing tail output with
  | zero =>
      let afterOutside := HeaderController.outsideAfter wordPrefix 0 tail
      let c0 := renameConfiguration controllerState
        (HeaderController.initialConfiguration problem.input wordPrefix
          0 tail output)
      let cDone := renameConfiguration controllerState
        (HeaderController.finalConfiguration problem.input wordPrefix
          0 tail output)
      let cF := renameConfiguration fAppenderState
        (BuilderTokenAppender.entryConfiguration .f
          (BuilderTokenAppender.workspaceTape problem.input afterOutside
            output))
      let final := loopFinalConfiguration problem wordPrefix 0 tail output
      have hController : workRunExact? (machine problem)
          (HeaderController.steps wordPrefix.length 0) c0 = some cDone := by
        simpa [c0, cDone] using controller_workRunExact problem wordPrefix 0
          tail output hPrefix
      have hLaunchStep := controllerF_launch_workStep problem
        (BuilderTokenAppender.workspaceTape problem.input afterOutside output)
      have hLaunch : workRunExact? (machine problem) 1 cDone = some cF := by
        apply global_workRunExact_one
        simpa [cDone, cF, afterOutside,
          HeaderController.finalConfiguration, renameConfiguration,
          BuilderTokenAppender.entryConfiguration] using hLaunchStep
      have hAppender : workRunExact? (machine problem)
          (BuilderTokenAppender.workSteps problem.input output) cF =
            some final := by
        have hExact := fAppender_workRunExact problem afterOutside output
        simpa [cF, final, loopFinalConfiguration, loopFinalOutside,
          afterOutside, HeaderController.outsideAfter, machine,
          renameConfiguration, BuilderTokenAppender.finalConfiguration,
          BuilderTokenAppender.machine, List.append_assoc] using hExact
      have h01 := PipelineMachineSimulation.workRunExact?_compose
        (machine problem) (HeaderController.steps wordPrefix.length 0) 1
        c0 cDone cF hController hLaunch
      have h02 := PipelineMachineSimulation.workRunExact?_compose
        (machine problem)
        (HeaderController.steps wordPrefix.length 0 + 1)
        (BuilderTokenAppender.workSteps problem.input output)
        c0 cF final h01 hAppender
      simpa [headerLoopSteps, c0, final, Nat.add_assoc] using h02
  | succ rest ih =>
      let afterOutside :=
        HeaderController.outsideAfter wordPrefix (rest + 1) tail
      let nextTail := BuilderUnaryPolynomial.scratchEndSymbol :: tail
      let nextOutput := output ++ [.t]
      let c0 := renameConfiguration controllerState
        (HeaderController.initialConfiguration problem.input wordPrefix
          (rest + 1) tail output)
      let cMore := renameConfiguration controllerState
        (HeaderController.finalConfiguration problem.input wordPrefix
          (rest + 1) tail output)
      let cT := renameConfiguration tAppenderState
        (BuilderTokenAppender.entryConfiguration .t
          (BuilderTokenAppender.workspaceTape problem.input afterOutside
            output))
      let cTDone := renameConfiguration tAppenderState
        (BuilderTokenAppender.finalConfiguration problem.input afterOutside
          nextOutput)
      let cNext := renameConfiguration controllerState
        (HeaderController.initialConfiguration problem.input wordPrefix
          rest nextTail nextOutput)
      let final := loopFinalConfiguration problem wordPrefix (rest + 1)
        tail output
      have hController : workRunExact? (machine problem)
          (HeaderController.steps wordPrefix.length (rest + 1)) c0 =
            some cMore := by
        simpa [c0, cMore] using controller_workRunExact problem wordPrefix
          (rest + 1) tail output hPrefix
      have hLaunchTStep := controllerT_launch_workStep problem
        (BuilderTokenAppender.workspaceTape problem.input afterOutside output)
      have hLaunchT : workRunExact? (machine problem) 1 cMore = some cT := by
        apply global_workRunExact_one
        simpa [cMore, cT, afterOutside,
          HeaderController.finalConfiguration, renameConfiguration,
          BuilderTokenAppender.entryConfiguration] using hLaunchTStep
      have hAppender : workRunExact? (machine problem)
          (BuilderTokenAppender.workSteps problem.input output) cT =
            some cTDone := by
        simpa [cT, cTDone, nextOutput] using
          (tAppender_workRunExact problem afterOutside output)
      have hLaunchBackStep := tController_launch_workStep problem
        (BuilderTokenAppender.workspaceTape problem.input afterOutside
          nextOutput)
      have hLaunchBack : workRunExact? (machine problem) 1 cTDone =
          some cNext := by
        apply global_workRunExact_one
        simpa [cTDone, cNext, nextOutput, nextTail, afterOutside,
          HeaderController.initialConfiguration,
          HeaderController.outsideAfter, HeaderController.outsideBefore,
          BuilderTokenAppender.finalConfiguration, renameConfiguration,
          HeaderController.machine, replicate_succ_append_global,
          List.append_assoc] using hLaunchBackStep
      have hTail := ih nextTail nextOutput
      have hTailExact : workRunExact? (machine problem)
          (headerLoopSteps problem.input wordPrefix.length rest nextOutput)
          cNext = some final := by
        have hEnds := replicate_succ_append_global (rest + 2)
          BuilderUnaryPolynomial.scratchEndSymbol
        simpa [cNext, final, nextTail, nextOutput,
          loopFinalConfiguration, loopFinalOutside, hEnds,
          List.replicate_succ, List.append_assoc] using hTail
      have h01 := PipelineMachineSimulation.workRunExact?_compose
        (machine problem)
        (HeaderController.steps wordPrefix.length (rest + 1)) 1
        c0 cMore cT hController hLaunchT
      have h02 := PipelineMachineSimulation.workRunExact?_compose
        (machine problem)
        (HeaderController.steps wordPrefix.length (rest + 1) + 1)
        (BuilderTokenAppender.workSteps problem.input output)
        c0 cT cTDone h01 hAppender
      have h03 := PipelineMachineSimulation.workRunExact?_compose
        (machine problem)
        (HeaderController.steps wordPrefix.length (rest + 1) + 1 +
          BuilderTokenAppender.workSteps problem.input output) 1
        c0 cTDone cNext h02 hLaunchBack
      have h04 := PipelineMachineSimulation.workRunExact?_compose
        (machine problem)
        (HeaderController.steps wordPrefix.length (rest + 1) + 1 +
          BuilderTokenAppender.workSteps problem.input output + 1)
        (headerLoopSteps problem.input wordPrefix.length rest nextOutput)
        c0 cNext final h03 hTailExact
      simpa [headerLoopSteps, c0, final, nextOutput, Nat.add_assoc] using h04

/-! ### Raw-input-to-complete-header endpoint -/

def baseOutside {language : Language}
    (problem : VerifierTableauProblem language) : List WorkSymbol :=
  PipelineInputFramer.totalInputFramerOutsideLeft problem.input

def rootPrefixLength {language : Language}
    (problem : VerifierTableauProblem language) : Nat :=
  (BuilderUnaryPolynomial.rootPrefixPolynomial
    (widthPolynomial problem)).eval problem.input.length

def controllerPrefixLength {language : Language}
    (problem : VerifierTableauProblem language) : Nat :=
  rootPrefixLength problem - 1

def headerTokens {language : Language}
    (problem : VerifierTableauProblem language) : List CNFToken :=
  List.replicate (width problem) CNFToken.t ++ [.f]

def finalOutside {language : Language}
    (problem : VerifierTableauProblem language) : List WorkSymbol :=
  let scratch := BuilderUnaryPolynomial.scratchWord
    (widthPolynomial problem) problem.input.length
  scratch.take (rootPrefixLength problem) ++
    List.replicate (width problem + 1)
      BuilderUnaryPolynomial.scratchEndSymbol ++
    (baseOutside problem).drop (scratch.length + 1)

def finalTape {language : Language}
    (problem : VerifierTableauProblem language) : WorkTape :=
  BuilderTokenAppender.workspaceTape problem.input
    (finalOutside problem) (headerTokens problem)

def finalConfiguration {language : Language}
    (problem : VerifierTableauProblem language) : WorkConfiguration :=
  { state := (machine problem).acceptState
    tape := finalTape problem }

def workSteps {language : Language}
    (problem : VerifierTableauProblem language) : Nat :=
  BuilderFirstTokenPrefix.workSteps problem.input + 1 +
    BuilderUnaryPolynomial.workSteps
      (widthPolynomial problem) problem.input + 1 +
    headerLoopSteps problem.input (controllerPrefixLength problem)
      (width problem - 1) [.t]

private def scalePolynomial (coefficient : Nat)
    (polynomial : NatPolynomial) : NatPolynomial :=
  .mul (.constant coefficient) polynomial

def headerLoopBoundPolynomial (polynomial : NatPolynomial) :
    NatPolynomial :=
  let rootPrefix := BuilderUnaryPolynomial.rootPrefixPolynomial polynomial
  let inside := .add
    (scalePolynomial 2 rootPrefix)
    (.add (scalePolynomial 4 .variable)
      (.add (.constant 18) (scalePolynomial 2 polynomial)))
  .add (.mul polynomial inside)
    (.add (scalePolynomial 2 polynomial) (.constant 1))

/-- External compiled-time polynomial for the complete header machine. -/
def rawTimeBound {language : Language}
    (verifier : PolynomialTimeVerifier language) : NatPolynomial :=
  let polynomial := formulaWidthPolynomial verifier
  .add BuilderFirstTokenPrefix.rawTimeBound
    (.add (.constant 12)
      (.add
        (scalePolynomial 6
          (BuilderUnaryPolynomial.workTimePolynomial polynomial))
        (scalePolynomial 6 (headerLoopBoundPolynomial polynomial))))

private theorem appender_workSteps_le (input : BitString)
    (output : List CNFToken) :
    BuilderTokenAppender.workSteps input output ≤
      4 * input.length + 2 * output.length + 8 := by
  have hSource := BuilderTokenAppender.sourceCellCount_le input
  unfold BuilderTokenAppender.workSteps BuilderTokenAppender.halfSteps
  omega

private theorem headerLoopSteps_le (input : BitString) (prefixLength : Nat)
    (remaining : Nat) (output : List CNFToken) :
    headerLoopSteps input prefixLength remaining output ≤
      (remaining + 1) *
          (2 * prefixLength + 4 * input.length + 2 * output.length + 16 +
            2 * remaining) +
        2 * remaining + 1 := by
  induction remaining generalizing output with
  | zero =>
      have hAppender := appender_workSteps_le input output
      simp [headerLoopSteps, HeaderController.steps]
      omega
  | succ remaining ih =>
      have hAppender := appender_workSteps_le input output
      have hTail := ih (output ++ [CNFToken.t])
      let stepCost :=
        2 * prefixLength + 4 * input.length + 2 * output.length + 16 +
          2 * (remaining + 1)
      have hInside :
          2 * prefixLength + 4 * input.length +
                2 * (output ++ [CNFToken.t]).length + 16 + 2 * remaining =
            stepCost := by
        simp only [List.length_append, List.length_singleton, stepCost]
        omega
      rw [hInside] at hTail
      rw [headerLoopSteps]
      calc
        HeaderController.steps prefixLength (remaining + 1) + 1 +
              BuilderTokenAppender.workSteps input output + 1 +
            headerLoopSteps input prefixLength remaining
              (output ++ [CNFToken.t]) ≤
            HeaderController.steps prefixLength (remaining + 1) + 1 +
              (4 * input.length + 2 * output.length + 8) + 1 +
                ((remaining + 1) * stepCost +
                  2 * remaining + 1) := by
            omega
        _ = (remaining + 1 + 1) *
              (2 * prefixLength + 4 * input.length + 2 * output.length +
                16 + 2 * (remaining + 1)) +
              2 * (remaining + 1) + 1 := by
            have hMul :
                (remaining + 1 + 1) * stepCost =
                  (remaining + 1) * stepCost + stepCost := by
              rw [Nat.add_mul]
              simp only [Nat.one_mul]
            rw [hMul]
            simp only [HeaderController.steps, stepCost]
            omega

private theorem headerLoop_initial_le {language : Language}
    (problem : VerifierTableauProblem language) :
    headerLoopSteps problem.input (controllerPrefixLength problem)
        (width problem - 1) [.t] ≤
      width problem *
          (2 * rootPrefixLength problem + 4 * problem.input.length + 18 +
            2 * width problem) +
        2 * width problem + 1 := by
  have hLoop := headerLoopSteps_le problem.input
    (controllerPrefixLength problem) (width problem - 1) [.t]
  have hPositive := width_positive problem
  cases hWidth : width problem with
  | zero => omega
  | succ remaining =>
      have hPrefix : controllerPrefixLength problem ≤
          rootPrefixLength problem := by
        unfold controllerPrefixLength
        omega
      have hInside :
          2 * controllerPrefixLength problem +
                4 * problem.input.length + 2 * ([CNFToken.t].length) + 16 +
              2 * remaining ≤
            2 * rootPrefixLength problem + 4 * problem.input.length + 18 +
              2 * (remaining + 1) := by
        simp only [List.length_singleton]
        omega
      have hScaled := Nat.mul_le_mul_left (remaining + 1) hInside
      simp only [hWidth, Nat.add_sub_cancel] at hLoop ⊢
      calc
        headerLoopSteps problem.input (controllerPrefixLength problem)
            remaining [.t] ≤
          (remaining + 1) *
                (2 * controllerPrefixLength problem +
                  4 * problem.input.length + 2 * ([CNFToken.t].length) +
                    16 + 2 * remaining) +
              2 * remaining + 1 := hLoop
        _ ≤ (remaining + 1) *
                (2 * rootPrefixLength problem + 4 * problem.input.length +
                  18 + 2 * (remaining + 1)) +
              2 * remaining + 1 := by
            omega
        _ ≤ (remaining + 1) *
                (2 * rootPrefixLength problem + 4 * problem.input.length +
                  18 + 2 * (remaining + 1)) +
              2 * (remaining + 1) + 1 := by
            omega

theorem rawTimeBound_eval {language : Language}
    (problem : VerifierTableauProblem language) :
    (rawTimeBound problem.verifier).eval problem.input.length =
      BuilderFirstTokenPrefix.rawTimeBound.eval problem.input.length + 12 +
        6 * BuilderUnaryPolynomial.workSteps
          (widthPolynomial problem) problem.input +
        6 *
          (width problem *
              (2 * rootPrefixLength problem + 4 * problem.input.length + 18 +
                2 * width problem) +
            2 * width problem + 1) := by
  rw [rawTimeBound]
  simp only [NatPolynomial.eval_add, NatPolynomial.eval_constant,
    NatPolynomial.eval_mul, scalePolynomial,
    BuilderUnaryPolynomial.workTimePolynomial_eval]
  simp [headerLoopBoundPolynomial, scalePolynomial,
    NatPolynomial.eval_add, NatPolynomial.eval_mul,
    NatPolynomial.eval_constant, NatPolynomial.eval_variable,
    width, widthPolynomial, rootPrefixLength, Nat.add_assoc]

theorem rawTimeBound_le {language : Language}
    (problem : VerifierTableauProblem language) :
    6 * workSteps problem ≤
      (rawTimeBound problem.verifier).eval problem.input.length := by
  have hPrefix := BuilderFirstTokenPrefix.rawTimeBound_le problem.input
  have hLoop := headerLoop_initial_le problem
  have hPrefix' :
      6 * BuilderFirstTokenPrefix.workSteps problem.input ≤
        BuilderFirstTokenPrefix.rawTimeBound.eval problem.input.length := by
    simpa [BitString.size] using hPrefix
  have hLoop' := Nat.mul_le_mul_left 6 hLoop
  rw [rawTimeBound_eval]
  unfold workSteps
  omega

private theorem take_prefix_separator (wordPrefix suffix : List WorkSymbol) :
    (wordPrefix ++ BuilderUnaryPolynomial.separatorSymbol :: suffix).take
        (wordPrefix.length + 1) =
      wordPrefix ++ [BuilderUnaryPolynomial.separatorSymbol] := by
  induction wordPrefix with
  | nil => rfl
  | cons first rest ih =>
      simp [ih]

/-- Every raw input follows one exact trace through the first-token prefix,
the exact unary width evaluator, and the complete header loop. -/
theorem workRunExact {language : Language}
    (problem : VerifierTableauProblem language) :
    workRunExact? (machine problem) (workSteps problem)
        (workStartConfiguration (machine problem)
          (rawInputWorkTape problem.input)) =
      some (finalConfiguration problem) := by
  let polynomial := widthPolynomial problem
  let scratch := BuilderUnaryPolynomial.scratchWord polynomial
    problem.input.length
  let outside := baseOutside problem
  rcases BuilderUnaryPolynomial.root_register_length polynomial
      problem.input.length with ⟨wordPrefix, hScratch, hPrefixLength⟩
  have hWidthEval : polynomial.eval problem.input.length = width problem := by
    rfl
  rw [hWidthEval] at hScratch
  have hPrefixLength' : wordPrefix.length + 1 = rootPrefixLength problem := by
    simpa [polynomial, rootPrefixLength] using hPrefixLength
  have hScratch' : scratch =
      wordPrefix ++ BuilderUnaryPolynomial.separatorSymbol ::
        List.replicate (width problem)
          BuilderUnaryPolynomial.unitSymbol := by
    simpa [scratch] using hScratch
  have hPositive := width_positive problem
  cases hWidth : width problem with
  | zero => omega
  | succ remaining =>
      let tail := outside.drop
        (wordPrefix.length + (remaining + 1 + 1) + 1)
      let c0 := workStartConfiguration (machine problem)
        (rawInputWorkTape problem.input)
      let cPrefix := renameConfiguration prefixState
        (BuilderFirstTokenPrefix.finalConfiguration problem.input)
      let cEvaluator := renameConfiguration evaluatorState
        (BuilderUnaryPolynomial.initialConfiguration polynomial problem.input
          outside [.t])
      let cEvaluatorDone := renameConfiguration evaluatorState
        (BuilderUnaryPolynomial.finalConfiguration polynomial problem.input
          outside [.t])
      let cController := renameConfiguration controllerState
        (HeaderController.initialConfiguration problem.input wordPrefix
          remaining tail [.t])
      let final := finalConfiguration problem
      have hPrefix : workRunExact? (machine problem)
          (BuilderFirstTokenPrefix.workSteps problem.input) c0 =
            some cPrefix := by
        simpa [c0, cPrefix] using prefix_workRunExact problem
      have hLaunchPrefixStep := prefixEvaluator_launch_workStep problem
        (BuilderFirstTokenPrefix.finalTape problem.input)
      have hLaunchPrefix : workRunExact? (machine problem) 1 cPrefix =
          some cEvaluator := by
        apply global_workRunExact_one
        simpa [cPrefix, cEvaluator, polynomial, outside, baseOutside,
          BuilderUnaryPolynomial.initialConfiguration,
          BuilderFirstTokenPrefix.finalConfiguration,
          BuilderFirstTokenPrefix.finalTape, renameConfiguration]
          using hLaunchPrefixStep
      have hEvaluator : workRunExact? (machine problem)
          (BuilderUnaryPolynomial.workSteps polynomial problem.input)
          cEvaluator = some cEvaluatorDone := by
        simpa [cEvaluator, cEvaluatorDone, polynomial] using
          evaluator_workRunExact problem outside [.t]
      have hEvaluatorOutside :
          BuilderUnaryPolynomial.finalOutsideLeft polynomial problem.input
            outside =
          HeaderController.outsideBefore wordPrefix remaining tail := by
        change scratch ++ BuilderUnaryPolynomial.scratchEndSymbol ::
            outside.drop (scratch.length + 1) = _
        rw [hScratch']
        simp [HeaderController.outsideBefore, tail, hWidth,
          replicate_succ_append_global, List.append_assoc]
      have hLaunchEvaluatorStep := evaluatorController_launch_workStep problem
        (BuilderUnaryPolynomial.finalConfiguration polynomial problem.input
          outside [.t]).tape
      have hLaunchEvaluator : workRunExact? (machine problem) 1
          cEvaluatorDone = some cController := by
        apply global_workRunExact_one
        simpa [cEvaluatorDone, cController, polynomial, tail,
          BuilderUnaryPolynomial.finalConfiguration,
          HeaderController.initialConfiguration,
          renameConfiguration, HeaderController.machine,
          hEvaluatorOutside] using
          hLaunchEvaluatorStep
      have hScratchPrefix : ∀ symbol ∈ wordPrefix,
          HeaderController.ScratchSymbol symbol := by
        intro symbol hMem
        have hInScratch : symbol ∈ scratch := by
          rw [hScratch']
          exact List.mem_append_left _ hMem
        exact BuilderUnaryPolynomial.scratchWord_symbol polynomial
          problem.input.length symbol (by simpa [scratch] using hInScratch)
      have hLoop := headerLoop_workRunExact problem wordPrefix remaining
        tail [.t] hScratchPrefix
      have hFinalOutside : finalOutside problem =
          loopFinalOutside wordPrefix remaining tail := by
        change scratch.take (rootPrefixLength problem) ++
            List.replicate (width problem + 1)
              BuilderUnaryPolynomial.scratchEndSymbol ++
            outside.drop (scratch.length + 1) = _
        rw [hScratch', ← hPrefixLength', hWidth]
        rw [take_prefix_separator]
        simp [loopFinalOutside, tail, List.append_assoc]
      have hHeaderTokens : headerTokens problem =
          [.t] ++ List.replicate remaining CNFToken.t ++ [.f] := by
        simp [headerTokens, hWidth, List.replicate_succ]
      have hLoopExact : workRunExact? (machine problem)
          (headerLoopSteps problem.input wordPrefix.length remaining [.t])
          cController = some final := by
        simpa [cController, final, finalConfiguration, finalTape,
          loopFinalConfiguration, hFinalOutside, hHeaderTokens,
          List.append_assoc] using hLoop
      have h01 := PipelineMachineSimulation.workRunExact?_compose
        (machine problem) (BuilderFirstTokenPrefix.workSteps problem.input) 1
        c0 cPrefix cEvaluator hPrefix hLaunchPrefix
      have h02 := PipelineMachineSimulation.workRunExact?_compose
        (machine problem)
        (BuilderFirstTokenPrefix.workSteps problem.input + 1)
        (BuilderUnaryPolynomial.workSteps polynomial problem.input)
        c0 cEvaluator cEvaluatorDone h01 hEvaluator
      have h03 := PipelineMachineSimulation.workRunExact?_compose
        (machine problem)
        (BuilderFirstTokenPrefix.workSteps problem.input + 1 +
          BuilderUnaryPolynomial.workSteps polynomial problem.input) 1
        c0 cEvaluatorDone cController h02 hLaunchEvaluator
      have h04 := PipelineMachineSimulation.workRunExact?_compose
        (machine problem)
        (BuilderFirstTokenPrefix.workSteps problem.input + 1 +
          BuilderUnaryPolynomial.workSteps polynomial problem.input + 1)
        (headerLoopSteps problem.input wordPrefix.length remaining [.t])
        c0 cController final h03 hLoopExact
      simpa [workSteps, polynomial, c0, final, hWidth,
        controllerPrefixLength, ← hPrefixLength', Nat.add_assoc] using h04

theorem finalTape_represents {language : Language}
    (problem : VerifierTableauProblem language) :
    PipelineTape.Represents (Tape.ofInput problem.input)
      (finalTape problem) := by
  exact BuilderTokenAppender.workspaceTape_represents problem.input
    (finalOutside problem) (headerTokens problem)

private theorem encodeUnaryTokens_eq_replicate (count : Nat) :
    encodeUnaryTokens count =
      List.replicate count CNFToken.t ++ [.f] := by
  induction count with
  | zero => rfl
  | succ count ih =>
      simp [encodeUnaryTokens, List.replicate_succ, ih]

theorem headerTokens_eq_encodeUnaryTokens {language : Language}
    (problem : VerifierTableauProblem language) :
    headerTokens problem = encodeUnaryTokens problem.FormulaWidth := by
  rw [← width_eq_FormulaWidth problem]
  exact (encodeUnaryTokens_eq_replicate (width problem)).symm

private theorem encodeTokenPairs_append_local
    (left right : List CNFToken) :
    encodeTokenPairs (left ++ right) =
      encodeTokenPairs left ++ encodeTokenPairs right := by
  induction left with
  | nil => rfl
  | cons token rest ih =>
      cases token <;>
        simp [encodeTokenPairs, ih, List.append_assoc]

/-- The emitted token pairs are exactly the complete canonical unary-width
prefix of the concrete encoded formula. -/
theorem finalTokenBits_eq_encodedFormula_header {language : Language}
    (problem : VerifierTableauProblem language) :
    encodeTokenPairs (headerTokens problem) =
      problem.encodedFormula.take (2 * (problem.FormulaWidth + 1)) := by
  rw [headerTokens_eq_encodeUnaryTokens]
  have hLength := encodeTokenPairs_length
    (encodeUnaryTokens problem.FormulaWidth)
  have hUnaryLength := encodeUnaryTokens_length problem.FormulaWidth
  rw [hUnaryLength] at hLength
  let suffix :=
    encodeTokenPairs
      (encodeClauseListTokens
        (BoundedClauses.emit (LocalProgram.emit problem.program)) ++
          [.finish]) ++ [false]
  have hShape : problem.encodedFormula =
      encodeTokenPairs (encodeUnaryTokens problem.FormulaWidth) ++ suffix := by
    simp [VerifierTableauProblem.encodedFormula,
      VerifierTableauProblem.formula, encodeCNF, encodeCNFTokens,
      LocalProgram.toFormula, suffix, encodeTokenPairs_append_local,
      List.append_assoc]
  rw [hShape, ← hLength]
  exact List.take_left.symm

private theorem finalConfiguration_isHalted {language : Language}
    (problem : VerifierTableauProblem language) :
    (machine problem).isHalted (finalConfiguration problem) = true := by
  rfl

/-- Exact six-for-one compilation of the complete header trace. -/
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

/-- The externally stated polynomial fuel reaches the exact complete-header
endpoint and then remains there. -/
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

/-- The exact first-token-prefix endpoint remains nonhalting until its bridge
into the polynomial evaluator consumes one further transition. -/
theorem prefixEndpoint_before_launch_timeout {language : Language}
    (problem : VerifierTableauProblem language) :
    workBoundedDecide (machine problem)
        (BuilderFirstTokenPrefix.workSteps problem.input)
        (rawInputWorkTape problem.input) = .timeout := by
  unfold workBoundedDecide
  rw [workRun_eq_of_workRunExact (machine problem)
    (BuilderFirstTokenPrefix.workSteps problem.input)
    (workStartConfiguration (machine problem)
      (rawInputWorkTape problem.input))
    (renameConfiguration prefixState
      (BuilderFirstTokenPrefix.finalConfiguration problem.input))
    (prefix_workRunExact problem)]
  exact verdict_timeout_of_not_halted problem _
    (machine_isHalted_prefix_false problem
      (BuilderFirstTokenPrefix.finalConfiguration problem.input))

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
  have hNotHalted := isHalted_false_of_workStep_some problem before final hLast
  unfold workBoundedDecide
  change
    (let result := workRun (machine problem) short initial
     if result.state == (machine problem).acceptState then WorkVerdict.accept
     else if result.state == (machine problem).rejectState then
       WorkVerdict.reject
     else WorkVerdict.timeout) = WorkVerdict.timeout
  rw [hRun]
  exact verdict_timeout_of_not_halted problem before hNotHalted

end BuilderCompleteHeader

end CookLevin

end PNP.Concrete
