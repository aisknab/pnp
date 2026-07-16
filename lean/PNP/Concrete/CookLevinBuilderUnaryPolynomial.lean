/-
Copyright (c) 2026 PNP Labs.

A literal unary evaluator for the nonnegative natural-polynomial syntax used
by the concrete Cook--Levin size bounds.  The generated finite work machine
constructs one delimiter-separated unary register per syntax-tree node in
postorder, outside the represented input's left boundary.  Its executable
rule table is compiled structurally from polynomial syntax and never invokes
`NatPolynomial.eval`.

This is an internal builder stage.  It does not inspect a verifier answer,
emit formula clauses, interpret a formula cursor, provide a RawRefinement or
reduction, decide CNF-SAT, or establish P = NP.
-/

import PNP.Concrete.CookLevinBuilderFirstTokenPrefix

namespace PNP.Concrete

namespace CookLevin

namespace BuilderUnaryPolynomial

open PipelineTape

/-! ### Phase-local unary scratch representation -/

/-- One durable unary register cell. -/
def unitSymbol : WorkSymbol := WorkSymbol.oneOne

/-- Delimiter preceding every postorder register. -/
def separatorSymbol : WorkSymbol := WorkSymbol.zeroOne

/-- Unique active end marker for the evaluator scratch prefix. -/
def scratchEndSymbol : WorkSymbol := WorkSymbol.blankOne

/-- Temporary mark for a processed unary register cell. -/
def registerMarkSymbol : WorkSymbol := WorkSymbol.zeroZero

/-- Temporary marks for source input bits while copying the variable leaf. -/
def sourceZeroMarkSymbol : WorkSymbol := WorkSymbol.zeroZero
def sourceOneMarkSymbol : WorkSymbol := WorkSymbol.oneZero

theorem unitSymbol_ne_separatorSymbol : unitSymbol ≠ separatorSymbol := by decide
theorem unitSymbol_ne_scratchEndSymbol : unitSymbol ≠ scratchEndSymbol := by decide
theorem separatorSymbol_ne_scratchEndSymbol :
    separatorSymbol ≠ scratchEndSymbol := by decide
theorem registerMarkSymbol_ne_unitSymbol :
    registerMarkSymbol ≠ unitSymbol := by decide
theorem registerMarkSymbol_ne_separatorSymbol :
    registerMarkSymbol ≠ separatorSymbol := by decide
theorem registerMarkSymbol_ne_scratchEndSymbol :
    registerMarkSymbol ≠ scratchEndSymbol := by decide

/-- Postorder node count. -/
def nodeCount : NatPolynomial → Nat
  | .constant _ => 1
  | .variable => 1
  | .add left right => nodeCount left + nodeCount right + 1
  | .mul left right => nodeCount left + nodeCount right + 1

/-- Sum, as polynomial syntax, of the values of every postorder node. -/
def subtreeValueSumPolynomial : NatPolynomial → NatPolynomial
  | polynomial@(.constant _) => polynomial
  | .variable => .variable
  | polynomial@(.add left right) =>
      .add
        (.add (subtreeValueSumPolynomial left)
          (subtreeValueSumPolynomial right))
        polynomial
  | polynomial@(.mul left right) =>
      .add
        (.add (subtreeValueSumPolynomial left)
          (subtreeValueSumPolynomial right))
        polynomial

/-- Exact number of non-end scratch cells occupied by all registers. -/
def registerSpanPolynomial (polynomial : NatPolynomial) : NatPolynomial :=
  .add (.constant (nodeCount polynomial))
    (subtreeValueSumPolynomial polynomial)

/-- Exact number of scratch cells before the root register's unary payload. -/
def rootPrefixPolynomial : NatPolynomial → NatPolynomial
  | .constant _ => .constant 1
  | .variable => .constant 1
  | .add left right =>
      .add
        (.add (registerSpanPolynomial left)
          (registerSpanPolynomial right))
        (.constant 1)
  | .mul left right =>
      .add
        (.add (registerSpanPolynomial left)
          (registerSpanPolynomial right))
        (.constant 1)

/-- Semantic postorder values used only to state and prove the endpoint. -/
def registerValues : NatPolynomial → Nat → List Nat
  | .constant value, _ => [value]
  | .variable, input => [input]
  | .add left right, input =>
      registerValues left input ++ registerValues right input ++
        [left.eval input + right.eval input]
  | .mul left right, input =>
      registerValues left input ++ registerValues right input ++
        [left.eval input * right.eval input]

/-- Concrete delimiter-separated unary register word. -/
def registerWord : List Nat → List WorkSymbol
  | [] => []
  | value :: rest =>
      separatorSymbol ::
        (List.replicate value unitSymbol ++ registerWord rest)

/-- Complete postorder scratch word, excluding its active end marker. -/
def scratchWord (polynomial : NatPolynomial) (inputLength : Nat) :
    List WorkSymbol :=
  registerWord (registerValues polynomial inputLength)

/-- Prefix overwrite used for arbitrary pre-existing exterior-left garbage. -/
def overlayScratch (word garbage : List WorkSymbol) : List WorkSymbol :=
  word ++ scratchEndSymbol :: garbage.drop (word.length + 1)

@[simp] theorem registerValues_length (polynomial : NatPolynomial)
    (input : Nat) :
    (registerValues polynomial input).length = nodeCount polynomial := by
  induction polynomial with
  | constant value => rfl
  | «variable» => rfl
  | add left right leftIH rightIH =>
      simp [registerValues, nodeCount, leftIH, rightIH] <;> omega
  | mul left right leftIH rightIH =>
      simp [registerValues, nodeCount, leftIH, rightIH] <;> omega

@[simp] theorem registerWord_length (values : List Nat) :
    (registerWord values).length = values.length + values.sum := by
  induction values with
  | nil => rfl
  | cons value rest ih =>
      simp [registerWord, ih]
      omega

@[simp] theorem registerWord_append (left right : List Nat) :
    registerWord (left ++ right) = registerWord left ++ registerWord right := by
  induction left with
  | nil => rfl
  | cons value rest ih =>
      simp [registerWord, ih, List.append_assoc]

theorem registerValues_sum (polynomial : NatPolynomial) (input : Nat) :
    (registerValues polynomial input).sum =
      (subtreeValueSumPolynomial polynomial).eval input := by
  induction polynomial with
  | constant value => rfl
  | «variable» => rfl
  | add left right leftIH rightIH =>
      simp [registerValues, subtreeValueSumPolynomial, leftIH, rightIH] <;>
        omega
  | mul left right leftIH rightIH =>
      simp [registerValues, subtreeValueSumPolynomial, leftIH, rightIH] <;>
        omega

theorem scratchWord_length (polynomial : NatPolynomial) (input : Nat) :
    (scratchWord polynomial input).length =
      (registerSpanPolynomial polynomial).eval input := by
  unfold scratchWord registerSpanPolynomial
  rw [registerWord_length, registerValues_length, registerValues_sum]
  rfl

theorem registerValues_eq_prefix_append_root
    (polynomial : NatPolynomial) (input : Nat) :
    ∃ valuesPrefix,
      registerValues polynomial input =
        valuesPrefix ++ [polynomial.eval input] := by
  cases polynomial with
  | constant value => exact ⟨[], rfl⟩
  | «variable» => exact ⟨[], rfl⟩
  | add left right =>
      exact ⟨registerValues left input ++ registerValues right input, rfl⟩
  | mul left right =>
      exact ⟨registerValues left input ++ registerValues right input, rfl⟩

theorem scratchWord_eq_root (polynomial : NatPolynomial) (input : Nat) :
    ∃ wordPrefix,
      scratchWord polynomial input =
        wordPrefix ++ separatorSymbol ::
          List.replicate (polynomial.eval input) unitSymbol := by
  rcases registerValues_eq_prefix_append_root polynomial input with
    ⟨valuesPrefix, hPrefix⟩
  refine ⟨registerWord valuesPrefix, ?_⟩
  simp [scratchWord, hPrefix, registerWord]

theorem root_prefix_length (polynomial : NatPolynomial) (input : Nat) :
    ∃ wordPrefix,
      scratchWord polynomial input =
          wordPrefix ++ separatorSymbol ::
            List.replicate (polynomial.eval input) unitSymbol ∧
      wordPrefix.length + 1 =
        (rootPrefixPolynomial polynomial).eval input := by
  cases polynomial with
  | constant value =>
      refine ⟨[], ?_, rfl⟩
      simp [scratchWord, registerValues, registerWord]
  | «variable» =>
      refine ⟨[], ?_, rfl⟩
      simp [scratchWord, registerValues, registerWord]
  | add left right =>
      refine ⟨scratchWord left input ++ scratchWord right input, ?_, ?_⟩
      · simp [scratchWord, registerValues, registerWord, List.append_assoc]
      · rw [List.length_append, scratchWord_length, scratchWord_length]
        rfl
  | mul left right =>
      refine ⟨scratchWord left input ++ scratchWord right input, ?_, ?_⟩
      · simp [scratchWord, registerValues, registerWord, List.append_assoc]
      · rw [List.length_append, scratchWord_length, scratchWord_length]
        rfl

/-! ### Total finite-table assembler -/

/-- One already-resolved action in the generated finite table. -/
structure StateAction where
  targetState : Nat
  writeSymbol : WorkSymbol
  move : HeadMove

/-- A finite control state is generated by resolving one action for each of
the nine work symbols.  The function is used only while constructing the
literal list of `WorkRule` records. -/
abbrev StateSpec := WorkSymbol → StateAction

def ruleOf (state : Nat) (spec : StateSpec) (read : WorkSymbol) : WorkRule :=
  let action := spec read
  { sourceState := state
    readSymbol := read
    targetState := action.targetState
    writeSymbol := action.writeSymbol
    move := action.move }

def rulesAt (state : Nat) (spec : StateSpec) : List WorkRule :=
  PipelineMachineSimulation.allWorkSymbols.map (ruleOf state spec)

def rulesFrom : Nat → List StateSpec → List WorkRule
  | _, [] => []
  | state, spec :: rest =>
      rulesAt state spec ++ rulesFrom (state + 1) rest

theorem rulesAt_length (state : Nat) (spec : StateSpec) :
    (rulesAt state spec).length = 9 := by rfl

theorem rulesFrom_length (base : Nat) (specs : List StateSpec) :
    (rulesFrom base specs).length = 9 * specs.length := by
  induction specs generalizing base with
  | nil => rfl
  | cons spec rest ih =>
      simp [rulesFrom, rulesAt_length, ih]
      omega

private theorem rulesAt_source_eq {state : Nat} {spec : StateSpec}
    {rule : WorkRule} (hMem : rule ∈ rulesAt state spec) :
    rule.sourceState = state := by
  rcases List.mem_map.mp hMem with ⟨symbol, _hSymbol, hRule⟩
  rw [← hRule]
  rfl

private theorem rulesFrom_source_bounds {base : Nat}
    {specs : List StateSpec} {rule : WorkRule}
    (hMem : rule ∈ rulesFrom base specs) :
    base ≤ rule.sourceState ∧ rule.sourceState < base + specs.length := by
  induction specs generalizing base with
  | nil => contradiction
  | cons spec rest ih =>
      rw [rulesFrom, List.mem_append] at hMem
      cases hMem with
      | inl hHead =>
          have hSource := rulesAt_source_eq hHead
          simp only [List.length_cons]
          constructor <;> omega
      | inr hRest =>
          have hBounds := ih hRest
          simp only [List.length_cons]
          constructor <;> omega

private theorem rulesAt_pairwise_query_distinct
    (state : Nat) (spec : StateSpec) :
    (rulesAt state spec).Pairwise (fun left right =>
      (left.sourceState, left.readSymbol) ≠
        (right.sourceState, right.readSymbol)) := by
  unfold rulesAt PipelineMachineSimulation.allWorkSymbols
  simp [ruleOf, WorkSymbol.blank, WorkSymbol.blankZero,
    WorkSymbol.blankOne, WorkSymbol.zeroBlank, WorkSymbol.zeroZero,
    WorkSymbol.zeroOne, WorkSymbol.oneBlank, WorkSymbol.oneZero,
    WorkSymbol.oneOne]

theorem rulesFrom_pairwise_query_distinct
    (base : Nat) (specs : List StateSpec) :
    (rulesFrom base specs).Pairwise (fun left right =>
      (left.sourceState, left.readSymbol) ≠
        (right.sourceState, right.readSymbol)) := by
  induction specs generalizing base with
  | nil => exact List.Pairwise.nil
  | cons spec rest ih =>
      rw [rulesFrom, List.pairwise_append]
      refine ⟨rulesAt_pairwise_query_distinct base spec,
        ih (base := base + 1), ?_⟩
      intro left hLeft right hRight hEqual
      have hLeftSource := rulesAt_source_eq hLeft
      have hRightBounds := rulesFrom_source_bounds hRight
      have hSourceEqual := congrArg Prod.fst hEqual
      simp only at hSourceEqual
      omega

private theorem findWorkRule_rulesAtFrom_of_mem
    (symbols : List WorkSymbol) (state : Nat) (spec : StateSpec)
    (selected : WorkSymbol) (hMem : selected ∈ symbols) :
    findWorkRule (symbols.map (ruleOf state spec)) state selected =
      some (ruleOf state spec selected) := by
  induction symbols with
  | nil => contradiction
  | cons first rest ih =>
      by_cases hFirst : first = selected
      · subst first
        apply findWorkRule_cons_of_matches
        exact ⟨rfl, rfl⟩
      · have hRest : selected ∈ rest := by
          cases hMem with
          | head => exact False.elim (hFirst rfl)
          | tail _ hTail => exact hTail
        change findWorkRule
          (ruleOf state spec first :: rest.map (ruleOf state spec))
            state selected = some (ruleOf state spec selected)
        rw [findWorkRule_cons_of_not_matches]
        · exact ih hRest
        · intro hMatch
          exact hFirst (by simpa [ruleOf] using hMatch.2)

theorem findWorkRule_rulesAt (state : Nat) (spec : StateSpec)
    (symbol : WorkSymbol) :
    findWorkRule (rulesAt state spec) state symbol =
      some (ruleOf state spec symbol) := by
  exact findWorkRule_rulesAtFrom_of_mem
    PipelineMachineSimulation.allWorkSymbols state spec symbol
    (PipelineMachineSimulation.allWorkSymbols_mem symbol)

theorem findWorkRule_rulesAt_none_of_state_ne
    (source state : Nat) (spec : StateSpec) (symbol : WorkSymbol)
    (hNe : source ≠ state) :
    findWorkRule (rulesAt source spec) state symbol = none := by
  unfold rulesAt
  apply PipelineMachineSimulation.findWorkRule_map_none_of_source_ne
  intro item
  simpa [ruleOf] using hNe

theorem findWorkRule_rulesFrom_head (base : Nat) (spec : StateSpec)
    (rest : List StateSpec) (symbol : WorkSymbol) :
    findWorkRule (rulesFrom base (spec :: rest)) base symbol =
      some (ruleOf base spec symbol) := by
  unfold rulesFrom
  exact findWorkRule_append_of_some _ _ _ _ _
    (findWorkRule_rulesAt base spec symbol)

theorem findWorkRule_rulesFrom_none_of_outside
    (base state : Nat) (specs : List StateSpec) (symbol : WorkSymbol)
    (hOutside : state < base ∨ base + specs.length ≤ state) :
    findWorkRule (rulesFrom base specs) state symbol = none := by
  induction specs generalizing base with
  | nil => rfl
  | cons spec rest ih =>
      unfold rulesFrom
      rw [findWorkRule_append_of_none]
      · apply ih (base := base + 1)
        simp only [List.length_cons] at hOutside
        omega
      · apply findWorkRule_rulesAt_none_of_state_ne
        simp only [List.length_cons] at hOutside
        omega

theorem rulesFrom_append (base : Nat) (left right : List StateSpec) :
    rulesFrom base (left ++ right) =
      rulesFrom base left ++ rulesFrom (base + left.length) right := by
  induction left generalizing base with
  | nil => simp [rulesFrom]
  | cons first rest ih =>
      simp only [List.cons_append, rulesFrom, List.length_cons]
      rw [ih (base := base + 1), List.append_assoc]
      rw [show base + 1 + rest.length = base + (rest.length + 1) by omega]

theorem findWorkRule_rulesFrom_at_append
    (base : Nat) (before : List StateSpec) (spec : StateSpec)
    (after : List StateSpec) (symbol : WorkSymbol) :
    findWorkRule (rulesFrom base (before ++ spec :: after))
        (base + before.length) symbol =
      some (ruleOf (base + before.length) spec symbol) := by
  rw [rulesFrom_append]
  rw [findWorkRule_append_of_none]
  · simpa using
      (findWorkRule_rulesFrom_head (base + before.length) spec after symbol)
  · apply findWorkRule_rulesFrom_none_of_outside
    exact Or.inr (Nat.le_refl _)

/-! ### Structurally compiled evaluator control states -/

def keepAction (target : Nat) (move : HeadMove)
    (read : WorkSymbol) : StateAction :=
  { targetState := target, writeSymbol := read, move := move }

def writeAction (target : Nat) (write : WorkSymbol)
    (move : HeadMove) : StateAction :=
  { targetState := target, writeSymbol := write, move := move }

def deadAction (dead : Nat) (read : WorkSymbol) : StateAction :=
  keepAction dead .stay read

private def appendManyStateCount (count : Nat) : Nat := 2 * count

private def appendManySpecs : Nat → Nat → Nat → Nat → List StateSpec
  | 0, _, _, _ => []
  | count + 1, base, next, dead =>
      let after := if count = 0 then next else base + 2
      (fun read =>
        if read = scratchEndSymbol then
          writeAction (base + 1) unitSymbol .left
        else
          deadAction dead read) ::
      (fun _read => writeAction after scratchEndSymbol .stay) ::
      appendManySpecs count (base + 2) next dead

@[simp] private theorem appendManySpecs_length
    (count base next dead : Nat) :
    (appendManySpecs count base next dead).length =
      appendManyStateCount count := by
  induction count generalizing base with
  | zero => rfl
  | succ count ih =>
      simp [appendManySpecs, appendManyStateCount, ih]
      omega

private def separatorSpecs (base next dead : Nat) : List StateSpec :=
  [(fun read =>
      if read = scratchEndSymbol then
        writeAction (base + 1) separatorSymbol .left
      else
        deadAction dead read),
   (fun _read => writeAction next scratchEndSymbol .stay)]

@[simp] private theorem separatorSpecs_length (base next dead : Nat) :
    (separatorSpecs base next dead).length = 2 := by rfl

private def constantOperationStateCount (value : Nat) : Nat :=
  2 + appendManyStateCount value

private def constantOperationSpecs (value base next dead : Nat) :
    List StateSpec :=
  separatorSpecs base (base + 2) dead ++
    appendManySpecs value (base + 2) next dead

@[simp] private theorem constantOperationSpecs_length
    (value base next dead : Nat) :
    (constantOperationSpecs value base next dead).length =
      constantOperationStateCount value := by
  simp [constantOperationSpecs, constantOperationStateCount,
    separatorSpecs]
  omega

private def sourceCopyStateCount : Nat := 8

/-- Resolved source-copy phases, named separately for exact trace proofs. -/
private def sourceStartSpec (base dead : Nat) : StateSpec := fun read =>
  if read = scratchEndSymbol then
    keepAction (base + 1) .right read
  else deadAction dead read

private def sourceSeekMarkerSpec (base dead : Nat) : StateSpec := fun read =>
  if read = unitSymbol ∨ read = separatorSymbol ∨
      read = registerMarkSymbol then
    keepAction (base + 1) .right read
  else if read = leftMarker then
    keepAction (base + 2) .right read
  else deadAction dead read

private def sourceScanInputSpec (base dead : Nat) : StateSpec := fun read =>
  if read = sourceZeroMarkSymbol ∨ read = sourceOneMarkSymbol then
    keepAction (base + 2) .right read
  else if read = WorkSymbol.zeroBlank then
    writeAction (base + 3) sourceZeroMarkSymbol .left
  else if read = WorkSymbol.oneBlank then
    writeAction (base + 3) sourceOneMarkSymbol .left
  else if read = rightMarker ∨ read = WorkSymbol.blank then
    keepAction (base + 6) .left read
  else deadAction dead read

private def sourceSeekEndSpec (base dead : Nat) : StateSpec := fun read =>
  if read = sourceZeroMarkSymbol ∨ read = sourceOneMarkSymbol ∨
      read = WorkSymbol.zeroBlank ∨ read = WorkSymbol.oneBlank ∨
      read = leftMarker ∨ read = unitSymbol ∨
      read = separatorSymbol ∨ read = registerMarkSymbol then
    keepAction (base + 3) .left read
  else if read = scratchEndSymbol then
    keepAction (base + 4) .stay read
  else deadAction dead read

private def sourceAppendFirstSpec (base dead : Nat) : StateSpec := fun read =>
  if read = scratchEndSymbol then
    writeAction (base + 5) unitSymbol .left
  else deadAction dead read

private def sourceAppendSecondSpec (base : Nat) : StateSpec := fun _read =>
  writeAction base scratchEndSymbol .stay

private def sourceRestoreInputSpec (base dead : Nat) : StateSpec := fun read =>
  if read = sourceZeroMarkSymbol then
    writeAction (base + 6) WorkSymbol.zeroBlank .left
  else if read = sourceOneMarkSymbol then
    writeAction (base + 6) WorkSymbol.oneBlank .left
  else if read = leftMarker then
    keepAction (base + 7) .left read
  else deadAction dead read

private def sourceSeekEndDoneSpec
    (base next dead : Nat) : StateSpec := fun read =>
  if read = unitSymbol ∨ read = separatorSymbol ∨
      read = registerMarkSymbol then
    keepAction (base + 7) .left read
  else if read = scratchEndSymbol then
    keepAction next .stay read
  else deadAction dead read

/-- Copy the represented source word into the newest unary register.  The
input marks are restored before control continues at `next`. -/
private def sourceCopySpecs (base next dead : Nat) : List StateSpec :=
  [sourceStartSpec base dead,
   sourceSeekMarkerSpec base dead,
   sourceScanInputSpec base dead,
   sourceSeekEndSpec base dead,
   sourceAppendFirstSpec base dead,
   sourceAppendSecondSpec base,
   sourceRestoreInputSpec base dead,
   sourceSeekEndDoneSpec base next dead]

@[simp] private theorem sourceCopySpecs_length (base next dead : Nat) :
    (sourceCopySpecs base next dead).length = sourceCopyStateCount := by
  rfl

private def variableOperationStateCount : Nat := 2 + sourceCopyStateCount

private def variableOperationSpecs (base next dead : Nat) : List StateSpec :=
  separatorSpecs base (base + 2) dead ++
    sourceCopySpecs (base + 2) next dead

@[simp] private theorem variableOperationSpecs_length
    (base next dead : Nat) :
    (variableOperationSpecs base next dead).length =
      variableOperationStateCount := by
  rfl

private def locateSpecs : Nat → Nat → Nat → Nat → List StateSpec
  | 0, _, _, _ => []
  | remaining + 1, base, scan, dead =>
      (fun read =>
        if read = unitSymbol ∨ read = registerMarkSymbol then
          keepAction base .right read
        else if read = separatorSymbol then
          if remaining = 0 then keepAction scan .right read
          else keepAction (base + 1) .right read
        else deadAction dead read) ::
      locateSpecs remaining (base + 1) scan dead

@[simp] private theorem locateSpecs_length
    (distance base scan dead : Nat) :
    (locateSpecs distance base scan dead).length = distance := by
  induction distance generalizing base with
  | zero => rfl
  | succ distance ih => simp [locateSpecs, ih]

private def copyStateCount (distance : Nat) : Nat := distance + 7

private def copyLocateBase (base : Nat) : Nat := base + 1
private def copyScanState (distance base : Nat) : Nat :=
  copyLocateBase base + distance
private def copySeekEndState (distance base : Nat) : Nat :=
  copyScanState distance base + 1
private def copyAppendFirstState (distance base : Nat) : Nat :=
  copyScanState distance base + 2
private def copyAppendSecondState (distance base : Nat) : Nat :=
  copyScanState distance base + 3
private def copyRestoreState (distance base : Nat) : Nat :=
  copyScanState distance base + 4
private def copySeekEndDoneState (distance base : Nat) : Nat :=
  copyScanState distance base + 5

private def copyStartSpec (base dead : Nat) : StateSpec := fun read =>
  if read = scratchEndSymbol then
    keepAction (copyLocateBase base) .right read
  else deadAction dead read

private def copyScanSpec (distance base dead : Nat) : StateSpec := fun read =>
  if read = registerMarkSymbol then
    keepAction (copyScanState distance base) .right read
  else if read = unitSymbol then
    writeAction (copySeekEndState distance base) registerMarkSymbol .left
  else if read = separatorSymbol then
    keepAction (copyRestoreState distance base) .left read
  else deadAction dead read

private def copySeekEndSpec (distance base dead : Nat) : StateSpec :=
    fun read =>
  if read = unitSymbol ∨ read = registerMarkSymbol ∨
      read = separatorSymbol then
    keepAction (copySeekEndState distance base) .left read
  else if read = scratchEndSymbol then
    keepAction (copyAppendFirstState distance base) .stay read
  else deadAction dead read

private def copyAppendFirstSpec (distance base dead : Nat) : StateSpec :=
    fun read =>
  if read = scratchEndSymbol then
    writeAction (copyAppendSecondState distance base) unitSymbol .left
  else deadAction dead read

private def copyAppendSecondSpec (base : Nat) : StateSpec := fun _read =>
  writeAction base scratchEndSymbol .stay

private def copyRestoreSpec (distance base dead : Nat) : StateSpec :=
    fun read =>
  if read = registerMarkSymbol then
    writeAction (copyRestoreState distance base) unitSymbol .left
  else if read = unitSymbol then
    keepAction (copyRestoreState distance base) .left read
  else if read = separatorSymbol then
    keepAction (copySeekEndDoneState distance base) .left read
  else deadAction dead read

private def copySeekEndDoneSpec
    (distance base next dead : Nat) : StateSpec := fun read =>
  if read = unitSymbol ∨ read = registerMarkSymbol ∨
      read = separatorSymbol then
    keepAction (copySeekEndDoneState distance base) .left read
  else if read = scratchEndSymbol then
    keepAction next .stay read
  else deadAction dead read

/-- Copy the register reached after crossing `distance` newer separators into
the newest destination register.  The source marks are restored exactly. -/
private def copySpecs (distance base next dead : Nat) : List StateSpec :=
  [copyStartSpec base dead] ++
    locateSpecs distance (copyLocateBase base)
      (copyScanState distance base) dead ++
    [copyScanSpec distance base dead,
     copySeekEndSpec distance base dead,
     copyAppendFirstSpec distance base dead,
     copyAppendSecondSpec base,
     copyRestoreSpec distance base dead,
     copySeekEndDoneSpec distance base next dead]

@[simp] private theorem copySpecs_length
    (distance base next dead : Nat) :
    (copySpecs distance base next dead).length = copyStateCount distance := by
  simp [copySpecs, copyStateCount]

private def addOperationStateCount (rightNodes : Nat) : Nat :=
  let leftDistance := rightNodes + 1
  2 + copyStateCount leftDistance + copyStateCount 1

private def addOperationSpecs
    (rightNodes base next dead : Nat) : List StateSpec :=
  let leftDistance := rightNodes + 1
  let leftCopyBase := base + 2
  let rightCopyBase := leftCopyBase + copyStateCount leftDistance
  separatorSpecs base leftCopyBase dead ++
    copySpecs leftDistance leftCopyBase rightCopyBase dead ++
    copySpecs 1 rightCopyBase next dead

@[simp] private theorem addOperationSpecs_length
    (rightNodes base next dead : Nat) :
    (addOperationSpecs rightNodes base next dead).length =
      addOperationStateCount rightNodes := by
  simp [addOperationSpecs, addOperationStateCount]
  omega

private def multiplyLoopStateCount (leftDistance : Nat) : Nat :=
  leftDistance + 13

private def multiplyLocateBase (base : Nat) : Nat := base + 1
private def multiplyScanState (leftDistance base : Nat) : Nat :=
  multiplyLocateBase base + leftDistance
private def multiplySeekCopyEndState (leftDistance base : Nat) : Nat :=
  multiplyScanState leftDistance base + 1
private def multiplyRightCopyBase (leftDistance base : Nat) : Nat :=
  multiplyScanState leftDistance base + 2
private def multiplyRestoreState (leftDistance base : Nat) : Nat :=
  multiplyRightCopyBase leftDistance base + copyStateCount 1
private def multiplySeekEndDoneState (leftDistance base : Nat) : Nat :=
  multiplyRestoreState leftDistance base + 1

private def multiplyStartSpec (base dead : Nat) : StateSpec := fun read =>
  if read = scratchEndSymbol then
    keepAction (multiplyLocateBase base) .right read
  else deadAction dead read

private def multiplyScanSpec
    (leftDistance base dead : Nat) : StateSpec := fun read =>
  if read = registerMarkSymbol then
    keepAction (multiplyScanState leftDistance base) .right read
  else if read = unitSymbol then
    writeAction (multiplySeekCopyEndState leftDistance base)
      registerMarkSymbol .left
  else if read = separatorSymbol then
    keepAction (multiplyRestoreState leftDistance base) .left read
  else deadAction dead read

private def multiplySeekCopyEndSpec
    (leftDistance base dead : Nat) : StateSpec := fun read =>
  if read = unitSymbol ∨ read = registerMarkSymbol ∨
      read = separatorSymbol then
    keepAction (multiplySeekCopyEndState leftDistance base) .left read
  else if read = scratchEndSymbol then
    keepAction (multiplyRightCopyBase leftDistance base) .stay read
  else deadAction dead read

private def multiplyRestoreSpec
    (leftDistance base dead : Nat) : StateSpec := fun read =>
  if read = registerMarkSymbol then
    writeAction (multiplyRestoreState leftDistance base) unitSymbol .left
  else if read = unitSymbol then
    keepAction (multiplyRestoreState leftDistance base) .left read
  else if read = separatorSymbol then
    keepAction (multiplySeekEndDoneState leftDistance base) .left read
  else deadAction dead read

private def multiplySeekEndDoneSpec
    (leftDistance base next dead : Nat) : StateSpec := fun read =>
  if read = unitSymbol ∨ read = registerMarkSymbol ∨
      read = separatorSymbol then
    keepAction (multiplySeekEndDoneState leftDistance base) .left read
  else if read = scratchEndSymbol then
    keepAction next .stay read
  else deadAction dead read

private def multiplyLoopSpecs
    (leftDistance base next dead : Nat) : List StateSpec :=
  [multiplyStartSpec base dead] ++
    locateSpecs leftDistance (multiplyLocateBase base)
      (multiplyScanState leftDistance base) dead ++
    [multiplyScanSpec leftDistance base dead,
     multiplySeekCopyEndSpec leftDistance base dead] ++
    copySpecs 1 (multiplyRightCopyBase leftDistance base) base dead ++
    [multiplyRestoreSpec leftDistance base dead,
     multiplySeekEndDoneSpec leftDistance base next dead]

@[simp] private theorem multiplyLoopSpecs_length
    (leftDistance base next dead : Nat) :
    (multiplyLoopSpecs leftDistance base next dead).length =
      multiplyLoopStateCount leftDistance := by
  simp [multiplyLoopSpecs, multiplyLoopStateCount, copyStateCount]

private def mulOperationStateCount (rightNodes : Nat) : Nat :=
  2 + multiplyLoopStateCount (rightNodes + 1)

private def mulOperationSpecs
    (rightNodes base next dead : Nat) : List StateSpec :=
  let loopBase := base + 2
  separatorSpecs base loopBase dead ++
    multiplyLoopSpecs (rightNodes + 1) loopBase next dead

@[simp] private theorem mulOperationSpecs_length
    (rightNodes base next dead : Nat) :
    (mulOperationSpecs rightNodes base next dead).length =
      mulOperationStateCount rightNodes := by
  simp [mulOperationSpecs, mulOperationStateCount]

/-- Number of generated control states for the complete postorder program. -/
def compilerStateCount : NatPolynomial → Nat
  | .constant value => constantOperationStateCount value
  | .variable => variableOperationStateCount
  | .add left right =>
      compilerStateCount left + compilerStateCount right +
        addOperationStateCount (nodeCount right)
  | .mul left right =>
      compilerStateCount left + compilerStateCount right +
        mulOperationStateCount (nodeCount right)

private def compileSpecs :
    NatPolynomial → Nat → Nat → Nat → List StateSpec
  | .constant value, base, next, dead =>
      constantOperationSpecs value base next dead
  | .variable, base, next, dead =>
      variableOperationSpecs base next dead
  | .add left right, base, next, dead =>
      let rightBase := base + compilerStateCount left
      let operationBase := rightBase + compilerStateCount right
      compileSpecs left base rightBase dead ++
        compileSpecs right rightBase operationBase dead ++
          addOperationSpecs (nodeCount right) operationBase next dead
  | .mul left right, base, next, dead =>
      let rightBase := base + compilerStateCount left
      let operationBase := rightBase + compilerStateCount right
      compileSpecs left base rightBase dead ++
        compileSpecs right rightBase operationBase dead ++
          mulOperationSpecs (nodeCount right) operationBase next dead

@[simp] private theorem compileSpecs_length
    (polynomial : NatPolynomial) (base next dead : Nat) :
    (compileSpecs polynomial base next dead).length =
      compilerStateCount polynomial := by
  induction polynomial generalizing base next with
  | constant value => simp [compileSpecs, compilerStateCount]
  | «variable» => simp [compileSpecs, compilerStateCount]
  | add left right leftIH rightIH =>
      simp [compileSpecs, compilerStateCount, leftIH, rightIH] <;> omega
  | mul left right leftIH rightIH =>
      simp [compileSpecs, compilerStateCount, leftIH, rightIH] <;> omega

/-- Three initialization states, the syntax compiler, and one exact rewind. -/
def stateCount (polynomial : NatPolynomial) : Nat :=
  3 + compilerStateCount polynomial + 1

def acceptState (polynomial : NatPolynomial) : Nat := stateCount polynomial
def rejectState (polynomial : NatPolynomial) : Nat := stateCount polynomial + 1
def deadState (polynomial : NatPolynomial) : Nat := stateCount polynomial + 2

private def initializationStartSpec (dead : Nat) : StateSpec := fun read =>
  if read = WorkSymbol.blank ∨ read = WorkSymbol.zeroBlank ∨
      read = WorkSymbol.oneBlank then
    keepAction 1 .left read
  else deadAction dead read

private def initializationMarkerSpec (dead : Nat) : StateSpec := fun read =>
  if read = leftMarker then keepAction 2 .left read
  else deadAction dead read

private def initializationEndSpec (compileStart : Nat) : StateSpec :=
  fun _read => writeAction compileStart scratchEndSymbol .stay

private def initializationSpecs
    (compileStart dead : Nat) : List StateSpec :=
  [initializationStartSpec dead,
   initializationMarkerSpec dead,
   initializationEndSpec compileStart]

private def rewindSpec (accept dead : Nat) : StateSpec :=
  fun read =>
    if read = scratchEndSymbol ∨ read = unitSymbol ∨
        read = separatorSymbol ∨ read = registerMarkSymbol then
      keepAction (accept - 1) .right read
    else if read = leftMarker then
      keepAction accept .right read
    else deadAction dead read

/-- Resolved finite control table. -/
def stateSpecs (polynomial : NatPolynomial) : List StateSpec :=
  let rewind := 3 + compilerStateCount polynomial
  initializationSpecs 3 (deadState polynomial) ++
    compileSpecs polynomial 3 rewind (deadState polynomial) ++
      [rewindSpec (acceptState polynomial) (deadState polynomial)]

@[simp] theorem stateSpecs_length (polynomial : NatPolynomial) :
    (stateSpecs polynomial).length = stateCount polynomial := by
  simp [stateSpecs, stateCount, initializationSpecs]
  omega

/-- Exact number of literal work rules generated for one polynomial. -/
def ruleCount (polynomial : NatPolynomial) : Nat := 9 * stateCount polynomial

def rules (polynomial : NatPolynomial) : List WorkRule :=
  rulesFrom 0 (stateSpecs polynomial)

def machine (polynomial : NatPolynomial) : WorkMachine :=
  { rules := rules polynomial
    startState := 0
    acceptState := acceptState polynomial
    rejectState := rejectState polynomial }

theorem rules_length (polynomial : NatPolynomial) :
    (rules polynomial).length = ruleCount polynomial := by
  simp [rules, ruleCount, rulesFrom_length]

theorem rules_pairwise_query_distinct (polynomial : NatPolynomial) :
    (rules polynomial).Pairwise (fun left right =>
      (left.sourceState, left.readSymbol) ≠
        (right.sourceState, right.readSymbol)) := by
  exact rulesFrom_pairwise_query_distinct 0 (stateSpecs polynomial)

theorem rule_source_lt_acceptState (polynomial : NatPolynomial)
    (rule : WorkRule) (hMem : rule ∈ (machine polynomial).rules) :
    rule.sourceState < (machine polynomial).acceptState := by
  have hBounds := rulesFrom_source_bounds (base := 0)
    (specs := stateSpecs polynomial) (rule := rule)
    (by simpa [machine, rules] using hMem)
  simpa [machine, acceptState, stateSpecs_length] using hBounds.2

theorem machine_acceptState_ne_rejectState (polynomial : NatPolynomial) :
    (machine polynomial).acceptState ≠ (machine polynomial).rejectState := by
  change stateCount polynomial ≠ stateCount polynomial + 1
  omega

/-! ### Exact table-step and tape infrastructure -/

private def specMachine (specs : List StateSpec)
    (accept reject : Nat) : WorkMachine :=
  { rules := rulesFrom 0 specs
    startState := 0
    acceptState := accept
    rejectState := reject }

private theorem specMachine_step
    (before : List StateSpec) (spec : StateSpec) (after : List StateSpec)
    (accept reject : Nat) (tape : WorkTape)
    (hAccept : before.length ≠ accept)
    (hReject : before.length ≠ reject) :
    workStep? (specMachine (before ++ spec :: after) accept reject)
        { state := before.length, tape := tape } =
      some
        { state := (spec tape.head).targetState
          tape := (tape.write (spec tape.head).writeSymbol).move
            (spec tape.head).move } := by
  have hHalted :
      (specMachine (before ++ spec :: after) accept reject).isHalted
        { state := before.length, tape := tape } = false := by
    unfold WorkMachine.isHalted specMachine
    rw [PipelineSequentialStateNamespace.nat_beq_false_of_ne _ _ hAccept,
      PipelineSequentialStateNamespace.nat_beq_false_of_ne _ _ hReject]
    rfl
  have hFind : findWorkRule
      (specMachine (before ++ spec :: after) accept reject).rules
        before.length tape.head =
      some (ruleOf before.length spec tape.head) := by
    unfold specMachine
    simpa using
      (findWorkRule_rulesFrom_at_append 0 before spec after tape.head)
  have hStep := workStep?_eq_apply_of_find
    (specMachine (before ++ spec :: after) accept reject)
    { state := before.length, tape := tape }
    (ruleOf before.length spec tape.head) hHalted hFind
  simpa [ruleOf, applyWorkRule] using hStep

private def closedSpecMachine (specs : List StateSpec) : WorkMachine :=
  specMachine specs specs.length (specs.length + 1)

private theorem closedSpecMachine_step
    (before : List StateSpec) (spec : StateSpec) (after : List StateSpec)
    (tape : WorkTape) :
    workStep? (closedSpecMachine (before ++ spec :: after))
        { state := before.length, tape := tape } =
      some
        { state := (spec tape.head).targetState
          tape := (tape.write (spec tape.head).writeSymbol).move
            (spec tape.head).move } := by
  unfold closedSpecMachine
  apply specMachine_step
  · simp only [List.length_append, List.length_cons]
    omega
  · simp only [List.length_append, List.length_cons]
    omega

private theorem machine_eq_closedSpecMachine (polynomial : NatPolynomial) :
    machine polynomial = closedSpecMachine (stateSpecs polynomial) := by
  unfold machine closedSpecMachine specMachine rules
  rw [stateSpecs_length]
  rfl

private theorem workRunExact_compose_for (machine : WorkMachine)
    (first second : Nat) (start middle final : WorkConfiguration)
    (hFirst : workRunExact? machine first start = some middle)
    (hSecond : workRunExact? machine second middle = some final) :
    workRunExact? machine (first + second) start = some final := by
  induction first generalizing start with
  | zero =>
      change some start = some middle at hFirst
      have hStart : start = middle := Option.some.inj hFirst
      simpa [hStart] using hSecond
  | succ first ih =>
      cases hStep : workStep? machine start with
      | none =>
          change
            (match workStep? machine start with
             | none => none
             | some next => workRunExact? machine first next) =
              some middle at hFirst
          rw [hStep] at hFirst
          contradiction
      | some next =>
          have hTail : workRunExact? machine first next = some middle := by
            change
              (match workStep? machine start with
               | none => none
               | some result => workRunExact? machine first result) =
                some middle at hFirst
            rw [hStep] at hFirst
            exact hFirst
          rw [Nat.succ_add]
          change
            (match workStep? machine start with
             | none => none
             | some result => workRunExact? machine (first + second) result) =
              some final
          rw [hStep]
          exact ih next hTail

private theorem workRunExact_one_for (machine : WorkMachine)
    (start next : WorkConfiguration)
    (hStep : workStep? machine start = some next) :
    workRunExact? machine 1 start = some next := by
  change
    (match workStep? machine start with
     | none => none
     | some result => some result) = some next
  rw [hStep]

private def endTape (outsideTail word inside : List WorkSymbol) : WorkTape :=
  { left := outsideTail
    head := scratchEndSymbol
    right := word.reverse ++ inside }

private def endConfiguration (state : Nat)
    (outsideTail word inside : List WorkSymbol) : WorkConfiguration :=
  { state := state, tape := endTape outsideTail word inside }

private def pathTape (leftSide : List WorkSymbol) :
    List WorkSymbol → WorkTape
  | [] => { left := leftSide, head := WorkSymbol.blank, right := [] }
  | head :: right => { left := leftSide, head := head, right := right }

@[simp] private theorem endTape_moveRight
    (outsideTail word inside : List WorkSymbol) :
  (endTape outsideTail word inside).moveRight =
      pathTape (scratchEndSymbol :: outsideTail) (word.reverse ++ inside) := by
  cases h : word.reverse ++ inside <;>
    simp [endTape, pathTape, WorkTape.moveRight, h]

private theorem WorkTape.write_eq_self_of_head_eq
    (tape : WorkTape) (symbol : WorkSymbol)
    (hHead : tape.head = symbol) :
    tape.write symbol = tape := by
  cases tape
  cases hHead
  rfl

@[simp] private theorem WorkTape.write_head (tape : WorkTape) :
    tape.write tape.head = tape := by
  cases tape
  rfl

@[simp] private theorem pathTape_moveRight_cons
    (leftSide : List WorkSymbol) (head : WorkSymbol)
    (right : List WorkSymbol) :
    (pathTape leftSide (head :: right)).moveRight =
      pathTape (head :: leftSide) right := by
  cases right <;> rfl

private def sourceWord : BitString → List WorkSymbol
  | [] => [WorkSymbol.blank]
  | bits => bits.map fun bit => dataSymbol (TapeSymbol.ofBool bit)

private def sourceDataSymbol (bit : Bool) : WorkSymbol :=
  dataSymbol (TapeSymbol.ofBool bit)

private def sourceMarkSymbol : Bool → WorkSymbol
  | false => sourceZeroMarkSymbol
  | true => sourceOneMarkSymbol

private def sourceDataSymbols (bits : BitString) : List WorkSymbol :=
  bits.map sourceDataSymbol

private def sourceMarkSymbols (bits : BitString) : List WorkSymbol :=
  bits.map sourceMarkSymbol

@[simp] private theorem sourceDataSymbols_length (bits : BitString) :
    (sourceDataSymbols bits).length = bits.length := by
  simp [sourceDataSymbols]

@[simp] private theorem sourceMarkSymbols_length (bits : BitString) :
    (sourceMarkSymbols bits).length = bits.length := by
  simp [sourceMarkSymbols]

private def leftPathTape (rightSide : List WorkSymbol) :
    List WorkSymbol → WorkTape
  | [] => { left := [], head := WorkSymbol.blank, right := rightSide }
  | head :: left => { left := left, head := head, right := rightSide }

private theorem pathTape_write_moveLeft_of_ne_nil
    (leftSide : List WorkSymbol) (head write : WorkSymbol)
    (right : List WorkSymbol) (hLeft : leftSide ≠ []) :
    ((pathTape leftSide (head :: right)).write write).moveLeft =
      leftPathTape (write :: right) leftSide := by
  cases leftSide with
  | nil => contradiction
  | cons first rest => rfl

@[simp] private theorem leftPathTape_moveLeft_cons
    (rightSide : List WorkSymbol) (head : WorkSymbol)
    (left : List WorkSymbol) :
    (leftPathTape rightSide (head :: left)).moveLeft =
      leftPathTape (head :: rightSide) left := by
  cases left <;> rfl

@[simp] private theorem leftPathTape_write_moveLeft_cons
    (rightSide : List WorkSymbol) (head write : WorkSymbol)
    (left : List WorkSymbol) :
    ((leftPathTape rightSide (head :: left)).write write).moveLeft =
      leftPathTape (write :: rightSide) left := by
  cases left <;> rfl

private def ScratchSymbol (symbol : WorkSymbol) : Prop :=
  symbol = unitSymbol ∨ symbol = separatorSymbol ∨
    symbol = registerMarkSymbol

private theorem registerWord_scratch (values : List Nat) :
    ∀ symbol ∈ registerWord values, ScratchSymbol symbol := by
  induction values with
  | nil => intro symbol hMem; contradiction
  | cons value rest ih =>
      intro symbol hMem
      simp only [registerWord, List.mem_cons, List.mem_append] at hMem
      rcases hMem with hSeparator | hUnits | hRest
      · exact Or.inr (Or.inl hSeparator)
      · have hUnit := List.eq_of_mem_replicate hUnits
        exact Or.inl hUnit
      · exact ih symbol hRest

private theorem scratch_append (left right : List WorkSymbol)
    (hLeft : ∀ symbol ∈ left, ScratchSymbol symbol)
    (hRight : ∀ symbol ∈ right, ScratchSymbol symbol) :
    ∀ symbol ∈ left ++ right, ScratchSymbol symbol := by
  intro symbol hMem
  rw [List.mem_append] at hMem
  cases hMem with
  | inl h => exact hLeft symbol h
  | inr h => exact hRight symbol h

private theorem replicate_unit_scratch (count : Nat) :
    ∀ symbol ∈ List.replicate count unitSymbol, ScratchSymbol symbol := by
  intro symbol hMem
  exact Or.inl (List.eq_of_mem_replicate hMem)

private def workspaceInside (input : BitString)
    (output : List CNFToken) : List WorkSymbol :=
  leftMarker ::
    (sourceWord input ++
      rightMarker ::
        (List.replicate input.length BuilderInputLength.tallySymbol ++
          BuilderTokenAppender.outputRegion output))

private def sourceInside (input : BitString)
    (workspace : List WorkSymbol) : List WorkSymbol :=
  leftMarker :: (sourceWord input ++ rightMarker :: workspace)

private theorem workspaceTape_eq_word (input : BitString)
    (outsideLeft : List WorkSymbol) (output : List CNFToken) :
    BuilderTokenAppender.workspaceTape input outsideLeft output =
      match sourceWord input with
      | [] => WorkTape.blank
      | head :: rest =>
          { left := leftMarker :: outsideLeft
            head := head
            right := rest ++
              rightMarker ::
                (List.replicate input.length BuilderInputLength.tallySymbol ++
                  BuilderTokenAppender.outputRegion output) } := by
  cases input with
  | nil => rfl
  | cons first rest =>
      simp [BuilderTokenAppender.workspaceTape, frameWithGarbage,
        Tape.ofInput, sourceWord]

private theorem appendMany_exact (count base next dead : Nat)
    (specPrefix suffix : List StateSpec)
    (outsideTail word inside : List WorkSymbol)
    (hBase : specPrefix.length = base)
    (hNext : next = base + appendManyStateCount count) :
    workRunExact?
        (closedSpecMachine
          (specPrefix ++ appendManySpecs count base next dead ++ suffix))
        (appendManyStateCount count)
        (endConfiguration base outsideTail word inside) =
      some (endConfiguration next (outsideTail.drop count)
        (word ++ List.replicate count unitSymbol) inside) := by
  induction count generalizing base specPrefix outsideTail word with
  | zero =>
      simp [appendManyStateCount] at hNext
      subst next
      simp [appendManySpecs, appendManyStateCount, endConfiguration]
      rfl
  | succ count ih =>
      let after : Nat := if count = 0 then next else base + 2
      let firstSpec : StateSpec := fun read =>
        if read = scratchEndSymbol then
          writeAction (base + 1) unitSymbol .left
        else deadAction dead read
      let secondSpec : StateSpec := fun _read =>
        writeAction after scratchEndSymbol .stay
      let rest := appendManySpecs count (base + 2) next dead
      let machineSpecs :=
        specPrefix ++ firstSpec :: secondSpec :: rest ++ suffix
      let firstTape :=
        (endTape outsideTail word inside).write unitSymbol |>.moveLeft
      let firstConfig : WorkConfiguration :=
        { state := base + 1, tape := firstTape }
      let afterConfig := endConfiguration after (outsideTail.drop 1)
        (word ++ [unitSymbol]) inside
      have hSpecs :
          specPrefix ++ appendManySpecs (count + 1) base next dead ++ suffix =
            machineSpecs := by
        simp [appendManySpecs, machineSpecs, firstSpec, secondSpec, rest,
          after, List.append_assoc]
      have hFirstStep :
          workStep? (closedSpecMachine machineSpecs)
              (endConfiguration base outsideTail word inside) =
            some firstConfig := by
        have hStep := closedSpecMachine_step specPrefix firstSpec
          (secondSpec :: rest ++ suffix)
          (endTape outsideTail word inside)
        simpa [machineSpecs, endConfiguration, firstConfig, firstTape,
          firstSpec, keepAction, writeAction, scratchEndSymbol, endTape,
          WorkTape.move,
          List.append_assoc, hBase] using hStep
      have hSecondStep :
          workStep? (closedSpecMachine machineSpecs) firstConfig =
            some afterConfig := by
        have hStep := closedSpecMachine_step (specPrefix ++ [firstSpec])
          secondSpec (rest ++ suffix) firstTape
        cases outsideTail <;>
          simpa [machineSpecs, firstConfig, afterConfig, firstTape,
            endConfiguration, endTape, secondSpec, writeAction,
            WorkTape.write, WorkTape.moveLeft, WorkTape.move,
            List.append_assoc,
            hBase] using hStep
      have hFirstExact := workRunExact_one_for
        (closedSpecMachine machineSpecs)
        (endConfiguration base outsideTail word inside) firstConfig hFirstStep
      have hSecondExact := workRunExact_one_for
        (closedSpecMachine machineSpecs) firstConfig afterConfig hSecondStep
      have hTwo := workRunExact_compose_for
        (closedSpecMachine machineSpecs) 1 1
        (endConfiguration base outsideTail word inside)
        firstConfig afterConfig hFirstExact hSecondExact
      have hRestBase :
          (specPrefix ++ [firstSpec, secondSpec]).length = base + 2 := by
        simp [hBase]
      have hRestNext :
          next = base + 2 + appendManyStateCount count := by
        simp [appendManyStateCount] at hNext ⊢
        omega
      have hAfter : after = base + 2 := by
        by_cases hCount : count = 0
        · subst count
          simp [after, appendManyStateCount] at hNext ⊢
          omega
        · simp [after, hCount]
      have hRest := ih (base := base + 2)
        (specPrefix := specPrefix ++ [firstSpec, secondSpec])
        (outsideTail := outsideTail.drop 1)
        (word := word ++ [unitSymbol]) hRestBase hRestNext
      have hAfterConfig : afterConfig =
          endConfiguration (base + 2) (outsideTail.drop 1)
            (word ++ [unitSymbol]) inside := by
        simp [afterConfig, hAfter]
      rw [hAfterConfig] at hTwo
      have hMachine :
          specPrefix ++ [firstSpec, secondSpec] ++ rest ++ suffix =
            machineSpecs := by
        simp [machineSpecs, List.append_assoc]
      rw [hMachine] at hRest
      have hAll := workRunExact_compose_for
        (closedSpecMachine machineSpecs) 2
        (appendManyStateCount count)
        (endConfiguration base outsideTail word inside)
        (endConfiguration (base + 2) (outsideTail.drop 1)
          (word ++ [unitSymbol]) inside)
        (endConfiguration next ((outsideTail.drop 1).drop count)
          ((word ++ [unitSymbol]) ++
            List.replicate count unitSymbol) inside)
        (by simpa using hTwo) hRest
      rw [hSpecs]
      have hSteps : 2 + appendManyStateCount count =
          appendManyStateCount (count + 1) := by
        simp [appendManyStateCount]
        omega
      rw [← hSteps]
      simpa [List.drop_drop, List.replicate_succ, List.append_assoc,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hAll

private theorem separator_exact (base next dead : Nat)
    (specPrefix suffix : List StateSpec)
    (outsideTail word inside : List WorkSymbol)
    (hBase : specPrefix.length = base) :
    workRunExact?
        (closedSpecMachine
          (specPrefix ++ separatorSpecs base next dead ++ suffix))
        2 (endConfiguration base outsideTail word inside) =
      some (endConfiguration next (outsideTail.drop 1)
        (word ++ [separatorSymbol]) inside) := by
  let firstSpec : StateSpec := fun read =>
    if read = scratchEndSymbol then
      writeAction (base + 1) separatorSymbol .left
    else deadAction dead read
  let secondSpec : StateSpec := fun _read =>
    writeAction next scratchEndSymbol .stay
  let machineSpecs := specPrefix ++ firstSpec :: secondSpec :: suffix
  let firstTape :=
    (endTape outsideTail word inside).write separatorSymbol |>.moveLeft
  let firstConfig : WorkConfiguration :=
    { state := base + 1, tape := firstTape }
  let finalConfig := endConfiguration next (outsideTail.drop 1)
    (word ++ [separatorSymbol]) inside
  have hFirstStep :
      workStep? (closedSpecMachine machineSpecs)
          (endConfiguration base outsideTail word inside) =
        some firstConfig := by
    have hStep := closedSpecMachine_step specPrefix firstSpec
      (secondSpec :: suffix) (endTape outsideTail word inside)
    simpa [machineSpecs, endConfiguration, firstConfig, firstTape,
      firstSpec, writeAction, scratchEndSymbol, endTape, WorkTape.move,
      List.append_assoc, hBase] using hStep
  have hSecondStep :
      workStep? (closedSpecMachine machineSpecs) firstConfig =
        some finalConfig := by
    have hStep := closedSpecMachine_step (specPrefix ++ [firstSpec])
      secondSpec suffix firstTape
    cases outsideTail <;>
      simpa [machineSpecs, firstConfig, finalConfig, firstTape,
        endConfiguration, endTape, secondSpec, writeAction,
        WorkTape.write, WorkTape.moveLeft, WorkTape.move,
        List.append_assoc, hBase] using hStep
  have hFirstExact := workRunExact_one_for
    (closedSpecMachine machineSpecs)
    (endConfiguration base outsideTail word inside) firstConfig hFirstStep
  have hSecondExact := workRunExact_one_for
    (closedSpecMachine machineSpecs) firstConfig finalConfig hSecondStep
  have hAll := workRunExact_compose_for
    (closedSpecMachine machineSpecs) 1 1
    (endConfiguration base outsideTail word inside) firstConfig finalConfig
    hFirstExact hSecondExact
  simpa [machineSpecs, finalConfig, separatorSpecs, firstSpec, secondSpec,
    List.append_assoc] using hAll

private theorem constantOperation_exact (value base next dead : Nat)
    (specPrefix suffix : List StateSpec)
    (outsideTail word inside : List WorkSymbol)
    (hBase : specPrefix.length = base)
    (hNext : next = base + constantOperationStateCount value) :
    workRunExact?
        (closedSpecMachine
          (specPrefix ++
            constantOperationSpecs value base next dead ++ suffix))
        (2 + appendManyStateCount value)
        (endConfiguration base outsideTail word inside) =
      some (endConfiguration next (outsideTail.drop (value + 1))
        (word ++ separatorSymbol :: List.replicate value unitSymbol)
        inside) := by
  let appendBase := base + 2
  have hSeparator := separator_exact base appendBase dead specPrefix
    (appendManySpecs value appendBase next dead ++ suffix)
    outsideTail word inside hBase
  have hAppendPrefix :
      (specPrefix ++ separatorSpecs base appendBase dead).length =
        appendBase := by
    simp [appendBase, hBase]
  have hAppendNext :
      next = appendBase + appendManyStateCount value := by
    simp [appendBase, constantOperationStateCount] at hNext ⊢
    omega
  have hAppend := appendMany_exact value appendBase next dead
    (specPrefix ++ separatorSpecs base appendBase dead) suffix
    (outsideTail.drop 1) (word ++ [separatorSymbol]) inside
    hAppendPrefix hAppendNext
  have hMachine :
      specPrefix ++ separatorSpecs base appendBase dead ++
          appendManySpecs value appendBase next dead ++ suffix =
        specPrefix ++ constantOperationSpecs value base next dead ++ suffix := by
    simp [constantOperationSpecs, appendBase, List.append_assoc]
  simp only [List.append_assoc] at hSeparator hAppend hMachine
  rw [hMachine] at hSeparator hAppend
  have hAll := workRunExact_compose_for
    (closedSpecMachine
      (specPrefix ++ constantOperationSpecs value base next dead ++ suffix))
    2 (appendManyStateCount value)
    (endConfiguration base outsideTail word inside)
    (endConfiguration appendBase (outsideTail.drop 1)
      (word ++ [separatorSymbol]) inside)
    (endConfiguration next ((outsideTail.drop 1).drop value)
      ((word ++ [separatorSymbol]) ++
        List.replicate value unitSymbol) inside)
    (by simpa [List.append_assoc] using hSeparator)
    (by simpa [List.append_assoc] using hAppend)
  simpa [List.drop_drop, List.append_assoc, Nat.add_comm,
    Nat.add_left_comm, Nat.add_assoc] using hAll

private theorem sourceStart_step (base next dead : Nat)
    (specPrefix suffix : List StateSpec) (tape : WorkTape)
    (hBase : specPrefix.length = base)
    (hHead : tape.head = scratchEndSymbol) :
    workStep?
        (closedSpecMachine
          (specPrefix ++ sourceCopySpecs base next dead ++ suffix))
        { state := base, tape := tape } =
      some { state := base + 1, tape := tape.moveRight } := by
  have hStep := closedSpecMachine_step specPrefix
    (sourceStartSpec base dead)
    ([sourceSeekMarkerSpec base dead, sourceScanInputSpec base dead,
      sourceSeekEndSpec base dead, sourceAppendFirstSpec base dead,
      sourceAppendSecondSpec base, sourceRestoreInputSpec base dead,
      sourceSeekEndDoneSpec base next dead] ++ suffix) tape
  have hAction : sourceStartSpec base dead tape.head =
      keepAction (base + 1) .right tape.head := by
    simp [sourceStartSpec, hHead]
  rw [hAction] at hStep
  simpa [sourceCopySpecs, keepAction,
    WorkTape.move, List.append_assoc, hBase] using hStep

private theorem sourceSeekMarker_scratch_step
    (base next dead : Nat) (specPrefix suffix : List StateSpec)
    (tape : WorkTape) (hBase : specPrefix.length = base)
    (hScratch : tape.head = unitSymbol ∨ tape.head = separatorSymbol ∨
      tape.head = registerMarkSymbol) :
    workStep?
        (closedSpecMachine
          (specPrefix ++ sourceCopySpecs base next dead ++ suffix))
        { state := base + 1, tape := tape } =
      some { state := base + 1, tape := tape.moveRight } := by
  have hStep := closedSpecMachine_step
    (specPrefix ++ [sourceStartSpec base dead])
    (sourceSeekMarkerSpec base dead)
    ([sourceScanInputSpec base dead, sourceSeekEndSpec base dead,
      sourceAppendFirstSpec base dead, sourceAppendSecondSpec base,
      sourceRestoreInputSpec base dead,
      sourceSeekEndDoneSpec base next dead] ++ suffix) tape
  rcases hScratch with hUnit | hSeparator | hMark
  · have hAction : sourceSeekMarkerSpec base dead tape.head =
        keepAction (base + 1) .right tape.head := by
      simp [sourceSeekMarkerSpec, hUnit]
    rw [hAction] at hStep
    simpa [sourceCopySpecs, keepAction,
      WorkTape.move, List.append_assoc, hBase] using hStep
  · have hAction : sourceSeekMarkerSpec base dead tape.head =
        keepAction (base + 1) .right tape.head := by
      simp [sourceSeekMarkerSpec, hSeparator]
    rw [hAction] at hStep
    simpa [sourceCopySpecs, keepAction, WorkTape.move, List.append_assoc,
      hBase] using hStep
  · have hAction : sourceSeekMarkerSpec base dead tape.head =
        keepAction (base + 1) .right tape.head := by
      simp [sourceSeekMarkerSpec, hMark, registerMarkSymbol_ne_unitSymbol,
        registerMarkSymbol_ne_separatorSymbol]
    rw [hAction] at hStep
    simpa [sourceCopySpecs, keepAction, WorkTape.move,
      List.append_assoc, hBase] using hStep

private theorem sourceSeekMarker_boundary_step
    (base next dead : Nat) (specPrefix suffix : List StateSpec)
    (tape : WorkTape) (hBase : specPrefix.length = base)
    (hHead : tape.head = leftMarker) :
    workStep?
        (closedSpecMachine
          (specPrefix ++ sourceCopySpecs base next dead ++ suffix))
        { state := base + 1, tape := tape } =
      some { state := base + 2, tape := tape.moveRight } := by
  have hStep := closedSpecMachine_step
    (specPrefix ++ [sourceStartSpec base dead])
    (sourceSeekMarkerSpec base dead)
    ([sourceScanInputSpec base dead, sourceSeekEndSpec base dead,
      sourceAppendFirstSpec base dead, sourceAppendSecondSpec base,
      sourceRestoreInputSpec base dead,
      sourceSeekEndDoneSpec base next dead] ++ suffix) tape
  have hAction : sourceSeekMarkerSpec base dead tape.head =
      keepAction (base + 2) .right tape.head := by
    simp [sourceSeekMarkerSpec, hHead,
    unitSymbol, separatorSymbol, registerMarkSymbol, leftMarker,
    WorkSymbol.oneOne, WorkSymbol.zeroOne, WorkSymbol.zeroZero]
  rw [hAction] at hStep
  simpa [sourceCopySpecs, keepAction,
    WorkTape.move, List.append_assoc, hBase] using hStep

private theorem sourceScan_mark_step
    (base next dead : Nat) (specPrefix suffix : List StateSpec)
    (tape : WorkTape) (bit : Bool) (hBase : specPrefix.length = base)
    (hHead : tape.head = sourceMarkSymbol bit) :
    workStep?
        (closedSpecMachine
          (specPrefix ++ sourceCopySpecs base next dead ++ suffix))
        { state := base + 2, tape := tape } =
      some { state := base + 2, tape := tape.moveRight } := by
  have hStep := closedSpecMachine_step
    (specPrefix ++ [sourceStartSpec base dead,
      sourceSeekMarkerSpec base dead])
    (sourceScanInputSpec base dead)
    ([sourceSeekEndSpec base dead, sourceAppendFirstSpec base dead,
      sourceAppendSecondSpec base, sourceRestoreInputSpec base dead,
      sourceSeekEndDoneSpec base next dead] ++ suffix) tape
  have hAction : sourceScanInputSpec base dead tape.head =
      keepAction (base + 2) .right tape.head := by
    cases bit <;> simp [sourceScanInputSpec, sourceMarkSymbol, hHead,
      sourceZeroMarkSymbol, sourceOneMarkSymbol, WorkSymbol.zeroZero,
      WorkSymbol.oneZero]
  rw [hAction] at hStep
  simpa [sourceCopySpecs, keepAction, WorkTape.move,
    List.append_assoc, hBase] using hStep

private theorem sourceScan_data_step
    (base next dead : Nat) (specPrefix suffix : List StateSpec)
    (tape : WorkTape) (bit : Bool) (hBase : specPrefix.length = base)
    (hHead : tape.head = sourceDataSymbol bit) :
    workStep?
        (closedSpecMachine
          (specPrefix ++ sourceCopySpecs base next dead ++ suffix))
        { state := base + 2, tape := tape } =
      some
        { state := base + 3
          tape := (tape.write (sourceMarkSymbol bit)).moveLeft } := by
  have hStep := closedSpecMachine_step
    (specPrefix ++ [sourceStartSpec base dead,
      sourceSeekMarkerSpec base dead])
    (sourceScanInputSpec base dead)
    ([sourceSeekEndSpec base dead, sourceAppendFirstSpec base dead,
      sourceAppendSecondSpec base, sourceRestoreInputSpec base dead,
      sourceSeekEndDoneSpec base next dead] ++ suffix) tape
  cases bit <;>
    simpa [sourceCopySpecs, sourceScanInputSpec, sourceDataSymbol,
      sourceMarkSymbol, sourceZeroMarkSymbol, sourceOneMarkSymbol,
      dataSymbol, TapeSymbol.ofBool, WorkSymbol.zeroBlank,
      WorkSymbol.oneBlank, WorkSymbol.zeroZero, WorkSymbol.oneZero,
      writeAction, WorkTape.move, List.append_assoc, hBase, hHead] using hStep

private theorem sourceScan_finish_step
    (base next dead : Nat) (specPrefix suffix : List StateSpec)
    (tape : WorkTape) (hBase : specPrefix.length = base)
    (hHead : tape.head = rightMarker ∨ tape.head = WorkSymbol.blank) :
    workStep?
        (closedSpecMachine
          (specPrefix ++ sourceCopySpecs base next dead ++ suffix))
        { state := base + 2, tape := tape } =
      some { state := base + 6, tape := tape.moveLeft } := by
  have hStep := closedSpecMachine_step
    (specPrefix ++ [sourceStartSpec base dead,
      sourceSeekMarkerSpec base dead])
    (sourceScanInputSpec base dead)
    ([sourceSeekEndSpec base dead, sourceAppendFirstSpec base dead,
      sourceAppendSecondSpec base, sourceRestoreInputSpec base dead,
      sourceSeekEndDoneSpec base next dead] ++ suffix) tape
  rcases hHead with hRight | hBlank
  · have hAction : sourceScanInputSpec base dead tape.head =
        keepAction (base + 6) .left tape.head := by
      simp [sourceScanInputSpec, hRight, rightMarker,
        sourceZeroMarkSymbol, sourceOneMarkSymbol,
        WorkSymbol.zeroZero, WorkSymbol.oneZero, WorkSymbol.zeroBlank,
        WorkSymbol.oneBlank]
    rw [hAction] at hStep
    simpa [sourceCopySpecs, keepAction, WorkTape.move,
      List.append_assoc, hBase] using hStep
  · have hAction : sourceScanInputSpec base dead tape.head =
        keepAction (base + 6) .left tape.head := by
      simp [sourceScanInputSpec, hBlank, rightMarker,
        sourceZeroMarkSymbol, sourceOneMarkSymbol,
        WorkSymbol.zeroZero, WorkSymbol.oneZero, WorkSymbol.blank,
        WorkSymbol.zeroBlank, WorkSymbol.oneBlank]
    rw [hAction] at hStep
    simpa [sourceCopySpecs, keepAction, WorkTape.move,
      List.append_assoc, hBase] using hStep

private def SourceSeekSymbol (symbol : WorkSymbol) : Prop :=
  symbol = sourceZeroMarkSymbol ∨ symbol = sourceOneMarkSymbol ∨
    symbol = WorkSymbol.zeroBlank ∨ symbol = WorkSymbol.oneBlank ∨
    symbol = leftMarker ∨ symbol = unitSymbol ∨
    symbol = separatorSymbol ∨ symbol = registerMarkSymbol

private theorem sourceSeekEnd_symbol_step
    (base next dead : Nat) (specPrefix suffix : List StateSpec)
    (tape : WorkTape) (hBase : specPrefix.length = base)
    (hSymbol : SourceSeekSymbol tape.head) :
    workStep?
        (closedSpecMachine
          (specPrefix ++ sourceCopySpecs base next dead ++ suffix))
        { state := base + 3, tape := tape } =
      some { state := base + 3, tape := tape.moveLeft } := by
  have hStep := closedSpecMachine_step
    (specPrefix ++ [sourceStartSpec base dead,
      sourceSeekMarkerSpec base dead, sourceScanInputSpec base dead])
    (sourceSeekEndSpec base dead)
    ([sourceAppendFirstSpec base dead, sourceAppendSecondSpec base,
      sourceRestoreInputSpec base dead,
      sourceSeekEndDoneSpec base next dead] ++ suffix) tape
  have hAction : sourceSeekEndSpec base dead tape.head =
      keepAction (base + 3) .left tape.head := by
    rcases hSymbol with h | h | h | h | h | h | h | h <;>
      simp [sourceSeekEndSpec, h]
  rw [hAction] at hStep
  simpa [sourceCopySpecs, keepAction, WorkTape.move,
    List.append_assoc, hBase] using hStep

private theorem sourceSeekEnd_end_step
    (base next dead : Nat) (specPrefix suffix : List StateSpec)
    (tape : WorkTape) (hBase : specPrefix.length = base)
    (hHead : tape.head = scratchEndSymbol) :
    workStep?
        (closedSpecMachine
          (specPrefix ++ sourceCopySpecs base next dead ++ suffix))
        { state := base + 3, tape := tape } =
      some { state := base + 4, tape := tape } := by
  have hStep := closedSpecMachine_step
    (specPrefix ++ [sourceStartSpec base dead,
      sourceSeekMarkerSpec base dead, sourceScanInputSpec base dead])
    (sourceSeekEndSpec base dead)
    ([sourceAppendFirstSpec base dead, sourceAppendSecondSpec base,
      sourceRestoreInputSpec base dead,
      sourceSeekEndDoneSpec base next dead] ++ suffix) tape
  have hAction : sourceSeekEndSpec base dead tape.head =
      keepAction (base + 4) .stay tape.head := by
    simp [sourceSeekEndSpec, hHead, scratchEndSymbol,
      sourceZeroMarkSymbol, sourceOneMarkSymbol, leftMarker,
      unitSymbol, separatorSymbol, registerMarkSymbol,
      WorkSymbol.blankOne, WorkSymbol.zeroZero, WorkSymbol.oneZero,
      WorkSymbol.zeroBlank, WorkSymbol.oneBlank, WorkSymbol.oneOne,
      WorkSymbol.zeroOne]
  rw [hAction] at hStep
  simpa [sourceCopySpecs, keepAction, WorkTape.move,
    List.append_assoc, hBase] using hStep

private theorem sourceAppendFirst_step
    (base next dead : Nat) (specPrefix suffix : List StateSpec)
    (tape : WorkTape) (hBase : specPrefix.length = base)
    (hHead : tape.head = scratchEndSymbol) :
    workStep?
        (closedSpecMachine
          (specPrefix ++ sourceCopySpecs base next dead ++ suffix))
        { state := base + 4, tape := tape } =
      some
        { state := base + 5
          tape := (tape.write unitSymbol).moveLeft } := by
  have hStep := closedSpecMachine_step
    (specPrefix ++ [sourceStartSpec base dead,
      sourceSeekMarkerSpec base dead, sourceScanInputSpec base dead,
      sourceSeekEndSpec base dead])
    (sourceAppendFirstSpec base dead)
    ([sourceAppendSecondSpec base, sourceRestoreInputSpec base dead,
      sourceSeekEndDoneSpec base next dead] ++ suffix) tape
  simpa [sourceCopySpecs, sourceAppendFirstSpec, hHead, writeAction,
    WorkTape.move, List.append_assoc, hBase] using hStep

private theorem sourceAppendSecond_step
    (base next dead : Nat) (specPrefix suffix : List StateSpec)
    (tape : WorkTape) (hBase : specPrefix.length = base) :
    workStep?
        (closedSpecMachine
          (specPrefix ++ sourceCopySpecs base next dead ++ suffix))
        { state := base + 5, tape := tape } =
      some
        { state := base
          tape := tape.write scratchEndSymbol } := by
  have hStep := closedSpecMachine_step
    (specPrefix ++ [sourceStartSpec base dead,
      sourceSeekMarkerSpec base dead, sourceScanInputSpec base dead,
      sourceSeekEndSpec base dead, sourceAppendFirstSpec base dead])
    (sourceAppendSecondSpec base)
    ([sourceRestoreInputSpec base dead,
      sourceSeekEndDoneSpec base next dead] ++ suffix) tape
  simpa [sourceCopySpecs, sourceAppendSecondSpec, writeAction,
    WorkTape.move, List.append_assoc, hBase] using hStep

private theorem sourceRestore_mark_step
    (base next dead : Nat) (specPrefix suffix : List StateSpec)
    (tape : WorkTape) (bit : Bool) (hBase : specPrefix.length = base)
    (hHead : tape.head = sourceMarkSymbol bit) :
    workStep?
        (closedSpecMachine
          (specPrefix ++ sourceCopySpecs base next dead ++ suffix))
        { state := base + 6, tape := tape } =
      some
        { state := base + 6
          tape := (tape.write (sourceDataSymbol bit)).moveLeft } := by
  have hStep := closedSpecMachine_step
    (specPrefix ++ [sourceStartSpec base dead,
      sourceSeekMarkerSpec base dead, sourceScanInputSpec base dead,
      sourceSeekEndSpec base dead, sourceAppendFirstSpec base dead,
      sourceAppendSecondSpec base])
    (sourceRestoreInputSpec base dead)
    ([sourceSeekEndDoneSpec base next dead] ++ suffix) tape
  cases bit <;>
    simpa [sourceCopySpecs, sourceRestoreInputSpec, sourceMarkSymbol,
      sourceDataSymbol, sourceZeroMarkSymbol, sourceOneMarkSymbol,
      dataSymbol, TapeSymbol.ofBool, WorkSymbol.zeroBlank,
      WorkSymbol.oneBlank, WorkSymbol.zeroZero, WorkSymbol.oneZero,
      writeAction, WorkTape.move, List.append_assoc, hBase, hHead] using hStep

private theorem sourceRestore_boundary_step
    (base next dead : Nat) (specPrefix suffix : List StateSpec)
    (tape : WorkTape) (hBase : specPrefix.length = base)
    (hHead : tape.head = leftMarker) :
    workStep?
        (closedSpecMachine
          (specPrefix ++ sourceCopySpecs base next dead ++ suffix))
        { state := base + 6, tape := tape } =
      some { state := base + 7, tape := tape.moveLeft } := by
  have hStep := closedSpecMachine_step
    (specPrefix ++ [sourceStartSpec base dead,
      sourceSeekMarkerSpec base dead, sourceScanInputSpec base dead,
      sourceSeekEndSpec base dead, sourceAppendFirstSpec base dead,
      sourceAppendSecondSpec base])
    (sourceRestoreInputSpec base dead)
    ([sourceSeekEndDoneSpec base next dead] ++ suffix) tape
  have hAction : sourceRestoreInputSpec base dead tape.head =
      keepAction (base + 7) .left tape.head := by
    simp [sourceRestoreInputSpec, hHead, sourceZeroMarkSymbol,
      sourceOneMarkSymbol, leftMarker, WorkSymbol.zeroZero,
      WorkSymbol.oneZero]
  rw [hAction] at hStep
  simpa [sourceCopySpecs, keepAction, WorkTape.move,
    List.append_assoc, hBase] using hStep

private theorem sourceSeekDone_scratch_step
    (base next dead : Nat) (specPrefix suffix : List StateSpec)
    (tape : WorkTape) (hBase : specPrefix.length = base)
    (hScratch : ScratchSymbol tape.head) :
    workStep?
        (closedSpecMachine
          (specPrefix ++ sourceCopySpecs base next dead ++ suffix))
        { state := base + 7, tape := tape } =
      some { state := base + 7, tape := tape.moveLeft } := by
  have hStep := closedSpecMachine_step
    (specPrefix ++ [sourceStartSpec base dead,
      sourceSeekMarkerSpec base dead, sourceScanInputSpec base dead,
      sourceSeekEndSpec base dead, sourceAppendFirstSpec base dead,
      sourceAppendSecondSpec base, sourceRestoreInputSpec base dead])
    (sourceSeekEndDoneSpec base next dead) suffix tape
  have hAction : sourceSeekEndDoneSpec base next dead tape.head =
      keepAction (base + 7) .left tape.head := by
    rcases hScratch with h | h | h <;>
      simp [sourceSeekEndDoneSpec, h]
  rw [hAction] at hStep
  simpa [sourceCopySpecs, keepAction, WorkTape.move,
    List.append_assoc, hBase] using hStep

private theorem sourceSeekDone_end_step
    (base next dead : Nat) (specPrefix suffix : List StateSpec)
    (tape : WorkTape) (hBase : specPrefix.length = base)
    (hHead : tape.head = scratchEndSymbol) :
    workStep?
        (closedSpecMachine
          (specPrefix ++ sourceCopySpecs base next dead ++ suffix))
        { state := base + 7, tape := tape } =
      some { state := next, tape := tape } := by
  have hStep := closedSpecMachine_step
    (specPrefix ++ [sourceStartSpec base dead,
      sourceSeekMarkerSpec base dead, sourceScanInputSpec base dead,
      sourceSeekEndSpec base dead, sourceAppendFirstSpec base dead,
      sourceAppendSecondSpec base, sourceRestoreInputSpec base dead])
    (sourceSeekEndDoneSpec base next dead) suffix tape
  have hAction : sourceSeekEndDoneSpec base next dead tape.head =
      keepAction next .stay tape.head := by
    simp [sourceSeekEndDoneSpec, hHead, scratchEndSymbol,
      unitSymbol, separatorSymbol, registerMarkSymbol,
      WorkSymbol.blankOne, WorkSymbol.oneOne, WorkSymbol.zeroOne,
      WorkSymbol.zeroZero]
  rw [hAction] at hStep
  simpa [sourceCopySpecs, keepAction, WorkTape.move,
    List.append_assoc, hBase] using hStep

private theorem sourceScanMarks_exact
    (base next dead : Nat) (specPrefix suffix : List StateSpec)
    (bits : BitString) (leftSide rightSide : List WorkSymbol)
    (hBase : specPrefix.length = base) :
    workRunExact?
        (closedSpecMachine
          (specPrefix ++ sourceCopySpecs base next dead ++ suffix))
        bits.length
        { state := base + 2
          tape := pathTape leftSide (sourceMarkSymbols bits ++ rightSide) } =
      some
        { state := base + 2
          tape := pathTape
            ((sourceMarkSymbols bits).reverse ++ leftSide) rightSide } := by
  induction bits generalizing leftSide with
  | nil => rfl
  | cons bit rest ih =>
      have hStep := sourceScan_mark_step base next dead specPrefix suffix
        (pathTape leftSide
          (sourceMarkSymbol bit :: sourceMarkSymbols rest ++ rightSide))
        bit hBase rfl
      have hFirst := workRunExact_one_for
        (closedSpecMachine
          (specPrefix ++ sourceCopySpecs base next dead ++ suffix))
        { state := base + 2
          tape := pathTape leftSide
            (sourceMarkSymbol bit :: sourceMarkSymbols rest ++ rightSide) }
        { state := base + 2
          tape := pathTape (sourceMarkSymbol bit :: leftSide)
            (sourceMarkSymbols rest ++ rightSide) }
        (by simpa using hStep)
      have hRest := ih (sourceMarkSymbol bit :: leftSide)
      have hAll := workRunExact_compose_for
        (closedSpecMachine
          (specPrefix ++ sourceCopySpecs base next dead ++ suffix))
        1 rest.length
        { state := base + 2
          tape := pathTape leftSide
            (sourceMarkSymbol bit :: sourceMarkSymbols rest ++ rightSide) }
        { state := base + 2
          tape := pathTape (sourceMarkSymbol bit :: leftSide)
            (sourceMarkSymbols rest ++ rightSide) }
        { state := base + 2
          tape := pathTape
            ((sourceMarkSymbols rest).reverse ++
              sourceMarkSymbol bit :: leftSide) rightSide }
        hFirst hRest
      simpa [sourceMarkSymbols, List.reverse_cons, List.append_assoc,
        Nat.add_comm] using hAll

private theorem sourceSeekEnd_exact
    (base next dead : Nat) (specPrefix suffix : List StateSpec)
    (symbols outsideTail rightSide : List WorkSymbol)
    (hBase : specPrefix.length = base)
    (hSymbols : ∀ symbol ∈ symbols, SourceSeekSymbol symbol) :
    workRunExact?
        (closedSpecMachine
          (specPrefix ++ sourceCopySpecs base next dead ++ suffix))
        (symbols.length + 1)
        { state := base + 3
          tape := leftPathTape rightSide
            (symbols ++ scratchEndSymbol :: outsideTail) } =
      some
        { state := base + 4
          tape :=
            { left := outsideTail
              head := scratchEndSymbol
              right := symbols.reverse ++ rightSide } } := by
  induction symbols generalizing rightSide with
  | nil =>
      have hStep := sourceSeekEnd_end_step base next dead specPrefix suffix
        (leftPathTape rightSide (scratchEndSymbol :: outsideTail))
        hBase rfl
      have hExact := workRunExact_one_for
        (closedSpecMachine
          (specPrefix ++ sourceCopySpecs base next dead ++ suffix))
        { state := base + 3
          tape := leftPathTape rightSide (scratchEndSymbol :: outsideTail) }
        { state := base + 4
          tape := leftPathTape rightSide (scratchEndSymbol :: outsideTail) }
        (by simpa [leftPathTape] using hStep)
      simpa [leftPathTape] using hExact
  | cons first rest ih =>
      have hFirstSymbol := hSymbols first (List.Mem.head rest)
      have hRestSymbols : ∀ symbol ∈ rest, SourceSeekSymbol symbol := by
        intro symbol hMem
        exact hSymbols symbol (List.Mem.tail first hMem)
      have hStep := sourceSeekEnd_symbol_step base next dead specPrefix suffix
        (leftPathTape rightSide
          (first :: rest ++ scratchEndSymbol :: outsideTail))
        hBase hFirstSymbol
      have hFirst := workRunExact_one_for
        (closedSpecMachine
          (specPrefix ++ sourceCopySpecs base next dead ++ suffix))
        { state := base + 3
          tape := leftPathTape rightSide
            (first :: rest ++ scratchEndSymbol :: outsideTail) }
        { state := base + 3
          tape := leftPathTape (first :: rightSide)
            (rest ++ scratchEndSymbol :: outsideTail) }
        (by simpa using hStep)
      have hRest := ih (first :: rightSide) hRestSymbols
      have hAll := workRunExact_compose_for
        (closedSpecMachine
          (specPrefix ++ sourceCopySpecs base next dead ++ suffix))
        1 (rest.length + 1)
        { state := base + 3
          tape := leftPathTape rightSide
            (first :: rest ++ scratchEndSymbol :: outsideTail) }
        { state := base + 3
          tape := leftPathTape (first :: rightSide)
            (rest ++ scratchEndSymbol :: outsideTail) }
        { state := base + 4
          tape :=
            { left := outsideTail
              head := scratchEndSymbol
              right := rest.reverse ++ first :: rightSide } }
        hFirst hRest
      have hSteps : 1 + (rest.length + 1) =
          (first :: rest).length + 1 := by simp; omega
      rw [← hSteps]
      simpa [List.reverse_cons, List.append_assoc] using hAll

private theorem sourceAppend_exact
    (base next dead : Nat) (specPrefix suffix : List StateSpec)
    (outsideTail word inside : List WorkSymbol)
    (hBase : specPrefix.length = base) :
    workRunExact?
        (closedSpecMachine
          (specPrefix ++ sourceCopySpecs base next dead ++ suffix))
        2 (endConfiguration (base + 4) outsideTail word inside) =
      some (endConfiguration base (outsideTail.drop 1)
        (word ++ [unitSymbol]) inside) := by
  let firstTape :=
    (endTape outsideTail word inside).write unitSymbol |>.moveLeft
  let firstConfig : WorkConfiguration :=
    { state := base + 5, tape := firstTape }
  let finalConfig := endConfiguration base (outsideTail.drop 1)
    (word ++ [unitSymbol]) inside
  have hFirstStep := sourceAppendFirst_step base next dead specPrefix suffix
    (endTape outsideTail word inside) hBase rfl
  have hFirst := workRunExact_one_for
    (closedSpecMachine
      (specPrefix ++ sourceCopySpecs base next dead ++ suffix))
    (endConfiguration (base + 4) outsideTail word inside) firstConfig
    (by simpa [endConfiguration, firstConfig, firstTape] using hFirstStep)
  have hSecondStep := sourceAppendSecond_step base next dead specPrefix suffix
    firstTape hBase
  have hSecond := workRunExact_one_for
    (closedSpecMachine
      (specPrefix ++ sourceCopySpecs base next dead ++ suffix))
    firstConfig finalConfig (by
      cases outsideTail <;>
        simpa [firstConfig, finalConfig, firstTape, endConfiguration,
          endTape, WorkTape.write, WorkTape.moveLeft] using hSecondStep)
  have hAll := workRunExact_compose_for
    (closedSpecMachine
      (specPrefix ++ sourceCopySpecs base next dead ++ suffix))
    1 1 (endConfiguration (base + 4) outsideTail word inside)
    firstConfig finalConfig hFirst hSecond
  simpa [finalConfig] using hAll

private theorem sourceRestoreMarks_exact
    (base next dead : Nat) (specPrefix suffix : List StateSpec)
    (bits : BitString) (leftRest rightSide : List WorkSymbol)
    (hBase : specPrefix.length = base) :
    workRunExact?
        (closedSpecMachine
          (specPrefix ++ sourceCopySpecs base next dead ++ suffix))
        bits.length
        { state := base + 6
          tape := leftPathTape rightSide
            (sourceMarkSymbols bits ++ leftRest) } =
      some
        { state := base + 6
          tape := leftPathTape
            (sourceDataSymbols bits.reverse ++ rightSide) leftRest } := by
  induction bits generalizing rightSide with
  | nil => rfl
  | cons bit rest ih =>
      have hStep := sourceRestore_mark_step base next dead specPrefix suffix
        (leftPathTape rightSide
          (sourceMarkSymbol bit :: sourceMarkSymbols rest ++ leftRest))
        bit hBase rfl
      have hFirst := workRunExact_one_for
        (closedSpecMachine
          (specPrefix ++ sourceCopySpecs base next dead ++ suffix))
        { state := base + 6
          tape := leftPathTape rightSide
            (sourceMarkSymbol bit :: sourceMarkSymbols rest ++ leftRest) }
        { state := base + 6
          tape := leftPathTape (sourceDataSymbol bit :: rightSide)
            (sourceMarkSymbols rest ++ leftRest) }
        (by simpa using hStep)
      have hRest := ih (sourceDataSymbol bit :: rightSide)
      have hAll := workRunExact_compose_for
        (closedSpecMachine
          (specPrefix ++ sourceCopySpecs base next dead ++ suffix))
        1 rest.length
        { state := base + 6
          tape := leftPathTape rightSide
            (sourceMarkSymbol bit :: sourceMarkSymbols rest ++ leftRest) }
        { state := base + 6
          tape := leftPathTape (sourceDataSymbol bit :: rightSide)
            (sourceMarkSymbols rest ++ leftRest) }
        { state := base + 6
          tape := leftPathTape
            (sourceDataSymbols rest.reverse ++
              sourceDataSymbol bit :: rightSide) leftRest }
        hFirst hRest
      simpa [sourceMarkSymbols, sourceDataSymbols, List.reverse_cons,
        List.map_append, List.append_assoc, Nat.add_comm] using hAll

private theorem sourceSeekMarker_exact
    (base next dead : Nat) (specPrefix suffix : List StateSpec)
    (symbols leftSide rightSide : List WorkSymbol)
    (hBase : specPrefix.length = base)
    (hScratch : ∀ symbol ∈ symbols,
      symbol = unitSymbol ∨ symbol = separatorSymbol ∨
        symbol = registerMarkSymbol) :
    workRunExact?
        (closedSpecMachine
          (specPrefix ++ sourceCopySpecs base next dead ++ suffix))
        (symbols.length + 1)
        { state := base + 1
          tape := pathTape leftSide (symbols ++ leftMarker :: rightSide) } =
      some
        { state := base + 2
          tape := pathTape
            (leftMarker :: symbols.reverse ++ leftSide) rightSide } := by
  induction symbols generalizing leftSide with
  | nil =>
      have hStep := sourceSeekMarker_boundary_step base next dead
        specPrefix suffix (pathTape leftSide (leftMarker :: rightSide))
        hBase rfl
      have hExact := workRunExact_one_for
        (closedSpecMachine
          (specPrefix ++ sourceCopySpecs base next dead ++ suffix))
        { state := base + 1
          tape := pathTape leftSide (leftMarker :: rightSide) }
        { state := base + 2
          tape := pathTape (leftMarker :: leftSide) rightSide }
        (by simpa using hStep)
      simpa [pathTape] using hExact
  | cons first rest ih =>
      have hFirstAllowed := hScratch first (List.Mem.head rest)
      have hRestAllowed : ∀ symbol ∈ rest,
          symbol = unitSymbol ∨ symbol = separatorSymbol ∨
            symbol = registerMarkSymbol := by
        intro symbol hMem
        exact hScratch symbol (List.Mem.tail first hMem)
      have hStep := sourceSeekMarker_scratch_step base next dead
        specPrefix suffix
        (pathTape leftSide (first :: rest ++ leftMarker :: rightSide))
        hBase hFirstAllowed
      have hFirstExact := workRunExact_one_for
        (closedSpecMachine
          (specPrefix ++ sourceCopySpecs base next dead ++ suffix))
        { state := base + 1
          tape := pathTape leftSide
            (first :: rest ++ leftMarker :: rightSide) }
        { state := base + 1
          tape := pathTape (first :: leftSide)
            (rest ++ leftMarker :: rightSide) }
        (by simpa using hStep)
      have hRest := ih (first :: leftSide) hRestAllowed
      have hAll := workRunExact_compose_for
        (closedSpecMachine
          (specPrefix ++ sourceCopySpecs base next dead ++ suffix))
        1 (rest.length + 1)
        { state := base + 1
          tape := pathTape leftSide
            (first :: rest ++ leftMarker :: rightSide) }
        { state := base + 1
          tape := pathTape (first :: leftSide)
            (rest ++ leftMarker :: rightSide) }
        { state := base + 2
          tape := pathTape
            (leftMarker :: rest.reverse ++ first :: leftSide) rightSide }
        hFirstExact hRest
      have hSteps : 1 + (rest.length + 1) =
          (first :: rest).length + 1 := by simp; omega
      rw [← hSteps]
      simpa [List.reverse_cons, List.append_assoc] using hAll

private theorem sourceSeekDone_exact
    (base next dead : Nat) (specPrefix suffix : List StateSpec)
    (symbols outsideTail rightSide : List WorkSymbol)
    (hBase : specPrefix.length = base)
    (hScratch : ∀ symbol ∈ symbols, ScratchSymbol symbol) :
    workRunExact?
        (closedSpecMachine
          (specPrefix ++ sourceCopySpecs base next dead ++ suffix))
        (symbols.length + 1)
        { state := base + 7
          tape := leftPathTape rightSide
            (symbols ++ scratchEndSymbol :: outsideTail) } =
      some
        { state := next
          tape :=
            { left := outsideTail
              head := scratchEndSymbol
              right := symbols.reverse ++ rightSide } } := by
  induction symbols generalizing rightSide with
  | nil =>
      have hStep := sourceSeekDone_end_step base next dead specPrefix suffix
        (leftPathTape rightSide (scratchEndSymbol :: outsideTail))
        hBase rfl
      have hExact := workRunExact_one_for
        (closedSpecMachine
          (specPrefix ++ sourceCopySpecs base next dead ++ suffix))
        { state := base + 7
          tape := leftPathTape rightSide (scratchEndSymbol :: outsideTail) }
        { state := next
          tape := leftPathTape rightSide (scratchEndSymbol :: outsideTail) }
        (by simpa [leftPathTape] using hStep)
      simpa [leftPathTape] using hExact
  | cons first rest ih =>
      have hFirstScratch := hScratch first (List.Mem.head rest)
      have hRestScratch : ∀ symbol ∈ rest, ScratchSymbol symbol := by
        intro symbol hMem
        exact hScratch symbol (List.Mem.tail first hMem)
      have hStep := sourceSeekDone_scratch_step base next dead
        specPrefix suffix
        (leftPathTape rightSide
          (first :: rest ++ scratchEndSymbol :: outsideTail))
        hBase hFirstScratch
      have hFirst := workRunExact_one_for
        (closedSpecMachine
          (specPrefix ++ sourceCopySpecs base next dead ++ suffix))
        { state := base + 7
          tape := leftPathTape rightSide
            (first :: rest ++ scratchEndSymbol :: outsideTail) }
        { state := base + 7
          tape := leftPathTape (first :: rightSide)
            (rest ++ scratchEndSymbol :: outsideTail) }
        (by simpa using hStep)
      have hRest := ih (first :: rightSide) hRestScratch
      have hAll := workRunExact_compose_for
        (closedSpecMachine
          (specPrefix ++ sourceCopySpecs base next dead ++ suffix))
        1 (rest.length + 1)
        { state := base + 7
          tape := leftPathTape rightSide
            (first :: rest ++ scratchEndSymbol :: outsideTail) }
        { state := base + 7
          tape := leftPathTape (first :: rightSide)
            (rest ++ scratchEndSymbol :: outsideTail) }
        { state := next
          tape :=
            { left := outsideTail
              head := scratchEndSymbol
              right := rest.reverse ++ first :: rightSide } }
        hFirst hRest
      have hSteps : 1 + (rest.length + 1) =
          (first :: rest).length + 1 := by simp; omega
      rw [← hSteps]
      simpa [List.reverse_cons, List.append_assoc] using hAll

private def sourceIterationSteps (wordLength processedLength : Nat) : Nat :=
  2 * wordLength + 2 * processedLength + 7

private def sourceFinishSteps (wordLength processedLength : Nat) : Nat :=
  2 * wordLength + 2 * processedLength + 5

private def sourceCopyLoopSteps : Nat → Nat → Nat → Nat
  | wordLength, processedLength, 0 =>
      sourceFinishSteps wordLength processedLength
  | wordLength, processedLength, remaining + 1 =>
      sourceIterationSteps wordLength processedLength +
        sourceCopyLoopSteps (wordLength + 1) (processedLength + 1) remaining

private def sourceCopySteps (wordLength inputLength : Nat) : Nat :=
  sourceCopyLoopSteps wordLength 0 inputLength

private theorem sourceCopy_iteration_exact
    (base next dead : Nat) (specPrefix suffix : List StateSpec)
    (processed : BitString) (bit : Bool) (remaining : BitString)
    (outsideTail word workspace : List WorkSymbol)
    (hBase : specPrefix.length = base)
    (hScratch : ∀ symbol ∈ word, ScratchSymbol symbol) :
    workRunExact?
        (closedSpecMachine
          (specPrefix ++ sourceCopySpecs base next dead ++ suffix))
        (sourceIterationSteps word.length processed.length)
        (endConfiguration base outsideTail word
          (leftMarker ::
            (sourceMarkSymbols processed ++
              sourceDataSymbol bit ::
                (sourceDataSymbols remaining ++ rightMarker :: workspace)))) =
      some
        (endConfiguration base (outsideTail.drop 1)
          (word ++ [unitSymbol])
          (leftMarker ::
            (sourceMarkSymbols (processed ++ [bit]) ++
              sourceDataSymbols remaining ++ rightMarker :: workspace))) := by
  let machine := closedSpecMachine
    (specPrefix ++ sourceCopySpecs base next dead ++ suffix)
  let initialInside :=
    leftMarker ::
      (sourceMarkSymbols processed ++
        sourceDataSymbol bit ::
          (sourceDataSymbols remaining ++ rightMarker :: workspace))
  let markedInside :=
    leftMarker ::
      (sourceMarkSymbols (processed ++ [bit]) ++
        sourceDataSymbols remaining ++ rightMarker :: workspace)
  have hStartStep := sourceStart_step base next dead specPrefix suffix
    (endTape outsideTail word initialInside) hBase rfl
  have hStart := workRunExact_one_for machine
    (endConfiguration base outsideTail word initialInside)
    { state := base + 1
      tape := (endTape outsideTail word initialInside).moveRight }
    (by simpa [machine, endConfiguration] using hStartStep)
  have hSeek := sourceSeekMarker_exact base next dead specPrefix suffix
    word.reverse (scratchEndSymbol :: outsideTail)
    (sourceMarkSymbols processed ++
      sourceDataSymbol bit ::
        (sourceDataSymbols remaining ++ rightMarker :: workspace))
    hBase (by
      intro symbol hMem
      exact hScratch symbol (by simpa using hMem))
  have hStartSeek := workRunExact_compose_for machine 1
    (word.reverse.length + 1)
    (endConfiguration base outsideTail word initialInside)
    { state := base + 1
      tape := (endTape outsideTail word initialInside).moveRight }
    { state := base + 2
      tape := pathTape
        (leftMarker :: word ++ scratchEndSymbol :: outsideTail)
        (sourceMarkSymbols processed ++
          sourceDataSymbol bit ::
            (sourceDataSymbols remaining ++ rightMarker :: workspace)) }
    hStart (by
      simpa [machine, initialInside, List.append_assoc] using hSeek)
  have hMarks := sourceScanMarks_exact base next dead specPrefix suffix
    processed (leftMarker :: word ++ scratchEndSymbol :: outsideTail)
    (sourceDataSymbol bit ::
      (sourceDataSymbols remaining ++ rightMarker :: workspace)) hBase
  have hThroughMarks := workRunExact_compose_for machine
    (1 + (word.reverse.length + 1)) processed.length
    (endConfiguration base outsideTail word initialInside)
    { state := base + 2
      tape := pathTape
        (leftMarker :: word ++ scratchEndSymbol :: outsideTail)
        (sourceMarkSymbols processed ++
          sourceDataSymbol bit ::
            (sourceDataSymbols remaining ++ rightMarker :: workspace)) }
    { state := base + 2
      tape := pathTape
        ((sourceMarkSymbols processed).reverse ++
          leftMarker :: word ++ scratchEndSymbol :: outsideTail)
        (sourceDataSymbol bit ::
          (sourceDataSymbols remaining ++ rightMarker :: workspace)) }
    hStartSeek (by simpa [machine, List.append_assoc] using hMarks)
  have hDataStep := sourceScan_data_step base next dead specPrefix suffix
    (pathTape
      ((sourceMarkSymbols processed).reverse ++
        leftMarker :: word ++ scratchEndSymbol :: outsideTail)
      (sourceDataSymbol bit ::
        (sourceDataSymbols remaining ++ rightMarker :: workspace)))
    bit hBase rfl
  have hDataLeftNe :
      (sourceMarkSymbols processed).reverse ++
        leftMarker :: word ++ scratchEndSymbol :: outsideTail ≠ [] := by
    simp
  have hDataTape := pathTape_write_moveLeft_of_ne_nil
    ((sourceMarkSymbols processed).reverse ++
      leftMarker :: word ++ scratchEndSymbol :: outsideTail)
    (sourceDataSymbol bit) (sourceMarkSymbol bit)
    (sourceDataSymbols remaining ++ rightMarker :: workspace) hDataLeftNe
  rw [hDataTape] at hDataStep
  have hData := workRunExact_one_for machine
    { state := base + 2
      tape := pathTape
        ((sourceMarkSymbols processed).reverse ++
          leftMarker :: word ++ scratchEndSymbol :: outsideTail)
        (sourceDataSymbol bit ::
          (sourceDataSymbols remaining ++ rightMarker :: workspace)) }
    { state := base + 3
      tape := leftPathTape
        (sourceMarkSymbol bit ::
          (sourceDataSymbols remaining ++ rightMarker :: workspace))
        ((sourceMarkSymbols processed).reverse ++
          leftMarker :: word ++ scratchEndSymbol :: outsideTail) }
    (by simpa [machine] using hDataStep)
  have hThroughData := workRunExact_compose_for machine
    ((1 + (word.reverse.length + 1)) + processed.length) 1
    (endConfiguration base outsideTail word initialInside)
    { state := base + 2
      tape := pathTape
        ((sourceMarkSymbols processed).reverse ++
          leftMarker :: word ++ scratchEndSymbol :: outsideTail)
        (sourceDataSymbol bit ::
          (sourceDataSymbols remaining ++ rightMarker :: workspace)) }
    { state := base + 3
      tape := leftPathTape
        (sourceMarkSymbol bit ::
          (sourceDataSymbols remaining ++ rightMarker :: workspace))
        ((sourceMarkSymbols processed).reverse ++
          leftMarker :: word ++ scratchEndSymbol :: outsideTail) }
    hThroughMarks hData
  let seekSymbols :=
    (sourceMarkSymbols processed).reverse ++ leftMarker :: word
  have hSeekSymbols : ∀ symbol ∈ seekSymbols, SourceSeekSymbol symbol := by
    intro symbol hMem
    simp only [seekSymbols, List.mem_append, List.mem_cons] at hMem
    rcases hMem with hMarksMem | hMarker | hWordMem
    · have hOriginal : symbol ∈ sourceMarkSymbols processed := by
        simpa using hMarksMem
      rcases List.mem_map.mp hOriginal with ⟨sourceBit, _hBit, hSymbol⟩
      subst symbol
      cases sourceBit
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hMarker))))
    · rcases hScratch symbol hWordMem with hUnit | hSeparator | hMark
      · exact Or.inr (Or.inr (Or.inr (Or.inr
          (Or.inr (Or.inl hUnit)))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr
          (Or.inr (Or.inr (Or.inl hSeparator))))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr
          (Or.inr (Or.inr (Or.inr hMark))))))
  have hSeekEnd := sourceSeekEnd_exact base next dead specPrefix suffix
    seekSymbols outsideTail
    (sourceMarkSymbol bit ::
      (sourceDataSymbols remaining ++ rightMarker :: workspace))
    hBase hSeekSymbols
  have hBeforeAppend := workRunExact_compose_for machine
    (((1 + (word.reverse.length + 1)) + processed.length) + 1)
    (seekSymbols.length + 1)
    (endConfiguration base outsideTail word initialInside)
    { state := base + 3
      tape := leftPathTape
        (sourceMarkSymbol bit ::
          (sourceDataSymbols remaining ++ rightMarker :: workspace))
        (seekSymbols ++ scratchEndSymbol :: outsideTail) }
    (endConfiguration (base + 4) outsideTail word markedInside)
    (by simpa [seekSymbols] using hThroughData)
    (by
      simpa [machine, seekSymbols, markedInside, endConfiguration, endTape,
        sourceMarkSymbols, List.map_append, List.append_assoc] using hSeekEnd)
  have hAppend := sourceAppend_exact base next dead specPrefix suffix
    outsideTail word markedInside hBase
  have hAll := workRunExact_compose_for machine
    ((((1 + (word.reverse.length + 1)) + processed.length) + 1) +
      (seekSymbols.length + 1)) 2
    (endConfiguration base outsideTail word initialInside)
    (endConfiguration (base + 4) outsideTail word markedInside)
    (endConfiguration base (outsideTail.drop 1)
      (word ++ [unitSymbol]) markedInside)
    hBeforeAppend hAppend
  have hCost :
      ((((1 + (word.reverse.length + 1)) + processed.length) + 1) +
          (seekSymbols.length + 1)) + 2 =
        sourceIterationSteps word.length processed.length := by
    simp [seekSymbols, sourceIterationSteps]
    omega
  rw [← hCost]
  simpa [machine, initialInside, markedInside, seekSymbols,
    sourceMarkSymbols, List.map_append, List.append_assoc] using hAll

private theorem sourceCopy_finish_bits_exact
    (base next dead : Nat) (specPrefix suffix : List StateSpec)
    (processed : BitString) (outsideTail word workspace : List WorkSymbol)
    (hBase : specPrefix.length = base)
    (hScratch : ∀ symbol ∈ word, ScratchSymbol symbol) :
    workRunExact?
        (closedSpecMachine
          (specPrefix ++ sourceCopySpecs base next dead ++ suffix))
        (sourceFinishSteps word.length processed.length)
        (endConfiguration base outsideTail word
          (leftMarker ::
            (sourceMarkSymbols processed ++ rightMarker :: workspace))) =
      some
        (endConfiguration next outsideTail word
          (leftMarker ::
            (sourceDataSymbols processed ++ rightMarker :: workspace))) := by
  let machine := closedSpecMachine
    (specPrefix ++ sourceCopySpecs base next dead ++ suffix)
  let markedInside := leftMarker ::
    (sourceMarkSymbols processed ++ rightMarker :: workspace)
  let restoredInside := leftMarker ::
    (sourceDataSymbols processed ++ rightMarker :: workspace)
  have hStartStep := sourceStart_step base next dead specPrefix suffix
    (endTape outsideTail word markedInside) hBase rfl
  have hStart := workRunExact_one_for machine
    (endConfiguration base outsideTail word markedInside)
    { state := base + 1
      tape := (endTape outsideTail word markedInside).moveRight }
    (by simpa [machine, endConfiguration] using hStartStep)
  have hSeek := sourceSeekMarker_exact base next dead specPrefix suffix
    word.reverse (scratchEndSymbol :: outsideTail)
    (sourceMarkSymbols processed ++ rightMarker :: workspace)
    hBase (by
      intro symbol hMem
      exact hScratch symbol (by simpa using hMem))
  have hStartSeek := workRunExact_compose_for machine 1
    (word.reverse.length + 1)
    (endConfiguration base outsideTail word markedInside)
    { state := base + 1
      tape := (endTape outsideTail word markedInside).moveRight }
    { state := base + 2
      tape := pathTape
        (leftMarker :: word ++ scratchEndSymbol :: outsideTail)
        (sourceMarkSymbols processed ++ rightMarker :: workspace) }
    hStart (by
      simpa [machine, markedInside, List.append_assoc] using hSeek)
  have hMarks := sourceScanMarks_exact base next dead specPrefix suffix
    processed (leftMarker :: word ++ scratchEndSymbol :: outsideTail)
    (rightMarker :: workspace) hBase
  have hThroughMarks := workRunExact_compose_for machine
    (1 + (word.reverse.length + 1)) processed.length
    (endConfiguration base outsideTail word markedInside)
    { state := base + 2
      tape := pathTape
        (leftMarker :: word ++ scratchEndSymbol :: outsideTail)
        (sourceMarkSymbols processed ++ rightMarker :: workspace) }
    { state := base + 2
      tape := pathTape
        ((sourceMarkSymbols processed).reverse ++
          leftMarker :: word ++ scratchEndSymbol :: outsideTail)
        (rightMarker :: workspace) }
    hStartSeek (by simpa [machine, List.append_assoc] using hMarks)
  have hFinishStep := sourceScan_finish_step base next dead specPrefix suffix
    (pathTape
      ((sourceMarkSymbols processed).reverse ++
        leftMarker :: word ++ scratchEndSymbol :: outsideTail)
      (rightMarker :: workspace)) hBase (Or.inl rfl)
  have hFinish := workRunExact_one_for machine
    { state := base + 2
      tape := pathTape
        ((sourceMarkSymbols processed).reverse ++
          leftMarker :: word ++ scratchEndSymbol :: outsideTail)
        (rightMarker :: workspace) }
    { state := base + 6
      tape := leftPathTape (rightMarker :: workspace)
        ((sourceMarkSymbols processed).reverse ++
          leftMarker :: word ++ scratchEndSymbol :: outsideTail) }
    (by
      have hLeftNe :
          (sourceMarkSymbols processed).reverse ++
            leftMarker :: word ++ scratchEndSymbol :: outsideTail ≠ [] := by
        simp
      have hTape := pathTape_write_moveLeft_of_ne_nil
        ((sourceMarkSymbols processed).reverse ++
          leftMarker :: word ++ scratchEndSymbol :: outsideTail)
        rightMarker rightMarker workspace hLeftNe
      rw [WorkTape.write_eq_self_of_head_eq _ rightMarker rfl] at hTape
      rw [hTape] at hFinishStep
      simpa [machine] using hFinishStep)
  have hBeforeRestore := workRunExact_compose_for machine
    ((1 + (word.reverse.length + 1)) + processed.length) 1
    (endConfiguration base outsideTail word markedInside)
    { state := base + 2
      tape := pathTape
        ((sourceMarkSymbols processed).reverse ++
          leftMarker :: word ++ scratchEndSymbol :: outsideTail)
        (rightMarker :: workspace) }
    { state := base + 6
      tape := leftPathTape (rightMarker :: workspace)
        ((sourceMarkSymbols processed).reverse ++
          leftMarker :: word ++ scratchEndSymbol :: outsideTail) }
    hThroughMarks hFinish
  have hRestore := sourceRestoreMarks_exact base next dead specPrefix suffix
    processed.reverse (leftMarker :: word ++ scratchEndSymbol :: outsideTail)
    (rightMarker :: workspace) hBase
  have hThroughRestore := workRunExact_compose_for machine
    (((1 + (word.reverse.length + 1)) + processed.length) + 1)
    processed.length
    (endConfiguration base outsideTail word markedInside)
    { state := base + 6
      tape := leftPathTape (rightMarker :: workspace)
        ((sourceMarkSymbols processed).reverse ++
          leftMarker :: word ++ scratchEndSymbol :: outsideTail) }
    { state := base + 6
      tape := leftPathTape
        (sourceDataSymbols processed ++ rightMarker :: workspace)
        (leftMarker :: word ++ scratchEndSymbol :: outsideTail) }
    hBeforeRestore (by
      simpa [machine, sourceMarkSymbols, sourceDataSymbols,
        List.map_reverse] using hRestore)
  have hBoundaryStep := sourceRestore_boundary_step base next dead
    specPrefix suffix
    (leftPathTape
      (sourceDataSymbols processed ++ rightMarker :: workspace)
      (leftMarker :: word ++ scratchEndSymbol :: outsideTail)) hBase rfl
  have hBoundary := workRunExact_one_for machine
    { state := base + 6
      tape := leftPathTape
        (sourceDataSymbols processed ++ rightMarker :: workspace)
        (leftMarker :: word ++ scratchEndSymbol :: outsideTail) }
    { state := base + 7
      tape := leftPathTape
        (leftMarker :: sourceDataSymbols processed ++ rightMarker :: workspace)
        (word ++ scratchEndSymbol :: outsideTail) }
    (by simpa [machine] using hBoundaryStep)
  have hBeforeDone := workRunExact_compose_for machine
    ((((1 + (word.reverse.length + 1)) + processed.length) + 1) +
      processed.length) 1
    (endConfiguration base outsideTail word markedInside)
    { state := base + 6
      tape := leftPathTape
        (sourceDataSymbols processed ++ rightMarker :: workspace)
        (leftMarker :: word ++ scratchEndSymbol :: outsideTail) }
    { state := base + 7
      tape := leftPathTape
        (leftMarker :: sourceDataSymbols processed ++ rightMarker :: workspace)
        (word ++ scratchEndSymbol :: outsideTail) }
    hThroughRestore hBoundary
  have hDone := sourceSeekDone_exact base next dead specPrefix suffix
    word outsideTail
    (leftMarker :: sourceDataSymbols processed ++ rightMarker :: workspace)
    hBase hScratch
  have hAll := workRunExact_compose_for machine
    (((((1 + (word.reverse.length + 1)) + processed.length) + 1) +
      processed.length) + 1) (word.length + 1)
    (endConfiguration base outsideTail word markedInside)
    { state := base + 7
      tape := leftPathTape
        (leftMarker :: sourceDataSymbols processed ++ rightMarker :: workspace)
        (word ++ scratchEndSymbol :: outsideTail) }
    (endConfiguration next outsideTail word restoredInside)
    hBeforeDone (by
      simpa [machine, restoredInside, endConfiguration, endTape,
        List.append_assoc] using hDone)
  have hCost :
      (((((1 + (word.reverse.length + 1)) + processed.length) + 1) +
          processed.length) + 1) + (word.length + 1) =
        sourceFinishSteps word.length processed.length := by
    simp [sourceFinishSteps]
    omega
  rw [← hCost]
  simpa [machine, markedInside, restoredInside] using hAll

private theorem sourceCopy_finish_empty_exact
    (base next dead : Nat) (specPrefix suffix : List StateSpec)
    (outsideTail word workspace : List WorkSymbol)
    (hBase : specPrefix.length = base)
    (hScratch : ∀ symbol ∈ word, ScratchSymbol symbol) :
    workRunExact?
        (closedSpecMachine
          (specPrefix ++ sourceCopySpecs base next dead ++ suffix))
        (sourceFinishSteps word.length 0)
        (endConfiguration base outsideTail word
          (leftMarker :: WorkSymbol.blank :: rightMarker :: workspace)) =
      some
        (endConfiguration next outsideTail word
          (leftMarker :: WorkSymbol.blank :: rightMarker :: workspace)) := by
  let machine := closedSpecMachine
    (specPrefix ++ sourceCopySpecs base next dead ++ suffix)
  let inside := leftMarker :: WorkSymbol.blank :: rightMarker :: workspace
  have hStartStep := sourceStart_step base next dead specPrefix suffix
    (endTape outsideTail word inside) hBase rfl
  have hStart := workRunExact_one_for machine
    (endConfiguration base outsideTail word inside)
    { state := base + 1, tape := (endTape outsideTail word inside).moveRight }
    (by simpa [machine, endConfiguration] using hStartStep)
  have hSeek := sourceSeekMarker_exact base next dead specPrefix suffix
    word.reverse (scratchEndSymbol :: outsideTail)
    ([WorkSymbol.blank, rightMarker] ++ workspace)
    hBase (by
      intro symbol hMem
      exact hScratch symbol (by simpa using hMem))
  have hStartSeek := workRunExact_compose_for machine 1
    (word.reverse.length + 1)
    (endConfiguration base outsideTail word inside)
    { state := base + 1, tape := (endTape outsideTail word inside).moveRight }
    { state := base + 2
      tape := pathTape (leftMarker :: word ++ scratchEndSymbol :: outsideTail)
        (WorkSymbol.blank :: rightMarker :: workspace) }
    hStart (by simpa [machine, inside, List.append_assoc] using hSeek)
  have hFinishStep := sourceScan_finish_step base next dead specPrefix suffix
    (pathTape (leftMarker :: word ++ scratchEndSymbol :: outsideTail)
      (WorkSymbol.blank :: rightMarker :: workspace))
    hBase (Or.inr rfl)
  have hFinish := workRunExact_one_for machine
    { state := base + 2
      tape := pathTape (leftMarker :: word ++ scratchEndSymbol :: outsideTail)
        (WorkSymbol.blank :: rightMarker :: workspace) }
    { state := base + 6
      tape := leftPathTape
        (WorkSymbol.blank :: rightMarker :: workspace)
        (leftMarker :: word ++ scratchEndSymbol :: outsideTail) }
    (by
      have hLeftNe : leftMarker :: word ++ scratchEndSymbol :: outsideTail ≠
          [] := by simp
      have hTape := pathTape_write_moveLeft_of_ne_nil
        (leftMarker :: word ++ scratchEndSymbol :: outsideTail)
        WorkSymbol.blank WorkSymbol.blank (rightMarker :: workspace) hLeftNe
      rw [WorkTape.write_eq_self_of_head_eq _ WorkSymbol.blank rfl] at hTape
      rw [hTape] at hFinishStep
      simpa [machine] using hFinishStep)
  have hBeforeBoundary := workRunExact_compose_for machine
    (1 + (word.reverse.length + 1)) 1
    (endConfiguration base outsideTail word inside)
    { state := base + 2
      tape := pathTape (leftMarker :: word ++ scratchEndSymbol :: outsideTail)
        (WorkSymbol.blank :: rightMarker :: workspace) }
    { state := base + 6
      tape := leftPathTape
        (WorkSymbol.blank :: rightMarker :: workspace)
        (leftMarker :: word ++ scratchEndSymbol :: outsideTail) }
    hStartSeek hFinish
  have hBoundaryStep := sourceRestore_boundary_step base next dead
    specPrefix suffix
    (leftPathTape (WorkSymbol.blank :: rightMarker :: workspace)
      (leftMarker :: word ++ scratchEndSymbol :: outsideTail)) hBase rfl
  have hBoundary := workRunExact_one_for machine
    { state := base + 6
      tape := leftPathTape (WorkSymbol.blank :: rightMarker :: workspace)
        (leftMarker :: word ++ scratchEndSymbol :: outsideTail) }
    { state := base + 7
      tape := leftPathTape
        (leftMarker :: WorkSymbol.blank :: rightMarker :: workspace)
        (word ++ scratchEndSymbol :: outsideTail) }
    (by simpa [machine] using hBoundaryStep)
  have hBeforeDone := workRunExact_compose_for machine
    ((1 + (word.reverse.length + 1)) + 1) 1
    (endConfiguration base outsideTail word inside)
    { state := base + 6
      tape := leftPathTape (WorkSymbol.blank :: rightMarker :: workspace)
        (leftMarker :: word ++ scratchEndSymbol :: outsideTail) }
    { state := base + 7
      tape := leftPathTape
        (leftMarker :: WorkSymbol.blank :: rightMarker :: workspace)
        (word ++ scratchEndSymbol :: outsideTail) }
    hBeforeBoundary hBoundary
  have hDone := sourceSeekDone_exact base next dead specPrefix suffix
    word outsideTail inside hBase hScratch
  have hAll := workRunExact_compose_for machine
    (((1 + (word.reverse.length + 1)) + 1) + 1) (word.length + 1)
    (endConfiguration base outsideTail word inside)
    { state := base + 7
      tape := leftPathTape inside (word ++ scratchEndSymbol :: outsideTail) }
    (endConfiguration next outsideTail word inside)
    (by simpa [inside] using hBeforeDone)
    (by simpa [machine, inside, endConfiguration, endTape,
      List.append_assoc] using hDone)
  have hCost :
      ((((1 + (word.reverse.length + 1)) + 1) + 1) +
          (word.length + 1)) = sourceFinishSteps word.length 0 := by
    simp [sourceFinishSteps]
    omega
  rw [← hCost]
  simpa [machine, inside] using hAll

private theorem sourceCopy_loop_exact
    (base next dead : Nat) (specPrefix suffix : List StateSpec)
    (processed remaining : BitString)
    (outsideTail word workspace : List WorkSymbol)
    (hBase : specPrefix.length = base)
    (hScratch : ∀ symbol ∈ word, ScratchSymbol symbol) :
    workRunExact?
        (closedSpecMachine
          (specPrefix ++ sourceCopySpecs base next dead ++ suffix))
        (sourceCopyLoopSteps word.length processed.length remaining.length)
        (endConfiguration base outsideTail word
          (leftMarker ::
            (sourceMarkSymbols processed ++
              sourceDataSymbols remaining ++ rightMarker :: workspace))) =
      some
        (endConfiguration next (outsideTail.drop remaining.length)
          (word ++ List.replicate remaining.length unitSymbol)
          (leftMarker ::
            (sourceDataSymbols (processed ++ remaining) ++
              rightMarker :: workspace))) := by
  induction remaining generalizing processed outsideTail word with
  | nil =>
      have hFinish := sourceCopy_finish_bits_exact base next dead
        specPrefix suffix processed outsideTail word workspace hBase hScratch
      simpa [sourceCopyLoopSteps, sourceDataSymbols] using hFinish
  | cons bit rest ih =>
      have hIteration := sourceCopy_iteration_exact base next dead
        specPrefix suffix processed bit rest outsideTail word workspace
        hBase hScratch
      have hScratchNext : ∀ symbol ∈ word ++ [unitSymbol],
          ScratchSymbol symbol := by
        apply scratch_append word [unitSymbol] hScratch
        intro symbol hMem
        simp at hMem
        exact Or.inl hMem
      have hRest := ih (processed ++ [bit]) (outsideTail.drop 1)
        (word ++ [unitSymbol]) hScratchNext
      have hAll := workRunExact_compose_for
        (closedSpecMachine
          (specPrefix ++ sourceCopySpecs base next dead ++ suffix))
        (sourceIterationSteps word.length processed.length)
        (sourceCopyLoopSteps (word.length + 1)
          (processed.length + 1) rest.length)
        (endConfiguration base outsideTail word
          (leftMarker ::
            (sourceMarkSymbols processed ++ sourceDataSymbol bit ::
              (sourceDataSymbols rest ++ rightMarker :: workspace))))
        (endConfiguration base (outsideTail.drop 1)
          (word ++ [unitSymbol])
          (leftMarker ::
            (sourceMarkSymbols (processed ++ [bit]) ++
              sourceDataSymbols rest ++ rightMarker :: workspace)))
        (endConfiguration next ((outsideTail.drop 1).drop rest.length)
          ((word ++ [unitSymbol]) ++ List.replicate rest.length unitSymbol)
          (leftMarker ::
            (sourceDataSymbols ((processed ++ [bit]) ++ rest) ++
              rightMarker :: workspace)))
        hIteration (by simpa using hRest)
      simpa [sourceCopyLoopSteps, sourceDataSymbols, List.map_append,
        List.drop_drop, List.replicate_succ, List.append_assoc,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hAll

private theorem sourceCopy_exact
    (base next dead : Nat) (specPrefix suffix : List StateSpec)
    (input : BitString) (outsideTail word workspace : List WorkSymbol)
    (hBase : specPrefix.length = base)
    (hScratch : ∀ symbol ∈ word, ScratchSymbol symbol) :
    workRunExact?
        (closedSpecMachine
          (specPrefix ++ sourceCopySpecs base next dead ++ suffix))
        (sourceCopySteps word.length input.length)
        (endConfiguration base outsideTail word
          (sourceInside input workspace)) =
      some
        (endConfiguration next (outsideTail.drop input.length)
          (word ++ List.replicate input.length unitSymbol)
          (sourceInside input workspace)) := by
  cases input with
  | nil =>
      -- `workspaceInside` with its right workspace removed leaves the framed
      -- blank source cell and right marker.
      simpa [sourceCopySteps, sourceCopyLoopSteps, sourceInside,
        sourceWord] using
        (sourceCopy_finish_empty_exact base next dead specPrefix suffix
          outsideTail word workspace hBase hScratch)
  | cons first rest =>
      have hLoop := sourceCopy_loop_exact base next dead specPrefix suffix
        [] (first :: rest) outsideTail word workspace hBase hScratch
      have hSourceDataSymbol :
          sourceDataSymbol =
            (fun bit => dataSymbol (TapeSymbol.ofBool bit)) := by
        rfl
      simpa [sourceCopySteps, sourceInside, sourceWord,
        sourceDataSymbols, hSourceDataSymbol, sourceMarkSymbols,
        List.append_assoc] using hLoop

private def variableOperationSteps
    (wordLength inputLength : Nat) : Nat :=
  2 + sourceCopySteps (wordLength + 1) inputLength

private theorem variableOperation_exact
    (base next dead : Nat) (specPrefix suffix : List StateSpec)
    (input : BitString) (outsideTail word workspace : List WorkSymbol)
    (hBase : specPrefix.length = base)
    (hScratch : ∀ symbol ∈ word, ScratchSymbol symbol) :
    workRunExact?
        (closedSpecMachine
          (specPrefix ++ variableOperationSpecs base next dead ++ suffix))
        (variableOperationSteps word.length input.length)
        (endConfiguration base outsideTail word
          (sourceInside input workspace)) =
      some
        (endConfiguration next (outsideTail.drop (input.length + 1))
          (word ++ separatorSymbol ::
            List.replicate input.length unitSymbol)
          (sourceInside input workspace)) := by
  let copyBase := base + 2
  have hSeparator := separator_exact base copyBase dead specPrefix
    (sourceCopySpecs copyBase next dead ++ suffix)
    outsideTail word (sourceInside input workspace) hBase
  have hCopyPrefix :
      (specPrefix ++ separatorSpecs base copyBase dead).length =
        copyBase := by
    simp [copyBase, hBase]
  have hCopyScratch :
      ∀ symbol ∈ word ++ [separatorSymbol], ScratchSymbol symbol := by
    apply scratch_append word [separatorSymbol] hScratch
    intro symbol hMem
    simp only [List.mem_singleton] at hMem
    exact Or.inr (Or.inl hMem)
  have hCopy := sourceCopy_exact copyBase next dead
    (specPrefix ++ separatorSpecs base copyBase dead) suffix input
    (outsideTail.drop 1) (word ++ [separatorSymbol]) workspace
    hCopyPrefix hCopyScratch
  have hMachine :
      specPrefix ++ separatorSpecs base copyBase dead ++
          sourceCopySpecs copyBase next dead ++ suffix =
        specPrefix ++ variableOperationSpecs base next dead ++ suffix := by
    simp [variableOperationSpecs, copyBase, List.append_assoc]
  simp only [List.append_assoc] at hSeparator hCopy hMachine
  rw [hMachine] at hSeparator hCopy
  have hAll := workRunExact_compose_for
    (closedSpecMachine
      (specPrefix ++ variableOperationSpecs base next dead ++ suffix))
    2 (sourceCopySteps (word.length + 1) input.length)
    (endConfiguration base outsideTail word
      (sourceInside input workspace))
    (endConfiguration copyBase (outsideTail.drop 1)
      (word ++ [separatorSymbol]) (sourceInside input workspace))
    (endConfiguration next
      ((outsideTail.drop 1).drop input.length)
      ((word ++ [separatorSymbol]) ++
        List.replicate input.length unitSymbol)
      (sourceInside input workspace))
    (by simpa [List.append_assoc] using hSeparator)
    (by simpa [List.append_assoc] using hCopy)
  simpa [variableOperationSteps, List.drop_drop, List.append_assoc,
    Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hAll

/-! ### Exact register-location primitive -/

private def locateTraversalWord : List Nat → List WorkSymbol
  | [] => []
  | value :: rest =>
      List.replicate value unitSymbol ++
        separatorSymbol :: locateTraversalWord rest

@[simp] private theorem locateTraversalWord_length (values : List Nat) :
    (locateTraversalWord values).length = values.length + values.sum := by
  induction values with
  | nil => rfl
  | cons value rest ih =>
      simp [locateTraversalWord, ih]
      omega

@[simp] private theorem locateTraversalWord_append
    (left right : List Nat) :
    locateTraversalWord (left ++ right) =
      locateTraversalWord left ++ locateTraversalWord right := by
  induction left with
  | nil => rfl
  | cons value rest ih =>
      simp [locateTraversalWord, ih, List.append_assoc]

private theorem replicate_unit_append_singleton (count : Nat) :
    List.replicate count unitSymbol ++ [unitSymbol] =
      List.replicate (count + 1) unitSymbol := by
  induction count with
  | zero => rfl
  | succ count ih =>
      simp only [List.replicate_succ, List.cons_append, ih]

private theorem replicate_unit_cons_comm
    (count : Nat) (tail : List WorkSymbol) :
    List.replicate count unitSymbol ++ unitSymbol :: tail =
      unitSymbol :: List.replicate count unitSymbol ++ tail := by
  induction count with
  | zero => rfl
  | succ count ih =>
      simp only [List.replicate_succ, List.cons_append,
        List.cons.injEq, true_and]
      exact ih

private theorem replicate_cons_comm
    (symbol : WorkSymbol) (count : Nat) (tail : List WorkSymbol) :
    List.replicate count symbol ++ symbol :: tail =
      symbol :: List.replicate count symbol ++ tail := by
  induction count with
  | zero => rfl
  | succ count ih =>
      simp only [List.replicate_succ, List.cons_append,
        List.cons.injEq, true_and]
      exact ih

private theorem registerWord_reverse_eq_locateTraversalWord
    (values : List Nat) :
    (registerWord values).reverse =
      locateTraversalWord values.reverse := by
  induction values with
  | nil => rfl
  | cons value rest ih =>
      simp [registerWord, List.reverse_append, ih, locateTraversalWord,
        locateTraversalWord_append, List.append_assoc]

private theorem locate_unit_step
    (remaining current scan dead : Nat)
    (specPrefix suffix : List StateSpec) (tape : WorkTape)
    (hCurrent : specPrefix.length = current)
    (hHead : tape.head = unitSymbol ∨
      tape.head = registerMarkSymbol) :
    workStep?
        (closedSpecMachine
          (specPrefix ++
            locateSpecs (remaining + 1) current scan dead ++ suffix))
        { state := current, tape := tape } =
      some { state := current, tape := tape.moveRight } := by
  let spec : StateSpec := fun read =>
    if read = unitSymbol ∨ read = registerMarkSymbol then
      keepAction current .right read
    else if read = separatorSymbol then
      if remaining = 0 then keepAction scan .right read
      else keepAction (current + 1) .right read
    else deadAction dead read
  have hStep := closedSpecMachine_step specPrefix spec
    (locateSpecs remaining (current + 1) scan dead ++ suffix) tape
  have hAction : spec tape.head = keepAction current .right tape.head := by
    simp [spec, hHead]
  rw [hAction] at hStep
  simpa [locateSpecs, spec, keepAction, WorkTape.move,
    List.append_assoc, hCurrent] using hStep

private theorem locate_separator_step
    (remaining current scan dead : Nat)
    (specPrefix suffix : List StateSpec) (tape : WorkTape)
    (hCurrent : specPrefix.length = current)
    (hHead : tape.head = separatorSymbol) :
    workStep?
        (closedSpecMachine
          (specPrefix ++
            locateSpecs (remaining + 1) current scan dead ++ suffix))
        { state := current, tape := tape } =
      some
        { state := if remaining = 0 then scan else current + 1
          tape := tape.moveRight } := by
  let spec : StateSpec := fun read =>
    if read = unitSymbol ∨ read = registerMarkSymbol then
      keepAction current .right read
    else if read = separatorSymbol then
      if remaining = 0 then keepAction scan .right read
      else keepAction (current + 1) .right read
    else deadAction dead read
  have hStep := closedSpecMachine_step specPrefix spec
    (locateSpecs remaining (current + 1) scan dead ++ suffix) tape
  have hAction : spec tape.head =
      keepAction (if remaining = 0 then scan else current + 1)
        .right tape.head := by
    by_cases hRemaining : remaining = 0 <;>
      simp [spec, hHead, hRemaining, separatorSymbol, unitSymbol,
        registerMarkSymbol, WorkSymbol.zeroOne, WorkSymbol.oneOne,
        WorkSymbol.zeroZero]
  rw [hAction] at hStep
  simpa [locateSpecs, spec, keepAction, WorkTape.move,
    List.append_assoc, hCurrent] using hStep

private theorem locate_units_exact
    (remaining current scan dead count : Nat)
    (specPrefix suffix : List StateSpec)
    (leftSide rightSide : List WorkSymbol)
    (hCurrent : specPrefix.length = current) :
    workRunExact?
        (closedSpecMachine
          (specPrefix ++
            locateSpecs (remaining + 1) current scan dead ++ suffix))
        count
        { state := current
          tape := pathTape leftSide
            (List.replicate count unitSymbol ++ rightSide) } =
      some
        { state := current
          tape := pathTape
            (List.replicate count unitSymbol ++ leftSide) rightSide } := by
  induction count generalizing leftSide with
  | zero => rfl
  | succ count ih =>
      have hStep := locate_unit_step remaining current scan dead
        specPrefix suffix
        (pathTape leftSide
          (unitSymbol :: List.replicate count unitSymbol ++ rightSide))
        hCurrent (Or.inl rfl)
      have hFirst := workRunExact_one_for
        (closedSpecMachine
          (specPrefix ++
            locateSpecs (remaining + 1) current scan dead ++ suffix))
        { state := current
          tape := pathTape leftSide
            (unitSymbol :: List.replicate count unitSymbol ++ rightSide) }
        { state := current
          tape := pathTape (unitSymbol :: leftSide)
            (List.replicate count unitSymbol ++ rightSide) }
        (by simpa using hStep)
      have hRest := ih (unitSymbol :: leftSide)
      have hAll := workRunExact_compose_for
        (closedSpecMachine
          (specPrefix ++
            locateSpecs (remaining + 1) current scan dead ++ suffix))
        1 count
        { state := current
          tape := pathTape leftSide
            (unitSymbol :: List.replicate count unitSymbol ++ rightSide) }
        { state := current
          tape := pathTape (unitSymbol :: leftSide)
            (List.replicate count unitSymbol ++ rightSide) }
        { state := current
          tape := pathTape
            (List.replicate count unitSymbol ++ unitSymbol :: leftSide)
            rightSide }
        hFirst hRest
      rw [replicate_unit_cons_comm count leftSide] at hAll
      simpa [List.replicate_succ, List.append_assoc,
        Nat.add_comm] using hAll

private theorem locate_register_exact
    (remaining current scan dead value : Nat)
    (specPrefix suffix : List StateSpec)
    (leftSide rightSide : List WorkSymbol)
    (hCurrent : specPrefix.length = current) :
    workRunExact?
        (closedSpecMachine
          (specPrefix ++
            locateSpecs (remaining + 1) current scan dead ++ suffix))
        (value + 1)
        { state := current
          tape := pathTape leftSide
            (List.replicate value unitSymbol ++
              separatorSymbol :: rightSide) } =
      some
        { state := if remaining = 0 then scan else current + 1
          tape := pathTape
            (separatorSymbol ::
              List.replicate value unitSymbol ++ leftSide) rightSide } := by
  have hUnits := locate_units_exact remaining current scan dead value
    specPrefix suffix leftSide (separatorSymbol :: rightSide) hCurrent
  have hSeparatorStep := locate_separator_step remaining current scan dead
    specPrefix suffix
    (pathTape (List.replicate value unitSymbol ++ leftSide)
      (separatorSymbol :: rightSide)) hCurrent rfl
  have hSeparator := workRunExact_one_for
    (closedSpecMachine
      (specPrefix ++
        locateSpecs (remaining + 1) current scan dead ++ suffix))
    { state := current
      tape := pathTape (List.replicate value unitSymbol ++ leftSide)
        (separatorSymbol :: rightSide) }
    { state := if remaining = 0 then scan else current + 1
      tape := pathTape
        (separatorSymbol :: List.replicate value unitSymbol ++ leftSide)
        rightSide }
    (by simpa using hSeparatorStep)
  have hAll := workRunExact_compose_for
    (closedSpecMachine
      (specPrefix ++
        locateSpecs (remaining + 1) current scan dead ++ suffix))
    value 1
    { state := current
      tape := pathTape leftSide
        (List.replicate value unitSymbol ++ separatorSymbol :: rightSide) }
    { state := current
      tape := pathTape (List.replicate value unitSymbol ++ leftSide)
        (separatorSymbol :: rightSide) }
    { state := if remaining = 0 then scan else current + 1
      tape := pathTape
        (separatorSymbol :: List.replicate value unitSymbol ++ leftSide)
        rightSide }
    hUnits hSeparator
  simpa using hAll

private theorem locate_traversal_exact
    (values : List Nat) (current scan dead : Nat)
    (specPrefix suffix : List StateSpec)
    (leftSide rightSide : List WorkSymbol)
    (hValues : values ≠ [])
    (hCurrent : specPrefix.length = current) :
    workRunExact?
        (closedSpecMachine
          (specPrefix ++
            locateSpecs values.length current scan dead ++ suffix))
        (values.length + values.sum)
        { state := current
          tape := pathTape leftSide
            (locateTraversalWord values ++ rightSide) } =
      some
        { state := scan
          tape := pathTape
            ((locateTraversalWord values).reverse ++ leftSide)
            rightSide } := by
  induction values generalizing current specPrefix leftSide with
  | nil => contradiction
  | cons value rest ih =>
      cases rest with
      | nil =>
          have hRegister := locate_register_exact 0 current scan dead value
            specPrefix suffix leftSide rightSide hCurrent
          simpa [locateTraversalWord, List.reverse_append,
            List.append_assoc, Nat.add_comm] using hRegister
      | cons nextValue tail =>
          let firstSpec : StateSpec := fun read =>
            if read = unitSymbol ∨ read = registerMarkSymbol then
              keepAction current .right read
            else if read = separatorSymbol then
              keepAction (current + 1) .right read
            else deadAction dead read
          let restSpecs :=
            locateSpecs (nextValue :: tail).length
              (current + 1) scan dead
          let machineSpecs := specPrefix ++ firstSpec :: restSpecs ++ suffix
          have hFirst := locate_register_exact (nextValue :: tail).length current
            scan dead value specPrefix suffix leftSide
            (locateTraversalWord (nextValue :: tail) ++ rightSide) hCurrent
          have hRestCurrent :
              (specPrefix ++ [firstSpec]).length = current + 1 := by
            simp [hCurrent]
          have hRest := ih (current := current + 1)
            (specPrefix := specPrefix ++ [firstSpec])
            (leftSide := separatorSymbol ::
              List.replicate value unitSymbol ++ leftSide)
            (by simp) hRestCurrent
          have hMachine :
              specPrefix ++ locateSpecs (value :: nextValue :: tail).length
                  current scan dead ++ suffix = machineSpecs := by
            simp [locateSpecs, firstSpec, restSpecs, machineSpecs,
              List.append_assoc]
          have hMachineFirst :
              specPrefix ++ locateSpecs ((nextValue :: tail).length + 1)
                  current scan dead ++ suffix = machineSpecs := by
            simp [locateSpecs, firstSpec, restSpecs, machineSpecs,
              List.append_assoc]
          have hMachineRest :
              specPrefix ++ [firstSpec] ++
                  locateSpecs (nextValue :: tail).length
                    (current + 1) scan dead ++
                    suffix = machineSpecs := by
            simp [restSpecs, machineSpecs, List.append_assoc]
          rw [hMachineFirst] at hFirst
          rw [hMachineRest] at hRest
          have hAll := workRunExact_compose_for
            (closedSpecMachine machineSpecs)
            (value + 1)
              ((nextValue :: tail).length + (nextValue :: tail).sum)
            { state := current
              tape := pathTape leftSide
                (List.replicate value unitSymbol ++ separatorSymbol ::
                  (locateTraversalWord (nextValue :: tail) ++ rightSide)) }
            { state := current + 1
              tape := pathTape
                (separatorSymbol ::
                  List.replicate value unitSymbol ++ leftSide)
                (locateTraversalWord (nextValue :: tail) ++ rightSide) }
            { state := scan
              tape := pathTape
                ((locateTraversalWord (nextValue :: tail)).reverse ++
                  separatorSymbol ::
                    List.replicate value unitSymbol ++ leftSide)
                rightSide }
            (by simpa [machineSpecs, List.append_assoc] using hFirst)
            (by simpa [machineSpecs, List.append_assoc] using hRest)
          rw [hMachine]
          simpa [locateTraversalWord, List.reverse_append,
            List.append_assoc, Nat.add_assoc, Nat.add_comm,
            Nat.add_left_comm] using hAll

/-! ### Exact unary-register copy primitive -/

private theorem copy_start_step
    (distance base next dead : Nat)
    (specPrefix suffix : List StateSpec) (tape : WorkTape)
    (hBase : specPrefix.length = base)
    (hHead : tape.head = scratchEndSymbol) :
    workStep?
        (closedSpecMachine
          (specPrefix ++ copySpecs distance base next dead ++ suffix))
        { state := base, tape := tape } =
      some
        { state := copyLocateBase base, tape := tape.moveRight } := by
  have hStep := closedSpecMachine_step specPrefix
    (copyStartSpec base dead)
    (locateSpecs distance (copyLocateBase base)
        (copyScanState distance base) dead ++
      [copyScanSpec distance base dead,
       copySeekEndSpec distance base dead,
       copyAppendFirstSpec distance base dead,
       copyAppendSecondSpec base,
       copyRestoreSpec distance base dead,
       copySeekEndDoneSpec distance base next dead] ++ suffix) tape
  have hAction : copyStartSpec base dead tape.head =
      keepAction (copyLocateBase base) .right tape.head := by
    simp [copyStartSpec, hHead]
  rw [hAction] at hStep
  simpa [copySpecs, keepAction, WorkTape.move,
    List.append_assoc, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm,
    hBase] using hStep

private theorem copy_scan_mark_step
    (distance base next dead : Nat)
    (specPrefix suffix : List StateSpec) (tape : WorkTape)
    (hBase : specPrefix.length = base)
    (hHead : tape.head = registerMarkSymbol) :
    workStep?
        (closedSpecMachine
          (specPrefix ++ copySpecs distance base next dead ++ suffix))
        { state := copyScanState distance base, tape := tape } =
      some
        { state := copyScanState distance base
          tape := tape.moveRight } := by
  let scanPrefix :=
    specPrefix ++ [copyStartSpec base dead] ++
      locateSpecs distance (copyLocateBase base)
        (copyScanState distance base) dead
  have hScanPrefix : scanPrefix.length = copyScanState distance base := by
    simp [scanPrefix, copyScanState, copyLocateBase, hBase]
    omega
  have hStep := closedSpecMachine_step scanPrefix
    (copyScanSpec distance base dead)
    ([copySeekEndSpec distance base dead,
      copyAppendFirstSpec distance base dead,
      copyAppendSecondSpec base,
      copyRestoreSpec distance base dead,
      copySeekEndDoneSpec distance base next dead] ++ suffix) tape
  have hAction : copyScanSpec distance base dead tape.head =
      keepAction (copyScanState distance base) .right tape.head := by
    simp [copyScanSpec, hHead]
  rw [hAction] at hStep
  simpa [copySpecs, scanPrefix, copyScanState, copyLocateBase,
    keepAction, WorkTape.move,
    List.append_assoc, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm,
    hBase] using hStep

private theorem copy_scan_unit_step
    (distance base next dead : Nat)
    (specPrefix suffix : List StateSpec) (tape : WorkTape)
    (hBase : specPrefix.length = base)
    (hHead : tape.head = unitSymbol) :
    workStep?
        (closedSpecMachine
          (specPrefix ++ copySpecs distance base next dead ++ suffix))
        { state := copyScanState distance base, tape := tape } =
      some
        { state := copySeekEndState distance base
          tape := (tape.write registerMarkSymbol).moveLeft } := by
  let scanPrefix :=
    specPrefix ++ [copyStartSpec base dead] ++
      locateSpecs distance (copyLocateBase base)
        (copyScanState distance base) dead
  have hStep := closedSpecMachine_step scanPrefix
    (copyScanSpec distance base dead)
    ([copySeekEndSpec distance base dead,
      copyAppendFirstSpec distance base dead,
      copyAppendSecondSpec base,
      copyRestoreSpec distance base dead,
      copySeekEndDoneSpec distance base next dead] ++ suffix) tape
  simpa [copySpecs, scanPrefix, copyScanSpec, hHead, unitSymbol,
    registerMarkSymbol, WorkSymbol.oneOne, WorkSymbol.zeroZero,
    writeAction, WorkTape.move, copyScanState, copyLocateBase,
    copySeekEndState, List.append_assoc, Nat.add_assoc, Nat.add_comm,
    Nat.add_left_comm, hBase] using hStep

private theorem copy_scan_finish_step
    (distance base next dead : Nat)
    (specPrefix suffix : List StateSpec) (tape : WorkTape)
    (hBase : specPrefix.length = base)
    (hHead : tape.head = separatorSymbol) :
    workStep?
        (closedSpecMachine
          (specPrefix ++ copySpecs distance base next dead ++ suffix))
        { state := copyScanState distance base, tape := tape } =
      some
        { state := copyRestoreState distance base
          tape := tape.moveLeft } := by
  let scanPrefix :=
    specPrefix ++ [copyStartSpec base dead] ++
      locateSpecs distance (copyLocateBase base)
        (copyScanState distance base) dead
  have hStep := closedSpecMachine_step scanPrefix
    (copyScanSpec distance base dead)
    ([copySeekEndSpec distance base dead,
      copyAppendFirstSpec distance base dead,
      copyAppendSecondSpec base,
      copyRestoreSpec distance base dead,
      copySeekEndDoneSpec distance base next dead] ++ suffix) tape
  have hAction : copyScanSpec distance base dead tape.head =
      keepAction (copyRestoreState distance base) .left tape.head := by
    simp [copyScanSpec, hHead, separatorSymbol, unitSymbol,
      registerMarkSymbol, WorkSymbol.zeroOne, WorkSymbol.oneOne,
      WorkSymbol.zeroZero]
  rw [hAction] at hStep
  simpa [copySpecs, scanPrefix, copyScanSpec, separatorSymbol,
    unitSymbol, registerMarkSymbol, WorkSymbol.zeroOne,
    WorkSymbol.oneOne, WorkSymbol.zeroZero, keepAction, WorkTape.move,
    copyScanState, copyLocateBase, copyRestoreState,
    List.append_assoc, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm,
    hBase] using hStep

private theorem copy_seek_end_scratch_step
    (distance base next dead : Nat)
    (specPrefix suffix : List StateSpec) (tape : WorkTape)
    (hBase : specPrefix.length = base)
    (hScratch : ScratchSymbol tape.head) :
    workStep?
        (closedSpecMachine
          (specPrefix ++ copySpecs distance base next dead ++ suffix))
        { state := copySeekEndState distance base, tape := tape } =
      some
        { state := copySeekEndState distance base
          tape := tape.moveLeft } := by
  let seekPrefix :=
    specPrefix ++ [copyStartSpec base dead] ++
      locateSpecs distance (copyLocateBase base)
        (copyScanState distance base) dead ++
      [copyScanSpec distance base dead]
  have hStep := closedSpecMachine_step seekPrefix
    (copySeekEndSpec distance base dead)
    ([copyAppendFirstSpec distance base dead,
      copyAppendSecondSpec base,
      copyRestoreSpec distance base dead,
      copySeekEndDoneSpec distance base next dead] ++ suffix) tape
  have hAction : copySeekEndSpec distance base dead tape.head =
      keepAction (copySeekEndState distance base) .left tape.head := by
    rcases hScratch with hUnit | hSeparator | hMark
    · simp [copySeekEndSpec, hUnit]
    · simp [copySeekEndSpec, hSeparator]
    · simp [copySeekEndSpec, hMark]
  rw [hAction] at hStep
  simpa [copySpecs, seekPrefix, copyScanState, copyLocateBase,
    copySeekEndState, keepAction, WorkTape.move,
    List.append_assoc, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm,
    hBase] using hStep

private theorem copy_seek_end_marker_step
    (distance base next dead : Nat)
    (specPrefix suffix : List StateSpec) (tape : WorkTape)
    (hBase : specPrefix.length = base)
    (hHead : tape.head = scratchEndSymbol) :
    workStep?
        (closedSpecMachine
          (specPrefix ++ copySpecs distance base next dead ++ suffix))
        { state := copySeekEndState distance base, tape := tape } =
      some
        { state := copyAppendFirstState distance base, tape := tape } := by
  let seekPrefix :=
    specPrefix ++ [copyStartSpec base dead] ++
      locateSpecs distance (copyLocateBase base)
        (copyScanState distance base) dead ++
      [copyScanSpec distance base dead]
  have hStep := closedSpecMachine_step seekPrefix
    (copySeekEndSpec distance base dead)
    ([copyAppendFirstSpec distance base dead,
      copyAppendSecondSpec base,
      copyRestoreSpec distance base dead,
      copySeekEndDoneSpec distance base next dead] ++ suffix) tape
  have hAction : copySeekEndSpec distance base dead tape.head =
      keepAction (copyAppendFirstState distance base) .stay tape.head := by
    simp [copySeekEndSpec, hHead, scratchEndSymbol, unitSymbol,
      separatorSymbol, registerMarkSymbol, WorkSymbol.blankOne,
      WorkSymbol.oneOne, WorkSymbol.zeroOne, WorkSymbol.zeroZero]
  rw [hAction] at hStep
  simpa [copySpecs, seekPrefix, copySeekEndSpec,
    scratchEndSymbol, unitSymbol, separatorSymbol, registerMarkSymbol,
    WorkSymbol.blankOne, WorkSymbol.oneOne, WorkSymbol.zeroOne,
    WorkSymbol.zeroZero, keepAction, WorkTape.move,
    copyScanState, copyLocateBase, copySeekEndState,
    copyAppendFirstState, List.append_assoc, Nat.add_assoc, Nat.add_comm,
    Nat.add_left_comm, hBase] using hStep

private theorem copy_append_first_step
    (distance base next dead : Nat)
    (specPrefix suffix : List StateSpec) (tape : WorkTape)
    (hBase : specPrefix.length = base)
    (hHead : tape.head = scratchEndSymbol) :
    workStep?
        (closedSpecMachine
          (specPrefix ++ copySpecs distance base next dead ++ suffix))
        { state := copyAppendFirstState distance base, tape := tape } =
      some
        { state := copyAppendSecondState distance base
          tape := (tape.write unitSymbol).moveLeft } := by
  let appendPrefix :=
    specPrefix ++ [copyStartSpec base dead] ++
      locateSpecs distance (copyLocateBase base)
        (copyScanState distance base) dead ++
      [copyScanSpec distance base dead,
       copySeekEndSpec distance base dead]
  have hStep := closedSpecMachine_step appendPrefix
    (copyAppendFirstSpec distance base dead)
    ([copyAppendSecondSpec base,
      copyRestoreSpec distance base dead,
      copySeekEndDoneSpec distance base next dead] ++ suffix) tape
  simpa [copySpecs, appendPrefix, copyAppendFirstSpec, hHead,
    writeAction, WorkTape.move, copyScanState, copyLocateBase,
    copyAppendFirstState, copyAppendSecondState,
    List.append_assoc, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm,
    hBase] using hStep

private theorem copy_append_second_step
    (distance base next dead : Nat)
    (specPrefix suffix : List StateSpec) (tape : WorkTape)
    (hBase : specPrefix.length = base) :
    workStep?
        (closedSpecMachine
          (specPrefix ++ copySpecs distance base next dead ++ suffix))
        { state := copyAppendSecondState distance base, tape := tape } =
      some
        { state := base, tape := tape.write scratchEndSymbol } := by
  let appendPrefix :=
    specPrefix ++ [copyStartSpec base dead] ++
      locateSpecs distance (copyLocateBase base)
        (copyScanState distance base) dead ++
      [copyScanSpec distance base dead,
       copySeekEndSpec distance base dead,
       copyAppendFirstSpec distance base dead]
  have hStep := closedSpecMachine_step appendPrefix
    (copyAppendSecondSpec base)
    ([copyRestoreSpec distance base dead,
      copySeekEndDoneSpec distance base next dead] ++ suffix) tape
  simpa [copySpecs, appendPrefix, copyAppendSecondSpec, writeAction,
    WorkTape.move, copyScanState, copyLocateBase,
    copyAppendSecondState, List.append_assoc, Nat.add_assoc,
    Nat.add_comm, Nat.add_left_comm, hBase] using hStep

private theorem copy_restore_mark_step
    (distance base next dead : Nat)
    (specPrefix suffix : List StateSpec) (tape : WorkTape)
    (hBase : specPrefix.length = base)
    (hHead : tape.head = registerMarkSymbol) :
    workStep?
        (closedSpecMachine
          (specPrefix ++ copySpecs distance base next dead ++ suffix))
        { state := copyRestoreState distance base, tape := tape } =
      some
        { state := copyRestoreState distance base
          tape := (tape.write unitSymbol).moveLeft } := by
  let restorePrefix :=
    specPrefix ++ [copyStartSpec base dead] ++
      locateSpecs distance (copyLocateBase base)
        (copyScanState distance base) dead ++
      [copyScanSpec distance base dead,
       copySeekEndSpec distance base dead,
       copyAppendFirstSpec distance base dead,
       copyAppendSecondSpec base]
  have hStep := closedSpecMachine_step restorePrefix
    (copyRestoreSpec distance base dead)
    ([copySeekEndDoneSpec distance base next dead] ++ suffix) tape
  simpa [copySpecs, restorePrefix, copyRestoreSpec, hHead,
    registerMarkSymbol, unitSymbol, separatorSymbol,
    WorkSymbol.zeroZero, WorkSymbol.oneOne, WorkSymbol.zeroOne,
    writeAction, WorkTape.move, copyScanState, copyLocateBase,
    copyRestoreState, List.append_assoc, Nat.add_assoc, Nat.add_comm,
    Nat.add_left_comm, hBase] using hStep

private theorem copy_restore_unit_step
    (distance base next dead : Nat)
    (specPrefix suffix : List StateSpec) (tape : WorkTape)
    (hBase : specPrefix.length = base)
    (hHead : tape.head = unitSymbol) :
    workStep?
        (closedSpecMachine
          (specPrefix ++ copySpecs distance base next dead ++ suffix))
        { state := copyRestoreState distance base, tape := tape } =
      some
        { state := copyRestoreState distance base
          tape := tape.moveLeft } := by
  let restorePrefix :=
    specPrefix ++ [copyStartSpec base dead] ++
      locateSpecs distance (copyLocateBase base)
        (copyScanState distance base) dead ++
      [copyScanSpec distance base dead,
       copySeekEndSpec distance base dead,
       copyAppendFirstSpec distance base dead,
       copyAppendSecondSpec base]
  have hStep := closedSpecMachine_step restorePrefix
    (copyRestoreSpec distance base dead)
    ([copySeekEndDoneSpec distance base next dead] ++ suffix) tape
  have hAction : copyRestoreSpec distance base dead tape.head =
      keepAction (copyRestoreState distance base) .left tape.head := by
    simp [copyRestoreSpec, hHead, unitSymbol, registerMarkSymbol,
      WorkSymbol.oneOne, WorkSymbol.zeroZero]
  rw [hAction] at hStep
  simpa [copySpecs, restorePrefix, copyRestoreSpec,
    registerMarkSymbol, unitSymbol, separatorSymbol,
    WorkSymbol.zeroZero, WorkSymbol.oneOne, WorkSymbol.zeroOne,
    keepAction, WorkTape.move, copyScanState, copyLocateBase,
    copyRestoreState, List.append_assoc, Nat.add_assoc, Nat.add_comm,
    Nat.add_left_comm, hBase] using hStep

private theorem copy_restore_separator_step
    (distance base next dead : Nat)
    (specPrefix suffix : List StateSpec) (tape : WorkTape)
    (hBase : specPrefix.length = base)
    (hHead : tape.head = separatorSymbol) :
    workStep?
        (closedSpecMachine
          (specPrefix ++ copySpecs distance base next dead ++ suffix))
        { state := copyRestoreState distance base, tape := tape } =
      some
        { state := copySeekEndDoneState distance base
          tape := tape.moveLeft } := by
  let restorePrefix :=
    specPrefix ++ [copyStartSpec base dead] ++
      locateSpecs distance (copyLocateBase base)
        (copyScanState distance base) dead ++
      [copyScanSpec distance base dead,
       copySeekEndSpec distance base dead,
       copyAppendFirstSpec distance base dead,
       copyAppendSecondSpec base]
  have hStep := closedSpecMachine_step restorePrefix
    (copyRestoreSpec distance base dead)
    ([copySeekEndDoneSpec distance base next dead] ++ suffix) tape
  have hAction : copyRestoreSpec distance base dead tape.head =
      keepAction (copySeekEndDoneState distance base) .left tape.head := by
    simp [copyRestoreSpec, hHead, unitSymbol, registerMarkSymbol,
      separatorSymbol, WorkSymbol.oneOne, WorkSymbol.zeroZero,
      WorkSymbol.zeroOne]
  rw [hAction] at hStep
  simpa [copySpecs, restorePrefix, copyRestoreSpec,
    registerMarkSymbol, unitSymbol, separatorSymbol,
    WorkSymbol.zeroZero, WorkSymbol.oneOne, WorkSymbol.zeroOne,
    keepAction, WorkTape.move, copyScanState, copyLocateBase,
    copyRestoreState, copySeekEndDoneState,
    List.append_assoc, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm,
    hBase] using hStep

private theorem copy_seek_done_scratch_step
    (distance base next dead : Nat)
    (specPrefix suffix : List StateSpec) (tape : WorkTape)
    (hBase : specPrefix.length = base)
    (hScratch : ScratchSymbol tape.head) :
    workStep?
        (closedSpecMachine
          (specPrefix ++ copySpecs distance base next dead ++ suffix))
        { state := copySeekEndDoneState distance base, tape := tape } =
      some
        { state := copySeekEndDoneState distance base
          tape := tape.moveLeft } := by
  let donePrefix :=
    specPrefix ++ [copyStartSpec base dead] ++
      locateSpecs distance (copyLocateBase base)
        (copyScanState distance base) dead ++
      [copyScanSpec distance base dead,
       copySeekEndSpec distance base dead,
       copyAppendFirstSpec distance base dead,
       copyAppendSecondSpec base,
       copyRestoreSpec distance base dead]
  have hStep := closedSpecMachine_step donePrefix
    (copySeekEndDoneSpec distance base next dead) suffix tape
  have hAction : copySeekEndDoneSpec distance base next dead tape.head =
      keepAction (copySeekEndDoneState distance base) .left tape.head := by
    rcases hScratch with hUnit | hSeparator | hMark
    · simp [copySeekEndDoneSpec, hUnit]
    · simp [copySeekEndDoneSpec, hSeparator]
    · simp [copySeekEndDoneSpec, hMark]
  rw [hAction] at hStep
  simpa [copySpecs, donePrefix, copyScanState, copyLocateBase,
    copySeekEndDoneState, keepAction, WorkTape.move,
    List.append_assoc, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm,
    hBase] using hStep

private theorem copy_seek_done_marker_step
    (distance base next dead : Nat)
    (specPrefix suffix : List StateSpec) (tape : WorkTape)
    (hBase : specPrefix.length = base)
    (hHead : tape.head = scratchEndSymbol) :
    workStep?
        (closedSpecMachine
          (specPrefix ++ copySpecs distance base next dead ++ suffix))
        { state := copySeekEndDoneState distance base, tape := tape } =
      some { state := next, tape := tape } := by
  let donePrefix :=
    specPrefix ++ [copyStartSpec base dead] ++
      locateSpecs distance (copyLocateBase base)
        (copyScanState distance base) dead ++
      [copyScanSpec distance base dead,
       copySeekEndSpec distance base dead,
       copyAppendFirstSpec distance base dead,
       copyAppendSecondSpec base,
       copyRestoreSpec distance base dead]
  have hStep := closedSpecMachine_step donePrefix
    (copySeekEndDoneSpec distance base next dead) suffix tape
  have hAction : copySeekEndDoneSpec distance base next dead tape.head =
      keepAction next .stay tape.head := by
    simp [copySeekEndDoneSpec, hHead, scratchEndSymbol, unitSymbol,
      separatorSymbol, registerMarkSymbol, WorkSymbol.blankOne,
      WorkSymbol.oneOne, WorkSymbol.zeroOne, WorkSymbol.zeroZero]
  rw [hAction] at hStep
  simpa [copySpecs, donePrefix, copySeekEndDoneSpec,
    scratchEndSymbol, unitSymbol, separatorSymbol, registerMarkSymbol,
    WorkSymbol.blankOne, WorkSymbol.oneOne, WorkSymbol.zeroOne,
    WorkSymbol.zeroZero, keepAction, WorkTape.move,
    copyScanState, copyLocateBase, copySeekEndDoneState,
    List.append_assoc, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm,
    hBase] using hStep

private theorem copy_scan_marks_exact
    (distance base next dead count : Nat)
    (specPrefix suffix : List StateSpec)
    (leftSide rightSide : List WorkSymbol)
    (hBase : specPrefix.length = base) :
    workRunExact?
        (closedSpecMachine
          (specPrefix ++ copySpecs distance base next dead ++ suffix))
        count
        { state := copyScanState distance base
          tape := pathTape leftSide
            (List.replicate count registerMarkSymbol ++ rightSide) } =
      some
        { state := copyScanState distance base
          tape := pathTape
            (List.replicate count registerMarkSymbol ++ leftSide)
            rightSide } := by
  induction count generalizing leftSide with
  | zero => rfl
  | succ count ih =>
      have hStep := copy_scan_mark_step distance base next dead
        specPrefix suffix
        (pathTape leftSide
          (registerMarkSymbol ::
            List.replicate count registerMarkSymbol ++ rightSide))
        hBase rfl
      have hFirst := workRunExact_one_for
        (closedSpecMachine
          (specPrefix ++ copySpecs distance base next dead ++ suffix))
        { state := copyScanState distance base
          tape := pathTape leftSide
            (registerMarkSymbol ::
              List.replicate count registerMarkSymbol ++ rightSide) }
        { state := copyScanState distance base
          tape := pathTape (registerMarkSymbol :: leftSide)
            (List.replicate count registerMarkSymbol ++ rightSide) }
        (by simpa using hStep)
      have hRest := ih (registerMarkSymbol :: leftSide)
      have hAll := workRunExact_compose_for
        (closedSpecMachine
          (specPrefix ++ copySpecs distance base next dead ++ suffix))
        1 count
        { state := copyScanState distance base
          tape := pathTape leftSide
            (registerMarkSymbol ::
              List.replicate count registerMarkSymbol ++ rightSide) }
        { state := copyScanState distance base
          tape := pathTape (registerMarkSymbol :: leftSide)
            (List.replicate count registerMarkSymbol ++ rightSide) }
        { state := copyScanState distance base
          tape := pathTape
            (List.replicate count registerMarkSymbol ++
              registerMarkSymbol :: leftSide) rightSide }
        hFirst hRest
      rw [replicate_cons_comm registerMarkSymbol count leftSide] at hAll
      simpa [List.replicate_succ, List.append_assoc,
        Nat.add_comm] using hAll

private theorem copy_seek_end_exact
    (distance base next dead : Nat)
    (specPrefix suffix : List StateSpec)
    (symbols outsideTail rightSide : List WorkSymbol)
    (hBase : specPrefix.length = base)
    (hScratch : ∀ symbol ∈ symbols, ScratchSymbol symbol) :
    workRunExact?
        (closedSpecMachine
          (specPrefix ++ copySpecs distance base next dead ++ suffix))
        (symbols.length + 1)
        { state := copySeekEndState distance base
          tape := leftPathTape rightSide
            (symbols ++ scratchEndSymbol :: outsideTail) } =
      some
        { state := copyAppendFirstState distance base
          tape :=
            { left := outsideTail
              head := scratchEndSymbol
              right := symbols.reverse ++ rightSide } } := by
  induction symbols generalizing rightSide with
  | nil =>
      have hStep := copy_seek_end_marker_step distance base next dead
        specPrefix suffix
        (leftPathTape rightSide (scratchEndSymbol :: outsideTail))
        hBase rfl
      have hExact := workRunExact_one_for
        (closedSpecMachine
          (specPrefix ++ copySpecs distance base next dead ++ suffix))
        { state := copySeekEndState distance base
          tape := leftPathTape rightSide
            (scratchEndSymbol :: outsideTail) }
        { state := copyAppendFirstState distance base
          tape := leftPathTape rightSide
            (scratchEndSymbol :: outsideTail) }
        (by simpa [leftPathTape] using hStep)
      simpa [leftPathTape] using hExact
  | cons first rest ih =>
      have hFirstScratch := hScratch first (List.Mem.head rest)
      have hRestScratch : ∀ symbol ∈ rest, ScratchSymbol symbol := by
        intro symbol hMem
        exact hScratch symbol (List.Mem.tail first hMem)
      have hStep := copy_seek_end_scratch_step distance base next dead
        specPrefix suffix
        (leftPathTape rightSide
          (first :: rest ++ scratchEndSymbol :: outsideTail))
        hBase hFirstScratch
      have hFirst := workRunExact_one_for
        (closedSpecMachine
          (specPrefix ++ copySpecs distance base next dead ++ suffix))
        { state := copySeekEndState distance base
          tape := leftPathTape rightSide
            (first :: rest ++ scratchEndSymbol :: outsideTail) }
        { state := copySeekEndState distance base
          tape := leftPathTape (first :: rightSide)
            (rest ++ scratchEndSymbol :: outsideTail) }
        (by simpa using hStep)
      have hRest := ih (first :: rightSide) hRestScratch
      have hAll := workRunExact_compose_for
        (closedSpecMachine
          (specPrefix ++ copySpecs distance base next dead ++ suffix))
        1 (rest.length + 1)
        { state := copySeekEndState distance base
          tape := leftPathTape rightSide
            (first :: rest ++ scratchEndSymbol :: outsideTail) }
        { state := copySeekEndState distance base
          tape := leftPathTape (first :: rightSide)
            (rest ++ scratchEndSymbol :: outsideTail) }
        { state := copyAppendFirstState distance base
          tape :=
            { left := outsideTail
              head := scratchEndSymbol
              right := rest.reverse ++ first :: rightSide } }
        hFirst hRest
      have hSteps : 1 + (rest.length + 1) =
          (first :: rest).length + 1 := by simp; omega
      rw [← hSteps]
      simpa [List.reverse_cons, List.append_assoc] using hAll

private theorem copy_append_exact
    (distance base next dead : Nat)
    (specPrefix suffix : List StateSpec)
    (outsideTail word inside : List WorkSymbol)
    (hBase : specPrefix.length = base) :
    workRunExact?
        (closedSpecMachine
          (specPrefix ++ copySpecs distance base next dead ++ suffix))
        2
        (endConfiguration (copyAppendFirstState distance base)
          outsideTail word inside) =
      some
        (endConfiguration base (outsideTail.drop 1)
          (word ++ [unitSymbol]) inside) := by
  let firstTape :=
    (endTape outsideTail word inside).write unitSymbol |>.moveLeft
  let firstConfig : WorkConfiguration :=
    { state := copyAppendSecondState distance base, tape := firstTape }
  let finalConfig := endConfiguration base (outsideTail.drop 1)
    (word ++ [unitSymbol]) inside
  have hFirstStep := copy_append_first_step distance base next dead
    specPrefix suffix (endTape outsideTail word inside) hBase rfl
  have hFirst := workRunExact_one_for
    (closedSpecMachine
      (specPrefix ++ copySpecs distance base next dead ++ suffix))
    (endConfiguration (copyAppendFirstState distance base)
      outsideTail word inside) firstConfig
    (by simpa [endConfiguration, firstConfig, firstTape] using hFirstStep)
  have hSecondStep := copy_append_second_step distance base next dead
    specPrefix suffix firstTape hBase
  have hSecond := workRunExact_one_for
    (closedSpecMachine
      (specPrefix ++ copySpecs distance base next dead ++ suffix))
    firstConfig finalConfig (by
      cases outsideTail <;>
        simpa [firstConfig, finalConfig, firstTape, endConfiguration,
          endTape, WorkTape.write, WorkTape.moveLeft, WorkTape.move]
          using hSecondStep)
  have hAll := workRunExact_compose_for
    (closedSpecMachine
      (specPrefix ++ copySpecs distance base next dead ++ suffix))
    1 1
    (endConfiguration (copyAppendFirstState distance base)
      outsideTail word inside)
    firstConfig finalConfig hFirst hSecond
  simpa [finalConfig] using hAll

private theorem copy_restore_marks_exact
    (distance base next dead count : Nat)
    (specPrefix suffix : List StateSpec)
    (leftRest rightSide : List WorkSymbol)
    (hBase : specPrefix.length = base) :
    workRunExact?
        (closedSpecMachine
          (specPrefix ++ copySpecs distance base next dead ++ suffix))
        count
        { state := copyRestoreState distance base
          tape := leftPathTape rightSide
            (List.replicate count registerMarkSymbol ++ leftRest) } =
      some
        { state := copyRestoreState distance base
          tape := leftPathTape
            (List.replicate count unitSymbol ++ rightSide) leftRest } := by
  induction count generalizing rightSide with
  | zero => rfl
  | succ count ih =>
      have hStep := copy_restore_mark_step distance base next dead
        specPrefix suffix
        (leftPathTape rightSide
          (registerMarkSymbol ::
            List.replicate count registerMarkSymbol ++ leftRest))
        hBase rfl
      have hFirst := workRunExact_one_for
        (closedSpecMachine
          (specPrefix ++ copySpecs distance base next dead ++ suffix))
        { state := copyRestoreState distance base
          tape := leftPathTape rightSide
            (registerMarkSymbol ::
              List.replicate count registerMarkSymbol ++ leftRest) }
        { state := copyRestoreState distance base
          tape := leftPathTape (unitSymbol :: rightSide)
            (List.replicate count registerMarkSymbol ++ leftRest) }
        (by simpa using hStep)
      have hRest := ih (unitSymbol :: rightSide)
      have hAll := workRunExact_compose_for
        (closedSpecMachine
          (specPrefix ++ copySpecs distance base next dead ++ suffix))
        1 count
        { state := copyRestoreState distance base
          tape := leftPathTape rightSide
            (registerMarkSymbol ::
              List.replicate count registerMarkSymbol ++ leftRest) }
        { state := copyRestoreState distance base
          tape := leftPathTape (unitSymbol :: rightSide)
            (List.replicate count registerMarkSymbol ++ leftRest) }
        { state := copyRestoreState distance base
          tape := leftPathTape
            (List.replicate count unitSymbol ++ unitSymbol :: rightSide)
            leftRest }
        hFirst hRest
      rw [replicate_unit_cons_comm count rightSide] at hAll
      simpa [List.replicate_succ, List.append_assoc,
        Nat.add_comm] using hAll

private theorem copy_seek_done_exact
    (distance base next dead : Nat)
    (specPrefix suffix : List StateSpec)
    (symbols outsideTail rightSide : List WorkSymbol)
    (hBase : specPrefix.length = base)
    (hScratch : ∀ symbol ∈ symbols, ScratchSymbol symbol) :
    workRunExact?
        (closedSpecMachine
          (specPrefix ++ copySpecs distance base next dead ++ suffix))
        (symbols.length + 1)
        { state := copySeekEndDoneState distance base
          tape := leftPathTape rightSide
            (symbols ++ scratchEndSymbol :: outsideTail) } =
      some
        { state := next
          tape :=
            { left := outsideTail
              head := scratchEndSymbol
              right := symbols.reverse ++ rightSide } } := by
  induction symbols generalizing rightSide with
  | nil =>
      have hStep := copy_seek_done_marker_step distance base next dead
        specPrefix suffix
        (leftPathTape rightSide (scratchEndSymbol :: outsideTail))
        hBase rfl
      have hExact := workRunExact_one_for
        (closedSpecMachine
          (specPrefix ++ copySpecs distance base next dead ++ suffix))
        { state := copySeekEndDoneState distance base
          tape := leftPathTape rightSide
            (scratchEndSymbol :: outsideTail) }
        { state := next
          tape := leftPathTape rightSide
            (scratchEndSymbol :: outsideTail) }
        (by simpa [leftPathTape] using hStep)
      simpa [leftPathTape] using hExact
  | cons first rest ih =>
      have hFirstScratch := hScratch first (List.Mem.head rest)
      have hRestScratch : ∀ symbol ∈ rest, ScratchSymbol symbol := by
        intro symbol hMem
        exact hScratch symbol (List.Mem.tail first hMem)
      have hStep := copy_seek_done_scratch_step distance base next dead
        specPrefix suffix
        (leftPathTape rightSide
          (first :: rest ++ scratchEndSymbol :: outsideTail))
        hBase hFirstScratch
      have hFirst := workRunExact_one_for
        (closedSpecMachine
          (specPrefix ++ copySpecs distance base next dead ++ suffix))
        { state := copySeekEndDoneState distance base
          tape := leftPathTape rightSide
            (first :: rest ++ scratchEndSymbol :: outsideTail) }
        { state := copySeekEndDoneState distance base
          tape := leftPathTape (first :: rightSide)
            (rest ++ scratchEndSymbol :: outsideTail) }
        (by simpa using hStep)
      have hRest := ih (first :: rightSide) hRestScratch
      have hAll := workRunExact_compose_for
        (closedSpecMachine
          (specPrefix ++ copySpecs distance base next dead ++ suffix))
        1 (rest.length + 1)
        { state := copySeekEndDoneState distance base
          tape := leftPathTape rightSide
            (first :: rest ++ scratchEndSymbol :: outsideTail) }
        { state := copySeekEndDoneState distance base
          tape := leftPathTape (first :: rightSide)
            (rest ++ scratchEndSymbol :: outsideTail) }
        { state := next
          tape :=
            { left := outsideTail
              head := scratchEndSymbol
              right := rest.reverse ++ first :: rightSide } }
        hFirst hRest
      have hSteps : 1 + (rest.length + 1) =
          (first :: rest).length + 1 := by simp; omega
      rw [← hSteps]
      simpa [List.reverse_cons, List.append_assoc] using hAll

private def copyNewerValues
    (intermediate : List Nat) (destination processed : Nat) : List Nat :=
  intermediate ++ [destination + processed]

private def copyLoopWord
    (older : List WorkSymbol) (remaining processed : Nat)
    (intermediate : List Nat) (destination : Nat) : List WorkSymbol :=
  older ++ separatorSymbol ::
    (List.replicate remaining unitSymbol ++
      List.replicate processed registerMarkSymbol ++
        registerWord (copyNewerValues intermediate destination processed))

private def copyMarkedWord
    (older : List WorkSymbol) (remaining processed : Nat)
    (intermediate : List Nat) (destination : Nat) : List WorkSymbol :=
  older ++ separatorSymbol ::
    (List.replicate remaining unitSymbol ++
      List.replicate (processed + 1) registerMarkSymbol ++
        registerWord (copyNewerValues intermediate destination processed))

private def copyIterationSteps
    (intermediate : List Nat) (destination processed : Nat) : Nat :=
  2 * (registerWord
      (copyNewerValues intermediate destination processed)).length +
    2 * processed + 5

private def copyFinishSteps
    (intermediate : List Nat) (destination processed : Nat) : Nat :=
  2 * (registerWord
      (copyNewerValues intermediate destination processed)).length +
    2 * processed + 3

private theorem copyNewerValues_ne_nil
    (intermediate : List Nat) (destination processed : Nat) :
    copyNewerValues intermediate destination processed ≠ [] := by
  simp [copyNewerValues]

private theorem copyNewerValues_length
    (intermediate : List Nat) (destination processed : Nat) :
    (copyNewerValues intermediate destination processed).length =
      intermediate.length + 1 := by
  simp [copyNewerValues]

private theorem copyLoopWord_scratch
    (older : List WorkSymbol) (remaining processed : Nat)
    (intermediate : List Nat) (destination : Nat)
    (hOlder : ∀ symbol ∈ older, ScratchSymbol symbol) :
    ∀ symbol ∈
        copyLoopWord older remaining processed intermediate destination,
      ScratchSymbol symbol := by
  have hSeparator :
      ∀ symbol ∈ [separatorSymbol], ScratchSymbol symbol := by
    intro symbol hMem
    simp only [List.mem_singleton] at hMem
    exact Or.inr (Or.inl hMem)
  have hMarks :
      ∀ symbol ∈ List.replicate processed registerMarkSymbol,
        ScratchSymbol symbol := by
    intro symbol hMem
    exact Or.inr (Or.inr (List.eq_of_mem_replicate hMem))
  have hUnitsMarks := scratch_append
    (List.replicate remaining unitSymbol)
    (List.replicate processed registerMarkSymbol)
    (replicate_unit_scratch remaining) hMarks
  have hPayload := scratch_append
    (List.replicate remaining unitSymbol ++
      List.replicate processed registerMarkSymbol)
    (registerWord (copyNewerValues intermediate destination processed))
    hUnitsMarks (registerWord_scratch _)
  have hAfterSeparator := scratch_append [separatorSymbol]
    (List.replicate remaining unitSymbol ++
      List.replicate processed registerMarkSymbol ++
        registerWord (copyNewerValues intermediate destination processed))
    hSeparator hPayload
  simpa [copyLoopWord, List.append_assoc] using
    (scratch_append older
      ([separatorSymbol] ++
        (List.replicate remaining unitSymbol ++
          List.replicate processed registerMarkSymbol ++
            registerWord
              (copyNewerValues intermediate destination processed)))
      hOlder hAfterSeparator)

private theorem registerWord_newer_reverse
    (intermediate : List Nat) (destination processed : Nat) :
    (registerWord
        (copyNewerValues intermediate destination processed)).reverse =
      locateTraversalWord
        (copyNewerValues intermediate destination processed).reverse :=
  registerWord_reverse_eq_locateTraversalWord _

private theorem locateTraversalWord_newer_reverse
    (intermediate : List Nat) (destination processed : Nat) :
    (locateTraversalWord
      (copyNewerValues intermediate destination processed).reverse).reverse =
        registerWord
          (copyNewerValues intermediate destination processed) := by
  rw [← registerWord_newer_reverse intermediate destination processed]
  simp

private theorem copy_iteration_exact
    (base next dead : Nat) (specPrefix suffix : List StateSpec)
    (older inside outsideTail : List WorkSymbol)
    (remaining processed destination : Nat)
    (intermediate : List Nat)
    (hBase : specPrefix.length = base) :
    workRunExact?
        (closedSpecMachine
          (specPrefix ++
            copySpecs (intermediate.length + 1) base next dead ++ suffix))
        (copyIterationSteps intermediate destination processed)
        (endConfiguration base outsideTail
          (copyLoopWord older (remaining + 1) processed
            intermediate destination) inside) =
      some
        (endConfiguration base (outsideTail.drop 1)
          (copyLoopWord older remaining (processed + 1)
            intermediate destination) inside) := by
  let distance := intermediate.length + 1
  let newer := copyNewerValues intermediate destination processed
  let traversal := locateTraversalWord newer.reverse
  let newerWord := registerWord newer
  let loopTail : List StateSpec :=
    [copyScanSpec distance base dead,
     copySeekEndSpec distance base dead,
     copyAppendFirstSpec distance base dead,
     copyAppendSecondSpec base,
     copyRestoreSpec distance base dead,
     copySeekEndDoneSpec distance base next dead]
  let machineSpecs :=
    specPrefix ++ copySpecs distance base next dead ++ suffix
  let rightAfterSource :=
    separatorSymbol :: older.reverse ++ inside
  let c0 := endConfiguration base outsideTail
    (copyLoopWord older (remaining + 1) processed
      intermediate destination) inside
  let c1 : WorkConfiguration :=
    { state := copyLocateBase base
      tape := pathTape (scratchEndSymbol :: outsideTail)
        (traversal ++
          List.replicate processed registerMarkSymbol ++
            unitSymbol :: List.replicate remaining unitSymbol ++
              rightAfterSource) }
  let locateLeft := traversal.reverse ++ scratchEndSymbol :: outsideTail
  let c2 : WorkConfiguration :=
    { state := copyScanState distance base
      tape := pathTape locateLeft
        (List.replicate processed registerMarkSymbol ++
          unitSymbol :: List.replicate remaining unitSymbol ++
            rightAfterSource) }
  let markedLeft :=
    List.replicate processed registerMarkSymbol ++ locateLeft
  let c3 : WorkConfiguration :=
    { state := copyScanState distance base
      tape := pathTape markedLeft
        (unitSymbol :: List.replicate remaining unitSymbol ++
          rightAfterSource) }
  let c4 : WorkConfiguration :=
    { state := copySeekEndState distance base
      tape := leftPathTape
        (registerMarkSymbol ::
          List.replicate remaining unitSymbol ++ rightAfterSource)
        markedLeft }
  let markedWord :=
    copyMarkedWord older remaining processed
      intermediate destination
  let c5 := endConfiguration (copyAppendFirstState distance base)
    outsideTail markedWord inside
  let c6 := endConfiguration base (outsideTail.drop 1)
    (copyLoopWord older remaining (processed + 1)
      intermediate destination) inside
  have hMachineDistance : distance = intermediate.length + 1 := rfl
  have hStartStep := copy_start_step distance base next dead
    specPrefix suffix (endTape outsideTail
      (copyLoopWord older (remaining + 1) processed
        intermediate destination) inside) hBase rfl
  have hStart : workRunExact? (closedSpecMachine machineSpecs) 1 c0 =
      some c1 := by
    apply workRunExact_one_for
    simpa [machineSpecs, c0, c1, copyLoopWord, newer, traversal,
      rightAfterSource, endConfiguration,
      registerWord_newer_reverse, List.reverse_append,
      List.reverse_cons, List.reverse_replicate, List.replicate_succ,
      replicate_unit_cons_comm, List.append_assoc]
      using hStartStep
  have hLocatePrefix :
      (specPrefix ++ [copyStartSpec base dead]).length =
        copyLocateBase base := by
    simp [copyLocateBase, hBase]
  have hLocate := locate_traversal_exact newer.reverse
    (copyLocateBase base) (copyScanState distance base) dead
    (specPrefix ++ [copyStartSpec base dead]) (loopTail ++ suffix)
    (scratchEndSymbol :: outsideTail)
    (List.replicate processed registerMarkSymbol ++
      unitSymbol :: List.replicate remaining unitSymbol ++ rightAfterSource)
    (by simpa [newer] using
      (copyNewerValues_ne_nil intermediate destination processed))
    hLocatePrefix
  have hLocateMachine :
      specPrefix ++ [copyStartSpec base dead] ++
          locateSpecs newer.reverse.length (copyLocateBase base)
            (copyScanState distance base) dead ++ (loopTail ++ suffix) =
        machineSpecs := by
    simp [machineSpecs, copySpecs, loopTail, newer, distance,
      copyNewerValues_length, List.append_assoc]
  rw [hLocateMachine] at hLocate
  have hLocateExact :
      workRunExact? (closedSpecMachine machineSpecs)
        (newer.length + newer.sum) c1 = some c2 := by
    simpa [c1, c2, newer, traversal, locateLeft, Nat.add_comm]
      using hLocate
  have hScan := copy_scan_marks_exact distance base next dead processed
    specPrefix suffix locateLeft
    (unitSymbol :: List.replicate remaining unitSymbol ++ rightAfterSource)
    hBase
  have hScanExact :
      workRunExact? (closedSpecMachine machineSpecs) processed c2 =
        some c3 := by
    simpa [machineSpecs, c2, c3, markedLeft, List.append_assoc]
      using hScan
  have hMarkStep := copy_scan_unit_step distance base next dead
    specPrefix suffix
    (pathTape markedLeft
      (unitSymbol :: List.replicate remaining unitSymbol ++
        rightAfterSource)) hBase rfl
  have hMarkedLeft : markedLeft ≠ [] := by
    simp [markedLeft, locateLeft]
  have hMarkTape := pathTape_write_moveLeft_of_ne_nil markedLeft
    unitSymbol registerMarkSymbol
    (List.replicate remaining unitSymbol ++ rightAfterSource) hMarkedLeft
  have hMark :
      workRunExact? (closedSpecMachine machineSpecs) 1 c3 = some c4 := by
    apply workRunExact_one_for
    simp only [List.cons_append] at hMarkStep
    rw [hMarkTape] at hMarkStep
    simpa [machineSpecs, c3, c4] using hMarkStep
  have hMarkedScratch :
      ∀ symbol ∈ List.replicate processed registerMarkSymbol ++ newerWord,
        ScratchSymbol symbol := by
    apply scratch_append
    · intro symbol hMem
      exact Or.inr (Or.inr (List.eq_of_mem_replicate hMem))
    · exact registerWord_scratch _
  have hSeek := copy_seek_end_exact distance base next dead
    specPrefix suffix
    (List.replicate processed registerMarkSymbol ++ newerWord)
    outsideTail
    (registerMarkSymbol ::
      List.replicate remaining unitSymbol ++ rightAfterSource)
    hBase hMarkedScratch
  have hSeekExact :
      workRunExact? (closedSpecMachine machineSpecs)
        ((List.replicate processed registerMarkSymbol ++
          newerWord).length + 1) c4 = some c5 := by
    simpa [machineSpecs, c4, c5, endConfiguration, endTape,
      markedLeft, locateLeft, traversal,
      newerWord, newer, markedWord, copyMarkedWord, rightAfterSource,
      registerWord_newer_reverse, locateTraversalWord_newer_reverse,
      List.reverse_append,
      List.reverse_cons, List.reverse_replicate, List.replicate_succ,
      replicate_cons_comm, List.append_assoc,
      Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
      using hSeek
  have hAppend := copy_append_exact distance base next dead
    specPrefix suffix outsideTail markedWord inside hBase
  have hAppendExact :
      workRunExact? (closedSpecMachine machineSpecs) 2 c5 = some c6 := by
    simpa [machineSpecs, c5, c6, markedWord, copyLoopWord,
      copyMarkedWord, copyNewerValues, registerWord, List.append_assoc,
      replicate_unit_append_singleton,
      Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
      using hAppend
  have h01 := workRunExact_compose_for (closedSpecMachine machineSpecs)
    1 (newer.length + newer.sum) c0 c1 c2 hStart hLocateExact
  have h03 := workRunExact_compose_for (closedSpecMachine machineSpecs)
    (1 + (newer.length + newer.sum)) processed c0 c2 c3 h01 hScanExact
  have h04 := workRunExact_compose_for (closedSpecMachine machineSpecs)
    (1 + (newer.length + newer.sum) + processed) 1 c0 c3 c4
    h03 hMark
  have h05 := workRunExact_compose_for (closedSpecMachine machineSpecs)
    (1 + (newer.length + newer.sum) + processed + 1)
    ((List.replicate processed registerMarkSymbol ++ newerWord).length + 1)
    c0 c4 c5 h04 hSeekExact
  have h06 := workRunExact_compose_for (closedSpecMachine machineSpecs)
    (1 + (newer.length + newer.sum) + processed + 1 +
      ((List.replicate processed registerMarkSymbol ++
      newerWord).length + 1)) 2 c0 c5 c6 h05 hAppendExact
  have hSteps :
      1 + (newer.length + newer.sum) + processed + 1 +
          ((List.replicate processed registerMarkSymbol ++
            newerWord).length + 1) + 2 =
        copyIterationSteps intermediate destination processed := by
    simp [copyIterationSteps, newer, newerWord, copyNewerValues,
      registerWord_length]
    omega
  rw [hSteps] at h06
  simpa [machineSpecs, c0, c6, distance,
    Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h06

private def copyFinishedWord
    (older : List WorkSymbol) (sourceValue : Nat)
    (intermediate : List Nat) (destination : Nat) : List WorkSymbol :=
  older ++ separatorSymbol ::
    (List.replicate sourceValue unitSymbol ++
      registerWord
        (copyNewerValues intermediate destination sourceValue))

private theorem copy_finish_exact
    (base next dead : Nat) (specPrefix suffix : List StateSpec)
    (older inside outsideTail : List WorkSymbol)
    (processed destination : Nat) (intermediate : List Nat)
    (hBase : specPrefix.length = base) :
    workRunExact?
        (closedSpecMachine
          (specPrefix ++
            copySpecs (intermediate.length + 1) base next dead ++ suffix))
        (copyFinishSteps intermediate destination processed)
        (endConfiguration base outsideTail
          (copyLoopWord older 0 processed intermediate destination) inside) =
      some
        (endConfiguration next outsideTail
          (copyFinishedWord older processed intermediate destination)
          inside) := by
  let distance := intermediate.length + 1
  let newer := copyNewerValues intermediate destination processed
  let traversal := locateTraversalWord newer.reverse
  let newerWord := registerWord newer
  let loopTail : List StateSpec :=
    [copyScanSpec distance base dead,
     copySeekEndSpec distance base dead,
     copyAppendFirstSpec distance base dead,
     copyAppendSecondSpec base,
     copyRestoreSpec distance base dead,
     copySeekEndDoneSpec distance base next dead]
  let machineSpecs :=
    specPrefix ++ copySpecs distance base next dead ++ suffix
  let rightAfterSource := separatorSymbol :: older.reverse ++ inside
  let c0 := endConfiguration base outsideTail
    (copyLoopWord older 0 processed intermediate destination) inside
  let c1 : WorkConfiguration :=
    { state := copyLocateBase base
      tape := pathTape (scratchEndSymbol :: outsideTail)
        (traversal ++
          List.replicate processed registerMarkSymbol ++
            rightAfterSource) }
  let locateLeft := traversal.reverse ++ scratchEndSymbol :: outsideTail
  let c2 : WorkConfiguration :=
    { state := copyScanState distance base
      tape := pathTape locateLeft
        (List.replicate processed registerMarkSymbol ++
          rightAfterSource) }
  let markedLeft :=
    List.replicate processed registerMarkSymbol ++ locateLeft
  let c3 : WorkConfiguration :=
    { state := copyScanState distance base
      tape := pathTape markedLeft rightAfterSource }
  let c4 : WorkConfiguration :=
    { state := copyRestoreState distance base
      tape := leftPathTape rightAfterSource markedLeft }
  obtain ⟨newerTail, hNewerWord⟩ :
      ∃ tail, newerWord = separatorSymbol :: tail := by
    have hNewer : newer ≠ [] := by
      simpa [newer] using
        (copyNewerValues_ne_nil intermediate destination processed)
    cases h : newer with
    | nil => contradiction
    | cons value rest =>
        refine ⟨List.replicate value unitSymbol ++ registerWord rest, ?_⟩
        simp [newerWord, h, registerWord]
  have hNewerWord' :
      registerWord newer = separatorSymbol :: newerTail := by
    simpa [newerWord] using hNewerWord
  let restoredRight :=
    List.replicate processed unitSymbol ++ rightAfterSource
  let c5 : WorkConfiguration :=
    { state := copyRestoreState distance base
      tape := leftPathTape restoredRight
        (newerWord ++ scratchEndSymbol :: outsideTail) }
  let c6 : WorkConfiguration :=
    { state := copySeekEndDoneState distance base
      tape := leftPathTape (separatorSymbol :: restoredRight)
        (newerTail ++ scratchEndSymbol :: outsideTail) }
  let c7 := endConfiguration next outsideTail
    (copyFinishedWord older processed intermediate destination) inside
  have hStartStep := copy_start_step distance base next dead
    specPrefix suffix
    (endTape outsideTail
      (copyLoopWord older 0 processed intermediate destination) inside)
    hBase rfl
  have hStart : workRunExact? (closedSpecMachine machineSpecs) 1 c0 =
      some c1 := by
    apply workRunExact_one_for
    simpa [machineSpecs, c0, c1, copyLoopWord, newer, traversal,
      rightAfterSource, endConfiguration, registerWord_newer_reverse,
      List.reverse_append, List.reverse_cons, List.reverse_replicate,
      List.append_assoc] using hStartStep
  have hLocatePrefix :
      (specPrefix ++ [copyStartSpec base dead]).length =
        copyLocateBase base := by
    simp [copyLocateBase, hBase]
  have hLocate := locate_traversal_exact newer.reverse
    (copyLocateBase base) (copyScanState distance base) dead
    (specPrefix ++ [copyStartSpec base dead]) (loopTail ++ suffix)
    (scratchEndSymbol :: outsideTail)
    (List.replicate processed registerMarkSymbol ++ rightAfterSource)
    (by simpa [newer] using
      (copyNewerValues_ne_nil intermediate destination processed))
    hLocatePrefix
  have hLocateMachine :
      specPrefix ++ [copyStartSpec base dead] ++
          locateSpecs newer.reverse.length (copyLocateBase base)
            (copyScanState distance base) dead ++ (loopTail ++ suffix) =
        machineSpecs := by
    simp [machineSpecs, copySpecs, loopTail, newer, distance,
      copyNewerValues_length, List.append_assoc]
  rw [hLocateMachine] at hLocate
  have hLocateExact :
      workRunExact? (closedSpecMachine machineSpecs)
        (newer.length + newer.sum) c1 = some c2 := by
    simpa [c1, c2, newer, traversal, locateLeft, Nat.add_comm]
      using hLocate
  have hScan := copy_scan_marks_exact distance base next dead processed
    specPrefix suffix locateLeft rightAfterSource hBase
  have hScanExact :
      workRunExact? (closedSpecMachine machineSpecs) processed c2 =
        some c3 := by
    simpa [machineSpecs, c2, c3, markedLeft, List.append_assoc]
      using hScan
  have hFinishStep := copy_scan_finish_step distance base next dead
    specPrefix suffix (pathTape markedLeft rightAfterSource) hBase rfl
  have hMarkedLeft : markedLeft ≠ [] := by
    simp [markedLeft, locateLeft]
  have hFinishTape :
      (pathTape markedLeft rightAfterSource).moveLeft =
        leftPathTape rightAfterSource markedLeft := by
    cases hMarked : markedLeft with
    | nil => exact False.elim (hMarkedLeft hMarked)
    | cons first rest => rfl
  have hFinish :
      workRunExact? (closedSpecMachine machineSpecs) 1 c3 = some c4 := by
    apply workRunExact_one_for
    rw [hFinishTape] at hFinishStep
    simpa [machineSpecs, c3, c4] using hFinishStep
  have hRestore := copy_restore_marks_exact distance base next dead
    processed specPrefix suffix
    (newerWord ++ scratchEndSymbol :: outsideTail) rightAfterSource hBase
  have hRestoreExact :
      workRunExact? (closedSpecMachine machineSpecs) processed c4 =
        some c5 := by
    simpa [machineSpecs, c4, c5, markedLeft, locateLeft, traversal,
      newerWord, newer, restoredRight,
      locateTraversalWord_newer_reverse, List.append_assoc]
      using hRestore
  have hBoundaryStep := copy_restore_separator_step distance base next dead
    specPrefix suffix
    (leftPathTape restoredRight
      (separatorSymbol :: newerTail ++ scratchEndSymbol :: outsideTail))
    hBase rfl
  have hBoundary :
      workRunExact? (closedSpecMachine machineSpecs) 1 c5 = some c6 := by
    apply workRunExact_one_for
    dsimp [c5]
    rw [hNewerWord]
    simpa [machineSpecs, c6, List.cons_append] using hBoundaryStep
  have hNewerTailScratch :
      ∀ symbol ∈ newerTail, ScratchSymbol symbol := by
    intro symbol hMem
    apply registerWord_scratch newer symbol
    rw [hNewerWord']
    exact List.Mem.tail separatorSymbol hMem
  have hDone := copy_seek_done_exact distance base next dead
    specPrefix suffix newerTail outsideTail
    (separatorSymbol :: restoredRight) hBase hNewerTailScratch
  have hDoneExact :
      workRunExact? (closedSpecMachine machineSpecs)
        (newerTail.length + 1) c6 = some c7 := by
    simpa [machineSpecs, c6, c7, restoredRight, rightAfterSource,
      copyFinishedWord, endConfiguration, endTape, newerWord, newer,
      hNewerWord, registerWord_newer_reverse, List.reverse_append,
      List.reverse_cons, List.reverse_replicate, List.append_assoc,
      Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hDone
  have h01 := workRunExact_compose_for (closedSpecMachine machineSpecs)
    1 (newer.length + newer.sum) c0 c1 c2 hStart hLocateExact
  have h03 := workRunExact_compose_for (closedSpecMachine machineSpecs)
    (1 + (newer.length + newer.sum)) processed c0 c2 c3 h01 hScanExact
  have h04 := workRunExact_compose_for (closedSpecMachine machineSpecs)
    (1 + (newer.length + newer.sum) + processed) 1 c0 c3 c4
    h03 hFinish
  have h05 := workRunExact_compose_for (closedSpecMachine machineSpecs)
    (1 + (newer.length + newer.sum) + processed + 1) processed
    c0 c4 c5 h04 hRestoreExact
  have h06 := workRunExact_compose_for (closedSpecMachine machineSpecs)
    (1 + (newer.length + newer.sum) + processed + 1 + processed) 1
    c0 c5 c6 h05 hBoundary
  have h07 := workRunExact_compose_for (closedSpecMachine machineSpecs)
    (1 + (newer.length + newer.sum) + processed + 1 + processed + 1)
    (newerTail.length + 1) c0 c6 c7 h06 hDoneExact
  have hNewerLength : newerTail.length + 1 = newerWord.length := by
    rw [hNewerWord]
    simp
  have hSteps :
      1 + (newer.length + newer.sum) + processed + 1 + processed + 1 +
          (newerTail.length + 1) =
        copyFinishSteps intermediate destination processed := by
    rw [hNewerLength]
    simp [copyFinishSteps, newer, newerWord, copyNewerValues,
      registerWord_length]
    omega
  rw [hSteps] at h07
  simpa [machineSpecs, c0, c7, distance] using h07

private def copyLoopSteps
    (intermediate : List Nat) (destination : Nat) : Nat → Nat → Nat
  | processed, 0 =>
      copyFinishSteps intermediate destination processed
  | processed, remaining + 1 =>
      copyIterationSteps intermediate destination processed +
        copyLoopSteps intermediate destination (processed + 1) remaining

private def copySteps
    (intermediate : List Nat) (destination sourceValue : Nat) : Nat :=
  copyLoopSteps intermediate destination 0 sourceValue

private theorem copy_loop_exact
    (base next dead : Nat) (specPrefix suffix : List StateSpec)
    (older inside outsideTail : List WorkSymbol)
    (remaining processed destination : Nat)
    (intermediate : List Nat)
    (hBase : specPrefix.length = base) :
    workRunExact?
        (closedSpecMachine
          (specPrefix ++
            copySpecs (intermediate.length + 1) base next dead ++ suffix))
        (copyLoopSteps intermediate destination processed remaining)
        (endConfiguration base outsideTail
          (copyLoopWord older remaining processed intermediate destination)
          inside) =
      some
        (endConfiguration next (outsideTail.drop remaining)
          (copyFinishedWord older (processed + remaining)
            intermediate destination) inside) := by
  induction remaining generalizing processed outsideTail with
  | zero =>
      simpa [copyLoopSteps, copyFinishedWord] using
        (copy_finish_exact base next dead specPrefix suffix older inside
          outsideTail processed destination intermediate hBase)
  | succ remaining ih =>
      have hIteration := copy_iteration_exact base next dead specPrefix suffix
        older inside outsideTail remaining processed destination intermediate
        hBase
      have hRest := ih (outsideTail.drop 1) (processed + 1)
      have hAll := workRunExact_compose_for
        (closedSpecMachine
          (specPrefix ++
            copySpecs (intermediate.length + 1) base next dead ++ suffix))
        (copyIterationSteps intermediate destination processed)
        (copyLoopSteps intermediate destination (processed + 1) remaining)
        (endConfiguration base outsideTail
          (copyLoopWord older (remaining + 1) processed
            intermediate destination) inside)
        (endConfiguration base (outsideTail.drop 1)
          (copyLoopWord older remaining (processed + 1)
            intermediate destination) inside)
        (endConfiguration next
          ((outsideTail.drop 1).drop remaining)
          (copyFinishedWord older (processed + 1 + remaining)
            intermediate destination) inside)
        hIteration hRest
      simpa [copyLoopSteps, List.drop_drop, Nat.add_assoc,
        Nat.add_comm, Nat.add_left_comm] using hAll

private theorem copy_exact
    (base next dead : Nat) (specPrefix suffix : List StateSpec)
    (older inside outsideTail : List WorkSymbol)
    (sourceValue destination : Nat) (intermediate : List Nat)
    (hBase : specPrefix.length = base) :
    workRunExact?
        (closedSpecMachine
          (specPrefix ++
            copySpecs (intermediate.length + 1) base next dead ++ suffix))
        (copySteps intermediate destination sourceValue)
        (endConfiguration base outsideTail
          (older ++ registerWord
            ([sourceValue] ++ intermediate ++ [destination])) inside) =
      some
        (endConfiguration next (outsideTail.drop sourceValue)
          (older ++ registerWord
            ([sourceValue] ++ intermediate ++
              [destination + sourceValue])) inside) := by
  have hLoop := copy_loop_exact base next dead specPrefix suffix older inside
    outsideTail sourceValue 0 destination intermediate hBase
  simpa [copySteps, copyLoopWord, copyFinishedWord, copyNewerValues,
    registerWord, List.append_assoc, Nat.add_assoc, Nat.add_comm,
    Nat.add_left_comm] using hLoop

private def addOperationSteps
    (rightValues : List Nat) (leftValue rightValue : Nat) : Nat :=
  2 + copySteps rightValues 0 leftValue +
    copySteps [] leftValue rightValue

private theorem addOperation_exact
    (rightNodes base next dead : Nat)
    (specPrefix suffix : List StateSpec)
    (existing leftPrefix rightPrefix : List Nat)
    (leftValue rightValue : Nat)
    (inside outsideTail : List WorkSymbol)
    (hBase : specPrefix.length = base)
    (hRightNodes : (rightPrefix ++ [rightValue]).length = rightNodes) :
    workRunExact?
        (closedSpecMachine
          (specPrefix ++
            addOperationSpecs rightNodes base next dead ++ suffix))
        (addOperationSteps (rightPrefix ++ [rightValue])
          leftValue rightValue)
        (endConfiguration base outsideTail
          (registerWord
            (existing ++ leftPrefix ++ [leftValue] ++
              rightPrefix ++ [rightValue])) inside) =
      some
        (endConfiguration next
          (outsideTail.drop (leftValue + rightValue + 1))
          (registerWord
            (existing ++ leftPrefix ++ [leftValue] ++
              rightPrefix ++ [rightValue, leftValue + rightValue]))
          inside) := by
  let leftDistance := rightNodes + 1
  let leftBase := base + 2
  let rightBase := leftBase + copyStateCount leftDistance
  let rightValues := rightPrefix ++ [rightValue]
  let startWord := registerWord
    (existing ++ leftPrefix ++ [leftValue] ++ rightValues)
  let afterSeparatorWord := startWord ++ [separatorSymbol]
  let afterLeftWord := registerWord
    (existing ++ leftPrefix ++ [leftValue] ++ rightValues ++ [leftValue])
  let finalWord := registerWord
    (existing ++ leftPrefix ++ [leftValue] ++
      rightPrefix ++ [rightValue, leftValue + rightValue])
  let machineSpecs :=
    specPrefix ++ addOperationSpecs rightNodes base next dead ++ suffix
  have hSeparator := separator_exact base leftBase dead specPrefix
    (copySpecs leftDistance leftBase rightBase dead ++
      copySpecs 1 rightBase next dead ++ suffix)
    outsideTail startWord inside hBase
  have hLeftPrefix :
      (specPrefix ++ separatorSpecs base leftBase dead).length =
        leftBase := by
    simp [leftBase, hBase]
  have hLeft := copy_exact leftBase rightBase dead
    (specPrefix ++ separatorSpecs base leftBase dead)
    (copySpecs 1 rightBase next dead ++ suffix)
    (registerWord (existing ++ leftPrefix)) inside
    (outsideTail.drop 1) leftValue 0 rightValues hLeftPrefix
  have hRightPrefix :
      (specPrefix ++ separatorSpecs base leftBase dead ++
        copySpecs leftDistance leftBase rightBase dead).length =
          rightBase := by
    simp [leftBase, rightBase, leftDistance, hBase,
      copyStateCount]
    omega
  have hRight := copy_exact rightBase next dead
    (specPrefix ++ separatorSpecs base leftBase dead ++
      copySpecs leftDistance leftBase rightBase dead)
    suffix
    (registerWord
      (existing ++ leftPrefix ++ [leftValue] ++ rightPrefix))
    inside ((outsideTail.drop 1).drop leftValue)
    rightValue leftValue [] hRightPrefix
  have hMachine :
      specPrefix ++ separatorSpecs base leftBase dead ++
          copySpecs leftDistance leftBase rightBase dead ++
            copySpecs 1 rightBase next dead ++ suffix =
        machineSpecs := by
    simp [machineSpecs, addOperationSpecs, leftDistance, leftBase,
      rightBase, List.append_assoc]
  have hDistance : rightValues.length + 1 = leftDistance := by
    simp [rightValues, leftDistance] at hRightNodes ⊢
    omega
  rw [hDistance] at hLeft
  simp only [List.length_nil, Nat.zero_add] at hRight
  simp only [List.append_assoc] at hSeparator hLeft hRight hMachine
  rw [hMachine] at hSeparator hLeft hRight
  have hSeparatorExact :
      workRunExact? (closedSpecMachine machineSpecs) 2
        (endConfiguration base outsideTail startWord inside) =
      some
        (endConfiguration leftBase (outsideTail.drop 1)
          afterSeparatorWord inside) := by
    simpa [startWord, afterSeparatorWord] using hSeparator
  have hLeftExact :
      workRunExact? (closedSpecMachine machineSpecs)
          (copySteps rightValues 0 leftValue)
          (endConfiguration leftBase (outsideTail.drop 1)
            afterSeparatorWord inside) =
        some
          (endConfiguration rightBase
            ((outsideTail.drop 1).drop leftValue)
            afterLeftWord inside) := by
    simpa [afterSeparatorWord, afterLeftWord, startWord, rightValues,
      leftDistance, hRightNodes, registerWord, List.append_assoc]
      using hLeft
  have hRightExact :
      workRunExact? (closedSpecMachine machineSpecs)
          (copySteps [] leftValue rightValue)
          (endConfiguration rightBase
            ((outsideTail.drop 1).drop leftValue)
            afterLeftWord inside) =
        some
          (endConfiguration next
            (((outsideTail.drop 1).drop leftValue).drop rightValue)
            finalWord inside) := by
    simpa [afterLeftWord, finalWord, rightValues, registerWord,
      List.append_assoc, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
      using hRight
  have h01 := workRunExact_compose_for (closedSpecMachine machineSpecs)
    2 (copySteps rightValues 0 leftValue)
    (endConfiguration base outsideTail startWord inside)
    (endConfiguration leftBase (outsideTail.drop 1)
      afterSeparatorWord inside)
    (endConfiguration rightBase
      ((outsideTail.drop 1).drop leftValue) afterLeftWord inside)
    hSeparatorExact hLeftExact
  have h02 := workRunExact_compose_for (closedSpecMachine machineSpecs)
    (2 + copySteps rightValues 0 leftValue)
    (copySteps [] leftValue rightValue)
    (endConfiguration base outsideTail startWord inside)
    (endConfiguration rightBase
      ((outsideTail.drop 1).drop leftValue) afterLeftWord inside)
    (endConfiguration next
      (((outsideTail.drop 1).drop leftValue).drop rightValue)
      finalWord inside) h01 hRightExact
  have hStartWord :
      startWord = registerWord
        (existing ++ leftPrefix ++ [leftValue] ++
          rightPrefix ++ [rightValue]) := by
    change registerWord
        (existing ++ leftPrefix ++ [leftValue] ++
          (rightPrefix ++ [rightValue])) = _
    apply congrArg registerWord
    simp [List.append_assoc]
  have hFinalWord :
      finalWord = registerWord
        (existing ++ leftPrefix ++ [leftValue] ++
          rightPrefix ++ [rightValue, leftValue + rightValue]) := rfl
  rw [← hStartWord, ← hFinalWord]
  simpa [machineSpecs, addOperationSteps, List.drop_drop,
    Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h02

/-! ### Exact multiplication loop phases -/

private theorem multiply_start_step
    (leftDistance base next dead : Nat)
    (specPrefix suffix : List StateSpec) (tape : WorkTape)
    (hBase : specPrefix.length = base)
    (hHead : tape.head = scratchEndSymbol) :
    workStep?
        (closedSpecMachine
          (specPrefix ++
            multiplyLoopSpecs leftDistance base next dead ++ suffix))
        { state := base, tape := tape } =
      some { state := multiplyLocateBase base, tape := tape.moveRight } := by
  have hStep := closedSpecMachine_step specPrefix
    (multiplyStartSpec base dead)
    (locateSpecs leftDistance (multiplyLocateBase base)
        (multiplyScanState leftDistance base) dead ++
      [multiplyScanSpec leftDistance base dead,
       multiplySeekCopyEndSpec leftDistance base dead] ++
      copySpecs 1 (multiplyRightCopyBase leftDistance base) base dead ++
      [multiplyRestoreSpec leftDistance base dead,
       multiplySeekEndDoneSpec leftDistance base next dead] ++ suffix) tape
  have hAction : multiplyStartSpec base dead tape.head =
      keepAction (multiplyLocateBase base) .right tape.head := by
    simp [multiplyStartSpec, hHead]
  rw [hAction] at hStep
  simpa [multiplyLoopSpecs, keepAction, WorkTape.move,
    List.append_assoc, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm,
    hBase] using hStep

private theorem multiply_scan_mark_step
    (leftDistance base next dead : Nat)
    (specPrefix suffix : List StateSpec) (tape : WorkTape)
    (hBase : specPrefix.length = base)
    (hHead : tape.head = registerMarkSymbol) :
    workStep?
        (closedSpecMachine
          (specPrefix ++
            multiplyLoopSpecs leftDistance base next dead ++ suffix))
        { state := multiplyScanState leftDistance base, tape := tape } =
      some
        { state := multiplyScanState leftDistance base
          tape := tape.moveRight } := by
  let scanPrefix := specPrefix ++ [multiplyStartSpec base dead] ++
    locateSpecs leftDistance (multiplyLocateBase base)
      (multiplyScanState leftDistance base) dead
  have hStep := closedSpecMachine_step scanPrefix
    (multiplyScanSpec leftDistance base dead)
    ([multiplySeekCopyEndSpec leftDistance base dead] ++
      copySpecs 1 (multiplyRightCopyBase leftDistance base) base dead ++
      [multiplyRestoreSpec leftDistance base dead,
       multiplySeekEndDoneSpec leftDistance base next dead] ++ suffix) tape
  have hAction : multiplyScanSpec leftDistance base dead tape.head =
      keepAction (multiplyScanState leftDistance base) .right tape.head := by
    simp [multiplyScanSpec, hHead]
  rw [hAction] at hStep
  simpa [multiplyLoopSpecs, scanPrefix, multiplyScanState,
    multiplyLocateBase, keepAction, WorkTape.move, List.append_assoc,
    Nat.add_assoc, Nat.add_comm, Nat.add_left_comm, hBase] using hStep

private theorem multiply_scan_unit_step
    (leftDistance base next dead : Nat)
    (specPrefix suffix : List StateSpec) (tape : WorkTape)
    (hBase : specPrefix.length = base)
    (hHead : tape.head = unitSymbol) :
    workStep?
        (closedSpecMachine
          (specPrefix ++
            multiplyLoopSpecs leftDistance base next dead ++ suffix))
        { state := multiplyScanState leftDistance base, tape := tape } =
      some
        { state := multiplySeekCopyEndState leftDistance base
          tape := (tape.write registerMarkSymbol).moveLeft } := by
  let scanPrefix := specPrefix ++ [multiplyStartSpec base dead] ++
    locateSpecs leftDistance (multiplyLocateBase base)
      (multiplyScanState leftDistance base) dead
  have hStep := closedSpecMachine_step scanPrefix
    (multiplyScanSpec leftDistance base dead)
    ([multiplySeekCopyEndSpec leftDistance base dead] ++
      copySpecs 1 (multiplyRightCopyBase leftDistance base) base dead ++
      [multiplyRestoreSpec leftDistance base dead,
       multiplySeekEndDoneSpec leftDistance base next dead] ++ suffix) tape
  simpa [multiplyLoopSpecs, scanPrefix, multiplyScanSpec, hHead,
    unitSymbol, registerMarkSymbol, WorkSymbol.oneOne,
    WorkSymbol.zeroZero, writeAction, WorkTape.move,
    multiplyScanState, multiplyLocateBase, multiplySeekCopyEndState,
    List.append_assoc, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm,
    hBase] using hStep

private theorem multiply_scan_finish_step
    (leftDistance base next dead : Nat)
    (specPrefix suffix : List StateSpec) (tape : WorkTape)
    (hBase : specPrefix.length = base)
    (hHead : tape.head = separatorSymbol) :
    workStep?
        (closedSpecMachine
          (specPrefix ++
            multiplyLoopSpecs leftDistance base next dead ++ suffix))
        { state := multiplyScanState leftDistance base, tape := tape } =
      some
        { state := multiplyRestoreState leftDistance base
          tape := tape.moveLeft } := by
  let scanPrefix := specPrefix ++ [multiplyStartSpec base dead] ++
    locateSpecs leftDistance (multiplyLocateBase base)
      (multiplyScanState leftDistance base) dead
  have hStep := closedSpecMachine_step scanPrefix
    (multiplyScanSpec leftDistance base dead)
    ([multiplySeekCopyEndSpec leftDistance base dead] ++
      copySpecs 1 (multiplyRightCopyBase leftDistance base) base dead ++
      [multiplyRestoreSpec leftDistance base dead,
       multiplySeekEndDoneSpec leftDistance base next dead] ++ suffix) tape
  have hAction : multiplyScanSpec leftDistance base dead tape.head =
      keepAction (multiplyRestoreState leftDistance base) .left tape.head := by
    simp [multiplyScanSpec, hHead, separatorSymbol, unitSymbol,
      registerMarkSymbol, WorkSymbol.zeroOne, WorkSymbol.oneOne,
      WorkSymbol.zeroZero]
  rw [hAction] at hStep
  simpa [multiplyLoopSpecs, scanPrefix, multiplyScanState,
    multiplyLocateBase, multiplyRestoreState, multiplyRightCopyBase,
    copyStateCount, keepAction, WorkTape.move, List.append_assoc,
    Nat.add_assoc, Nat.add_comm, Nat.add_left_comm, hBase] using hStep

private theorem multiply_seek_scratch_step
    (leftDistance base next dead : Nat)
    (specPrefix suffix : List StateSpec) (tape : WorkTape)
    (hBase : specPrefix.length = base)
    (hScratch : ScratchSymbol tape.head) :
    workStep?
        (closedSpecMachine
          (specPrefix ++
            multiplyLoopSpecs leftDistance base next dead ++ suffix))
        { state := multiplySeekCopyEndState leftDistance base, tape := tape } =
      some
        { state := multiplySeekCopyEndState leftDistance base
          tape := tape.moveLeft } := by
  let seekPrefix := specPrefix ++ [multiplyStartSpec base dead] ++
    locateSpecs leftDistance (multiplyLocateBase base)
      (multiplyScanState leftDistance base) dead ++
    [multiplyScanSpec leftDistance base dead]
  have hStep := closedSpecMachine_step seekPrefix
    (multiplySeekCopyEndSpec leftDistance base dead)
    (copySpecs 1 (multiplyRightCopyBase leftDistance base) base dead ++
      [multiplyRestoreSpec leftDistance base dead,
       multiplySeekEndDoneSpec leftDistance base next dead] ++ suffix) tape
  have hAction : multiplySeekCopyEndSpec leftDistance base dead tape.head =
      keepAction (multiplySeekCopyEndState leftDistance base)
        .left tape.head := by
    rcases hScratch with hUnit | hSeparator | hMark
    · simp [multiplySeekCopyEndSpec, hUnit]
    · simp [multiplySeekCopyEndSpec, hSeparator]
    · simp [multiplySeekCopyEndSpec, hMark]
  rw [hAction] at hStep
  simpa [multiplyLoopSpecs, seekPrefix, multiplyScanState,
    multiplyLocateBase, multiplySeekCopyEndState, keepAction,
    WorkTape.move, List.append_assoc, Nat.add_assoc, Nat.add_comm,
    Nat.add_left_comm, hBase] using hStep

private theorem multiply_seek_marker_step
    (leftDistance base next dead : Nat)
    (specPrefix suffix : List StateSpec) (tape : WorkTape)
    (hBase : specPrefix.length = base)
    (hHead : tape.head = scratchEndSymbol) :
    workStep?
        (closedSpecMachine
          (specPrefix ++
            multiplyLoopSpecs leftDistance base next dead ++ suffix))
        { state := multiplySeekCopyEndState leftDistance base, tape := tape } =
      some
        { state := multiplyRightCopyBase leftDistance base, tape := tape } := by
  let seekPrefix := specPrefix ++ [multiplyStartSpec base dead] ++
    locateSpecs leftDistance (multiplyLocateBase base)
      (multiplyScanState leftDistance base) dead ++
    [multiplyScanSpec leftDistance base dead]
  have hStep := closedSpecMachine_step seekPrefix
    (multiplySeekCopyEndSpec leftDistance base dead)
    (copySpecs 1 (multiplyRightCopyBase leftDistance base) base dead ++
      [multiplyRestoreSpec leftDistance base dead,
       multiplySeekEndDoneSpec leftDistance base next dead] ++ suffix) tape
  have hAction : multiplySeekCopyEndSpec leftDistance base dead tape.head =
      keepAction (multiplyRightCopyBase leftDistance base)
        .stay tape.head := by
    simp [multiplySeekCopyEndSpec, hHead, scratchEndSymbol,
      unitSymbol, separatorSymbol, registerMarkSymbol,
      WorkSymbol.blankOne, WorkSymbol.oneOne, WorkSymbol.zeroOne,
      WorkSymbol.zeroZero]
  rw [hAction] at hStep
  simpa [multiplyLoopSpecs, seekPrefix, multiplyScanState,
    multiplyLocateBase, multiplySeekCopyEndState,
    multiplyRightCopyBase, keepAction, WorkTape.move,
    List.append_assoc, Nat.add_assoc, Nat.add_comm,
    Nat.add_left_comm, hBase] using hStep

private theorem multiply_restore_mark_step
    (leftDistance base next dead : Nat)
    (specPrefix suffix : List StateSpec) (tape : WorkTape)
    (hBase : specPrefix.length = base)
    (hHead : tape.head = registerMarkSymbol) :
    workStep?
        (closedSpecMachine
          (specPrefix ++
            multiplyLoopSpecs leftDistance base next dead ++ suffix))
        { state := multiplyRestoreState leftDistance base, tape := tape } =
      some
        { state := multiplyRestoreState leftDistance base
          tape := (tape.write unitSymbol).moveLeft } := by
  let restorePrefix := specPrefix ++ [multiplyStartSpec base dead] ++
    locateSpecs leftDistance (multiplyLocateBase base)
      (multiplyScanState leftDistance base) dead ++
    [multiplyScanSpec leftDistance base dead,
     multiplySeekCopyEndSpec leftDistance base dead] ++
    copySpecs 1 (multiplyRightCopyBase leftDistance base) base dead
  have hStep := closedSpecMachine_step restorePrefix
    (multiplyRestoreSpec leftDistance base dead)
    ([multiplySeekEndDoneSpec leftDistance base next dead] ++ suffix) tape
  simpa [multiplyLoopSpecs, restorePrefix, multiplyRestoreSpec, hHead,
    registerMarkSymbol, unitSymbol, separatorSymbol,
    WorkSymbol.zeroZero, WorkSymbol.oneOne, WorkSymbol.zeroOne,
    writeAction, WorkTape.move, multiplyScanState, multiplyLocateBase,
    multiplyRightCopyBase, multiplyRestoreState, copyStateCount,
    List.append_assoc, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm,
    hBase] using hStep

private theorem multiply_restore_separator_step
    (leftDistance base next dead : Nat)
    (specPrefix suffix : List StateSpec) (tape : WorkTape)
    (hBase : specPrefix.length = base)
    (hHead : tape.head = separatorSymbol) :
    workStep?
        (closedSpecMachine
          (specPrefix ++
            multiplyLoopSpecs leftDistance base next dead ++ suffix))
        { state := multiplyRestoreState leftDistance base, tape := tape } =
      some
        { state := multiplySeekEndDoneState leftDistance base
          tape := tape.moveLeft } := by
  let restorePrefix := specPrefix ++ [multiplyStartSpec base dead] ++
    locateSpecs leftDistance (multiplyLocateBase base)
      (multiplyScanState leftDistance base) dead ++
    [multiplyScanSpec leftDistance base dead,
     multiplySeekCopyEndSpec leftDistance base dead] ++
    copySpecs 1 (multiplyRightCopyBase leftDistance base) base dead
  have hStep := closedSpecMachine_step restorePrefix
    (multiplyRestoreSpec leftDistance base dead)
    ([multiplySeekEndDoneSpec leftDistance base next dead] ++ suffix) tape
  have hAction : multiplyRestoreSpec leftDistance base dead tape.head =
      keepAction (multiplySeekEndDoneState leftDistance base)
        .left tape.head := by
    simp [multiplyRestoreSpec, hHead, separatorSymbol, unitSymbol,
      registerMarkSymbol, WorkSymbol.zeroOne, WorkSymbol.oneOne,
      WorkSymbol.zeroZero]
  rw [hAction] at hStep
  simpa [multiplyLoopSpecs, restorePrefix, multiplyScanState,
    multiplyLocateBase, multiplyRightCopyBase, multiplyRestoreState,
    multiplySeekEndDoneState, copyStateCount, keepAction, WorkTape.move,
    List.append_assoc, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm,
    hBase] using hStep

private theorem multiply_done_scratch_step
    (leftDistance base next dead : Nat)
    (specPrefix suffix : List StateSpec) (tape : WorkTape)
    (hBase : specPrefix.length = base)
    (hScratch : ScratchSymbol tape.head) :
    workStep?
        (closedSpecMachine
          (specPrefix ++
            multiplyLoopSpecs leftDistance base next dead ++ suffix))
        { state := multiplySeekEndDoneState leftDistance base, tape := tape } =
      some
        { state := multiplySeekEndDoneState leftDistance base
          tape := tape.moveLeft } := by
  let donePrefix := specPrefix ++ [multiplyStartSpec base dead] ++
    locateSpecs leftDistance (multiplyLocateBase base)
      (multiplyScanState leftDistance base) dead ++
    [multiplyScanSpec leftDistance base dead,
     multiplySeekCopyEndSpec leftDistance base dead] ++
    copySpecs 1 (multiplyRightCopyBase leftDistance base) base dead ++
    [multiplyRestoreSpec leftDistance base dead]
  have hStep := closedSpecMachine_step donePrefix
    (multiplySeekEndDoneSpec leftDistance base next dead) suffix tape
  have hAction : multiplySeekEndDoneSpec leftDistance base next dead
      tape.head = keepAction (multiplySeekEndDoneState leftDistance base)
        .left tape.head := by
    rcases hScratch with hUnit | hSeparator | hMark
    · simp [multiplySeekEndDoneSpec, hUnit]
    · simp [multiplySeekEndDoneSpec, hSeparator]
    · simp [multiplySeekEndDoneSpec, hMark]
  rw [hAction] at hStep
  simpa [multiplyLoopSpecs, donePrefix, multiplyScanState,
    multiplyLocateBase, multiplyRightCopyBase, multiplyRestoreState,
    multiplySeekEndDoneState, copyStateCount, keepAction, WorkTape.move,
    List.append_assoc, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm,
    hBase] using hStep

private theorem multiply_done_marker_step
    (leftDistance base next dead : Nat)
    (specPrefix suffix : List StateSpec) (tape : WorkTape)
    (hBase : specPrefix.length = base)
    (hHead : tape.head = scratchEndSymbol) :
    workStep?
        (closedSpecMachine
          (specPrefix ++
            multiplyLoopSpecs leftDistance base next dead ++ suffix))
        { state := multiplySeekEndDoneState leftDistance base, tape := tape } =
      some { state := next, tape := tape } := by
  let donePrefix := specPrefix ++ [multiplyStartSpec base dead] ++
    locateSpecs leftDistance (multiplyLocateBase base)
      (multiplyScanState leftDistance base) dead ++
    [multiplyScanSpec leftDistance base dead,
     multiplySeekCopyEndSpec leftDistance base dead] ++
    copySpecs 1 (multiplyRightCopyBase leftDistance base) base dead ++
    [multiplyRestoreSpec leftDistance base dead]
  have hStep := closedSpecMachine_step donePrefix
    (multiplySeekEndDoneSpec leftDistance base next dead) suffix tape
  have hAction : multiplySeekEndDoneSpec leftDistance base next dead
      tape.head = keepAction next .stay tape.head := by
    simp [multiplySeekEndDoneSpec, hHead, scratchEndSymbol,
      unitSymbol, separatorSymbol, registerMarkSymbol,
      WorkSymbol.blankOne, WorkSymbol.oneOne, WorkSymbol.zeroOne,
      WorkSymbol.zeroZero]
  rw [hAction] at hStep
  simpa [multiplyLoopSpecs, donePrefix, multiplyScanState,
    multiplyLocateBase, multiplyRightCopyBase, multiplyRestoreState,
    multiplySeekEndDoneState, copyStateCount, keepAction, WorkTape.move,
    List.append_assoc, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm,
    hBase] using hStep

private theorem multiply_scan_marks_exact
    (leftDistance base next dead count : Nat)
    (specPrefix suffix : List StateSpec)
    (leftSide rightSide : List WorkSymbol)
    (hBase : specPrefix.length = base) :
    workRunExact?
        (closedSpecMachine
          (specPrefix ++
            multiplyLoopSpecs leftDistance base next dead ++ suffix))
        count
        { state := multiplyScanState leftDistance base
          tape := pathTape leftSide
            (List.replicate count registerMarkSymbol ++ rightSide) } =
      some
        { state := multiplyScanState leftDistance base
          tape := pathTape
            (List.replicate count registerMarkSymbol ++ leftSide)
            rightSide } := by
  induction count generalizing leftSide with
  | zero => rfl
  | succ count ih =>
      have hStep := multiply_scan_mark_step leftDistance base next dead
        specPrefix suffix
        (pathTape leftSide
          (registerMarkSymbol ::
            List.replicate count registerMarkSymbol ++ rightSide))
        hBase rfl
      have hFirst := workRunExact_one_for
        (closedSpecMachine
          (specPrefix ++
            multiplyLoopSpecs leftDistance base next dead ++ suffix))
        { state := multiplyScanState leftDistance base
          tape := pathTape leftSide
            (registerMarkSymbol ::
              List.replicate count registerMarkSymbol ++ rightSide) }
        { state := multiplyScanState leftDistance base
          tape := pathTape (registerMarkSymbol :: leftSide)
            (List.replicate count registerMarkSymbol ++ rightSide) }
        (by simpa using hStep)
      have hRest := ih (registerMarkSymbol :: leftSide)
      have hAll := workRunExact_compose_for
        (closedSpecMachine
          (specPrefix ++
            multiplyLoopSpecs leftDistance base next dead ++ suffix))
        1 count
        { state := multiplyScanState leftDistance base
          tape := pathTape leftSide
            (registerMarkSymbol ::
              List.replicate count registerMarkSymbol ++ rightSide) }
        { state := multiplyScanState leftDistance base
          tape := pathTape (registerMarkSymbol :: leftSide)
            (List.replicate count registerMarkSymbol ++ rightSide) }
        { state := multiplyScanState leftDistance base
          tape := pathTape
            (List.replicate count registerMarkSymbol ++
              registerMarkSymbol :: leftSide) rightSide }
        hFirst hRest
      rw [replicate_cons_comm registerMarkSymbol count leftSide] at hAll
      simpa [List.replicate_succ, List.append_assoc,
        Nat.add_comm] using hAll

private theorem multiply_seek_exact
    (leftDistance base next dead : Nat)
    (specPrefix suffix : List StateSpec)
    (symbols outsideTail rightSide : List WorkSymbol)
    (hBase : specPrefix.length = base)
    (hScratch : ∀ symbol ∈ symbols, ScratchSymbol symbol) :
    workRunExact?
        (closedSpecMachine
          (specPrefix ++
            multiplyLoopSpecs leftDistance base next dead ++ suffix))
        (symbols.length + 1)
        { state := multiplySeekCopyEndState leftDistance base
          tape := leftPathTape rightSide
            (symbols ++ scratchEndSymbol :: outsideTail) } =
      some
        { state := multiplyRightCopyBase leftDistance base
          tape :=
            { left := outsideTail
              head := scratchEndSymbol
              right := symbols.reverse ++ rightSide } } := by
  induction symbols generalizing rightSide with
  | nil =>
      have hStep := multiply_seek_marker_step leftDistance base next dead
        specPrefix suffix
        (leftPathTape rightSide (scratchEndSymbol :: outsideTail))
        hBase rfl
      have hExact := workRunExact_one_for
        (closedSpecMachine
          (specPrefix ++
            multiplyLoopSpecs leftDistance base next dead ++ suffix))
        { state := multiplySeekCopyEndState leftDistance base
          tape := leftPathTape rightSide
            (scratchEndSymbol :: outsideTail) }
        { state := multiplyRightCopyBase leftDistance base
          tape := leftPathTape rightSide
            (scratchEndSymbol :: outsideTail) }
        (by simpa [leftPathTape] using hStep)
      simpa [leftPathTape] using hExact
  | cons first rest ih =>
      have hFirstScratch := hScratch first (List.Mem.head rest)
      have hRestScratch : ∀ symbol ∈ rest, ScratchSymbol symbol := by
        intro symbol hMem
        exact hScratch symbol (List.Mem.tail first hMem)
      have hStep := multiply_seek_scratch_step leftDistance base next dead
        specPrefix suffix
        (leftPathTape rightSide
          (first :: rest ++ scratchEndSymbol :: outsideTail))
        hBase hFirstScratch
      have hFirst := workRunExact_one_for
        (closedSpecMachine
          (specPrefix ++
            multiplyLoopSpecs leftDistance base next dead ++ suffix))
        { state := multiplySeekCopyEndState leftDistance base
          tape := leftPathTape rightSide
            (first :: rest ++ scratchEndSymbol :: outsideTail) }
        { state := multiplySeekCopyEndState leftDistance base
          tape := leftPathTape (first :: rightSide)
            (rest ++ scratchEndSymbol :: outsideTail) }
        (by simpa using hStep)
      have hRest := ih (first :: rightSide) hRestScratch
      have hAll := workRunExact_compose_for
        (closedSpecMachine
          (specPrefix ++
            multiplyLoopSpecs leftDistance base next dead ++ suffix))
        1 (rest.length + 1)
        { state := multiplySeekCopyEndState leftDistance base
          tape := leftPathTape rightSide
            (first :: rest ++ scratchEndSymbol :: outsideTail) }
        { state := multiplySeekCopyEndState leftDistance base
          tape := leftPathTape (first :: rightSide)
            (rest ++ scratchEndSymbol :: outsideTail) }
        { state := multiplyRightCopyBase leftDistance base
          tape :=
            { left := outsideTail
              head := scratchEndSymbol
              right := rest.reverse ++ first :: rightSide } }
        hFirst hRest
      have hSteps : 1 + (rest.length + 1) =
          (first :: rest).length + 1 := by simp; omega
      rw [← hSteps]
      simpa [List.reverse_cons, List.append_assoc] using hAll

private theorem multiply_restore_marks_exact
    (leftDistance base next dead count : Nat)
    (specPrefix suffix : List StateSpec)
    (leftRest rightSide : List WorkSymbol)
    (hBase : specPrefix.length = base) :
    workRunExact?
        (closedSpecMachine
          (specPrefix ++
            multiplyLoopSpecs leftDistance base next dead ++ suffix))
        count
        { state := multiplyRestoreState leftDistance base
          tape := leftPathTape rightSide
            (List.replicate count registerMarkSymbol ++ leftRest) } =
      some
        { state := multiplyRestoreState leftDistance base
          tape := leftPathTape
            (List.replicate count unitSymbol ++ rightSide) leftRest } := by
  induction count generalizing rightSide with
  | zero => rfl
  | succ count ih =>
      have hStep := multiply_restore_mark_step leftDistance base next dead
        specPrefix suffix
        (leftPathTape rightSide
          (registerMarkSymbol ::
            List.replicate count registerMarkSymbol ++ leftRest))
        hBase rfl
      have hFirst := workRunExact_one_for
        (closedSpecMachine
          (specPrefix ++
            multiplyLoopSpecs leftDistance base next dead ++ suffix))
        { state := multiplyRestoreState leftDistance base
          tape := leftPathTape rightSide
            (registerMarkSymbol ::
              List.replicate count registerMarkSymbol ++ leftRest) }
        { state := multiplyRestoreState leftDistance base
          tape := leftPathTape (unitSymbol :: rightSide)
            (List.replicate count registerMarkSymbol ++ leftRest) }
        (by simpa using hStep)
      have hRest := ih (unitSymbol :: rightSide)
      have hAll := workRunExact_compose_for
        (closedSpecMachine
          (specPrefix ++
            multiplyLoopSpecs leftDistance base next dead ++ suffix))
        1 count
        { state := multiplyRestoreState leftDistance base
          tape := leftPathTape rightSide
            (registerMarkSymbol ::
              List.replicate count registerMarkSymbol ++ leftRest) }
        { state := multiplyRestoreState leftDistance base
          tape := leftPathTape (unitSymbol :: rightSide)
            (List.replicate count registerMarkSymbol ++ leftRest) }
        { state := multiplyRestoreState leftDistance base
          tape := leftPathTape
            (List.replicate count unitSymbol ++ unitSymbol :: rightSide)
            leftRest }
        hFirst hRest
      rw [replicate_unit_cons_comm count rightSide] at hAll
      simpa [List.replicate_succ, List.append_assoc,
        Nat.add_comm] using hAll

private theorem multiply_done_exact
    (leftDistance base next dead : Nat)
    (specPrefix suffix : List StateSpec)
    (symbols outsideTail rightSide : List WorkSymbol)
    (hBase : specPrefix.length = base)
    (hScratch : ∀ symbol ∈ symbols, ScratchSymbol symbol) :
    workRunExact?
        (closedSpecMachine
          (specPrefix ++
            multiplyLoopSpecs leftDistance base next dead ++ suffix))
        (symbols.length + 1)
        { state := multiplySeekEndDoneState leftDistance base
          tape := leftPathTape rightSide
            (symbols ++ scratchEndSymbol :: outsideTail) } =
      some
        { state := next
          tape :=
            { left := outsideTail
              head := scratchEndSymbol
              right := symbols.reverse ++ rightSide } } := by
  induction symbols generalizing rightSide with
  | nil =>
      have hStep := multiply_done_marker_step leftDistance base next dead
        specPrefix suffix
        (leftPathTape rightSide (scratchEndSymbol :: outsideTail))
        hBase rfl
      have hExact := workRunExact_one_for
        (closedSpecMachine
          (specPrefix ++
            multiplyLoopSpecs leftDistance base next dead ++ suffix))
        { state := multiplySeekEndDoneState leftDistance base
          tape := leftPathTape rightSide
            (scratchEndSymbol :: outsideTail) }
        { state := next
          tape := leftPathTape rightSide
            (scratchEndSymbol :: outsideTail) }
        (by simpa [leftPathTape] using hStep)
      simpa [leftPathTape] using hExact
  | cons first rest ih =>
      have hFirstScratch := hScratch first (List.Mem.head rest)
      have hRestScratch : ∀ symbol ∈ rest, ScratchSymbol symbol := by
        intro symbol hMem
        exact hScratch symbol (List.Mem.tail first hMem)
      have hStep := multiply_done_scratch_step leftDistance base next dead
        specPrefix suffix
        (leftPathTape rightSide
          (first :: rest ++ scratchEndSymbol :: outsideTail))
        hBase hFirstScratch
      have hFirst := workRunExact_one_for
        (closedSpecMachine
          (specPrefix ++
            multiplyLoopSpecs leftDistance base next dead ++ suffix))
        { state := multiplySeekEndDoneState leftDistance base
          tape := leftPathTape rightSide
            (first :: rest ++ scratchEndSymbol :: outsideTail) }
        { state := multiplySeekEndDoneState leftDistance base
          tape := leftPathTape (first :: rightSide)
            (rest ++ scratchEndSymbol :: outsideTail) }
        (by simpa using hStep)
      have hRest := ih (first :: rightSide) hRestScratch
      have hAll := workRunExact_compose_for
        (closedSpecMachine
          (specPrefix ++
            multiplyLoopSpecs leftDistance base next dead ++ suffix))
        1 (rest.length + 1)
        { state := multiplySeekEndDoneState leftDistance base
          tape := leftPathTape rightSide
            (first :: rest ++ scratchEndSymbol :: outsideTail) }
        { state := multiplySeekEndDoneState leftDistance base
          tape := leftPathTape (first :: rightSide)
            (rest ++ scratchEndSymbol :: outsideTail) }
        { state := next
          tape :=
            { left := outsideTail
              head := scratchEndSymbol
              right := rest.reverse ++ first :: rightSide } }
        hFirst hRest
      have hSteps : 1 + (rest.length + 1) =
          (first :: rest).length + 1 := by simp; omega
      rw [← hSteps]
      simpa [List.reverse_cons, List.append_assoc] using hAll

private def multiplyNewerValues
    (rightPrefix : List Nat) (rightValue processed : Nat) : List Nat :=
  rightPrefix ++ [rightValue, processed * rightValue]

private def multiplyLoopWord
    (older : List WorkSymbol) (remaining processed : Nat)
    (rightPrefix : List Nat) (rightValue : Nat) : List WorkSymbol :=
  older ++ separatorSymbol ::
    (List.replicate remaining unitSymbol ++
      List.replicate processed registerMarkSymbol ++
        registerWord
          (multiplyNewerValues rightPrefix rightValue processed))

private def multiplyMarkedWord
    (older : List WorkSymbol) (remaining processed : Nat)
    (rightPrefix : List Nat) (rightValue : Nat) : List WorkSymbol :=
  older ++ separatorSymbol ::
    (List.replicate remaining unitSymbol ++
      List.replicate (processed + 1) registerMarkSymbol ++
        registerWord
          (multiplyNewerValues rightPrefix rightValue processed))

private def multiplyFinishedWord
    (older : List WorkSymbol) (leftValue : Nat)
    (rightPrefix : List Nat) (rightValue : Nat) : List WorkSymbol :=
  older ++ separatorSymbol ::
    (List.replicate leftValue unitSymbol ++
      registerWord
        (multiplyNewerValues rightPrefix rightValue leftValue))

private def multiplyIterationSteps
    (rightPrefix : List Nat) (rightValue processed : Nat) : Nat :=
  let newerWord := registerWord
    (multiplyNewerValues rightPrefix rightValue processed)
  2 * newerWord.length + 2 * processed + 3 +
    copySteps [] (processed * rightValue) rightValue

private def multiplyFinishSteps
    (rightPrefix : List Nat) (rightValue processed : Nat) : Nat :=
  2 * (registerWord
      (multiplyNewerValues rightPrefix rightValue processed)).length +
    2 * processed + 3

private theorem multiplyNewerValues_ne_nil
    (rightPrefix : List Nat) (rightValue processed : Nat) :
    multiplyNewerValues rightPrefix rightValue processed ≠ [] := by
  simp [multiplyNewerValues]

private theorem multiplyNewerValues_length
    (rightPrefix : List Nat) (rightValue processed : Nat) :
    (multiplyNewerValues rightPrefix rightValue processed).length =
      rightPrefix.length + 2 := by
  simp [multiplyNewerValues]

private theorem multiply_iteration_exact
    (base next dead : Nat) (specPrefix suffix : List StateSpec)
    (older inside outsideTail : List WorkSymbol)
    (remaining processed rightValue : Nat) (rightPrefix : List Nat)
    (hBase : specPrefix.length = base) :
    workRunExact?
        (closedSpecMachine
          (specPrefix ++
            multiplyLoopSpecs (rightPrefix.length + 2)
              base next dead ++ suffix))
        (multiplyIterationSteps rightPrefix rightValue processed)
        (endConfiguration base outsideTail
          (multiplyLoopWord older (remaining + 1) processed
            rightPrefix rightValue) inside) =
      some
        (endConfiguration base (outsideTail.drop rightValue)
          (multiplyLoopWord older remaining (processed + 1)
            rightPrefix rightValue) inside) := by
  let leftDistance := rightPrefix.length + 2
  let newer := multiplyNewerValues rightPrefix rightValue processed
  let traversal := locateTraversalWord newer.reverse
  let newerWord := registerWord newer
  let innerBase := multiplyRightCopyBase leftDistance base
  let restoreTail : List StateSpec :=
    [multiplyRestoreSpec leftDistance base dead,
     multiplySeekEndDoneSpec leftDistance base next dead]
  let loopTail : List StateSpec :=
    [multiplyScanSpec leftDistance base dead,
     multiplySeekCopyEndSpec leftDistance base dead] ++
    copySpecs 1 innerBase base dead ++ restoreTail
  let machineSpecs := specPrefix ++
    multiplyLoopSpecs leftDistance base next dead ++ suffix
  let rightAfterSource := separatorSymbol :: older.reverse ++ inside
  let c0 := endConfiguration base outsideTail
    (multiplyLoopWord older (remaining + 1) processed
      rightPrefix rightValue) inside
  let c1 : WorkConfiguration :=
    { state := multiplyLocateBase base
      tape := pathTape (scratchEndSymbol :: outsideTail)
        (traversal ++ List.replicate processed registerMarkSymbol ++
          unitSymbol :: List.replicate remaining unitSymbol ++
            rightAfterSource) }
  let locateLeft := traversal.reverse ++ scratchEndSymbol :: outsideTail
  let c2 : WorkConfiguration :=
    { state := multiplyScanState leftDistance base
      tape := pathTape locateLeft
        (List.replicate processed registerMarkSymbol ++
          unitSymbol :: List.replicate remaining unitSymbol ++
            rightAfterSource) }
  let markedLeft :=
    List.replicate processed registerMarkSymbol ++ locateLeft
  let c3 : WorkConfiguration :=
    { state := multiplyScanState leftDistance base
      tape := pathTape markedLeft
        (unitSymbol :: List.replicate remaining unitSymbol ++
          rightAfterSource) }
  let c4 : WorkConfiguration :=
    { state := multiplySeekCopyEndState leftDistance base
      tape := leftPathTape
        (registerMarkSymbol ::
          List.replicate remaining unitSymbol ++ rightAfterSource)
        markedLeft }
  let markedWord := multiplyMarkedWord older remaining processed
    rightPrefix rightValue
  let c5 := endConfiguration innerBase outsideTail markedWord inside
  let c6 := endConfiguration base (outsideTail.drop rightValue)
    (multiplyLoopWord older remaining (processed + 1)
      rightPrefix rightValue) inside
  have hStartStep := multiply_start_step leftDistance base next dead
    specPrefix suffix
    (endTape outsideTail
      (multiplyLoopWord older (remaining + 1) processed
        rightPrefix rightValue) inside) hBase rfl
  have hStart : workRunExact? (closedSpecMachine machineSpecs) 1 c0 =
      some c1 := by
    apply workRunExact_one_for
    simpa [machineSpecs, c0, c1, multiplyLoopWord, newer, traversal,
      rightAfterSource, endConfiguration,
      registerWord_reverse_eq_locateTraversalWord,
      List.reverse_append, List.reverse_cons, List.reverse_replicate,
      List.replicate_succ, replicate_unit_cons_comm,
      List.append_assoc] using hStartStep
  have hLocatePrefix :
      (specPrefix ++ [multiplyStartSpec base dead]).length =
        multiplyLocateBase base := by
    simp [multiplyLocateBase, hBase]
  have hLocate := locate_traversal_exact newer.reverse
    (multiplyLocateBase base)
    (multiplyScanState leftDistance base) dead
    (specPrefix ++ [multiplyStartSpec base dead]) (loopTail ++ suffix)
    (scratchEndSymbol :: outsideTail)
    (List.replicate processed registerMarkSymbol ++
      unitSymbol :: List.replicate remaining unitSymbol ++ rightAfterSource)
    (by simpa [newer] using
      (multiplyNewerValues_ne_nil rightPrefix rightValue processed))
    hLocatePrefix
  have hLocateMachine :
      specPrefix ++ [multiplyStartSpec base dead] ++
          locateSpecs newer.reverse.length (multiplyLocateBase base)
            (multiplyScanState leftDistance base) dead ++
              (loopTail ++ suffix) = machineSpecs := by
    simp [machineSpecs, multiplyLoopSpecs, loopTail, restoreTail,
      innerBase, newer, leftDistance, multiplyNewerValues_length,
      List.append_assoc]
  rw [hLocateMachine] at hLocate
  have hLocateExact :
      workRunExact? (closedSpecMachine machineSpecs)
        (newer.length + newer.sum) c1 = some c2 := by
    simpa [c1, c2, newer, traversal, locateLeft, Nat.add_comm]
      using hLocate
  have hScan := multiply_scan_marks_exact leftDistance base next dead
    processed specPrefix suffix locateLeft
    (unitSymbol :: List.replicate remaining unitSymbol ++ rightAfterSource)
    hBase
  have hScanExact :
      workRunExact? (closedSpecMachine machineSpecs) processed c2 =
        some c3 := by
    simpa [machineSpecs, c2, c3, markedLeft, List.append_assoc]
      using hScan
  have hMarkStep := multiply_scan_unit_step leftDistance base next dead
    specPrefix suffix
    (pathTape markedLeft
      (unitSymbol :: List.replicate remaining unitSymbol ++
        rightAfterSource)) hBase rfl
  have hMarkedLeft : markedLeft ≠ [] := by
    simp [markedLeft, locateLeft]
  have hMarkTape := pathTape_write_moveLeft_of_ne_nil markedLeft
    unitSymbol registerMarkSymbol
    (List.replicate remaining unitSymbol ++ rightAfterSource) hMarkedLeft
  have hMark :
      workRunExact? (closedSpecMachine machineSpecs) 1 c3 = some c4 := by
    apply workRunExact_one_for
    simp only [List.cons_append] at hMarkStep
    rw [hMarkTape] at hMarkStep
    simpa [machineSpecs, c3, c4] using hMarkStep
  have hMarkedScratch :
      ∀ symbol ∈ List.replicate processed registerMarkSymbol ++ newerWord,
        ScratchSymbol symbol := by
    apply scratch_append
    · intro symbol hMem
      exact Or.inr (Or.inr (List.eq_of_mem_replicate hMem))
    · exact registerWord_scratch _
  have hSeek := multiply_seek_exact leftDistance base next dead
    specPrefix suffix
    (List.replicate processed registerMarkSymbol ++ newerWord)
    outsideTail
    (registerMarkSymbol ::
      List.replicate remaining unitSymbol ++ rightAfterSource)
    hBase hMarkedScratch
  have hSeekExact :
      workRunExact? (closedSpecMachine machineSpecs)
        ((List.replicate processed registerMarkSymbol ++
          newerWord).length + 1) c4 = some c5 := by
    have hTraversalReverse : traversal.reverse = newerWord := by
      simp [traversal, newerWord, newer,
        ← registerWord_reverse_eq_locateTraversalWord]
    simpa [machineSpecs, c4, c5, endConfiguration, endTape,
      markedLeft, locateLeft, traversal, newerWord, newer, markedWord,
      multiplyMarkedWord, rightAfterSource, hTraversalReverse,
      registerWord_reverse_eq_locateTraversalWord,
      List.reverse_append, List.reverse_cons, List.reverse_replicate,
      List.replicate_succ, replicate_cons_comm, List.append_assoc,
      Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hSeek
  let innerPrefix :=
    specPrefix ++ [multiplyStartSpec base dead] ++
      locateSpecs leftDistance (multiplyLocateBase base)
        (multiplyScanState leftDistance base) dead ++
      [multiplyScanSpec leftDistance base dead,
       multiplySeekCopyEndSpec leftDistance base dead]
  have hInnerPrefix : innerPrefix.length = innerBase := by
    simp [innerPrefix, innerBase, multiplyRightCopyBase,
      multiplyScanState, multiplyLocateBase, hBase]
    omega
  have hInner := copy_exact innerBase base dead innerPrefix
    (restoreTail ++ suffix)
    (older ++ separatorSymbol ::
      (List.replicate remaining unitSymbol ++
        List.replicate (processed + 1) registerMarkSymbol ++
          registerWord rightPrefix))
    inside outsideTail rightValue (processed * rightValue) [] hInnerPrefix
  have hInnerMachine :
      innerPrefix ++ copySpecs 1 innerBase base dead ++
          (restoreTail ++ suffix) = machineSpecs := by
    simp [innerPrefix, machineSpecs, multiplyLoopSpecs, restoreTail,
      innerBase, List.append_assoc]
  simp only [List.length_nil, Nat.zero_add] at hInner
  rw [hInnerMachine] at hInner
  have hInnerExact :
      workRunExact? (closedSpecMachine machineSpecs)
        (copySteps [] (processed * rightValue) rightValue) c5 =
      some c6 := by
    simpa [c5, c6, markedWord, multiplyMarkedWord,
      multiplyLoopWord, multiplyNewerValues, registerWord,
      List.append_assoc, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm,
      Nat.succ_mul] using hInner
  have h01 := workRunExact_compose_for (closedSpecMachine machineSpecs)
    1 (newer.length + newer.sum) c0 c1 c2 hStart hLocateExact
  have h03 := workRunExact_compose_for (closedSpecMachine machineSpecs)
    (1 + (newer.length + newer.sum)) processed c0 c2 c3 h01 hScanExact
  have h04 := workRunExact_compose_for (closedSpecMachine machineSpecs)
    (1 + (newer.length + newer.sum) + processed) 1 c0 c3 c4
    h03 hMark
  have h05 := workRunExact_compose_for (closedSpecMachine machineSpecs)
    (1 + (newer.length + newer.sum) + processed + 1)
    ((List.replicate processed registerMarkSymbol ++ newerWord).length + 1)
    c0 c4 c5 h04 hSeekExact
  have h06 := workRunExact_compose_for (closedSpecMachine machineSpecs)
    (1 + (newer.length + newer.sum) + processed + 1 +
      ((List.replicate processed registerMarkSymbol ++
        newerWord).length + 1))
    (copySteps [] (processed * rightValue) rightValue)
    c0 c5 c6 h05 hInnerExact
  have hSteps :
      1 + (newer.length + newer.sum) + processed + 1 +
          ((List.replicate processed registerMarkSymbol ++
            newerWord).length + 1) +
          copySteps [] (processed * rightValue) rightValue =
        multiplyIterationSteps rightPrefix rightValue processed := by
    simp [multiplyIterationSteps, newer, newerWord,
      multiplyNewerValues, registerWord_length]
    omega
  rw [hSteps] at h06
  simpa [machineSpecs, c0, c6, leftDistance] using h06

private theorem multiply_finish_exact
    (base next dead : Nat) (specPrefix suffix : List StateSpec)
    (older inside outsideTail : List WorkSymbol)
    (processed rightValue : Nat) (rightPrefix : List Nat)
    (hBase : specPrefix.length = base) :
    workRunExact?
        (closedSpecMachine
          (specPrefix ++
            multiplyLoopSpecs (rightPrefix.length + 2)
              base next dead ++ suffix))
        (multiplyFinishSteps rightPrefix rightValue processed)
        (endConfiguration base outsideTail
          (multiplyLoopWord older 0 processed rightPrefix rightValue)
          inside) =
      some
        (endConfiguration next outsideTail
          (multiplyFinishedWord older processed rightPrefix rightValue)
          inside) := by
  let leftDistance := rightPrefix.length + 2
  let newer := multiplyNewerValues rightPrefix rightValue processed
  let traversal := locateTraversalWord newer.reverse
  let newerWord := registerWord newer
  let innerBase := multiplyRightCopyBase leftDistance base
  let restoreTail : List StateSpec :=
    [multiplyRestoreSpec leftDistance base dead,
     multiplySeekEndDoneSpec leftDistance base next dead]
  let loopTail : List StateSpec :=
    [multiplyScanSpec leftDistance base dead,
     multiplySeekCopyEndSpec leftDistance base dead] ++
    copySpecs 1 innerBase base dead ++ restoreTail
  let machineSpecs := specPrefix ++
    multiplyLoopSpecs leftDistance base next dead ++ suffix
  let rightAfterSource := separatorSymbol :: older.reverse ++ inside
  let c0 := endConfiguration base outsideTail
    (multiplyLoopWord older 0 processed rightPrefix rightValue) inside
  let c1 : WorkConfiguration :=
    { state := multiplyLocateBase base
      tape := pathTape (scratchEndSymbol :: outsideTail)
        (traversal ++ List.replicate processed registerMarkSymbol ++
          rightAfterSource) }
  let locateLeft := traversal.reverse ++ scratchEndSymbol :: outsideTail
  let c2 : WorkConfiguration :=
    { state := multiplyScanState leftDistance base
      tape := pathTape locateLeft
        (List.replicate processed registerMarkSymbol ++
          rightAfterSource) }
  let markedLeft :=
    List.replicate processed registerMarkSymbol ++ locateLeft
  let c3 : WorkConfiguration :=
    { state := multiplyScanState leftDistance base
      tape := pathTape markedLeft rightAfterSource }
  let c4 : WorkConfiguration :=
    { state := multiplyRestoreState leftDistance base
      tape := leftPathTape rightAfterSource markedLeft }
  obtain ⟨newerTail, hNewerWord⟩ :
      ∃ tail, newerWord = separatorSymbol :: tail := by
    have hNewer : newer ≠ [] := by
      simpa [newer] using
        (multiplyNewerValues_ne_nil rightPrefix rightValue processed)
    cases h : newer with
    | nil => contradiction
    | cons value rest =>
        refine ⟨List.replicate value unitSymbol ++ registerWord rest, ?_⟩
        simp [newerWord, h, registerWord]
  have hNewerWord' :
      registerWord newer = separatorSymbol :: newerTail := by
    simpa [newerWord] using hNewerWord
  let restoredRight :=
    List.replicate processed unitSymbol ++ rightAfterSource
  let c5 : WorkConfiguration :=
    { state := multiplyRestoreState leftDistance base
      tape := leftPathTape restoredRight
        (newerWord ++ scratchEndSymbol :: outsideTail) }
  let c6 : WorkConfiguration :=
    { state := multiplySeekEndDoneState leftDistance base
      tape := leftPathTape (separatorSymbol :: restoredRight)
        (newerTail ++ scratchEndSymbol :: outsideTail) }
  let c7 := endConfiguration next outsideTail
    (multiplyFinishedWord older processed rightPrefix rightValue) inside
  have hStartStep := multiply_start_step leftDistance base next dead
    specPrefix suffix
    (endTape outsideTail
      (multiplyLoopWord older 0 processed rightPrefix rightValue) inside)
    hBase rfl
  have hStart : workRunExact? (closedSpecMachine machineSpecs) 1 c0 =
      some c1 := by
    apply workRunExact_one_for
    simpa [machineSpecs, c0, c1, multiplyLoopWord, newer, traversal,
      rightAfterSource, endConfiguration,
      registerWord_reverse_eq_locateTraversalWord,
      List.reverse_append, List.reverse_cons, List.reverse_replicate,
      List.append_assoc] using hStartStep
  have hLocatePrefix :
      (specPrefix ++ [multiplyStartSpec base dead]).length =
        multiplyLocateBase base := by
    simp [multiplyLocateBase, hBase]
  have hLocate := locate_traversal_exact newer.reverse
    (multiplyLocateBase base)
    (multiplyScanState leftDistance base) dead
    (specPrefix ++ [multiplyStartSpec base dead]) (loopTail ++ suffix)
    (scratchEndSymbol :: outsideTail)
    (List.replicate processed registerMarkSymbol ++ rightAfterSource)
    (by simpa [newer] using
      (multiplyNewerValues_ne_nil rightPrefix rightValue processed))
    hLocatePrefix
  have hLocateMachine :
      specPrefix ++ [multiplyStartSpec base dead] ++
          locateSpecs newer.reverse.length (multiplyLocateBase base)
            (multiplyScanState leftDistance base) dead ++
              (loopTail ++ suffix) = machineSpecs := by
    simp [machineSpecs, multiplyLoopSpecs, loopTail, restoreTail,
      innerBase, newer, leftDistance, multiplyNewerValues_length,
      List.append_assoc]
  rw [hLocateMachine] at hLocate
  have hLocateExact :
      workRunExact? (closedSpecMachine machineSpecs)
        (newer.length + newer.sum) c1 = some c2 := by
    simpa [c1, c2, newer, traversal, locateLeft, Nat.add_comm]
      using hLocate
  have hScan := multiply_scan_marks_exact leftDistance base next dead
    processed specPrefix suffix locateLeft rightAfterSource hBase
  have hScanExact :
      workRunExact? (closedSpecMachine machineSpecs) processed c2 =
        some c3 := by
    simpa [machineSpecs, c2, c3, markedLeft, List.append_assoc]
      using hScan
  have hFinishStep := multiply_scan_finish_step leftDistance base next dead
    specPrefix suffix (pathTape markedLeft rightAfterSource) hBase rfl
  have hMarkedLeft : markedLeft ≠ [] := by
    simp [markedLeft, locateLeft]
  have hFinishTape :
      (pathTape markedLeft rightAfterSource).moveLeft =
        leftPathTape rightAfterSource markedLeft := by
    cases hMarked : markedLeft with
    | nil => exact False.elim (hMarkedLeft hMarked)
    | cons first rest => rfl
  have hFinish :
      workRunExact? (closedSpecMachine machineSpecs) 1 c3 = some c4 := by
    apply workRunExact_one_for
    rw [hFinishTape] at hFinishStep
    simpa [machineSpecs, c3, c4] using hFinishStep
  have hRestore := multiply_restore_marks_exact leftDistance base next dead
    processed specPrefix suffix
    (newerWord ++ scratchEndSymbol :: outsideTail) rightAfterSource hBase
  have hRestoreExact :
      workRunExact? (closedSpecMachine machineSpecs) processed c4 =
        some c5 := by
    have hTraversalReverse : traversal.reverse = newerWord := by
      simp [traversal, newerWord, newer,
        ← registerWord_reverse_eq_locateTraversalWord]
    simpa [machineSpecs, c4, c5, markedLeft, locateLeft, traversal,
      newerWord, newer, restoredRight, hTraversalReverse,
      List.append_assoc] using hRestore
  have hBoundaryStep := multiply_restore_separator_step
    leftDistance base next dead specPrefix suffix
    (leftPathTape restoredRight
      (separatorSymbol :: newerTail ++ scratchEndSymbol :: outsideTail))
    hBase rfl
  have hBoundary :
      workRunExact? (closedSpecMachine machineSpecs) 1 c5 = some c6 := by
    apply workRunExact_one_for
    dsimp [c5]
    rw [hNewerWord]
    simpa [machineSpecs, c6, List.cons_append] using hBoundaryStep
  have hNewerTailScratch :
      ∀ symbol ∈ newerTail, ScratchSymbol symbol := by
    intro symbol hMem
    apply registerWord_scratch newer symbol
    rw [hNewerWord']
    exact List.Mem.tail separatorSymbol hMem
  have hDone := multiply_done_exact leftDistance base next dead
    specPrefix suffix newerTail outsideTail
    (separatorSymbol :: restoredRight) hBase hNewerTailScratch
  have hDoneExact :
      workRunExact? (closedSpecMachine machineSpecs)
        (newerTail.length + 1) c6 = some c7 := by
    simpa [machineSpecs, c6, c7, restoredRight, rightAfterSource,
      multiplyFinishedWord, endConfiguration, endTape, newerWord, newer,
      hNewerWord, registerWord_reverse_eq_locateTraversalWord,
      List.reverse_append, List.reverse_cons, List.reverse_replicate,
      List.append_assoc, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
      using hDone
  have h01 := workRunExact_compose_for (closedSpecMachine machineSpecs)
    1 (newer.length + newer.sum) c0 c1 c2 hStart hLocateExact
  have h03 := workRunExact_compose_for (closedSpecMachine machineSpecs)
    (1 + (newer.length + newer.sum)) processed c0 c2 c3 h01 hScanExact
  have h04 := workRunExact_compose_for (closedSpecMachine machineSpecs)
    (1 + (newer.length + newer.sum) + processed) 1 c0 c3 c4
    h03 hFinish
  have h05 := workRunExact_compose_for (closedSpecMachine machineSpecs)
    (1 + (newer.length + newer.sum) + processed + 1) processed
    c0 c4 c5 h04 hRestoreExact
  have h06 := workRunExact_compose_for (closedSpecMachine machineSpecs)
    (1 + (newer.length + newer.sum) + processed + 1 + processed) 1
    c0 c5 c6 h05 hBoundary
  have h07 := workRunExact_compose_for (closedSpecMachine machineSpecs)
    (1 + (newer.length + newer.sum) + processed + 1 + processed + 1)
    (newerTail.length + 1) c0 c6 c7 h06 hDoneExact
  have hNewerLength : newerTail.length + 1 = newerWord.length := by
    rw [hNewerWord]
    simp
  have hSteps :
      1 + (newer.length + newer.sum) + processed + 1 + processed + 1 +
          (newerTail.length + 1) =
        multiplyFinishSteps rightPrefix rightValue processed := by
    rw [hNewerLength]
    simp [multiplyFinishSteps, newer, newerWord, multiplyNewerValues,
      registerWord_length]
    omega
  rw [hSteps] at h07
  simpa [machineSpecs, c0, c7, leftDistance] using h07

private def multiplyLoopSteps
    (rightPrefix : List Nat) (rightValue : Nat) : Nat → Nat → Nat
  | processed, 0 =>
      multiplyFinishSteps rightPrefix rightValue processed
  | processed, remaining + 1 =>
      multiplyIterationSteps rightPrefix rightValue processed +
        multiplyLoopSteps rightPrefix rightValue (processed + 1) remaining

private def multiplySteps
    (rightPrefix : List Nat) (leftValue rightValue : Nat) : Nat :=
  multiplyLoopSteps rightPrefix rightValue 0 leftValue

private theorem multiply_loop_exact
    (base next dead : Nat) (specPrefix suffix : List StateSpec)
    (older inside outsideTail : List WorkSymbol)
    (remaining processed rightValue : Nat) (rightPrefix : List Nat)
    (hBase : specPrefix.length = base) :
    workRunExact?
        (closedSpecMachine
          (specPrefix ++
            multiplyLoopSpecs (rightPrefix.length + 2)
              base next dead ++ suffix))
        (multiplyLoopSteps rightPrefix rightValue processed remaining)
        (endConfiguration base outsideTail
          (multiplyLoopWord older remaining processed rightPrefix rightValue)
          inside) =
      some
        (endConfiguration next
          (outsideTail.drop (remaining * rightValue))
          (multiplyFinishedWord older (processed + remaining)
            rightPrefix rightValue) inside) := by
  induction remaining generalizing processed outsideTail with
  | zero =>
      simpa [multiplyLoopSteps, multiplyFinishedWord] using
        (multiply_finish_exact base next dead specPrefix suffix older inside
          outsideTail processed rightValue rightPrefix hBase)
  | succ remaining ih =>
      have hIteration := multiply_iteration_exact base next dead
        specPrefix suffix older inside outsideTail remaining processed
        rightValue rightPrefix hBase
      have hRest := ih (outsideTail.drop rightValue) (processed + 1)
      have hAll := workRunExact_compose_for
        (closedSpecMachine
          (specPrefix ++
            multiplyLoopSpecs (rightPrefix.length + 2)
              base next dead ++ suffix))
        (multiplyIterationSteps rightPrefix rightValue processed)
        (multiplyLoopSteps rightPrefix rightValue (processed + 1) remaining)
        (endConfiguration base outsideTail
          (multiplyLoopWord older (remaining + 1) processed
            rightPrefix rightValue) inside)
        (endConfiguration base (outsideTail.drop rightValue)
          (multiplyLoopWord older remaining (processed + 1)
            rightPrefix rightValue) inside)
        (endConfiguration next
          ((outsideTail.drop rightValue).drop (remaining * rightValue))
          (multiplyFinishedWord older (processed + 1 + remaining)
            rightPrefix rightValue) inside)
        hIteration hRest
      simpa [multiplyLoopSteps, List.drop_drop, Nat.succ_mul,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hAll

private theorem multiply_exact
    (base next dead : Nat) (specPrefix suffix : List StateSpec)
    (older inside outsideTail : List WorkSymbol)
    (leftValue rightValue : Nat) (rightPrefix : List Nat)
    (hBase : specPrefix.length = base) :
    workRunExact?
        (closedSpecMachine
          (specPrefix ++
            multiplyLoopSpecs (rightPrefix.length + 2)
              base next dead ++ suffix))
        (multiplySteps rightPrefix leftValue rightValue)
        (endConfiguration base outsideTail
          (older ++ registerWord
            ([leftValue] ++ rightPrefix ++ [rightValue, 0])) inside) =
      some
        (endConfiguration next
          (outsideTail.drop (leftValue * rightValue))
          (older ++ registerWord
            ([leftValue] ++ rightPrefix ++
              [rightValue, leftValue * rightValue])) inside) := by
  have hLoop := multiply_loop_exact base next dead specPrefix suffix older
    inside outsideTail leftValue 0 rightValue rightPrefix hBase
  simpa [multiplySteps, multiplyLoopWord, multiplyFinishedWord,
    multiplyNewerValues, registerWord, List.append_assoc,
    Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hLoop

private def mulOperationSteps
    (rightPrefix : List Nat) (leftValue rightValue : Nat) : Nat :=
  2 + multiplySteps rightPrefix leftValue rightValue

private theorem mulOperation_exact
    (rightNodes base next dead : Nat)
    (specPrefix suffix : List StateSpec)
    (existing leftPrefix rightPrefix : List Nat)
    (leftValue rightValue : Nat)
    (inside outsideTail : List WorkSymbol)
    (hBase : specPrefix.length = base)
    (hRightNodes : (rightPrefix ++ [rightValue]).length = rightNodes) :
    workRunExact?
        (closedSpecMachine
          (specPrefix ++
            mulOperationSpecs rightNodes base next dead ++ suffix))
        (mulOperationSteps rightPrefix leftValue rightValue)
        (endConfiguration base outsideTail
          (registerWord
            (existing ++ leftPrefix ++ [leftValue] ++
              rightPrefix ++ [rightValue])) inside) =
      some
        (endConfiguration next
          (outsideTail.drop (leftValue * rightValue + 1))
          (registerWord
            (existing ++ leftPrefix ++ [leftValue] ++
              rightPrefix ++ [rightValue, leftValue * rightValue]))
          inside) := by
  let loopBase := base + 2
  let startWord := registerWord
    (existing ++ leftPrefix ++ [leftValue] ++ rightPrefix ++ [rightValue])
  let afterSeparatorWord := startWord ++ [separatorSymbol]
  let finalWord := registerWord
    (existing ++ leftPrefix ++ [leftValue] ++
      rightPrefix ++ [rightValue, leftValue * rightValue])
  let machineSpecs :=
    specPrefix ++ mulOperationSpecs rightNodes base next dead ++ suffix
  have hSeparator := separator_exact base loopBase dead specPrefix
    (multiplyLoopSpecs (rightNodes + 1) loopBase next dead ++ suffix)
    outsideTail startWord inside hBase
  have hLoopPrefix :
      (specPrefix ++ separatorSpecs base loopBase dead).length =
        loopBase := by
    simp [loopBase, hBase]
  have hLoop := multiply_exact loopBase next dead
    (specPrefix ++ separatorSpecs base loopBase dead) suffix
    (registerWord (existing ++ leftPrefix)) inside
    (outsideTail.drop 1) leftValue rightValue rightPrefix hLoopPrefix
  have hDistance : rightPrefix.length + 2 = rightNodes + 1 := by
    simp at hRightNodes
    omega
  rw [hDistance] at hLoop
  have hMachine :
      specPrefix ++ separatorSpecs base loopBase dead ++
          multiplyLoopSpecs (rightNodes + 1) loopBase next dead ++ suffix =
        machineSpecs := by
    simp [machineSpecs, mulOperationSpecs, loopBase, List.append_assoc]
  simp only [List.append_assoc] at hSeparator hLoop hMachine
  rw [hMachine] at hSeparator hLoop
  have hSeparatorExact :
      workRunExact? (closedSpecMachine machineSpecs) 2
        (endConfiguration base outsideTail startWord inside) =
      some
        (endConfiguration loopBase (outsideTail.drop 1)
          afterSeparatorWord inside) := by
    simpa [startWord, afterSeparatorWord] using hSeparator
  have hLoopExact :
      workRunExact? (closedSpecMachine machineSpecs)
          (multiplySteps rightPrefix leftValue rightValue)
          (endConfiguration loopBase (outsideTail.drop 1)
            afterSeparatorWord inside) =
        some
          (endConfiguration next
            ((outsideTail.drop 1).drop (leftValue * rightValue))
            finalWord inside) := by
    simpa [afterSeparatorWord, startWord, finalWord, registerWord,
      List.append_assoc, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
      using hLoop
  have hAll := workRunExact_compose_for (closedSpecMachine machineSpecs)
    2 (multiplySteps rightPrefix leftValue rightValue)
    (endConfiguration base outsideTail startWord inside)
    (endConfiguration loopBase (outsideTail.drop 1)
      afterSeparatorWord inside)
    (endConfiguration next
      ((outsideTail.drop 1).drop (leftValue * rightValue))
      finalWord inside) hSeparatorExact hLoopExact
  have hStartWord :
      startWord = registerWord
        (existing ++ leftPrefix ++ [leftValue] ++
          rightPrefix ++ [rightValue]) := rfl
  have hFinalWord :
      finalWord = registerWord
        (existing ++ leftPrefix ++ [leftValue] ++
          rightPrefix ++ [rightValue, leftValue * rightValue]) := rfl
  rw [← hStartWord, ← hFinalWord]
  simpa [machineSpecs, mulOperationSteps, List.drop_drop,
    Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hAll

/-! ### Structural compiler trace -/

private def rootPrefixValues : NatPolynomial → Nat → List Nat
  | .constant _, _ => []
  | .variable, _ => []
  | .add left right, input =>
      registerValues left input ++ registerValues right input
  | .mul left right, input =>
      registerValues left input ++ registerValues right input

private theorem registerValues_eq_rootPrefixValues
    (polynomial : NatPolynomial) (input : Nat) :
    registerValues polynomial input =
      rootPrefixValues polynomial input ++ [polynomial.eval input] := by
  cases polynomial <;> rfl

private def compilerSteps :
    NatPolynomial → Nat → List Nat → Nat
  | .constant value, _, _ => 2 + appendManyStateCount value
  | .variable, input, existing =>
      variableOperationSteps (registerWord existing).length input
  | .add left right, input, existing =>
      compilerSteps left input existing +
        compilerSteps right input
          (existing ++ registerValues left input) +
        addOperationSteps (registerValues right input)
          (left.eval input) (right.eval input)
  | .mul left right, input, existing =>
      compilerSteps left input existing +
        compilerSteps right input
          (existing ++ registerValues left input) +
        mulOperationSteps (rootPrefixValues right input)
          (left.eval input) (right.eval input)

private theorem compile_exact
    (polynomial : NatPolynomial) (base next dead : Nat)
    (specPrefix suffix : List StateSpec)
    (input : BitString) (workspace outsideTail : List WorkSymbol)
    (existing : List Nat)
    (hBase : specPrefix.length = base)
    (hNext : next = base + compilerStateCount polynomial) :
    workRunExact?
        (closedSpecMachine
          (specPrefix ++ compileSpecs polynomial base next dead ++ suffix))
        (compilerSteps polynomial input.length existing)
        (endConfiguration base outsideTail (registerWord existing)
          (sourceInside input workspace)) =
      some
        (endConfiguration next
          (outsideTail.drop
            (registerWord (registerValues polynomial input.length)).length)
          (registerWord
            (existing ++ registerValues polynomial input.length))
          (sourceInside input workspace)) := by
  induction polynomial generalizing base next specPrefix suffix existing outsideTail with
  | constant value =>
      have hConstant := constantOperation_exact value base next dead
        specPrefix suffix outsideTail (registerWord existing)
        (sourceInside input workspace) hBase (by
          simpa [compilerStateCount] using hNext)
      simpa [compileSpecs, compilerSteps, registerValues, registerWord,
        List.drop_drop, List.append_assoc, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm] using hConstant
  | «variable» =>
      have hVariable := variableOperation_exact base next dead
        specPrefix suffix input outsideTail (registerWord existing)
        workspace hBase (registerWord_scratch existing)
      simpa [compileSpecs, compilerSteps, registerValues, registerWord,
        List.drop_drop, List.append_assoc, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm] using hVariable
  | add left right leftIH rightIH =>
      let rightBase := base + compilerStateCount left
      let operationBase := rightBase + compilerStateCount right
      let rightSpecs := compileSpecs right rightBase operationBase dead
      let operationSpecs :=
        addOperationSpecs (nodeCount right) operationBase next dead
      let machineSpecs := specPrefix ++
        compileSpecs left base rightBase dead ++ rightSpecs ++
          operationSpecs ++ suffix
      have hLeftNext : rightBase = base + compilerStateCount left := rfl
      have hLeft := leftIH base rightBase specPrefix
        (rightSpecs ++ operationSpecs ++ suffix) outsideTail existing hBase
        hLeftNext
      have hRightPrefix :
          (specPrefix ++ compileSpecs left base rightBase dead).length =
            rightBase := by
        simp [rightBase, hBase]
      have hRightNext :
          operationBase = rightBase + compilerStateCount right := rfl
      have hRight := rightIH rightBase operationBase
        (specPrefix ++ compileSpecs left base rightBase dead)
        (operationSpecs ++ suffix)
        (outsideTail.drop
          (registerWord (registerValues left input.length)).length)
        (existing ++ registerValues left input.length)
        hRightPrefix hRightNext
      have hOperationPrefix :
          (specPrefix ++ compileSpecs left base rightBase dead ++
            rightSpecs).length = operationBase := by
        simp [rightSpecs, operationBase, rightBase, hBase]
        omega
      have hOperation := addOperation_exact (nodeCount right)
        operationBase next dead
        (specPrefix ++ compileSpecs left base rightBase dead ++ rightSpecs)
        suffix existing (rootPrefixValues left input.length)
        (rootPrefixValues right input.length)
        (left.eval input.length) (right.eval input.length)
        (sourceInside input workspace)
        ((outsideTail.drop
          (registerWord (registerValues left input.length)).length).drop
            (registerWord (registerValues right input.length)).length)
        hOperationPrefix (by
          have hLength := registerValues_length right input.length
          rw [registerValues_eq_rootPrefixValues] at hLength
          exact hLength)
      have hMachine :
          specPrefix ++ compileSpecs (.add left right) base next dead ++
              suffix = machineSpecs := by
        simp [compileSpecs, machineSpecs, rightSpecs, operationSpecs,
          rightBase, operationBase, List.append_assoc]
      have hLeftValues :=
        registerValues_eq_rootPrefixValues left input.length
      have hRightValues :=
        registerValues_eq_rootPrefixValues right input.length
      have hOperationStart :
          existing ++ rootPrefixValues left input.length ++
                [left.eval input.length] ++
              rootPrefixValues right input.length ++
            [right.eval input.length] =
          existing ++ registerValues left input.length ++
            registerValues right input.length := by
        rw [hLeftValues, hRightValues]
        simp [List.append_assoc]
      have hOperationFinal :
          existing ++ rootPrefixValues left input.length ++
                [left.eval input.length] ++
              rootPrefixValues right input.length ++
            [right.eval input.length,
              left.eval input.length + right.eval input.length] =
          existing ++ registerValues left input.length ++
            registerValues right input.length ++
              [left.eval input.length + right.eval input.length] := by
        rw [hLeftValues, hRightValues]
        simp [List.append_assoc]
      rw [hOperationStart, hOperationFinal,
        ← hRightValues] at hOperation
      have h01 := workRunExact_compose_for
        (closedSpecMachine machineSpecs)
        (compilerSteps left input.length existing)
        (compilerSteps right input.length
          (existing ++ registerValues left input.length))
        (endConfiguration base outsideTail (registerWord existing)
          (sourceInside input workspace))
        (endConfiguration rightBase
          (outsideTail.drop
            (registerWord (registerValues left input.length)).length)
          (registerWord
            (existing ++ registerValues left input.length))
          (sourceInside input workspace))
        (endConfiguration operationBase
          ((outsideTail.drop
            (registerWord (registerValues left input.length)).length).drop
              (registerWord (registerValues right input.length)).length)
          (registerWord
            (existing ++ registerValues left input.length ++
              registerValues right input.length))
          (sourceInside input workspace))
        (by simpa [machineSpecs, List.append_assoc] using hLeft)
        (by simpa [machineSpecs, List.append_assoc] using hRight)
      have h02 := workRunExact_compose_for
        (closedSpecMachine machineSpecs)
        (compilerSteps left input.length existing +
          compilerSteps right input.length
            (existing ++ registerValues left input.length))
        (addOperationSteps (registerValues right input.length)
          (left.eval input.length) (right.eval input.length))
        (endConfiguration base outsideTail (registerWord existing)
          (sourceInside input workspace))
        (endConfiguration operationBase
          ((outsideTail.drop
            (registerWord (registerValues left input.length)).length).drop
              (registerWord (registerValues right input.length)).length)
          (registerWord
            (existing ++ registerValues left input.length ++
              registerValues right input.length))
          (sourceInside input workspace))
        (endConfiguration next
          (((outsideTail.drop
            (registerWord (registerValues left input.length)).length).drop
              (registerWord (registerValues right input.length)).length).drop
                (left.eval input.length + right.eval input.length + 1))
          (registerWord
            (existing ++ registerValues left input.length ++
              registerValues right input.length ++
                [left.eval input.length + right.eval input.length]))
          (sourceInside input workspace))
        h01 (by
          simpa [machineSpecs, List.append_assoc] using hOperation)
      rw [hMachine]
      simpa [compilerSteps, registerValues, registerWord_append,
        List.drop_drop, List.length_append, List.append_assoc,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h02
  | mul left right leftIH rightIH =>
      let rightBase := base + compilerStateCount left
      let operationBase := rightBase + compilerStateCount right
      let rightSpecs := compileSpecs right rightBase operationBase dead
      let operationSpecs :=
        mulOperationSpecs (nodeCount right) operationBase next dead
      let machineSpecs := specPrefix ++
        compileSpecs left base rightBase dead ++ rightSpecs ++
          operationSpecs ++ suffix
      have hLeft := leftIH base rightBase specPrefix
        (rightSpecs ++ operationSpecs ++ suffix) outsideTail existing hBase rfl
      have hRightPrefix :
          (specPrefix ++ compileSpecs left base rightBase dead).length =
            rightBase := by
        simp [rightBase, hBase]
      have hRight := rightIH rightBase operationBase
        (specPrefix ++ compileSpecs left base rightBase dead)
        (operationSpecs ++ suffix)
        (outsideTail.drop
          (registerWord (registerValues left input.length)).length)
        (existing ++ registerValues left input.length)
        hRightPrefix rfl
      have hOperationPrefix :
          (specPrefix ++ compileSpecs left base rightBase dead ++
            rightSpecs).length = operationBase := by
        simp [rightSpecs, operationBase, rightBase, hBase]
        omega
      have hOperation := mulOperation_exact (nodeCount right)
        operationBase next dead
        (specPrefix ++ compileSpecs left base rightBase dead ++ rightSpecs)
        suffix existing (rootPrefixValues left input.length)
        (rootPrefixValues right input.length)
        (left.eval input.length) (right.eval input.length)
        (sourceInside input workspace)
        ((outsideTail.drop
          (registerWord (registerValues left input.length)).length).drop
            (registerWord (registerValues right input.length)).length)
        hOperationPrefix (by
          have hLength := registerValues_length right input.length
          rw [registerValues_eq_rootPrefixValues] at hLength
          exact hLength)
      have hMachine :
          specPrefix ++ compileSpecs (.mul left right) base next dead ++
              suffix = machineSpecs := by
        simp [compileSpecs, machineSpecs, rightSpecs, operationSpecs,
          rightBase, operationBase, List.append_assoc]
      have hLeftValues :=
        registerValues_eq_rootPrefixValues left input.length
      have hRightValues :=
        registerValues_eq_rootPrefixValues right input.length
      have hOperationStart :
          existing ++ rootPrefixValues left input.length ++
                [left.eval input.length] ++
              rootPrefixValues right input.length ++
            [right.eval input.length] =
          existing ++ registerValues left input.length ++
            registerValues right input.length := by
        rw [hLeftValues, hRightValues]
        simp [List.append_assoc]
      have hOperationFinal :
          existing ++ rootPrefixValues left input.length ++
                [left.eval input.length] ++
              rootPrefixValues right input.length ++
            [right.eval input.length,
              left.eval input.length * right.eval input.length] =
          existing ++ registerValues left input.length ++
            registerValues right input.length ++
              [left.eval input.length * right.eval input.length] := by
        rw [hLeftValues, hRightValues]
        simp [List.append_assoc]
      rw [hOperationStart, hOperationFinal] at hOperation
      have h01 := workRunExact_compose_for
        (closedSpecMachine machineSpecs)
        (compilerSteps left input.length existing)
        (compilerSteps right input.length
          (existing ++ registerValues left input.length))
        (endConfiguration base outsideTail (registerWord existing)
          (sourceInside input workspace))
        (endConfiguration rightBase
          (outsideTail.drop
            (registerWord (registerValues left input.length)).length)
          (registerWord
            (existing ++ registerValues left input.length))
          (sourceInside input workspace))
        (endConfiguration operationBase
          ((outsideTail.drop
            (registerWord (registerValues left input.length)).length).drop
              (registerWord (registerValues right input.length)).length)
          (registerWord
            (existing ++ registerValues left input.length ++
              registerValues right input.length))
          (sourceInside input workspace))
        (by simpa [machineSpecs, List.append_assoc] using hLeft)
        (by simpa [machineSpecs, List.append_assoc] using hRight)
      have h02 := workRunExact_compose_for
        (closedSpecMachine machineSpecs)
        (compilerSteps left input.length existing +
          compilerSteps right input.length
            (existing ++ registerValues left input.length))
        (mulOperationSteps (rootPrefixValues right input.length)
          (left.eval input.length) (right.eval input.length))
        (endConfiguration base outsideTail (registerWord existing)
          (sourceInside input workspace))
        (endConfiguration operationBase
          ((outsideTail.drop
            (registerWord (registerValues left input.length)).length).drop
              (registerWord (registerValues right input.length)).length)
          (registerWord
            (existing ++ registerValues left input.length ++
              registerValues right input.length))
          (sourceInside input workspace))
        (endConfiguration next
          (((outsideTail.drop
            (registerWord (registerValues left input.length)).length).drop
              (registerWord (registerValues right input.length)).length).drop
                (left.eval input.length * right.eval input.length + 1))
          (registerWord
            (existing ++ registerValues left input.length ++
              registerValues right input.length ++
                [left.eval input.length * right.eval input.length]))
          (sourceInside input workspace))
        h01 (by
          simpa [machineSpecs, List.append_assoc] using hOperation)
      rw [hMachine]
      simpa [compilerSteps, registerValues, registerWord_append,
        List.drop_drop, List.length_append, List.append_assoc,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h02

/-! ### Initialization, rewind, and public evaluator endpoint -/

private def workspaceSuffix (input : BitString)
    (output : List CNFToken) : List WorkSymbol :=
  List.replicate input.length BuilderInputLength.tallySymbol ++
    BuilderTokenAppender.outputRegion output

private theorem initialization_exact
    (polynomial : NatPolynomial) (input : BitString)
    (outsideLeft : List WorkSymbol) (output : List CNFToken) :
    workRunExact? (closedSpecMachine (stateSpecs polynomial)) 3
        { state := 0
          tape := BuilderTokenAppender.workspaceTape
            input outsideLeft output } =
      some
        (endConfiguration 3 (outsideLeft.drop 1) []
          (sourceInside input (workspaceSuffix input output))) := by
  let tape0 := BuilderTokenAppender.workspaceTape input outsideLeft output
  let tape1 := tape0.moveLeft
  let tape2 := tape1.moveLeft
  let c0 : WorkConfiguration := { state := 0, tape := tape0 }
  let c1 : WorkConfiguration := { state := 1, tape := tape1 }
  let c2 : WorkConfiguration := { state := 2, tape := tape2 }
  let c3 := endConfiguration 3 (outsideLeft.drop 1) []
    (sourceInside input (workspaceSuffix input output))
  have hFirstStep := closedSpecMachine_step []
    (initializationStartSpec (deadState polynomial))
    ([initializationMarkerSpec (deadState polynomial),
      initializationEndSpec 3] ++
      compileSpecs polynomial 3 (3 + compilerStateCount polynomial)
        (deadState polynomial) ++
      [rewindSpec (acceptState polynomial) (deadState polynomial)]) tape0
  have hFirstAllowed : tape0.head = WorkSymbol.blank ∨
      tape0.head = WorkSymbol.zeroBlank ∨
      tape0.head = WorkSymbol.oneBlank := by
    cases input with
    | nil =>
        simp [tape0, BuilderTokenAppender.workspaceTape,
          frameWithGarbage, Tape.ofInput, Tape.blank, dataSymbol,
          WorkSymbol.blank]
    | cons first rest =>
        cases first <;>
          simp [tape0, BuilderTokenAppender.workspaceTape,
            frameWithGarbage, Tape.ofInput, dataSymbol,
            TapeSymbol.ofBool, WorkSymbol.zeroBlank,
            WorkSymbol.oneBlank]
  have hFirstAction : initializationStartSpec (deadState polynomial)
      tape0.head = keepAction 1 .left tape0.head := by
    simp [initializationStartSpec, hFirstAllowed]
  rw [hFirstAction] at hFirstStep
  have hFirst : workRunExact? (closedSpecMachine (stateSpecs polynomial))
      1 c0 = some c1 := by
    apply workRunExact_one_for
    simpa [stateSpecs, initializationSpecs, c0, c1, tape1,
      keepAction, WorkTape.move, List.append_assoc] using hFirstStep
  have hSecondStep := closedSpecMachine_step
    [initializationStartSpec (deadState polynomial)]
    (initializationMarkerSpec (deadState polynomial))
    ([initializationEndSpec 3] ++
      compileSpecs polynomial 3 (3 + compilerStateCount polynomial)
        (deadState polynomial) ++
      [rewindSpec (acceptState polynomial) (deadState polynomial)]) tape1
  have hSecondHead : tape1.head = leftMarker := by
    cases input with
    | nil =>
        simp [tape0, tape1, BuilderTokenAppender.workspaceTape,
          frameWithGarbage, Tape.ofInput, Tape.blank, dataSymbol,
          leftMarker, WorkTape.moveLeft]
    | cons first rest =>
        simp [tape0, tape1, BuilderTokenAppender.workspaceTape,
          frameWithGarbage, Tape.ofInput, leftMarker, WorkTape.moveLeft]
  have hSecondAction : initializationMarkerSpec (deadState polynomial)
      tape1.head = keepAction 2 .left tape1.head := by
    simp [initializationMarkerSpec, hSecondHead]
  rw [hSecondAction] at hSecondStep
  have hSecond : workRunExact? (closedSpecMachine (stateSpecs polynomial))
      1 c1 = some c2 := by
    apply workRunExact_one_for
    simpa [stateSpecs, initializationSpecs, c1, c2, tape2,
      keepAction, WorkTape.move, List.append_assoc] using hSecondStep
  have hThirdStep := closedSpecMachine_step
    [initializationStartSpec (deadState polynomial),
      initializationMarkerSpec (deadState polynomial)]
    (initializationEndSpec 3)
    (compileSpecs polynomial 3 (3 + compilerStateCount polynomial)
        (deadState polynomial) ++
      [rewindSpec (acceptState polynomial) (deadState polynomial)]) tape2
  have hThird : workRunExact? (closedSpecMachine (stateSpecs polynomial))
      1 c2 = some c3 := by
    apply workRunExact_one_for
    cases input <;> cases outsideLeft <;>
      simp [stateSpecs, initializationSpecs, c2, c3, tape0, tape1,
        tape2, initializationEndSpec, writeAction, WorkTape.move,
        BuilderTokenAppender.workspaceTape, frameWithGarbage,
        Tape.ofInput, endConfiguration, endTape, sourceInside,
        Tape.blank, dataSymbol, sourceWord, workspaceSuffix] at hThirdStep ⊢
    all_goals exact hThirdStep
  have h01 := workRunExact_compose_for
    (closedSpecMachine (stateSpecs polynomial)) 1 1 c0 c1 c2 hFirst hSecond
  have h03 := workRunExact_compose_for
    (closedSpecMachine (stateSpecs polynomial)) 2 1 c0 c2 c3 h01 hThird
  simpa [c0, c3, tape0] using h03

private theorem rewind_scratch_step
    (polynomial : NatPolynomial) (tape : WorkTape)
    (hAllowed : tape.head = scratchEndSymbol ∨ ScratchSymbol tape.head) :
    workStep? (closedSpecMachine (stateSpecs polynomial))
        { state := 3 + compilerStateCount polynomial, tape := tape } =
      some
        { state := 3 + compilerStateCount polynomial
          tape := tape.moveRight } := by
  have hStep := closedSpecMachine_step
    (initializationSpecs 3 (deadState polynomial) ++
      compileSpecs polynomial 3 (3 + compilerStateCount polynomial)
        (deadState polynomial))
    (rewindSpec (acceptState polynomial) (deadState polynomial)) [] tape
  have hAction : rewindSpec (acceptState polynomial)
      (deadState polynomial) tape.head =
        keepAction (3 + compilerStateCount polynomial) .right tape.head := by
    rcases hAllowed with hEnd | hScratch
    · simp [rewindSpec, hEnd, stateCount, acceptState]
    · rcases hScratch with hUnit | hSeparator | hMark
      · simp [rewindSpec, hUnit, stateCount, acceptState]
      · simp [rewindSpec, hSeparator, stateCount, acceptState]
      · simp [rewindSpec, hMark, stateCount, acceptState]
  rw [hAction] at hStep
  have hPrefixLength :
      (initializationSpecs 3 (deadState polynomial) ++
        compileSpecs polynomial 3 (3 + compilerStateCount polynomial)
          (deadState polynomial)).length =
        3 + compilerStateCount polynomial := by
    simp [initializationSpecs]
    omega
  rw [hPrefixLength] at hStep
  simpa [stateSpecs, initializationSpecs, keepAction, WorkTape.move,
    List.append_assoc,
    Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hStep

private theorem rewind_marker_step
    (polynomial : NatPolynomial) (tape : WorkTape)
    (hHead : tape.head = leftMarker) :
    workStep? (closedSpecMachine (stateSpecs polynomial))
        { state := 3 + compilerStateCount polynomial, tape := tape } =
      some { state := acceptState polynomial, tape := tape.moveRight } := by
  have hStep := closedSpecMachine_step
    (initializationSpecs 3 (deadState polynomial) ++
      compileSpecs polynomial 3 (3 + compilerStateCount polynomial)
        (deadState polynomial))
    (rewindSpec (acceptState polynomial) (deadState polynomial)) [] tape
  have hAction : rewindSpec (acceptState polynomial)
      (deadState polynomial) tape.head =
        keepAction (acceptState polynomial) .right tape.head := by
    simp [rewindSpec, hHead, leftMarker, scratchEndSymbol,
      unitSymbol, separatorSymbol, registerMarkSymbol,
      WorkSymbol.blankOne, WorkSymbol.oneOne,
      WorkSymbol.zeroOne, WorkSymbol.zeroZero]
  rw [hAction] at hStep
  have hPrefixLength :
      (initializationSpecs 3 (deadState polynomial) ++
        compileSpecs polynomial 3 (3 + compilerStateCount polynomial)
          (deadState polynomial)).length =
        3 + compilerStateCount polynomial := by
    simp [initializationSpecs]
    omega
  rw [hPrefixLength] at hStep
  simpa [stateSpecs, initializationSpecs, keepAction, WorkTape.move,
    List.append_assoc,
    Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hStep

private def RewindSymbol (symbol : WorkSymbol) : Prop :=
  symbol = scratchEndSymbol ∨ ScratchSymbol symbol

private theorem rewind_scan_exact
    (polynomial : NatPolynomial) (symbols : List WorkSymbol)
    (leftSide rightSide : List WorkSymbol)
    (hSymbols : ∀ symbol ∈ symbols, RewindSymbol symbol) :
    workRunExact? (closedSpecMachine (stateSpecs polynomial)) symbols.length
        { state := 3 + compilerStateCount polynomial
          tape := pathTape leftSide (symbols ++ rightSide) } =
      some
        { state := 3 + compilerStateCount polynomial
          tape := pathTape (symbols.reverse ++ leftSide) rightSide } := by
  induction symbols generalizing leftSide with
  | nil => rfl
  | cons first rest ih =>
      have hFirstAllowed := hSymbols first (List.Mem.head rest)
      have hRestAllowed : ∀ symbol ∈ rest, RewindSymbol symbol := by
        intro symbol hMem
        exact hSymbols symbol (List.Mem.tail first hMem)
      have hStep := rewind_scratch_step polynomial
        (pathTape leftSide (first :: rest ++ rightSide)) hFirstAllowed
      have hFirst := workRunExact_one_for
        (closedSpecMachine (stateSpecs polynomial))
        { state := 3 + compilerStateCount polynomial
          tape := pathTape leftSide (first :: rest ++ rightSide) }
        { state := 3 + compilerStateCount polynomial
          tape := pathTape (first :: leftSide) (rest ++ rightSide) }
        (by simpa using hStep)
      have hRest := ih (first :: leftSide) hRestAllowed
      have hAll := workRunExact_compose_for
        (closedSpecMachine (stateSpecs polynomial)) 1 rest.length
        { state := 3 + compilerStateCount polynomial
          tape := pathTape leftSide (first :: rest ++ rightSide) }
        { state := 3 + compilerStateCount polynomial
          tape := pathTape (first :: leftSide) (rest ++ rightSide) }
        { state := 3 + compilerStateCount polynomial
          tape := pathTape (rest.reverse ++ first :: leftSide) rightSide }
        hFirst hRest
      simpa [List.reverse_cons, List.append_assoc, Nat.add_comm] using hAll

private theorem rewind_exact
    (polynomial : NatPolynomial) (input : BitString)
    (outsideTail word : List WorkSymbol) (output : List CNFToken)
    (hScratch : ∀ symbol ∈ word, ScratchSymbol symbol) :
    workRunExact? (closedSpecMachine (stateSpecs polynomial))
        (word.length + 2)
        (endConfiguration (3 + compilerStateCount polynomial)
          outsideTail word
          (sourceInside input (workspaceSuffix input output))) =
      some
        { state := acceptState polynomial
          tape := BuilderTokenAppender.workspaceTape input
            (word ++ scratchEndSymbol :: outsideTail) output } := by
  let symbols := scratchEndSymbol :: word.reverse
  have hSymbols : ∀ symbol ∈ symbols, RewindSymbol symbol := by
    intro symbol hMem
    simp only [symbols, List.mem_cons, List.mem_reverse] at hMem
    rcases hMem with hEnd | hWord
    · exact Or.inl hEnd
    · exact Or.inr (hScratch symbol hWord)
  have hScan := rewind_scan_exact polynomial symbols outsideTail
    (sourceInside input (workspaceSuffix input output)) hSymbols
  have hMarkerStep := rewind_marker_step polynomial
    (pathTape (symbols.reverse ++ outsideTail)
      (leftMarker :: sourceWord input ++
        rightMarker :: workspaceSuffix input output)) rfl
  have hMarker := workRunExact_one_for
    (closedSpecMachine (stateSpecs polynomial))
    { state := 3 + compilerStateCount polynomial
      tape := pathTape (symbols.reverse ++ outsideTail)
        (leftMarker :: sourceWord input ++
          rightMarker :: workspaceSuffix input output) }
    { state := acceptState polynomial
      tape := pathTape
        (leftMarker :: symbols.reverse ++ outsideTail)
        (sourceWord input ++ rightMarker :: workspaceSuffix input output) }
    (by simpa using hMarkerStep)
  have hAll := workRunExact_compose_for
    (closedSpecMachine (stateSpecs polynomial)) symbols.length 1
    (endConfiguration (3 + compilerStateCount polynomial)
      outsideTail word
      (sourceInside input (workspaceSuffix input output)))
    { state := 3 + compilerStateCount polynomial
      tape := pathTape (symbols.reverse ++ outsideTail)
        (leftMarker :: sourceWord input ++
          rightMarker :: workspaceSuffix input output) }
    { state := acceptState polynomial
      tape := pathTape
        (leftMarker :: symbols.reverse ++ outsideTail)
        (sourceWord input ++ rightMarker :: workspaceSuffix input output) }
    (by simpa [symbols, endConfiguration, endTape, sourceInside,
      pathTape, List.reverse_cons, List.append_assoc] using hScan)
    hMarker
  cases input with
  | nil =>
      simpa [symbols, workspaceSuffix, sourceInside,
        BuilderTokenAppender.workspaceTape, frameWithGarbage, Tape.ofInput,
        Tape.blank, dataSymbol, WorkSymbol.blank, sourceWord, pathTape,
        List.reverse_cons, List.reverse_reverse, List.append_assoc,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hAll
  | cons first rest =>
      simpa [symbols, workspaceSuffix, sourceInside,
        BuilderTokenAppender.workspaceTape, frameWithGarbage, Tape.ofInput,
        sourceWord, pathTape, Function.comp_def,
        List.reverse_cons, List.reverse_reverse,
        List.append_assoc, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm] using hAll

/-- Exact evaluator work cost for one represented input and empty scratch. -/
def workSteps (polynomial : NatPolynomial) (input : BitString) : Nat :=
  3 + compilerSteps polynomial input.length [] +
    (scratchWord polynomial input.length).length + 2

/-- Exterior-left tape after the evaluator overwrites its finite scratch
prefix and restores the logical input focus. -/
def finalOutsideLeft (polynomial : NatPolynomial) (input : BitString)
    (outsideLeft : List WorkSymbol) : List WorkSymbol :=
  overlayScratch (scratchWord polynomial input.length) outsideLeft

/-- Canonical evaluator entry configuration. -/
def initialConfiguration (polynomial : NatPolynomial) (input : BitString)
    (outsideLeft : List WorkSymbol) (output : List CNFToken) :
    WorkConfiguration :=
  { state := (machine polynomial).startState
    tape := BuilderTokenAppender.workspaceTape input outsideLeft output }

/-- Canonical evaluator endpoint, with the existing builder output and the
input/tally workspace preserved. -/
def finalConfiguration (polynomial : NatPolynomial) (input : BitString)
    (outsideLeft : List WorkSymbol) (output : List CNFToken) :
    WorkConfiguration :=
  { state := (machine polynomial).acceptState
    tape := BuilderTokenAppender.workspaceTape input
      (finalOutsideLeft polynomial input outsideLeft) output }

theorem root_register_length (polynomial : NatPolynomial)
    (inputLength : Nat) :
    ∃ wordPrefix,
      scratchWord polynomial inputLength =
          wordPrefix ++ separatorSymbol ::
            List.replicate (polynomial.eval inputLength) unitSymbol ∧
      wordPrefix.length + 1 =
        (rootPrefixPolynomial polynomial).eval inputLength :=
  root_prefix_length polynomial inputLength

/-- Every materialized evaluator scratch cell before the active end marker
is either a unary unit or a register separator. -/
theorem scratchWord_symbol (polynomial : NatPolynomial) (inputLength : Nat)
    (symbol : WorkSymbol) (hMem : symbol ∈ scratchWord polynomial inputLength) :
    symbol = unitSymbol ∨ symbol = separatorSymbol := by
  have hRegister : ∀ values symbol,
      symbol ∈ registerWord values →
        symbol = unitSymbol ∨ symbol = separatorSymbol := by
    intro values
    induction values with
    | nil => intro item hItem; contradiction
    | cons value rest ih =>
        intro item hItem
        simp only [registerWord, List.mem_cons, List.mem_append] at hItem
        rcases hItem with hSeparator | hUnits | hRest
        · exact Or.inr hSeparator
        · exact Or.inl (List.eq_of_mem_replicate hUnits)
        · exact ih item hRest
  exact hRegister (registerValues polynomial inputLength) symbol
    (by simpa [scratchWord] using hMem)

/-- Exact all-input trace of the literal compiled unary evaluator. -/
theorem workRunExact (polynomial : NatPolynomial) (input : BitString)
    (outsideLeft : List WorkSymbol) (output : List CNFToken) :
    workRunExact? (machine polynomial) (workSteps polynomial input)
        (initialConfiguration polynomial input outsideLeft output) =
      some (finalConfiguration polynomial input outsideLeft output) := by
  let rewind := 3 + compilerStateCount polynomial
  let scratch := scratchWord polynomial input.length
  let suffix := workspaceSuffix input output
  let closed := closedSpecMachine (stateSpecs polynomial)
  let c0 := initialConfiguration polynomial input outsideLeft output
  let c1 := endConfiguration 3 (outsideLeft.drop 1) []
    (sourceInside input suffix)
  let c2 := endConfiguration rewind
    ((outsideLeft.drop 1).drop scratch.length) scratch
    (sourceInside input suffix)
  let c3 := finalConfiguration polynomial input outsideLeft output
  have hInit := initialization_exact polynomial input outsideLeft output
  have hCompilePrefix :
      (initializationSpecs 3 (deadState polynomial)).length = 3 := by rfl
  have hCompile := compile_exact polynomial 3 rewind
    (deadState polynomial)
    (initializationSpecs 3 (deadState polynomial))
    [rewindSpec (acceptState polynomial) (deadState polynomial)]
    input suffix (outsideLeft.drop 1) [] hCompilePrefix rfl
  have hCompileMachine :
      initializationSpecs 3 (deadState polynomial) ++
          compileSpecs polynomial 3 rewind (deadState polynomial) ++
            [rewindSpec (acceptState polynomial) (deadState polynomial)] =
        stateSpecs polynomial := by
    simp [stateSpecs, rewind, List.append_assoc]
  rw [hCompileMachine] at hCompile
  have hRewind := rewind_exact polynomial input
    ((outsideLeft.drop 1).drop scratch.length) scratch output
    (registerWord_scratch (registerValues polynomial input.length))
  have hInitExact : workRunExact? closed 3 c0 = some c1 := by
    simpa [closed, c0, c1, initialConfiguration, machine, suffix]
      using hInit
  have hCompileExact :
      workRunExact? closed
          (compilerSteps polynomial input.length []) c1 = some c2 := by
    simpa [closed, c1, c2, rewind, scratch, suffix, scratchWord,
      registerWord]
      using hCompile
  have hRewindExact :
      workRunExact? closed (scratch.length + 2) c2 = some c3 := by
    simpa [closed, c2, c3, rewind, scratch, suffix,
      finalConfiguration, machine, finalOutsideLeft, overlayScratch,
      List.drop_drop, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
      using hRewind
  have h01 := workRunExact_compose_for closed 3
    (compilerSteps polynomial input.length []) c0 c1 c2
    hInitExact hCompileExact
  have h03 := workRunExact_compose_for closed
    (3 + compilerSteps polynomial input.length [])
    (scratch.length + 2) c0 c2 c3 h01 hRewindExact
  rw [machine_eq_closedSpecMachine polynomial]
  simpa [workSteps, closed, c0, c3, scratch,
    Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h03

/-! ### Exact external runtime polynomial -/

private theorem sourceCopyLoopSteps_closed
    (wordLength processed remaining : Nat) :
    sourceCopyLoopSteps wordLength processed remaining =
      2 * wordLength * remaining + 2 * processed * remaining +
        2 * remaining * remaining + 9 * remaining +
          2 * wordLength + 2 * processed + 5 := by
  induction remaining generalizing wordLength processed with
  | zero =>
      simp [sourceCopyLoopSteps, sourceFinishSteps]
  | succ remaining ih =>
      simp only [sourceCopyLoopSteps, sourceIterationSteps, ih]
      simp [Nat.add_mul, Nat.mul_add]
      omega

private theorem sourceCopySteps_closed (wordLength inputLength : Nat) :
    sourceCopySteps wordLength inputLength =
      2 * wordLength * inputLength + 2 * inputLength * inputLength +
        9 * inputLength + 2 * wordLength + 5 := by
  unfold sourceCopySteps
  rw [sourceCopyLoopSteps_closed]
  simp

private theorem copyLoopSteps_closed
    (intermediate : List Nat) (destination processed remaining : Nat) :
    let base := intermediate.length + 1 + intermediate.sum + destination
    copyLoopSteps intermediate destination processed remaining =
      2 * base * remaining + 4 * processed * remaining +
        2 * remaining * remaining + 7 * remaining +
          2 * base + 4 * processed + 3 := by
  induction remaining generalizing processed with
  | zero =>
      simp [copyLoopSteps, copyFinishSteps, copyNewerValues,
        registerWord_length]
      omega
  | succ remaining ih =>
      simp only [copyLoopSteps, copyIterationSteps, ih]
      simp [copyNewerValues, registerWord_length,
        Nat.add_mul, Nat.mul_add]
      omega

private theorem copySteps_closed
    (intermediate : List Nat) (destination sourceValue : Nat) :
    let base := intermediate.length + 1 + intermediate.sum + destination
    copySteps intermediate destination sourceValue =
      2 * base * sourceValue + 2 * sourceValue * sourceValue +
        7 * sourceValue + 2 * base + 3 := by
  unfold copySteps
  rw [copyLoopSteps_closed]
  simp

private theorem multiplyLoopSteps_closed
    (rightPrefix : List Nat) (rightValue processed remaining : Nat) :
    let base := rightPrefix.length + 2 + rightPrefix.sum + rightValue
    let square := rightValue * rightValue
    let stepSquare := square + 2 * rightValue + 1
    multiplyLoopSteps rightPrefix rightValue processed remaining =
      remaining * (2 * base + square + 7 * rightValue + 7) +
        stepSquare * remaining * remaining +
          2 * stepSquare * remaining * processed +
            2 * base + 2 * (processed + remaining) * rightValue +
              2 * (processed + remaining) + 3 := by
  induction remaining generalizing processed with
  | zero =>
      simp [multiplyLoopSteps, multiplyFinishSteps,
        multiplyNewerValues, registerWord_length, Nat.add_mul,
        Nat.mul_add, Nat.mul_two, Nat.two_mul]
      omega
  | succ remaining ih =>
      simp only [multiplyLoopSteps, multiplyIterationSteps, ih]
      rw [copySteps_closed]
      simp [multiplyNewerValues, registerWord_length,
        Nat.add_mul, Nat.mul_add, Nat.mul_two, Nat.two_mul]
      have hProcessedRight : processed * rightValue =
          rightValue * processed := Nat.mul_comm _ _
      have hProcessedSquare :
          (processed * rightValue) * rightValue =
            (rightValue * rightValue) * processed := by
        rw [Nat.mul_assoc, Nat.mul_comm processed]
      omega

private theorem multiplySteps_closed
    (rightPrefix : List Nat) (leftValue rightValue : Nat) :
    let base := rightPrefix.length + 2 + rightPrefix.sum + rightValue
    let square := rightValue * rightValue
    let stepSquare := square + 2 * rightValue + 1
    multiplySteps rightPrefix leftValue rightValue =
      leftValue * (2 * base + square + 7 * rightValue + 7) +
        stepSquare * leftValue * leftValue +
          2 * base + 2 * leftValue * rightValue + 2 * leftValue + 3 := by
  unfold multiplySteps
  rw [multiplyLoopSteps_closed]
  simp

def sumPolynomial : List NatPolynomial → NatPolynomial
  | [] => .constant 0
  | polynomial :: rest => .add polynomial (sumPolynomial rest)

def registerValuePolynomials : NatPolynomial → List NatPolynomial
  | polynomial@(.constant _) => [polynomial]
  | .variable => [.variable]
  | polynomial@(.add left right) =>
      registerValuePolynomials left ++ registerValuePolynomials right ++
        [polynomial]
  | polynomial@(.mul left right) =>
      registerValuePolynomials left ++ registerValuePolynomials right ++
        [polynomial]

def rootPrefixValuePolynomials : NatPolynomial → List NatPolynomial
  | .constant _ => []
  | .variable => []
  | .add left right =>
      registerValuePolynomials left ++ registerValuePolynomials right
  | .mul left right =>
      registerValuePolynomials left ++ registerValuePolynomials right

def registerWordPolynomial (values : List NatPolynomial) : NatPolynomial :=
  .add (.constant values.length) (sumPolynomial values)

private def scalePolynomial (coefficient : Nat)
    (polynomial : NatPolynomial) : NatPolynomial :=
  .mul (.constant coefficient) polynomial

private def squarePolynomial (polynomial : NatPolynomial) : NatPolynomial :=
  .mul polynomial polynomial

private def sourceCopyPolynomial (wordLength : NatPolynomial) :
    NatPolynomial :=
  let input := NatPolynomial.variable
  .add
    (.add
      (.add
        (.add
          (.mul (scalePolynomial 2 wordLength) input)
          (scalePolynomial 2 (squarePolynomial input)))
        (scalePolynomial 9 input))
      (scalePolynomial 2 wordLength))
    (.constant 5)

private def copyPolynomial (intermediate : List NatPolynomial)
    (destination sourceValue : NatPolynomial) : NatPolynomial :=
  let base := .add
    (.add (.constant (intermediate.length + 1))
      (sumPolynomial intermediate))
    destination
  .add
    (.add
      (.add
        (.add
          (.mul (scalePolynomial 2 base) sourceValue)
          (scalePolynomial 2 (squarePolynomial sourceValue)))
        (scalePolynomial 7 sourceValue))
      (scalePolynomial 2 base))
    (.constant 3)

private def multiplyPolynomial (rightPrefix : List NatPolynomial)
    (leftValue rightValue : NatPolynomial) : NatPolynomial :=
  let base := .add
    (.add (.constant (rightPrefix.length + 2))
      (sumPolynomial rightPrefix))
    rightValue
  let square := squarePolynomial rightValue
  let stepSquare := .add square
    (.add (scalePolynomial 2 rightValue) (.constant 1))
  .add
    (.add
      (.add
        (.add
          (.mul leftValue
            (.add (scalePolynomial 2 base)
              (.add square
                (.add (scalePolynomial 7 rightValue) (.constant 7)))))
          (.mul stepSquare (squarePolynomial leftValue)))
        (scalePolynomial 2 base))
      (.mul (scalePolynomial 2 leftValue) rightValue))
    (.add (scalePolynomial 2 leftValue) (.constant 3))

def compilerStepsPolynomial :
    NatPolynomial → List NatPolynomial → NatPolynomial
  | .constant value, _ => .constant (2 + 2 * value)
  | .variable, existing =>
      .add (.constant 2)
        (sourceCopyPolynomial
          (.add (registerWordPolynomial existing) (.constant 1)))
  | .add left right, existing =>
      .add
        (.add
          (compilerStepsPolynomial left existing)
          (compilerStepsPolynomial right
            (existing ++ registerValuePolynomials left)))
        (.add (.constant 2)
          (.add
            (copyPolynomial (registerValuePolynomials right)
              (.constant 0) left)
            (copyPolynomial [] left right)))
  | .mul left right, existing =>
      .add
        (.add
          (compilerStepsPolynomial left existing)
          (compilerStepsPolynomial right
            (existing ++ registerValuePolynomials left)))
        (.add (.constant 2)
          (multiplyPolynomial (rootPrefixValuePolynomials right)
            left right))

private theorem sumPolynomial_eval (values : List NatPolynomial)
    (input : Nat) :
    (sumPolynomial values).eval input =
      (values.map (fun polynomial => polynomial.eval input)).sum := by
  induction values with
  | nil => rfl
  | cons polynomial rest ih =>
      simp [sumPolynomial, ih]

private theorem registerValuePolynomials_eval
    (polynomial : NatPolynomial) (input : Nat) :
    registerValues polynomial input =
      (registerValuePolynomials polynomial).map
        (fun value => value.eval input) := by
  induction polynomial with
  | constant value => rfl
  | «variable» => rfl
  | add left right leftIH rightIH =>
      simp [registerValues, registerValuePolynomials, leftIH, rightIH,
        List.append_assoc]
  | mul left right leftIH rightIH =>
      simp [registerValues, registerValuePolynomials, leftIH, rightIH,
        List.append_assoc]

private theorem rootPrefixValuePolynomials_eval
    (polynomial : NatPolynomial) (input : Nat) :
    rootPrefixValues polynomial input =
      (rootPrefixValuePolynomials polynomial).map
        (fun value => value.eval input) := by
  cases polynomial <;>
    simp [rootPrefixValues, rootPrefixValuePolynomials,
      registerValuePolynomials_eval]

private theorem registerWordPolynomial_eval
    (values : List NatPolynomial) (input : Nat) :
    (registerWordPolynomial values).eval input =
      (registerWord
        (values.map (fun polynomial => polynomial.eval input))).length := by
  rw [registerWord_length]
  simp [registerWordPolynomial, sumPolynomial_eval]

private theorem sourceCopyPolynomial_eval (wordLength : NatPolynomial)
    (input : Nat) :
    (sourceCopyPolynomial wordLength).eval input =
      sourceCopySteps (wordLength.eval input) input := by
  rw [sourceCopySteps_closed]
  simp [sourceCopyPolynomial, scalePolynomial, squarePolynomial,
    Nat.mul_assoc]

private theorem copyPolynomial_eval (intermediate : List NatPolynomial)
    (destination sourceValue : NatPolynomial) (input : Nat) :
    (copyPolynomial intermediate destination sourceValue).eval input =
      copySteps
        (intermediate.map (fun polynomial => polynomial.eval input))
        (destination.eval input) (sourceValue.eval input) := by
  rw [copySteps_closed]
  simp [copyPolynomial, scalePolynomial, squarePolynomial,
    sumPolynomial_eval, Nat.mul_assoc]

private theorem multiplyPolynomial_eval
    (rightPrefix : List NatPolynomial)
    (leftValue rightValue : NatPolynomial) (input : Nat) :
    (multiplyPolynomial rightPrefix leftValue rightValue).eval input =
      multiplySteps
        (rightPrefix.map (fun polynomial => polynomial.eval input))
        (leftValue.eval input) (rightValue.eval input) := by
  rw [multiplySteps_closed]
  simp [multiplyPolynomial, scalePolynomial, squarePolynomial,
    sumPolynomial_eval, Nat.mul_assoc, Nat.add_assoc]

theorem compilerStepsPolynomial_eval (polynomial : NatPolynomial)
    (existing : List NatPolynomial) (input : Nat) :
    (compilerStepsPolynomial polynomial existing).eval input =
      compilerSteps polynomial input
        (existing.map (fun value => value.eval input)) := by
  induction polynomial generalizing existing with
  | constant value =>
      simp [compilerStepsPolynomial, compilerSteps, appendManyStateCount]
  | «variable» =>
      rw [compilerStepsPolynomial, compilerSteps]
      simp only [NatPolynomial.eval_add, NatPolynomial.eval_constant]
      rw [sourceCopyPolynomial_eval]
      change 2 + sourceCopySteps
        ((registerWordPolynomial existing).eval input + 1) input = _
      rw [registerWordPolynomial_eval]
      rfl
  | add left right leftIH rightIH =>
      rw [compilerStepsPolynomial, compilerSteps]
      simp only [NatPolynomial.eval_add, NatPolynomial.eval_constant]
      rw [leftIH, rightIH, copyPolynomial_eval, copyPolynomial_eval,
        registerValuePolynomials_eval]
      simp [List.map_append, addOperationSteps,
        registerValuePolynomials_eval, Nat.add_assoc]
  | mul left right leftIH rightIH =>
      rw [compilerStepsPolynomial, compilerSteps]
      simp only [NatPolynomial.eval_add, NatPolynomial.eval_constant]
      rw [leftIH, rightIH, multiplyPolynomial_eval,
        registerValuePolynomials_eval, rootPrefixValuePolynomials_eval]
      simp [List.map_append, mulOperationSteps,
        Nat.add_assoc]

/-- Exact work-transition polynomial for the structurally compiled unary
evaluator. -/
def workTimePolynomial (polynomial : NatPolynomial) : NatPolynomial :=
  .add
    (.add (.constant 3) (compilerStepsPolynomial polynomial []))
    (.add (registerSpanPolynomial polynomial) (.constant 2))

theorem workTimePolynomial_eval (polynomial : NatPolynomial)
    (input : BitString) :
    (workTimePolynomial polynomial).eval input.length =
      workSteps polynomial input := by
  rw [workTimePolynomial, NatPolynomial.eval_add,
    NatPolynomial.eval_add, NatPolynomial.eval_add,
    NatPolynomial.eval_constant, NatPolynomial.eval_constant,
    compilerStepsPolynomial_eval]
  rw [← scratchWord_length]
  rfl

end BuilderUnaryPolynomial

end CookLevin

end PNP.Concrete
