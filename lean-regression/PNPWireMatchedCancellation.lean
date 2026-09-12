import PNP

namespace PNP.DirectWire.WireMatchedCancellation.Regression

def dropAll {fields : Nat} : Fin fields → Bool := fun _ => false
def keepAll {fields : Nat} : Fin fields → Bool := fun _ => true

def tautologyProgram : Program 1 2 :=
  ((.empty : Program 1 0).snoc ⟨.input 0, .input 0⟩).snoc
    ⟨.input 0, .gate ⟨0, by decide⟩⟩

def outputAlias : WireCarrier 1 1 1 :=
  { implementation :=
      (Candidate.ofDirectWireWord tautologyProgram
        (⟨fun _ => .gate ⟨1, by decide⟩⟩ : DirectWireWord 1 2 1)).toImplementation
    source := fun _ => .gate ⟨1, by decide⟩ }

def mixedAliases : WireCarrier 1 1 2 :=
  { implementation :=
      (Candidate.ofDirectWireWord
        (tautologyProgram.snoc ⟨.input 0, .input 0⟩)
        (⟨fun _ => .gate ⟨1, by decide⟩⟩ : DirectWireWord 1 3 1)).toImplementation
    source := fun field =>
      if field.val = 0 then .gate ⟨1, by decide⟩ else .gate ⟨2, by decide⟩ }

def repeatedAliases : WireCarrier 1 1 4 :=
  { implementation := mixedAliases.implementation
    source := fun field =>
      if field.val = 1 || field.val = 3 then .gate ⟨1, by decide⟩
      else .gate ⟨2, by decide⟩ }

def trueReplacement (fields : Nat) : WireCarrier 1 1 fields :=
  { implementation :=
      (Candidate.ofDirectWireWord (.empty : Program 1 0)
        (⟨fun _ => .constant true⟩ : DirectWireWord 1 0 1)).toImplementation
    source := fun _ => .constant false }

private theorem trueReplacement_output (fields : Nat)
    (valuation : Valuation 1) (output : Fin 1) :
    (trueReplacement fields).implementation.candidate.semantics valuation output = true := by
  unfold trueReplacement
  dsimp only [Candidate.toImplementation]
  rw [Candidate.ofDirectWireWord_semantics]
  rfl

private theorem outputAlias_output (valuation : Valuation 1) (output : Fin 1) :
    outputAlias.implementation.candidate.semantics valuation output = true := by
  unfold outputAlias
  dsimp only [Candidate.toImplementation]
  rw [Candidate.ofDirectWireWord_semantics]
  change boolNand (valuation 0) (boolNand (valuation 0) (valuation 0)) = true
  cases valuation 0 <;> rfl

private theorem mixedAliases_output (valuation : Valuation 1) (output : Fin 1) :
    mixedAliases.implementation.candidate.semantics valuation output = true := by
  unfold mixedAliases
  dsimp only [Candidate.toImplementation]
  rw [Candidate.ofDirectWireWord_semantics]
  change boolNand (valuation 0) (boolNand (valuation 0) (valuation 0)) = true
  cases valuation 0 <;> rfl

private def trueAgreement {fields : Nat} (carrier : WireCarrier 1 1 fields)
    (outputTrue : ∀ valuation output,
      carrier.implementation.candidate.semantics valuation output = true) :
    WireQuotientLift.QuotientAgreement carrier dropAll (trueReplacement fields) where
  output := by
    intro valuation output
    rw [WireObligationRestoration.projected_output, trueReplacement_output]
    exact (outputTrue valuation output).symm
  keptField := by
    intro _valuation _field kept
    cases kept

def outputAgreement := trueAgreement outputAlias outputAlias_output
def mixedAgreement := trueAgreement mixedAliases mixedAliases_output
def repeatedAgreement := trueAgreement repeatedAliases mixedAliases_output

def keptAlias : WireCarrier 1 1 2 :=
  { implementation :=
      (Candidate.ofDirectWireWord
        ((.empty : Program 1 0).snoc ⟨.input 0, .input 0⟩)
        (⟨fun _ => .constant true⟩ : DirectWireWord 1 1 1)).toImplementation
    source := fun _ => .gate ⟨0, by decide⟩ }

def keepFirst (field : Fin 2) : Bool := field.val == 0

private def maskedAgreement {inputs outputs fields : Nat}
    (carrier : WireCarrier inputs outputs fields) (keep : Fin fields → Bool) :
    WireQuotientLift.QuotientAgreement carrier keep
      (WireObligationRestoration.masked carrier keep) where
  output := fun valuation output =>
    ((WireObligationRestoration.masked carrier keep).normalize_output valuation output).symm
  keptField := fun valuation field _kept =>
    ((WireObligationRestoration.masked carrier keep).normalize_field valuation field).symm

def noRetained : WireCarrier 1 0 2 :=
  { implementation :=
      (Candidate.ofDirectWireWord
        ((.empty : Program 1 0).snoc ⟨.input 0, .input 0⟩)
        (⟨Fin.elim0⟩ : DirectWireWord 1 1 0)).toImplementation
    source := fun _ => .gate ⟨0, by decide⟩ }

def paddingCollision : WireCarrier 1 1 1 :=
  { implementation :=
      (Candidate.ofDirectWireWord
        ((.empty : Program 1 0).snoc ⟨.input 0, .input 0⟩)
        (⟨fun _ => .constant false⟩ : DirectWireWord 1 1 1)).toImplementation
    source := fun _ => .gate ⟨0, by decide⟩ }

-- The same gate index in a different actual program has a different full value.
def unrelatedHidden : WireCarrier 1 1 1 :=
  { implementation :=
      (Candidate.ofDirectWireWord
        ((.empty : Program 1 0).snoc ⟨.constant true, .constant true⟩)
        (⟨fun _ => .constant false⟩ : DirectWireWord 1 1 1)).toImplementation
    source := fun _ => .gate ⟨0, by decide⟩ }

def unrelatedAgreement :
    WireQuotientLift.QuotientAgreement paddingCollision dropAll unrelatedHidden where
  output := by
    intro valuation output
    rw [WireObligationRestoration.projected_output]
    unfold unrelatedHidden paddingCollision
    dsimp only [Candidate.toImplementation]
    rw [Candidate.ofDirectWireWord_semantics, Candidate.ofDirectWireWord_semantics]
    rfl
  keptField := by
    intro _valuation _field kept
    cases kept

def freeFields : WireCarrier 1 1 4 :=
  { implementation :=
      (Candidate.ofDirectWireWord (.empty : Program 1 0)
        (⟨fun _ => .input 0⟩ : DirectWireWord 1 0 1)).toImplementation
    source := fun field =>
      if field.val = 1 then .constant false
      else if field.val = 3 then .constant true else .input 0 }

def freeKeep (field : Fin 4) : Bool := field.val == 1 || field.val == 3

def empty : WireCarrier 0 0 0 :=
  { implementation :=
      (Candidate.ofDirectWireWord (.empty : Program 0 0)
        (⟨Fin.elim0⟩ : DirectWireWord 0 0 0)).toImplementation
    source := Fin.elim0 }

example : (representative outputAlias dropAll 0).isSome = true := by decide
example : (representative keptAlias keepFirst 1).isSome = true := by decide
example : (representative mixedAliases dropAll 1).isSome = false := by decide
example : (representative noRetained dropAll 0).isSome = false := by decide
example : (representative noRetained dropAll 1).isSome = false := by decide
example : (representative paddingCollision dropAll 0).isSome = false := by decide
example : allResolved outputAlias dropAll = true := by decide
example : charge outputAlias dropAll = 0 :=
  charge_allResolved outputAlias dropAll (by decide)

-- A locally legal quotient replacement need not already restore forgotten fields.
example :
    (trueReplacement 1).fieldValue (fun _ => false) 0 ≠
      outputAlias.fieldValue (fun _ => false) 0 := by decide

example : ¬WireQuotientLift.QuotientAgreement outputAlias dropAll unrelatedHidden := by
  intro same
  have bad := same.output (fun _ => false) 0
  rw [WireObligationRestoration.projected_output] at bad
  change false = true at bad
  cases bad

example : ¬WireQuotientLift.QuotientAgreement keptAlias keepFirst (trueReplacement 2) := by
  intro same
  have bad := same.keptField (fun _ => false) 0 rfl
  rw [WireObligationRestoration.projected_kept_field
    keptAlias keepFirst (fun _ => false) 0 rfl] at bad
  change false = true at bad
  cases bad

example :
    unrelatedHidden.fieldValue (fun _ => false) 0 ≠
      paddingCollision.fieldValue (fun _ => false) 0 := by decide

example {inputs outputs fields : Nat}
    (carrier : WireCarrier inputs outputs fields) (keep : Fin fields → Bool)
    (replacement : WireCarrier inputs outputs fields)
    (same : WireQuotientLift.QuotientAgreement carrier keep replacement)
    (valuation : Valuation inputs) (field : Fin fields) :
    (expanded carrier keep replacement).fieldValue valuation field =
      carrier.fieldValue valuation field :=
  expanded_field carrier keep replacement same valuation field

example {inputs outputs fields : Nat}
    (carrier : WireCarrier inputs outputs fields) (keep : Fin fields → Bool)
    (replacement : WireCarrier inputs outputs fields)
    (same : WireQuotientLift.QuotientAgreement carrier keep replacement)
    (creation : WireObligationRestoration.R5Creation carrier keep)
    (valuation : Valuation inputs) :
    (discharge carrier keep replacement same creation).actualSource.eval valuation
        ((expanded carrier keep replacement).implementation.candidate.program.eval valuation) =
      carrier.fieldValue valuation creation.coordinate :=
  discharge_full_value carrier keep replacement same creation valuation

example {inputs outputs fields : Nat}
    (carrier : WireCarrier inputs outputs fields) (keep : Fin fields → Bool)
    (replacement : WireCarrier inputs outputs fields)
    (same : WireQuotientLift.QuotientAgreement carrier keep replacement) :
    replay [] (events carrier keep replacement same) = some [] :=
  replay_closed carrier keep replacement same

private def checkFullFixture {inputs outputs fields : Nat}
    (carrier : WireCarrier inputs outputs fields) (keep : Fin fields → Bool)
    (replacement : WireCarrier inputs outputs fields)
    (same : WireQuotientLift.QuotientAgreement carrier keep replacement)
    (valuation : Valuation inputs) : IO Unit := do
  let actual := expanded carrier keep replacement
  for output in allFin outputs do
    if actual.implementation.candidate.semantics valuation output !=
        carrier.implementation.candidate.semantics valuation output then
      throw (IO.userError "a full ordinary output changed")
  for field in allFin fields do
    if actual.fieldValue valuation field != carrier.fieldValue valuation field then
      throw (IO.userError "an ordered full computational field changed")
    if forgotten : keep field = false then
      let creation := WireObligationRestoration.createR5 carrier keep field forgotten
      let witness := discharge carrier keep replacement same creation
      if witness.isR6 != (representative carrier keep field).isSome then
        throw (IO.userError "the discharge kind disagrees with the computed visible match")
      if witness.actualSource.eval valuation
          (actual.implementation.candidate.program.eval valuation) !=
            carrier.fieldValue valuation field then
        throw (IO.userError "a discharge witness used the wrong actual full source")
  let transcript := events carrier keep replacement same
  if replay [] transcript != some [] ||
      createdCoordinates transcript != WireObligationRestoration.forgottenCoordinates keep ||
      dischargedCoordinates transcript != WireObligationRestoration.forgottenCoordinates keep then
    throw (IO.userError "the mixed ledger did not close exactly the forgotten coordinates")

-- Bounded executions supplement the kernel-checked general and negative statements.
#eval show IO Unit from do
  let aliasResult := expanded outputAlias dropAll (trueReplacement 1)
  if charge outputAlias dropAll != 0 || aliasResult.implementation.gateCount != 0 ||
      !(checkedGain outputAlias dropAll (trueReplacement 1) outputAgreement).isSome then
    throw (IO.userError "an actually retained identical wire incurred a duplicate materializer")
  if (representative outputAlias dropAll 0).map (fun alias => alias.observation.val) != some 0 ||
      (representative keptAlias keepFirst 1).map (fun alias => alias.observation.val) != some 1 then
    throw (IO.userError "the canonical retained observation was not used")
  let mixedResult := expanded mixedAliases dropAll (trueReplacement 2)
  if charge mixedAliases dropAll != 1 || mixedResult.implementation.gateCount != 1 ||
      !(checkedGain mixedAliases dropAll (trueReplacement 2) mixedAgreement).isSome then
    throw (IO.userError "the mixed cancellation and restoration did not pay its actual one-gate cost")
  let repeatedResult := expanded repeatedAliases dropAll (trueReplacement 4)
  if charge repeatedAliases dropAll != 1 || repeatedResult.implementation.gateCount != 1 ||
      (allFin 4).map (fun field => (representative repeatedAliases dropAll field).isSome) !=
        [false, true, false, true] then
    throw (IO.userError "reordered aliases lost their order or duplicated physical ownership")
  let keptReplacement := WireObligationRestoration.masked keptAlias keepFirst
  if charge keptAlias keepFirst != 0 ||
      (expanded keptAlias keepFirst keptReplacement).implementation.gateCount != 1 then
    throw (IO.userError "an actual kept field failed to resolve its identical forgotten wire")
  let fieldsReplacement := WireObligationRestoration.projected noRetained dropAll
  if (representative noRetained dropAll 0).isSome ||
      (representative noRetained dropAll 1).isSome ||
      charge noRetained dropAll != 1 ||
      (expanded noRetained dropAll fieldsReplacement).implementation.gateCount != 1 ||
      (checkedGain noRetained dropAll fieldsReplacement
        (WireQuotientLift.referenceAgreement noRetained dropAll)).isSome then
    throw (IO.userError "forgotten wires cancelled each other without a retained representative")
  if (representative paddingCollision dropAll 0).isSome ||
      charge paddingCollision dropAll != 1 ||
      (expanded paddingCollision dropAll unrelatedHidden).implementation.gateCount != 2 ||
      (checkedGain paddingCollision dropAll unrelatedHidden unrelatedAgreement).isSome then
    throw (IO.userError "masked padding or an unrelated gate index fabricated a full cancellation")
  if (checkedGain outputAlias keepAll (WireObligationRestoration.masked outputAlias keepAll)
        (maskedAgreement outputAlias keepAll)).isSome || charge outputAlias keepAll != 0 then
    throw (IO.userError "an unchanged original cost was misreported as a strict gain")
  if charge freeFields freeKeep != 0 || charge empty dropAll != 0 ||
      (checkedGain empty dropAll (WireObligationRestoration.masked empty dropAll)
        (maskedAgreement empty dropAll)).isSome then
    throw (IO.userError "free or empty data fabricated a materializer or strict gain")
  let first := WireObligationRestoration.createR5 mixedAliases dropAll (0 : Fin 2) rfl
  let second := WireObligationRestoration.createR5 mixedAliases dropAll (1 : Fin 2) rfl
  let firstWitness := discharge mixedAliases dropAll (trueReplacement 2) mixedAgreement first
  let secondWitness := discharge mixedAliases dropAll (trueReplacement 2) mixedAgreement second
  if !firstWitness.isR6 || secondWitness.isR6 then
    throw (IO.userError "the mixed ledger did not choose distinct R6 and R8 branches")
  let transcript := events mixedAliases dropAll (trueReplacement 2) mixedAgreement
  if replay [] (transcript ++ transcript) != none then
    throw (IO.userError "a discharged identity was created again later in the transcript")
  let premature : List (Event mixedAliases dropAll (trueReplacement 2)) :=
    [.discharge first firstWitness]
  let wrongCoordinate : List (Event mixedAliases dropAll (trueReplacement 2)) :=
    [.createR5 first, .discharge second secondWitness]
  let duplicatePending : List (Event mixedAliases dropAll (trueReplacement 2)) :=
    [.createR5 first, .createR5 first]
  if replay [] premature != none || replay [] wrongCoordinate != none ||
      replay [] duplicatePending != none || replay [0] transcript != none then
    throw (IO.userError "the replay accepted an invalid ordering or reused identity")
  for value in [false, true] do
    let valuation : Valuation 1 := fun _ => value
    checkFullFixture outputAlias dropAll (trueReplacement 1) outputAgreement valuation
    checkFullFixture mixedAliases dropAll (trueReplacement 2) mixedAgreement valuation
    checkFullFixture repeatedAliases dropAll (trueReplacement 4) repeatedAgreement valuation
    checkFullFixture keptAlias keepFirst keptReplacement
      (maskedAgreement keptAlias keepFirst) valuation
    checkFullFixture noRetained dropAll fieldsReplacement
      (WireQuotientLift.referenceAgreement noRetained dropAll) valuation
    checkFullFixture paddingCollision dropAll unrelatedHidden unrelatedAgreement valuation
    checkFullFixture outputAlias keepAll (WireObligationRestoration.masked outputAlias keepAll)
      (maskedAgreement outputAlias keepAll) valuation
    checkFullFixture freeFields freeKeep (WireObligationRestoration.masked freeFields freeKeep)
      (maskedAgreement freeFields freeKeep) valuation
  checkFullFixture empty dropAll (WireObligationRestoration.masked empty dropAll)
    (maskedAgreement empty dropAll) Fin.elim0
  IO.println "M254_FULL_MODE_WIRE_CANCELLATION_RUNTIME_FIXTURES_GREEN"

end PNP.DirectWire.WireMatchedCancellation.Regression
