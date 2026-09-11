/-
Unbounded retained-profile locality interfaces. Finite fixtures supplement,
but do not replace, these arbitrary-dimension theorem applications.
-/
import PNP.ResidualTerminalProfileLocality

open PNP PNP.DirectWire

section
variable {inputs gates outputs profileWidth : Nat}
variable (candidate : Candidate inputs gates outputs)
variable (model : TerminalCandidateSaturationModel
  (profileWidth := profileWidth) candidate)
variable (left right seed : List
  (TerminalPrimitiveRecord inputs gates outputs profileWidth))
variable (coordinate : Fin profileWidth)

example (selectedEqual : terminalGateSelected left = terminalGateSelected right) :
    { extractTerminalSupport candidate left with records := right } =
      extractTerminalSupport candidate right :=
  extractTerminalSupport_eq_of_gateSelected_eq candidate left right selectedEqual

example (selectedEqual : terminalGateSelected left = terminalGateSelected right) :
    terminalAmbientSupportImplementation candidate left =
      terminalAmbientSupportImplementation candidate right :=
  terminalAmbientSupportImplementation_eq_of_gateSelected_eq
    candidate left right selectedEqual

example (leftGates rightGates : List (Fin gates))
    (sameGates : ∀ gate, gate ∈ leftGates ↔ gate ∈ rightGates) :
    terminalCandidateProfileObservation candidate model leftGates coordinate =
      terminalCandidateProfileObservation candidate model rightGates coordinate :=
  terminalCandidateProfileObservation_eq_of_gateMembership_iff
    candidate model leftGates rightGates coordinate sameGates

example
    (profileMember : TerminalPrimitiveRecord.profile coordinate ∈
      terminalSaturateRecords
        (terminalCandidateSaturationSystem candidate model) seed)
    (recordAgreement : ∀ gate,
      TerminalPrimitiveRecord.gate gate ∈
        terminalSaturateRecords
          (terminalCandidateSaturationSystem candidate model) seed →
      (TerminalPrimitiveRecord.gate gate ∈ left ↔
        TerminalPrimitiveRecord.gate gate ∈ right)) :
    model.observe (terminalAmbientSupportImplementation candidate left) coordinate =
      model.observe (terminalAmbientSupportImplementation candidate right) coordinate :=
  terminalCandidateSaturate_profile_locality
    candidate model seed left right coordinate profileMember recordAgreement

example
    (profileMember : TerminalPrimitiveRecord.profile coordinate ∈
      terminalSaturateRecords
        (terminalCandidateSaturationSystem candidate model) seed) :
    model.observe
        (terminalAmbientSupportImplementation candidate
          (terminalSaturateRecords
            (terminalCandidateSaturationSystem candidate model) seed)) coordinate =
      model.observe
        (terminalAmbientSupportImplementation candidate
          (allTerminalPrimitiveRecords inputs gates outputs profileWidth)) coordinate :=
  terminalCandidateSaturate_profile_preserved
    candidate model seed coordinate profileMember

end

namespace TerminalProfileLocalityRegression

def first : Fin 2 := ⟨0, by decide⟩
def second : Fin 2 := ⟨1, by decide⟩
def coordinate : Fin 1 := ⟨0, by decide⟩

/-- The first gate is true; the second is an independent, unobserved gate. -/
def program : Program 0 2 :=
  .snoc (.snoc .empty { left := .constant false, right := .constant false })
    { left := .constant true, right := .constant true }

def candidate : Candidate 0 2 1 :=
  Candidate.ofDirectWireWord program ⟨fun _ => .gate first⟩

/-- Read the actual first ambient gate output, not a constant profile. -/
def outputModel :
    TerminalCandidateSaturationModel (profileWidth := 1) candidate :=
  { profileSystem := { role := fun _ => .origin, observe := fun _ _ => false }
    projection := { keep := fun _ => false }
    observe := fun implementation _ =>
      implementation.candidate.semantics (fun _ => false) first }

def profileSeed : List (TerminalPrimitiveRecord 0 2 1 1) := [.profile coordinate]

def saturated : List (TerminalPrimitiveRecord 0 2 1 1) :=
  terminalSaturateRecords (terminalCandidateSaturationSystem candidate outputModel) profileSeed

def completeRecords : List (TerminalPrimitiveRecord 0 2 1 1) :=
  allTerminalPrimitiveRecords 0 2 1 1

example : terminalCandidateProfileObservation candidate outputModel [] coordinate = false := by
  decide

example : terminalCandidateProfileObservation candidate outputModel [first] coordinate = true := by
  decide

example : terminalGateInfluencesProfile candidate outputModel first coordinate = true ∧
    terminalGateInfluencesProfile candidate outputModel second coordinate = false := by
  decide

example : TerminalPrimitiveRecord.profile coordinate ∈ saturated ∧
    TerminalPrimitiveRecord.gate first ∈ saturated ∧
    TerminalPrimitiveRecord.gate second ∉ saturated := by
  decide

example :
    outputModel.observe (terminalAmbientSupportImplementation candidate saturated) coordinate =
      outputModel.observe (terminalAmbientSupportImplementation candidate completeRecords)
        coordinate :=
  terminalCandidateSaturate_profile_preserved candidate outputModel
    profileSeed coordinate (by decide)

example :
    outputModel.observe (terminalAmbientSupportImplementation candidate saturated) coordinate =
      true := by
  decide

def reorderedRecords : List (TerminalPrimitiveRecord 0 2 1 1) :=
  [.profile coordinate, .gate second, .gate first, .gate first, .interface coordinate]

example :
    terminalAmbientSupportImplementation candidate reorderedRecords =
      terminalAmbientSupportImplementation (profileWidth := 1) candidate [.gate first, .gate second] := by
  apply terminalAmbientSupportImplementation_eq_of_gateSelected_eq candidate
  funext gate
  exact (by decide : ∀ gate : Fin 2, terminalGateSelected reorderedRecords gate =
    terminalGateSelected ([.gate first, .gate second] :
      List (TerminalPrimitiveRecord 0 2 1 1)) gate) gate

/-- Locality also removes the genuinely omitted second gate and ignores metadata. -/
example :
    outputModel.observe
        (terminalAmbientSupportImplementation candidate [.gate first, .profile coordinate])
        coordinate =
      outputModel.observe (terminalAmbientSupportImplementation candidate reorderedRecords)
        coordinate :=
  terminalCandidateSaturate_profile_locality candidate outputModel profileSeed
    [.gate first, .profile coordinate] reorderedRecords coordinate (by decide) (by decide)

example :
    terminalCandidateProfileObservation candidate outputModel [second, first, first] coordinate =
      terminalCandidateProfileObservation candidate outputModel [first, second] coordinate :=
  terminalCandidateProfileObservation_eq_of_gateMembership_iff candidate outputModel
    [second, first, first] [first, second] coordinate (by decide)

/-- Empty closure retains no profile, and its false output differs from the
    complete support's true output. The retained-profile premise is necessary. -/
example :
    TerminalPrimitiveRecord.profile coordinate ∉
      terminalSaturateRecords (terminalCandidateSaturationSystem candidate outputModel) [] ∧
    outputModel.observe
        (terminalAmbientSupportImplementation candidate
          (terminalSaturateRecords (terminalCandidateSaturationSystem candidate outputModel) []))
        coordinate ≠
      outputModel.observe (terminalAmbientSupportImplementation candidate completeRecords)
        coordinate := by
  decide

example : ¬ (∀ seed : List (TerminalPrimitiveRecord 0 2 1 1),
    outputModel.observe
        (terminalAmbientSupportImplementation candidate
          (terminalSaturateRecords (terminalCandidateSaturationSystem candidate outputModel) seed))
        coordinate =
      outputModel.observe (terminalAmbientSupportImplementation candidate completeRecords)
        coordinate) := by
  intro unconditional
  have counterexample :
      outputModel.observe
          (terminalAmbientSupportImplementation candidate
            (terminalSaturateRecords (terminalCandidateSaturationSystem candidate outputModel) []))
          coordinate ≠
        outputModel.observe (terminalAmbientSupportImplementation candidate completeRecords)
          coordinate := by decide
  exact counterexample (unconditional [])

/-- Interaction sensitivity from M232 remains within the new theorem's scope. -/
def interactionModel :
    TerminalCandidateSaturationModel (profileWidth := 1) candidate :=
  { profileSystem := { role := fun _ => .origin, observe := fun _ _ => false }
    projection := { keep := fun _ => false }
    observe := fun implementation _ => decide (2 ≤ implementation.gateCount) }

example :
    terminalCandidateProfileObservation candidate interactionModel [first] coordinate =
      terminalCandidateProfileObservation candidate interactionModel [] coordinate ∧
    terminalCandidateProfileObservation candidate interactionModel [first, second] coordinate ≠
      terminalCandidateProfileObservation candidate interactionModel [second] coordinate := by
  decide

example :
    interactionModel.observe
        (terminalAmbientSupportImplementation candidate
          (terminalSaturateRecords (terminalCandidateSaturationSystem candidate interactionModel)
            profileSeed)) coordinate =
      interactionModel.observe (terminalAmbientSupportImplementation candidate completeRecords)
        coordinate :=
  terminalCandidateSaturate_profile_preserved candidate interactionModel
    profileSeed coordinate (by decide)

end TerminalProfileLocalityRegression
