/-
General candidate-profile dependency contracts.  Finite fixtures do not replace
these unbounded theorem applications.
-/
import PNP.ResidualTerminalCandidateSaturation

open PNP PNP.DirectWire

section
variable {inputs gates outputs profileWidth : Nat}
variable (candidate : Candidate inputs gates outputs)
variable (model : TerminalCandidateSaturationModel
  (profileWidth := profileWidth) candidate)

example (gate : Fin gates) (coordinate : Fin profileWidth) :
    terminalGateInfluencesProfile candidate model gate coordinate = true ↔
      ∃ context,
        context ∈ terminalListSubsets
          ((allFin gates).filter (fun other => decide (other ≠ gate))) ∧
        terminalCandidateProfileObservation candidate model (gate :: context) coordinate ≠
          terminalCandidateProfileObservation candidate model context coordinate :=
  terminalGateInfluencesProfile_eq_true_iff candidate model gate coordinate

example (kind : TerminalSaturationRuleKind)
    (coordinate : Fin profileWidth) (gate : Fin gates) :
    (terminalCandidateSaturationSystem candidate model).requires kind
        (.profile coordinate) (.gate gate) =
      (decide (kind = terminalSaturationRuleOfProfileRole
        (model.profileSystem.role coordinate)) &&
        terminalGateInfluencesProfile candidate model gate coordinate) :=
  terminalCandidateProfileRequires_eq_influence candidate model kind coordinate gate

example (seed : List (TerminalPrimitiveRecord inputs gates outputs profileWidth))
    (coordinate : Fin profileWidth) (gate : Fin gates) (context : List (Fin gates))
    (profileMember : TerminalPrimitiveRecord.profile coordinate ∈
      terminalSaturateRecords (terminalCandidateSaturationSystem candidate model) seed)
    (gateAbsent : TerminalPrimitiveRecord.gate gate ∉
      terminalSaturateRecords (terminalCandidateSaturationSystem candidate model) seed)
    (canonicalContext : context ∈ terminalListSubsets
      ((allFin gates).filter (fun other => decide (other ≠ gate)))) :
    terminalCandidateProfileObservation candidate model (gate :: context) coordinate =
      terminalCandidateProfileObservation candidate model context coordinate :=
  terminalCandidateSaturate_profile_noninterference candidate model seed coordinate gate
    context profileMember gateAbsent canonicalContext

end

namespace TerminalProfileDependencyRegression

def input : Fin 1 := ⟨0, by decide⟩
def first : Fin 2 := ⟨0, by decide⟩
def second : Fin 2 := ⟨1, by decide⟩
def coordinate : Fin 1 := ⟨0, by decide⟩

def program : Program 1 2 :=
  .snoc (.snoc .empty { left := .input input, right := .input input })
    { left := .input input, right := .input input }

def candidate : Candidate 1 2 2 :=
  Candidate.ofDirectWireWord program ⟨fun output => .gate output⟩

/-- No singleton has two gates, but the two-gate context does. -/
def interactionModel (role : TerminalProfileRole) :
    TerminalCandidateSaturationModel (profileWidth := 1) candidate :=
  { profileSystem := { role := fun _ => role, observe := fun _ _ => false }
    projection := { keep := fun _ => false }
    observe := fun implementation _ => decide (2 ≤ implementation.gateCount) }

def constantModel :
    TerminalCandidateSaturationModel (profileWidth := 1) candidate :=
  { profileSystem := { role := fun _ => .origin, observe := fun _ _ => false }
    projection := { keep := fun _ => false }
    observe := fun _ _ => false }

example : terminalCandidateProfileObservation candidate (interactionModel .origin)
    [first] coordinate =
      terminalCandidateProfileObservation candidate (interactionModel .origin)
        [] coordinate := by decide

example : terminalCandidateProfileObservation candidate (interactionModel .origin)
    [first, second] coordinate ≠
      terminalCandidateProfileObservation candidate (interactionModel .origin)
        [second] coordinate := by decide

example : [second] ∈ terminalListSubsets
    ((allFin 2).filter (fun other => decide (other ≠ first))) := by decide

example : terminalGateInfluencesProfile candidate (interactionModel .origin)
    first coordinate = true := by decide

example :
    ([.carrier, .origin, .kernel, .obligation, .prefix, .direction,
        .saturation, .budget, .charge, .frontier] : List TerminalProfileRole).map
      (fun role =>
        (terminalCandidateSaturationSystem candidate (interactionModel role)).requires
          (terminalSaturationRuleOfProfileRole role) (.profile coordinate) (.gate first)) =
      [true, true, true, true, true, true, true, true, true, true] := by decide

example :
    (terminalCandidateSaturationSystem candidate (interactionModel .origin)).requires
      .budget (.profile coordinate) (.gate first) = false := by decide

def profileSeed : List (TerminalPrimitiveRecord 1 2 2 1) := [.profile coordinate]

example : TerminalPrimitiveRecord.profile coordinate ∈
    terminalSaturateRecords
      (terminalCandidateSaturationSystem candidate constantModel) profileSeed := by decide

example : TerminalPrimitiveRecord.gate first ∉
    terminalSaturateRecords
      (terminalCandidateSaturationSystem candidate constantModel) profileSeed := by decide

example : terminalCandidateProfileObservation candidate constantModel
    [first, second] coordinate =
      terminalCandidateProfileObservation candidate constantModel [second] coordinate :=
  terminalCandidateSaturate_profile_noninterference candidate constantModel
    profileSeed coordinate first [second] (by decide) (by decide) (by decide)

end TerminalProfileDependencyRegression
