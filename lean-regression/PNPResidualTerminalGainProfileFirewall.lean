import PNP.ResidualTerminalGainProfileFirewall

namespace PNP.DirectWire

-- Apply the exact public interface at arbitrary dimensions.
example
    {inputs outputs profileWidth : Nat}
    (system : TerminalProfileSystem inputs outputs profileWidth)
    (current replacement : Implementation inputs outputs) :
    firstTerminalGainProfileMismatch system current replacement = none ↔
      ∀ coordinate, system.observe replacement coordinate =
        system.observe current coordinate :=
  firstTerminalGainProfileMismatch_eq_none_iff system current replacement

-- Apply the exact public interface at arbitrary dimensions.
example
    {inputs outputs profileWidth : Nat}
    (system : TerminalProfileSystem inputs outputs profileWidth)
    (current replacement : Implementation inputs outputs)
    (coordinate : Fin profileWidth)
    (foundAt : firstTerminalGainProfileMismatch system current replacement =
      some coordinate) :
    system.observe replacement coordinate ≠ system.observe current coordinate ∧
      ∃ before after : List (Fin profileWidth),
        allFin profileWidth = before ++ coordinate :: after ∧
        ∀ earlier, earlier ∈ before →
          system.observe replacement earlier = system.observe current earlier :=
  firstTerminalGainProfileMismatch_spec system current replacement coordinate foundAt

-- Apply the exact public interface at arbitrary dimensions.
example
    {inputs outputs profileWidth : Nat}
    {system : TerminalProfileSystem inputs outputs profileWidth}
    {current : Implementation inputs outputs}
    (full : TerminalFullCarrierRealization system current) :
    terminalFullProfileMinimum system full.realization.implementation =
      terminalFullProfileMinimum system current :=
  terminalFullProfileMinimum_eq_of_fullRealization full

-- Apply the exact public interface at arbitrary dimensions.
example
    {inputs gates outputs profileWidth : Nat}
    (candidate : Candidate inputs gates outputs)
    (model : TerminalCandidateSaturationModel
      (profileWidth := profileWidth) candidate) :
    (classifyTerminalCandidateGainProfile candidate model).tag = .accepted ↔
      ∃ replacement : Implementation inputs outputs,
        findTerminalCandidatePhysicalGain candidate model = some replacement ∧
        ∀ coordinate, model.profileSystem.observe replacement coordinate =
          model.profileSystem.observe candidate.toImplementation coordinate :=
  classifyTerminalCandidateGainProfile_accepted_iff candidate model

-- Apply the exact public interface at arbitrary dimensions.
example
    {inputs gates outputs profileWidth : Nat}
    (candidate : Candidate inputs gates outputs)
    (model : TerminalCandidateSaturationModel
      (profileWidth := profileWidth) candidate) :
    (classifyTerminalCandidateGainProfile candidate model).tag = .noPhysicalGain ↔
      findTerminalCandidatePhysicalGain candidate model = none :=
  classifyTerminalCandidateGainProfile_noGain_iff candidate model

-- Apply the exact public interface at arbitrary dimensions.
example
    {inputs gates outputs profileWidth : Nat}
    (candidate : Candidate inputs gates outputs)
    (model : TerminalCandidateSaturationModel
      (profileWidth := profileWidth) candidate) :
    (classifyTerminalCandidateGainProfile candidate model).tag = .profileMismatch ↔
      ∃ (replacement : Implementation inputs outputs) (coordinate : Fin profileWidth),
        findTerminalCandidatePhysicalGain candidate model = some replacement ∧
        firstTerminalGainProfileMismatch model.profileSystem
          candidate.toImplementation replacement = some coordinate :=
  classifyTerminalCandidateGainProfile_mismatch_iff candidate model

-- Apply the exact public interface at arbitrary dimensions.
example
    {inputs gates outputs profileWidth : Nat}
    {candidate : Candidate inputs gates outputs}
    {model : TerminalCandidateSaturationModel
      (profileWidth := profileWidth) candidate}
    (gain : TerminalCandidateFullProfileGain candidate model) :
    ∃ found : TerminalCandidateProperPositiveSupport candidate model,
      findTerminalCandidateProperPositiveSupport candidate model = some found ∧
      (gain.implementation.gateCount -
          terminalFullProfileMinimum model.profileSystem gain.implementation) +
          terminalSupportLocalGain candidate
            (terminalCandidateSaturationSystem candidate model) found.seed =
        gates - terminalFullProfileMinimum model.profileSystem candidate.toImplementation ∧
      gain.implementation.gateCount -
          terminalFullProfileMinimum model.profileSystem gain.implementation <
        gates - terminalFullProfileMinimum model.profileSystem candidate.toImplementation :=
  TerminalCandidateFullProfileGain.fullSlack_gain gain

#print axioms PNP.DirectWire.firstTerminalGainProfileMismatch_eq_none_iff
#print axioms PNP.DirectWire.firstTerminalGainProfileMismatch_spec
#print axioms PNP.DirectWire.terminalFullProfileMinimum_eq_of_fullRealization
#print axioms PNP.DirectWire.classifyTerminalCandidateGainProfile_accepted_iff
#print axioms PNP.DirectWire.classifyTerminalCandidateGainProfile_noGain_iff
#print axioms PNP.DirectWire.classifyTerminalCandidateGainProfile_mismatch_iff
#print axioms PNP.DirectWire.TerminalCandidateFullProfileGain.fullSlack_gain

namespace GainProfileFirewallRegression

def searchProgram : Program 1 2 :=
  .snoc
    (.snoc .empty { left := .constant false, right := .constant false })
    { left := .gate 0, right := .input 0 }

def searchCandidate : Candidate 1 2 1 :=
  Candidate.ofDirectWireWord searchProgram ⟨fun _ => .gate 1⟩

def semanticModel : TerminalCandidateSaturationModel
    (profileWidth := 1) searchCandidate :=
  { profileSystem :=
      { role := fun _ => .carrier
        observe := fun implementation _ =>
          implementation.candidate.semantics (fun _ => false) 0 }
    projection := { keep := fun _ => false }
    observe := fun _ _ => false }

def mismatchModel : TerminalCandidateSaturationModel
    (profileWidth := 3) searchCandidate :=
  { profileSystem :=
      { role := fun coordinate => if coordinate.val = 0 then .obligation else .origin
        observe := fun implementation coordinate =>
          if coordinate.val = 1 then decide (2 ≤ implementation.gateCount) else false }
    projection := { keep := fun coordinate => decide (coordinate.val = 0) }
    observe := fun _ _ => false }

def zeroProfileModel {inputs gates outputs : Nat}
    (candidate : Candidate inputs gates outputs) :
    TerminalCandidateSaturationModel (profileWidth := 0) candidate :=
  { profileSystem := { role := Fin.elim0, observe := fun _ => Fin.elim0 }
    projection := { keep := Fin.elim0 }
    observe := fun _ => Fin.elim0 }

def zeroCandidate : Candidate 0 0 0 :=
  Candidate.ofDirectWireWord .empty ⟨Fin.elim0⟩

-- Read each complete computation once into its observable data summary.
def outcomeSummary {inputs gates outputs profileWidth : Nat}
    {candidate : Candidate inputs gates outputs}
    {model : TerminalCandidateSaturationModel
      (profileWidth := profileWidth) candidate} :
    TerminalCandidateGainProfileOutcome candidate model →
      TerminalGainProfileTag × Option Nat × Option Nat
  | .noPhysicalGain _ => (.noPhysicalGain, none, none)
  | .profileMismatch replacement _ coordinate _ =>
      (.profileMismatch, some replacement.gateCount, some coordinate.val)
  | .accepted gain => (.accepted, some gain.implementation.gateCount, none)

-- This observer is not constant over implementations: it reads an actual output.
def wireCandidate : Candidate 1 0 1 :=
  Candidate.ofDirectWireWord .empty ⟨fun _ => .input 0⟩

example :
    semanticModel.profileSystem.observe searchCandidate.toImplementation 0 = true ∧
    semanticModel.profileSystem.observe wireCandidate.toImplementation 0 = false := by decide

-- Execute the same complete semantic-observer case through Lean's runtime.
-- The arbitrary-dimension proofs above remain kernel checked. This assertion
-- tests program execution; it is not a theorem or a native-decide proof shortcut.
#eval do
  let actual := outcomeSummary
    (classifyTerminalCandidateGainProfile searchCandidate semanticModel)
  if actual == (TerminalGainProfileTag.accepted, some 1, none) then
    IO.println "m239-semantic-observer-acceptance-execution-ok"
  else
    throw (IO.userError "M239 semantic-observer acceptance regression failed")

-- The first coordinate agrees; the second changes under the actual physical gain.
-- A quotient that forgets the second coordinate must not authorize full-mode use.
example :
    outcomeSummary (classifyTerminalCandidateGainProfile searchCandidate mismatchModel) =
      (.profileMismatch, some 1, some 1) := by decide

example : mismatchModel.projection.keep 1 = false := by decide

-- A zero-width full profile has no mismatching coordinate.
example :
    outcomeSummary (classifyTerminalCandidateGainProfile searchCandidate
      (zeroProfileModel searchCandidate)) = (.accepted, some 1, none) := by decide

-- Empty dimensions follow the actual no-gain branch.
example :
    outcomeSummary (classifyTerminalCandidateGainProfile zeroCandidate
      (zeroProfileModel zeroCandidate)) = (.noPhysicalGain, none, none) := by decide

-- A profile-preserving realization transports existing discharge; it does not
-- discharge an obligation that was already open.
example {inputs gates outputs profileWidth : Nat}
    {candidate : Candidate inputs gates outputs}
    {model : TerminalCandidateSaturationModel
      (profileWidth := profileWidth) candidate}
    (gain : TerminalCandidateFullProfileGain candidate model)
    (discharged : model.profileSystem.ObligationsDischarged candidate.toImplementation) :
    model.profileSystem.ObligationsDischarged gain.implementation :=
  gain.fullRealization.obligationsDischarged discharged

def openObligationSystem : TerminalProfileSystem 1 1 1 :=
  { role := fun _ => .obligation
    observe := fun _ _ => true }

example : ¬ openObligationSystem.ObligationsDischarged searchCandidate.toImplementation := by
  intro discharged
  have impossible := discharged 0 rfl
  cases impossible

end GainProfileFirewallRegression

end PNP.DirectWire
