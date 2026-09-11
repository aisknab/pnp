import PNP.ResidualTerminalPhysicalGain

namespace PNP.DirectWire

-- Apply the exact public contract at arbitrary dimensions.
example
    {inputs gates outputs profileWidth : Nat}
    (candidate : Candidate inputs gates outputs)
    (model : TerminalCandidateSaturationModel
      (profileWidth := profileWidth) candidate)
    (seed : List (TerminalPrimitiveRecord inputs gates outputs profileWidth)) :
    let replacement := terminalCandidateSaturatePhysicalMinimumReplacement
      candidate model seed
    Equivalent replacement.candidate.program replacement.candidate.directWireWord
      candidate.program candidate.directWireWord :=
  terminalCandidateSaturatePhysicalMinimumReplacement_equivalent candidate model seed

-- Apply the exact public contract at arbitrary dimensions.
example
    {inputs gates outputs profileWidth : Nat}
    (candidate : Candidate inputs gates outputs)
    (model : TerminalCandidateSaturationModel
      (profileWidth := profileWidth) candidate)
    (seed : List (TerminalPrimitiveRecord inputs gates outputs profileWidth)) :
    (terminalCandidateSaturatePhysicalMinimumReplacement candidate model seed).gateCount +
      terminalSupportLocalGain candidate
        (terminalCandidateSaturationSystem candidate model) seed = gates :=
  terminalCandidateSaturatePhysicalMinimumReplacement_size_gain candidate model seed

-- Apply the exact public contract at arbitrary dimensions.
example
    {inputs gates outputs profileWidth : Nat}
    (candidate : Candidate inputs gates outputs)
    (model : TerminalCandidateSaturationModel
      (profileWidth := profileWidth) candidate)
    (seed : List (TerminalPrimitiveRecord inputs gates outputs profileWidth)) :
    residualSlack (terminalCandidateSaturatePhysicalMinimumReplacement candidate model seed) +
      terminalSupportLocalGain candidate
        (terminalCandidateSaturationSystem candidate model) seed =
      residualSlack candidate.toImplementation :=
  terminalCandidateSaturatePhysicalMinimumReplacement_slack_gain candidate model seed

-- Apply the exact public contract at arbitrary dimensions.
example
    {inputs gates outputs profileWidth : Nat}
    (candidate : Candidate inputs gates outputs)
    (model : TerminalCandidateSaturationModel
      (profileWidth := profileWidth) candidate)
    (result : Implementation inputs outputs)
    (foundAt : findTerminalCandidatePhysicalGain candidate model = some result) :
    ∃ found : TerminalCandidateProperPositiveSupport candidate model,
      findTerminalCandidateProperPositiveSupport candidate model = some found ∧
      found.seed ∈ allTerminalSupportSeeds inputs gates outputs profileWidth ∧
      TerminalSupportProper candidate
        (terminalCandidateSaturationSystem candidate model) found.seed ∧
      0 < terminalSupportLocalGain candidate
        (terminalCandidateSaturationSystem candidate model) found.seed ∧
      result = terminalCandidateSaturatePhysicalMinimumReplacement
        candidate model found.seed ∧
      Equivalent result.candidate.program result.candidate.directWireWord
        candidate.program candidate.directWireWord ∧
      result.gateCount + terminalSupportLocalGain candidate
        (terminalCandidateSaturationSystem candidate model) found.seed = gates ∧
      residualSlack result + terminalSupportLocalGain candidate
        (terminalCandidateSaturationSystem candidate model) found.seed =
          residualSlack candidate.toImplementation ∧
      result.gateCount < gates ∧
      residualSlack result < residualSlack candidate.toImplementation :=
  findTerminalCandidatePhysicalGain_sound candidate model result foundAt

-- Apply the exact public contract at arbitrary dimensions.
example
    {inputs gates outputs profileWidth : Nat}
    (candidate : Candidate inputs gates outputs)
    (model : TerminalCandidateSaturationModel
      (profileWidth := profileWidth) candidate) :
    findTerminalCandidatePhysicalGain candidate model = none ↔
      ∀ seed, seed ∈ allTerminalSupportSeeds inputs gates outputs profileWidth →
        ¬(TerminalSupportProper candidate
            (terminalCandidateSaturationSystem candidate model) seed ∧
          TerminalSupportPositive candidate
            (terminalCandidateSaturationSystem candidate model) seed) :=
  findTerminalCandidatePhysicalGain_eq_none_iff candidate model

#print axioms terminalCandidateSaturatePhysicalMinimumReplacement_equivalent
#print axioms terminalCandidateSaturatePhysicalMinimumReplacement_size_gain
#print axioms terminalCandidateSaturatePhysicalMinimumReplacement_slack_gain
#print axioms findTerminalCandidatePhysicalGain_sound
#print axioms findTerminalCandidatePhysicalGain_eq_none_iff

namespace PhysicalGainRegression

def zeroProfileModel {inputs gates outputs : Nat}
    (candidate : Candidate inputs gates outputs) :
    TerminalCandidateSaturationModel (profileWidth := 0) candidate :=
  { profileSystem := { role := Fin.elim0, observe := fun _ => Fin.elim0 }
    projection := { keep := Fin.elim0 }
    observe := fun _ => Fin.elim0 }

-- The first two gates compute the identity. Their proper saturated support
-- can be replaced by a wire while preserving the final negation and bypass.
def gainProgram : Program 1 3 :=
  .snoc
    (.snoc
      (.snoc .empty { left := .input 0, right := .input 0 })
      { left := .gate 0, right := .gate 0 })
    { left := .gate 1, right := .gate 1 }

def gainCandidate : Candidate 1 3 3 :=
  Candidate.ofDirectWireWord gainProgram ⟨fun output =>
    if output.val = 2 then .input 0 else .gate 2⟩

def gainModel := zeroProfileModel gainCandidate
abbrev GainRecord := TerminalPrimitiveRecord 1 3 3 0
def gainSeed : List GainRecord := [.gate 1]
def gainSystem := terminalCandidateSaturationSystem gainCandidate gainModel
def gainSupport := extractSaturatedTerminalSupport gainCandidate gainSystem gainSeed
def gainReplacement :=
  terminalCandidateSaturatePhysicalMinimumReplacement gainCandidate gainModel gainSeed

example : gainSupport.selectedGates = [0, 1] := by decide
example : gainSupport.boundary = [.input 0] := by decide
example : gainSupport.interface = [1] := by decide
example : terminalSupportLocalGain gainCandidate gainSystem gainSeed = 2 := by decide
example : gainReplacement.gateCount = 1 := by decide
example : equivalentBool gainReplacement.candidate gainCandidate = true := by decide
example : residualSlack gainCandidate.toImplementation = 2 := by decide
example : residualSlack gainReplacement = 0 := by decide

-- Use a smaller physical universe for the exhaustive complete search. The
-- richer fixture above separately covers repeated outputs and input bypasses.
-- Its first constant gate has a genuine proper unit gain.
def searchProgram : Program 1 2 :=
  .snoc
    (.snoc .empty { left := .constant false, right := .constant false })
    { left := .gate 0, right := .input 0 }

def searchCandidate : Candidate 1 2 1 :=
  Candidate.ofDirectWireWord searchProgram ⟨fun _ => .gate 1⟩

def searchModel := zeroProfileModel searchCandidate

-- Exercise the complete seed-search/minimum/context pipeline, not a supplied
-- support result or supplied whole-circuit correctness certificate.
example :
    (findTerminalCandidatePhysicalGain searchCandidate searchModel).map
      (fun result => result.gateCount) = some 1 := by decide

-- Duplicated seeds do not create extra physical gain or duplicate gates.
example :
    (terminalCandidateSaturatePhysicalMinimumReplacement gainCandidate gainModel
      ([.gate 1, .gate 1] : List GainRecord)).gateCount = 1 := by decide

-- A double negation has whole-circuit slack two, but every proper nonempty
-- saturated support is the single irreducible first negation.
-- Thus failure of the proper-support search does not imply global minimality.
def doubleProgram : Program 1 2 :=
  .snoc
    (.snoc .empty { left := .input 0, right := .input 0 })
    { left := .gate 0, right := .gate 0 }

def doubleCandidate : Candidate 1 2 1 :=
  Candidate.ofDirectWireWord doubleProgram ⟨fun _ => .gate 1⟩

def doubleModel := zeroProfileModel doubleCandidate

example : residualSlack doubleCandidate.toImplementation = 2 := by decide
example :
    (findTerminalCandidatePhysicalGain doubleCandidate doubleModel).isSome =
      false := by decide

-- Empty supports do not shrink a nonempty candidate or invent positive gain.
example :
    (terminalCandidateSaturatePhysicalMinimumReplacement gainCandidate gainModel
      ([] : List GainRecord)).gateCount = 3 := by decide

def zeroCandidate : Candidate 0 0 0 :=
  Candidate.ofDirectWireWord .empty ⟨Fin.elim0⟩

def zeroModel := zeroProfileModel zeroCandidate

example :
    (findTerminalCandidatePhysicalGain zeroCandidate zeroModel).isSome = false := by decide
example :
    (terminalCandidateSaturatePhysicalMinimumReplacement zeroCandidate zeroModel []).gateCount =
      0 := by decide

def wireCandidate : Candidate 1 0 2 :=
  Candidate.ofDirectWireWord .empty ⟨fun output =>
    if output.val = 0 then .input 0 else .constant false⟩

def wireModel := zeroProfileModel wireCandidate

example :
    (findTerminalCandidatePhysicalGain wireCandidate wireModel).isSome = false := by decide

end PhysicalGainRegression
end PNP.DirectWire
