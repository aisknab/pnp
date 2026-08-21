import PNP.ResidualTerminalHNBWLCertifiedPathMinimum

namespace PNP
namespace DirectWire
namespace HNBWLCertifiedPathMinimumRegression

def fixtureInput : Fin 1 := ⟨0, by decide⟩
def fixtureFirstGate : Fin 2 := ⟨0, by decide⟩
def fixtureSecondGate : Fin 2 := ⟨1, by decide⟩

def fixtureTwoGateProgram : Program 1 2 :=
  .snoc
    (.snoc .empty
      { left := .input fixtureInput
        right := .input fixtureInput })
    { left := .input fixtureInput
      right := .input fixtureInput }

def fixtureTwoGateWord : DirectWireWord 1 2 1 :=
  ⟨fun _output => .gate fixtureSecondGate⟩

def fixtureCurrent : Implementation 1 1 :=
  ⟨2, Candidate.ofDirectWireWord fixtureTwoGateProgram fixtureTwoGateWord⟩

def fixtureOneGateProgram : Program 1 1 :=
  .snoc .empty
    { left := .input fixtureInput
      right := .input fixtureInput }

def fixtureOneGateWord : DirectWireWord 1 1 1 :=
  ⟨fun _output => .gate (Fin.last 0)⟩

def fixtureMinimum : Implementation 1 1 :=
  ⟨1, Candidate.ofDirectWireWord fixtureOneGateProgram fixtureOneGateWord⟩

theorem fixtureMinimum_semanticFaithful : Equivalent
    fixtureMinimum.candidate.program fixtureMinimum.candidate.directWireWord
    fixtureCurrent.candidate.program fixtureCurrent.candidate.directWireWord :=
  equivalentBool_sound (by decide)

abbrev FixturePath :=
  TerminalHNBWLCertifiedPath fixtureCurrent Nat Nat [10, 11]

def fixturePath (shape : TerminalHNShape)
    (implementation : Implementation 1 1)
    (semanticFaithful : Equivalent
      implementation.candidate.program implementation.candidate.directWireWord
      fixtureCurrent.candidate.program fixtureCurrent.candidate.directWireWord)
    (residualRank frontierDeviation directWireCode : Nat) : FixturePath :=
  { shape := shape
    support := [20, 21]
    blocks := [[20], [21]]
    blocksNonempty := by decide
    blocksCover := rfl
    frontier := [10, 11]
    implementation := implementation
    semanticFaithful := semanticFaithful
    frontierFaithful := rfl
    residualRank := residualRank
    frontierDeviation := frontierDeviation
    directWireCode := directWireCode }

def costPoorPath : FixturePath :=
  fixturePath .nonflat fixtureCurrent
    (Equivalent.refl fixtureCurrent.candidate.program
      fixtureCurrent.candidate.directWireWord)
    0 0 0

def residualRankPoorPath : FixturePath :=
  fixturePath .spine fixtureMinimum fixtureMinimum_semanticFaithful 1 0 0

def frontierDeviationPoorPath : FixturePath :=
  fixturePath .tripod fixtureMinimum fixtureMinimum_semanticFaithful 0 1 0

def directWireCodePoorPath : FixturePath :=
  fixturePath .pair fixtureMinimum fixtureMinimum_semanticFaithful 0 0 1

def exactMinimumPath : FixturePath :=
  fixturePath .pair fixtureMinimum fixtureMinimum_semanticFaithful 0 0 0

def fixturePaths : List FixturePath :=
  [costPoorPath, residualRankPoorPath, frontierDeviationPoorPath,
    directWireCodePoorPath, exactMinimumPath]

example : costPoorPath.objective.cost = 2 := rfl
example : exactMinimumPath.objective.cost = 1 := rfl
example : residualRankPoorPath.shape = .spine := rfl
example : frontierDeviationPoorPath.shape = .tripod := rfl
example : costPoorPath.shape = .nonflat := rfl
example : exactMinimumPath.shape = .pair := rfl

example :
    exactMinimumPath.objective.checkLexLE directWireCodePoorPath.objective =
      true := rfl
example :
    exactMinimumPath.objective.checkLexLE frontierDeviationPoorPath.objective =
      true := rfl
example :
    exactMinimumPath.objective.checkLexLE residualRankPoorPath.objective =
      true := rfl
example :
    exactMinimumPath.objective.checkLexLE costPoorPath.objective = true := rfl

example : terminalHNBWLMinimum? fixturePaths = some exactMinimumPath := rfl

example : exactMinimumPath ∈ fixturePaths := by
  simp [fixturePaths]
example : exactMinimumPath.blocks.flatten = exactMinimumPath.support := rfl
example : exactMinimumPath.frontier = [10, 11] := rfl
example : Equivalent
    exactMinimumPath.implementation.candidate.program
    exactMinimumPath.implementation.candidate.directWireWord
    fixtureCurrent.candidate.program fixtureCurrent.candidate.directWireWord :=
  exactMinimumPath.semanticFaithful

def fixtureGoverned (path : FixturePath) : Prop := path ∈ fixturePaths

example : TerminalHNBWLFamilyComplete fixturePaths fixtureGoverned := by
  intro path governed
  exact governed

example :
    ∃ chosen,
      terminalHNBWLMinimum? fixturePaths = some chosen ∧
      chosen ∈ fixturePaths ∧
      (∀ alternative, fixtureGoverned alternative →
        chosen.objective.LexLE alternative.objective) ∧
      Equivalent chosen.implementation.candidate.program
        chosen.implementation.candidate.directWireWord
        fixtureCurrent.candidate.program fixtureCurrent.candidate.directWireWord ∧
      chosen.frontier = [10, 11] ∧
      chosen.blocks ≠ [] ∧
      chosen.blocks.flatten = chosen.support ∧
      (chosen.shape = .pair ∨ chosen.shape = .tripod ∨
        chosen.shape = .spine ∨ chosen.shape = .nonflat) :=
  terminal_hn_bwl_certified_path_minimum_complete
    fixturePaths fixtureGoverned (by simp [fixturePaths]) (by
      intro path governed
      exact governed)

end HNBWLCertifiedPathMinimumRegression
end DirectWire
end PNP
