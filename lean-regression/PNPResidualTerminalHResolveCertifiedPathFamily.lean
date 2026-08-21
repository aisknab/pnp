import PNP.ResidualTerminalHResolveCertifiedPathFamily

namespace PNP
namespace DirectWire
namespace HResolveCertifiedPathFamilyRegression

def fixtureInput : Fin 1 := ⟨0, by decide⟩

def fixtureProgram : Program 1 1 :=
  .snoc .empty
    { left := .input fixtureInput
      right := .input fixtureInput }

def fixtureWord : DirectWireWord 1 1 1 :=
  ⟨fun _output => .gate (Fin.last 0)⟩

def fixtureCurrent : Implementation 1 1 :=
  ⟨1, Candidate.ofDirectWireWord fixtureProgram fixtureWord⟩

def fixturePath (shape : TerminalHNShape) (support frontier : List Nat)
    (residualRank frontierDeviation directWireCode : Nat) :
    TerminalHNBWLCertifiedPath fixtureCurrent Nat Nat frontier :=
  { shape := shape
    support := support
    blocks := [support]
    blocksNonempty := by simp
    blocksCover := by simp
    frontier := frontier
    implementation := fixtureCurrent
    semanticFaithful := Equivalent.refl fixtureCurrent.candidate.program
      fixtureCurrent.candidate.directWireWord
    frontierFaithful := rfl
    residualRank := residualRank
    frontierDeviation := frontierDeviation
    directWireCode := directWireCode }

def selectedAPoorPath :
    TerminalHNBWLCertifiedPath fixtureCurrent Nat Nat [10] :=
  fixturePath .tripod [20] [10] 1 0 0

def selectedAMinimumPath :
    TerminalHNBWLCertifiedPath fixtureCurrent Nat Nat [10] :=
  fixturePath .pair [20] [10] 0 0 0

def selectedBMinimumPath :
    TerminalHNBWLCertifiedPath fixtureCurrent Nat Nat [11] :=
  fixturePath .spine [21] [11] 0 0 1

def blockedMinimumPath :
    TerminalHNBWLCertifiedPath fixtureCurrent Nat Nat [12] :=
  fixturePath .nonflat [20] [12] 0 1 0

def fixtureFootprint (support frontier origin kernel obligation prefixTail
    charge interface : Nat) :
    TerminalHereditaryFootprint Nat Nat Nat Nat Nat Nat Nat Nat :=
  { support := [support]
    frontier := [frontier]
    origin := [origin]
    kernel := [kernel]
    obligation := [obligation]
    prefixTail := [prefixTail]
    charge := [charge]
    interface := [interface] }

abbrev FixtureCandidate :=
  TerminalHResolveCertifiedPathCandidate fixtureCurrent Nat Nat Nat Nat Nat
    Nat Nat Nat

def selectedAPaths := [selectedAPoorPath, selectedAMinimumPath]
def selectedAGoverned (path :
    TerminalHNBWLCertifiedPath fixtureCurrent Nat Nat [10]) : Prop :=
  path ∈ selectedAPaths

def selectedACandidate : FixtureCandidate :=
  { expectedFrontier := [10]
    footprint := fixtureFootprint 20 10 30 40 50 60 70 80
    paths := selectedAPaths
    pathsNonempty := by simp [selectedAPaths]
    governed := selectedAGoverned
    pathsComplete := by
      intro path governed
      exact governed
    pathFootprintFaithful := by
      intro path member
      simp only [selectedAPaths, List.mem_cons, List.not_mem_nil,
        or_false] at member
      rcases member with rfl | rfl <;> exact ⟨rfl, rfl⟩ }

def selectedBPaths := [selectedBMinimumPath]
def selectedBGoverned (path :
    TerminalHNBWLCertifiedPath fixtureCurrent Nat Nat [11]) : Prop :=
  path ∈ selectedBPaths

def selectedBCandidate : FixtureCandidate :=
  { expectedFrontier := [11]
    footprint := fixtureFootprint 21 11 31 41 51 61 71 81
    paths := selectedBPaths
    pathsNonempty := by simp [selectedBPaths]
    governed := selectedBGoverned
    pathsComplete := by
      intro path governed
      exact governed
    pathFootprintFaithful := by
      intro path member
      simp only [selectedBPaths, List.mem_singleton] at member
      cases member
      exact ⟨rfl, rfl⟩ }

def blockedPaths := [blockedMinimumPath]
def blockedGoverned (path :
    TerminalHNBWLCertifiedPath fixtureCurrent Nat Nat [12]) : Prop :=
  path ∈ blockedPaths

def blockedCandidate : FixtureCandidate :=
  { expectedFrontier := [12]
    footprint := fixtureFootprint 20 12 32 42 52 62 72 82
    paths := blockedPaths
    pathsNonempty := by simp [blockedPaths]
    governed := blockedGoverned
    pathsComplete := by
      intro path governed
      exact governed
    pathFootprintFaithful := by
      intro path member
      simp only [blockedPaths, List.mem_singleton] at member
      cases member
      exact ⟨rfl, rfl⟩ }

def fixtureFamily : List FixtureCandidate :=
  [blockedCandidate, selectedACandidate, selectedBCandidate]

theorem blockedCandidate_ne_selectedACandidate :
    blockedCandidate ≠ selectedACandidate := by
  intro equal
  have frontierEqual := congrArg
    (fun candidate : FixtureCandidate => candidate.expectedFrontier) equal
  change ([12] : List Nat) = [10] at frontierEqual
  cases frontierEqual

theorem blockedCandidate_ne_selectedBCandidate :
    blockedCandidate ≠ selectedBCandidate := by
  intro equal
  have frontierEqual := congrArg
    (fun candidate : FixtureCandidate => candidate.expectedFrontier) equal
  change ([12] : List Nat) = [11] at frontierEqual
  cases frontierEqual

theorem selectedACandidate_ne_selectedBCandidate :
    selectedACandidate ≠ selectedBCandidate := by
  intro equal
  have frontierEqual := congrArg
    (fun candidate : FixtureCandidate => candidate.expectedFrontier) equal
  change ([10] : List Nat) = [11] at frontierEqual
  cases frontierEqual

theorem fixtureFamily_nodup : fixtureFamily.Nodup := by
  simp [fixtureFamily, blockedCandidate_ne_selectedACandidate,
    blockedCandidate_ne_selectedBCandidate,
    selectedACandidate_ne_selectedBCandidate]

example : selectedACandidate.minimum? = some selectedAMinimumPath := rfl

example : selectedACandidate.checkHDisjoint selectedBCandidate = true := rfl

example : selectedACandidate.HDisjoint selectedBCandidate :=
  (selectedACandidate.checkHDisjoint_eq_true_iff selectedBCandidate).mp rfl

example : blockedCandidate.firstInterference? selectedACandidate =
    some .support := rfl

example : terminalHResolveGreedyCertifiedPathFamily fixtureFamily =
    [selectedACandidate, selectedBCandidate] := rfl

example : selectedAMinimumPath.support =
    selectedACandidate.footprint.support := rfl

example : selectedAMinimumPath.frontier =
    selectedACandidate.footprint.frontier := rfl

example :
    let selected := terminalHResolveGreedyCertifiedPathFamily fixtureFamily
    selected.Nodup ∧
      (∀ candidate, candidate ∈ selected → candidate ∈ fixtureFamily) ∧
      selected.Pairwise TerminalHResolveCertifiedPathCandidate.HDisjoint ∧
      (∀ candidate, candidate ∈ fixtureFamily →
        candidate ∈ selected ∨
          ∃ blocker, blocker ∈ selected ∧
            ∃ route, candidate.firstInterference? blocker = some route) ∧
      (∀ candidate, candidate ∈ selected →
        ∃ chosen,
          candidate.minimum? = some chosen ∧
          chosen ∈ candidate.paths ∧
          (∀ alternative, candidate.governed alternative →
            chosen.objective.LexLE alternative.objective) ∧
          Equivalent chosen.implementation.candidate.program
            chosen.implementation.candidate.directWireWord
            fixtureCurrent.candidate.program
            fixtureCurrent.candidate.directWireWord ∧
          chosen.frontier = candidate.expectedFrontier ∧
          chosen.blocks ≠ [] ∧
          chosen.blocks.flatten = chosen.support ∧
          chosen.support = candidate.footprint.support ∧
          chosen.frontier = candidate.footprint.frontier ∧
          (chosen.shape = .pair ∨ chosen.shape = .tripod ∨
            chosen.shape = .spine ∨ chosen.shape = .nonflat)) :=
  terminal_hresolve_certified_path_family_complete fixtureFamily
    fixtureFamily_nodup

end HResolveCertifiedPathFamilyRegression
end DirectWire
end PNP
