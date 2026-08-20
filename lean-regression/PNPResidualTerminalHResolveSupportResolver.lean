import PNP.ResidualTerminalHResolveSupportResolver

namespace PNP
namespace DirectWire
namespace HResolveSupportResolverRegression

abbrev FixtureRecord := TerminalPrimitiveRecord 1 2 1 0

def fixtureInput : Fin 1 := ⟨0, by decide⟩
def fixtureFirstGate : Fin 2 := ⟨0, by decide⟩
def fixtureSecondGate : Fin 2 := ⟨1, by decide⟩

def fixtureProgram : Program 1 2 :=
  .snoc
    (.snoc .empty
      { left := .input fixtureInput
        right := .input fixtureInput })
    { left := .input fixtureInput
      right := .input fixtureInput }

def fixtureWord : DirectWireWord 1 2 1 :=
  ⟨fun _output => .gate fixtureSecondGate⟩

/-- The first gate is deliberately redundant; the second gate alone computes
    the same output. -/
def fixtureCandidate : Candidate 1 2 1 :=
  Candidate.ofDirectWireWord fixtureProgram fixtureWord

def fixtureProfileSystem : TerminalProfileSystem 1 1 0 :=
  { role := fun coordinate => Fin.elim0 coordinate
    observe := fun _implementation coordinate => Fin.elim0 coordinate }

def fixtureProjection : TerminalProfileProjection 0 :=
  { keep := fun coordinate => Fin.elim0 coordinate }

def fixtureModel :
    TerminalCandidateSaturationModel (profileWidth := 0) fixtureCandidate :=
  { profileSystem := fixtureProfileSystem
    projection := fixtureProjection
    observe := fun _implementation coordinate => Fin.elim0 coordinate }

def fixtureFamily := terminalHResolveSupportFamily 1 2 1 0

def fixtureEmptySeed : List FixtureRecord := []

def fixtureFullSeed : List FixtureRecord :=
  canonicalTerminalSupportSeed 1 2 1 0 (fun _record => true)

example : fixtureFamily.candidates.length = 16 := by decide

example : fixtureFamily.candidates.Nodup :=
  terminalHResolveSupportFamily_nodup 1 2 1 0

example : fixtureFullSeed ∈ fixtureFamily.candidates :=
  canonicalTerminalSupportSeed_mem_terminalHResolveSupportFamily
    1 2 1 0 (fun _record => true)

example : TerminalHResolveSupportExact
    fixtureCandidate fixtureModel fixtureEmptySeed := by decide

example : terminalHResolveSupportClassify
    fixtureCandidate fixtureModel fixtureEmptySeed = .exact := by decide

example : TerminalHResolveSupportGain
    fixtureCandidate fixtureModel fixtureFullSeed := by decide

example : terminalHResolveSupportClassify
    fixtureCandidate fixtureModel fixtureFullSeed = .gain := by decide

example : IsSemanticallyMinimum
    (terminalHResolveSupportImplementation
      fixtureCandidate fixtureModel fixtureEmptySeed) :=
  (terminalHResolveSupportExact_iff_semanticallyMinimum
    fixtureCandidate fixtureModel fixtureEmptySeed).1 (by decide)

example : ∃ next, StrictEquivalentGain
    (terminalHResolveSupportImplementation
      fixtureCandidate fixtureModel fixtureFullSeed) next :=
  (terminalHResolveSupportGain_iff_exists_strictEquivalentGain
    fixtureCandidate fixtureModel fixtureFullSeed).1 (by decide)

example : fixtureFamily.candidates.Nodup ∧
    ∀ seed, seed ∈ fixtureFamily.candidates →
      (terminalHResolveSupportClassify fixtureCandidate fixtureModel seed =
          .exact ∧
        IsSemanticallyMinimum
          (terminalHResolveSupportImplementation
            fixtureCandidate fixtureModel seed)) ∨
      (terminalHResolveSupportClassify fixtureCandidate fixtureModel seed =
          .gain ∧
        ∃ next, StrictEquivalentGain
          (terminalHResolveSupportImplementation
            fixtureCandidate fixtureModel seed) next) :=
  terminal_hresolve_support_resolver_constructive_complete
    fixtureCandidate fixtureModel

end HResolveSupportResolverRegression
end DirectWire
end PNP
