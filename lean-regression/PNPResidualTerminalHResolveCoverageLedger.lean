import PNP.ResidualTerminalHResolveCoverageLedger

namespace PNP
namespace DirectWire
namespace HResolveCoverageLedgerRegression

inductive FixtureCandidate where
  | exactCandidate
  | gainCandidate
  | blockedLeft
  | blockedRight
  | unresolvedCandidate
deriving DecidableEq, Repr

open FixtureCandidate

def fixtureExact (candidate : FixtureCandidate) : Prop :=
  candidate = .exactCandidate

def fixtureGain (candidate : FixtureCandidate) : Prop :=
  candidate = .gainCandidate

def fixtureBlocked (candidate : FixtureCandidate) : Prop :=
  candidate = .blockedLeft ∨ candidate = .blockedRight

instance : DecidablePred fixtureExact := fun _ => by
  unfold fixtureExact
  exact inferInstance

instance : DecidablePred fixtureGain := fun _ => by
  unfold fixtureGain
  exact inferInstance

instance : DecidablePred fixtureBlocked := fun _ => by
  unfold fixtureBlocked
  exact inferInstance

def blockedFamily : TerminalHResolveFamily FixtureCandidate :=
  ⟨[blockedLeft, blockedRight]⟩

def duplicateFamily : TerminalHResolveFamily FixtureCandidate :=
  ⟨[blockedLeft, blockedLeft]⟩

def exactFamily : TerminalHResolveFamily FixtureCandidate :=
  ⟨[blockedLeft, exactCandidate]⟩

def gainFamily : TerminalHResolveFamily FixtureCandidate :=
  ⟨[blockedLeft, gainCandidate]⟩

def unresolvedFamily : TerminalHResolveFamily FixtureCandidate :=
  ⟨[blockedLeft, unresolvedCandidate]⟩

example : terminalHResolveClassify fixtureExact fixtureGain fixtureBlocked
    exactCandidate = .exact := rfl

example : terminalHResolveClassify fixtureExact fixtureGain fixtureBlocked
    gainCandidate = .gain := rfl

example : terminalHResolveClassify fixtureExact fixtureGain fixtureBlocked
    blockedLeft = .blocked := rfl

example : terminalHResolveClassify fixtureExact fixtureGain fixtureBlocked
    unresolvedCandidate = .unresolved := rfl

example : blockedFamily.routeLedger fixtureExact fixtureGain fixtureBlocked =
    [(blockedLeft, .blocked), (blockedRight, .blocked)] := rfl

example : blockedFamily.checkNoHereditarySidecar
    fixtureExact fixtureGain fixtureBlocked = true := by decide

example : duplicateFamily.checkNoHereditarySidecar
    fixtureExact fixtureGain fixtureBlocked = false := by decide

example : exactFamily.checkNoHereditarySidecar
    fixtureExact fixtureGain fixtureBlocked = false := by decide

example : gainFamily.checkNoHereditarySidecar
    fixtureExact fixtureGain fixtureBlocked = false := by decide

example : unresolvedFamily.checkNoHereditarySidecar
    fixtureExact fixtureGain fixtureBlocked = false := by decide

example : blockedFamily.NoHereditarySidecarAccepted
    fixtureExact fixtureGain fixtureBlocked :=
  (blockedFamily.checkNoHereditarySidecar_eq_true_iff
    fixtureExact fixtureGain fixtureBlocked).mp (by decide)

example : ∀ candidate, candidate ∈ blockedFamily.candidates →
    ¬fixtureExact candidate ∧ ¬fixtureGain candidate :=
  terminal_hresolve_checked_sidecar_excludes_constructive_routes
    blockedFamily fixtureExact fixtureGain fixtureBlocked (by decide)

end HResolveCoverageLedgerRegression
end DirectWire
end PNP
