import PNP.ResidualTerminalHResolveZeroSlackSidecar

namespace PNP
namespace HResolveZeroSlackSidecarRegression

open DirectWire

inductive FixtureCandidate where
  | blockedLeft
  | blockedRight
  | exactWitness
  | gainWitness
  | unresolvedWitness
deriving DecidableEq, Repr

open FixtureCandidate

def fixtureMinimum : Implementation 1 1 :=
  ⟨0, Candidate.ofDirectWireWord identityProgram identityWord⟩

theorem fixtureMinimum_isSemanticallyMinimum :
    IsSemanticallyMinimum fixtureMinimum := by
  intro gateCount _candidate _equivalent
  exact Nat.zero_le gateCount

theorem fixtureRedundantGain :
    StrictEquivalentGain redundantIdentityImplementation fixtureMinimum := by
  constructor
  · exact Nat.zero_lt_succ 0
  · exact identityCandidate_equivalent_redundantIdentity

def fixtureImplementation : FixtureCandidate → Implementation 1 1
  | .gainWitness => redundantIdentityImplementation
  | _ => fixtureMinimum

def fixtureExact (candidate : FixtureCandidate) : Prop :=
  candidate = .exactWitness

def fixtureGain (candidate : FixtureCandidate) : Prop :=
  candidate = .gainWitness

def fixtureBlocked (candidate : FixtureCandidate) : Prop :=
  candidate = .blockedLeft ∨ candidate = .blockedRight

instance : DecidablePred fixtureExact := fun _candidate => by
  unfold fixtureExact
  infer_instance

instance : DecidablePred fixtureGain := fun _candidate => by
  unfold fixtureGain
  infer_instance

instance : DecidablePred fixtureBlocked := fun _candidate => by
  unfold fixtureBlocked
  infer_instance

def blockedFamily : TerminalHResolveFamily FixtureCandidate :=
  ⟨[blockedLeft, blockedRight]⟩

def duplicateFamily : TerminalHResolveFamily FixtureCandidate :=
  ⟨[blockedLeft, blockedLeft]⟩

def exactFamily : TerminalHResolveFamily FixtureCandidate :=
  ⟨[blockedLeft, exactWitness]⟩

def gainFamily : TerminalHResolveFamily FixtureCandidate :=
  ⟨[blockedLeft, gainWitness]⟩

def unresolvedFamily : TerminalHResolveFamily FixtureCandidate :=
  ⟨[blockedLeft, unresolvedWitness]⟩

theorem fixtureExactSound : ∀ candidate, fixtureExact candidate →
    IsSemanticallyMinimum (fixtureImplementation candidate) := by
  intro candidate exact
  cases exact
  exact fixtureMinimum_isSemanticallyMinimum

theorem fixtureGainSound : ∀ candidate, fixtureGain candidate →
    ∃ next, StrictEquivalentGain (fixtureImplementation candidate) next := by
  intro candidate gain
  cases gain
  exact ⟨fixtureMinimum, fixtureRedundantGain⟩

def checkedSidecar : HResolveSidecarCertificate :=
  { inputs := 1
    outputs := 1
    Candidate := FixtureCandidate
    candidateDecidableEq := inferInstance
    family := blockedFamily
    implementation := fixtureImplementation
    exact := fixtureExact
    gain := fixtureGain
    blocked := fixtureBlocked
    exactDecidable := inferInstance
    gainDecidable := inferInstance
    blockedDecidable := inferInstance
    noHereditarySidecar := by decide
    exactMinimumRouteSound := fixtureExactSound
    gainRouteSound := fixtureGainSound }

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

example : checkedSidecar.family.NoHereditarySidecarAccepted
    checkedSidecar.exact checkedSidecar.gain checkedSidecar.blocked :=
  checkedSidecar.accepted

example : ¬checkedSidecar.exact blockedLeft :=
  checkedSidecar.not_exact blockedLeft (by
    change blockedLeft ∈ [blockedLeft, blockedRight]
    exact List.Mem.head _)

example : ¬checkedSidecar.gain blockedRight :=
  checkedSidecar.not_gain blockedRight (by
    change blockedRight ∈ [blockedLeft, blockedRight]
    exact List.Mem.tail _ (List.Mem.head _))

example : checkedSidecar.blocked blockedLeft :=
  checkedSidecar.blocked_of_mem blockedLeft
    (by
      change blockedLeft ∈ [blockedLeft, blockedRight]
      exact List.Mem.head _)

example : IsSemanticallyMinimum
    (checkedSidecar.implementation exactWitness) :=
  checkedSidecar.exact_route_sound exactWitness rfl

example : ∃ next, StrictEquivalentGain
    (checkedSidecar.implementation gainWitness) next :=
  checkedSidecar.gain_route_sound gainWitness rfl

example : checkedSidecar.family.candidates.Nodup ∧
    ∀ candidate, candidate ∈ checkedSidecar.family.candidates →
      (¬checkedSidecar.exact candidate ∧
        ¬checkedSidecar.gain candidate ∧
        checkedSidecar.blocked candidate) ∧
      (checkedSidecar.exact candidate →
        IsSemanticallyMinimum (checkedSidecar.implementation candidate)) ∧
      (checkedSidecar.gain candidate →
        ∃ next, StrictEquivalentGain
          (checkedSidecar.implementation candidate) next) :=
  hresolve_zeroslack_sidecar_checked_complete checkedSidecar

end HResolveZeroSlackSidecarRegression
end PNP
