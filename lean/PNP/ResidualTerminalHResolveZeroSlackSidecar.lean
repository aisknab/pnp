/-
Copyright (c) 2026 PNP Labs.

Proof-bearing HResolve sidecar boundary for the report-facing ZeroSlack
certificate.  The governed finite family, implementation map, three route
predicates, and their decidability witnesses are explicit data.  Acceptance
is not a caller flag: the existing finite-family checker recomputes uniqueness
and requires every candidate to take the blocked route after both constructive
routes fail.  Exact and gain predicates are separately bound to semantic
minimum and strict-equivalent-gain propositions.

The family, implementation map, predicates, and blocker semantics remain
inputs.  This module does not derive hereditary candidates from terminal data,
formalize the HN grammar, BWL, ParseOrExit, leaf tightness, H0--H4 blocker
semantics, full or polynomial HResolve, the complete no-lower ledger,
unconditional ZeroSlack, PCCMin, SAT in P, or P = NP.
-/

import PNP.ResidualTerminalHResolveCoverageLedger

namespace PNP

/-- Checked, proof-bearing HResolve evidence consumed by the structured
    ZeroSlack boundary.  Every former string field is now either the result of
    the executable NoHereditary checker or a semantic theorem. -/
structure HResolveSidecarCertificate where
  inputs : Nat
  outputs : Nat
  Candidate : Type
  candidateDecidableEq : DecidableEq Candidate
  family : DirectWire.TerminalHResolveFamily Candidate
  implementation : Candidate → DirectWire.Implementation inputs outputs
  exact : Candidate → Prop
  gain : Candidate → Prop
  blocked : Candidate → Prop
  exactDecidable : DecidablePred exact
  gainDecidable : DecidablePred gain
  blockedDecidable : DecidablePred blocked
  noHereditarySidecar :
    @DirectWire.TerminalHResolveFamily.checkNoHereditarySidecar
      Candidate candidateDecidableEq family exact gain blocked
        exactDecidable gainDecidable blockedDecidable = true
  exactMinimumRouteSound : ∀ candidate, exact candidate →
      DirectWire.IsSemanticallyMinimum (implementation candidate)
  gainRouteSound : ∀ candidate, gain candidate →
      ∃ next, DirectWire.StrictEquivalentGain
        (implementation candidate) next

/-- The stored Boolean equation exposes exactly the checker's mathematical
    accepted-sidecar proposition. -/
theorem HResolveSidecarCertificate.accepted
    (certificate : HResolveSidecarCertificate) :
    certificate.family.NoHereditarySidecarAccepted
      certificate.exact certificate.gain certificate.blocked := by
  exact (@DirectWire.TerminalHResolveFamily.checkNoHereditarySidecar_eq_true_iff
      certificate.Candidate certificate.candidateDecidableEq
      certificate.family certificate.exact certificate.gain
      certificate.blocked certificate.exactDecidable
      certificate.gainDecidable certificate.blockedDecidable).mp
        certificate.noHereditarySidecar

/-- A checked HResolve ZeroSlack sidecar excludes its exact predicate for
    every governed candidate. -/
theorem HResolveSidecarCertificate.not_exact
    (certificate : HResolveSidecarCertificate)
    (candidate : certificate.Candidate)
    (member : candidate ∈ certificate.family.candidates) :
    ¬certificate.exact candidate :=
  (certificate.accepted.2 candidate member).1

/-- A checked HResolve ZeroSlack sidecar excludes its gain predicate for
    every governed candidate. -/
theorem HResolveSidecarCertificate.not_gain
    (certificate : HResolveSidecarCertificate)
    (candidate : certificate.Candidate)
    (member : candidate ∈ certificate.family.candidates) :
    ¬certificate.gain candidate :=
  (certificate.accepted.2 candidate member).2.1

/-- Every governed candidate in a checked sidecar carries the positive blocker
    predicate after both constructive routes have failed. -/
theorem HResolveSidecarCertificate.blocked_of_mem
    (certificate : HResolveSidecarCertificate)
    (candidate : certificate.Candidate)
    (member : candidate ∈ certificate.family.candidates) :
    certificate.blocked candidate :=
  (certificate.accepted.2 candidate member).2.2

/-- The certificate's exact predicate has actual semantic-minimum meaning. -/
theorem HResolveSidecarCertificate.exact_route_sound
    (certificate : HResolveSidecarCertificate)
    (candidate : certificate.Candidate)
    (exact : certificate.exact candidate) :
    DirectWire.IsSemanticallyMinimum (certificate.implementation candidate) :=
  certificate.exactMinimumRouteSound candidate exact

/-- The certificate's gain predicate has an actual strict equivalent
    implementation witness. -/
theorem HResolveSidecarCertificate.gain_route_sound
    (certificate : HResolveSidecarCertificate)
    (candidate : certificate.Candidate)
    (gain : certificate.gain candidate) :
    ∃ next, DirectWire.StrictEquivalentGain
      (certificate.implementation candidate) next :=
  certificate.gainRouteSound candidate gain

/-- Named M177 endpoint: one checked proof-bearing sidecar supplies unique
    governed coverage, exact/gain exclusion and positive blocking for every
    candidate, while retaining genuine semantic meanings for both constructive
    route predicates. -/
theorem hresolve_zeroslack_sidecar_checked_complete
    (certificate : HResolveSidecarCertificate) :
    certificate.family.candidates.Nodup ∧
      ∀ candidate, candidate ∈ certificate.family.candidates →
        (¬certificate.exact candidate ∧
          ¬certificate.gain candidate ∧
          certificate.blocked candidate) ∧
        (certificate.exact candidate →
          DirectWire.IsSemanticallyMinimum
            (certificate.implementation candidate)) ∧
        (certificate.gain candidate →
          ∃ next, DirectWire.StrictEquivalentGain
            (certificate.implementation candidate) next) := by
  refine ⟨certificate.accepted.1, ?_⟩
  intro candidate member
  exact ⟨⟨certificate.not_exact candidate member,
      certificate.not_gain candidate member,
      certificate.blocked_of_mem candidate member⟩,
    certificate.exact_route_sound candidate,
    certificate.gain_route_sound candidate⟩

end PNP
