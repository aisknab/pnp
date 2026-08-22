/-
Copyright (c) 2026 PNP Labs.

Proof-bearing Budget sidecar boundary for the report-facing ZeroSlack
certificate.  The finite direct-wire candidate, candidate-derived saturation
model, and natural resource caps are explicit data.  Acceptance is not a
caller flag: the existing exhaustive terminal-envelope search must compute
`none`, which excludes every canonical support seed by the same checked
feasibility predicate.  Exact and gain route meanings are derived from the
existing semantic reflection theorems rather than stored as proof handles.

The caps remain inputs, and exhaustive support enumeration, saturation, and
reference minimization may be exponential.  This module does not formalize
the BUD grammar, B0--B4 blocker semantics, a polynomial envelope dynamic
program, full BudgetResolve, the complete no-lower ledger, unconditional
ZeroSlack, PCCMin, SAT in P, or P = NP.
-/

import PNP.ResidualTerminalBudgetEnvelopeResolver

namespace PNP

/-- Checked, proof-bearing `NoBudget` evidence consumed by the structured
    ZeroSlack boundary.  A failed exhaustive search replaces all former string
    handles; constructive route semantics are recovered from existing kernel
    theorems. -/
structure BudgetSidecarCertificate where
  inputs : Nat
  gates : Nat
  outputs : Nat
  profileWidth : Nat
  budget : DirectWire.TerminalSupportBudget
  candidate : DirectWire.Candidate inputs gates outputs
  model : DirectWire.TerminalCandidateSaturationModel
    (profileWidth := profileWidth) candidate
  noBudgetSidecar :
    DirectWire.findTerminalBudgetFeasibleSupport budget candidate model = none

/-- The stored search equation exposes exactly the exhaustive terminal
    `NoBudget` proposition. -/
theorem BudgetSidecarCertificate.excluded
    (certificate : BudgetSidecarCertificate) :
    ∀ seed,
      seed ∈ DirectWire.allTerminalSupportSeeds certificate.inputs
        certificate.gates certificate.outputs certificate.profileWidth →
      ¬certificate.budget.Fits certificate.candidate certificate.model seed :=
  (DirectWire.findTerminalBudgetFeasibleSupport_eq_none_iff
    certificate.budget certificate.candidate certificate.model).mp
      certificate.noBudgetSidecar

/-- A checked Budget sidecar has no feasible governed terminal support. -/
theorem BudgetSidecarCertificate.no_feasible_support
    (certificate : BudgetSidecarCertificate) :
    ¬∃ seed,
      seed ∈ DirectWire.allTerminalSupportSeeds certificate.inputs
        certificate.gates certificate.outputs certificate.profileWidth ∧
      certificate.budget.Fits certificate.candidate certificate.model seed := by
  rintro ⟨seed, governed, fits⟩
  exact certificate.excluded seed governed fits

/-- Any explicit exact route at this boundary retains genuine semantic-minimum
    meaning; no separate caller proof or string handle is accepted. -/
theorem BudgetSidecarCertificate.exact_route_sound
    (certificate : BudgetSidecarCertificate)
    (seed : List (DirectWire.TerminalPrimitiveRecord certificate.inputs
      certificate.gates certificate.outputs certificate.profileWidth))
    (route : DirectWire.TerminalHResolveSupportExact certificate.candidate
      certificate.model seed) :
    DirectWire.IsSemanticallyMinimum
      (DirectWire.terminalHResolveSupportImplementation certificate.candidate
        certificate.model seed) :=
  (DirectWire.terminalHResolveSupportExact_iff_semanticallyMinimum
    certificate.candidate certificate.model seed).mp route

/-- Any explicit gain route at this boundary retains a genuine strict
    equivalent implementation witness. -/
theorem BudgetSidecarCertificate.gain_route_sound
    (certificate : BudgetSidecarCertificate)
    (seed : List (DirectWire.TerminalPrimitiveRecord certificate.inputs
      certificate.gates certificate.outputs certificate.profileWidth))
    (route : DirectWire.TerminalHResolveSupportGain certificate.candidate
      certificate.model seed) :
    ∃ next, DirectWire.StrictEquivalentGain
      (DirectWire.terminalHResolveSupportImplementation certificate.candidate
        certificate.model seed) next :=
  (DirectWire.terminalHResolveSupportGain_iff_exists_strictEquivalentGain
    certificate.candidate certificate.model seed).mp route

/-- Named M178 endpoint: one checked proof-bearing Budget sidecar supplies
    exhaustive terminal-envelope exclusion and preserves real semantic
    meanings for both constructive route forms. -/
theorem budget_zeroslack_sidecar_checked_complete
    (certificate : BudgetSidecarCertificate) :
    (∀ seed,
      seed ∈ DirectWire.allTerminalSupportSeeds certificate.inputs
        certificate.gates certificate.outputs certificate.profileWidth →
      ¬certificate.budget.Fits certificate.candidate certificate.model seed) ∧
    (¬∃ seed,
      seed ∈ DirectWire.allTerminalSupportSeeds certificate.inputs
        certificate.gates certificate.outputs certificate.profileWidth ∧
      certificate.budget.Fits certificate.candidate certificate.model seed) ∧
    (∀ seed : List (DirectWire.TerminalPrimitiveRecord certificate.inputs
        certificate.gates certificate.outputs certificate.profileWidth),
      DirectWire.TerminalHResolveSupportExact certificate.candidate
          certificate.model seed →
        DirectWire.IsSemanticallyMinimum
          (DirectWire.terminalHResolveSupportImplementation
            certificate.candidate certificate.model seed)) ∧
    (∀ seed : List (DirectWire.TerminalPrimitiveRecord certificate.inputs
        certificate.gates certificate.outputs certificate.profileWidth),
      DirectWire.TerminalHResolveSupportGain certificate.candidate
          certificate.model seed →
        ∃ next, DirectWire.StrictEquivalentGain
          (DirectWire.terminalHResolveSupportImplementation
            certificate.candidate certificate.model seed) next) := by
  exact ⟨certificate.excluded, certificate.no_feasible_support,
    certificate.exact_route_sound, certificate.gain_route_sound⟩

end PNP
