# M232 plan: semantic reflection of terminal profile dependencies

Status: implemented and kernel checked. Publication requires the verification
and review gates below. Started from the verified M231 core merge
`e4af115a66cd5a6715a9363abea7a2008238d401`, tree
`28bf3e0bb8f4afccf308859c5f42f9c27b14edbb`.
The independent M230/M231 website publication remains pinned to that exact
source. Do not change its source or artifacts while this core work proceeds.

## Legacy anchor and dependency edge

Sections 3 and 5 of the pinned legacy manuscript require saturated supports
to retain their governed profile dependencies. Section 10's
`RW-SaturatePositive` argument then requires faithful origin, kernel and
obligation closure reasoning. Use the document tag in
[the archive manifest](../../archive/legacy-v0/ARCHIVE.json) as specification
and provenance, never as Lean theorem authority.

`ResidualTerminalCandidateSaturation` already computes physical incidence
from the program and profile incidence from finite Boolean influence over
every canonical gate-subset context. Do not reconstruct that algorithm again.
The missing local edge is a proved semantic interpretation of that computed
profile incidence and its consequence for the actual computed saturation.

The intended path is: candidate and executable observer, computed influence,
semantic dependency reflection and noninterference, faithful profile closure
reasoning, complete SaturatePositive routing, BCELReady, then ZeroSlack.
This change closes only the reflection/noninterference edge. It does not
supply the remaining global steps in that path.

## Unbounded abstraction and exact theorem interfaces

Quantify over every finite candidate size, profile width, executable model,
profile coordinate, gate, seed and canonical context. Define the observation
notation below by the existing ambient support implementation, with no new
semantic oracle or correctness field:

```lean
def terminalCandidateProfileObservation
    {inputs gates outputs profileWidth : Nat}
    (candidate : Candidate inputs gates outputs)
    (model : TerminalCandidateSaturationModel
      (profileWidth := profileWidth) candidate)
    (context : List (Fin gates)) (coordinate : Fin profileWidth) : Bool :=
  model.observe (terminalAmbientSupportImplementation candidate
    (context.map (fun gate =>
      (TerminalPrimitiveRecord.gate gate :
        TerminalPrimitiveRecord inputs gates outputs profileWidth)))) coordinate
```

With the same universally quantified parameters, prove:

```lean
theorem terminalGateInfluencesProfile_eq_true_iff :
    terminalGateInfluencesProfile candidate model gate coordinate = true ↔
      ∃ context,
        context ∈ terminalListSubsets
          ((allFin gates).filter (fun other => decide (other ≠ gate))) ∧
        terminalCandidateProfileObservation candidate model
            (gate :: context) coordinate ≠
          terminalCandidateProfileObservation candidate model context coordinate

theorem terminalCandidateProfileRequires_eq_influence :
    (terminalCandidateSaturationSystem candidate model).requires kind
        (.profile coordinate) (.gate gate) =
      (decide (kind = terminalSaturationRuleOfProfileRole
        (model.profileSystem.role coordinate)) &&
        terminalGateInfluencesProfile candidate model gate coordinate)

theorem terminalCandidateSaturate_profile_noninterference
    (profileMember : TerminalPrimitiveRecord.profile coordinate ∈
      terminalSaturateRecords (terminalCandidateSaturationSystem candidate model) seed)
    (gateAbsent : TerminalPrimitiveRecord.gate gate ∉
      terminalSaturateRecords (terminalCandidateSaturationSystem candidate model) seed)
    (canonicalContext : context ∈ terminalListSubsets
      ((allFin gates).filter (fun other => decide (other ≠ gate)))) :
    terminalCandidateProfileObservation candidate model (gate :: context) coordinate =
      terminalCandidateProfileObservation candidate model context coordinate
```

The context membership and computed-support membership conditions are ordinary
domain premises, not supplied soundness or coverage certificates. The result
must retain the actual candidate, observer, dependency computation and
computed closure. Do not replace them with an arbitrary caller dependency
relation or a singleton-context test. The noninterference claim concerns the
canonical contexts above, not an unproved normalization of arbitrary records.

## Producer and expectation plan

| Producer | Consumers prepared together | First rejecting checks |
| --- | --- | --- |
| Observation and three general theorem interfaces | Focused Lean audit and unbounded regressions, source/type hostile contract | Exact leaf build, expected axiom closures and general theorem application |
| Compiled public names and types | Reviewed-name producer/consumer sets, milestone map and source-closure contract | Name-set equality before inventory extraction; compiled type fingerprints afterward |
| Earned local evidence row | Status and progress history, core documentation and current report | Fail-closed scope, unchanged checkpoint score and generated byte checks |

Use interaction-sensitive regression data: an observer whose value can change
only in a nonempty context must not be treated as independent merely because
a singleton test is silent. Cover all rule roles, exact computed-closure
membership and a genuinely absent dependency. Fixtures are regressions for
the general theorem, not separate earned milestones.

## Verification, scoring and publication decision

Prepare source and affected expectations before compilation or broad testing.
Reuse only the exact matching M231 source/toolchain cache, rebuild the changed
dependency chain and explicit root, then run the new permanent axiom audit and
regressions. Derive fingerprints and counts from compiled output. Reconcile
the canonical inventory, publication map, status, ledger history and report
before broad checks, normal PR/merge gates and exact-source reproduction.

No fixed weighted checkpoint is earned by this local theorem alone. Keep the
risk-weighted estimate at 40%, uncertainty 20% to 40%, and all five gates open.
The observer/model remains supplied and influence construction still uses
exhaustive subsets. Input-derived profile semantics, complete global routes,
unconditional SaturatePositive/BCELReady/ZeroSlack and full polynomial PCCMin
remain open. Do not award runtime credit or imply a SAT algorithm.

Publication decision: defer a separate website update unless verification
exposes a correction to an existing public claim. Preserve the coherent M231
site pin and report this core result through meaningful progress notifications.

## Integration evidence and verification ownership

The explicit root build and the exact durable four-declaration axiom-audit
block passed. All three public theorem fingerprints were extracted from the
compiled declarations; their closures contain only `propext` and `Quot.sound`.
The generated inventory, reviewed publication map and current status agree.

The focused package/public-surface preflight passed six tests. The combined
M232, current-status, M231 compatibility and historical cost-balance checks
passed all 59 tests with no skips. Complete the remaining required test files,
deterministic report build, normal PR/post-merge checks and exact-head clean
reproduction before treating this as a merged milestone. Reuse the unchanged
focused test-file evidence in that combined coverage rather than repeating
the long current-status mutation sweep. Recheck a file when one of its actual
inputs changes; source/fixture edits must precede those checks.

Formal artefact coverage: 208 of 210 current scoped publication rows earned.
Risk-weighted proof completion estimate: 40%. Uncertainty range: 20% to 40%.
Global gates closed: 0 of 5. No project-specific axiom remains in the compiled
inventory; `PNP.Main.p_eq_np` is absent and the publication gate is false.
