# Computed terminal saturation-positivity firewall

## Result

`PNP.ResidualTerminalSaturationPositivityFirewall` removes the final
caller-supplied Boolean choice at the current terminal saturation-to-BCEL
boundary. Its input is the existing finite `TerminalBCELAnchorProblem`: one
proof-bearing governed proper-positive support, an explicit terminal dependency
system, one forgetful projection, and one executable ambient observer.

`classifyTerminalSaturationPositivity` computes the projection defect of the
complete canonical anchor family. The caller does not provide a positivity
proof, a loss flag, a lift certificate, or a BCEL branch selector.

## Exact two-branch boundary

The total result has exactly two constructors:

1. `projectionPositivityLost` means that the whole-support projection defect is
   zero. Its `TerminalProjectionPositivityLoss` record contains the exact zero
   equality, an attained quotient-minimum comparison, and
   `TerminalCheckedFullLift` evidence for every forgotten profile coordinate.
   The full and quotient exhaustive minima are therefore equal. The word
   "lost" refers to loss of a positive projection defect, not loss of the
   support's already proved positive local gain.
2. `bcel` contains an internally derived proof that the whole-support defect is
   positive and the exact result of `classifyTerminalBCELAnchorNucleus`. The
   existing order remains insufficient nucleus, anchor algebra, cut defects,
   full-before-quotient local route, or ready.

Positive defect rules out a checked full lift at every attained quotient
minimum. Zero defect cannot silently enter BCEL, and positive defect cannot
bypass the existing fail-closed BCEL classifier.

## Arbitrary finite theorem scope

The classifier is total for every finite direct-wire candidate, explicit
terminal dependency system, computed governed proper-positive support,
forgetful projection, and executable ambient observer. It is not a theorem
about only the regression fixtures. The existing support continues to provide:

- executable-saturation closure of its records;
- physical boundary and interface compatibility;
- exact extracted open-support semantics; and
- positive exact local gain with a smaller semantic replacement.

The dependency system, projection, observer, and already computed support
remain explicit inputs. This milestone does not derive them from an arbitrary
circuit.

## Legacy obligation boundary

The pinned manuscript's `RW-SaturatePositive` theorem names five independent
sub-obligations. This milestone closes only
`projectionPositivityNotLostSilently` in the current finite terminal model. The
following remain open:

- `transparentSaturationCostBalanced`;
- `interfaceExposureRoutesToE`;
- `originKernelObligationClosureRouted`; and
- `firstNontransparentStepRecorded`.

Accordingly `leanSaturatePositiveFormalized` and `leanBCELReadyFormalized`
remain false. No Package E, global route-completeness, ZeroSlack, PCCMin,
polynomial runtime, SAT-in-P, or P = NP result follows.

## Trust and verification

The dedicated axiom transcript covers the new public declarations and their
minimum, lift, support, and BCEL dependencies. The measured closure uses only
`propext` and `Quot.sound`; it excludes project axioms, `Classical.choice`,
`sorryAx`, native evaluation, SAT shortcuts, and host-side selection.

The finite regression exercises the zero-defect checked-lift result and the
positive ready, insufficient, algebra-failure, and route-failure BCEL results.
The hostile source audit also fixes the cut-defect constructor and the exact
delegation order even where an inexpensive standalone cut-defect fixture is not
available.

The durable checks are:

```bash
lake build PNP
lake env lean -DwarningAsError=true lean-audit/PNPResidualTerminalSaturationPositivityFirewallAxiomAudit.lean
lake env lean -DwarningAsError=true lean-regression/PNPResidualTerminalSaturationPositivityFirewall.lean
node --test audits/lean-residual-terminal-saturation-positivity-firewall0.test.mjs
npm run formal:inventory:check
npm run formal:publication:check
npm run report:check
```

The root import, workflow, theorem inventory, publication map, reconstruction
status, canonical report, and public mirrors are released as one fail-closed
surface.
