# Counterexample to the unrestricted compatible-support slack law

This kernel-checked finding concerns the unrestricted raw-port-completeness
interpretation of section 2.2 of the pinned historical manuscript. It is
**not a refutation of the checked acyclic framed law**, a properly restricted
admissible-support law, or the complete saturated manuscript route. It does
not decide P versus NP.

## What fails

The historical definition lists every incoming boundary wire and outgoing
interface wire, but does not explicitly require that an arbitrary equivalent
replacement remain acyclic when reconnected to the exterior. Port completeness
and equality of the independent open function do not supply that requirement.

The [literal eleven-gate source](../lean/PNP/NANDCompatibleSupportSlackMinimum.lean)
has four inputs and ten ordinary outputs. Its minimum is eleven among every
equivalent finite NAND implementation, not just a bounded synthesis search.
Ten distinct nonconstant, nonprojection outputs need ten distinct gates; none
can be the first NAND of two free input/constant sources, so an additional
hidden first gate is necessary.

The existing extractor selects nine gates and computes the complete cut:

- Incoming ports: primary inputs `a`, `b`, and exterior gate `z`.
- Outgoing ports: source gates `1, 4, 5, 6, 7, 8, 9, 10`.
- Exact minimum for the independent open function: eight gates.

The [open comparison](../lean/PNP/NANDCompatibleSupportSlackComparison.lean)
uses the actual extractor, not a hand-written substitute with fewer ports.
Its cheaper implementation preserves every independent boundary valuation and
every ordered output. Nevertheless its literal reconnection is cyclic.
The identity replacement is an independent successful-compilation control.

Thus the [checked obstruction](../lean/PNP/NANDCompatibleSupportSlackObstruction.lean)
proves local slack `9 - 8 = 1` and whole slack `11 - 11 = 0`:

```lean
theorem global_slack_law_violation :
    ¬ residualSlack support.extractedCandidate.toImplementation ≤
      residualSlack original.toImplementation
```

A syntactic dependency through the exterior may persist even when Boolean
simplification removes the corresponding semantic dependency. Treating the
replacement as an independently correct open function does not by itself
produce a well-formed global circuit of the claimed smaller size.

## What remains valid and what needs repair

The existing acyclic framed and successfully compiled arbitrary-support
replacement theorems retain their exact hypotheses. The completed,
dependency-closed computational-profile comparisons also retain their scope.
This example does not establish a contradiction in those Lean results.

The source-derived full-profile admissibility and first-loss routing remain open.
A repaired route must derive its admissibility or valid routed alternative from
actual terminal data and preserve the claimed physical cost. Supplying the
desired compiler success, minimum, completeness certificate or rank-decrease
premise would not discharge that obligation.

The pinned historical manuscript is unchanged. See the
[current reconstruction notice](./FORMAL_RECONSTRUCTION.md) and the
[reviewer question AQ-03](./audit_questions.md#aq-03--compatible-replacement-and-global-slack-law)
for the distinction between its intended claim and current theorem authority.

## Evidence and progress treatment

The [axiom audit](../lean-audit/PNPCompatibleSupportSlackObstructionAxiomAudit.lean)
imports the explicit root and covers all eighteen explicitly declared public
theorems. The compiled inventory also records generated declarations.
The [regression](../lean-regression/PNPCompatibleSupportSlackObstructionProbe.lean)
checks literal truth tables, actual ports, successful identity substitution,
failed cyclic substitution and rejection of a wrong output word. Runtime
checks are controls, not proof authority; the lower bounds and inequality are
kernel-checked. No exhaustive reference minimum is executed to establish them.

No positive publication row or fixed checkpoint is awarded for this correction.
The previously earned checkpoints do not use the refuted unrestricted lemma,
so their credit is not revoked by this result. Formal artefact coverage and
risk-weighted proof completion remain separate measurements in the
[canonical progress ledger](../status/PROOF_PROGRESS.json).
A future repair receives credit only when it closes a fixed complete obligation.
