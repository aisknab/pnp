# Source-only proper-support descendant certificates

M268 connects complete descendant execution to a source-only verifier for proper computational supports. The specification is section 6.1 VerifyDW and section 4 materializer charging in the [pinned manuscript](../archive/legacy-v0/ARCHIVE.json). It closes the acceptance edge after [persistent descendant ownership](lean_descendant_history_ownership.md), not the full manuscript verifier.

## Input and acceptance

The caller supplies a source wire carrier, raw outer support records and a raw descendant program. Input, output, field and gate dimensions, support sizes, boundary widths and program lengths are arbitrary finite data. The outer computational carrier retains its existing zero abstract-profile width; every literal field is exposed and preserved. This does not claim that the manuscript profile is empty.

Acceptance is equivalent to all four conditions:

1. Every raw outer support record decodes against the actual source.
2. The complete local program executes on the extracted source.
3. The retained physical exterior is nonempty: the selected support is proper.
4. The final local physical gate count is strictly smaller than the extracted source.

Outer compilation is derived from arbitrary-label execution dependency bounds; successful splicing is not an extra supplied premise. The returned receipt retains the actual run and literal compiler result. A failed later stage rejects the entire program. Duplicate records retain their input identity without counting a physical gate twice.

## Preserved meaning and costs

The actual ambient result has one copy of the exterior and preserves every ordinary output and literal computational field. Its final gate count plus actual cumulative removals equals the original gate count plus actual cumulative charges. Later deletion cannot erase a historical allocation charge.

Intermediate stages may grow. Only final local saving is required; it yields the existing StrictEquivalentGain and strict residual descent. No intermediate circuit, correctness proof, ownership map, cost certificate, rank, ordering witness or semantic oracle is supplied. Rejecting an offered certificate is not evidence that no better certificate exists.

## Source and verification boundaries

| Source | Boundary |
| --- | --- |
| [Causal bounds](../lean/PNP/NANDWireDescendantCausalBounds.lean) | Actual arbitrary-program dependency preservation and derived outer compilation |
| [Proper embedding](../lean/PNP/NANDWireDescendantProperSupport.lean) | Literal one-copy splice, all observations and historical cost balance |
| [Source-only verifier](../lean/PNP/NANDWireDescendantCertificate.lean) | Exact acceptance, soundness, completeness and fail-closed rejection |

The [source contracts](../audits/lean-proper-descendant-certificates0.test.mjs), [compiled publication contracts](../audits/lean-proper-descendant-certificates-publication0.test.mjs) and [explicit-root axiom audit](../lean-audit/PNPProperDescendantCertificateAxiomAudit.lean) bind 33 reviewed theorems. Run `npm run audit:m268` after generated status is reconciled. The regression programs exercise zero dimensions, malformed records, proper and whole supports, duplicate records, temporary expansion, failed tails and final nondecrease. Those finite executions are tests; the arbitrary-dimension Lean statements are theorem authority.

## Reviewed publication boundary

As of `PNP-FORMAL-RECONSTRUCTION-STATUS-2026-09-17-268`:

For arbitrary finite computational wire-carrier dimensions, raw outer support records and raw descendant programs, source-only verification decodes every outer coordinate and executes the complete local program on the extracted source. Arbitrary-label dependency bounds follow actual execution and derive literal outer compilation without a supplied wiring order or successful-splice premise. Acceptance is exactly complete decoding, successful complete local execution, proper physical support and strict final local saving. The constructed one-copy ambient splice preserves all ordinary outputs and literal fields, retains the actual run and compiler receipts, and satisfies exact historical charge/removal accounting. Intermediate expansion is permitted; invalid coordinates, a failed later stage, whole support and final nondecrease reject. Every accepted certificate yields StrictEquivalentGain and strict residual descent without supplied intermediate circuits, correctness, owners, costs, ranks or semantic oracles.

This verifies offered finite programs in the existing closed computational wire-carrier language. It does not prove that every nonminimal input has an accepted certificate, construct a globally successful strategy, derive terminal families or establish local minimality after rejection. Full manuscript profiles, all R1-R9 and N1-N10 rule families, cross-support transport of open obligations, matched-kappa arbitrary-support Pull/Expand, full manuscript VerifyDW, ChargeSoundness and Package E remain open. No bound on temporary growth, encoded-input polynomial runtime, output size or certificate size is proved. Global route coverage, unconditional SaturatePositive, BCELReady and ZeroSlack, exact general PCCMin, deterministic CNFSAT in P and the eligible root remain open. Runtime fixtures are regression evidence, not theorem authority. No fixed weighted checkpoint or global gate closes, and P = NP is not proved.

Formal artefact coverage: 244 of 246 current scoped publication rows earned.
Risk-weighted proof completion estimate: 40%.
Uncertainty range: 20% to 40%.
Global gates closed: 0 of 5.

Publication decision: defer. The source-only proper-support verifier closes the computational offered-program acceptance edge, not full manuscript VerifyDW or certificate discovery for arbitrary nonminimal inputs. No fixed weighted checkpoint or global gate changes, and the published global bottom line remains unchanged. Preserve the coherent M264 website pin and batch pending core evidence at the next major publication.

The [fixed progress ledger](../status/PROOF_PROGRESS.json) is authoritative. Its estimate is neither confidence that the route is correct nor a delivery or time-remaining estimate.
