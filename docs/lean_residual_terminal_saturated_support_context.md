# Computed saturated-support replacement context and physical slack

M237 derives a real replacement context from every production saturated
physical support. This closes the construction edge between the existing
support extractor and the supplied-frame replacement and slack laws.

## Exact theorem boundary

The [computed-context module](../lean/PNP/ResidualTerminalSaturatedSupportContext.lean)
uses the actual production saturation records and computes their physical gate
complement. It reuses the existing extractor for both halves. No caller supplies
a frame, fan-in-closure certificate, gate partition or reconstruction proof.

The five interfaces apply at arbitrary finite input, gate, output and profile
widths, candidates, executable terminal models and seed lists:

- `terminalCandidateSaturate_boundary_isInput` proves that the extracted
  boundary contains only primary inputs. Production gate-source closure
  internalizes every required predecessor gate.
- `terminalCandidateSaturatePhysicalContext_size` proves the exact
  physical gate-count equation for every replacement size, with no semantic
  or smaller-replacement premise.
- `terminalCandidateSaturatePhysicalContext_equivalent` proves that
  plugging the unchanged extracted support reproduces the complete original
  ordered Boolean output word at every input valuation.
- `terminalCandidateSaturatePhysicalContext_replace_equivalent` transports
  any equivalent replacement on the exact extracted boundary and interface
  back to the original whole circuit.
- `terminalCandidateSaturatePhysicalSupport_slack_le` bounds the
  computed support's physical Boolean residual slack by whole-circuit slack.

The zero-gate environment forwards support boundary inputs and original input
bypasses. The continuation rebinds the extracted complement to actual support
interface outputs and bypasses. Every complement gate boundary and every
original gate output has a proved available binding; fallback branches cannot
replace missing reconstruction evidence. Duplicate outputs retain their
original order and multiplicity.

The exact count includes every inherited seed gate. Selected and complement
gates partition the original physical NAND universe, whether the selected
indices are contiguous or not. Replacements may be smaller or larger.

## Manuscript linkage and limits

The [plan](plans/2026-09-11-computed-saturated-support-context.md) anchors this
step in the pinned manuscript's section 2 Compatible replacement and Global
slack law, section 3 computed support saturation, and section 4 physical
charge accounting. The earlier
[physical-charge ledger](lean_residual_terminal_physical_charge_ledger.md)
remains unchanged.

These are physical Boolean replacement and slack laws for actual production
saturated supports, not arbitrary raw supports or full-profile compatibility.
The complete manuscript profile/materializer charge universe, fixed global
ownership map and full-profile replacement transport remain open.

The executable observer and profile model remain supplied data. Influence and
semantic minima use exhaustive finite reference constructions; no polynomial
runtime is proved. A physical slack inequality is not an unconditional
manuscript-level saturation, activation or residual-minimization theorem.

## Regression and assumption evidence

The [permanent regressions](../lean-regression/PNPResidualTerminalSaturatedSupportContext.lean)
apply all five interfaces at arbitrary dimensions. Executable cases cover
noncontiguous fan-in-closed gates, multiple outside consumers, repeated global
outputs and seeds, original input bypasses, smaller and larger equivalent
replacements, empty and full supports, constants and zero-width carriers.

A deliberately unsaturated raw support has an external gate on its boundary.
This guards the distinction between production saturation and an arbitrary
supplied gate set; the zero-environment theorem does not apply to that raw set.

The [explicit-root audit](../lean-audit/PNPResidualTerminalSaturatedSupportContextAxiomAudit.lean)
checks all five theorem interfaces. Their axiom closures contain only
`propext` and `Quot.sound`, with no project-specific axiom or classical choice.
The [source and publication contracts](../audits/lean-residual-terminal-saturated-support-context0.test.mjs)
reject supplied frames, finite-only statements, weakened equivalence, wrong
charge accounting, assumption-backed substitutes and compiled type drift.

## Remaining proof burden and progress

No full-minimum growth, quotient bound, global named route, input-derived
complete terminal family, unconditional SaturatePositive, BCELReady or ZeroSlack,
or complete polynomial PCCMin runtime and certificate bounds is established.
Deterministic CNFSAT in P and the eligible root theorem remain absent.
The publication gate remains false. No fixed weighted checkpoint or global
gate closes.

Formal artefact coverage: 213 of 215 current scoped publication rows earned.
Risk-weighted proof completion estimate: 40%. Uncertainty range: 20% to 40%. Global gates closed: 0 of 5.

These separate measures come from the
[canonical progress ledger](../status/PROOF_PROGRESS.json). Neither is confidence
that `P = NP` is true, a probability of success or a time estimate.

Publication decision: defer. Preserve the coherent M231 PNPLabs source pin
until a major publication is warranted. Meaningful core submilestone and
release notifications continue independently.
