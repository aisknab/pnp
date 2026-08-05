# Lean extraction of arbitrary terminal supports

`lean/PNP/ResidualTerminalSupportExtraction.lean` reconstructs the next named
dependency edge from §2.2 of the canonical manuscript pinned by
`archive/legacy-v0/ARCHIVE.json` at
`final-pnp-proof-report-docs-hardened-7072f8d-sealed`:

```text
(L_U, W_U) = Extract(C, U)
[[W_U]] = F_{C,U}
```

The preceding milestone computed the physical triple `(U, ∂U, ιU)`. This
milestone turns that finite support into an actual direct-wire circuit and
proves what the extracted circuit computes.

## Plain-language result

A large Boolean circuit can contain a selected group of gates that is spread
throughout the circuit rather than sitting in one continuous block. Lean can
now cut out any such finite selection and build a smaller circuit for it.

The cut has clear rules. Wires arriving from outside become the smaller
circuit's inputs. Wires between two selected gates stay inside. The constants stay
local instead of becoming fake external wires. Selected results that are used
outside, or exposed by the original circuit, become the outgoing interface.
Duplicate or scrambled selection records do not change the canonical gate
order.

Lean proves that, for every possible assignment to the incoming boundary, the
new smaller circuit gives exactly the same answers as independently evaluating
the selected part of the original circuit. It also proves a useful consistency
case: when boundary values come from a real whole-circuit execution, every
outgoing interface value is exactly the corresponding original gate value.

This is a general construction over arbitrary finite and noncontiguous gate
selections. The small circuits in the regression are examples used to test the
universal theorem, not hard-coded proof coordinates.

## Technical construction

`terminalSelectedGateIndices` scans all gate coordinates from earliest to
latest. Its membership theorem identifies the list exactly with the Boolean
selector, and its `Nodup` theorem prevents duplicate extracted gates.

`extractTerminalProgramAux` performs one proof-producing structural scan of the
intrinsically topological `Program`:

- a selected predecessor is reindexed to the already extracted prefix;
- a primary input or unselected predecessor is reindexed through the exact
  incoming boundary `terminalBoundaryPorts`;
- a constant remains the same constant; and
- an unselected gate contributes no extracted NAND gate.

The accumulator carries the extracted gate count, program, reindexing map, and
semantic invariant. Consequently `extractTerminalSupport_gateCount` proves
that the resulting program has exactly one NAND gate per canonically selected
gate. `terminalExtractedCandidate` maps the ordered
`terminalInterfacePorts` through that same reindexing map, so output order is
physical and canonical rather than supplied by a caller.

`terminalOpenGateEvaluation` and `terminalOpenSupportSemantics` are independent
open-support evaluators over original program coordinates. They read exactly
the incoming boundary for primary inputs and unselected predecessors, while
selected predecessors are internal. The central theorem
`extractTerminalSupport_semantics` states, for every boundary valuation and
every interface coordinate, that the extracted candidate denotes this open
function.

`terminalInducedBoundaryValuation` restricts a whole-circuit execution to the
computed boundary. Physical incoming completeness supplies every lookup needed
by the structural recovery induction. Theorems
`terminalOpenGateEvaluation_induced_selected`,
`terminalOpenSupportSemantics_induced`, and
`extractTerminalSupport_induced` then recover the corresponding original gate
values. `extractSaturatedTerminalSupport` composes the same construction with
the executable terminal saturation from the preceding milestone.

No interval, offset table, caller mapping, correctness certificate, or
host-side lookup participates in the construction.

## Regression and axiom boundary

The regression includes empty, singleton, full, and duplicate/scrambled
noncontiguous selections; exact selected-gate, incoming-boundary, and outgoing-
interface order; internal and external predecessor wiring; local constants;
all four assignments to a two-wire boundary; universal semantic equality;
saturation composition; and recovery from induced whole-circuit values.

The axiom transcript covers all 26 new public declarations and eight reused
saturation/physical interfaces exactly once. The compiled closure permits only
the Lean-standard axioms actually reported by the kernel: `propext`,
`Quot.sound`, or no axioms. The hostile audit rejects `Classical.choice`,
project axioms, `sorry`, `admit`, native/SAT shortcuts, externalized constants,
wrong boundary roles, altered interface order, fixed-coordinate intervals,
host lookup, caller certificates, weakened semantics, missing saturation
composition, and downstream overclaims.

The durable checks are:

```bash
lake build PNP
lake env lean -DwarningAsError=true lean-audit/PNPResidualTerminalSupportExtractionAxiomAudit.lean
lake env lean -DwarningAsError=true lean-regression/PNPResidualTerminalSupportExtraction.lean
node --test audits/lean-residual-terminal-support-extraction0.test.mjs
```

## Generated publication evidence

Inventory coordinate `PNP-LEAN-THEOREM-INVENTORY-2026-08-05-103` records
24,211 declarations, 13,049 theorem-kind declarations, 6,927 assumption-free
theorems, 14,524 excluded private declarations, 219 source-closure modules,
and 2,183 reviewed milestone candidates. Its 13,945,316 canonical bytes have
SHA-256
`253dff68782561bf47e6a059233a3207aa73f5fab1e9dd05fc961af50f1912fb`;
the exact Lean source closure has SHA-256
`1dd96e3dacf0ce978270cdb494a25253a6d7f465eaa153937e8aaac06586983c`.

Publication-map coordinate `PNP-FORMAL-PUBLICATION-MAP-2026-08-05-103`
contains 83 milestones: 80 earned and three deliberately unearned. Its
709,628 bytes pin 2,183 exact kernel theorem types, including all 21 theorem
pins for this milestone, and have SHA-256
`da4a437c935e7c5072b09534669305d6876ac7d9b375cef34a08d9dbb4390480`.

Status coordinate `PNP-FORMAL-RECONSTRUCTION-STATUS-2026-08-05-103`, paired
with public-surface coordinate
`PUBLIC-SURFACE-BASELINE-2026-08-05-RESIDUAL-TERMINAL-SUPPORT-EXTRACTION-102`,
is 1,749,669 bytes with SHA-256
`0281e267926f6623d4cbb8f4e000a5c2ce4547602fa46bfcc40750903bfa9388`.
It retains all four project assumptions, all six blockers, unset activation
fingerprints, an absent `PNP.Main.p_eq_np`, and a false concrete publication
gate.

Canonical report coordinate
`PNP-CANONICAL-FORMAL-RECONSTRUCTION-REPORT-2026-08-05-103` has a 187,652-byte
TeX source with SHA-256
`50d1f6ea41f371510e0be86bd84dd33f535154228692dbe1ebcafb3ff5e47ca2`
and a deterministic 74-page, 430,495-byte A4 PDF with SHA-256
`a3db2479dbe5fe0620802bfdfcded79cbc1359ed62f65107b68e57e25fd897fa`.

## What remains open

This theorem accepts a finite terminal record list; it does not yet derive the
manuscript's complete profile frontier or prove that a selected support is a
proper positive support. It does not prove support completion in the full
governed sense, square legitimacy, the required projection square, or
`SaturatePositive`. Package E, BCEL/BN2–BN6, complete residual routing,
ZeroSlack, PCCMin, polynomial runtime, SAT in P, removal of the four project
assumptions, and `P = NP` remain open.

The next earned milestone must close a named proper-support or square
dependency on that finite path. Extracting another fixed slot or another
bounded circuit example would add regression coverage, not theorem progress.
