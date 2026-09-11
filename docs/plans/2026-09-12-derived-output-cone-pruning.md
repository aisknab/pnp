# M244: derived output-cone pruning

## Legacy anchor and dependency edge

The pinned manuscript's Package E structural-congruence and traceable-normalization
discussion (canonical report, R1 and the N1–N10 normalization list, especially N2)
requires deletion of unused physical structure. This milestone reconstructs the
physical NAND-gate subcase only. It does not identify physical output reachability
with the manuscript's complete metadata/profile support.

The dependency edge is: arbitrary finite direct-wire program and ordered output
word -> computed predecessor-closed output cone -> existing checked support
extraction -> equivalent smaller implementation with the original I/O shape ->
concrete PCCMin normalization stage.

## Unbounded construction and exact theorem boundary

For every `current : Implementation inputs outputs`, construct
`outputConeImplementation current : Implementation inputs outputs`.
Compute seeds from actual gate-valued outputs and dependencies from actual gate
sources. Instantiate the existing executable terminal saturation with only the
physical gate-source rule and an empty profile index type. This is explicitly a
physical-only system, not a replacement for the full-profile governance model.

Prove that the computed cone contains each output gate, is closed under actual
gate predecessors, and is contained in every gate set with those two properties.
Reuse `extractTerminalSupport`; do not duplicate its gate compiler. Prove that
the derived cone has no external gate-valued incoming boundary, rename its
remaining boundary inputs to the original primary inputs, and reconnect every
original output position, preserving constants, input wires and repeated outputs.

The central theorem has the exact shape:

```lean
theorem outputConeImplementation_equivalent {inputs outputs : Nat}
    (current : Implementation inputs outputs) :
    Equivalent (outputConeImplementation current).candidate.program
      (outputConeImplementation current).candidate.directWireWord
      current.candidate.program current.candidate.directWireWord
```

Also prove exact selected/deleted gate accounting, nonincrease of gate count,
invariance of `referenceMinimum`, exact residual-slack reduction by the deleted
gate count, and strict physical gain precisely when at least one gate is deleted.
Package the computed stage as a checked `PCCMinTotalNormalizer`. A no-deletion
branch does not assert semantic minimality or complete manuscript normal form.
No caller-supplied support, output coverage proof, optimizer or correctness
certificate is permitted in the public computation.

## Source/expectation contract map

- New Lean source and reviewed theorem set: exact universal type regressions,
  axiom transcript, root import, inventory producer/required-name consumer,
  publication fingerprint keys and durable read-only workflow block.
- Computed cone and adapter: fixtures for empty shapes, constant/input outputs,
  unused chains, shared predecessors and repeated ordered outputs. Include a
  circuit whose complete structural cone still has positive semantic slack.
- Claim boundary: source and hostile publication contracts reject supplied
  correctness, unconditional global claims, or profile-preservation credit.
- Canonical status, publication map, progress ledger and report: generate only
  after the final Lean source is stable; derive emitted hashes/counts from the
  compiled evidence and reconcile all current consumers before broad validation.

## Verification and release

Use one isolated remote checkout. Reuse the cache only after exact predecessor
tree/toolchain comparison. Run bounded changed-leaf checks and regressions first,
then the explicit root and exact axiom/type contracts, then seal the inventory.
Reconcile generated status/progress/current docs, run focused hostile checks,
build the report once with its built-in reproduction, and run one deduplicated
complete verification union. Preserve exact-object independent reproduction,
normal PR/post-merge CI and manual merge gates. Reanchor to the actual M243 merge
before publication; unchanged-tree heavy evidence is reusable.

All temporary artifacts remain scoped to this milestone and are removed after
its final release verification, or after an abandoned investigation is diagnosed.

## Remaining obligations and progress policy

This component does not prove full-profile/metadata preservation, a proper
Package E rewrite ledger, complete N1–N10 normalization, terminal-derived global
families, global routing, SaturatePositive, BCELReady, ZeroSlack, exact PCCMin or
uniform encoded-size polynomial runtime. Arbitrary supplied observers may
distinguish a physically pruned implementation; the M239 firewall remains active.
No semantic reference-minimum enumeration is executed by this pass.

Risk-weighted proof completion remains 40%, uncertainty 20%–40%, with zero of five
global gates closed unless a separate fixed checkpoint is actually discharged.
Publication-row coverage is independent; its next generated value is not assumed
as proof progress. PNPLabs publication is deferred: a physical normalization
component alone does not change the public end-to-end bottom line. Batch it with
a later major verified capability. Notify meaningful verified substeps separately.
