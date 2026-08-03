# Terminal full-carrier residual bridge

`lean/PNP/ResidualTerminalFullBridge.lean` reconstructs the direct-wire
specialization of the terminal whole-carrier bridge in §8 of the pinned legacy
report. The manuscript names the equality `RW-MuBridge` and immediately follows
it with the whole-span policy: a closed full word that represents the whole
circuit and uses fewer gates must give strict residual descent.

The Lean result is deliberately a semantic bridge, not the rest of the
manuscript's residual-witness engine.

## What “full” means here

A `TerminalFullRealization current` contains another whole implementation with
the same input and output arities and a proof that the two implementations agree
on every input and every output coordinate. It is not a sample, one selected
output, a truth-table digest supplied by a caller, or a projected equality.

`terminalize current` regards the whole implementation as its own realization.
Lean proves that this translation changes neither the implementation nor its
gate count. Forgetting the wrapper with `realize` preserves the complete
multi-output semantics.

This is the direct-wire counterpart of the manuscript's first three terminal
bridge obligations:

- the terminal carrier preserves semantics;
- terminalization preserves size; and
- a closed full word realizes the whole circuit.

The current theorem does not yet construct the manuscript's separate quotient
carrier or its quotient-to-full mode firewall. In this module, all constructive
realizations are full equalities from the outset.

## Independent minimum specification

`IsTerminalFullMinimum current n` is stated without mentioning the existing
exhaustive reference minimum. It requires both:

1. a complete terminal realization whose gate count is exactly `n`; and
2. a proof that `n` is no larger than the gate count of every complete terminal
   realization.

Lean then defines `terminalFullMinimum` using the already formalized exhaustive
reference realization and proves the independent minimum specification. It also
proves

```text
terminalFullMinimum current = referenceMinimum current
```

This is the direct-wire terminal `RW-MuBridge`. The two uniqueness theorems show
that a number satisfies the independent specification exactly when it equals
the terminal minimum, equivalently the exhaustive semantic reference minimum.

The proof is mathematical and exhaustive. It is not an efficient procedure for
finding the minimizing realization.

## Whole-span policy

A `WholeSpanResidualWitness current` is a complete terminal realization with a
strictly smaller gate count. Every such witness becomes the existing
`StrictEquivalentGain` object and therefore strictly decreases `residualSlack`.
Conversely, positive residual slack supplies a whole-span witness through the
exhaustive reference-minimum realization. Lean proves the exact equivalences

```text
0 < residualSlack current
  ↔ Nonempty (WholeSpanResidualWitness current)

residualSlack current = 0
  ↔ ¬Nonempty (WholeSpanResidualWitness current)
```

This closes the manuscript edge “whole-span cheaper word gives descent” for the
whole direct-wire implementation. It does not turn that witness into a local
support rewrite or an executable search result.

## Trust and regression boundary

The axiom transcript prints all 22 public declarations. The hostile audit fixes
the import closure and public surface, and rejects partial output semantics, a
minimum without the universal lower bound, a non-strict whole-span witness,
project axioms, `Classical.choice`, `sorry`, `admit`, native evaluation,
host-side lookup, caller certificates, and theorem overclaims.

The regression covers a zero-gate identity, a redundant one-gate identity with
a concrete strict whole-span witness, zero-input/zero-output semantics, two
output coordinates, exact terminalization, the independent minimum
specification, strict descent, and zero-slack stopping.

Run the focused checks only after building the root target:

```bash
lake build PNP
lake env lean -DwarningAsError=true lean-audit/PNPResidualTerminalFullBridgeAxiomAudit.lean
lake env lean -DwarningAsError=true lean-regression/PNPResidualTerminalFullBridge.lean
node --test audits/lean-residual-terminal-full-bridge0.test.mjs
```

## Exact non-claims

This milestone formalizes only the terminal full mode for complete direct-wire
semantics. It does not formalize the manuscript's quotient carrier, quotient
firewall, proper supports, governed local witnesses, `SaturatePositive`, rank
well-foundedness, BCEL-ready anchor extraction, the BCEL/BN2–BN6 packet and
selector layers, `PCCOracle`, the `ZeroSlack` certificate, route completeness,
or a polynomial runtime for finding or checking a minimum. It adds no
assumption and does not prove CNF-SAT is in P or `P = NP`.
