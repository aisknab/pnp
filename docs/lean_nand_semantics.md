# Lean direct-wire NAND semantics

`lean/PNP/NANDSemantics.lean` formalizes the Boolean direct-wire core used by the report. It is a
foundation for later enumeration, replacement, minimization, and locked-construction work; it does
not prove any of those later layers.

## Typed syntax

The module represents boundary valuations and multi-output Boolean functions with finite,
order-sensitive coordinates. A source is exactly one of:

- a positive boundary input;
- a Boolean carrier constant; or
- an earlier NAND-gate output.

Programs are built by appending one gate at a time. The source type for the appended gate contains
only the preceding gate indices, so a future or out-of-range gate reference cannot be constructed.
A direct-wire word stores the program separately from its ordered output wiring.

This separation implements the report's output convention: a word may expose a boundary input, a
constant, or any computed gate; it may repeat an output source; and none of those output choices adds
a NAND gate. Program size is the number of appended NAND gates.

The foundational syntax permits a zero-length output tuple. That keeps the semantic core closed
under ordinary finite-coordinate operations. Any later public enumerator intended to match the
legacy JavaScript candidate policy must impose its separate nonempty-output condition explicitly.

## Checked semantics

The module defines total evaluation for sources, programs, and words. The typed program evaluator
proves that appending a gate preserves every earlier value and that the new final value is the NAND
of its two sources. The word semantics then evaluates every ordered output source against the final
gate valuation.

The checked examples include:

- zero-gate positive projections and constants;
- repeated outputs without added gates;
- one-gate NAND;
- one-gate NAND-encoded negation; and
- two-gate NAND-encoded conjunction.

Extensional word equivalence is proved reflexive, symmetric, and transitive. These are Boolean
semantic facts only; no claim is made that the syntax is canonical or quotient-normalized.

## Axiom boundary

`DirectWireSemanticsCertificate` collects the foundational semantic laws. Run:

```bash
lake build PNP
lake env lean -DwarningAsError=true lean-audit/PNPNANDSemanticsAxiomAudit.lean
```

The dedicated audit prints no axioms for every explicit declaration in the module. The current
repository-wide inventory reports three project-specific axioms; M186 replaced
`PNP.LockedNANDThreshold` with the exact concrete encoded language definition.

## Not established here

This module does not formalize or prove:

- the report's carrier/profile record system;
- enumeration or completeness of bounded direct-wire words;
- minimum equivalent NAND size;
- compatible support extraction or replacement;
- the global residual-slack inequality;
- `G-Sep+`, cross-instance freshness, or the locked builder;
- baseline distinctness, trace equivalence, or the locked threshold theorem;
- correspondence with the historical JavaScript evaluator; or
- SAT membership, SAT hardness, or `P = NP`.

Boundary coordinate order is semantic. A future cross-language layer must give an explicit,
order-preserving correspondence between Lean `Fin` coordinates and any JavaScript name arrays.
Likewise, the locked builder must prove that carrier constants are not used as shortcuts for the
checked internal data constrained by `M0` and `M1`.
