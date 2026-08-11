# V54 consumer-antichain normal form

This milestone reconstructs the pinned manuscript's theorem **V54,
consumer-antichain normal form** over an arbitrary finite carrier. It is the
mathematical edge between PkgC's separating-consumer conclusion and the
hyperedge cut indicator used by BN6.

The Lean module is
`lean/PNP/ResidualTerminalConsumerAntichainNormalForm.lean`.

## Exact theorem boundary

`TerminalV54ConsumerSystem` contains a finite duplicate-free carrier and a
finite antichain of duplicate-free, nonempty consumers. Every consumer is
contained in the carrier, and no listed consumer is extensionally contained
in a different listed consumer. The generated request is active on a cut
exactly when the cut contains a listed consumer.

Lean proves that this request is monotone, is false on the empty cut, and that
every listed consumer is inclusion-minimal among active sets. It then proves
both conclusions of manuscript V54:

1. two-sided activation is nonzero on some cut if and only if the minimal
   consumer antichain contains a disjoint pair; and
2. if every disjoint consumer pair is singleton-singleton, two-sided
   activation on every cut is exactly the Boolean cut indicator of
   `E = {a | [a] is a minimal consumer}`.

The second result is exported both as a proposition-level equivalence and as
literal equality of executable Boolean functions. No anchor cardinality or
cut coordinate is fixed.

## Verification

The hostile regression covers:

- a crossing pair of singleton consumers, where activation and the indicator
  are both true;
- a noncrossing cut, where both are false;
- a disjoint nonsingleton consumer pair, where activation is true but the
  singleton indicator is false, demonstrating that PkgC singletonization is
  indispensable; and
- intersecting minimal consumers, for which exhaustive finite cut search
  finds no active two-sided cut.

The axiom transcript prints every declaration in the module. The durable
source audit rejects assumptions, unsafe or noncomputable declarations,
classical shortcuts, weakened disjointness, erased antichain minimality, a
caller-supplied cut indicator, or removal of the singletonization premise.

## Deliberate nonclaims

This theorem consumes an explicit minimal-consumer antichain.
It does not yet construct PkgC request traces or restoration universes, prove global PkgC route
silence, derive the antichain from a terminal candidate, prove V53 or BN6,
establish polynomial runtime, prove ZeroSlack or PCCMin, put SAT in P, remove a
project-specific axiom, or prove `P = NP`.
