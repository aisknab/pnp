import PNP.Concrete.NormalizerVertexEquality

namespace PNP.Concrete.NormalizerBlocks

example (c n : Nat) : LawfulBEq (Sum (Fin c) (Fin n)) :=
  ConstructiveVertexEquality.lawful c n

example (a b : Sum (Fin c) (Fin n)) (same : (a == b) = true) : a = b :=
  ConstructiveVertexEquality.equal a b same

#print axioms ConstructiveVertexEquality.lawful
#print axioms ConstructiveVertexEquality.equal
#print axioms ConstructiveVertexEquality.reflexive

end PNP.Concrete.NormalizerBlocks
