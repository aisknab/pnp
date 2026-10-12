import PNP.Concrete.NormalizerCacheLiteralQuery
namespace PNP.Concrete.NormalizerBlocks
example (r : CacheLiteral.State) : (CacheLiteral.result r).registers.output.length = 1 :=
  CacheLiteral.result_sign_length r
example (r : CacheLiteral.State) (formula : List (List CNFLiteral)) (row : Nat)
    (literal : CNFLiteral) (rest : List CNFLiteral)
    (f : r.formula = GraphQuery.clauseData formula) (i : r.index = List.replicate row true)
    (s : r.remaining = []) (clause : formula[row]?.getD [] = literal::rest) :
    (CacheLiteral.result r).registers.output = [literal.positive] :=
  (CacheLiteral.canonical r formula row [] literal rest f i s clause).2
example (r : CacheLiteral.State) (n : Nat) (f : r.formula.length ≤ n)
    (i : r.index.length ≤ n) (s : r.remaining.length ≤ n) :
    CacheLiteral.fuel r ≤ CacheLiteral.bound.eval n := CacheLiteral.fuel_bound r n f i s
#print axioms CacheLiteral.bits_append
#print axioms CacheLiteral.readAt_exec
#print axioms CacheLiteral.atFuel_bound
#print axioms CacheLiteral.atRead_canonical
#print axioms CacheLiteral.emitSign_exec
#print axioms CacheLiteral.read_exec
#print axioms CacheLiteral.result_fields
#print axioms CacheLiteral.result_sign_length
#print axioms CacheLiteral.result_index_bound
#print axioms CacheLiteral.fuel_bound
#print axioms CacheLiteral.canonical
end PNP.Concrete.NormalizerBlocks
