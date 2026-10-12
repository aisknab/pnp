import PNP.Concrete.NormalizerVertexRange

namespace PNP.Concrete.NormalizerBlocks

example (tag : Bool) (r : Occurrence.Registers) :
    Exec (SearchVertices.loop tag) r.store (SearchVertices.whole tag r).fuel
      (SearchVertices.whole tag r).state.store := SearchVertices.whole_exec tag r
example (tag : Bool) (r : Occurrence.Registers) :
    (SearchVertices.whole tag r).state.input = r.input := SearchVertices.whole_input tag r
example (tag : Bool) (r : Occurrence.Registers) :
    (SearchVertices.whole tag r).state.excess =
      (SearchVertices.rangeBits tag r.remaining.length r.target.length).reverse ++ r.excess :=
  SearchVertices.whole_excess tag r
example (tag : Bool) (r : Occurrence.Registers) :
    (SearchVertices.whole tag r).fuel ≤
      (4 * (r.target.length + r.remaining.length) + 13) * r.remaining.length + 1 :=
  SearchVertices.whole_fuel_bound tag r

#print axioms SearchVertices.run_exec
#print axioms SearchVertices.run_input
#print axioms SearchVertices.run_stopped
#print axioms SearchVertices.run_excess
#print axioms SearchVertices.run_target_length
#print axioms SearchVertices.run_fuel_bound
#print axioms SearchVertices.whole_exec
#print axioms SearchVertices.whole_input
#print axioms SearchVertices.whole_excess
#print axioms SearchVertices.whole_fuel_bound

end PNP.Concrete.NormalizerBlocks
