import PNP.Concrete.NormalizerCoefficientState
namespace PNP.Concrete.NormalizerBlocks
open BitRegister Occurrence
example (r : Coefficient.State) : Coefficient.indexWord .variableIndex r = r.variableIndex := rfl
example (r : Coefficient.State) : Coefficient.indexWord .row r = r.row := rfl
example (kind : CoefficientCache.Kind) (index : Coefficient.Index) (r : Coefficient.State) :
    (Coefficient.queried kind index r).data = r.data := Coefficient.queried_data kind index r
#print axioms Coefficient.liftCache_exec
#print axioms Coefficient.liftCore_exec
#print axioms Coefficient.liftDense_exec
#print axioms Coefficient.loadIndex_exec
#print axioms Coefficient.query_exec
#print axioms Coefficient.queried_data
#print axioms Coefficient.queried_buffers
#print axioms Coefficient.queried_indices
#print axioms Coefficient.queryFuel_bound
#print axioms Coefficient.queried_output_bound
#print axioms Coefficient.query_canonical
end PNP.Concrete.NormalizerBlocks
