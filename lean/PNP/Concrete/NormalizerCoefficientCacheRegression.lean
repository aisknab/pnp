import PNP.Concrete.NormalizerCoefficientCache
namespace PNP.Concrete.NormalizerBlocks
open BitRegister Occurrence
example (r : CoefficientCache.State) : CoefficientCache.table .owner r = r.matching := rfl
example (r : CoefficientCache.State) : CoefficientCache.table .slot r = r.counter := rfl
example (r : CoefficientCache.State) : CoefficientCache.table .mode r = r.target := rfl
example (kind : CoefficientCache.Kind) (r : CoefficientCache.State) :
    (CoefficientCache.result kind r).core.core.buffer = r.core.core.buffer :=
  (CoefficientCache.result_fields kind r).2.2.2.2.1
#print axioms CoefficientCache.readMode_exec
#print axioms CoefficientCache.modeFuel_bound
#print axioms CoefficientCache.modeRead_output_bound
#print axioms CoefficientCache.modeRead_canonical
#print axioms CoefficientCache.read_exec
#print axioms CoefficientCache.result_fields
#print axioms CoefficientCache.fuel_bound
#print axioms CoefficientCache.output_bound
#print axioms CoefficientCache.canonical
end PNP.Concrete.NormalizerBlocks
