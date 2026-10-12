import PNP.Concrete.NormalizerFirstFailureLoop
namespace PNP.Concrete.NormalizerBlocks
open BitRegister Occurrence
example (r : FirstFailure.State) : (FirstFailure.scan [] r).fuel = 1 := rfl
example (word : BitString) (r : FirstFailure.State) :
    (FirstFailure.scan word r).state.remaining = [] := (FirstFailure.scan_fields word r).2.2
example (word : BitString) (r : FirstFailure.State) :
    (FirstFailure.scan word r).state.core.matching = r.core.matching := (FirstFailure.scan_fields word r).2.1
#print axioms FirstFailure.scan_exec
#print axioms FirstFailure.scan_fields
#print axioms FirstFailure.scan_fuel_bound
#print axioms FirstFailure.whole_exec
#print axioms FirstFailure.whole_fuel_bound
end PNP.Concrete.NormalizerBlocks
