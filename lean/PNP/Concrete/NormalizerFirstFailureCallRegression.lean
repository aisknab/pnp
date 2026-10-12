import PNP.Concrete.NormalizerFirstFailureCall
namespace PNP.Concrete.NormalizerBlocks
open BitRegister Occurrence
example : FirstFailure.find (fun _ => true) 0 4 = none := rfl
example : FirstFailure.find (fun i => i != 2) 0 5 = some 2 := rfl
example : FirstFailure.find (fun _ => false) 3 5 = some 3 := rfl
example (test : Nat → Bool) : FirstFailure.find test 0 0 = none := rfl
#print axioms FirstFailure.query_truth
#print axioms FirstFailure.scan_buffer
#print axioms FirstFailure.find_ofFn
#print axioms FirstFailure.start_exec
#print axioms FirstFailure.front_exec
#print axioms FirstFailure.finish_exec
#print axioms FirstFailure.call_exec
#print axioms FirstFailure.called_fields
#print axioms FirstFailure.called_canonical
#print axioms FirstFailure.callSteps_bound
end PNP.Concrete.NormalizerBlocks
