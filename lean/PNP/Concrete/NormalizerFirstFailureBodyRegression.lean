import PNP.Concrete.NormalizerFirstFailureBody
namespace PNP.Concrete.NormalizerBlocks
open BitRegister Occurrence
example (r : FirstFailure.State) : (FirstFailure.stopped r).remaining = [] := rfl
example (r : FirstFailure.State) : (FirstFailure.stopped r).buffer = true::r.counter := rfl
example (r : FirstFailure.State) : (FirstFailure.queried r).core.matching = r.core.matching :=
  (FirstFailure.queried_fields r).2.1
#print axioms FirstFailure.query_exec
#print axioms FirstFailure.stop_exec
#print axioms FirstFailure.decideNext_exec
#print axioms FirstFailure.body_exec
#print axioms FirstFailure.body_fields
#print axioms FirstFailure.body_remaining
#print axioms FirstFailure.body_counter
#print axioms FirstFailure.body_buffer
#print axioms FirstFailure.bodyFuel_bound
end PNP.Concrete.NormalizerBlocks
