import PNP.Concrete.NormalizerBlocks

namespace PNP.Concrete.NormalizerBlocks

open BitRegister

example {count : Nat} (block : Block count) (base next : Nat) :
    (block.code base next).length = block.size := block.code_length base next
example {count : Nat} (block : Block count) : 0 < block.size := block.size_positive
example {count : Nat} (action : Action count) (store : Store count) :
    Exec (.action action) store 1 (action.update store) := .action action store
example {count : Nat} (store : Store count) :
    Exec (.seq .skip .skip) store 2 store := .seq (.skip store) (.skip store)
example {count : Nat} (source : Fin count) (body : Block count) (store : Store count)
    (empty : store.get source = []) : Exec (.loop source body) store 1 store := .loopStop empty

#print axioms Action.execute
#print axioms Block.code_length
#print axioms Block.size_positive
#print axioms Placed.full
#print axioms Placed.head
#print axioms Placed.prefix
#print axioms Placed.suffix
#print axioms Placed.tail
#print axioms branch_segments

end PNP.Concrete.NormalizerBlocks
