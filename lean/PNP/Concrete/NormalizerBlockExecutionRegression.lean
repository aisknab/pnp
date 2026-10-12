import PNP.Concrete.NormalizerBlockExecution

namespace PNP.Concrete.NormalizerBlocks

open BitRegister

example {count : Nat} {block : Block count} {before after : Store count} {fuel : Nat}
    (checked : Exec block before fuel after) (p : Program count) (base next : Nat)
    (placed : Placed p base (block.code base next)) :
    BitRegister.run p fuel ⟨.running base, before⟩ = ⟨.running next, after⟩ :=
  checked.run p base next placed
example {count : Nat} {block : Block count} {before after : Store count} {fuel : Nat}
    (checked : Exec block before fuel after) (bound : Nat) (bounded : before.Bounded bound) :
    after.Bounded (bound + fuel) := checked.bounded bound bounded
example {count : Nat} {block : Block count} {before after : Store count} {fuel : Nat}
    (checked : Exec block before fuel after) (input output : Fin count) :
    BitRegister.run (block.program input output) (fuel + 1) ⟨.running 0, before⟩ = ⟨.accepted, after⟩ :=
  checked.program_run input output
example (bits : BitString) :
    BitRegister.run ((Block.action (.pop (0 : Fin 1))).program 0 0) 2
      ⟨.running 0, .cons bits .nil⟩ = ⟨.accepted, .cons bits.tail .nil⟩ :=
  (Exec.action (.pop 0) (.cons bits .nil)).program_run 0 0

#print axioms single_step
#print axioms branch_empty
#print axioms branch_zero
#print axioms branch_one
#print axioms Exec.run
#print axioms Exec.bounded
#print axioms Block.program_placed
#print axioms Block.program_accept
#print axioms Exec.program_run

end PNP.Concrete.NormalizerBlocks
