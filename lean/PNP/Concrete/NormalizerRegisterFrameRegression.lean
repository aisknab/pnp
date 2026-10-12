import PNP.Concrete.NormalizerRegisterFrame

namespace PNP.Concrete.NormalizerBlocks

open BitRegister

example {count extra : Nat} (core : Store count) (frame : Store extra) (i : Fin count) :
    (Frame.join core frame).get (Frame.index extra i) = core.get i := Frame.get_core core frame i
example {count extra : Nat} (core : Store count) (frame : Store extra) (i : Fin extra) :
    (Frame.join core frame).get (Frame.frameIndex count i) = frame.get i := Frame.get_frame core frame i
example {count extra : Nat} (core : Store count) (frame : Store extra) (operation : Action count) :
    (Frame.action extra operation).update (Frame.join core frame) =
      Frame.join (operation.update core) frame := Frame.action_update operation core frame
example {count extra : Nat} {body : Block count} {before after : Store count} {fuel : Nat}
    (checked : Exec body before fuel after) (frame : Store extra) :
    Exec (Frame.block extra body) (Frame.join before frame) fuel (Frame.join after frame) :=
  Frame.execution checked frame

#print axioms Frame.get_core
#print axioms Frame.set_core
#print axioms Frame.get_frame
#print axioms Frame.join_bounded
#print axioms Frame.action_update
#print axioms Frame.block_size
#print axioms Frame.execution

end PNP.Concrete.NormalizerBlocks
