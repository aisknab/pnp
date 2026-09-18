import PNP.NANDGateRenamingEncoding

open PNP.DirectWire.StructuralReindexing

example (nodes : Nat) (relabeling : GateRenaming nodes) :
    GateRenaming.decode nodes (GateRenaming.encode relabeling) = some relabeling :=
  GateRenaming.decode_encode relabeling

example (nodes : Nat) (relabeling : GateRenaming nodes) :
    (GateRenaming.encode relabeling).length ≤ nodes :=
  GateRenaming.encode_length_le relabeling

example (nodes : Nat) (relabeling : GateRenaming nodes) :
    GateRenaming.validCode nodes (GateRenaming.encode relabeling) = true :=
  GateRenaming.validCode_encode relabeling

#print axioms GateRenaming.decode_encode
#print axioms GateRenaming.encode_length_le
#print axioms GateRenaming.validCode_encode

private def roundTrip (nodes : Nat) (raw : List (Nat × Nat)) : Bool :=
  match GateRenaming.decode nodes raw with
  | none => false
  | some original =>
      let encoded := GateRenaming.encode original
      decide (encoded.length ≤ nodes) && GateRenaming.validCode nodes encoded &&
        match GateRenaming.decode nodes encoded with
        | none => false
        | some decoded => (PNP.DirectWire.allFin nodes).all fun index =>
            decide (decoded.forward index = original.forward index) &&
            decide (decoded.backward index = original.backward index)

-- Runtime regression evidence only; the arbitrary-width theorems above are kernel checked.
#eval do
  let cases := [roundTrip 0 [], roundTrip 1 [], roundTrip 1 [(0, 0)],
    roundTrip 4 [(0, 1), (1, 2)], roundTrip 4 [(3, 1), (1, 0), (0, 2)],
    roundTrip 5 [(0, 4), (1, 3), (2, 2), (4, 1)]]
  if cases.all id then IO.println "GATE_RENAMING_ENCODING_RUNTIME_PASSED"
  else throw (IO.userError "gate renaming encoding round-trip failed")
