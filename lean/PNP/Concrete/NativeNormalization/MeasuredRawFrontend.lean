import PNP.Concrete.NativeNormalization.MeasuredRawCompiler

namespace PNP.Concrete.NativeNormalization.MeasuredRawFrontend

open PNP PNP.Concrete PNP.DirectWire PNP.DirectWire.LockedNANDTrace MeasuredReach

def index (inputs : Nat) : LockedNAND.RawSource → Nat
  | .input i => i
  | .constant false => inputs
  | .constant true => inputs+1
  | .gate i => inputs+2+i

theorem index_reification (s : Source n g) :
    index n (LockedNAND.RawSource.ofSource s) = NativeTseitin.sourceIndex s := by
  cases s with
  | input i => rfl
  | gate i => rfl
  | constant b => cases b <;> rfl

def gateData (n k : Nat) (g : LockedNAND.RawGate) : List (List CNFLiteral) :=
  let left := index n g.left
  let right := index n g.right
  let output := n+2+k
  [[⟨false,left⟩,⟨false,right⟩,⟨false,output⟩],
   [⟨true,left⟩,⟨true,output⟩,⟨true,output⟩],
   [⟨true,right⟩,⟨true,output⟩,⟨true,output⟩]]

theorem gateData_reification (g : Gate n k) :
    gateData n k (LockedNAND.RawGate.ofGate g) = NativeTseitin.gateClauses g := by
  simp only [gateData,LockedNAND.RawGate.ofGate,index_reification,NativeTseitin.gateClauses]

def clausesData (n : Nat) : Nat → List LockedNAND.RawGate → List (List CNFLiteral)
  | _,[] => []
  | k,g::gs => gateData n k g ++ clausesData n (k+1) gs

theorem clausesData_append (n k : Nat) (xs ys : List LockedNAND.RawGate) :
    clausesData n k (xs++ys) =
      clausesData n k xs++clausesData n (k+xs.length) ys := by
  induction xs generalizing k with
  | nil => simp only [List.nil_append,clausesData,List.length_nil,Nat.add_zero]
  | cons g xs ih =>
      have he : k+1+xs.length = k+(xs.length+1) := by omega
      simp only [List.cons_append,clausesData,ih,List.length_cons,List.append_assoc]
      rw [he]

theorem clausesData_reification (p : Program n g) :
    clausesData n 0 (LockedNAND.rawProgramGates p) = NativeTseitin.programClauses p := by
  induction p with
  | empty => rfl
  | @snoc count initial gate ih =>
      simp only [LockedNAND.rawProgramGates,clausesData_append,ih,
        LockedNAND.RawBuilder.rawProgramGates_length,Nat.zero_add,clausesData,
        List.append_nil,gateData_reification,NativeTseitin.programClauses]

def formulaData (r : LockedNAND.RawCircuit) : CNFFormula :=
  ⟨r.inputCount+2+r.gates.length,
    [NativeTseitin.unitClause r.inputCount false,
      NativeTseitin.unitClause (r.inputCount+1) true] ++
    clausesData r.inputCount 0 r.gates ++
    [NativeTseitin.unitClause (index r.inputCount r.output) true]⟩

theorem formulaData_reification (C : Circuit n) :
    formulaData (LockedNAND.RawCircuit.ofCircuit C) = NativeTseitin.formula C := by
  simp only [formulaData,LockedNAND.RawCircuit.ofCircuit,
    LockedNAND.RawBuilder.rawProgramGates_length,clausesData_reification,index,NativeTseitin.formula]

def source (n : Nat) (s : LockedNAND.RawSource) : Measured Nat := ⟨index n s,4⟩
theorem source_value (n : Nat) (s : LockedNAND.RawSource) : (source n s).value = index n s := rfl
theorem source_cost (n : Nat) (s : LockedNAND.RawSource) : (source n s).cost = 4 := rfl

def unit (i : Nat) (b : Bool) : Measured (List CNFLiteral) := ⟨NativeTseitin.unitClause i b,12⟩
theorem unit_value (i : Nat) (b : Bool) : (unit i b).value = NativeTseitin.unitClause i b := rfl
theorem unit_cost (i : Nat) (b : Bool) : (unit i b).cost = 12 := rfl

/-- Source indices are shared within the three fixed clauses, and every produced
list/literal constructor is covered by the fixed word-operation charge. -/
def gate (n k : Nat) (g : LockedNAND.RawGate) : Measured (List (List CNFLiteral)) :=
  let left := source n g.left
  let right := source n g.right
  let output := n+2+k
  ⟨[[⟨false,left.value⟩,⟨false,right.value⟩,⟨false,output⟩],
    [⟨true,left.value⟩,⟨true,output⟩,⟨true,output⟩],
    [⟨true,right.value⟩,⟨true,output⟩,⟨true,output⟩]],left.cost+right.cost+40⟩

theorem gate_value (n k : Nat) (g : LockedNAND.RawGate) : (gate n k g).value = gateData n k g := rfl
theorem gate_cost (n k : Nat) (g : LockedNAND.RawGate) : (gate n k g).cost = 48 := rfl
theorem gate_length (n k : Nat) (g : LockedNAND.RawGate) : (gate n k g).value.length = 3 := rfl

/-- Build forward from the raw gate list; append only the fixed three-clause prefix,
not an ever-growing accumulated clause list. -/
def gates (n : Nat) : Nat → List LockedNAND.RawGate → Measured (List (List CNFLiteral))
  | _,[] => ⟨[],1⟩
  | k,g::gs =>
      let head := gate n k g
      let tail := gates n (k+1) gs
      let joined := MeasuredCollections.append head.value tail.value
      ⟨joined.value,head.cost+tail.cost+joined.cost+3⟩

theorem gates_value (n k : Nat) (gs : List LockedNAND.RawGate) :
    (gates n k gs).value = clausesData n k gs := by
  induction gs generalizing k with
  | nil => rfl
  | cons g gs ih => simp only [gates,MeasuredCollections.append_value,gate_value,ih,clausesData]

theorem gates_length (n k : Nat) (gs : List LockedNAND.RawGate) :
    (gates n k gs).value.length = 3*gs.length := by
  induction gs generalizing k with
  | nil => rfl
  | cons g gs ih =>
      simp only [gates,MeasuredCollections.append_value,List.length_append,gate_length,
        ih,List.length_cons,Nat.mul_succ]
      omega

theorem gates_cost (n k : Nat) (gs : List LockedNAND.RawGate) :
    (gates n k gs).cost = 55*gs.length+1 := by
  induction gs generalizing k with
  | nil => rfl
  | cons g gs ih =>
      simp only [gates,MeasuredCollections.append_cost,gate_cost,gate_length,ih,List.length_cons]
      omega

def formula (r : LockedNAND.RawCircuit) : Measured CNFFormula :=
  let size := MeasuredAccess.length r.gates
  let zero := unit r.inputCount false
  let one := unit (r.inputCount+1) true
  let body := gates r.inputCount 0 r.gates
  let output := source r.inputCount r.output
  let last := unit output.value true
  let head := MeasuredCollections.append [zero.value,one.value] body.value
  let all := MeasuredCollections.append head.value [last.value]
  ⟨⟨r.inputCount+2+size.value,all.value⟩,
    size.cost+zero.cost+one.cost+body.cost+output.cost+last.cost+head.cost+all.cost+8⟩

theorem formula_value (r : LockedNAND.RawCircuit) : (formula r).value = formulaData r := by
  simp only [formula,formulaData,MeasuredAccess.length_value,unit_value,gates_value,
    source_value,MeasuredCollections.append_value,List.append_assoc]

theorem formula_cost (r : LockedNAND.RawCircuit) : (formula r).cost = 59*r.gates.length+56 := by
  simp only [formula,MeasuredAccess.length_cost,unit_cost,gates_cost,source_cost,
    MeasuredCollections.append_cost,MeasuredCollections.append_value,List.length_append,
    List.length_cons,List.length_nil,gates_length]
  omega

/-- The public exact compiler bridge supplies all raw data internally. -/
def build (F : CNFFormula) : Measured CNFFormula :=
  let compiled := MeasuredRawCompiler.build F
  let result := formula compiled.value
  ⟨result.value,compiled.cost+result.cost+1⟩

theorem build_value (F : CNFFormula) : (build F).value = NativeTseitin.frontend F := by
  simp only [build,formula_value,MeasuredRawCompiler.build_value,CNFToNAND.compileFormula,
    formulaData_reification,NativeTseitin.frontend]

theorem decoded_gate_bound (bits : BitString) (F : CNFFormula)
    (decoded : decodeEncodedCNF bits = some F) :
    (CNFToNAND.compileFormula F).gates.length ≤ 5*bits.length+1 := by
  have hg := CNFToNAND.compileFormula_gateCount_le F
  have he := CNFToNAND.formulaPlan_length_exact F
  have hp := CNFToNAND.formulaPlan_length_le_encoded_bits bits F decoded
  omega

def workPolynomial : NatPolynomial :=
  let size : NatPolynomial := .add (.mul (.constant 5) .variable) (.constant 1)
  .add (.add MeasuredRawCompiler.workPolynomial (.mul (.constant 59) size)) (.constant 57)

theorem workPolynomial_eval (m : Nat) :
    workPolynomial.eval m = MeasuredRawCompiler.workPolynomial.eval m+59*(5*m+1)+57 := rfl

theorem decoded_build_polynomial (bits : BitString) (F : CNFFormula)
    (decoded : decodeEncodedCNF bits = some F) :
    (build F).cost ≤ workPolynomial.eval bits.length := by
  have hc := MeasuredRawCompiler.decoded_build_polynomial bits F decoded
  have hg := decoded_gate_bound bits F decoded
  rw [workPolynomial_eval]
  simp only [build,formula_cost,MeasuredRawCompiler.build_value]
  omega

theorem build_satisfiable_iff (F : CNFFormula) : (build F).value.Satisfiable ↔ F.Satisfiable := by
  rw [build_value]
  exact NativeTseitin.frontend_satisfiable_iff F


end PNP.Concrete.NativeNormalization.MeasuredRawFrontend
