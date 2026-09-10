/-
Copyright (c) 2026 PNP Labs.

Physical access to a retained unary register from the represented input head.
A fixed scan reaches the active scratch end and one real transition launches
the existing preserved-register copier. The endpoint remains at the new scratch
end; it has not returned to the cursor or constructed a divider input.
-/

import PNP.Concrete.CookLevinBuilderCursorSource

namespace PNP.Concrete.CookLevin.BuilderRegisterAccess

open PipelineTape PipelineStateNamespace
open BuilderUnaryPolynomial

private def keep (source target : Nat) (symbol : WorkSymbol)
    (move : HeadMove) : WorkRule :=
  { sourceState := source, readSymbol := symbol, targetState := target,
    writeSymbol := symbol, move := move }

def seekRules : List WorkRule :=
  [keep 0 1 .blank .left, keep 0 1 .zeroBlank .left,
   keep 0 1 .oneBlank .left, keep 1 2 leftMarker .left,
   keep 2 2 unitSymbol .left, keep 2 2 separatorSymbol .left,
   keep 2 3 scratchEndSymbol .stay]

def seekMachine : WorkMachine :=
  { rules := seekRules, startState := 0, acceptState := 3, rejectState := 4 }

theorem seekRules_length : seekRules.length = 7 := rfl

theorem seekRules_pairwise_query_distinct :
    seekRules.Pairwise WorkMachineChain.QueryDistinct := by
  unfold WorkMachineChain.QueryDistinct
  decide

theorem seek_noRuleAtAccept : WorkMachineChain.NoRuleAtAccept seekMachine := by
  intro rule hRule
  change rule.sourceState ≠ 3
  change rule ∈ seekRules at hRule
  decide +revert

theorem registerWord_symbols (values : List Nat) :
    BuilderBalancedCursor.RegisterSymbols (registerWord values) := by
  unfold BuilderBalancedCursor.RegisterSymbols
  induction values with
  | nil => intro symbol hSymbol; contradiction
  | cons value rest ih =>
    intro symbol hSymbol
    simp only [registerWord, List.mem_cons, List.mem_append] at hSymbol
    rcases hSymbol with hSeparator | hUnit | hRest
    · exact Or.inr hSeparator
    · exact Or.inl (List.eq_of_mem_replicate hUnit)
    · exact ih symbol hRest

def sourceTape (head : WorkSymbol) (sourceTail word tail : List WorkSymbol) : WorkTape :=
  { left := leftMarker :: (word ++ scratchEndSymbol :: tail),
    head := head, right := sourceTail }

def endTape (head : WorkSymbol) (sourceTail word tail : List WorkSymbol) : WorkTape :=
  { left := tail, head := scratchEndSymbol,
    right := word.reverse ++ leftMarker :: head :: sourceTail }

def seekInitialConfiguration (head : WorkSymbol) (sourceTail word tail : List WorkSymbol) :
    WorkConfiguration :=
  { state := 0, tape := sourceTape head sourceTail word tail }

def seekFinalConfiguration (head : WorkSymbol) (sourceTail word tail : List WorkSymbol) :
    WorkConfiguration :=
  { state := 3, tape := endTape head sourceTail word tail }

private def leftFocus (left right : List WorkSymbol) : WorkTape :=
  match left with
  | [] => { left := [], head := .blank, right := right }
  | symbol :: rest => { left := rest, head := symbol, right := right }

private theorem scan_left (scanned tail right : List WorkSymbol)
    (hSymbols : BuilderBalancedCursor.RegisterSymbols scanned) :
    workRunExact? seekMachine scanned.length
        { state := 2, tape := leftFocus (scanned ++ scratchEndSymbol :: tail) right } =
      some { state := 2, tape :=
        { left := tail, head := scratchEndSymbol, right := scanned.reverse ++ right } } := by
  induction scanned generalizing right with
  | nil => rfl
  | cons symbol rest ih =>
    have hSymbol := hSymbols symbol List.mem_cons_self
    have hRest : BuilderBalancedCursor.RegisterSymbols rest := by
      intro item hItem
      exact hSymbols item (List.mem_cons_of_mem symbol hItem)
    have hStep : workStep? seekMachine
        { state := 2
          tape := {
            left := rest ++ scratchEndSymbol :: tail
            head := symbol
            right := right
          }
        } =
      some {
        state := 2
        tape := leftFocus (rest ++ scratchEndSymbol :: tail) (symbol :: right)
      } := by
      rcases hSymbol with hSymbol | hSymbol <;> subst symbol <;> rfl
    simp only [List.length_cons, List.cons_append, leftFocus, workRunExact?]
    rw [hStep]
    simpa only [List.reverse_cons, List.append_assoc, List.cons_append, List.nil_append]
      using ih (symbol :: right) hRest

theorem seek_workRunExact (head : WorkSymbol) (sourceTail word tail : List WorkSymbol)
    (hHead : head = .blank ∨ head = .zeroBlank ∨ head = .oneBlank)
    (hWord : BuilderBalancedCursor.RegisterSymbols word) :
    workRunExact? seekMachine (word.length + 3)
        (seekInitialConfiguration head sourceTail word tail) =
      some (seekFinalConfiguration head sourceTail word tail) := by
  let inside := leftMarker :: head :: sourceTail
  let middle : WorkConfiguration :=
    { state := 2, tape := leftFocus (word ++ scratchEndSymbol :: tail) inside }
  let atEnd : WorkConfiguration :=
    { state := 2, tape := endTape head sourceTail word tail }
  have hStart : workRunExact? seekMachine 2
      (seekInitialConfiguration head sourceTail word tail) = some middle := by
    rcases hHead with hHead | hHead | hHead <;> subst head <;> rfl
  have hScan : workRunExact? seekMachine word.length middle = some atEnd :=
    scan_left word tail inside hWord
  have hStop : workRunExact? seekMachine 1 atEnd =
      some (seekFinalConfiguration head sourceTail word tail) := by rfl
  have hFirst := PipelineMachineSimulation.workRunExact?_compose seekMachine
    2 word.length _ _ _ hStart hScan
  have hAll := PipelineMachineSimulation.workRunExact?_compose seekMachine
    (2 + word.length) 1 _ _ _ hFirst hStop
  have hLength : 2 + word.length + 1 = word.length + 3 := by omega
  rw [hLength] at hAll
  exact hAll

/-- The only input-independent parameter is the selected register's offset. -/
def machine (newerCount : Nat) : WorkMachine :=
  WorkMachineChain.machine seekMachine (RegisterCopy.machine newerCount)

theorem rules_pairwise_query_distinct (newerCount : Nat) :
    (machine newerCount).rules.Pairwise WorkMachineChain.QueryDistinct :=
  WorkMachineChain.rules_pairwise_query_distinct seekMachine (RegisterCopy.machine newerCount)
    seekRules_pairwise_query_distinct (RegisterCopy.rules_pairwise_query_distinct newerCount)
    seek_noRuleAtAccept

theorem noRuleAtAccept (newerCount : Nat) : WorkMachineChain.NoRuleAtAccept (machine newerCount) := by
  apply WorkMachineChain.noRuleAtAccept
  intro rule hRule
  exact Nat.ne_of_lt (RegisterCopy.rule_source_lt_acceptState newerCount rule hRule)

theorem machine_acceptState_ne_rejectState (newerCount : Nat) :
    (machine newerCount).acceptState ≠ (machine newerCount).rejectState :=
  WorkMachineChain.machine_acceptState_ne_rejectState seekMachine (RegisterCopy.machine newerCount)
    (RegisterCopy.machine_acceptState_ne_rejectState newerCount)

def encodedWord (older : List WorkSymbol) (sourceValue : Nat) (newer : List Nat) :
    List WorkSymbol :=
  older ++ registerWord ([sourceValue] ++ newer)

def initialConfiguration (head : WorkSymbol) (sourceTail older : List WorkSymbol)
    (sourceValue : Nat) (newer : List Nat) (tail : List WorkSymbol) : WorkConfiguration :=
  renameConfiguration WorkMachineChain.firstState
    (seekInitialConfiguration head sourceTail (encodedWord older sourceValue newer) tail)

def finalConfiguration (head : WorkSymbol) (sourceTail older : List WorkSymbol)
    (sourceValue : Nat) (newer : List Nat) (tail : List WorkSymbol) : WorkConfiguration :=
  renameConfiguration WorkMachineChain.secondState
    (RegisterCopy.finalConfiguration older (leftMarker :: head :: sourceTail) tail sourceValue newer)

theorem initialConfiguration_state (head : WorkSymbol) (sourceTail older : List WorkSymbol)
    (sourceValue : Nat) (newer : List Nat) (tail : List WorkSymbol) :
    (initialConfiguration head sourceTail older sourceValue newer tail).state =
      (machine newer.length).startState := rfl

theorem finalConfiguration_state (head : WorkSymbol) (sourceTail older : List WorkSymbol)
    (sourceValue : Nat) (newer : List Nat) (tail : List WorkSymbol) :
    (finalConfiguration head sourceTail older sourceValue newer tail).state =
      (machine newer.length).acceptState := by
  change WorkMachineChain.secondState (RegisterCopy.stateCount newer.length) =
    WorkMachineChain.secondState ((RegisterCopy.machine newer.length).acceptState)
  rw [RegisterCopy.machine_acceptState]

def workSteps (older : List WorkSymbol) (sourceValue : Nat) (newer : List Nat) : Nat :=
  (encodedWord older sourceValue newer).length + 3 + 1 + RegisterCopy.steps newer sourceValue

theorem workRunExact (head : WorkSymbol) (sourceTail older : List WorkSymbol)
    (sourceValue : Nat) (newer : List Nat) (tail : List WorkSymbol)
    (hHead : head = .blank ∨ head = .zeroBlank ∨ head = .oneBlank)
    (hOlder : BuilderBalancedCursor.RegisterSymbols older) :
    workRunExact? (machine newer.length) (workSteps older sourceValue newer)
        (initialConfiguration head sourceTail older sourceValue newer tail) =
      some (finalConfiguration head sourceTail older sourceValue newer tail) := by
  have hWord : BuilderBalancedCursor.RegisterSymbols (encodedWord older sourceValue newer) := by
    intro symbol hMem
    rcases List.mem_append.mp hMem with hOld | hNew
    · exact hOlder symbol hOld
    · exact registerWord_symbols ([sourceValue] ++ newer) symbol hNew
  have hSeek := seek_workRunExact head sourceTail (encodedWord older sourceValue newer) tail
    hHead hWord
  have hCopy := RegisterCopy.workRunExact older (leftMarker :: head :: sourceTail) tail
    sourceValue newer
  exact WorkMachineChain.workRunExact seekMachine (RegisterCopy.machine newer.length)
    ((encodedWord older sourceValue newer).length + 3) (RegisterCopy.steps newer sourceValue)
    (seekInitialConfiguration head sourceTail (encodedWord older sourceValue newer) tail)
    (seekFinalConfiguration head sourceTail (encodedWord older sourceValue newer) tail)
    (RegisterCopy.finalConfiguration older (leftMarker :: head :: sourceTail) tail sourceValue newer)
    hSeek rfl hCopy

theorem run_compile_exact (head : WorkSymbol) (sourceTail older : List WorkSymbol)
    (sourceValue : Nat) (newer : List Nat) (tail : List WorkSymbol)
    (hHead : head = .blank ∨ head = .zeroBlank ∨ head = .oneBlank)
    (hOlder : BuilderBalancedCursor.RegisterSymbols older) :
    run (compileWorkMachine (machine newer.length)) (6 * workSteps older sourceValue newer)
        (encodeWorkConfiguration (initialConfiguration head sourceTail older sourceValue newer tail)) =
      encodeWorkConfiguration (finalConfiguration head sourceTail older sourceValue newer tail) :=
  run_compileWorkMachine_mul_of_workRunExact _ _ _ _
    (workRunExact head sourceTail older sourceValue newer tail hHead hOlder)

theorem workSteps_le (older : List WorkSymbol) (sourceValue : Nat) (newer : List Nat)
    (bound : Nat) (hSpan : (encodedWord older sourceValue newer).length ≤ bound) :
    workSteps older sourceValue newer ≤
      bound + 4 + (4 * (bound + 1) * (bound + 1) + 9 * (bound + 1) + 5) := by
  have hLength : (encodedWord older sourceValue newer).length =
      older.length + 1 + sourceValue + newer.length + newer.sum := by
    simp [encodedWord, registerWord_length] <;> omega
  have hSource : sourceValue ≤ bound := by omega
  have hNewer : newer.length + newer.sum ≤ bound := by omega
  have hCopy := RegisterCopy.steps_le newer sourceValue bound hSource hNewer
  unfold workSteps
  omega

end PNP.Concrete.CookLevin.BuilderRegisterAccess
