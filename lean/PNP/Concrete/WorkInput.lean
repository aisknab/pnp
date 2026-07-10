/-
Copyright (c) 2026 PNP Labs.

Exact pairing of raw input cells into the nine-symbol work alphabet.  The
canonical two-frame input has positive even length, so the work view neither
invents nor discards a raw cell.
-/

import PNP.Concrete.WorkMachine

namespace PNP.Concrete

/-- Group adjacent raw cells into work symbols.  An odd final cell is paired
with blank; the canonical paired-input path below proves that case unreachable. -/
def packWorkSymbols : List TapeSymbol → List WorkSymbol
  | [] => []
  | first :: [] => [⟨first, .blank⟩]
  | first :: second :: rest => ⟨first, second⟩ :: packWorkSymbols rest

@[simp] theorem packWorkSymbols_encodeWorkRight (symbols : List WorkSymbol) :
    packWorkSymbols (encodeWorkRight symbols) = symbols := by
  induction symbols with
  | nil => rfl
  | cons symbol rest ih =>
      change { first := symbol.first, second := symbol.second } ::
        packWorkSymbols (encodeWorkRight rest) = symbol :: rest
      have hSymbol : ({ first := symbol.first, second := symbol.second } : WorkSymbol) =
          symbol := by
        cases symbol
        rfl
      rw [hSymbol, ih]

theorem encodeWorkRight_append (left right : List WorkSymbol) :
    encodeWorkRight (left ++ right) = encodeWorkRight left ++ encodeWorkRight right := by
  induction left with
  | nil => rfl
  | cons symbol rest ih =>
      change symbol.first :: symbol.second :: encodeWorkRight (rest ++ right) =
        symbol.first :: symbol.second :: (encodeWorkRight rest ++ encodeWorkRight right)
      exact congrArg (List.cons symbol.first) (congrArg (List.cons symbol.second) ih)

/-- Constructive evenness witness used by the exact input bridge. -/
def EvenLength {α : Type} (items : List α) : Prop :=
  ∃ half, items.length = 2 * half

private theorem two_mul_succ (n : Nat) : 2 * (n + 1) = (2 * n) + 2 := by
  change 2 * (n + 1) = 2 * n + 2
  rw [Nat.mul_add]

theorem encodeWorkRight_packWorkSymbols (symbols : List TapeSymbol)
    (hEven : EvenLength symbols) :
    encodeWorkRight (packWorkSymbols symbols) = symbols := by
  rcases hEven with ⟨half, hLength⟩
  induction half generalizing symbols with
  | zero =>
      cases symbols with
      | nil => rfl
      | cons first rest =>
          change Nat.succ rest.length = 0 at hLength
          contradiction
  | succ half ih =>
      cases symbols with
      | nil =>
          rw [two_mul_succ] at hLength
          contradiction
      | cons first tail =>
          cases tail with
          | nil =>
              rw [two_mul_succ] at hLength
              have hImpossible : 0 = 2 * half + 1 := Nat.succ.inj hLength
              contradiction
          | cons second rest =>
              change first :: second :: encodeWorkRight (packWorkSymbols rest) =
                first :: second :: rest
              apply congrArg (List.cons first)
              apply congrArg (List.cons second)
              apply ih
              rw [two_mul_succ] at hLength
              exact Nat.succ.inj (Nat.succ.inj hLength)

theorem add_one_middle_eq_two_mul_add_one (n : Nat) :
    n + 1 + n = 2 * n + 1 := by
  rw [Nat.two_mul]
  rw [Nat.add_assoc]
  rw [Nat.add_comm 1 n]
  rw [← Nat.add_assoc]

private theorem add_four_reorder (a b c d : Nat) :
    (a + b) + (c + d) = (a + c) + (b + d) := by
  rw [Nat.add_assoc a b (c + d)]
  rw [← Nat.add_assoc b c d]
  rw [Nat.add_comm b c]
  rw [Nat.add_assoc c b d]
  rw [← Nat.add_assoc a c (b + d)]

theorem add_one_pairs (left right : Nat) :
    (left + 1 + left) + (right + 1 + right) =
      2 * (left + right + 1) := by
  rw [add_one_middle_eq_two_mul_add_one]
  rw [add_one_middle_eq_two_mul_add_one]
  rw [Nat.two_mul left, Nat.two_mul right]
  rw [Nat.two_mul (left + right + 1)]
  have hLeft := add_four_reorder (left + left) 1 (right + right) 1
  have hMiddle := add_four_reorder left left right right
  have hRight := add_four_reorder (left + right) 1 (left + right) 1
  exact hLeft.trans (congrArg (fun value => value + (1 + 1)) hMiddle) |>.trans hRight.symm

theorem pair_length_normalized (left right : BitString) :
    (BitString.pair left right).length =
      2 * (left.length + right.length + 1) := by
  have hSize := BitString.size_pair left right
  change (BitString.pair left right).length =
    (left.length + 1 + left.length) + (right.length + 1 + right.length) at hSize
  rw [hSize]
  exact add_one_pairs left.length right.length

theorem pair_length_positive_even (left right : BitString) :
    (BitString.pair left right).length ≠ 0 ∧
      EvenLength (BitString.pair left right) := by
  constructor
  · rw [pair_length_normalized]
    intro h
    have hPositive : 0 < left.length + right.length + 1 :=
      Nat.zero_lt_succ (left.length + right.length)
    have hTwicePositive : 0 < 2 * (left.length + right.length + 1) :=
      Nat.mul_pos (by decide) hPositive
    exact Nat.ne_of_gt hTwicePositive h
  · exact ⟨left.length + right.length + 1, pair_length_normalized left right⟩

theorem length_map_ofBool (bits : BitString) :
    (bits.map TapeSymbol.ofBool).length = bits.length := by
  induction bits with
  | nil => rfl
  | cons _ rest ih => exact congrArg Nat.succ ih

namespace WorkTape

/-- Focus a finite work-symbol word at its first symbol. -/
def ofSymbols : List WorkSymbol → WorkTape
  | [] => blank
  | symbol :: rest => { left := [], head := symbol, right := rest }

end WorkTape

private def rawInputSymbols (bits : BitString) : List TapeSymbol :=
  bits.map TapeSymbol.ofBool

/-- Work-tape view of a canonical paired bitstring input. -/
def pairedWorkTape (left right : BitString) : WorkTape :=
  WorkTape.ofSymbols
    (packWorkSymbols (rawInputSymbols (BitString.pair left right)))

theorem pairedWorkTape_eq_of_pack (left right : BitString)
    {first : WorkSymbol} {rest : List WorkSymbol}
    (hPack : packWorkSymbols (rawInputSymbols (BitString.pair left right)) =
      first :: rest) :
    pairedWorkTape left right =
      { left := [], head := first, right := rest } := by
  unfold pairedWorkTape
  rw [hPack]
  rfl

private theorem map_ofBool_nonempty {bits : BitString} (h : bits.length ≠ 0) :
    rawInputSymbols bits ≠ [] := by
  intro hEmpty
  have hLengths := congrArg List.length hEmpty
  change (rawInputSymbols bits).length = 0 at hLengths
  unfold rawInputSymbols at hLengths
  rw [length_map_ofBool] at hLengths
  exact h hLengths

private theorem map_ofBool_even {bits : BitString} (h : EvenLength bits) :
    EvenLength (rawInputSymbols bits) := by
  rcases h with ⟨half, hHalf⟩
  exact ⟨half, (length_map_ofBool bits).trans hHalf⟩

theorem packWorkSymbols_paired_ne_nil (left right : BitString) :
    packWorkSymbols (rawInputSymbols (BitString.pair left right)) ≠ [] := by
  have hPair := pair_length_positive_even left right
  have hRawNonempty : rawInputSymbols (BitString.pair left right) ≠ [] :=
    map_ofBool_nonempty hPair.1
  cases hRaw : rawInputSymbols (BitString.pair left right) with
  | nil => exact False.elim (hRawNonempty hRaw)
  | cons first rest =>
      cases rest with
      | nil =>
          change packWorkSymbols [first] ≠ []
          intro impossible
          contradiction
      | cons second tail =>
          change packWorkSymbols (first :: second :: tail) ≠ []
          intro impossible
          contradiction

private theorem tapeOfInput_eq_of_symbols {bits : BitString}
    {first second : TapeSymbol} {rest : List TapeSymbol}
    (hSymbols : rawInputSymbols bits = first :: second :: rest) :
    Tape.ofInput bits =
      { left := [], head := first, right := second :: rest } := by
  cases bits with
  | nil => contradiction
  | cons bit tail =>
      unfold rawInputSymbols at hSymbols
      have hFirst : TapeSymbol.ofBool bit = first :=
        congrArg List.head? hSymbols |> Option.some.inj
      have hTail : tail.map TapeSymbol.ofBool = second :: rest := by
        exact List.cons.inj hSymbols |>.2
      change Tape.mk [] (TapeSymbol.ofBool bit) (tail.map TapeSymbol.ofBool) =
        Tape.mk [] first (second :: rest)
      rw [hFirst, hTail]

theorem encodeWorkTape_pairedWorkTape (left right : BitString) :
    encodeWorkTape (pairedWorkTape left right) =
      Tape.ofInput (BitString.pair left right) := by
  have hPair := pair_length_positive_even left right
  have hEven : EvenLength (rawInputSymbols (BitString.pair left right)) :=
    map_ofBool_even hPair.2
  have hNonempty : rawInputSymbols (BitString.pair left right) ≠ [] :=
    map_ofBool_nonempty hPair.1
  cases hRaw : rawInputSymbols (BitString.pair left right) with
  | nil => exact False.elim (hNonempty hRaw)
  | cons first tail =>
      cases tail with
      | nil =>
          rcases hEven with ⟨half, hHalf⟩
          rw [hRaw] at hHalf
          cases half with
          | zero => contradiction
          | succ half =>
              have hTwo := two_mul_succ half
              rw [hTwo] at hHalf
              have hImpossible : 0 = 2 * half + 1 := Nat.succ.inj hHalf
              contradiction
      | cons second rest =>
          have hRestEven : EvenLength rest := by
            rcases hEven with ⟨half, hHalf⟩
            rw [hRaw] at hHalf
            cases half with
            | zero => contradiction
            | succ half =>
                refine ⟨half, ?_⟩
                have hTwo := two_mul_succ half
                rw [hTwo] at hHalf
                exact Nat.succ.inj (Nat.succ.inj hHalf)
          have hTailEncode : encodeWorkRight (packWorkSymbols rest) = rest :=
            encodeWorkRight_packWorkSymbols rest hRestEven
          have hTapeInput : Tape.ofInput (BitString.pair left right) =
              { left := [], head := first, right := second :: rest } :=
            tapeOfInput_eq_of_symbols hRaw
          unfold pairedWorkTape WorkTape.ofSymbols encodeWorkTape
          rw [hRaw]
          change Tape.mk [] first
              (second :: encodeWorkRight (packWorkSymbols rest)) =
            Tape.ofInput (BitString.pair left right)
          rw [hTailEncode, hTapeInput]

theorem startConfig_compileWorkMachine_paired (machine : WorkMachine)
    (left right : BitString) :
    startConfig (compileWorkMachine machine) (BitString.pair left right) =
      encodeWorkConfiguration
        (workStartConfiguration machine (pairedWorkTape left right)) := by
  unfold startConfig compileWorkMachine encodeWorkConfiguration
    workStartConfiguration
  rw [encodeWorkTape_pairedWorkTape]

end PNP.Concrete
