import GeneralizedDecoratedSemantics

/-! Exact images of correlated factors under the physical deletion scan.
The proofs use the executable scan already linked to the literal machine,
not finite examples or an assumed closure specification. -/
namespace StackSorting.Generalized
namespace Decorated
open Coordinates

abbrev Binary (digits : List Nat) : Prop := ∀ digit ∈ digits, digit ≤ 1
abbrev BoundedDigits (digits : List Nat) : Prop := ∀ digit ∈ digits, digit < 3

theorem Factor.denotes_bounded {factor : Factor} {digits : List Nat}
    (h : factor.denotes digits) : BoundedDigits digits := by
  cases factor with
  | Z => subst digits; simp [BoundedDigits]
  | O => subst digits; simp [BoundedDigits]
  | B => rcases h with rfl | rfl <;> simp [BoundedDigits]
  | T => rcases h with rfl | rfl | rfl <;> simp [BoundedDigits]
  | C size => exact fun digit hd => by have := h.2.1 digit hd; omega

theorem denotes_bounded {state : State} {digits : List Nat}
    (h : denotes state digits) : BoundedDigits digits := by
  induction state generalizing digits with
  | nil => subst digits; simp [BoundedDigits]
  | cons factor state ih =>
    obtain ⟨left, right, hl, hr, rfl⟩ := h
    intro digit hd
    rcases List.mem_append.mp hd with hd | hd
    · exact Factor.denotes_bounded hl digit hd
    · exact ih hr digit hd

theorem scan_two_nonempty {digits : List Nat} (hn : digits ≠ [])
    (hb : BoundedDigits digits) : scan 3 2 digits = none := by
  cases digits with
  | nil => exact (hn rfl).elim
  | cons head rest => exact scan_three_two_cons (hb head (by simp)) rest

/-- After a binary digit from live state one, only the empty tail can remain. -/
theorem scan_one_binary_head {digit : Nat} (hb : digit ≤ 1) (tail : List Nat)
    (bounded : BoundedDigits tail) :
    scan 3 1 (digit :: tail) = if tail = [] then some [digit] else none := by
  have ha : advance digit 1 = 2 := by simp [advance, hb]
  have hr : retained digit 1 = digit := by simp [retained, hb]
  simp only [scan, Nat.reduceLT, ite_true, ha, hr]
  by_cases he : tail = []
  · simp [he, scan]
  · rw [scan_two_nonempty he bounded]
    simp [he]

theorem scan_zero_ones_append (n : Nat) (tail : List Nat) :
    scan 3 0 (List.replicate n 1 ++ tail) =
      (scan 3 0 tail).map (List.replicate n 0 ++ ·) := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [List.replicate_succ, List.cons_append, scan_three_zero_one, ih,
      Option.map_map, Function.comp_def]

/-- With a nonempty bounded suffix, a successful correlated binary prefix
must have its first zero in its final coordinate. The exact output prefix is
all zeros and the suffix begins in scanner state one. -/
theorem scan_clause_nonempty_tail {block tail : List Nat}
    (binary : Binary block) (hasZero : 0 ∈ block)
    (tailNonempty : tail ≠ []) (tailBounded : BoundedDigits tail) :
    scan 3 0 (block ++ tail) =
      if block = List.replicate (block.length-1) 1 ++ [0] then
        (scan 3 1 tail).map (List.replicate block.length 0 ++ ·)
      else none := by
  induction block with
  | nil => simp at hasZero
  | cons digit rest ih =>
    have hd : digit ≤ 1 := binary digit (by simp)
    have hrest : Binary rest := fun a ha => binary a (by simp [ha])
    have casesDigit : digit = 0 ∨ digit = 1 := by omega
    rcases casesDigit with rfl | rfl
    · cases rest with
      | nil => simp [scan_three_zero_zero]
      | cons a rest =>
        have ha : a ≤ 1 := hrest a (by simp)
        have hb : BoundedDigits (rest ++ tail) := by
          intro x hx
          rcases List.mem_append.mp hx with hx | hx
          · have := hrest x (by simp [hx]); omega
          · exact tailBounded x hx
        have hn : rest ++ tail ≠ [] := by
          intro h
          exact tailNonempty (List.append_eq_nil_iff.mp h).2
        have hs := scan_one_binary_head ha (rest ++ tail) hb
        simp only [List.cons_append, scan_three_zero_zero]
        rw [hs]
        simp [hn, List.replicate_succ]
    · have hz : 0 ∈ rest := by simpa using hasZero
      have he : rest ≠ [] := by intro h; simp [h] at hz
      have shape : (1 :: rest = List.replicate rest.length 1 ++ [0]) ↔
          rest = List.replicate (rest.length-1) 1 ++ [0] := by
        cases rest with
        | nil => exact (he rfl).elim
        | cons a rest => simp [List.replicate_succ]
      simp only [List.cons_append, scan_three_zero_one, ih hrest hz,
        List.length_cons, Nat.add_sub_cancel, shape]
      by_cases hs : rest = List.replicate (rest.length-1) 1 ++ [0]
      · simp only [ite_eq_left hs, Option.map_map, Function.comp_def, List.replicate_succ]
        rfl
      · simp only [ite_eq_right hs, Option.map_none]

/-- A nonempty binary clause can only emit zeros, except possibly for its
last output digit. This statement covers arbitrary clause length. -/
theorem scan_clause_shape {block output : List Nat}
    (binary : Binary block) (hasZero : 0 ∈ block)
    (accepted : scan 3 0 block = some output) :
    ∃ last, last ≤ 1 ∧ output = List.replicate (block.length-1) 0 ++ [last] := by
  induction block generalizing output with
  | nil => simp at hasZero
  | cons digit rest ih =>
    have hd : digit ≤ 1 := binary digit (by simp)
    have hrest : Binary rest := fun a ha => binary a (by simp [ha])
    have casesDigit : digit = 0 ∨ digit = 1 := by omega
    rcases casesDigit with rfl | rfl
    · cases rest with
      | nil =>
        have ho : output = [0] := by simpa [scan, advance, retained] using accepted.symm
        exact ⟨0, by omega, by simp [ho]⟩
      | cons a rest =>
        have ha : a ≤ 1 := hrest a (by simp)
        have hb : BoundedDigits rest := fun x hx => by have := hrest x (by simp [hx]); omega
        rw [scan_three_zero_zero, scan_one_binary_head ha rest hb] at accepted
        by_cases he : rest = []
        · simp only [he, ite_true, Option.map_some, Option.some.injEq] at accepted
          subst output
          exact ⟨a, ha, by simp [he]⟩
        · simp [he] at accepted
    · have hz : 0 ∈ rest := by simpa using hasZero
      rw [scan_three_zero_one, Option.map_eq_some_iff] at accepted
      obtain ⟨tailOutput, ht, rfl⟩ := accepted
      obtain ⟨last, hl, ho⟩ := ih hrest hz ht
      have hlen : rest.length = (rest.length-1)+1 := by
        have hn : rest ≠ [] := by intro h; simp [h] at hz
        have hp : 0 < rest.length := List.length_pos_iff.mpr hn
        omega
      refine ⟨last, hl, ?_⟩
      simp only [List.length_cons, Nat.add_sub_cancel, ho]
      rw [hlen, List.replicate_succ]
      rfl

theorem denotes_singleton (factor : Factor) (digits : List Nat) :
    denotes [factor] digits ↔ factor.denotes digits := by
  simp [denotes]

theorem denotes_replicate_Z (n : Nat) (digits : List Nat) :
    denotes (List.replicate n Factor.Z) digits ↔ digits = List.replicate n 0 := by
  induction n generalizing digits with
  | zero => rfl
  | succ n ih => simp [List.replicate_succ, denotes, Factor.denotes, ih]

theorem zeroEnding_clause (m : Nat) (hm : 0 < m) :
    (Factor.C m).denotes (List.replicate (m-1) 1 ++ [0]) := by
  refine ⟨?_, ?_, by simp⟩
  · simp; omega
  · intro digit hd
    simp only [List.mem_append, List.mem_replicate, List.mem_singleton] at hd
    rcases hd with ⟨_, rfl⟩ | rfl <;> omega

/-- Exact C_m image with a nonempty following factor word. -/
theorem ScanImage_C_nonempty {m : Nat} {state : State} {output : List Nat}
    (hm : 0 < m) (nonempty : 0 < height state) :
    ScanImage 0 (.C m :: state) output ↔
      ∃ tail, ScanImage 1 state tail ∧ output = List.replicate m 0 ++ tail := by
  constructor
  · rintro ⟨digits, ⟨block, inputTail, hc, ht, rfl⟩, hs⟩
    have htne : inputTail ≠ [] := by
      intro he
      have hl := denotes_length ht
      simp [he] at hl
      omega
    rw [scan_clause_nonempty_tail hc.2.1 hc.2.2 htne (denotes_bounded ht)] at hs
    split at hs
    next hshape =>
      obtain ⟨tail, hscan, he⟩ := Option.map_eq_some_iff.mp hs
      exact ⟨tail, ⟨inputTail, ht, hscan⟩, by simpa [hc.1] using he.symm⟩
    next hshape => simp at hs
  · rintro ⟨tail, ⟨inputTail, ht, hscan⟩, rfl⟩
    let block := List.replicate (m-1) 1 ++ [0]
    have hc : (Factor.C m).denotes block := zeroEnding_clause m hm
    refine ⟨block ++ inputTail, ⟨block, inputTail, hc, ht, rfl⟩, ?_⟩
    have htne : inputTail ≠ [] := by
      intro he
      have hl := denotes_length ht
      simp [he] at hl
      omega
    rw [scan_clause_nonempty_tail hc.2.1 hc.2.2 htne (denotes_bounded ht)]
    have hshape : block = List.replicate (block.length-1) 1 ++ [0] := by
      rw [hc.1]
    rw [ite_eq_left hshape, hc.1, hscan]
    rfl

/-- A correlated block of at least two binary coordinates never survives
from suffix-scanner state one, irrespective of the following factor word. -/
theorem ScanImage_one_C {m : Nat} {state : State} {output : List Nat}
    (hm : 2 ≤ m) : ¬ ScanImage 1 (.C m :: state) output := by
  rintro ⟨digits, ⟨block, inputTail, hc, ht, rfl⟩, hs⟩
  cases block with
  | nil => simp [Factor.denotes] at hc
  | cons a rest =>
    cases rest with
    | nil => have hl := hc.1; simp at hl; omega
    | cons b rest =>
      have ha : a ≤ 1 := hc.2.1 a (by simp)
      have bounded : BoundedDigits (b :: rest ++ inputTail) := by
        intro digit hd
        rcases List.mem_append.mp hd with hd | hd
        · have := hc.2.1 digit (by simp [hd]); omega
        · exact denotes_bounded ht digit hd
      simp only [List.cons_append] at hs
      have hscan := scan_one_binary_head ha (b :: rest ++ inputTail) bounded
      simp only [List.cons_append] at hscan
      rw [hscan] at hs
      simp at hs

/-- The terminal correlated factor has exactly the Z^(m-1) B image.
This includes both possible final output digits, without counting preimages. -/
theorem ScanImage_C_empty {m : Nat} {output : List Nat} (hm : 2 ≤ m) :
    ScanImage 0 [.C m] output ↔
      denotes (List.replicate (m-1) .Z ++ [.B]) output := by
  constructor
  · rintro ⟨block, hc, hs⟩
    have hc' := (denotes_singleton (.C m) block).mp hc
    obtain ⟨last, hl, ho⟩ := scan_clause_shape hc'.2.1 hc'.2.2 hs
    apply (denotes_append _ _ _).mpr
    refine ⟨List.replicate (m-1) 0, [last], (denotes_replicate_Z _ _).mpr rfl, ?_, ?_⟩
    · apply (denotes_singleton .B [last]).mpr
      have hd : last = 0 ∨ last = 1 := by omega
      rcases hd with rfl | rfl <;> simp [Factor.denotes]
    · simpa [hc'.1] using ho
  · intro hd
    obtain ⟨zeros, last, hz, hl, rfl⟩ := (denotes_append _ _ _).mp hd
    have hzeros := (denotes_replicate_Z _ _).mp hz
    subst zeros
    have hlast := (denotes_singleton .B last).mp hl
    rcases hlast with rfl | rfl
    · let block := List.replicate (m-1) 1 ++ [0]
      refine ⟨block, (denotes_singleton _ _).mpr (zeroEnding_clause m (by omega)), ?_⟩
      simp only [block, scan_zero_ones_append]
      simp [scan, advance, retained]
    · let block := List.replicate (m-2) 1 ++ [0,1]
      have hc : (Factor.C m).denotes block := by
        refine ⟨?_, ?_, by simp [block]⟩
        · simp [block]; omega
        · intro digit hd
          simp only [block, List.mem_append, List.mem_replicate, List.mem_cons,
            List.not_mem_nil, or_false] at hd
          rcases hd with ⟨_, rfl⟩ | rfl | rfl <;> omega
      refine ⟨block, (denotes_singleton _ _).mpr hc, ?_⟩
      simp only [block, scan_zero_ones_append]
      have he : m-1 = (m-2)+1 := by omega
      simp [scan, advance, retained, he, List.replicate_succ', List.append_assoc]

#print axioms scan_clause_nonempty_tail
#print axioms scan_clause_shape
#print axioms ScanImage_C_nonempty
#print axioms ScanImage_one_C
#print axioms ScanImage_C_empty

end Decorated
end StackSorting.Generalized
