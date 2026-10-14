import EqualPrefix

/-! The `M`-phase of the prefix (Section 5.1 steps 4-5 and Section 5.4 cases
(P3), (P4), (P5), (P7) and `C` deleted), after the standard low phase
`std_qphase`: the stack is `E's ++ [P]`, the next value is `C = 3r-2`, and
`2r-1` values have been output. -/
namespace StackSorting.Generalized
namespace Equal
open BasisFamily (delete)
open Unequal (readCount)

variable {r d : Nat}

theorem readCount_le' (d next : Nat) : readCount d next ≤ next := by
  unfold readCount; split <;> omega

/-- No deletion among `C, U, M1, V, M2, E_1`: `C` goes below `P`, `U` and then
`V` just above `C`; the result is regime S. -/
theorem mphase_std (hr : 3 ≤ r) {out rem : List Nat}
    (h : Prog r d (3*r-2) [] [r-1] out ([3*r, r-1, 3*r+2, 3*r-1, r+2] ++ rem))
    (hlen : out.length = 2*r-1) (hd1 : d ≠ 3*r-2) (hd2 : d ≠ 3*r-1) (hd3 : d ≠ 3*r)
    (hd4 : d ≠ 3*r+1) (hd5 : d ≠ 3*r+2) (hd6 : d ≠ r+2) :
    Prog r d (3*r+3) [] [3*r-2] (out ++ [3*r, r-1, 3*r+2, 3*r-1, r+2]) rem := by
  have h₁ := Prog.push_in_bot (p := [r-1]) (q := []) (by simpa using h)
    (by have := readCount_le' d (3*r-2); simp; omega) (Ne.symm hd1)
  have h₂ := Prog.push_in_bot (p := [r-1]) (q := [3*r-2])
    ((by simpa using h₁ : Prog r d (3*r-2+1) [] [r-1, 3*r-2] out _).cast
      (by omega : 3*r-2+1 = 3*r-1))
    (by have := readCount_le' d (3*r-1); simp; omega) (Ne.symm hd2)
  have h₃ := Prog.recordEq (v := 3*r) (by simpa using h₂) (by omega) (by omega) (Ne.symm hd3)
  have h₄ := Prog.pop_bot (p := []) (q := [3*r-1, 3*r-2]) (by simpa using h₃)
    (by have := readCount_le' d (3*r+1); simp; omega)
  have h₅ := Prog.push_in_bot (p := [3*r-1]) (q := [3*r-2]) (by simpa using h₄)
    (by have := readCount_le' d (3*r+1); simp; omega) (Ne.symm hd4)
  have h₆ := Prog.recordEq (v := 3*r+2) (by simpa using h₅) (by omega) (by omega) (Ne.symm hd5)
  have h₇ := Prog.pop_bot (p := []) (q := [3*r+1, 3*r-2]) (by simpa using h₆)
    (by have := readCount_le' d (3*r+2+1); simp; omega)
  have h₈ := Prog.pop_mid (y := r+2) (by simpa using h₇) (by omega) (Ne.symm hd6) (by simp)
    (by simp; omega) (by have := readCount_le' d (3*r+2+1); simp; omega)
  have h₉ := Prog.demote_bot (p := [3*r+1]) (q := [3*r-2]) (by simpa using h₈)
  simpa using h₉.cast (show 3*r+2+1 = 3*r+3 by omega)

/-- Deleting `V`. -/
theorem mphase_V (hr : 3 ≤ r) {out rem : List Nat}
    (h : Prog r (3*r+1) (3*r-2) [] [r-1] out ([3*r, r-1, 3*r+2, 3*r-1, r+2] ++ rem))
    (hlen : out.length = 2*r-1) :
    Loose r (3*r+1) (3*r+3) (out ++ [3*r, r-1, 3*r+2, 3*r-1, r+2]) rem := by
  have h₁ := Prog.push_in_bot (p := [r-1]) (q := []) (by simpa using h)
    (by rw [readCount_ge' (by omega)]; simp; omega) (by omega)
  have h₂ := Prog.push_in_bot (p := [r-1]) (q := [3*r-2])
    ((by simpa using h₁ : Prog r _ (3*r-2+1) [] [r-1, 3*r-2] out _).cast
      (by omega : 3*r-2+1 = 3*r-1))
    (by rw [readCount_ge' (by omega)]; simp; omega) (by omega)
  have h₃ := Prog.recordEq (v := 3*r) (by simpa using h₂) (by omega) (by omega) (by omega)
  have h₄ := Prog.pop_bot (p := []) (q := [3*r-1, 3*r-2]) (by simpa using h₃)
    (by rw [readCount_ge' (by omega)]; simp; omega)
  have h₅ := Prog.skipEq (by simpa using h₄) rfl
  have h₆ := Prog.recordEq (v := 3*r+2) (by simpa using h₅) (by omega) (by omega) (by omega)
  have h₇ := Prog.pop_bot (p := []) (q := [3*r-2]) (by simpa using h₆)
    (by rw [readCount_lt' (by omega)]; simp; omega)
  have h₈ := Prog.pop_mid (y := r+2) (by simpa using h₇) (by omega) (by omega) (by simp)
    (by simp; omega) (by rw [readCount_lt' (by omega)]; simp; omega)
  have h₉ := Prog.toLoose (bot := []) (by simpa using h₈)
    (by rw [readCount_lt' (by omega)]; simp; omega)
  exact (by simpa using h₉ : Loose r _ (3*r+2+1) _ rem).cast (by omega)

/-- Deleting `C` (regime Z): `U` goes below `P`, `V` on top. -/
theorem mphase_C (hr : 3 ≤ r) {out rem : List Nat}
    (h : Prog r (3*r-2) (3*r-2) [] [r-1] out ([3*r, r-1, 3*r+2, 3*r-1, r+2] ++ rem))
    (hlen : out.length = 2*r-1) :
    Loose r (3*r-2) (3*r+3) (out ++ [3*r, r-1, 3*r+2, 3*r-1, r+2]) rem := by
  have h₁ := (h.skipEq rfl).cast (by omega : 3*r-2+1 = 3*r-1)
  have h₂ := Prog.push_in_bot (p := [r-1]) (q := []) (by simpa using h₁)
    (by rw [readCount_lt' (by omega)]; simp; omega) (by omega)
  have h₃ := Prog.recordEq (v := 3*r) (by simpa using h₂) (by omega) (by omega) (by omega)
  have h₄ := Prog.pop_bot (p := []) (q := [3*r-1]) (by simpa using h₃)
    (by rw [readCount_lt' (by omega)]; simp; omega)
  have h₅ := Prog.push_top (by simpa using h₄) (by simp; omega) (by omega)
  have h₆ := Prog.recordEq (v := 3*r+2) (by simpa using h₅) (by omega) (by omega) (by omega)
  have h₇ := Prog.pop_bot (p := []) (q := []) (by simpa using h₆)
    (by rw [readCount_lt' (by omega)]; simp; omega)
  have h₈ := Prog.pop_mid (y := r+2) (by simpa using h₇) (by omega) (by omega) (by simp)
    (by simp) (by rw [readCount_lt' (by omega)]; simp; omega)
  have h₉ := Prog.toLooseZ (by simpa using h₈)
    (by rw [readCount_lt' (by omega)]; simp; omega) rfl
  exact (by simpa using h₉ : Loose r _ (3*r+2+1) _ rem).cast (by omega)

/-- (P3) Deleting `E_1 = r+2`: `C` above `P`, `U` and `V` at the bottom. -/
theorem mphase_E1 (hr : 3 ≤ r) {out rem : List Nat}
    (h : Prog r (r+2) (3*r-2) [] [r-1] out ([3*r, r-1, 3*r+2, 3*r-1] ++ rem))
    (hlen : out.length = 2*r-1) :
    Loose r (r+2) (3*r+3) (out ++ [3*r, r-1, 3*r+2, 3*r-1]) rem := by
  have h₁ := Prog.push_in_bot (p := []) (q := [r-1]) (by simpa using h)
    (by rw [readCount_lt' (by omega)]; simp; omega) (by omega)
  have h₂ := Prog.push_in_bot (p := [3*r-2, r-1]) (q := [])
    ((by simpa using h₁ : Prog r _ (3*r-2+1) [] [3*r-2, r-1] out _).cast
      (by omega : 3*r-2+1 = 3*r-1))
    (by rw [readCount_lt' (by omega)]; simp; omega) (by omega)
  have h₃ := Prog.recordEq (v := 3*r) (by simpa using h₂) (by omega) (by omega) (by omega)
  have h₄ := Prog.pop_bot (p := [3*r-2]) (q := [3*r-1]) (by simpa using h₃)
    (by rw [readCount_lt' (by omega)]; simp; omega)
  have h₅ := Prog.push_in_bot (p := [3*r-2, 3*r-1]) (q := []) (by simpa using h₄)
    (by rw [readCount_lt' (by omega)]; simp; omega) (by omega)
  have h₆ := Prog.recordEq (v := 3*r+2) (by simpa using h₅) (by omega) (by omega) (by omega)
  have h₇ := Prog.pop_bot (p := [3*r-2]) (q := [3*r+1]) (by simpa using h₆)
    (by rw [readCount_lt' (by omega)]; simp; omega)
  have h₈ := Prog.toLoose (bot := [3*r+1]) (by simpa using h₇)
    (by rw [readCount_lt' (by omega)]; simp; omega)
  exact (by simpa using h₈ : Loose r _ (3*r+2+1) _ rem).cast (by omega)

/-- (P4) Deleting `U`: `C` below `P`, `V` at the bottom. -/
theorem mphase_U (hr : 3 ≤ r) {out rem : List Nat}
    (h : Prog r (3*r-1) (3*r-2) [] [r-1] out ([3*r, r-1, 3*r+2, r+2] ++ rem))
    (hlen : out.length = 2*r-1) :
    Loose r (3*r-1) (3*r+3) (out ++ [3*r, r-1, 3*r+2, r+2]) rem := by
  have h₁ := Prog.push_in_bot (p := [r-1]) (q := []) (by simpa using h)
    (by rw [readCount_ge' (by omega)]; simp; omega) (by omega)
  have h₂ := Prog.skipEq (by simpa using h₁) (by omega)
  have h₃ := Prog.recordEq (v := 3*r) (by simpa using h₂) (by omega) (by omega) (by omega)
  have h₄ := Prog.pop_bot (p := []) (q := [3*r-2]) (by simpa using h₃)
    (by rw [readCount_lt' (by omega)]; simp; omega)
  have h₅ := Prog.push_in_bot (p := [3*r-2]) (q := []) (by simpa using h₄)
    (by rw [readCount_lt' (by omega)]; simp; omega) (by omega)
  have h₆ := Prog.recordEq (v := 3*r+2) (by simpa using h₅) (by omega) (by omega) (by omega)
  have h₇ := Prog.pop_mid (y := r+2) (by simpa using h₆) (by omega) (by omega) (by simp)
    (by simp; omega) (by rw [readCount_lt' (by omega)]; simp; omega)
  have h₈ := Prog.toLoose (bot := [3*r+1]) (by simpa using h₇)
    (by rw [readCount_lt' (by omega)]; simp; omega)
  exact (by simpa using h₈ : Loose r _ (3*r+2+1) _ rem).cast (by omega)

/-- (P5) Deleting `M1`: `P` is output at once, then `C` and `U` are tracked on
top. -/
theorem mphase_M1 (hr : 3 ≤ r) {out rem : List Nat}
    (h : Prog r (3*r) (3*r-2) [] [r-1] out ([r-1, 3*r+2, 3*r-1, r+2] ++ rem))
    (hlen : out.length = 2*r-1) :
    Loose r (3*r) (3*r+3) (out ++ [r-1, 3*r+2, 3*r-1, r+2]) rem := by
  have h₁ := Prog.pop_bot (p := []) (q := []) (by simpa using h)
    (by rw [readCount_ge' (by omega)]; simp; omega)
  have h₂ := Prog.push_protect (by simpa using h₁) (by simp; omega) (by omega)
  have h₃ := Prog.push_protect ((by simpa using h₂ : Prog r _ (3*r-2+1) [3*r-2] [] _ _).cast
    (by omega : 3*r-2+1 = 3*r-1)) (by simp; omega) (by omega)
  have h₄ := Prog.skipEq h₃ (by omega)
  have h₅ := Prog.push_top h₄ (by simp; omega) (by omega)
  have h₆ := Prog.recordEq (v := 3*r+2) (by simpa using h₅) (by omega) (by omega) (by omega)
  have h₇ := Prog.pop_top (p := [3*r-2]) (q := []) (by simpa using h₆) (by simp; omega)
  have h₈ := Prog.pop_mid (y := r+2) (by simpa using h₇) (by omega) (by omega)
    (by simp; omega) (by simp) (by rw [readCount_lt' (by omega)]; simp; omega)
  refine ⟨[3*r-2], ?_, by simp; omega, Or.inr (by simp)⟩
  simpa using h₈.cast (show 3*r+2+1 = 3*r+3 by omega)

/-- (P7) Deleting `M2`: `C` below `P` and `U` above `C`; `U` and `E_1` are
output right after `P`, and `V` stays pending. -/
theorem mphase_M2 (hr : 3 ≤ r) {out rem : List Nat}
    (h : Prog r (3*r+2) (3*r-2) [] [r-1] out ([3*r, r-1, 3*r-1, r+2] ++ rem))
    (hlen : out.length = 2*r-1) :
    Loose r (3*r+2) (3*r+1) (out ++ [3*r, r-1, 3*r-1, r+2]) rem := by
  have h₁ := Prog.push_in_bot (p := [r-1]) (q := []) (by simpa using h)
    (by rw [readCount_ge' (by omega)]; simp; omega) (by omega)
  have h₂ := Prog.push_in_bot (p := [r-1]) (q := [3*r-2])
    ((by simpa using h₁ : Prog r _ (3*r-2+1) [] [r-1, 3*r-2] out _).cast
      (by omega : 3*r-2+1 = 3*r-1))
    (by rw [readCount_ge' (by omega)]; simp; omega) (by omega)
  have h₃ := Prog.recordEq (v := 3*r) (by simpa using h₂) (by omega) (by omega) (by omega)
  have h₄ := Prog.pop_bot (p := []) (q := [3*r-1, 3*r-2]) (by simpa using h₃)
    (by rw [readCount_ge' (by omega)]; simp; omega)
  have h₅ := Prog.pop_bot (p := []) (q := [3*r-2]) (by simpa using h₄)
    (by rw [readCount_ge' (by omega)]; simp; omega)
  have h₆ := Prog.pop_mid (y := r+2) (by simpa using h₅) (by omega) (by omega) (by simp)
    (by simp; omega) (by rw [readCount_ge' (by omega)]; simp; omega)
  have h₇ := Prog.toLoose (bot := []) (by simpa using h₆)
    (by rw [readCount_ge' (by omega)]; simp; omega)
  simpa using h₇

#print axioms mphase_std
#print axioms mphase_V
#print axioms mphase_C
#print axioms mphase_E1
#print axioms mphase_U
#print axioms mphase_M1
#print axioms mphase_M2
end Equal
end StackSorting.Generalized
