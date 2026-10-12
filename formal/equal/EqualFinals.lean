import EqualRegimes

/-! Section 5.5, from regime S with the deleted value in the final segment.

Here `a = 3r+3+3k`, the stack is `Q ++ [C]` with `r-1` tokens, and slot `r-1`
is just below `C`. Each case is the table row of the draft; every pop is
justified by its position, which is computed from the count. -/
namespace StackSorting.Generalized
namespace Equal
open BasisFamily (delete)
open Unequal (readCount delete_append delete_eq_self)

variable {r d : Nat}

theorem delete_queue_self {r k : Nat} (hr : 3 ≤ r) (hd : 3*r+3+3*k ≤ d) :
    delete d (queue r k) = queue r k :=
  delete_eq_self (fun x hx => by have := queue_bound hr hx; omega)

theorem queue_held {r k next : Nat} (hr : 3 ≤ r) (hn : 3*r+3+3*k ≤ next) (hd : 3*r+3+3*k ≤ d) :
    ∀ y ∈ queue r k, y < next ∧ y ≠ d :=
  fun y hy => by have := queue_bound hr hy; exact ⟨by omega, by omega⟩

/-- Table row A, deleted `a+3`. -/
theorem Std.finalA_3 (hr : 3 ≤ r) {k : Nat} {out : List Nat}
    (h : Std r d (3*r+3+3*k) out (delete d (finA r k))) (hd : d = 3*r+6+3*k) :
    Prog r d (3*r+7+3*k) [] [] (out ++ delete d (finA r k)) [] := by
  subst hd
  have hC : (3*r-2 != 3*r+6+3*k) = true := by simp; omega
  have hdel : delete (3*r+6+3*k) (finA r k) =
      [3*r+3+3*k, 3*r-2] ++ (queue r k ++ [3*r+4+3*k, 3*r+5+3*k]) := by
    simp only [finA, delete_append, delete_queue_self hr (by omega : 3*r+3+3*k ≤ 3*r+6+3*k)]
    simp [delete, hC]
  rw [hdel] at h ⊢
  obtain ⟨hp, hc⟩ := h
  rw [readCount_ge' (by omega)] at hc
  have h₁ := Prog.recordEq (v := 3*r+3+3*k) (by simpa using hp) rfl (by omega) (by omega)
  have h₂ := Prog.pop_bot (p := []) (q := []) (by simpa using h₁)
    (by rw [readCount_ge' (by omega)]; simp; omega)
  have h₃ := Prog.drain (queue r k) (rem := [3*r+4+3*k, 3*r+5+3*k]) (by simpa using h₂)
    (queue_held hr (by omega) (by omega)) (by rw [readCount_ge' (by omega)]; simp; omega)
  have h₄ := Prog.recordEq (v := 3*r+4+3*k) (by simpa using h₃) (by omega) (by omega) (by omega)
  have h₅ := Prog.recordEq (v := 3*r+5+3*k) (by simpa using h₄) (by omega) (by omega) (by omega)
  have h₆ := h₅.skipEq (by omega)
  simpa using h₆.cast (show 3*r+6+3*k+1 = 3*r+7+3*k by omega)

/-- Table row A, deleted `a`. -/
theorem Std.finalA_0 (hr : 3 ≤ r) {k : Nat} {out : List Nat}
    (h : Std r d (3*r+3+3*k) out (delete d (finA r k))) (hd : d = 3*r+3+3*k) :
    Prog r d (3*r+7+3*k) [] [] (out ++ delete d (finA r k)) [] := by
  subst hd
  have hC : (3*r-2 != 3*r+3+3*k) = true := by simp; omega
  have hdel : delete (3*r+3+3*k) (finA r k) =
      [3*r+6+3*k, 3*r-2] ++ (queue r k ++ [3*r+4+3*k, 3*r+5+3*k]) := by
    simp only [finA, delete_append, delete_queue_self hr (Nat.le_refl _)]
    simp [delete, hC]
  rw [hdel] at h ⊢
  obtain ⟨hp, hc⟩ := h
  rw [readCount_ge' (by omega)] at hc
  have h₁ := (hp.skipEq rfl).cast (show 3*r+3+3*k+1 = 3*r+4+3*k by omega)
  have h₂ := Prog.push_in_bot (p := [3*r-2]) (q := []) (by simpa using h₁)
    (by rw [readCount_lt' (by omega)]; simp; omega) (by omega)
  have h₃ := Prog.push_in_bot (p := [3*r-2]) (q := [3*r+4+3*k])
    ((by simpa using h₂ : Prog r _ (3*r+4+3*k+1) [] _ out _).cast (by omega :
      3*r+4+3*k+1 = 3*r+5+3*k))
    (by rw [readCount_lt' (by omega)]; simp; omega) (by omega)
  have h₄ := Prog.recordEq (v := 3*r+6+3*k) (by simpa using h₃) (by omega) (by omega) (by omega)
  have h₅ := Prog.pop_bot (p := []) (q := [3*r+5+3*k, 3*r+4+3*k]) (by simpa using h₄)
    (by rw [readCount_lt' (by omega)]; simp; omega)
  have h₆ := Prog.demote_bot (p := [3*r+5+3*k, 3*r+4+3*k]) (q := []) (by simpa using h₅)
  have h₇ := Prog.drain (queue r k ++ [3*r+4+3*k, 3*r+5+3*k]) (rem := []) (by simpa using h₆)
    (by
      intro y hy
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hy
      rcases hy with hy | hy | hy
      · exact queue_held hr (by omega) (by omega) y hy
      · exact ⟨by omega, by omega⟩
      · exact ⟨by omega, by omega⟩)
    (by rw [readCount_lt' (by omega)]; simp; omega)
  simpa using h₇.cast (show 3*r+6+3*k+1 = 3*r+7+3*k by omega)

/-- Table row A, deleted `a+1` or `a+2`: `x` is the other one. -/
theorem Std.finalA_12 (hr : 3 ≤ r) {k : Nat} {out : List Nat}
    (h : Std r d (3*r+3+3*k) out (delete d (finA r k)))
    (hd : d = 3*r+4+3*k ∨ d = 3*r+5+3*k) :
    Prog r d (3*r+7+3*k) [] [] (out ++ delete d (finA r k)) [] := by
  have hC : (3*r-2 != d) = true := by simp; omega
  obtain ⟨x, hx, hxd⟩ : ∃ x, (x = 3*r+4+3*k ∨ x = 3*r+5+3*k) ∧ x ≠ d ∧
      delete d [3*r+4+3*k, 3*r+5+3*k] = [x] := by
    rcases hd with rfl | rfl
    · exact ⟨3*r+5+3*k, Or.inr rfl, by omega, by simp [delete]⟩
    · exact ⟨3*r+4+3*k, Or.inl rfl, by omega, by simp [delete]⟩
  have hdel : delete d (finA r k) = [3*r+6+3*k, 3*r+3+3*k, 3*r-2] ++ (queue r k ++ [x]) := by
    have e₀ := hxd.2
    simp only [finA, delete_append, delete_queue_self hr (by omega : 3*r+3+3*k ≤ d), e₀]
    have e₁ : (3*r+6+3*k != d) = true := by simp; omega
    have e₂ : (3*r+3+3*k != d) = true := by simp; omega
    simp [delete, hC, e₁, e₂]
  rw [hdel] at h ⊢
  obtain ⟨hp, hc⟩ := h
  rw [readCount_ge' (by omega)] at hc
  -- a at slot r-2 (just above C), then a+1 (or a+2), skipping d
  have h₁ := Prog.push_in_bot (p := []) (q := [3*r-2]) (by simpa using hp)
    (by rw [readCount_ge' (by omega)]; simp; omega) (by omega)
  have h₂ : Prog r d (3*r+6+3*k) [] [3*r+3+3*k, x, 3*r-2] out
      ([3*r+6+3*k, 3*r+3+3*k, 3*r-2] ++ (queue r k ++ [x])) := by
    rcases hd with rfl | rfl
    · have hx' : x = 3*r+5+3*k := by omega
      subst hx'
      have h₂ := (Prog.skipEq (by simpa using h₁) (by omega)).cast
        (show 3*r+4+3*k+1 = 3*r+5+3*k by omega)
      have h₃ := Prog.push_in_bot (p := [3*r+3+3*k]) (q := [3*r-2]) h₂
        (by rw [readCount_lt' (by omega)]; simp; omega) (by omega)
      simpa using h₃.cast (show 3*r+5+3*k+1 = 3*r+6+3*k by omega)
    · have hx' : x = 3*r+4+3*k := by omega
      subst hx'
      have h₂ := Prog.push_in_bot (p := [3*r+3+3*k]) (q := [3*r-2])
        ((by simpa using h₁ : Prog r _ (3*r+3+3*k+1) [] _ out _).cast
          (show 3*r+3+3*k+1 = 3*r+4+3*k by omega))
        (by rw [readCount_ge' (by omega)]; simp; omega) (by omega)
      have h₃ := Prog.skipEq h₂ (by omega)
      simpa using h₃.cast (show 3*r+5+3*k+1 = 3*r+6+3*k by omega)
  have h₄ := Prog.recordEq (v := 3*r+6+3*k) h₂ rfl (by omega) (by omega)
  have h₅ := Prog.pop_bot (p := []) (q := [x, 3*r-2]) (by simpa using h₄)
    (by rw [readCount_lt' (by omega)]; simp; omega)
  have h₆ := Prog.pop_bot (p := [x]) (q := []) (by simpa using h₅)
    (by rw [readCount_lt' (by omega)]; simp; omega)
  have h₇ := Prog.demote_bot (p := [x]) (q := []) (by simpa using h₆)
  have h₈ := Prog.drain (queue r k ++ [x]) (rem := []) (by simpa using h₇)
    (by
      intro y hy
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hy
      rcases hy with hy | hy
      · exact queue_held hr (by omega) (by omega) y hy
      · exact ⟨by omega, by omega⟩)
    (by rw [readCount_lt' (by omega)]; simp; omega)
  simpa using h₈.cast (show 3*r+6+3*k+1 = 3*r+7+3*k by omega)

/-- Table row B, deleted `a+2`. -/
theorem Std.finalB_2 (hr : 3 ≤ r) {k : Nat} {out : List Nat}
    (h : Std r d (3*r+3+3*k) out (delete d (finB r k))) (hd : d = 3*r+5+3*k) :
    Prog r d (3*r+8+3*k) [] [] (out ++ delete d (finB r k)) [] := by
  subst hd
  have hC : (3*r-2 != 3*r+5+3*k) = true := by simp; omega
  have hdel : delete (3*r+5+3*k) (finB r k) =
      [3*r+3+3*k, 3*r+7+3*k, 3*r-2] ++ (queue r k ++ [3*r+4+3*k, 3*r+6+3*k]) := by
    simp only [finB, delete_append, delete_queue_self hr (by omega : 3*r+3+3*k ≤ 3*r+5+3*k)]
    simp [delete, hC]
  rw [hdel] at h ⊢
  obtain ⟨hp, hc⟩ := h
  rw [readCount_ge' (by omega)] at hc
  have h₁ := Prog.recordEq (v := 3*r+3+3*k) (by simpa using hp) rfl (by omega) (by omega)
  have h₂ := Prog.push_in_bot (p := [3*r-2]) (q := [])
    ((by simpa using h₁ : Prog r _ (3*r+3+3*k+1) [] _ _ _).cast
      (show 3*r+3+3*k+1 = 3*r+4+3*k by omega))
    (by rw [readCount_ge' (by omega)]; simp; omega) (by omega)
  have h₃ := (Prog.skipEq (by simpa using h₂) (by omega)).cast
    (show 3*r+5+3*k+1 = 3*r+6+3*k by omega)
  have h₄ := Prog.push_in_bot (p := [3*r-2]) (q := [3*r+4+3*k]) h₃
    (by rw [readCount_lt' (by omega)]; simp; omega) (by omega)
  have h₅ := Prog.recordEq (v := 3*r+7+3*k) (by simpa using h₄) (by omega) (by omega) (by omega)
  have h₆ := Prog.pop_bot (p := []) (q := [3*r+6+3*k, 3*r+4+3*k]) (by simpa using h₅)
    (by rw [readCount_lt' (by omega)]; simp; omega)
  have h₇ := Prog.demote_bot (p := [3*r+6+3*k, 3*r+4+3*k]) (q := []) (by simpa using h₆)
  have h₈ := Prog.drain (queue r k ++ [3*r+4+3*k, 3*r+6+3*k]) (rem := []) (by simpa using h₇)
    (by
      intro y hy
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hy
      rcases hy with hy | hy | hy
      · exact queue_held hr (by omega) (by omega) y hy
      · exact ⟨by omega, by omega⟩
      · exact ⟨by omega, by omega⟩)
    (by rw [readCount_lt' (by omega)]; simp; omega)
  simpa using h₈.cast (show 3*r+7+3*k+1 = 3*r+8+3*k by omega)

/-- Table row B, deleted `a`. -/
theorem Std.finalB_0 (hr : 3 ≤ r) {k : Nat} {out : List Nat}
    (h : Std r d (3*r+3+3*k) out (delete d (finB r k))) (hd : d = 3*r+3+3*k) :
    Prog r d (3*r+8+3*k) [] [] (out ++ delete d (finB r k)) [] := by
  subst hd
  have hC : (3*r-2 != 3*r+3+3*k) = true := by simp; omega
  have hdel : delete (3*r+3+3*k) (finB r k) =
      [3*r+5+3*k, 3*r+7+3*k, 3*r-2] ++ (queue r k ++ [3*r+4+3*k, 3*r+6+3*k]) := by
    simp only [finB, delete_append, delete_queue_self hr (Nat.le_refl _)]
    simp [delete, hC]
  rw [hdel] at h ⊢
  obtain ⟨hp, hc⟩ := h
  rw [readCount_ge' (by omega)] at hc
  have h₁ := (hp.skipEq rfl).cast (show 3*r+3+3*k+1 = 3*r+4+3*k by omega)
  have h₂ := Prog.push_in_bot (p := [3*r-2]) (q := []) (by simpa using h₁)
    (by rw [readCount_lt' (by omega)]; simp; omega) (by omega)
  have h₃ := Prog.recordEq (v := 3*r+5+3*k) (by simpa using h₂) (by omega) (by omega) (by omega)
  have h₄ := Prog.push_in_bot (p := [3*r-2]) (q := [3*r+4+3*k])
    ((by simpa using h₃ : Prog r _ (3*r+5+3*k+1) [] _ _ _).cast
      (show 3*r+5+3*k+1 = 3*r+6+3*k by omega))
    (by rw [readCount_lt' (by omega)]; simp; omega) (by omega)
  have h₅ := Prog.recordEq (v := 3*r+7+3*k) (by simpa using h₄) (by omega) (by omega) (by omega)
  have h₆ := Prog.pop_bot (p := []) (q := [3*r+6+3*k, 3*r+4+3*k]) (by simpa using h₅)
    (by rw [readCount_lt' (by omega)]; simp; omega)
  have h₇ := Prog.demote_bot (p := [3*r+6+3*k, 3*r+4+3*k]) (q := []) (by simpa using h₆)
  have h₈ := Prog.drain (queue r k ++ [3*r+4+3*k, 3*r+6+3*k]) (rem := []) (by simpa using h₇)
    (by
      intro y hy
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hy
      rcases hy with hy | hy | hy
      · exact queue_held hr (by omega) (by omega) y hy
      · exact ⟨by omega, by omega⟩
      · exact ⟨by omega, by omega⟩)
    (by rw [readCount_lt' (by omega)]; simp; omega)
  simpa using h₈.cast (show 3*r+7+3*k+1 = 3*r+8+3*k by omega)

/-- Table row B, deleted `a+4`. -/
theorem Std.finalB_4 (hr : 3 ≤ r) {k : Nat} {out : List Nat}
    (h : Std r d (3*r+3+3*k) out (delete d (finB r k))) (hd : d = 3*r+7+3*k) :
    Prog r d (3*r+8+3*k) [] [] (out ++ delete d (finB r k)) [] := by
  subst hd
  have hC : (3*r-2 != 3*r+7+3*k) = true := by simp; omega
  have hdel : delete (3*r+7+3*k) (finB r k) =
      [3*r+5+3*k, 3*r+3+3*k, 3*r-2] ++ (queue r k ++ [3*r+4+3*k, 3*r+6+3*k]) := by
    simp only [finB, delete_append, delete_queue_self hr (by omega : 3*r+3+3*k ≤ 3*r+7+3*k)]
    simp [delete, hC]
  rw [hdel] at h ⊢
  obtain ⟨hp, hc⟩ := h
  rw [readCount_ge' (by omega)] at hc
  have h₁ := Prog.push_in_bot (p := []) (q := [3*r-2]) (by simpa using hp)
    (by rw [readCount_ge' (by omega)]; simp; omega) (by omega)
  have h₂ := Prog.push_in_bot (p := [3*r+3+3*k]) (q := [3*r-2])
    ((by simpa using h₁ : Prog r _ (3*r+3+3*k+1) [] _ _ _).cast
      (show 3*r+3+3*k+1 = 3*r+4+3*k by omega))
    (by rw [readCount_ge' (by omega)]; simp; omega) (by omega)
  have h₃ := Prog.recordEq (v := 3*r+5+3*k) (by simpa using h₂) (by omega) (by omega) (by omega)
  have h₄ := Prog.pop_bot (p := []) (q := [3*r+4+3*k, 3*r-2]) (by simpa using h₃)
    (by rw [readCount_ge' (by omega)]; simp; omega)
  have h₅ := Prog.pop_bot (p := [3*r+4+3*k]) (q := []) (by simpa using h₄)
    (by rw [readCount_ge' (by omega)]; simp; omega)
  have h₆ := Prog.demote_bot (p := [3*r+4+3*k]) (q := []) (by simpa using h₅)
  have h₇ := Prog.drain (queue r k ++ [3*r+4+3*k]) (rem := [3*r+6+3*k]) (by simpa using h₆)
    (by
      intro y hy
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hy
      rcases hy with hy | hy
      · exact queue_held hr (by omega) (by omega) y hy
      · exact ⟨by omega, by omega⟩)
    (by rw [readCount_ge' (by omega)]; simp; omega)
  have h₈ := Prog.recordEq (v := 3*r+6+3*k) (by simpa using h₇) (by omega) (by omega) (by omega)
  have h₉ := Prog.skipEq h₈ (by omega)
  simpa using h₉.cast (show 3*r+7+3*k+1 = 3*r+8+3*k by omega)

/-- Table row B, deleted `a+1`. -/
theorem Std.finalB_1 (hr : 3 ≤ r) {k : Nat} {out : List Nat}
    (h : Std r d (3*r+3+3*k) out (delete d (finB r k))) (hd : d = 3*r+4+3*k) :
    Prog r d (3*r+8+3*k) [] [] (out ++ delete d (finB r k)) [] := by
  subst hd
  have hC : (3*r-2 != 3*r+4+3*k) = true := by simp; omega
  have hdel : delete (3*r+4+3*k) (finB r k) =
      [3*r+5+3*k, 3*r+3+3*k, 3*r+7+3*k, 3*r-2] ++ (queue r k ++ [3*r+6+3*k]) := by
    simp only [finB, delete_append, delete_queue_self hr (by omega : 3*r+3+3*k ≤ 3*r+4+3*k)]
    simp [delete, hC]
  rw [hdel] at h ⊢
  obtain ⟨hp, hc⟩ := h
  rw [readCount_ge' (by omega)] at hc
  have h₁ := Prog.push_in_bot (p := [3*r-2]) (q := []) (by simpa using hp)
    (by rw [readCount_ge' (by omega)]; simp; omega) (by omega)
  have h₂ := (Prog.skipEq (by simpa using h₁) (by omega)).cast
    (show 3*r+4+3*k+1 = 3*r+5+3*k by omega)
  have h₃ := Prog.recordEq (v := 3*r+5+3*k) h₂ rfl (by omega) (by omega)
  have h₄ := Prog.pop_bot (p := [3*r-2]) (q := []) (by simpa using h₃)
    (by rw [readCount_lt' (by omega)]; simp; omega)
  have h₅ := Prog.push_in_bot (p := [3*r-2]) (q := [])
    ((by simpa using h₄ : Prog r _ (3*r+5+3*k+1) [] _ _ _).cast
      (show 3*r+5+3*k+1 = 3*r+6+3*k by omega))
    (by rw [readCount_lt' (by omega)]; simp; omega) (by omega)
  have h₆ := Prog.recordEq (v := 3*r+7+3*k) (by simpa using h₅) (by omega) (by omega) (by omega)
  have h₇ := Prog.pop_bot (p := []) (q := [3*r+6+3*k]) (by simpa using h₆)
    (by rw [readCount_lt' (by omega)]; simp; omega)
  have h₈ := Prog.demote_bot (p := [3*r+6+3*k]) (q := []) (by simpa using h₇)
  have h₉ := Prog.drain (queue r k ++ [3*r+6+3*k]) (rem := []) (by simpa using h₈)
    (by
      intro y hy
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hy
      rcases hy with hy | hy
      · exact queue_held hr (by omega) (by omega) y hy
      · exact ⟨by omega, by omega⟩)
    (by rw [readCount_lt' (by omega)]; simp; omega)
  simpa using h₉.cast (show 3*r+7+3*k+1 = 3*r+8+3*k by omega)

/-- Table row B, deleted `a+3`. -/
theorem Std.finalB_3 (hr : 3 ≤ r) {k : Nat} {out : List Nat}
    (h : Std r d (3*r+3+3*k) out (delete d (finB r k))) (hd : d = 3*r+6+3*k) :
    Prog r d (3*r+8+3*k) [] [] (out ++ delete d (finB r k)) [] := by
  subst hd
  have hC : (3*r-2 != 3*r+6+3*k) = true := by simp; omega
  have hdel : delete (3*r+6+3*k) (finB r k) =
      [3*r+5+3*k, 3*r+3+3*k, 3*r+7+3*k, 3*r-2] ++ (queue r k ++ [3*r+4+3*k]) := by
    simp only [finB, delete_append, delete_queue_self hr (by omega : 3*r+3+3*k ≤ 3*r+6+3*k)]
    simp [delete, hC]
  rw [hdel] at h ⊢
  obtain ⟨hp, hc⟩ := h
  rw [readCount_ge' (by omega)] at hc
  have h₁ := Prog.push_in_bot (p := []) (q := [3*r-2]) (by simpa using hp)
    (by rw [readCount_ge' (by omega)]; simp; omega) (by omega)
  have h₂ := Prog.push_in_bot (p := [3*r+3+3*k]) (q := [3*r-2])
    ((by simpa using h₁ : Prog r _ (3*r+3+3*k+1) [] _ _ _).cast
      (show 3*r+3+3*k+1 = 3*r+4+3*k by omega))
    (by rw [readCount_ge' (by omega)]; simp; omega) (by omega)
  have h₃ := Prog.recordEq (v := 3*r+5+3*k) (by simpa using h₂) (by omega) (by omega) (by omega)
  have h₄ := Prog.pop_bot (p := []) (q := [3*r+4+3*k, 3*r-2]) (by simpa using h₃)
    (by rw [readCount_ge' (by omega)]; simp; omega)
  have h₅ := Prog.skipEq h₄ (by omega)
  have h₆ := Prog.recordEq (v := 3*r+7+3*k) (by simpa using h₅) (by omega) (by omega) (by omega)
  have h₇ := Prog.pop_bot (p := [3*r+4+3*k]) (q := []) (by simpa using h₆)
    (by rw [readCount_lt' (by omega)]; simp; omega)
  have h₈ := Prog.demote_bot (p := [3*r+4+3*k]) (q := []) (by simpa using h₇)
  have h₉ := Prog.drain (queue r k ++ [3*r+4+3*k]) (rem := []) (by simpa using h₈)
    (by
      intro y hy
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hy
      rcases hy with hy | hy
      · exact queue_held hr (by omega) (by omega) y hy
      · exact ⟨by omega, by omega⟩)
    (by rw [readCount_lt' (by omega)]; simp; omega)
  simpa using h₉.cast (show 3*r+7+3*k+1 = 3*r+8+3*k by omega)

#print axioms Std.finalA_3
#print axioms Std.finalA_0
#print axioms Std.finalA_12
#print axioms Std.finalB_2
#print axioms Std.finalB_0
#print axioms Std.finalB_4
#print axioms Std.finalB_1
#print axioms Std.finalB_3
end Equal
end StackSorting.Generalized
