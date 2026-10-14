import EqualMPhase

/-! Every single deletion of `A_r(k)` and `B_r(k)` is generated (Section 5 of
`docs/infinite-basis-equal-width-draft.md`). The cases partition every value
`d < n` (Section 5.6):
- `d` in the prefix, `C`, or an `O_0` token: a prefix script ending in regime
  L or Z, then the L/Z steps and final (`Loose.finishA`/`Loose.finishB`);
- `d` in step `j`: regime S up to step `j`, the Section 5.3 step, then L;
- `d` in the final segment: regime S throughout, then a Section 5.5 table row. -/
namespace StackSorting.Generalized
namespace Equal
open BasisFamily (delete)
open Unequal (readCount lowSeg lowSeg_ne delete_append delete_eq_self delete_nodup
  length_delete_range' length_lowSeg)

variable {r d : Nat}

theorem delete_cons' (d x : Nat) (l : List Nat) :
    delete d (x :: l) = if x = d then delete d l else x :: delete d l := by
  by_cases h : x = d <;> simp [delete, h]

theorem delete_nil' (d : Nat) : delete d [] = [] := rfl

theorem ite_no {α : Type} {c : Prop} [Decidable c] {a b : α} (h : ¬ c) :
    (if c then a else b) = b := by simp [h]

theorem ite_T {α : Type} {a b : α} : (if True then a else b) = a := rfl

/-! Deleting from the literal lists of the prefix and of one step. Each
comparison is decided by `omega`. -/

theorem prefixTail_del_self (hd : d ≠ r ∧ d ≠ 3*r ∧ d ≠ r-1 ∧ d ≠ 3*r+2 ∧ d ≠ 3*r-1 ∧ d ≠ r+2) :
    delete d (prefixTail r) = prefixTail r :=
  delete_eq_self (fun x hx => by simp [prefixTail] at hx; omega)

theorem prefixTail_del_P (hr : 3 ≤ r) :
    delete (r-1) (prefixTail r) = [r, 3*r, 3*r+2, 3*r-1, r+2] := by
  simp (disch := omega) only [prefixTail, delete_cons', delete_nil', ite_no, ite_T]

theorem prefixTail_del_E0 (hr : 3 ≤ r) :
    delete r (prefixTail r) = [3*r, r-1, 3*r+2, 3*r-1, r+2] := by
  simp (disch := omega) only [prefixTail, delete_cons', delete_nil', ite_no, ite_T]

theorem prefixTail_del_E1 (hr : 3 ≤ r) :
    delete (r+2) (prefixTail r) = [r, 3*r, r-1, 3*r+2, 3*r-1] := by
  simp (disch := omega) only [prefixTail, delete_cons', delete_nil', ite_no, ite_T]

theorem prefixTail_del_U (hr : 3 ≤ r) :
    delete (3*r-1) (prefixTail r) = [r, 3*r, r-1, 3*r+2, r+2] := by
  simp (disch := omega) only [prefixTail, delete_cons', delete_nil', ite_no, ite_T]

theorem prefixTail_del_M1 (hr : 3 ≤ r) :
    delete (3*r) (prefixTail r) = [r, r-1, 3*r+2, 3*r-1, r+2] := by
  simp (disch := omega) only [prefixTail, delete_cons', delete_nil', ite_no, ite_T]

theorem prefixTail_del_M2 (hr : 3 ≤ r) :
    delete (3*r+2) (prefixTail r) = [r, 3*r, r-1, 3*r-1, r+2] := by
  simp (disch := omega) only [prefixTail, delete_cons', delete_nil', ite_no, ite_T]

theorem pair_del_low (r i : Nat) : delete i [r+1+2*i, i] = [r+1+2*i] := by
  simp (disch := omega) only [delete_cons', delete_nil', ite_no, ite_T]

theorem pair_del_rec (r t : Nat) : delete (r+1+2*t) [r+1+2*t, t] = [t] := by
  simp (disch := omega) only [delete_cons', delete_nil', ite_no, ite_T]

theorem step_del_a (hr : 3 ≤ r) (j : Nat) :
    delete (3*r+3+3*j) [3*r+5+3*j, 3*r+3+3*j, qv r j] = [3*r+5+3*j, qv r j] := by
  have := qv_lt r j hr
  simp (disch := omega) only [delete_cons', delete_nil', ite_no, ite_T]

theorem step_del_b (hr : 3 ≤ r) (j : Nat) :
    delete (3*r+4+3*j) [3*r+5+3*j, 3*r+3+3*j, qv r j] = [3*r+5+3*j, 3*r+3+3*j, qv r j] := by
  have := qv_lt r j hr
  simp (disch := omega) only [delete_cons', delete_nil', ite_no]

theorem step_del_R (hr : 3 ≤ r) (j : Nat) :
    delete (3*r+5+3*j) [3*r+5+3*j, 3*r+3+3*j, qv r j] = [3*r+3+3*j, qv r j] := by
  have := qv_lt r j hr
  simp (disch := omega) only [delete_cons', delete_nil', ite_no, ite_T]

theorem length_delete_perm {p : List Nat} {n : Nat} (hp : p.Perm (List.range n)) (hd : d < n) :
    (delete d p).length = n - 1 := by
  have hl := (hp.filter (· != d)).length_eq
  have he : (List.filter (· != d) (List.range n)).length = readCount d n := by
    have := length_delete_range' d n
    simpa [delete, List.range_eq_range'] using this
  simp only [delete] at hl ⊢
  rw [hl, he, readCount_lt' hd]

theorem run_of_prog {n : Nat} {W : List Nat} (hd : d < n) (h : Prog r d n [] [] W [])
    (hl : W.length = n - 1) : Run r r [] (delete d (List.range n)) W [] := by
  have := h.finish (by rw [readCount_lt' hd]; exact hl)
  simpa [List.range_eq_range'] using this

theorem lowSeg_del_self (h : ∀ i, i + 2 ≤ r → r+1+2*i ≠ d ∧ i ≠ d) :
    delete d (lowSeg r 0 (r-1)) = lowSeg r 0 (r-1) :=
  delete_eq_self (lowSeg_ne (fun i _ hi => h i (by omega)))

/-- Every prefix deletion, and every deletion of `C` or an `O_0` token, ends
the prefix in regime L or Z. -/
theorem prefix_loose (hr : 3 ≤ r) {rem : List Nat} (hd : d < 3*r+3)
    (hW : (delete d (lowSeg r 0 (r-1)) ++ (delete d (prefixTail r) ++ rem)).Nodup) :
    ∃ next, next ≤ 3*r+3 ∧
      Loose r d next (delete d (lowSeg r 0 (r-1)) ++ delete d (prefixTail r)) rem := by
  by_cases h₁ : d < r - 1
  · -- (P2) a low
    have e₁ : delete d (lowSeg r 0 (r-1)) =
        lowSeg r 0 d ++ ([r+1+2*d] ++ lowSeg r (d+1) (r-2-d)) := by
      rw [lowSeg_cut r d (by omega), delete_append, delete_append,
        delete_eq_self (lowSeg_ne (fun i _ _ => ⟨by omega, by omega⟩)),
        delete_eq_self (lowSeg_ne (fun i _ _ => ⟨by omega, by omega⟩))]
      rw [pair_del_low]
    have e₂ : delete d (prefixTail r) = prefixTail r :=
      prefixTail_del_self ⟨by omega, by omega, by omega, by omega, by omega, by omega⟩
    rw [e₁, e₂] at hW ⊢
    exact ⟨_, Nat.le_refl _, prefix_low hr (i := d) (by omega) (by simpa using hW)⟩
  by_cases h₂ : d = r - 1
  · -- (P6) P
    subst h₂
    rw [lowSeg_del_self (fun i hi => ⟨by omega, by omega⟩)] at hW ⊢
    have e₂ := prefixTail_del_P hr
    rw [e₂] at hW ⊢
    exact ⟨_, Nat.le_refl _, prefix_P hr hW⟩
  by_cases h₃ : d = r
  · -- (P2) E_0
    subst h₃
    rw [lowSeg_del_self (fun i hi => ⟨by omega, by omega⟩)] at hW ⊢
    have e₂ := prefixTail_del_E0 hr
    rw [e₂] at hW ⊢
    exact ⟨_, Nat.le_refl _, prefix_E0 hr hW⟩
  by_cases h₄ : d = r + 1
  · -- (P1) Q_0
    subst h₄
    have e₁ : delete (r+1) (lowSeg r 0 (r-1)) = [0] ++ lowSeg r 1 (r-2) := by
      rw [lowSeg_full r hr, delete_append,
        delete_eq_self (lowSeg_ne (fun i _ _ => ⟨by omega, by omega⟩))]
      congr 1
      simp (disch := omega) only [delete_cons', delete_nil', ite_no, ite_T]
    have e₂ : delete (r+1) (prefixTail r) = prefixTail r :=
      prefixTail_del_self ⟨by omega, by omega, by omega, by omega, by omega, by omega⟩
    rw [e₁, e₂] at hW ⊢
    exact ⟨_, Nat.le_refl _, prefix_Q0 hr (by simpa using hW)⟩
  by_cases h₅ : d ≤ 3*r-3 ∧ (d - r) % 2 = 1
  · -- (P2) Q_t with t >= 1
    obtain ⟨t, rfl⟩ : ∃ t, d = r+1+2*t := ⟨(d-r-1)/2, by omega⟩
    have e₁ : delete (r+1+2*t) (lowSeg r 0 (r-1)) =
        lowSeg r 0 t ++ ([t] ++ lowSeg r (t+1) (r-2-t)) := by
      rw [lowSeg_cut r t (by omega), delete_append, delete_append,
        delete_eq_self (lowSeg_ne (fun i _ _ => ⟨by omega, by omega⟩)),
        delete_eq_self (lowSeg_ne (fun i _ _ => ⟨by omega, by omega⟩))]
      rw [pair_del_rec]
    have e₂ : delete (r+1+2*t) (prefixTail r) = prefixTail r :=
      prefixTail_del_self ⟨by omega, by omega, by omega, by omega, by omega, by omega⟩
    rw [e₁, e₂] at hW ⊢
    exact ⟨_, Nat.le_refl _, prefix_Q hr (t := t) (by omega) (by omega) (by simpa using hW)⟩
  -- From here `d` is not in the low phase: the standard low phase applies.
  have hlow : delete d (lowSeg r 0 (r-1)) = lowSeg r 0 (r-1) :=
    lowSeg_del_self (fun i hi => ⟨by omega, by omega⟩)
  rw [hlow] at hW ⊢
  have hQ : ∀ j, j + 2 ≤ r → d ≠ r+1+2*j := fun j hj => by omega
  have hlen : (lowSeg r 0 (r-1) ++ [r]).length = 2*r-1 := by
    simp [length_lowSeg]; omega
  by_cases h₆ : d = r + 2
  · -- (P3) E_1
    subst h₆
    have e₂ := prefixTail_del_E1 hr
    rw [e₂] at hW ⊢
    have hq := std_qphase hr (d := r+2) (rem := [3*r, r-1, 3*r+2, 3*r-1] ++ rem) (by omega) hQ
      (by simpa using hW)
    exact ⟨_, Nat.le_refl _, by simpa using mphase_E1 hr hq hlen⟩
  by_cases h₇ : d < 3*r-2
  · -- an O_0 relay E_s, s >= 2: the standard prefix leaves C at depth r-3
    have e₂ : delete d (prefixTail r) = prefixTail r :=
      prefixTail_del_self ⟨by omega, by omega, by omega, by omega, by omega, by omega⟩
    rw [e₂] at hW ⊢
    have hq := std_qphase hr (d := d) (rem := [3*r, r-1, 3*r+2, 3*r-1, r+2] ++ rem) (by omega)
      hQ (by simpa [prefixTail] using hW)
    have hm := mphase_std hr hq hlen (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega)
    have hL := Prog.toLoose (bot := []) (by simpa using hm)
      (by rw [readCount_lt' (by omega)]; simp [length_lowSeg]; omega)
    exact ⟨_, Nat.le_refl _, by simpa [prefixTail] using hL⟩
  by_cases h₈ : d = 3*r-2
  · -- C: regime Z
    subst h₈
    have e₂ : delete (3*r-2) (prefixTail r) = prefixTail r :=
      prefixTail_del_self ⟨by omega, by omega, by omega, by omega, by omega, by omega⟩
    rw [e₂] at hW ⊢
    have hq := std_qphase hr (d := 3*r-2) (rem := [3*r, r-1, 3*r+2, 3*r-1, r+2] ++ rem)
      (by omega) hQ (by simpa [prefixTail] using hW)
    exact ⟨_, Nat.le_refl _, by simpa [prefixTail] using mphase_C hr hq hlen⟩
  by_cases h₉ : d = 3*r-1
  · -- (P4) U
    subst h₉
    have e₂ := prefixTail_del_U hr
    rw [e₂] at hW ⊢
    have hq := std_qphase hr (d := 3*r-1) (rem := [3*r, r-1, 3*r+2, r+2] ++ rem)
      (by omega) hQ (by simpa using hW)
    exact ⟨_, Nat.le_refl _, by simpa using mphase_U hr hq hlen⟩
  by_cases h₁₀ : d = 3*r
  · -- (P5) M1
    subst h₁₀
    have e₂ := prefixTail_del_M1 hr
    rw [e₂] at hW ⊢
    have hq := std_qphase hr (d := 3*r) (rem := [r-1, 3*r+2, 3*r-1, r+2] ++ rem)
      (by omega) hQ (by simpa using hW)
    exact ⟨_, Nat.le_refl _, by simpa using mphase_M1 hr hq hlen⟩
  by_cases h₁₁ : d = 3*r+1
  · -- V
    subst h₁₁
    have e₂ : delete (3*r+1) (prefixTail r) = prefixTail r :=
      prefixTail_del_self ⟨by omega, by omega, by omega, by omega, by omega, by omega⟩
    rw [e₂] at hW ⊢
    have hq := std_qphase hr (d := 3*r+1) (rem := [3*r, r-1, 3*r+2, 3*r-1, r+2] ++ rem)
      (by omega) hQ (by simpa [prefixTail] using hW)
    exact ⟨_, Nat.le_refl _, by simpa [prefixTail] using mphase_V hr hq hlen⟩
  · -- (P7) M2
    have h₁₂ : d = 3*r+2 := by omega
    subst h₁₂
    have e₂ := prefixTail_del_M2 hr
    rw [e₂] at hW ⊢
    have hq := std_qphase hr (d := 3*r+2) (rem := [3*r, r-1, 3*r-1, r+2] ++ rem)
      (by omega) hQ (by simpa using hW)
    exact ⟨3*r+1, by omega, by simpa using mphase_M2 hr hq hlen⟩

/-- With no deletion below `a_0`, the prefix ends in regime S. -/
theorem prefix_std (hr : 3 ≤ r) {rem : List Nat} (hd : 3*r+3 ≤ d)
    (hW : (lowSeg r 0 (r-1) ++ (prefixTail r ++ rem)).Nodup) :
    Std r d (3*r+3) (lowSeg r 0 (r-1) ++ prefixTail r) rem := by
  have hQ : ∀ j, j + 2 ≤ r → d ≠ r+1+2*j := fun j hj => by omega
  have hlen : (lowSeg r 0 (r-1) ++ [r]).length = 2*r-1 := by
    simp [length_lowSeg]; omega
  have hq := std_qphase hr (d := d) (rem := [3*r, r-1, 3*r+2, 3*r-1, r+2] ++ rem) (by omega)
    hQ (by simpa [prefixTail] using hW)
  have hm := mphase_std hr hq hlen (by omega) (by omega) (by omega) (by omega) (by omega)
    (by omega)
  refine ⟨by simpa [prefixTail] using hm, ?_⟩
  rw [readCount_ge' hd]
  simp [length_lowSeg, prefixTail]
  omega

theorem stepSeg_cut (r k j : Nat) (hj : j < k) :
    stepSeg r 0 k = stepSeg r 0 j ++
      ([3*r+5+3*j, 3*r+3+3*j, qv r j] ++ stepSeg r (j+1) (k-(j+1))) := by
  have h₁ := stepSeg_append r 0 j (k-(j+1)+1)
  rw [stepSeg_succ, show 0 + j = j by omega, show j + (k-(j+1)+1) = k by omega] at h₁
  exact h₁.symm

theorem stepSeg_del_self {r a c : Nat} (hr : 3 ≤ r) (hd : 3*r+3+3*(a+c) ≤ d) :
    delete d (stepSeg r a c) = stepSeg r a c :=
  delete_eq_self (fun x hx => by
    obtain ⟨j, h₁, h₂, hx⟩ := mem_stepSeg.mp hx
    have := qv_lt r j hr
    omega)

/-- The common shape: deleting `d` from the whole family. -/
theorem famA_delete_eq (r k : Nat) : delete d (famA r k) = delete d (lowSeg r 0 (r-1)) ++
    (delete d (prefixTail r) ++ (delete d (stepSeg r 0 k) ++ delete d (finA r k))) := by
  rw [famA_eq]; simp only [delete_append]

theorem famB_delete_eq (r k : Nat) : delete d (famB r k) = delete d (lowSeg r 0 (r-1)) ++
    (delete d (prefixTail r) ++ (delete d (stepSeg r 0 k) ++ delete d (finB r k))) := by
  rw [famB_eq]; simp only [delete_append]

/-- Every single deletion of `A_r(k)` is generated by the original `(r,r)`
machine. -/
theorem famA_deletion (hr : 3 ≤ r) {k : Nat} (hd : d < 3*r+7+3*k) :
    Run r r [] (delete d (List.range (3*r+7+3*k))) (delete d (famA r k)) [] := by
  have hW := delete_nodup (d := d) (famA_nodup r k hr)
  have hlen := length_delete_perm (famA_perm r k hr) hd
  rw [famA_delete_eq] at hW hlen ⊢
  simp only [List.length_append] at hlen
  apply run_of_prog hd _ (by simp only [List.length_append]; omega)
  by_cases hd₀ : d < 3*r+3
  · obtain ⟨next, hn, hL⟩ := prefix_loose hr hd₀
      (rem := delete d (stepSeg r 0 k) ++ delete d (finA r k)) (by simpa using hW)
    have h := Loose.finishA hr (k := k) (j := 0) (by simpa using hL) (Nat.zero_le _) hn hd₀
      (by simp only [List.length_append, Nat.sub_zero]; omega)
    simpa using h
  have hlow : delete d (lowSeg r 0 (r-1)) = lowSeg r 0 (r-1) :=
    lowSeg_del_self (fun i hi => ⟨by omega, by omega⟩)
  have htail : delete d (prefixTail r) = prefixTail r :=
    prefixTail_del_self ⟨by omega, by omega, by omega, by omega, by omega, by omega⟩
  rw [hlow, htail] at hW hlen ⊢
  by_cases hd₁ : d < 3*r+3+3*k
  · -- a deletion inside step j
    obtain ⟨j, e, he, hdj⟩ : ∃ j e, e < 3 ∧ d = 3*r+3+3*j+e :=
      ⟨(d-(3*r+3))/3, (d-(3*r+3))%3, by omega, by omega⟩
    have hjk : j < k := by omega
    rw [stepSeg_cut r k j hjk, delete_append, delete_append,
      stepSeg_del_self (a := 0) (c := j) hr (by omega)] at hW hlen ⊢
    have hS := prefix_std hr (d := d) (by omega) (by simpa using hW)
    have hS₁ := Std.steps hr j 0 (by simpa using hS) (by omega)
    have hn₁ : 3*r+3+3*(0+j) = 3*r+3+3*j := by omega
    rw [hn₁] at hS₁
    have hq := qv_lt r j hr
    have hfin : ∀ {next : Nat} {out : List Nat}, next ≤ 3*r+3+3*(j+1) →
        Loose r d next out (delete d (stepSeg r (j+1) (k-(j+1))) ++ delete d (finA r k)) →
        out.length + (delete d (stepSeg r (j+1) (k-(j+1)))).length +
          (delete d (finA r k)).length = 3*r+6+3*k →
        Prog r d (3*r+7+3*k) [] [] (out ++ delete d (stepSeg r (j+1) (k-(j+1))) ++
          delete d (finA r k)) [] := by
      intro next out hn hL hl
      exact Loose.finishA hr (k := k) (j := j+1) hL (by omega) hn (by omega) hl
    rcases (by omega : e = 0 ∨ e = 1 ∨ e = 2) with rfl | rfl | rfl
    · -- a_j
      have e₁ : delete d [3*r+5+3*j, 3*r+3+3*j, qv r j] = [3*r+5+3*j, qv r j] := by
        rw [show d = 3*r+3+3*j by omega]; exact step_del_a hr j
      rw [e₁] at hW hlen hS₁ ⊢
      have hL := Std.del_a hr (j := j) (by simpa using hS₁) (by omega)
      have h := hfin (next := 3*r+6+3*j) (by omega) (by simpa using hL)
        (by simp only [List.length_append, List.length_cons, List.length_nil,
              length_lowSeg, length_stepSeg, prefixTail] at hlen ⊢; omega)
      simpa using h
    · -- b_j
      have e₁ : delete d [3*r+5+3*j, 3*r+3+3*j, qv r j] = [3*r+5+3*j, 3*r+3+3*j, qv r j] := by
        rw [show d = 3*r+4+3*j by omega]; exact step_del_b hr j
      rw [e₁] at hW hlen hS₁ ⊢
      have hL := Std.del_b hr (j := j) (by simpa using hS₁) (by omega)
      have h := hfin (next := 3*r+6+3*j) (by omega) (by simpa using hL)
        (by simp only [List.length_append, List.length_cons, List.length_nil,
              length_lowSeg, length_stepSeg, prefixTail] at hlen ⊢; omega)
      simpa using h
    · -- R_j
      have e₁ : delete d [3*r+5+3*j, 3*r+3+3*j, qv r j] = [3*r+3+3*j, qv r j] := by
        rw [show d = 3*r+5+3*j by omega]; exact step_del_R hr j
      rw [e₁] at hW hlen hS₁ ⊢
      have hL := Std.del_R hr (j := j) (by simpa using hS₁) (by omega)
      have h := hfin (next := 3*r+4+3*j) (by omega) (by simpa using hL)
        (by simp only [List.length_append, List.length_cons, List.length_nil,
              length_lowSeg, length_stepSeg, prefixTail] at hlen ⊢; omega)
      simpa using h
  · -- a deletion in the final segment
    rw [stepSeg_del_self (a := 0) (c := k) hr (by omega)] at hW hlen ⊢
    have hS := prefix_std hr (d := d) (by omega) (by simpa using hW)
    have hS₁ := Std.steps hr k 0 (by simpa using hS) (by omega)
    have hn₁ : 3*r+3+3*(0+k) = 3*r+3+3*k := by omega
    rw [hn₁] at hS₁
    have hS₂ : Std r d (3*r+3+3*k) (lowSeg r 0 (r-1) ++ prefixTail r ++ stepSeg r 0 k)
        (delete d (finA r k)) := by simpa using hS₁
    rcases (by omega : d = 3*r+3+3*k ∨ d = 3*r+4+3*k ∨ d = 3*r+5+3*k ∨ d = 3*r+6+3*k)
      with h | h | h | h
    · simpa using Std.finalA_0 hr hS₂ h
    · simpa using Std.finalA_12 hr hS₂ (Or.inl h)
    · simpa using Std.finalA_12 hr hS₂ (Or.inr h)
    · simpa using Std.finalA_3 hr hS₂ h

/-- Every single deletion of `B_r(k)` is generated by the original `(r,r)`
machine. -/
theorem famB_deletion (hr : 3 ≤ r) {k : Nat} (hd : d < 3*r+8+3*k) :
    Run r r [] (delete d (List.range (3*r+8+3*k))) (delete d (famB r k)) [] := by
  have hW := delete_nodup (d := d) (famB_nodup r k hr)
  have hlen := length_delete_perm (famB_perm r k hr) hd
  rw [famB_delete_eq] at hW hlen ⊢
  simp only [List.length_append] at hlen
  apply run_of_prog hd _ (by simp only [List.length_append]; omega)
  by_cases hd₀ : d < 3*r+3
  · obtain ⟨next, hn, hL⟩ := prefix_loose hr hd₀
      (rem := delete d (stepSeg r 0 k) ++ delete d (finB r k)) (by simpa using hW)
    have h := Loose.finishB hr (k := k) (j := 0) (by simpa using hL) (Nat.zero_le _) hn hd₀
      (by simp only [List.length_append, Nat.sub_zero]; omega)
    simpa using h
  have hlow : delete d (lowSeg r 0 (r-1)) = lowSeg r 0 (r-1) :=
    lowSeg_del_self (fun i hi => ⟨by omega, by omega⟩)
  have htail : delete d (prefixTail r) = prefixTail r :=
    prefixTail_del_self ⟨by omega, by omega, by omega, by omega, by omega, by omega⟩
  rw [hlow, htail] at hW hlen ⊢
  by_cases hd₁ : d < 3*r+3+3*k
  · obtain ⟨j, e, he, hdj⟩ : ∃ j e, e < 3 ∧ d = 3*r+3+3*j+e :=
      ⟨(d-(3*r+3))/3, (d-(3*r+3))%3, by omega, by omega⟩
    have hjk : j < k := by omega
    rw [stepSeg_cut r k j hjk, delete_append, delete_append,
      stepSeg_del_self (a := 0) (c := j) hr (by omega)] at hW hlen ⊢
    have hS := prefix_std hr (d := d) (by omega) (by simpa using hW)
    have hS₁ := Std.steps hr j 0 (by simpa using hS) (by omega)
    have hn₁ : 3*r+3+3*(0+j) = 3*r+3+3*j := by omega
    rw [hn₁] at hS₁
    have hq := qv_lt r j hr
    have hfin : ∀ {next : Nat} {out : List Nat}, next ≤ 3*r+3+3*(j+1) →
        Loose r d next out (delete d (stepSeg r (j+1) (k-(j+1))) ++ delete d (finB r k)) →
        out.length + (delete d (stepSeg r (j+1) (k-(j+1)))).length +
          (delete d (finB r k)).length = 3*r+7+3*k →
        Prog r d (3*r+8+3*k) [] [] (out ++ delete d (stepSeg r (j+1) (k-(j+1))) ++
          delete d (finB r k)) [] := by
      intro next out hn hL hl
      exact Loose.finishB hr (k := k) (j := j+1) hL (by omega) hn (by omega) hl
    rcases (by omega : e = 0 ∨ e = 1 ∨ e = 2) with rfl | rfl | rfl
    · have e₁ : delete d [3*r+5+3*j, 3*r+3+3*j, qv r j] = [3*r+5+3*j, qv r j] := by
        rw [show d = 3*r+3+3*j by omega]; exact step_del_a hr j
      rw [e₁] at hW hlen hS₁ ⊢
      have hL := Std.del_a hr (j := j) (by simpa using hS₁) (by omega)
      have h := hfin (next := 3*r+6+3*j) (by omega) (by simpa using hL)
        (by simp only [List.length_append, List.length_cons, List.length_nil,
              length_lowSeg, length_stepSeg, prefixTail] at hlen ⊢; omega)
      simpa using h
    · have e₁ : delete d [3*r+5+3*j, 3*r+3+3*j, qv r j] = [3*r+5+3*j, 3*r+3+3*j, qv r j] := by
        rw [show d = 3*r+4+3*j by omega]; exact step_del_b hr j
      rw [e₁] at hW hlen hS₁ ⊢
      have hL := Std.del_b hr (j := j) (by simpa using hS₁) (by omega)
      have h := hfin (next := 3*r+6+3*j) (by omega) (by simpa using hL)
        (by simp only [List.length_append, List.length_cons, List.length_nil,
              length_lowSeg, length_stepSeg, prefixTail] at hlen ⊢; omega)
      simpa using h
    · have e₁ : delete d [3*r+5+3*j, 3*r+3+3*j, qv r j] = [3*r+3+3*j, qv r j] := by
        rw [show d = 3*r+5+3*j by omega]; exact step_del_R hr j
      rw [e₁] at hW hlen hS₁ ⊢
      have hL := Std.del_R hr (j := j) (by simpa using hS₁) (by omega)
      have h := hfin (next := 3*r+4+3*j) (by omega) (by simpa using hL)
        (by simp only [List.length_append, List.length_cons, List.length_nil,
              length_lowSeg, length_stepSeg, prefixTail] at hlen ⊢; omega)
      simpa using h
  · rw [stepSeg_del_self (a := 0) (c := k) hr (by omega)] at hW ⊢
    have hS := prefix_std hr (d := d) (by omega) (by simpa using hW)
    have hS₁ := Std.steps hr k 0 (by simpa using hS) (by omega)
    have hn₁ : 3*r+3+3*(0+k) = 3*r+3+3*k := by omega
    rw [hn₁] at hS₁
    have hS₂ : Std r d (3*r+3+3*k) (lowSeg r 0 (r-1) ++ prefixTail r ++ stepSeg r 0 k)
        (delete d (finB r k)) := by simpa using hS₁
    rcases (by omega : d = 3*r+3+3*k ∨ d = 3*r+4+3*k ∨ d = 3*r+5+3*k ∨ d = 3*r+6+3*k ∨
      d = 3*r+7+3*k) with h | h | h | h | h
    · simpa using Std.finalB_0 hr hS₂ h
    · simpa using Std.finalB_1 hr hS₂ h
    · simpa using Std.finalB_2 hr hS₂ h
    · simpa using Std.finalB_3 hr hS₂ h
    · simpa using Std.finalB_4 hr hS₂ h

#print axioms prefix_loose
#print axioms famA_deletion
#print axioms famB_deletion
end Equal
end StackSorting.Generalized
