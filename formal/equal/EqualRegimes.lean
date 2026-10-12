import EqualHist

/-! The regimes of Section 5.2 of `docs/infinite-basis-equal-width-draft.md`,
their steps, and the final segments (Sections 5.3 and 5.5).

`C = 3r-2` is the carrier. In `Std` (regime S) nothing below `next` has been
deleted and the stack is `Q ++ [C]` with exactly `r-1` tokens. In `Loose`
(regimes L and Z) the tracked prefix has at most `r-2` tokens and contains
`C` unless `C` itself was deleted; unread old tokens may be pending. -/
namespace StackSorting.Generalized
namespace Equal
open BasisFamily (delete)
open Unequal (lowSeg readCount delete_append delete_eq_self delete_cons_self delete_cons_ne mem_delete
  length_delete_le)

variable {r d : Nat}

/-- The final segment of `A_r(k)` after the steps. -/
def finA (r k : Nat) : List Nat :=
  [3*r+6+3*k, 3*r+3+3*k, 3*r-2] ++ queue r k ++ [3*r+4+3*k, 3*r+5+3*k]

/-- The final segment of `B_r(k)` after the steps. -/
def finB (r k : Nat) : List Nat :=
  [3*r+5+3*k, 3*r+3+3*k, 3*r+7+3*k, 3*r-2] ++ queue r k ++ [3*r+4+3*k, 3*r+6+3*k]

theorem famA_eq (r k : Nat) :
    famA r k = lowSeg r 0 (r-1) ++ (prefixTail r ++ (stepSeg r 0 k ++ finA r k)) := by
  simp [famA, finA]

theorem famB_eq (r k : Nat) :
    famB r k = lowSeg r 0 (r-1) ++ (prefixTail r ++ (stepSeg r 0 k ++ finB r k)) := by
  simp [famB, finB]

theorem queue_bound {r k y : Nat} (hr : 3 ≤ r) (hy : y ∈ queue r k) :
    y < 3*r+3+3*k ∧ y ≠ 3*r-2 := by
  obtain ⟨i, h₁, h₂, rfl⟩ := mem_queue.mp hy
  rcases qv_cases r i with ⟨_, h⟩ | ⟨_, h⟩ <;> omega

theorem length_delete_queue {r k : Nat} : (delete d (queue r k)).length ≤ r - 2 := by
  have := length_delete_le (d := d) (l := queue r k)
  rw [length_queue] at this
  exact this

def Loose (r d next : Nat) (out rem : List Nat) : Prop :=
  ∃ top, Prog r d next top [] out rem ∧ top.length + 2 ≤ r ∧ (3*r-2 = d ∨ 3*r-2 ∈ top)

def Std (r d next : Nat) (out rem : List Nat) : Prop :=
  Prog r d next [] [3*r-2] out rem ∧ readCount d next = out.length + (r-1)

theorem Prog.pop_any {next y : Nat} {top out rem : List Nat}
    (h : Prog r d next top [] out (y :: rem)) (hy : y < next) (hyd : y ≠ d)
    (hc : readCount d next ≤ out.length + r) :
    ∃ top', Prog r d next top' [] (out ++ [y]) rem ∧ top'.length ≤ top.length ∧
      ∀ x ∈ top, x ≠ y → x ∈ top' := by
  obtain ⟨top', h', hl, hm⟩ := h.1.pop_any hy hyd h.not_out hc
  exact ⟨top', ⟨h', by simpa using h.2⟩, hl, hm⟩

theorem Prog.absorb {next : Nat} {top bot out rem : List Nat} (h : Prog r d next top bot out rem) :
    ∃ t, Prog r d next (top ++ t ++ bot) [] out rem ∧
      (top ++ t ++ bot).length + out.length = readCount d next := by
  obtain ⟨t, h', hl⟩ := h.1.absorb
  exact ⟨t, ⟨h', h.2⟩, hl⟩

/-- Leave regime S with a stack whose bottom token is `C`, or `C` above one
extra token, once at most `r-2` tokens lie above that bottom part. -/
theorem Prog.toLoose {next : Nat} {bot out rem : List Nat}
    (h : Prog r d next [] ((3*r-2) :: bot) out rem)
    (hc : readCount d next + 2 ≤ out.length + r + bot.length) :
    Loose r d next out rem := by
  obtain ⟨t, h', hl⟩ := h.absorb
  have h'' : Prog r d next ((t ++ [3*r-2]) ++ bot) [] out rem := by simpa using h'
  refine ⟨t ++ [3*r-2], h''.demote_top, ?_, Or.inr (by simp)⟩
  simp only [List.nil_append, List.length_append, List.length_cons, List.length_nil] at hl ⊢
  omega

theorem delete_step {r j : Nat} (c : Nat) (hd : d < 3*r+3+3*j) :
    delete d (stepSeg r j (c+1)) =
      [3*r+5+3*j, 3*r+3+3*j] ++ (delete d [qv r j] ++ delete d (stepSeg r (j+1) c)) := by
  rw [stepSeg_succ, delete_append]
  have h₁ : [3*r+5+3*j, 3*r+3+3*j, qv r j] = (3*r+5+3*j) :: (3*r+3+3*j) :: [qv r j] := rfl
  rw [h₁, delete_cons_ne _ (by omega), delete_cons_ne _ (by omega)]
  simp

/-! Regime L/Z steps. -/

theorem Loose.cast {next next' : Nat} {out rem : List Nat} (h : Loose r d next out rem)
    (he : next = next') : Loose r d next' out rem := by
  subst he; exact h

theorem Std.cast {next next' : Nat} {out rem : List Nat} (h : Std r d next out rem)
    (he : next = next') : Std r d next' out rem := by
  subst he; exact h

theorem Loose.step (hr : 3 ≤ r) {j next : Nat} {out rem : List Nat}
    (h : Loose r d next out ([3*r+5+3*j, 3*r+3+3*j] ++ (delete d [qv r j] ++ rem)))
    (hn : next ≤ 3*r+3+3*j) (hd : d < 3*r+3+3*j)
    (hlive : readCount d (3*r+3+3*j) + 1 ≤ out.length + r) :
    Loose r d (3*r+6+3*j) (out ++ ([3*r+5+3*j, 3*r+3+3*j] ++ delete d [qv r j])) rem := by
  obtain ⟨top, hp, hl, hC⟩ := h
  have h₁ := hp.read (by omega) (3*r+3+3*j - next)
  rw [show next + (3*r+3+3*j - next) = 3*r+3+3*j by omega] at h₁
  have h₂ := h₁.push_protect (by omega) (by omega)
  have h₃ := h₂.push_top (by simp; omega) (by omega)
  have h₄ := Prog.recordEq (v := 3*r+5+3*j) (by simpa using h₃) (by omega) (by omega) (by omega)
  have h₅ := Prog.pop_top (p := top) (q := []) (by simpa using h₄) (by omega)
  have hrc : readCount d (3*r+3+3*j+1+1+1) = readCount d (3*r+3+3*j) + 3 := by
    rw [readCount_lt' (by omega), readCount_lt' (by omega)]; omega
  have he : 3*r+3+3*j+1+1+1 = 3*r+6+3*j := by omega
  have hrc' : readCount d (3*r+6+3*j) = readCount d (3*r+3+3*j) + 3 := by
    rw [readCount_lt' (by omega), readCount_lt' (by omega)]; omega
  by_cases hq : qv r j = d
  · have hdel : delete d [qv r j] = [] := by simp [delete, hq]
    rw [hdel] at h₅
    refine ⟨top, ?_, hl, hC⟩
    rw [hdel]
    have h₆ : Prog r d (3*r+5+3*j+1) top [] (out ++ [3*r+5+3*j, 3*r+3+3*j]) rem := by
      simpa using h₅
    simpa using h₆.cast (show 3*r+5+3*j+1 = 3*r+6+3*j by omega)
  · have hdel : delete d [qv r j] = [qv r j] := by simp [delete, hq]
    rw [hdel] at h₅
    have h₅' : Prog r d (3*r+5+3*j+1) top [] (out ++ [3*r+5+3*j, 3*r+3+3*j])
        (qv r j :: rem) := by simpa using h₅
    obtain ⟨top', h₆, hl', hm'⟩ := (h₅'.cast (show 3*r+5+3*j+1 = 3*r+6+3*j by omega)).pop_any
      (by have := qv_lt r j hr; omega) hq (by rw [hrc']; simp; omega)
    refine ⟨top', ?_, by omega, ?_⟩
    · rw [hdel]
      simpa using h₆
    · rcases hC with hC | hC
      · exact Or.inl hC
      · exact Or.inr (hm' _ hC (Ne.symm (qv_ne_C r j hr)))

theorem Loose.steps (hr : 3 ≤ r) :
    ∀ c j {next : Nat} {out rem : List Nat},
      Loose r d next out (delete d (stepSeg r j c) ++ rem) → next ≤ 3*r+3+3*j →
      d < 3*r+3+3*j →
      readCount d (3*r+3+3*j) + 3*c + 1 ≤ out.length + (delete d (stepSeg r j c)).length + r →
      ∃ next', next' ≤ 3*r+3+3*(j+c) ∧ Loose r d next' (out ++ delete d (stepSeg r j c)) rem := by
  intro c
  induction c with
  | zero =>
    intro j next out rem h hn _ _
    exact ⟨next, by omega, by simpa [stepSeg, delete] using h⟩
  | succ c ih =>
    intro j next out rem h hn hd hlive
    rw [delete_step c hd] at h hlive ⊢
    have hl₀ := length_delete_le (d := d) (l := stepSeg r (j+1) c)
    rw [length_stepSeg] at hl₀
    have hq₀ := length_delete_le (d := d) (l := [qv r j])
    simp only [List.length_append, List.length_cons, List.length_nil] at hlive hq₀
    have h₁ := Loose.step hr (by simpa [List.append_assoc] using h) hn hd (by omega)
    have hn₁ : 3*r+6+3*j = 3*r+3+3*(j+1) := by omega
    rw [hn₁] at h₁
    obtain ⟨n', hn', h₂⟩ := ih (j+1) h₁ (by omega) (by omega) (by
      rw [readCount_lt' (by omega)]
      rw [readCount_lt' (by omega)] at hlive
      simp only [List.length_append, List.length_cons, List.length_nil]
      omega)
    refine ⟨n', by omega, ?_⟩
    simpa [List.append_assoc] using h₂

theorem delete_finA {r k : Nat} (hd : d < 3*r+3+3*k) :
    delete d (finA r k) = [3*r+6+3*k, 3*r+3+3*k] ++
      (delete d [3*r-2] ++ (delete d (queue r k) ++ [3*r+4+3*k, 3*r+5+3*k])) := by
  have e₁ : delete d [3*r+6+3*k, 3*r+3+3*k, 3*r-2] =
      [3*r+6+3*k, 3*r+3+3*k] ++ delete d [3*r-2] := by
    rw [delete_cons_ne _ (by omega), delete_cons_ne _ (by omega)]; rfl
  have e₂ : delete d [3*r+4+3*k, 3*r+5+3*k] = [3*r+4+3*k, 3*r+5+3*k] :=
    delete_eq_self (by intro x hx; simp at hx; omega)
  simp only [finA, delete_append, e₁, e₂, List.append_assoc]

theorem delete_finB {r k : Nat} (hd : d < 3*r+3+3*k) :
    delete d (finB r k) = [3*r+5+3*k, 3*r+3+3*k, 3*r+7+3*k] ++
      (delete d [3*r-2] ++ (delete d (queue r k) ++ [3*r+4+3*k, 3*r+6+3*k])) := by
  have e₁ : delete d [3*r+5+3*k, 3*r+3+3*k, 3*r+7+3*k, 3*r-2] =
      [3*r+5+3*k, 3*r+3+3*k, 3*r+7+3*k] ++ delete d [3*r-2] := by
    rw [delete_cons_ne _ (by omega), delete_cons_ne _ (by omega), delete_cons_ne _ (by omega)]; rfl
  have e₂ : delete d [3*r+4+3*k, 3*r+6+3*k] = [3*r+4+3*k, 3*r+6+3*k] :=
    delete_eq_self (by intro x hx; simp at hx; omega)
  simp only [finB, delete_append, e₁, e₂, List.append_assoc]

/-- Pop `C` from the tracked prefix, if it was not deleted, then forget the
prefix. -/
theorem Prog.popC {next : Nat} {top out rem : List Nat}
    (h : Prog r d next top [] out (delete d [3*r-2] ++ rem))
    (hC : 3*r-2 = d ∨ 3*r-2 ∈ top) (hl : top.length + 2 ≤ r) :
    Prog r d next [] [] (out ++ delete d [3*r-2]) rem := by
  by_cases hCd : 3*r-2 = d
  · have hdel : delete d [3*r-2] = [] := by simp [delete, hCd]
    rw [hdel] at h ⊢
    simpa using h.demote_top (p := []) (q := top)
  · have hdel : delete d [3*r-2] = [3*r-2] := by simp [delete, hCd]
    rw [hdel] at h ⊢
    have hm : 3*r-2 ∈ top := by rcases hC with hC | hC; exact absurd hC hCd; exact hC
    obtain ⟨p, q, rfl⟩ := List.append_of_mem hm
    have h₁ := Prog.pop_top (by simpa using h) (by simp at hl; omega)
    exact h₁.demote_top (p := []) (q := p ++ q)

theorem Loose.finalA (hr : 3 ≤ r) {k next : Nat} {out : List Nat}
    (h : Loose r d next out (delete d (finA r k)))
    (hn : next ≤ 3*r+3+3*k) (hd : d < 3*r+3+3*k)
    (hlen : out.length + (delete d (finA r k)).length = 3*r+6+3*k) :
    Prog r d (3*r+7+3*k) [] [] (out ++ delete d (finA r k)) [] := by
  obtain ⟨top, hp, hl, hC⟩ := h
  rw [delete_finA hd] at hp hlen ⊢
  have h₁ := hp.read (by omega) (3*r+3+3*k - next)
  rw [show next + (3*r+3+3*k - next) = 3*r+3+3*k by omega] at h₁
  have h₂ := h₁.push_protect (by omega) (by omega)
  have h₃ := h₂.push_top (by simp; omega) (by omega)
  have h₄ := h₃.push_top (by simp; omega) (by omega)
  have h₅ := Prog.recordEq (v := 3*r+6+3*k) (by simpa using h₄) (by omega) (by omega) (by omega)
  have h₆ := Prog.pop_top (p := top) (q := []) (by simpa using h₅) (by omega)
  have h₇ := Prog.popC (by simpa using h₆) hC hl
  have hlq := length_delete_queue (d := d) (r := r) (k := k)
  have hlC := length_delete_le (d := d) (l := [3*r-2])
  simp only [List.length_append, List.length_cons, List.length_nil] at hlen hlC
  have h₈ := Prog.drain (delete d (queue r k) ++ [3*r+4+3*k, 3*r+5+3*k])
    (rem := []) (by simpa using h₇)
    (by
      intro y hy
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hy
      rcases hy with hy | hy | hy
      · obtain ⟨hy, hyd⟩ := mem_delete.mp hy
        exact ⟨by have := queue_bound hr hy; omega, hyd⟩
      · exact ⟨by omega, by omega⟩
      · exact ⟨by omega, by omega⟩)
    (by rw [readCount_lt' (by omega)]; simp; omega)
  simpa [List.append_assoc] using h₈.cast (show 3*r+6+3*k+1 = 3*r+7+3*k by omega)

theorem Loose.finalB (hr : 3 ≤ r) {k next : Nat} {out : List Nat}
    (h : Loose r d next out (delete d (finB r k)))
    (hn : next ≤ 3*r+3+3*k) (hd : d < 3*r+3+3*k)
    (hlen : out.length + (delete d (finB r k)).length = 3*r+7+3*k) :
    Prog r d (3*r+8+3*k) [] [] (out ++ delete d (finB r k)) [] := by
  obtain ⟨top, hp, hl, hC⟩ := h
  rw [delete_finB hd] at hp hlen ⊢
  have h₁ := hp.read (by omega) (3*r+3+3*k - next)
  rw [show next + (3*r+3+3*k - next) = 3*r+3+3*k by omega] at h₁
  have h₂ := h₁.push_protect (by omega) (by omega)
  have h₃ := h₂.push_top (by simp; omega) (by omega)
  have h₄ := Prog.recordEq (v := 3*r+5+3*k) (by simpa using h₃) (by omega) (by omega) (by omega)
  have h₅ := Prog.pop_top (p := top) (q := []) (by simpa using h₄) (by omega)
  have h₆ := h₅.push_top (by simp; omega) (by omega)
  have h₇ := Prog.recordEq (v := 3*r+7+3*k) (by simpa using h₆) (by omega) (by omega) (by omega)
  have h₈ := Prog.popC (by simpa using h₇) hC hl
  have hlq := length_delete_queue (d := d) (r := r) (k := k)
  have hlC := length_delete_le (d := d) (l := [3*r-2])
  simp only [List.length_append, List.length_cons, List.length_nil] at hlen hlC
  have h₉ := Prog.drain (delete d (queue r k) ++ [3*r+4+3*k, 3*r+6+3*k])
    (rem := []) (by simpa using h₈)
    (by
      intro y hy
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hy
      rcases hy with hy | hy | hy
      · obtain ⟨hy, hyd⟩ := mem_delete.mp hy
        exact ⟨by have := queue_bound hr hy; omega, hyd⟩
      · exact ⟨by omega, by omega⟩
      · exact ⟨by omega, by omega⟩)
    (by rw [readCount_lt' (by omega)]; simp; omega)
  simpa [List.append_assoc] using h₉.cast (show 3*r+7+3*k+1 = 3*r+8+3*k by omega)

/-- From regime L/Z at step `j`: all remaining steps and the final segment of
`A_r(k)`. The only count hypothesis is the global length of the target. -/
theorem Loose.finishA (hr : 3 ≤ r) {k j next : Nat} {out : List Nat}
    (h : Loose r d next out (delete d (stepSeg r j (k-j)) ++ delete d (finA r k)))
    (hj : j ≤ k) (hn : next ≤ 3*r+3+3*j) (hd : d < 3*r+3+3*j)
    (hlen : out.length + (delete d (stepSeg r j (k-j))).length +
      (delete d (finA r k)).length = 3*r+6+3*k) :
    Prog r d (3*r+7+3*k) [] [] (out ++ delete d (stepSeg r j (k-j)) ++ delete d (finA r k)) [] := by
  have hfin := length_delete_le (d := d) (l := finA r k)
  have hfl : (finA r k).length = r + 3 := by
    simp [finA, length_queue]; omega
  obtain ⟨n', hn', h₁⟩ := Loose.steps hr (k-j) j h hn hd (by
    rw [readCount_lt' (by omega)]; omega)
  have he : j + (k - j) = k := by omega
  rw [he] at hn'
  exact Loose.finalA hr h₁ hn' (by omega) (by simp only [List.length_append]; omega)

theorem Loose.finishB (hr : 3 ≤ r) {k j next : Nat} {out : List Nat}
    (h : Loose r d next out (delete d (stepSeg r j (k-j)) ++ delete d (finB r k)))
    (hj : j ≤ k) (hn : next ≤ 3*r+3+3*j) (hd : d < 3*r+3+3*j)
    (hlen : out.length + (delete d (stepSeg r j (k-j))).length +
      (delete d (finB r k)).length = 3*r+7+3*k) :
    Prog r d (3*r+8+3*k) [] [] (out ++ delete d (stepSeg r j (k-j)) ++ delete d (finB r k)) [] := by
  have hfin := length_delete_le (d := d) (l := finB r k)
  have hfl : (finB r k).length = r + 4 := by
    simp [finB, length_queue]; omega
  obtain ⟨n', hn', h₁⟩ := Loose.steps hr (k-j) j h hn hd (by
    rw [readCount_lt' (by omega)]; omega)
  have he : j + (k - j) = k := by omega
  rw [he] at hn'
  exact Loose.finalB hr h₁ hn' (by omega) (by simp only [List.length_append]; omega)

/-! Regime S steps. -/

theorem Std.step (hr : 3 ≤ r) {j : Nat} {out rem : List Nat}
    (h : Std r d (3*r+3+3*j) out ([3*r+5+3*j, 3*r+3+3*j, qv r j] ++ rem))
    (hd : 3*r+5+3*j < d) :
    Std r d (3*r+6+3*j) (out ++ [3*r+5+3*j, 3*r+3+3*j, qv r j]) rem := by
  obtain ⟨hp, hc⟩ := h
  have hq := qv_lt r j hr
  have hqC := qv_ne_C r j hr
  have h₁ := Prog.push_in_bot (p := []) (q := [3*r-2]) (by simpa using hp)
    (by simp; omega) (by omega)
  have h₂ := Prog.push_in_bot (p := [3*r+3+3*j]) (q := [3*r-2]) (by simpa using h₁)
    (by rw [readCount_ge' (by omega)]; rw [readCount_ge' (by omega)] at hc; simp; omega)
    (by omega)
  have h₃ := Prog.recordEq (v := 3*r+5+3*j) (by simpa using h₂) (by omega) (by omega) (by omega)
  have h₄ := Prog.pop_bot (p := []) (q := [3*r+3+3*j+1, 3*r-2]) (by simpa using h₃)
    (by rw [readCount_ge' (by omega)]; rw [readCount_ge' (by omega)] at hc; simp; omega)
  have h₅ := Prog.pop_mid (by simpa using h₄) (by omega) (by omega) (by simp)
    (by simp; omega)
    (by rw [readCount_ge' (by omega)]; rw [readCount_ge' (by omega)] at hc; simp; omega)
  have h₆ := Prog.demote_bot (p := [3*r+3+3*j+1]) (q := [3*r-2]) (by simpa using h₅)
  refine ⟨(by simpa using h₆ : Prog r d (3*r+5+3*j+1) [] [3*r-2] _ rem).cast (by omega), ?_⟩
  rw [readCount_ge' (by omega)]; rw [readCount_ge' (by omega)] at hc
  simp; omega

theorem Std.steps (hr : 3 ≤ r) :
    ∀ c j {out rem : List Nat}, Std r d (3*r+3+3*j) out (stepSeg r j c ++ rem) →
      3*r+3+3*(j+c) ≤ d →
      Std r d (3*r+3+3*(j+c)) (out ++ stepSeg r j c) rem := by
  intro c
  induction c with
  | zero => intro j out rem h _; simpa [stepSeg] using h
  | succ c ih =>
    intro j out rem h hd
    rw [stepSeg_succ] at h ⊢
    have h₁ := Std.step hr (by simpa [List.append_assoc] using h) (by omega)
    rw [show 3*r+6+3*j = 3*r+3+3*(j+1) by omega] at h₁
    have h₂ := ih (j+1) h₁ (by omega)
    rw [show j + 1 + c = j + (c+1) by omega] at h₂
    simpa [List.append_assoc] using h₂

/-- Section 5.3, deleting the record `R_j`. -/
theorem Std.del_R (hr : 3 ≤ r) {j : Nat} {out rem : List Nat}
    (h : Std r d (3*r+3+3*j) out ([3*r+3+3*j, qv r j] ++ rem)) (hd : d = 3*r+5+3*j) :
    Loose r d (3*r+4+3*j) (out ++ [3*r+3+3*j, qv r j]) rem := by
  obtain ⟨hp, hc⟩ := h
  rw [readCount_ge' (by omega)] at hc
  have h₁ := Prog.recordEq (v := 3*r+3+3*j) (by simpa using hp) (by omega) (by omega) (by omega)
  have h₂ := Prog.pop_mid (by simpa using h₁) (by have := qv_lt r j hr; omega)
    (by have := qv_lt r j hr; omega) (by simp)
    (by simp; exact qv_ne_C r j hr)
    (by rw [readCount_ge' (by omega)]; simp; omega)
  have h₃ := Prog.toLoose (bot := []) (by simpa using h₂)
    (by rw [readCount_ge' (by omega)]; simp; omega)
  exact (by simpa using h₃ : Loose r d (3*r+3+3*j+1) _ rem).cast (by omega)

/-- Section 5.3, deleting `a_j`. -/
theorem Std.del_a (hr : 3 ≤ r) {j : Nat} {out rem : List Nat}
    (h : Std r d (3*r+3+3*j) out ([3*r+5+3*j, qv r j] ++ rem)) (hd : d = 3*r+3+3*j) :
    Loose r d (3*r+6+3*j) (out ++ [3*r+5+3*j, qv r j]) rem := by
  obtain ⟨hp, hc⟩ := h
  rw [readCount_ge' (by omega)] at hc
  subst hd
  have h₁ := hp.skip
  have h₂ := Prog.push_in_bot (p := [3*r-2]) (q := []) (by simpa using h₁)
    (by rw [readCount_lt' (by omega)]; simp; omega) (by omega)
  have h₃ := Prog.recordEq (v := 3*r+5+3*j) (by simpa using h₂) (by omega) (by omega) (by omega)
  have h₄ := Prog.pop_mid (by simpa using h₃) (by have := qv_lt r j hr; omega)
    (by have := qv_lt r j hr; omega) (by simp)
    (by simp; exact ⟨qv_ne_C r j hr, by have := qv_lt r j hr; omega⟩)
    (by rw [readCount_lt' (by omega)]; simp; omega)
  have h₅ := Prog.toLoose (bot := [3*r+3+3*j+1]) (by simpa using h₄)
    (by rw [readCount_lt' (by omega)]; simp; omega)
  exact (by simpa using h₅ : Loose r _ (3*r+5+3*j+1) _ rem).cast (by omega)

/-- Section 5.3, deleting `b_j`. -/
theorem Std.del_b (hr : 3 ≤ r) {j : Nat} {out rem : List Nat}
    (h : Std r d (3*r+3+3*j) out ([3*r+5+3*j, 3*r+3+3*j, qv r j] ++ rem))
    (hd : d = 3*r+4+3*j) :
    Loose r d (3*r+6+3*j) (out ++ [3*r+5+3*j, 3*r+3+3*j, qv r j]) rem := by
  obtain ⟨hp, hc⟩ := h
  rw [readCount_ge' (by omega)] at hc
  subst hd
  have h₁ := Prog.push_in_bot (p := [3*r-2]) (q := []) (by simpa using hp)
    (by rw [readCount_ge' (by omega)]; simp; omega) (by omega)
  have h₂ := h₁.skipEq (by omega)
  have h₃ := Prog.recordEq (v := 3*r+5+3*j) (by simpa using h₂) (by omega) (by omega) (by omega)
  have h₄ := Prog.pop_bot (p := [3*r-2]) (q := []) (by simpa using h₃)
    (by rw [readCount_lt' (by omega)]; simp; omega)
  have h₅ := Prog.pop_mid (by simpa using h₄) (by have := qv_lt r j hr; omega)
    (by have := qv_lt r j hr; omega) (by simp)
    (by simp; exact qv_ne_C r j hr)
    (by rw [readCount_lt' (by omega)]; simp; omega)
  have h₆ := Prog.toLoose (bot := []) (by simpa using h₅)
    (by rw [readCount_lt' (by omega)]; simp; omega)
  exact (by simpa using h₆ : Loose r _ (3*r+5+3*j+1) _ rem).cast (by omega)

#print axioms Loose.finishA
#print axioms Loose.finishB
#print axioms Std.steps
#print axioms Std.del_R
#print axioms Std.del_a
#print axioms Std.del_b
end Equal
end StackSorting.Generalized
