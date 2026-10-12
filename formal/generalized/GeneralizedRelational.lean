import GeneralizedRawMachine
import GeneralizedDeletion

/-! Equivalence of executable slot-indexed histories and prefix-split semantics. -/
namespace StackSorting.Generalized

theorem insertAt_prefix (pre post : List Nat) (a : Nat) :
    insertAt? pre.length a (pre ++ post) = some (pre ++ a :: post) := by
  induction pre with
  | nil => rfl
  | cons x pre ih => simpa [insertAt?] using congrArg (Option.map (x :: ·)) ih

theorem removeAt_prefix (pre post : List Nat) (a : Nat) :
    removeAt? pre.length (pre ++ a :: post) = some (pre ++ post, a) := by
  induction pre with
  | nil => rfl
  | cons x pre ih =>
    simp [removeAt?, ih]

theorem insertAt_split (k a : Nat) (xs ys : List Nat)
    (h : insertAt? k a xs = some ys) :
    ∃ pre post, xs = pre ++ post ∧ pre.length = k ∧ ys = pre ++ a :: post := by
  induction k generalizing xs ys with
  | zero => simp [insertAt?] at h; exact ⟨[], xs, rfl, rfl, h.symm⟩
  | succ k ih =>
    cases xs with
    | nil => simp [insertAt?] at h
    | cons x xs =>
      cases ht : insertAt? k a xs with
      | none => simp [insertAt?, ht] at h
      | some zs =>
        simp [insertAt?, ht] at h
        obtain ⟨pre, post, hx, hl, hz⟩ := ih xs zs ht
        exact ⟨x :: pre, post, by simp [hx], by simp [hl], by simp [← h, hz]⟩

theorem removeAt_split (k a : Nat) (xs ys : List Nat)
    (h : removeAt? k xs = some (ys, a)) :
    ∃ pre post, xs = pre ++ a :: post ∧ pre.length = k ∧ ys = pre ++ post := by
  induction k generalizing xs ys with
  | zero =>
    cases xs with
    | nil => simp [removeAt?] at h
    | cons x xs =>
      simp [removeAt?] at h
      rcases h with ⟨rfl, rfl⟩
      exact ⟨[], xs, rfl, rfl, rfl⟩
  | succ k ih =>
    cases xs with
    | nil => simp [removeAt?] at h
    | cons x xs =>
      cases ht : removeAt? k xs with
      | none => simp [removeAt?, ht] at h
      | some p =>
        rcases p with ⟨zs, b⟩
        simp [removeAt?, ht] at h
        rcases h with ⟨rfl, rfl⟩
        obtain ⟨pre, post, hx, hl, hz⟩ := ih xs zs ht
        exact ⟨x :: pre, post, by simp [hx], by simp [hl], by simp [hz]⟩

theorem step_relational (r s : Nat) (op : RawOp) (held after out : List Nat)
    (h : step r s op held = some (after, out)) :
    Step r s held (introduced op) out after := by
  cases op with
  | push k a =>
    by_cases hk : k < r
    · cases hi : insertAt? k a held with
      | none => simp [step, hk, hi] at h
      | some zs =>
        simp [step, hk, hi] at h
        rcases h with ⟨rfl, rfl⟩
        obtain ⟨pre, post, rfl, hl, rfl⟩ := insertAt_split k a held zs hi
        exact Step.push pre post a (by simpa [hl] using hk)
    · simp [step, hk] at h
  | pop k =>
    by_cases hk : k < s
    · cases hi : removeAt? k held with
      | none => simp [step, hk, hi] at h
      | some p =>
        rcases p with ⟨zs, a⟩
        simp [step, hk, hi] at h
        rcases h with ⟨rfl, rfl⟩
        obtain ⟨pre, post, rfl, hl, rfl⟩ := removeAt_split k a held zs hi
        exact Step.pop pre post a (by simpa [hl] using hk)
    · simp [step, hk] at h

theorem Step.executable {r s : Nat} {held input output final : List Nat}
    (h : Step r s held input output final) :
    ∃ op, step r s op held = some (final, output) ∧ introduced op = input := by
  cases h with
  | push pre post x allowed =>
    exact ⟨.push pre.length x, by simp [step, allowed, insertAt_prefix], rfl⟩
  | pop pre post x allowed =>
    exact ⟨.pop pre.length, by simp [step, allowed, removeAt_prefix], rfl⟩

theorem run_relational (r s : Nat) (ops : List RawOp) (held after out : List Nat)
    (h : run r s ops held = some (after, out)) :
    Run r s held (inputs ops) out after := by
  induction ops generalizing held after out with
  | nil =>
    simp [run] at h
    rcases h with ⟨rfl, rfl⟩
    exact Run.nil held
  | cons op ops ih =>
    obtain ⟨middle, emitted, tail, hs, ht, ho⟩ := split_run r s op ops held after out h
    simpa [inputs, ho] using Run.cons (step_relational r s op held middle emitted hs)
      (ih middle after tail ht)

theorem Run.executable {r s : Nat} {held input output final : List Nat}
    (h : Run r s held input output final) :
    ∃ ops, run r s ops held = some (final, output) ∧ inputs ops = input := by
  induction h with
  | nil held => exact ⟨[], rfl, rfl⟩
  | cons head tail ih =>
    obtain ⟨op, hs, hi⟩ := head.executable
    obtain ⟨ops, hr, his⟩ := ih
    exact ⟨op :: ops, by simp [run, hs, hr], by simp [inputs] at hi his ⊢; rw [hi, his]⟩

/-- Exact semantic equivalence, with no canonicality, distinctness or sorting
hypothesis, and arbitrary initial/final physical stacks. -/
theorem run_relational_iff (r s : Nat) (held input output final : List Nat) :
    Run r s held input output final ↔
      ∃ ops, run r s ops held = some (final, output) ∧ inputs ops = input := by
  constructor
  · exact Run.executable
  · rintro ⟨ops, hr, rfl⟩
    exact run_relational r s ops held final output hr

#print axioms run_relational_iff
end StackSorting.Generalized
