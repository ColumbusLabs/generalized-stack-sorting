import UnequalSymmetry

/-! Physical capacity for the original machine.

`RunH r s H` is the relational semantics `Run` with every visited stack,
including the transient stack just after a new token is pushed, of length at
most `H`. `runH_iff_fits` shows it is exactly the reviewed executable notion
`Fits`. The main facts here:
- every history generating `p` needs capacity `BoundedAt H p`, meaning the
  `j`-th output `p_j` has `p_j + 1 <= H + j` (`RunH.bounded_range`);
- conversely, any generated `p` is generated within that capacity, via lazy
  normalization (`Run.capacity`);
- when `H <= s+1`, every `p` with `BoundedAt H p` is generated
  (`generate_bounded`). -/
namespace StackSorting.Generalized

inductive RunH {α : Type} (r s H : Nat) : List α → List α → List α → List α → Prop where
  | nil (held : List α) (cap : held.length ≤ H) : RunH r s H held [] [] held
  | cons {held middle final input output inputs outputs : List α}
      (cap : held.length ≤ H) (head : Step r s held input output middle)
      (tail : RunH r s H middle inputs outputs final) :
      RunH r s H held (input ++ inputs) (output ++ outputs) final

variable {α : Type}

theorem RunH.toRun {r s H : Nat} {held input output final : List α}
    (h : RunH r s H held input output final) : Run r s held input output final := by
  induction h with
  | nil held _ => exact Run.nil held
  | cons _ head _ ih => exact Run.cons head ih

theorem RunH.start_cap {r s H : Nat} {held input output final : List α}
    (h : RunH r s H held input output final) : held.length ≤ H := by
  cases h with
  | nil _ cap => exact cap
  | cons cap _ _ => exact cap

theorem RunH.mono {r s H H' : Nat} {held input output final : List α}
    (h : RunH r s H held input output final) (hH : H ≤ H') :
    RunH r s H' held input output final := by
  induction h with
  | nil held cap => exact RunH.nil held (by omega)
  | cons cap head _ ih => exact RunH.cons (by omega) head ih

theorem RunH.append {r s H : Nat} {held middle final ins outs ins' outs' : List α}
    (h : RunH r s H held ins outs middle) (h' : RunH r s H middle ins' outs' final) :
    RunH r s H held (ins ++ ins') (outs ++ outs') final := by
  induction h with
  | nil => simpa using h'
  | cons cap head tail ih => simpa [List.append_assoc] using RunH.cons cap head (ih h')

theorem RunH.map {β : Type} {r s H : Nat} {held input output final : List α}
    (h : RunH r s H held input output final) (f : α → β) :
    RunH r s H (held.map f) (input.map f) (output.map f) (final.map f) := by
  induction h with
  | nil held cap => simpa using RunH.nil (r := r) (s := s) (held.map f) (by simpa using cap)
  | cons cap head tail ih =>
    simpa using RunH.cons (by simpa using cap) (head.map f) ih

theorem RunH.final_cap {r s H : Nat} {held input output final : List α}
    (h : RunH r s H held input output final) : final.length ≤ H := by
  induction h with
  | nil _ cap => exact cap
  | cons _ _ _ ih => exact ih

theorem RunH.reverse {r s H : Nat} {held input output final : List α}
    (h : RunH r s H held input output final) :
    RunH s r H final output.reverse input.reverse held := by
  induction h with
  | nil held cap => simpa using RunH.nil (r := s) (s := r) held cap
  | cons cap head tail ih =>
    have hz := ih.append (RunH.cons (tail.start_cap) head.reverse (RunH.nil _ cap))
    simpa [List.reverse_append] using hz

/-- `RunH` is exactly the reviewed executable capacity predicate `Fits`. -/
theorem runH_iff_fits (r s H : Nat) (held input output final : List Nat) :
    RunH r s H held input output final ↔
      ∃ ops, run r s ops held = some (final, output) ∧ inputs ops = input ∧
        Fits r s H ops held := by
  constructor
  · intro h
    induction h with
    | nil held cap => exact ⟨[], rfl, rfl, cap⟩
    | @cons held middle final inp outp inps outps cap head tail ih =>
      obtain ⟨op, hs, hi⟩ := head.executable
      obtain ⟨ops, hr, his, hf⟩ := ih
      refine ⟨op :: ops, by simp [run, hs, hr], ?_, cap, middle, outp, hs, hf⟩
      simp only [inputs, List.flatMap_cons] at hi his ⊢; rw [hi, his]
  · rintro ⟨ops, hr, rfl, hf⟩
    induction ops generalizing held final output with
    | nil =>
      simp [run] at hr
      rcases hr with ⟨rfl, rfl⟩
      exact RunH.nil held hf
    | cons op ops ih =>
      obtain ⟨middle, emitted, tail, hs, ht, ho⟩ := split_run r s op ops held final output hr
      obtain ⟨cap, ys, out, hs', hf'⟩ := hf
      have hy : ys = middle ∧ out = emitted := by
        rw [hs] at hs'
        simp at hs'
        exact ⟨hs'.1.symm, hs'.2.symm⟩
      rcases hy with ⟨rfl, rfl⟩
      subst ho
      simpa [inputs] using RunH.cons cap (step_relational r s op held ys out hs) (ih ys tail final ht hf')

/-- A history with no output only grows, so it fits in its final length. -/
theorem Run.pushes_capacity {r s H : Nat} {held input final : List Nat}
    (h : Run r s held input [] final) (hf : final.length ≤ H) :
    RunH r s H held input [] final := by
  generalize ho : ([] : List Nat) = output at h
  induction h with
  | nil held => exact RunH.nil held hf
  | @cons held middle final input output inputs outputs head tail ih =>
    have ho' : output = [] ∧ outputs = [] := List.append_eq_nil_iff.mp ho.symm
    obtain ⟨rfl, rfl⟩ := ho'
    have hgrow : held.length ≤ final.length := by
      have h₁ := head.supply.length_eq
      have h₂ := tail.supply.length_eq
      simp at h₁ h₂
      omega
    simpa using RunH.cons (by omega) head (ih hf rfl)

/-! Bounded outputs: `BoundedAt B (x :: xs)` means `x + 1 <= B`, and the
bound increases by one at each later position. `BoundedAt H p` is the exact
capacity condition for generating `p` from increasing input. -/

def BoundedAt : Nat → List Nat → Prop
  | _, [] => True
  | B, x :: xs => x + 1 ≤ B ∧ BoundedAt (B+1) xs

theorem BoundedAt.mono {B B' : Nat} : ∀ {l : List Nat}, BoundedAt B l → B ≤ B' → BoundedAt B' l
  | [], _, _ => trivial
  | _ :: _, ⟨h₁, h₂⟩, hB => ⟨by omega, BoundedAt.mono h₂ (by omega)⟩

theorem boundedAt_append {B : Nat} : ∀ (l₁ l₂ : List Nat),
    BoundedAt B (l₁ ++ l₂) ↔ BoundedAt B l₁ ∧ BoundedAt (B + l₁.length) l₂
  | [], l₂ => by simp [BoundedAt]
  | x :: l₁, l₂ => by
    have ih := boundedAt_append (B := B+1) l₁ l₂
    simp only [List.cons_append, BoundedAt, ih, List.length_cons]
    rw [show B + 1 + l₁.length = B + (l₁.length + 1) by omega]
    constructor
    · rintro ⟨h₁, h₂, h₃⟩; exact ⟨⟨h₁, h₂⟩, h₃⟩
    · rintro ⟨⟨h₁, h₂⟩, h₃⟩; exact ⟨h₁, h₂, h₃⟩

theorem boundedAt_iff_getElem {B : Nat} : ∀ (l : List Nat),
    BoundedAt B l ↔ ∀ i (h : i < l.length), l[i] + 1 ≤ B + i
  | [] => by simp [BoundedAt]
  | x :: xs => by
    have ih := boundedAt_iff_getElem (B := B+1) xs
    simp only [BoundedAt, ih, List.length_cons]
    constructor
    · rintro ⟨h₀, h⟩ i hi
      cases i with
      | zero => simpa using h₀
      | succ i => have := h i (by omega); simp; omega
    · intro h
      refine ⟨by simpa using h 0 (by omega), fun i hi => ?_⟩
      have := h (i+1) (by omega); simp at this; omega

/-- Lazy record segmentation fits in the capacity given by `BoundedAt`. -/
theorem RangeLazyRun.historyH {r s limit next : Nat} {held output : List Nat}
    (h : RangeLazyRun r s limit next held output) :
    ∀ j H, held.length + j = next → held.length ≤ H → BoundedAt (H + j) output →
      RunH r s H held (List.range' next (limit - next)) output [] := by
  induction h with
  | nil => intro j H _ hc _; simpa using RunH.nil (r := r) (s := s) _ hc
  | @held next a held after out pop tail ih =>
    intro j H hj hc hb
    have hl := pop.supply.length_eq
    simp at hl
    have ht := ih (j+1) H (by omega) (by omega) (by simpa [Nat.add_assoc] using hb.2)
    simpa using RunH.cons hc pop ht
  | @record next a held before after out lower upper fresh read pop tail ih =>
    intro j H hj hc hb
    have hl₁ := read.supply.length_eq
    have hl₂ := pop.supply.length_eq
    simp at hl₁ hl₂
    have hbefore : before.length ≤ H := by have := hb.1; omega
    have hr := read.pushes_capacity hbefore
    have ht := ih (j+1) H (by omega) (by omega) (by simpa [Nat.add_assoc] using hb.2)
    have hz := hr.append (RunH.cons hbefore pop ht)
    have he : List.range' next (a+1-next) ++ List.range' (a+1) (limit-(a+1)) =
        List.range' next (limit-next) := by
      have hstart : next + 1 * (a+1-next) = a+1 := by omega
      have hcount : a+1-next + (limit-(a+1)) = limit-next := by omega
      have hz := List.range'_append (s := next) (m := a+1-next)
        (n := limit-(a+1)) (step := 1)
      simpa only [hstart, hcount] using hz
    simpa [he] using hz

/-- Any generated output is generated within the capacity `BoundedAt` allows. -/
theorem Run.capacity {r s n H : Nat} {p : List Nat}
    (h : Run r s [] (List.range n) p []) (hb : BoundedAt H p) :
    RunH r s H [] (List.range n) p [] := by
  have hl := generated_rangeLazy h
  have hz := hl.historyH 0 H rfl (Nat.zero_le _) (by simpa using hb)
  simpa [List.range_eq_range'] using hz

/-- Lower bound: every history from `held` reading `range' k c` has outputs
bounded by its capacity. -/
theorem RunH.bounded_range {r s H : Nat} {held input output final : List Nat}
    (h : RunH r s H held input output final) :
    ∀ k c, input = List.range' k c → (∀ x ∈ held, x < k) →
      BoundedAt (H + k - held.length) output := by
  induction h with
  | nil => intro _ _ _ _; trivial
  | @cons held middle final input output inputs outputs cap head tail ih =>
    intro k c hi hheld
    cases head with
    | push pre post x allowed =>
      rcases c with _ | c
      · simp at hi
      · simp [List.range'_succ] at hi
        obtain ⟨rfl, rfl⟩ := hi
        have hz := ih (x+1) c rfl (by
          intro y hy
          simp only [List.mem_append, List.mem_cons] at hy
          rcases hy with hy | rfl | hy
          · have := hheld y (by simp [hy]); omega
          · omega
          · have := hheld y (by simp [hy]); omega)
        simp only [List.length_append, List.length_cons] at hz ⊢
        rwa [show H + (x+1) - (pre.length + (post.length + 1)) = H + x - (pre.length + post.length)
          by omega] at hz
    | pop pre post x allowed =>
      simp only [List.nil_append] at hi
      have hx : x < k := hheld x (by simp)
      have hz := ih k c hi (fun y hy => hheld y (by
        simp only [List.mem_append] at hy ⊢; simp only [List.mem_cons]
        rcases hy with hy | hy
        · exact Or.inl hy
        · exact Or.inr (Or.inr hy)))
      have hcap : pre.length + (post.length + 1) ≤ H := by
        have := cap; simp only [List.length_append, List.length_cons] at this; omega
      refine ⟨by simp only [List.length_append, List.length_cons]; omega, ?_⟩
      simp only [List.length_append, List.length_cons] at hz ⊢
      rwa [show H + k - (pre.length + post.length) = H + k - (pre.length + (post.length + 1)) + 1
        by omega] at hz

theorem RunH.bounded {r s H n : Nat} {p : List Nat}
    (h : RunH r s H [] (List.range n) p []) : BoundedAt H p := by
  simpa using h.bounded_range 0 n (by simp [List.range_eq_range']) (by simp)

/-- Reading `k,...,k+t-1` into slot zero leaves them on top, newest first. -/
theorem Run.push_top {r s : Nat} (hr : 0 < r) :
    ∀ (t k : Nat) (st : List Nat),
      Run r s st (List.range' k t) [] ((List.range' k t).reverse ++ st) := by
  intro t
  induction t with
  | zero => intro k st; simpa using Run.nil (r := r) (s := s) st
  | succ t ih =>
    intro k st
    have h₁ := ih k st
    have h₂ := Run.single (Step.push (r := r) (s := s) [] ((List.range' k t).reverse ++ st) (k+t)
      (by simpa using hr))
    have hz := h₁.append h₂
    simpa [List.range'_concat] using hz

/-- When `H <= s+1`, the lazy strategy (every push at slot zero) generates every
bounded output within capacity `H`. -/
theorem generate_bounded {r s H : Nat} (hr : 0 < r) (hs : 0 < s) (hH : H ≤ s + 1) :
    ∀ (out st : List Nat) (k c : Nat), out.Perm (st ++ List.range' k c) →
      (∀ x ∈ st, x < k) → (st = [] ∨ st.length + 1 ≤ H) →
      BoundedAt (H + k - st.length) out → RunH r s H st (List.range' k c) out [] := by
  intro out
  induction out with
  | nil =>
    intro st k c hp _ _ _
    have he := hp.symm.eq_nil
    have hst : st = [] := by cases st <;> simp_all
    have hc : c = 0 := by
      subst hst; cases c <;> simp_all [List.range'_succ]
    subst hst; subst hc
    exact RunH.nil [] (Nat.zero_le _)
  | cons x out ih =>
    intro st k c hp hlt hinv hb
    have hxm : x ∈ st ++ List.range' k c := hp.mem_iff.mp (by simp)
    by_cases hxs : x ∈ st
    · obtain ⟨s₁, s₂, rfl⟩ := List.append_of_mem hxs
      have hlen : (s₁ ++ x :: s₂).length + 1 ≤ H := by
        rcases hinv with h | h
        · simp at h
        · exact h
      have hlen' : s₁.length + s₂.length + 2 ≤ H := by
        have := hlen; rw [List.length_append, List.length_cons] at this; omega
      have hidx : s₁.length < s := by
        have := hlen; rw [List.length_append, List.length_cons] at this; omega
      have hp' : out.Perm ((s₁ ++ s₂) ++ List.range' k c) := by
        have h₁ : (x :: out).Perm (x :: ((s₁ ++ s₂) ++ List.range' k c)) := by
          refine hp.trans ?_
          have hm := List.perm_middle (a := x) (l₁ := s₁) (l₂ := s₂ ++ List.range' k c)
          simp only [List.append_assoc, List.cons_append] at hm ⊢
          exact hm
        exact h₁.cons_inv
      have ht := ih (s₁ ++ s₂) k c hp'
        (fun y hy => hlt y (by
          simp only [List.mem_append, List.mem_cons] at hy ⊢
          rcases hy with hy | hy
          · exact Or.inl hy
          · exact Or.inr (Or.inr hy)))
        (Or.inr (by
          have := hlen; rw [List.length_append, List.length_cons] at this
          rw [List.length_append]; omega))
        (by
          have := hb.2
          simp only [List.length_append, List.length_cons] at this ⊢
          rw [show H + k - (s₁.length + s₂.length) = H + k - (s₁.length + (s₂.length + 1)) + 1 by
            omega]
          exact this)
      have hz := RunH.cons (by omega) (Step.pop (r := r) (s := s) s₁ s₂ x hidx) ht
      simpa using hz
    · have hxr : x ∈ List.range' k c := by
        simp only [List.mem_append] at hxm
        rcases hxm with h | h
        · exact absurd h hxs
        · exact h
      rw [List.mem_range'] at hxr
      obtain ⟨t, ht, hxt⟩ := hxr
      simp only [Nat.one_mul] at hxt
      subst hxt
      -- read k..k+t-1 into slot zero, then pass k+t through slot zero
      have hsplit : List.range' k c = List.range' k t ++ (k+t) :: List.range' (k+t+1) (c-t-1) := by
        have h₁ := List.range'_append (s := k) (m := t) (n := c-t) (step := 1)
        rw [show t + (c-t) = c by omega] at h₁
        rw [← h₁, show c - t = (c-t-1) + 1 by omega, List.range'_succ]
        simp [Nat.add_assoc]
      have hread := Run.push_top (s := s) hr t k st
      have hbefore : ((List.range' k t).reverse ++ st).length + 1 ≤ H := by
        have := hb.1; simp; omega
      have hbefore' : t + st.length + 1 ≤ H := by simpa using hbefore
      have hreadH := hread.pushes_capacity (H := H) (by omega)
      have hpush := Step.push (r := r) (s := s) [] ((List.range' k t).reverse ++ st) (k+t)
        (by simpa using hr)
      have hpop := Step.pop (r := r) (s := s) [] ((List.range' k t).reverse ++ st) (k+t)
        (by simpa using hs)
      have hp' : out.Perm (((List.range' k t).reverse ++ st) ++ List.range' (k+t+1) (c-t-1)) := by
        have h₁ : ((k+t) :: out).Perm ((k+t) :: (((List.range' k t).reverse ++ st) ++
            List.range' (k+t+1) (c-t-1))) := by
          refine hp.trans ?_
          rw [hsplit]
          have h₂ : (st ++ (List.range' k t ++ (k+t) :: List.range' (k+t+1) (c-t-1))).Perm
              ((k+t) :: (st ++ (List.range' k t ++ List.range' (k+t+1) (c-t-1)))) := by
            have := List.perm_middle (a := k+t) (l₁ := st ++ List.range' k t)
              (l₂ := List.range' (k+t+1) (c-t-1))
            simpa [List.append_assoc] using this
          refine h₂.trans (List.Perm.cons _ ?_)
          have h₃ : (st ++ List.range' k t).Perm ((List.range' k t).reverse ++ st) :=
            List.perm_append_comm.trans (List.Perm.append_right _ (List.reverse_perm _).symm)
          simpa [List.append_assoc] using h₃.append_right (List.range' (k+t+1) (c-t-1))
        exact h₁.cons_inv
      have htail := ih ((List.range' k t).reverse ++ st) (k+t+1) (c-t-1) hp'
        (by
          intro y hy
          simp only [List.mem_append, List.mem_reverse, List.mem_range'] at hy
          rcases hy with ⟨i, hi, rfl⟩ | hy
          · omega
          · have := hlt y hy; omega)
        (Or.inr hbefore)
        (by
          have := hb.2
          simp only [List.length_append, List.length_reverse, List.length_range'] at this ⊢
          rw [show H + (k+t+1) - (t + st.length) = H + k - st.length + 1 by omega]
          exact this)
      have hrec := RunH.cons (by simp only [List.nil_append]; omega)
        hpush (RunH.cons (by simp only [List.nil_append, List.length_cons]; omega) hpop htail)
      have hz := hreadH.append hrec
      rw [hsplit]
      simpa [List.append_assoc] using hz

#print axioms runH_iff_fits
#print axioms Run.capacity
#print axioms RunH.bounded
#print axioms generate_bounded
end StackSorting.Generalized
