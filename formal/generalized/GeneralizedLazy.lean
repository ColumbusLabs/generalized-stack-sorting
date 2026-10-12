import GeneralizedRelational

/-! First-output lazy normalization for the actual arbitrary-width machine. -/
namespace StackSorting.Generalized

theorem Run.firstOutput {r s : Nat} {held input output final : List Nat}
    (h : Run r s held input output final) (a : Nat) (out : List Nat)
    (ho : output = a :: out) :
    ∃ before after pre rest, Run r s held pre [] before ∧
      Step r s before [] [a] after ∧ Run r s after rest out final ∧ input = pre ++ rest := by
  induction h with
  | nil => simp at ho
  | @cons held middle final input output inputs outputs head tail ih =>
    cases head with
    | push pre post x allowed =>
      obtain ⟨before, after, ins, rest, hp, hs, hr, hi⟩ := ih (by simpa using ho)
      exact ⟨before, after, x :: ins, rest,
        by simpa using Run.cons (Step.push pre post x allowed) hp,
        hs, hr, by simp [hi]⟩
    | pop pre post x allowed =>
      simp at ho
      rcases ho with ⟨rfl, rfl⟩
      exact ⟨pre ++ x :: post, pre ++ post, [], inputs,
        Run.nil _, Step.pop pre post x allowed, tail, rfl⟩

theorem push_pop_swap {r s x y : Nat} {held middle after : List Nat}
    (hi : Step r s held [x] [] middle) (hp : Step r s middle [] [y] after)
    (hne : y ≠ x) :
    ∃ first, Step r s held [] [y] first ∧ Step r s first [x] [] after := by
  obtain ⟨op, hs, hin⟩ := hp.executable
  cases op with
  | push k a => simp [introduced] at hin
  | pop j =>
    have hj : j < s := by
      by_cases hjs : j < s
      · exact hjs
      · simp [step, hjs] at hs
    cases hm : removeAt? j middle with
    | none => simp [step, hj, hm] at hs
    | some p =>
      rcases p with ⟨zs, z⟩
      simp [step, hj, hm] at hs
      rcases hs with ⟨rfl, rfl⟩
      cases hi with
      | push pre post x hir =>
        obtain ⟨first, i', j', _, _, hs₁, hs₂, _, _⟩ :=
          legal_push_pop_commute r s pre.length j x z (pre ++ post)
            (pre ++ x :: post) zs hir hj (insertAt_prefix pre post x) hm hne
        exact ⟨first, step_relational r s (.pop j') _ _ _ hs₁,
          step_relational r s (.push i' x) _ _ _ hs₂⟩

/-- Pull the first requested pop through any push-only prefix that does not
introduce that value. No assumption of an increasing output is involved. -/
theorem Run.pullPop {r s : Nat} {held input output middle : List Nat}
    (h : Run r s held input output middle) (empty : output = [])
    {a : Nat} {after : List Nat} (hp : Step r s middle [] [a] after)
    (fresh : a ∉ input) :
    ∃ first, Step r s held [] [a] first ∧ Run r s first input [] after := by
  induction h with
  | nil => exact ⟨after, hp, Run.nil _⟩
  | @cons held next middle ins outs input output head tail ih =>
    cases head with
    | push pre post x allowed =>
      have ht : output = [] := by simpa using empty
      have ha : a ≠ x ∧ a ∉ input := by simpa using fresh
      obtain ⟨first, hs, hr⟩ := ih ht hp ha.2
      obtain ⟨start, hp', hi'⟩ := push_pop_swap (Step.push pre post x allowed) hs ha.1
      exact ⟨start, hp', by simpa using Run.cons hi' hr⟩
    | pop pre post x allowed => simp at empty

theorem Step.supply {r s : Nat} {held input output after : List Nat}
    (h : Step r s held input output after) : (held ++ input).Perm (output ++ after) := by
  cases h with
  | push pre post x allowed =>
    simpa [List.append_assoc] using
      List.Perm.append_left pre (List.perm_append_comm (l₁ := post) (l₂ := [x]))
  | pop pre post x allowed => simpa only [List.append_nil, List.singleton_append] using (List.perm_middle (a := x) (l₁ := pre) (l₂ := post))

theorem Run.supply {r s : Nat} {held input output after : List Nat}
    (h : Run r s held input output after) : (held ++ input).Perm (output ++ after) := by
  induction h with
  | nil => simp
  | @cons held middle final input output inputs outputs head tail ih =>
    have h₁ := head.supply.append_right inputs
    have h₂ := List.Perm.append_left output ih
    exact (by simpa [List.append_assoc] using h₁.trans (by simpa [List.append_assoc] using h₂))

theorem Run.noOutputSplit {r s : Nat} {held input output after : List Nat}
    (h : Run r s held input output after) (empty : output = [])
    (pre rest : List Nat) (hi : input = pre ++ rest) :
    ∃ middle, Run r s held pre [] middle ∧ Run r s middle rest [] after := by
  induction h generalizing pre rest with
  | nil held =>
    have he : pre = [] ∧ rest = [] := by simpa using hi.symm
    rcases he with ⟨rfl, rfl⟩
    exact ⟨held, Run.nil _, Run.nil _⟩
  | @cons held next after ins outs input output head tail ih =>
    cases head with
    | push xs ys a allowed =>
      have ht : output = [] := by simpa using empty
      cases pre with
      | nil =>
        simp at hi
        subst rest
        exact ⟨xs ++ ys, Run.nil _, by simpa [ht] using Run.cons (Step.push xs ys a allowed) tail⟩
      | cons b pre =>
        simp at hi
        rcases hi with ⟨rfl, hi⟩
        obtain ⟨middle, hp, hr⟩ := ih ht pre rest hi
        exact ⟨middle, by simpa using Run.cons (Step.push xs ys a allowed) hp, hr⟩
    | pop xs ys a allowed => simp at empty

theorem Run.remaining_nodup {r s : Nat} {held pre output after : List Nat}
    (h : Run r s held pre output after) (rest : List Nat)
    (hd : (held ++ (pre ++ rest)).Nodup) : (after ++ rest).Nodup := by
  have hp := h.supply.append_right rest
  have hn := hp.nodup_iff.mp (by simpa [List.append_assoc] using hd)
  have hn' : (output ++ (after ++ rest)).Nodup := by simpa [List.append_assoc] using hn
  exact (List.nodup_append.mp hn').2.1

/-- A complete history segmented immediately after each output. A held output
is popped before any read. Otherwise exactly the input prefix through that
output is read, and its last token is popped immediately. -/
inductive LazyRun (r s : Nat) : List Nat → List Nat → List Nat → Prop where
  | nil : LazyRun r s [] [] []
  | held {held after input out : List Nat} {a : Nat}
      (pop : Step r s held [] [a] after)
      (tail : LazyRun r s after input out) : LazyRun r s held input (a :: out)
  | record {held before after pre rest out : List Nat} {a : Nat}
      (fresh : a ∉ held) (first : a ∉ pre)
      (read : Run r s held (pre ++ [a]) [] before)
      (pop : Step r s before [] [a] after)
      (tail : LazyRun r s after rest out) :
      LazyRun r s held (pre ++ a :: rest) (a :: out)

theorem LazyRun.history {r s : Nat} {held input output : List Nat}
    (h : LazyRun r s held input output) : Run r s held input output [] := by
  induction h with
  | nil => exact Run.nil _
  | held pop tail ih => simpa using Run.cons pop ih
  | record fresh first read pop tail ih =>
    simpa [List.append_assoc] using read.append (Run.cons pop ih)

/-- Full lazy-normalization completeness for arbitrary widths and distinct
source tokens. This theorem starts from an unrestricted original history. -/
theorem Run.lazy {r s : Nat} (output : List Nat) {held input : List Nat}
    (h : Run r s held input output []) (hd : (held ++ input).Nodup) :
    LazyRun r s held input output := by
  induction output generalizing held input with
  | nil =>
    have hp := h.supply
    have hz : held = [] ∧ input = [] := by simpa using hp
    rcases hz with ⟨rfl, rfl⟩
    exact LazyRun.nil
  | cons a out ih =>
    obtain ⟨before, after, read, rest, hread, hpop, htail, hi⟩ := h.firstOutput a out rfl
    by_cases ha : a ∈ held
    · have hnot : a ∉ read := by
        intro har
        exact (List.nodup_append.mp hd).2.2 a ha a (by simp [hi, har]) rfl
      obtain ⟨first, hp, hr⟩ := hread.pullPop rfl hpop hnot
      have hn : Run r s first input out [] := by simpa [hi] using hr.append htail
      have hd' := (Run.single hp).remaining_nodup input (by simpa using hd)
      exact LazyRun.held hp (ih hn hd')
    · have ham : a ∈ before := by
        have hm := hpop.supply.mem_iff.mpr (by simp : a ∈ [a] ++ after)
        simpa using hm
      have har : a ∈ read := by
        have hm := hread.supply.mem_iff.mpr (by simpa using ham)
        simpa [ha] using hm
      obtain ⟨pre, delayed, hrd⟩ := List.mem_iff_append.mp har
      have hreadnodup : read.Nodup :=
        (List.nodup_append.mp (by simpa [hi] using (List.nodup_append.mp hd).2.1)).1
      have hnod : pre.Nodup ∧ (a :: delayed).Nodup ∧
          ∀ x, x ∈ pre → ∀ y, y ∈ a :: delayed → x ≠ y := by
        simpa [hrd] using (List.nodup_append.mp (show (pre ++ a :: delayed).Nodup by simpa [hrd] using hreadnodup))
      have hpre : a ∉ pre := by
        intro hm
        exact hnod.2.2 a hm a (by simp) rfl
      have hdelay : a ∉ delayed := (List.nodup_cons.mp hnod.2.1).1
      obtain ⟨middle, hr₁, hr₂⟩ :=
        hread.noOutputSplit rfl (pre ++ [a]) delayed (by simpa [List.append_assoc] using hrd)
      obtain ⟨first, hp, hr⟩ := hr₂.pullPop rfl hpop hdelay
      have hn : Run r s first (delayed ++ rest) out [] := by simpa using hr.append htail
      have hsegment : Run r s held (pre ++ [a]) [a] first := by
        simpa using hr₁.append (Run.single hp)
      have hd' := hsegment.remaining_nodup (delayed ++ rest)
        (by simpa [hi, hrd, List.append_assoc] using hd)
      have hz := LazyRun.record ha hpre hr₁ hp (ih hn hd')
      simpa [hi, hrd, List.append_assoc] using hz

theorem lazyRun_iff {r s : Nat} (held input output : List Nat)
    (hd : (held ++ input).Nodup) :
    LazyRun r s held input output ↔ Run r s held input output [] :=
  ⟨LazyRun.history, fun h => h.lazy output hd⟩

#print axioms Run.lazy
#print axioms lazyRun_iff

#print axioms Run.firstOutput
#print axioms Run.pullPop
end StackSorting.Generalized
