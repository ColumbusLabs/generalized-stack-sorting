import ContainerPatterns
import GeneralizedRelational

/-! Arbitrary legal container insertion, selectable top-`s` removal, and
optional direct bypass. There is no imposed insertion-width restriction in
`CStep`: the theorem derives it from literal pattern-avoidance membership. -/
set_option linter.unusedSimpArgs false
namespace StackSorting.Generalized.Container

/-- The original container operations. Only the resulting class membership
restricts a push; `pre` may have any length. -/
inductive CStep (r s : Nat) (bypass : Bool) :
    List Nat → List Nat → List Nat → List Nat → Prop where
  | push (pre post : List Nat) (x : Nat) (legal : Member r (pre ++ x :: post)) :
      CStep r s bypass (pre ++ post) [x] [] (pre ++ x :: post)
  | pop (pre post : List Nat) (x : Nat) (allowed : pre.length < s) :
      CStep r s bypass (pre ++ x :: post) [] [x] (pre ++ post)
  | bypass (held : List Nat) (x : Nat) (allowed : bypass = true) :
      CStep r s bypass held [x] [x] held

inductive CRun (r s : Nat) (bypass : Bool) :
    List Nat → List Nat → List Nat → List Nat → Prop where
  | nil (held : List Nat) : CRun r s bypass held [] [] held
  | cons {held middle final input output inputs outputs : List Nat}
      (head : CStep r s bypass held input output middle)
      (tail : CRun r s bypass middle inputs outputs final) :
      CRun r s bypass held (input ++ inputs) (output ++ outputs) final

/-- Every held token is older (smaller) than every unread token. -/
def Before (held input : List Nat) : Prop :=
  ∀ x ∈ held, ∀ y ∈ input, x < y

theorem smallerBefore_insert_old (x a : Nat) (pre post : List Nat) (h : x < a) :
    smallerBefore x (pre ++ a :: post) = smallerBefore x (pre ++ post) := by
  induction pre with
  | nil => simp [smallerBefore, show x ≠ a by omega, show ¬ a < x by omega]
  | cons y pre ih => simp [smallerBefore, ih]

theorem smallerBefore_insert_new (a : Nat) (pre post : List Nat)
    (h : ∀ y ∈ pre, y < a) :
    smallerBefore a (pre ++ a :: post) = pre.length := by
  rw [smallerBefore_at a pre post (by intro hm; have := h a hm; omega)]
  rw [List.filter_eq_self.mpr (by simpa using h)]

theorem nodup_insert {pre post : List Nat} {a : Nat}
    (hn : (pre ++ post).Nodup) (h : ∀ y ∈ pre ++ post, y < a) :
    (pre ++ a :: post).Nodup := by
  have ha : a ∉ pre ++ post := by intro hm; have := h a hm; omega
  have hd : (a :: (pre ++ post)).Nodup := List.nodup_cons.mpr ⟨ha, hn⟩
  exact (List.perm_middle (a := a) (l₁ := pre) (l₂ := post)).nodup_iff.mpr hd

/-- Every legal original push preserves the genuine avoidance class. -/
theorem member_insert {r : Nat} {pre post : List Nat} {a : Nat}
    (hm : Member r (pre ++ post)) (h : ∀ y ∈ pre ++ post, y < a)
    (hk : pre.length < r) : Member r (pre ++ a :: post) := by
  have hn := nodup_insert hm.1 h
  refine ⟨hn, (avoids_iff_countGood hn).mpr ?_⟩
  intro x hx
  rcases List.mem_append.mp hx with hx | hx
  · have hold : x ∈ pre ++ post := List.mem_append_left post hx
    rw [smallerBefore_insert_old x a pre post (h x hold)]
    exact (avoids_iff_countGood hm.1).mp hm.2 x hold
  · rcases List.mem_cons.mp hx with he | hx
    · subst x
      simpa [smallerBefore_insert_new a pre post (fun y hy => h y (by simp [hy]))] using hk
    · have hold : x ∈ pre ++ post := List.mem_append_right pre hx
      rw [smallerBefore_insert_old x a pre post (h x hold)]
      exact (avoids_iff_countGood hm.1).mp hm.2 x hold

/-- Conversely, a legal insertion of a new maximum must be at depth `< r`. -/
theorem legal_insert_depth {r : Nat} {pre post : List Nat} {a : Nat}
    (hm : Member r (pre ++ a :: post)) (h : ∀ y ∈ pre ++ post, y < a) :
    pre.length < r := by
  have hc := (avoids_iff_countGood hm.1).mp hm.2 a (by simp)
  simpa [smallerBefore_insert_new a pre post (fun y hy => h y (by simp [hy]))] using hc

/-- Avoidance is hereditary under ordinary subsequence containment. -/
theorem member_sublist {r : Nat} {xs ys : List Nat} (hm : Member r xs)
    (hs : ys.Sublist xs) : Member r ys := by
  refine ⟨hm.1.sublist hs, ?_⟩
  intro p hp ho
  obtain ⟨f, hf, hsub⟩ := ho
  exact hm.2 p hp ⟨f, hf, hsub.trans hs⟩

theorem member_pop {r : Nat} {pre post : List Nat} {a : Nat}
    (hm : Member r (pre ++ a :: post)) : Member r (pre ++ post) :=
  member_sublist hm ((List.Sublist.refl pre).append (List.sublist_cons_self a post))

theorem member_nil (r : Nat) : Member r [] := by
  refine ⟨by simp, (avoids_iff_countGood (by simp)).mpr ?_⟩
  simp [CountGood]

theorem before_push {pre post inputs : List Nat} {x : Nat}
    (hb : Before (pre ++ post) (x :: inputs)) (hi : (x :: inputs).Pairwise (· < ·)) :
    Before (pre ++ x :: post) inputs := by
  intro a ha b hbi
  rcases List.mem_append.mp ha with ha | ha
  · exact hb a (by simp [ha]) b (by simp [hbi])
  · rcases List.mem_cons.mp ha with ha | ha
    · subst a; exact (List.pairwise_cons.mp hi).1 b hbi
    · exact hb a (by simp [ha]) b (by simp [hbi])

theorem before_pop {pre post input : List Nat} {x : Nat}
    (hb : Before (pre ++ x :: post) input) : Before (pre ++ post) input := by
  intro a ha b hb'
  apply hb a _ b hb'
  rcases List.mem_append.mp ha with ha | ha
  · simp [ha]
  · simp [ha]

theorem before_tail {held input : List Nat} {x : Nat}
    (hb : Before held (x :: input)) : Before held input := by
  intro a ha b hb'
  exact hb a ha b (by simp [hb'])

/-- Every original history with increasing input preserves class membership
at every step, and is itself a legal container history without bypass. No
normalization, laziness, or bound on the output is assumed. -/
theorem original_to_container {r s : Nat} {held input output final : List Nat}
    (h : Run r s held input output final) (hm : Member r held)
    (hi : input.Pairwise (· < ·)) (hb : Before held input) :
    CRun r s false held input output final ∧ Member r final := by
  induction h with
  | nil held => exact ⟨CRun.nil held, hm⟩
  | @cons held middle final input output inputs outputs head tail ih =>
    cases head with
    | push pre post x allowed =>
      have hi' : (x :: inputs).Pairwise (· < ·) := by simpa using hi
      have hb' : Before (pre ++ post) (x :: inputs) := by simpa using hb
      have hm' := member_insert hm (fun y hy => hb' y hy x (by simp)) allowed
      obtain ⟨ht, hf⟩ := ih hm' (List.pairwise_cons.mp hi').2 (before_push hb' hi')
      exact ⟨CRun.cons (CStep.push pre post x hm') ht, hf⟩
    | pop pre post x allowed =>
      have hi' : inputs.Pairwise (· < ·) := by simpa using hi
      have hb' : Before (pre ++ x :: post) inputs := by simpa using hb
      obtain ⟨ht, hf⟩ := ih (member_pop hm) hi' (before_pop hb')
      exact ⟨CRun.cons (CStep.pop pre post x allowed) ht, hf⟩

/-- A bypass is exactly a push into slot zero followed by a pop from slot
zero in the original machine. Both intermediate physical states are real. -/
theorem simulate_bypass {r s : Nat} (hr : 0 < r) (hs : 0 < s)
    (held : List Nat) (x : Nat) : Run r s held [x] [x] held := by
  have hp := Step.push (r := r) (s := s) [] held x (by simpa using hr)
  have hq := Step.pop (r := r) (s := s) [] held x (by simpa using hs)
  simpa using (Run.single hp).append (Run.single hq)

/-- Simulation of every legal container history, including arbitrary legal
push positions and optional bypass, by the literal original machine. -/
theorem container_to_original {r s : Nat} {bypass : Bool}
    {held input output final : List Nat} (h : CRun r s bypass held input output final)
    (hr : 0 < r) (hs : 0 < s) (hi : input.Pairwise (· < ·))
    (hb : Before held input) : Run r s held input output final := by
  induction h with
  | nil held => exact Run.nil held
  | @cons held middle final input output inputs outputs head tail ih =>
    cases head with
    | push pre post x legal =>
      have hi' : (x :: inputs).Pairwise (· < ·) := by simpa using hi
      have hb' : Before (pre ++ post) (x :: inputs) := by simpa using hb
      have hk := legal_insert_depth legal (fun y hy => hb' y hy x (by simp))
      exact Run.cons (Step.push pre post x hk)
        (ih (List.pairwise_cons.mp hi').2 (before_push hb' hi'))
    | pop pre post x allowed =>
      have hi' : inputs.Pairwise (· < ·) := by simpa using hi
      have hb' : Before (pre ++ x :: post) inputs := by simpa using hb
      exact Run.cons (Step.pop pre post x allowed) (ih hi' (before_pop hb'))
    | bypass held x allowed =>
      have hi' : (x :: inputs).Pairwise (· < ·) := by simpa using hi
      have hb' : Before held (x :: inputs) := by simpa using hb
      exact (simulate_bypass hr hs held x).append
        (ih (List.pairwise_cons.mp hi').2 (before_tail hb'))

theorem CRun.allow_bypass {r s : Nat} {held input output final : List Nat}
    (h : CRun r s false held input output final) : CRun r s true held input output final := by
  induction h with
  | nil held => exact CRun.nil held
  | cons head tail ih =>
    cases head with
    | push pre post x legal => exact CRun.cons (CStep.push pre post x legal) ih
    | pop pre post x allowed => exact CRun.cons (CStep.pop pre post x allowed) ih
    | bypass held x allowed => cases allowed

/-- Proposition 5.1, simultaneously with and without bypass, on arbitrary
strictly increasing input (including deleted, unstandardized inputs). -/
theorem generates_iff {r s : Nat} (hr : 0 < r) (hs : 0 < s)
    (bypass : Bool) (input output : List Nat) (hi : input.Pairwise (· < ·)) :
    CRun r s bypass [] input output [] ↔ Run r s [] input output [] := by
  constructor
  · intro h; exact container_to_original h hr hs hi (by simp [Before])
  · intro h
    have hc := (original_to_container h (member_nil r) hi (by simp [Before])).1
    cases bypass with
    | false => exact hc
    | true => exact hc.allow_bypass

/-- Exact equivalence to the executable slot-indexed machine, not just to an
abstract or lazy replacement semantics. -/
theorem generates_executable_iff {r s : Nat} (hr : 0 < r) (hs : 0 < s)
    (bypass : Bool) (n : Nat) (output : List Nat) :
    CRun r s bypass [] (List.range n) output [] ↔
      ∃ ops, run r s ops [] = some ([], output) ∧ inputs ops = List.range n := by
  rw [generates_iff hr hs bypass _ _ List.pairwise_lt_range, run_relational_iff]

#print axioms member_insert
#print axioms legal_insert_depth
#print axioms original_to_container
#print axioms simulate_bypass
#print axioms container_to_original
#print axioms generates_iff
#print axioms generates_executable_iff
end StackSorting.Generalized.Container
