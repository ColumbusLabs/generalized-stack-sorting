import UnequalFamily
import RangeLazyInversion

/-! Physical bottom-token invariants for the arbitrary-width original machine.

A token `z` at the bottom of a stack with at least `r-1` tokens above it can
never have a new token inserted below it, keeps its position under pops of
other tokens, and can itself be popped only when fewer than `s` tokens lie
above it. These are statements about literal stacks, not abstract states. -/
namespace StackSorting.Generalized

theorem Step.pop_mem' {r s : Nat} {held after : List Nat} {x : Nat}
    (h : Step r s held [] [x] after) : x ∈ held := by
  have hm : x ∈ [x] ++ after := by simp
  simpa using h.supply.mem_iff.mpr hm

theorem Step.mem_after {r s : Nat} {held input output after : List Nat}
    (h : Step r s held input output after) {x : Nat} (hx : x ∈ after) :
    x ∈ held ∨ x ∈ input := by
  have hm := h.supply.mem_iff.mpr (List.mem_append_right output hx)
  simpa [List.mem_append] using hm

theorem Run.mem_after {r s : Nat} {held input output after : List Nat}
    (h : Run r s held input output after) {x : Nat} (hx : x ∈ after) :
    x ∈ held ∨ x ∈ input := by
  have hm := h.supply.mem_iff.mpr (List.mem_append_right output hx)
  simpa [List.mem_append] using hm

theorem Step.silent_input {r s : Nat} {held input after : List Nat}
    (h : Step r s held input [] after) : ∃ x, input = [x] := by
  cases h with
  | push pre post x allowed => exact ⟨x, rfl⟩

namespace Unequal

theorem split_above_bottom {pre post ys : List Nat} {z : Nat}
    (h : pre ++ post = ys ++ [z]) (hl : pre.length ≤ ys.length) :
    ∃ t, ys = pre ++ t ∧ post = t ++ [z] := by
  rcases List.append_eq_append_iff.mp h with ⟨as, hys, hpost⟩ | ⟨bs, hpre, hz⟩
  · exact ⟨as, hys, hpost⟩
  · have hlen := congrArg List.length hpre
    simp only [List.length_append] at hlen
    have hb : bs = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst hb
    simp only [List.append_nil, List.nil_append] at hpre hz
    exact ⟨[], by simp [hpre], by simp [hz]⟩

/-- A push cannot pass below a bottom token that has at least `r-1` tokens
above it. -/
theorem push_above_bottom {r s : Nat} {ys after : List Nat} {x z : Nat}
    (h : Step r s (ys ++ [z]) [x] [] after) (hr : r ≤ ys.length + 1)
    (hx : x ≠ z) (hz : z ∉ ys) :
    ∃ ys', after = ys' ++ [z] ∧ ys'.length = ys.length + 1 ∧ z ∉ ys' := by
  generalize hh : ys ++ [z] = held at h
  generalize hi : [x] = input at h
  cases h with
  | push pre post y allowed =>
    have hy : x = y := by simpa using hi
    subst hy
    obtain ⟨t, hys, hpost⟩ := split_above_bottom hh.symm (by omega)
    refine ⟨pre ++ x :: t, by simp [hpost], by simp [hys]; omega, ?_⟩
    intro hm
    simp only [List.mem_append, List.mem_cons] at hm
    rcases hm with hm | hm | hm
    · exact hz (by simp [hys, hm])
    · exact hx hm.symm
    · exact hz (by simp [hys, hm])

/-- Removing a token other than the bottom token keeps the bottom token. -/
theorem pop_above_bottom {r s : Nat} {ys after : List Nat} {a z : Nat}
    (h : Step r s (ys ++ [z]) [] [a] after) (ha : a ≠ z) (hz : z ∉ ys) :
    ∃ ys', after = ys' ++ [z] ∧ ys'.length + 1 = ys.length ∧ z ∉ ys' := by
  generalize hh : ys ++ [z] = held at h
  generalize ho : [a] = output at h
  cases h with
  | pop pre post y allowed =>
    have hy : a = y := by simpa using ho
    subst hy
    rcases List.eq_nil_or_concat post with hp | ⟨l, b, hp⟩
    · subst hp
      have hz' := (List.append_inj' hh (by simp)).2
      simp at hz'
      exact absurd hz'.symm ha
    · rw [List.concat_eq_append] at hp
      subst hp
      have he : ys ++ [z] = (pre ++ a :: l) ++ [b] := by simpa using hh
      obtain ⟨hys, hzb⟩ := List.append_inj' he (by simp)
      simp at hzb
      subst hzb
      refine ⟨pre ++ l, by simp, by simp [hys]; omega, ?_⟩
      intro hm
      apply hz
      simp only [List.mem_append] at hm
      rcases hm with hm | hm <;> simp [hys, hm]

/-- The bottom token can be popped only from a slot below the pop width. -/
theorem pop_bottom_depth {r s : Nat} {ys after : List Nat} {z : Nat}
    (h : Step r s (ys ++ [z]) [] [z] after) (hz : z ∉ ys) : ys.length < s := by
  generalize hh : ys ++ [z] = held at h
  generalize ho : [z] = output at h
  cases h with
  | pop pre post y allowed =>
    have hy : z = y := by simpa using ho
    subst hy
    rcases List.eq_nil_or_concat post with hp | ⟨l, b, hp⟩
    · subst hp
      have hys := (List.append_inj' hh (by simp)).1
      rw [hys]
      exact allowed
    · rw [List.concat_eq_append] at hp
      subst hp
      have he : ys ++ [z] = (pre ++ z :: l) ++ [b] := by simpa using hh
      have hys := (List.append_inj' he (by simp)).1
      exact absurd (by simp [hys]) hz

/-- A history that reads without output keeps a sufficiently deep bottom token
and grows exactly by the number of tokens read. -/
theorem read_above_bottom {r s : Nat} {held input output after : List Nat}
    (h : Run r s held input output after) :
    output = [] → ∀ ys z, held = ys ++ [z] → r ≤ ys.length + 1 → z ∉ ys →
      z ∉ input →
      ∃ ys', after = ys' ++ [z] ∧ ys'.length = ys.length + input.length ∧ z ∉ ys' := by
  induction h with
  | nil held =>
    intro _ ys z hh _ hz _
    exact ⟨ys, hh, by simp, hz⟩
  | @cons held middle final input output inputs outputs head tail ih =>
    intro ho ys z hh hr hz hzi
    have ho' : output = [] ∧ outputs = [] := by simpa using ho
    obtain ⟨rfl, rfl⟩ := ho'
    subst hh
    obtain ⟨x, rfl⟩ := head.silent_input
    have hx : x ≠ z := by
      intro he
      exact hzi (by simp [he])
    obtain ⟨ys₁, hm, hl₁, hz₁⟩ := push_above_bottom head hr hx hz
    have hzi' : z ∉ inputs := by
      intro hm'
      exact hzi (by simp [hm'])
    obtain ⟨ys₂, hf, hl₂, hz₂⟩ := ih rfl ys₁ z hm (by omega) hz₁ hzi'
    refine ⟨ys₂, hf, ?_, hz₂⟩
    simp only [List.length_append, List.length_cons, List.length_nil] at hl₂ ⊢
    omega

/-- The first `r` tokens read into an empty stack determine its bottom token,
which therefore has label below `r`. -/
theorem initial_read {r s k : Nat} {before : List Nat} (hr : 1 ≤ r) (hk : r ≤ k)
    (h : Run r s [] (List.range' 0 k) [] before) :
    ∃ ys z, before = ys ++ [z] ∧ ys.length + 1 = k ∧ z ∉ ys ∧ z < r ∧
      ∀ x ∈ before, x < k := by
  have hsplit : List.range' 0 k = List.range' 0 r ++ List.range' r (k-r) := by
    have hz := List.range'_append (s := 0) (m := r) (n := k-r) (step := 1)
    have hk' : r + (k-r) = k := by omega
    simp only [Nat.one_mul, Nat.zero_add, hk'] at hz
    exact hz.symm
  obtain ⟨mid, h₁, h₂⟩ := h.noOutputSplit rfl _ _ hsplit
  have hp : (List.range' 0 r).Perm mid := by simpa using h₁.supply
  have hlen : mid.length = r := by simpa using hp.length_eq.symm
  have hnd : mid.Nodup := hp.nodup_iff.mp (List.nodup_range' (s := 0) (n := r))
  rcases List.eq_nil_or_concat mid with hm | ⟨ys, z, hm⟩
  · subst hm; simp at hlen; omega
  rw [List.concat_eq_append] at hm
  subst hm
  have hzr : z < r := by
    have hz : z ∈ List.range' 0 r := hp.mem_iff.mpr (by simp)
    rw [List.mem_range'] at hz
    omega
  have hzys : z ∉ ys := by
    intro hz
    have hd := List.nodup_append.mp hnd
    exact hd.2.2 z hz z (by simp) rfl
  have hzi : z ∉ List.range' r (k-r) := by
    intro hz
    rw [List.mem_range'] at hz
    omega
  have hl : ys.length + 1 = r := by simpa using hlen
  obtain ⟨ys', hb, hl', hz'⟩ := read_above_bottom h₂ rfl ys z rfl (by omega) hzys hzi
  refine ⟨ys', z, hb, ?_, hz', hzr, ?_⟩
  · simp only [List.length_range'] at hl'
    omega
  · intro x hx
    rcases h.mem_after hx with hx | hx
    · simp at hx
    · rw [List.mem_range'] at hx
      omega

/-- `st` has bottom token `z` with exactly `d` tokens above it, and every held
token is below the next unread input value. -/
def Shape (z d next : Nat) (st : List Nat) : Prop :=
  ∃ ys, st = ys ++ [z] ∧ ys.length = d ∧ z ∉ ys ∧ ∀ x ∈ st, x < next

theorem Shape.bottom_lt {z d next : Nat} {st : List Nat} (hs : Shape z d next st) :
    z < next := by
  obtain ⟨ys, rfl, _, _, hb⟩ := hs
  exact hb z (by simp)

/-- A new-maximum output reads its whole batch above the bottom token. -/
theorem Shape.record {r s limit z d next a : Nat} {st out : List Nat}
    (hs : Shape z d next st) (hr : r ≤ d + 1) (ha : next ≤ a)
    (h : RangeLazyRun r s limit next st (a :: out)) :
    ∃ st', Shape z (d + (a - next)) (a+1) st' ∧ RangeLazyRun r s limit (a+1) st' out := by
  have hzn := hs.bottom_lt
  obtain ⟨ys, rfl, hl, hz, hb⟩ := hs
  rcases h.cons_cases with ⟨after, pop, tail⟩ |
    ⟨before, after, lower, upper, fresh, read, pop, tail⟩
  · have hm := hb a (Step.pop_mem' pop)
    omega
  · have hzr : z ∉ List.range' next (a+1-next) := by
      intro hm
      rw [List.mem_range'] at hm
      omega
    have hbound : ∀ x ∈ after, x < a+1 := by
      intro x hx
      rcases pop.mem_after hx with hx | hx
      · rcases read.mem_after hx with hx | hx
        · have := hb x hx; omega
        · rw [List.mem_range'] at hx; omega
      · simp at hx
    obtain ⟨ys₁, hb₁, hl₁, hz₁⟩ := read_above_bottom read rfl ys z rfl (by omega) hz hzr
    rw [hb₁] at pop
    obtain ⟨ys₂, ha₂, hl₂, hz₂⟩ := pop_above_bottom pop (by omega) hz₁
    refine ⟨after, ⟨ys₂, ha₂, ?_, hz₂, hbound⟩, tail⟩
    simp only [List.length_range'] at hl₁
    omega

/-- Outputting an already-held token other than the bottom token. -/
theorem Shape.held_other {r s limit z d next a : Nat} {st out : List Nat}
    (hs : Shape z d next st) (ha : a < next) (haz : a ≠ z)
    (h : RangeLazyRun r s limit next st (a :: out)) :
    ∃ st', Shape z (d - 1) next st' ∧ RangeLazyRun r s limit next st' out := by
  obtain ⟨ys, rfl, hl, hz, hb⟩ := hs
  rcases h.cons_cases with ⟨after, pop, tail⟩ |
    ⟨before, after, lower, upper, fresh, read, pop, tail⟩
  · have hbound : ∀ x ∈ after, x < next := by
      intro x hx
      rcases pop.mem_after hx with hx | hx
      · exact hb x hx
      · simp at hx
    obtain ⟨ys', ha', hl', hz'⟩ := pop_above_bottom pop haz hz
    exact ⟨after, ⟨ys', ha', by omega, hz', hbound⟩, tail⟩
  · omega

/-- Outputting the bottom token requires fewer than `s` tokens above it. -/
theorem Shape.held_bottom {r s limit z d next : Nat} {st out : List Nat}
    (hs : Shape z d next st) (h : RangeLazyRun r s limit next st (z :: out)) :
    d < s := by
  have hzn := hs.bottom_lt
  obtain ⟨ys, rfl, hl, hz, hb⟩ := hs
  rcases h.cons_cases with ⟨after, pop, tail⟩ |
    ⟨before, after, lower, upper, fresh, read, pop, tail⟩
  · have := pop_bottom_depth pop hz
    omega
  · omega

/-- Drain a list of held non-bottom outputs. -/
theorem Shape.drain {r s limit z next : Nat} (l : List Nat)
    (hl : ∀ a ∈ l, a < next ∧ a ≠ z) :
    ∀ {d : Nat} {st out : List Nat}, Shape z d next st →
      RangeLazyRun r s limit next st (l ++ out) →
      ∃ st', Shape z (d - l.length) next st' ∧ RangeLazyRun r s limit next st' out := by
  induction l with
  | nil => intro d st out hs h; exact ⟨st, by simpa using hs, by simpa using h⟩
  | cons a l ih =>
    intro d st out hs h
    have ha := hl a (by simp)
    obtain ⟨st₁, hs₁, h₁⟩ := hs.held_other ha.1 ha.2 (by simpa using h)
    obtain ⟨st₂, hs₂, h₂⟩ := ih (fun b hb => hl b (by simp [hb])) hs₁ h₁
    refine ⟨st₂, ?_, h₂⟩
    have he : d - 1 - l.length = d - (a :: l).length := by simp; omega
    rw [he] at hs₂
    exact hs₂

/-- The first output `s+1` (zero-based `Q_0`) is a record read into an empty
stack. Its batch fixes a bottom token `z < r` at depth exactly `s`. -/
theorem first_record {r s limit : Nat} {out : List Nat} (hr : 1 ≤ r) (hrs : r < s)
    (h : RangeLazyRun r s limit 0 [] ((s+1) :: out)) :
    ∃ z st, z < r ∧ Shape z s (s+2) st ∧ RangeLazyRun r s limit (s+2) st out := by
  rcases h.cons_cases with ⟨after, pop, tail⟩ |
    ⟨before, after, lower, upper, fresh, read, pop, tail⟩
  · have hm := Step.pop_mem' pop
    simp at hm
  · have hread : Run r s [] (List.range' 0 (s+2)) [] before := by
      have hc : s+1+1-0 = s+2 := by omega
      simpa [hc] using read
    obtain ⟨ys, z, hb, hl, hz, hzr, hbd⟩ := initial_read hr (by omega) hread
    have hbound : ∀ x ∈ after, x < s+2 := by
      intro x hx
      rcases pop.mem_after hx with hx | hx
      · exact hbd x hx
      · simp at hx
    rw [hb] at pop
    obtain ⟨ys', ha, hl', hz'⟩ := pop_above_bottom pop (by omega) hz
    exact ⟨z, after, hzr, ⟨ys', ha, by omega, hz', hbound⟩, tail⟩

#print axioms read_above_bottom
#print axioms initial_read
#print axioms Shape.record
#print axioms Shape.held_bottom
#print axioms first_record
end Unequal
end StackSorting.Generalized
