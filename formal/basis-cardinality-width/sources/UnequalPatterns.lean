import UnequalThreshold

/-! Pattern closure at physical capacity `H`. Deleting any tokens from a
capacity-`H` history leaves a capacity-`H` history. So the capacity-`H`
classes are closed under patterns, and the single-deletion conditions of
`MinimalForbiddenH` and `SortMinimalH` make every proper pattern a member. -/
namespace StackSorting.Generalized

variable {α : Type}

/-- Filtering one step gives at most one step, and never a taller stack. -/
theorem Step.filterH {r s H : Nat} {held input output final : List α}
    (h : Step r s held input output final) (keep : α → Bool)
    (hc : held.length ≤ H) (hf : final.length ≤ H) :
    RunH r s H (held.filter keep) (input.filter keep) (output.filter keep)
      (final.filter keep) := by
  have hc' : (held.filter keep).length ≤ H :=
    Nat.le_trans (List.length_filter_le _ _) hc
  have hf' : (final.filter keep).length ≤ H :=
    Nat.le_trans (List.length_filter_le _ _) hf
  cases h with
  | push pre post x allowed =>
    have bound : (pre.filter keep).length < r :=
      Nat.lt_of_le_of_lt (List.length_filter_le _ _) allowed
    cases hx : keep x with
    | false =>
      simp only [List.filter_append, List.filter_cons, hx] at hc' hf' ⊢
      simpa using RunH.nil (r := r) (s := s) (pre.filter keep ++ post.filter keep) hc'
    | true =>
      simp only [List.filter_append, List.filter_cons, hx] at hc' hf' ⊢
      simpa using RunH.cons hc' (Step.push (pre.filter keep) (post.filter keep) x bound)
        (RunH.nil _ (by simpa using hf'))
  | pop pre post x allowed =>
    have bound : (pre.filter keep).length < s :=
      Nat.lt_of_le_of_lt (List.length_filter_le _ _) allowed
    cases hx : keep x with
    | false =>
      simp only [List.filter_append, List.filter_cons, hx] at hc' hf' ⊢
      simpa using RunH.nil (r := r) (s := s) (pre.filter keep ++ post.filter keep) hf'
    | true =>
      simp only [List.filter_append, List.filter_cons, hx] at hc' hf' ⊢
      simpa using RunH.cons hc' (Step.pop (pre.filter keep) (post.filter keep) x bound)
        (RunH.nil _ hf')

/-- Exact whole-history deletion at capacity `H`. -/
theorem RunH.filter {r s H : Nat} {held input output final : List α}
    (h : RunH r s H held input output final) (keep : α → Bool) :
    RunH r s H (held.filter keep) (input.filter keep) (output.filter keep)
      (final.filter keep) := by
  induction h with
  | nil held cap =>
    simpa using RunH.nil (r := r) (s := s) (held.filter keep)
      (Nat.le_trans (List.length_filter_le _ _) cap)
  | cons cap head tail ih =>
    simpa only [List.filter_append] using
      (head.filterH keep cap tail.start_cap).append ih

namespace Unequal
open BasisFamily (delete filter_delete)

/-- Every proper pattern of a capacity-`H` generated-side basis element is
generated within capacity `H`, under any relabelling (standardization in
particular). -/
theorem MinimalForbiddenH.proper_filter_map {r s H n : Nat} {p : List Nat}
    (h : MinimalForbiddenH r s H n p) (keep : Nat → Bool)
    (proper : ∃ a, a < n ∧ keep a = false) (f : Nat → Nat) :
    RunH r s H [] (((List.range n).filter keep).map f) ((p.filter keep).map f) [] := by
  obtain ⟨a, ha, hk⟩ := proper
  have hz := ((h.2.2 a ha).filter keep).map f
  simpa [filter_delete a _ keep hk] using hz

/-- Every proper pattern of a capacity-`H` sortable-side basis element is
sorted within capacity `H`, under any relabelling. -/
theorem SortMinimalH.proper_filter_map {r s H n : Nat} {π : List Nat}
    (h : SortMinimalH r s H n π) (keep : Nat → Bool)
    (proper : ∃ a, a < n ∧ keep a = false) (f : Nat → Nat) :
    RunH r s H [] ((π.filter keep).map f) (((List.range n).filter keep).map f) [] := by
  obtain ⟨a, ha, hk⟩ := proper
  have hz := ((h.2.2 a ha).filter keep).map f
  simpa [filter_delete a _ keep hk] using hz

end Unequal

#print axioms Step.filterH
#print axioms RunH.filter
#print axioms Unequal.MinimalForbiddenH.proper_filter_map
#print axioms Unequal.SortMinimalH.proper_filter_map
#print axioms RunH.map
#print axioms RunH.reverse
#print axioms Unequal.genH_delete_iff
#print axioms Unequal.MinimalForbiddenH.toSort
#print axioms Unequal.SortMinimalH.toGen
#print axioms Unequal.MinimalForbiddenH.toDual
#print axioms Unequal.family_minimalH
end StackSorting.Generalized
