import GeneralizedCanonicalRecords

/-!
Every nonempty token subset has one token satisfying both strict endpoint bounds
if and only if the token system can be peeled. Composing with canonical endpoint
recognition gives an all-length literal-machine criterion for every permutation.
No MSO-definability, graph-width, tree-automata or algebraicity claim is made.
-/
namespace StackSorting.IntervalCritical
open List

/-- Sublists inherit the ambient order. On a duplicate-free ambient token list,
these represent each subset exactly once. Both bounds concern the same token. -/
def EverySublistEligible (e : Endpoints) (r s : Nat) (U : Tokens) : Prop :=
  ∀ V : Tokens, V <+ U → V ≠ [] → ∃ v, v ∈ V ∧ Eligible e r s V v

/-- Order-independent finite subsets, represented by arbitrary duplicate-free
lists. Duplicate entries are excluded because endpoint counts count tokens. -/
def EverySubsetEligible (e : Endpoints) (r s : Nat) (U : Tokens) : Prop :=
  ∀ V : Tokens, V.Nodup → V ⊆ U → V ≠ [] → ∃ v, v ∈ V ∧ Eligible e r s V v

theorem Peelable.exists_eligible {e : Endpoints} {r s : Nat} {U : Tokens}
    (h : Peelable e r s U) (hne : U ≠ []) :
    ∃ v, v ∈ U ∧ Eligible e r s U v := by
  cases h with
  | nil => exact False.elim (hne rfl)
  | step v hv he _ => exact ⟨v, hv, he⟩

/-- Successful peeling restricts to every sublist of a duplicate-free universe. -/
theorem Peelable.everySublistEligible {e : Endpoints} {r s : Nat} {U : Tokens}
    (h : Peelable e r s U) (hn : U.Nodup) : EverySublistEligible e r s U := by
  intro V hsub hne
  have heq : V = U.filter (fun v => decide (v ∈ V)) := by
    apply StackSorting.Generalized.sublist_eq_filter hn hsub
    intro v _
    simp
  have hV : Peelable e r s V := by
    rw [heq]
    exact h.filter (fun v => decide (v ∈ V))
  exact hV.exists_eligible hne

/-- The universal condition descends through deletion without a width or
endpoint-validity hypothesis. -/
theorem EverySublistEligible.sublist {e : Endpoints} {r s : Nat} {U V : Tokens}
    (h : EverySublistEligible e r s U) (hsub : V <+ U) :
    EverySublistEligible e r s V := by
  intro W hW hne
  exact h W (hW.trans hsub) hne

/-- Choose an eligible token from the current nonempty list and erase it. Strong
induction on the list length terminates this construction of a peeling witness. -/
theorem EverySublistEligible.peelable {e : Endpoints} {r s : Nat} {U : Tokens}
    (h : EverySublistEligible e r s U) : Peelable e r s U := by
  have aux : ∀ m : Nat, ∀ W : Tokens, W.length = m →
      EverySublistEligible e r s W → Peelable e r s W := by
    intro m
    induction m using Nat.strongRecOn with
    | ind m ih =>
      intro W hm hW
      by_cases hnil : W = []
      · subst W
        exact .nil
      · obtain ⟨v, hv, he⟩ := hW W (.refl _) hnil
        have hlt : (W.erase v).length < m := by
          have hpos : 0 < W.length := List.length_pos_iff.mpr hnil
          rw [List.length_erase_of_mem hv]
          omega
        exact .step v hv he
          (ih _ hlt (W.erase v) rfl (hW.sublist List.erase_sublist))
  exact aux U.length U rfl h

theorem peelable_iff_everySublistEligible {e : Endpoints} {r s : Nat} {U : Tokens}
    (hn : U.Nodup) : Peelable e r s U ↔ EverySublistEligible e r s U :=
  ⟨fun h => h.everySublistEligible hn, EverySublistEligible.peelable⟩

/-- A subset in an arbitrary order is a permutation of the ambient membership
filter. Existing permutation invariance removes any order convention. -/
theorem Peelable.everySubsetEligible {e : Endpoints} {r s : Nat} {U : Tokens}
    (h : Peelable e r s U) (hn : U.Nodup) : EverySubsetEligible e r s U := by
  intro V hVn hsub hne
  let keep : Nat → Bool := fun v => decide (v ∈ V)
  have hp : (U.filter keep).Perm V := by
    apply (List.perm_ext_iff_of_nodup (hn.filter keep) hVn).mpr
    intro v
    simp only [List.mem_filter, keep, decide_eq_true_eq]
    exact ⟨fun hv => hv.2, fun hv => ⟨hsub hv, hv⟩⟩
  exact ((h.filter keep).perm hp).exists_eligible hne

/-- On a duplicate-free universe every sublist is one of the finite subsets. -/
theorem EverySubsetEligible.everySublistEligible {e : Endpoints} {r s : Nat}
    {U : Tokens} (h : EverySubsetEligible e r s U) (hn : U.Nodup) :
    EverySublistEligible e r s U := by
  intro V hsub hne
  exact h V (hn.sublist hsub) hsub.subset hne

theorem peelable_iff_everySubsetEligible {e : Endpoints} {r s : Nat} {U : Tokens}
    (hn : U.Nodup) : Peelable e r s U ↔ EverySubsetEligible e r s U :=
  ⟨fun h => h.everySubsetEligible hn,
   fun h => (h.everySublistEligible hn).peelable⟩

theorem everySublistEligible_iff_everySubsetEligible {e : Endpoints} {r s : Nat}
    {U : Tokens} (hn : U.Nodup) :
    EverySublistEligible e r s U ↔ EverySubsetEligible e r s U :=
  (peelable_iff_everySublistEligible hn).symm.trans
    (peelable_iff_everySubsetEligible hn)

end StackSorting.IntervalCritical

namespace StackSorting.Generalized
open List IntervalCritical

/-- Every output permutation is generated exactly when each nonempty canonical
sublist has a token eligible at both endpoints. Widths may be zero. -/
theorem generated_iff_everySublistEligible {r s n : Nat} {output : List Nat}
    (hp : output.Perm (List.range n)) :
    Run r s [] (List.range n) output [] ↔
      EverySublistEligible (extractedEndpoints (canonicalEvents 0 output)) r s (List.range n) :=
  (generated_iff_canonical_peelable hp).trans
    (peelable_iff_everySublistEligible List.nodup_range)

/-- Order-independent all-subsets endpoint criterion for the literal machine.
The sole premise says that the output is a genuine permutation of the input. -/
theorem generated_iff_everySubsetEligible {r s n : Nat} {output : List Nat}
    (hp : output.Perm (List.range n)) :
    Run r s [] (List.range n) output [] ↔
      EverySubsetEligible (extractedEndpoints (canonicalEvents 0 output)) r s (List.range n) :=
  (generated_iff_canonical_peelable hp).trans
    (peelable_iff_everySubsetEligible List.nodup_range)

/-- The final criterion with its quantifiers and both strict counts displayed.
The same witness token must meet the insertion and removal bound. -/
theorem generated_iff_every_subset_endpoint_bounds {r s n : Nat} {output : List Nat}
    (hp : output.Perm (List.range n)) :
    Run r s [] (List.range n) output [] ↔
      ∀ V : List Nat, V.Nodup → V ⊆ List.range n → V ≠ [] →
        ∃ v, v ∈ V ∧
          endpointCount (extractedEndpoints (canonicalEvents 0 output)) V
            ((extractedEndpoints (canonicalEvents 0 output)).left v) < r ∧
          endpointCount (extractedEndpoints (canonicalEvents 0 output)) V
            ((extractedEndpoints (canonicalEvents 0 output)).right v) < s :=
  generated_iff_everySubsetEligible hp

#print generated_iff_every_subset_endpoint_bounds
#print axioms generated_iff_everySublistEligible
#print axioms generated_iff_everySubsetEligible
#print axioms generated_iff_every_subset_endpoint_bounds
end StackSorting.Generalized

#print axioms StackSorting.IntervalCritical.Peelable.everySublistEligible
#print axioms StackSorting.IntervalCritical.EverySublistEligible.peelable
#print axioms StackSorting.IntervalCritical.peelable_iff_everySubsetEligible
