import Mathlib.Combinatorics.Pigeonhole
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Prod
import Mathlib.Tactic

/-!
Finite indexed counting for the B–P Lemma 5.9 construction.

The index type is never replaced by an endpoint-pair set: distinct indices with
identical endpoints remain distinct members of every fiber and path-use set.
Ordered endpoint pairs give the safe upper bound |A|²; distinctness or symmetry
of the endpoints is not needed. The route-existence/edge-incidence proof is
outside this file. Its exact counting interface is disjointness of a child's
pending-use set from at least one of the two constructed halves.
-/
namespace StackSorting.LowPathwidthParts.IndexedEndpointLoad

open Finset

variable {ι α : Type*} [DecidableEq ι] [DecidableEq α]

omit [DecidableEq ι] in
/-- A largest endpoint-pair fiber, constructed for a nonempty indexed family.
The cardinal inequality counts indices, including repeated endpoint pairs. -/
theorem exists_largest_endpoint_fiber (I : Finset ι) (A : Finset α)
    (endpoint : ι → α × α)
    (hendpoint : ∀ i ∈ I, (endpoint i).1 ∈ A ∧ (endpoint i).2 ∈ A)
    (hI : I.Nonempty) :
    ∃ p ∈ (A ×ˢ A),
      (∀ q ∈ (A ×ˢ A),
        (I.filter (fun i => endpoint i = q)).card ≤
          (I.filter (fun i => endpoint i = p)).card) ∧
      I.card ≤ A.card * A.card * (I.filter (fun i => endpoint i = p)).card := by
  have hmaps : ∀ i ∈ I, endpoint i ∈ (A ×ˢ A) := by
    intro i hi
    exact Finset.mem_product.mpr (hendpoint i hi)
  obtain ⟨i, hi⟩ := hI
  obtain ⟨p, hp, hmax⟩ := ((A ×ˢ A)).exists_max_image
    (fun q => (I.filter (fun i => endpoint i = q)).card) ⟨endpoint i, hmaps i hi⟩
  refine ⟨p, hp, hmax, ?_⟩
  by_contra h
  have hlt : ((A ×ˢ A)).card * (I.filter (fun i => endpoint i = p)).card <
      I.card := by
    rw [Finset.card_product]
    exact Nat.lt_of_not_ge h
  obtain ⟨q, hq, hqbig⟩ :=
    Finset.exists_lt_card_fiber_of_mul_lt_card_of_maps_to hmaps hlt
  exact (Nat.not_lt_of_ge (hmax q hq)) hqbig

/-- A finite nearly equal partition, including the empty set. -/
theorem exists_balanced_partition (S : Finset ι) :
    ∃ L R : Finset ι,
      L ⊆ S ∧ R ⊆ S ∧ Disjoint L R ∧ L ∪ R = S ∧
      L.card = S.card / 2 ∧ R.card = S.card - S.card / 2 ∧
      L.card ≤ R.card ∧ R.card ≤ L.card + 1 := by
  obtain ⟨L, hLS, hL⟩ := Finset.exists_subset_card_eq (s := S) (Nat.div_le_self S.card 2)
  refine ⟨L, S \ L, hLS, Finset.sdiff_subset, ?_, ?_, hL, ?_, ?_, ?_⟩
  · exact Finset.disjoint_left.mpr (by
      intro i hi hR
      exact (Finset.mem_sdiff.mp hR).2 hi)
  · exact Finset.union_sdiff_of_subset hLS
  · rw [Finset.card_sdiff_of_subset hLS, hL]
  · rw [Finset.card_sdiff_of_subset hLS, hL]
    omega
  · rw [Finset.card_sdiff_of_subset hLS, hL]
    omega

/-- The exact cubic arithmetic used by the indexed routing construction.
The zero-width case forces the pending index family to be empty. -/
theorem cubic_load_bound (k n m : Nat)
    (hcap : n ≤ 2 * k ^ 3) (hfiber : n ≤ k * k * m) :
    k + n - m / 2 ≤ 2 * k ^ 3 := by
  by_cases hk : k = 0
  · subst k
    have hn : n = 0 := by simpa using hcap
    subst n
    simp
  by_cases hsmall : k + n ≤ 2 * k ^ 3
  · omega
  have hk1 : 1 ≤ k := by omega
  have hk2 : k ≤ k * k := by nlinarith
  have hm : 2 * k ≤ m := by
    by_contra h
    have hm' : m + 1 ≤ 2 * k := by omega
    have hmul := Nat.mul_le_mul_left (k * k) hm'
    nlinarith [hcap]
  have hhalf : k ≤ m / 2 := by omega
  omega

/-- Actual pending index sets that avoid either half omit at least the smaller
half. This is the interface for an edge visited by at most one designated path. -/
theorem child_load_of_avoids_half (I S L R U : Finset ι) (k oldLoad : Nat)
    (hSI : S ⊆ I) (hLS : L ⊆ S) (hRS : R ⊆ S)
    (hL : L.card = S.card / 2) (hR : S.card / 2 ≤ R.card)
    (hUI : U ⊆ I) (havoid : Disjoint U L ∨ Disjoint U R)
    (hold : oldLoad ≤ k) :
    oldLoad + U.card ≤ k + I.card - S.card / 2 := by
  have omit_count {H : Finset ι} (hHI : H ⊆ I) (hUH : Disjoint U H) :
      U.card ≤ I.card - H.card := by
    have hsub : U ⊆ I \ H := by
      intro i hi
      exact Finset.mem_sdiff.mpr ⟨hUI hi, fun hH =>
        (Finset.disjoint_left.mp hUH) hi hH⟩
    simpa only [Finset.card_sdiff_of_subset hHI] using Finset.card_le_card hsub
  have hScard : S.card ≤ I.card := Finset.card_le_card hSI
  rcases havoid with hUL | hUR
  · have hU := omit_count (hLS.trans hSI) hUL
    omega
  · have hU := omit_count (hRS.trans hSI) hUR
    have hRcard : R.card ≤ I.card := Finset.card_le_card (hRS.trans hSI)
    omega

/-- Construct the largest fiber and its two balanced halves, then establish
all child-load bounds simultaneously. Empty families have three empty sets;
no endpoint pair is chosen when there is no pending index. -/
theorem exists_balanced_endpoint_split (I : Finset ι) (A : Finset α)
    (endpoint : ι → α × α) (k : Nat)
    (hendpoint : ∀ i ∈ I, (endpoint i).1 ∈ A ∧ (endpoint i).2 ∈ A)
    (hA : A.card ≤ k) (hIcap : I.card ≤ 2 * k ^ 3) :
    ∃ S L R : Finset ι,
      S ⊆ I ∧ L ⊆ S ∧ R ⊆ S ∧ Disjoint L R ∧ L ∪ R = S ∧
      L.card = S.card / 2 ∧ R.card = S.card - S.card / 2 ∧
      L.card ≤ R.card ∧ R.card ≤ L.card + 1 ∧
      (I = ∅ ∧ S = ∅ ∨
        ∃ p ∈ (A ×ˢ A), S = I.filter (fun i => endpoint i = p) ∧
          ∀ q ∈ (A ×ˢ A), (I.filter (fun i => endpoint i = q)).card ≤ S.card) ∧
      I.card ≤ k * k * S.card ∧
      ∀ (U : Finset ι) (oldLoad : Nat), U ⊆ I →
        (Disjoint U L ∨ Disjoint U R) → oldLoad ≤ k →
        oldLoad + U.card ≤ k + I.card - S.card / 2 ∧
        oldLoad + U.card ≤ 2 * k ^ 3 := by
  have construct (S : Finset ι) (hSI : S ⊆ I)
      (hsource : I = ∅ ∧ S = ∅ ∨
        ∃ p ∈ (A ×ˢ A), S = I.filter (fun i => endpoint i = p) ∧
          ∀ q ∈ (A ×ˢ A), (I.filter (fun i => endpoint i = q)).card ≤ S.card)
      (hcount : I.card ≤ k * k * S.card) :
      ∃ L R : Finset ι,
        L ⊆ S ∧ R ⊆ S ∧ Disjoint L R ∧ L ∪ R = S ∧
        L.card = S.card / 2 ∧ R.card = S.card - S.card / 2 ∧
        L.card ≤ R.card ∧ R.card ≤ L.card + 1 ∧
        (I = ∅ ∧ S = ∅ ∨
          ∃ p ∈ (A ×ˢ A), S = I.filter (fun i => endpoint i = p) ∧
            ∀ q ∈ (A ×ˢ A), (I.filter (fun i => endpoint i = q)).card ≤ S.card) ∧
        I.card ≤ k * k * S.card ∧
        ∀ (U : Finset ι) (oldLoad : Nat), U ⊆ I →
          (Disjoint U L ∨ Disjoint U R) → oldLoad ≤ k →
          oldLoad + U.card ≤ k + I.card - S.card / 2 ∧
          oldLoad + U.card ≤ 2 * k ^ 3 := by
    obtain ⟨L, R, hLS, hRS, hdisj, hunion, hL, hR, hLR, hRL⟩ :=
      exists_balanced_partition S
    refine ⟨L, R, hLS, hRS, hdisj, hunion, hL, hR, hLR, hRL,
      hsource, hcount, ?_⟩
    intro U oldLoad hUI havoid hold
    have hbound := child_load_of_avoids_half I S L R U k oldLoad hSI hLS hRS hL
      (by omega) hUI havoid hold
    exact ⟨hbound, hbound.trans (cubic_load_bound k I.card S.card hIcap hcount)⟩
  by_cases hI : I = ∅
  · obtain ⟨L, R, hrest⟩ := construct ∅ (Finset.empty_subset I)
      (Or.inl ⟨hI, rfl⟩) (by simp [hI])
    exact ⟨∅, L, R, Finset.empty_subset I, hrest⟩
  · obtain ⟨p, hp, hmax, hcountA⟩ := exists_largest_endpoint_fiber I A endpoint hendpoint
      (Finset.nonempty_iff_ne_empty.mpr hI)
    let S := I.filter (fun i => endpoint i = p)
    have hSI : S ⊆ I := Finset.filter_subset _ _
    have hcount : I.card ≤ k * k * S.card := hcountA.trans
      (Nat.mul_le_mul_right S.card (Nat.mul_le_mul hA hA))
    obtain ⟨L, R, hrest⟩ := construct S hSI (Or.inr ⟨p, hp, rfl, hmax⟩) hcount
    exact ⟨S, L, R, hSI, hrest⟩

omit [DecidableEq ι] in
/-- At width zero, the cap alone forces the indexed family to be empty. -/
theorem pending_empty_at_zero (I : Finset ι) (h : I.card ≤ 2 * (0 : Nat) ^ 3) :
    I = ∅ := by
  apply Finset.card_eq_zero.mp
  simpa using h

end StackSorting.LowPathwidthParts.IndexedEndpointLoad
