import SparseModelReconstruction

namespace StackSorting.SparseEndpointMSO
open Generalized IntervalCritical

noncomputable def removalVertices (D : Model) : List Nat := by
  classical
  exact D.domain.filter (fun x => decide (D.R x))

@[simp] theorem mem_removalVertices (D : Model) (x : Nat) :
    x ∈ removalVertices D ↔ x ∈ D.domain ∧ D.R x := by
  classical
  simp [removalVertices]

theorem partner_insert_iff_remove {D : Model} (h : MatchingAxioms D) {x : Nat}
    (hx : x ∈ D.domain) : D.I (partner D x) ↔ D.R x := by
  obtain ⟨hy, hm⟩ := partner_spec h hx
  exact h.opposite _ hy x hx (h.symmetric x hx _ hy hm)

theorem partner_injective_on_domain {D : Model} (h : MatchingAxioms D)
    {x y : Nat} (hx : x ∈ D.domain) (hy : y ∈ D.domain)
    (he : partner D x = partner D y) : x = y := by
  have he' := congrArg (partner D) he
  simpa only [partner_involutive h hx, partner_involutive h hy] using he'

/-- A small domain-restricted injectivity lemma, avoiding any extension of the
matching involution to arbitrary natural-number vertex names. -/
theorem nodup_map_on {α β : Type} {L : List α} (hL : L.Nodup) (f : α → β)
    (hinj : ∀ x ∈ L, ∀ y ∈ L, f x = f y → x = y) : (L.map f).Nodup := by
  induction L with
  | nil => simp
  | cons a L ih =>
    have h := List.nodup_cons.mp hL
    refine List.nodup_cons.mpr ⟨?_, ih h.2 ?_⟩
    · intro hm
      obtain ⟨b, hb, he⟩ := List.mem_map.mp hm
      exact h.1 ((hinj b (by simp [hb]) a (by simp) he) ▸ hb)
    · intro x hx y hy he
      exact hinj x (by simp [hx]) y (by simp [hy]) he

/-- Read the insertion partner at each removal, in literal chronological order. -/
noncomputable def vertexOutput (D : Model) : List Nat :=
  (removalVertices D).map (partner D)

/-- Perfect matching alone proves that the output uses each insertion exactly
once. There is no pre-existing permutation premise. -/
theorem vertexOutput_perm {D : Model} {length : Nat}
    (hp : TimePath D length) (h : MatchingAxioms D) :
    (vertexOutput D).Perm (insertionTokens D) := by
  classical
  have hr : (removalVertices D).Nodup := (hp.1 ▸ List.nodup_range).filter _
  have hout : (vertexOutput D).Nodup := nodup_map_on hr _ (by
    intro x hx y hy he
    exact partner_injective_on_domain h ((mem_removalVertices D x).mp hx).1
      ((mem_removalVertices D y).mp hy).1 he)
  apply (List.perm_ext_iff_of_nodup hout (insertionTokens_nodup hp)).mpr
  intro v
  constructor
  · intro hv
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hv
    obtain ⟨hym, hyr⟩ := (mem_removalVertices D y).mp hy
    exact (mem_insertionTokens D _).mpr
      ⟨(partner_spec h hym).1, (partner_insert_iff_remove h hym).mpr hyr⟩
  · intro hv
    obtain ⟨hvm, hvi⟩ := (mem_insertionTokens D v).mp hv
    obtain ⟨hpm, hm⟩ := partner_spec h hvm
    have hpr := (h.opposite v hvm _ hpm hm).mp hvi
    exact List.mem_map.mpr ⟨partner D v,
      (mem_removalVertices D _).mpr ⟨hpm, hpr⟩, partner_involutive h hvm⟩

theorem map_idxOf_self {L : List Nat} (hn : L.Nodup) :
    L.map L.idxOf = List.range L.length := by
  apply List.ext_getElem (by simp)
  intro i hi hj
  simp only [List.getElem_map, List.getElem_range]
  exact hn.idxOf_getElem i (by simpa using hi)

/-- Zero-based insertion ranks turn the decoded vertex labels into the exact
permutation convention of canonicalEvents and the original stack machine. -/
noncomputable def decodedPermutation (D : Model) : List Nat :=
  (vertexOutput D).map (insertionTokens D).idxOf

theorem decodedPermutation_perm {D : Model} {length : Nat}
    (hp : TimePath D length) (h : MatchingAxioms D) :
    (decodedPermutation D).Perm (List.range (insertionTokens D).length) := by
  have he := (vertexOutput_perm hp h).map (insertionTokens D).idxOf
  simpa only [decodedPermutation, map_idxOf_self (insertionTokens_nodup hp)] using he

theorem decodedPermutation_length {D : Model} {length : Nat}
    (hp : TimePath D length) (h : MatchingAxioms D) :
    (decodedPermutation D).length = (insertionTokens D).length := by
  simpa using (decodedPermutation_perm hp h).length_eq

/-- Insertion-rank decoding is injective on the entire domain of token names. -/
theorem insertion_rank_injective {D : Model} {x y : Nat}
    (hx : x ∈ insertionTokens D) (hy : y ∈ insertionTokens D)
    (he : (insertionTokens D).idxOf x = (insertionTokens D).idxOf y) : x = y := by
  have hix := List.idxOf_lt_length_of_mem hx
  have hiy := List.idxOf_lt_length_of_mem hy
  calc
    x = (insertionTokens D)[(insertionTokens D).idxOf x] := (List.getElem_idxOf hix).symm
    _ = (insertionTokens D)[(insertionTokens D).idxOf y] := by congr 1
    _ = y := List.getElem_idxOf hiy

#print axioms vertexOutput_perm
#print axioms decodedPermutation_perm
#print axioms insertion_rank_injective
end StackSorting.SparseEndpointMSO
