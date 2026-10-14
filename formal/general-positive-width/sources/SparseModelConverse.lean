import SparseModelEvents

namespace StackSorting.SparseEndpointMSO
open Generalized IntervalCritical

theorem modelEvents_lookup_iff {D : Model} {length x : Nat}
    (hp : TimePath D length) (e : EndpointEvent) :
    (modelEvents D)[x]? = some e ↔ x ∈ D.domain ∧ modelEvent D x = e := by
  constructor
  · intro he
    obtain ⟨hx, _⟩ := List.getElem?_eq_some_iff.mp he
    have hb : x < length := by simpa [modelEvents_length, hp.1] using hx
    have hm : x ∈ D.domain := by simpa [hp.1] using hb
    exact ⟨hm, Option.some.inj ((modelEvents_get hp hb).symm.trans he)⟩
  · rintro ⟨hx, he⟩
    have hb : x < length := by simpa [hp.1] using hx
    simpa [he] using modelEvents_get hp hb

theorem eventDiagram_modelEvents_insert {D : Model} {length x : Nat}
    (hp : TimePath D length) :
    (eventDiagram (modelEvents D)).I x ↔ x ∈ D.domain ∧ D.I x := by
  change (∃ a, (modelEvents D)[x]? = some (.push a)) ↔ _
  simp only [modelEvents_lookup_iff hp, modelEvent_push_iff]
  exact ⟨fun ⟨_, hm, hi, _⟩ => ⟨hm, hi⟩,
    fun ⟨hm, hi⟩ => ⟨insertionRank D x, hm, hi, rfl⟩⟩

theorem eventDiagram_modelEvents_remove {D : Model} {length x : Nat}
    (hp : TimePath D length) (h : MatchingAxioms D) :
    (eventDiagram (modelEvents D)).R x ↔ x ∈ D.domain ∧ D.R x := by
  change (∃ a, (modelEvents D)[x]? = some (.pop a)) ↔ _
  simp only [modelEvents_lookup_iff hp, modelEvent_pop_iff]
  constructor
  · rintro ⟨_, hm, hi, _⟩
    exact ⟨hm, (h.partition x hm).1.resolve_left hi⟩
  · rintro ⟨hm, hr⟩
    exact ⟨_, hm, fun hi => (h.partition x hm).2 ⟨hi, hr⟩, rfl⟩

theorem insertionRank_injective {D : Model} {length x y : Nat}
    (hp : TimePath D length) (hx : x ∈ D.domain) (hy : y ∈ D.domain)
    (hix : D.I x) (hiy : D.I y) (he : insertionRank D x = insertionRank D y) : x = y := by
  rw [insertionRank_eq_idxOf hp hx hix, insertionRank_eq_idxOf hp hy hiy] at he
  exact insertion_rank_injective ((mem_insertionTokens D x).mpr ⟨hx, hix⟩)
    ((mem_insertionTokens D y).mpr ⟨hy, hiy⟩) he

theorem eventDiagram_modelEvents_matching {D : Model} {length x y : Nat}
    (hp : TimePath D length) (h : MatchingAxioms D) :
    (eventDiagram (modelEvents D)).M x y ↔
      x ∈ D.domain ∧ y ∈ D.domain ∧ D.M x y := by
  change (∃ a, ((modelEvents D)[x]? = some (.push a) ∧
    (modelEvents D)[y]? = some (.pop a)) ∨
    ((modelEvents D)[x]? = some (.pop a) ∧
    (modelEvents D)[y]? = some (.push a))) ↔ _
  simp only [modelEvents_lookup_iff hp, modelEvent_push_iff, modelEvent_pop_iff]
  constructor
  · rintro ⟨a, hxy | hyx⟩
    · obtain ⟨⟨hx, hi, hxa⟩, ⟨hy, hni, hya⟩⟩ := hxy
      have hr := (h.partition y hy).1.resolve_left hni
      have hpi := (partner_insert_iff_remove h hy).mpr hr
      have he := insertionRank_injective hp hx (partner_spec h hy).1 hi hpi
        (hxa.trans hya.symm)
      exact ⟨hx, hy, he ▸ h.symmetric y hy _ (partner_spec h hy).1 (partner_spec h hy).2⟩
    · obtain ⟨⟨hx, hni, hxa⟩, ⟨hy, hi, hya⟩⟩ := hyx
      have hr := (h.partition x hx).1.resolve_left hni
      have hpi := (partner_insert_iff_remove h hx).mpr hr
      have he := insertionRank_injective hp hy (partner_spec h hx).1 hi hpi
        (hya.trans hxa.symm)
      exact ⟨hx, hy, he ▸ (partner_spec h hx).2⟩
  · rintro ⟨hx, hy, hm⟩
    rcases (h.partition x hx).1 with hi | hr
    · have hyr := (h.opposite x hx y hy hm).mp hi
      have hyni : ¬ D.I y := fun hyi => (h.partition y hy).2 ⟨hyi, hyr⟩
      have he := partner_unique h hy hx (h.symmetric x hx y hy hm)
      exact ⟨insertionRank D x, Or.inl ⟨⟨hx, hi, rfl⟩,
        ⟨hy, hyni, congrArg (insertionRank D) he.symm⟩⟩⟩
    · have hnyi : D.I y := (h.opposite y hy x hx (h.symmetric x hx y hy hm)).mpr hr
      have hxni : ¬ D.I x := fun hxi => (h.partition x hx).2 ⟨hxi, hr⟩
      have he := partner_unique h hx hy hm
      exact ⟨insertionRank D y, Or.inr ⟨⟨hx, hxni, congrArg (insertionRank D) he.symm⟩,
        ⟨hy, hnyi, rfl⟩⟩⟩

theorem model_extensionality (D E : Model) (hd : D.domain = E.domain)
    (hi : D.I = E.I) (hr : D.R = E.R) (hs : D.S = E.S) (hm : D.M = E.M) : D = E := by
  cases D
  cases E
  cases hd
  cases hi
  cases hr
  cases hs
  cases hm
  rfl

/-- Reconstruction preserves the entire sparse structure, including both
directions of every matching edge. Only off-domain predicates are normalized. -/
theorem supported_eq_eventDiagram {D : Model} {length : Nat}
    (hp : TimePath D length) (h : MatchingAxioms D) :
    supported D = eventDiagram (modelEvents D) := by
  apply model_extensionality
  · change D.domain = List.range (modelEvents D).length
    simp [modelEvents_length, hp.1]
  · funext x
    exact propext (eventDiagram_modelEvents_insert hp).symm
  · funext x
    exact propext (eventDiagram_modelEvents_remove hp h).symm
  · funext x y
    apply propext
    change (x ∈ D.domain ∧ y ∈ D.domain ∧ D.S x y) ↔
      x < (modelEvents D).length ∧ y < (modelEvents D).length ∧ x + 1 = y
    simp only [modelEvents_length, hp.1, List.length_range, List.mem_range]
    constructor
    · rintro ⟨hx, hy, hs⟩
      exact ⟨hx, hy, (hp.2 _ (by simpa [hp.1] using hx) _ (by simpa [hp.1] using hy)).mp hs⟩
    · rintro ⟨hx, hy, he⟩
      exact ⟨hx, hy, (hp.2 _ (by simpa [hp.1] using hx) _ (by simpa [hp.1] using hy)).mpr he⟩
  · funext x y
    exact propext (eventDiagram_modelEvents_matching hp h).symm

/-- Arbitrary time-indexed lazy matching structures are canonical permutation
diagrams. No recognition or feasibility premise is needed for this bijection
direction; the empty structure is included. -/
theorem supported_eq_canonicalDiagram {D : Model} {length : Nat}
    (hp : TimePath D length) (h : MatchingAxioms D) (hl : LazyBoundary D) :
    supported D = canonicalDiagram (decodedPermutation D) := by
  rw [supported_eq_eventDiagram hp h, modelEvents_eq_canonical hp h hl]
  rfl

/-- Actual original-machine generation is exactly the sparse eligibility
sentence for an arbitrary time-indexed lazy matching structure. -/
theorem sparseModel_generated_iff {D : Model} {length r s : Nat}
    (hp : TimePath D length) (h : MatchingAxioms D) (hl : LazyBoundary D) :
    Generalized.Run r s [] (List.range (insertionTokens D).length) (decodedPermutation D) [] ↔
      Satisfies D (eligibilitySentence r s) := by
  rw [generated_iff_sparseEndpointMSO (decodedPermutation_perm hp h),
    ← supported_eq_canonicalDiagram hp h hl]
  exact satisfies_supported D (eligibilitySentence r s)

#print axioms supported_eq_eventDiagram
#print axioms supported_eq_canonicalDiagram
#print axioms sparseModel_generated_iff
end StackSorting.SparseEndpointMSO
