import LocalForestLift
import StartMarkedDecomposition

universe u v
namespace StackSorting.Simon
open FactorizationTree

/-- The actual induction step at a selected letter image c. The hypotheses
are precisely the smaller-support and smaller-local-monoid induction results;
the conclusion constructs the original literal word's ambient tree. -/
theorem marked_local_divisor_reduction
    {A : Type u} {M : Type v} [Monoid M] [Fintype M] [DecidableEq M]
    (φ : A → M) (F : Finset M) (c : M) (w : List A)
    (hall : ∀ a ∈ w, φ a ∈ F) (hocc : ∃ a ∈ w, φ a = c)
    (H K : ℕ)
    (hsmaller : ∀ u : List A, u ≠ [] → (∀ a ∈ u, φ a ∈ F.erase c) → HasTree φ u H)
    (hlocal : ∀ (B : Type u) (ψ : B → LocalDivisor c) (z : List B), z ≠ [] → HasTree ψ z K) :
    HasTree φ w (H + (3 * Fintype.card M + 3) * K + 2) := by
  classical
  obtain ⟨pre,blocks,hw,hp,hb⟩ :=
    exists_start_marked_decomposition (fun a => φ a = c) w
  have hpF : ∀ a ∈ pre, φ a ∈ F.erase c := by
    intro a ha
    refine Finset.mem_erase.mpr ⟨hp a ha, hall a ?_⟩
    rw [hw]
    exact List.mem_append_left _ ha
  have hbF : ∀ z ∈ blocks, ∀ a ∈ z.2, φ a ∈ F.erase c := by
    intro z hz a ha
    refine Finset.mem_erase.mpr ⟨(hb z hz).2 a ha, hall a ?_⟩
    rw [hw]
    apply List.mem_append_right
    exact List.mem_flatMap.mpr ⟨z,hz,List.mem_cons_of_mem _ ha⟩
  have hblocks : blocks ≠ [] := by
    intro hempty
    obtain ⟨a,ha,hea⟩ := hocc
    rw [hw] at ha
    have hap : a ∈ pre := by simpa [hempty] using ha
    exact hp a hap hea
  let B := {z : A × List A // z ∈ blocks}
  let interior : B → M := fun b => (b.val.2.map φ).prod
  let subst : B → List A := fun b => b.val.1 :: b.val.2
  have hbase : ∀ b : B, HasTree φ (subst b) (H + 1) := by
    intro b
    by_cases htail : b.val.2 = []
    · simpa [subst,htail] using hasTree_singleton φ b.val.1 (H + 1)
    · have ht := hsmaller b.val.2 htail (hbF b.val b.property)
      simpa [subst] using hasTree_binary (hasTree_singleton φ b.val.1 H) ht
  have hvalue : ∀ b : B, ((subst b).map φ).prod = ambientBlockValue c interior b := by
    intro b
    simp [subst,ambientBlockValue,interior,(hb b.val b.property).1]
  have htlocal := hlocal B (localBlockValue c interior) blocks.attach
    (by
      intro he
      apply hblocks
      apply List.length_eq_zero_iff.mp
      simpa using congrArg List.length he)
  have htlift := localForest_lift c interior blocks.attach K htlocal
  have htsub := hasTree_substitute (ambientBlockValue c interior) φ subst (H + 1)
    hbase hvalue blocks.attach ((3 * Fintype.card M + 3) * K) htlift
  have hflatten : blocks.attach.flatMap subst = blocks.flatMap (fun z => z.1 :: z.2) := by
    simp only [subst,List.flatMap_def]
    exact congrArg List.flatten (List.attach_map_val (l := blocks)
      (f := fun z : A × List A => z.1 :: z.2))
  rw [hflatten] at htsub
  have htsub' : HasTree φ (blocks.flatMap (fun z => z.1 :: z.2))
      (H + (3 * Fintype.card M + 3) * K + 1) := hasTree_mono htsub (by omega)
  by_cases hprefix : pre = []
  · rw [hw,hprefix,List.nil_append]
    exact hasTree_mono htsub' (by omega)
  · have htpre := hsmaller pre hprefix hpF
    have htpre' := hasTree_mono htpre
      (by omega : H ≤ H + (3 * Fintype.card M + 3) * K + 1)
    rw [hw]
    simpa only [Nat.add_assoc] using hasTree_binary htpre' htsub'

#print axioms marked_local_divisor_reduction
end StackSorting.Simon
