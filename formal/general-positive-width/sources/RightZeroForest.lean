import FactorizationTree
import MarkedWordDecomposition

namespace StackSorting.Simon
open FactorizationTree

variable {A M : Type*} [Monoid M]

private theorem prod_append_singleton_of_absorbs (φ : A → M) (u : List A)
    (a : A) (h : ∀ b ∈ u, φ b * φ a = φ a) :
    ((u ++ [a]).map φ).prod = φ a := by
  induction u with
  | nil => simp
  | cons b u ih =>
    simp only [List.cons_append, List.map_cons, List.prod_cons]
    rw [ih (by intro c hc; exact h c (by simp [hc]))]
    exact h b (by simp)

/-- Genuine existence for a right-zero image: all letter-image products are
absorbed by their right factor. The height is uniform in the word length. -/
theorem exists_rightZero_tree_on_support (φ : A → M)
    (hzero : ∀ a b, φ a * φ b = φ b) (F : Finset M) :
    ∀ w : List A, w ≠ [] → (∀ a ∈ w, φ a ∈ F) →
      HasTree φ w (3 * F.card + 1) := by
  classical
  induction F using Finset.induction_on with
  | empty =>
    intro w hne hall
    obtain ⟨a, tail, rfl⟩ := List.exists_cons_of_ne_nil hne
    have := hall a (by simp)
    simp at this
  | @insert e F he ih =>
    intro w hne hall
    by_cases hocc : ∃ a ∈ w, φ a = e
    · obtain ⟨blocks, rest, hw, hblocks, hrest⟩ :=
        exists_marked_decomposition (fun a => φ a = e) w
      have hblocks_ne : blocks ≠ [] := by
        intro hempty
        obtain ⟨a, ha, hea⟩ := hocc
        have har : a ∈ rest := by
          rw [hw] at ha
          simpa [hempty] using ha
        exact hrest a har hea
      have hinterior : ∀ z ∈ blocks, ∀ a ∈ z.1, φ a ∈ F := by
        intro z hz a ha
        have ham : a ∈ w := by
          rw [hw]
          exact block_member_of_decomposition blocks rest hz ha
        have hm := hall a ham
        simp only [Finset.mem_insert] at hm
        exact hm.resolve_left ((hblocks z hz).2 a ha)
      have hrestF : ∀ a ∈ rest, φ a ∈ F := by
        intro a ha
        have ham : a ∈ w := by
          rw [hw]
          exact List.mem_append_right _ ha
        have hm := hall a ham
        simp only [Finset.mem_insert] at hm
        exact hm.resolve_left (hrest a ha)
      have hblocktrees : ∀ v ∈ blocks.map (fun z => z.1 ++ [z.2]),
          HasTree φ v (3 * F.card + 2) := by
        intro v hv
        obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hv
        by_cases hzi : z.1 = []
        · simpa [hzi] using hasTree_singleton φ z.2 (3 * F.card + 2)
        · have hzTree := ih z.1 hzi (hinterior z hz)
          have hend := hasTree_singleton φ z.2 (3 * F.card + 1)
          simpa only [Nat.add_assoc] using hasTree_binary hzTree hend
      have hvalues : ∀ v ∈ blocks.map (fun z => z.1 ++ [z.2]),
          (v.map φ).prod = e := by
        intro v hv
        obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hv
        rw [prod_append_singleton_of_absorbs φ z.1 z.2
          (by intro a _; exact hzero a z.2)]
        exact (hblocks z hz).1
      have hee : e * e = e := by
        obtain ⟨a, _, rfl⟩ := hocc
        exact hzero a a
      have hmain := hasTree_idempotent_blocks φ
        (blocks.map fun z => z.1 ++ [z.2]) (3 * F.card + 2)
        (by simpa using hblocks_ne) hblocktrees e hee hvalues
      have hmain' : HasTree φ (blocks.flatMap fun z => z.1 ++ [z.2])
          (3 * F.card + 3) := by
        simpa only [List.flatMap_def, Nat.add_assoc] using hmain
      have hcard : (insert e F).card = F.card + 1 := Finset.card_insert_of_notMem he
      by_cases hrnil : rest = []
      · rw [hw, hrnil, List.append_nil]
        exact hasTree_mono hmain' (by rw [hcard]; omega)
      · have hrTree := ih rest hrnil hrestF
        have hrTree' := hasTree_mono hrTree (by omega : 3 * F.card + 1 ≤ 3 * F.card + 3)
        rw [hw]
        exact hasTree_mono (hasTree_binary hmain' hrTree') (by rw [hcard]; omega)
    · have hi : HasTree φ w (3 * F.card + 1) := ih w hne (by
        intro a ha
        have hm := hall a ha
        simp only [Finset.mem_insert] at hm
        exact hm.resolve_left (by intro hae; exact hocc ⟨a, ha, hae⟩))
      apply hasTree_mono hi
      rw [Finset.card_insert_of_notMem he]
      omega

theorem exists_rightZero_tree [Fintype M] (φ : A → M)
    (hzero : ∀ a b, φ a * φ b = φ b) (w : List A) (hne : w ≠ []) :
    HasTree φ w (3 * Fintype.card M + 1) := by
  classical
  simpa using exists_rightZero_tree_on_support φ hzero Finset.univ w hne
    (by intro a _; exact Finset.mem_univ (φ a))

#print axioms exists_rightZero_tree_on_support
#print axioms exists_rightZero_tree
end StackSorting.Simon
