import OrderedBagPath

namespace FiniteFlow.Hypergraph
variable {V E I : Type*} [DecidableEq V] [LinearOrder I]

/- Geometric conditions on the regions and endpoint bags of a finite chain.
These are elementary overlap conditions, not a global decomposition witness. -/
structure BagChainCompatible (parts : I → Finset V) {bound : Nat}
    (D : ∀ i, BagPath (parts i) bound) : Prop where
  region_interval : ∀ i j k, i ≤ j → j ≤ k → ∀ x,
    x ∈ parts i → x ∈ parts k → x ∈ parts j
  seam : ∀ i j, i < j → ∀ x, x ∈ parts i → x ∈ parts j →
    x ∈ (D i).bag (D i).last ∧ x ∈ (D j).bag 0

private theorem lex_fst_le {A : I → Type*} [∀ i, LinearOrder (A i)]
    {a b : Σₗ i, A i} (h : a ≤ b) : a.1 ≤ b.1 := by
  rcases Sigma.Lex.le_def.mp h with h | ⟨h,_⟩
  · exact le_of_lt h
  · exact le_of_eq h

private theorem lex_same_le {A : I → Type*} [∀ i, LinearOrder (A i)]
    {i : I} {a b : A i} (h : toLex (⟨i,a⟩ : Sigma A) ≤ toLex ⟨i,b⟩) : a ≤ b := by
  rcases Sigma.Lex.le_def.mp h with h | ⟨h,hh⟩
  · exact (lt_irrefl i h).elim
  · cases h
    exact hh

/- Flatten every actual local bag, in lexicographic piece/bag order. The
running-intersection proof handles all four ways three bags can occupy pieces. -/
def assembleOrderedBagPath {whole : Finset V} {bound : Nat}
    (parts : I → Finset V) (D : ∀ i, BagPath (parts i) bound)
    (inside : ∀ i, parts i ⊆ whole)
    (cover : ∀ x ∈ whole, ∃ i, x ∈ parts i)
    (compatible : BagChainCompatible parts D) :
    OrderedBagPath (Σₗ i, Fin ((D i).last+1)) whole bound where
  bag := fun a => (D a.1).bag a.2.val
  inside := fun a => Finset.Subset.trans ((D a.1).inside a.2.val (by have := a.2.isLt; omega))
    (inside a.1)
  bounded := fun a => (D a.1).bounded a.2.val (by have := a.2.isLt; omega)
  vertex := by
    intro x hx
    obtain ⟨i,hi⟩ := cover x hx
    obtain ⟨a,ha,hxa⟩ := (D i).vertex x hi
    exact ⟨⟨i,⟨a,by omega⟩⟩,hxa⟩
  interval := by
    rintro ⟨i,a⟩ ⟨j,b⟩ ⟨k,c⟩ hab hbc x hxa hxc
    have hij : i ≤ j := lex_fst_le hab
    have hjk : j ≤ k := lex_fst_le hbc
    have ha : a.val ≤ (D i).last := by have := a.isLt; omega
    have hb : b.val ≤ (D j).last := by have := b.isLt; omega
    have hc : c.val ≤ (D k).last := by have := c.isLt; omega
    have hxi := (D i).inside _ ha hxa
    have hxk := (D k).inside _ hc hxc
    by_cases heq : i = j
    · subst j
      have hab' : a.val ≤ b.val := lex_same_le hab
      by_cases heq : i = k
      · subst k
        have hbc' : b.val ≤ c.val := lex_same_le hbc
        exact (D i).interval _ _ _ hab' hbc' hc x hxa hxc
      · have hik : i < k := lt_of_le_of_ne hjk heq
        have hs := compatible.seam i k hik x hxi hxk
        exact (D i).interval _ _ _ hab' hb le_rfl x hxa hs.1
    · have hij' : i < j := lt_of_le_of_ne hij heq
      by_cases heq : j = k
      · subst k
        have hbc' : b.val ≤ c.val := lex_same_le hbc
        have hs := compatible.seam i j hij' x hxi hxk
        exact (D j).interval _ _ _ (Nat.zero_le _) hbc' hc x hs.2 hxc
      · have hjk' : j < k := lt_of_le_of_ne hjk heq
        have hxj := compatible.region_interval i j k hij hjk x hxi hxk
        have hfirst := (compatible.seam i j hij' x hxi hxj).2
        have hlast := (compatible.seam j k hjk' x hxj hxk).1
        exact (D j).interval 0 b.val (D j).last (Nat.zero_le _) hb le_rfl x hfirst hlast

/- Whole-hyperedge localization, followed by the actual local covering bag,
provides a whole-hyperedge covering bag of the assembled path. -/
omit [DecidableEq V] in
theorem assembleOrderedBagPath_covers {whole : Finset V} {bound : Nat}
    (parts : I → Finset V) (D : ∀ i, BagPath (parts i) bound)
    (inside : ∀ i, parts i ⊆ whole) (cover : ∀ x ∈ whole, ∃ i, x ∈ parts i)
    (compatible : BagChainCompatible parts D) {inc : V → E → Prop}
    (local_cover : ∀ i, (D i).Covers inc)
    (localized : ∀ e, ∃ i, ∀ x ∈ whole, inc x e → x ∈ parts i) :
    (assembleOrderedBagPath parts D inside cover compatible).Covers inc := by
  intro e
  obtain ⟨i,hi⟩ := localized e
  obtain ⟨a,ha,hea⟩ := local_cover i e
  refine ⟨⟨i,⟨a,by omega⟩⟩,?_⟩
  intro x hx hxe
  exact hea x (hi x hx hxe) hxe

noncomputable instance assemblyIndexNonempty [Nonempty I] {parts : I → Finset V} {bound : Nat}
    (D : ∀ i, BagPath (parts i) bound) : Nonempty (Σₗ i, Fin ((D i).last+1)) :=
  ⟨toLex ⟨Classical.choice (inferInstance : Nonempty I),⟨0,Nat.zero_lt_succ _⟩⟩⟩

/- The finite-chain construction returns the original natural-index bag path.
This theorem is the reusable assembly engine, not the network-specific 5.7
statement: its region and seam conditions still require component proofs. -/
noncomputable def assembleBagPath [Fintype I] [Nonempty I]
    {whole : Finset V} {bound : Nat}
    (parts : I → Finset V) (D : ∀ i, BagPath (parts i) bound)
    (inside : ∀ i, parts i ⊆ whole) (cover : ∀ x ∈ whole, ∃ i, x ∈ parts i)
    (compatible : BagChainCompatible parts D) : BagPath whole bound :=
  (assembleOrderedBagPath parts D inside cover compatible).toBagPath

omit [DecidableEq V] in
theorem assembleBagPath_covers [Fintype I] [Nonempty I]
    {whole : Finset V} {bound : Nat}
    (parts : I → Finset V) (D : ∀ i, BagPath (parts i) bound)
    (inside : ∀ i, parts i ⊆ whole) (cover : ∀ x ∈ whole, ∃ i, x ∈ parts i)
    (compatible : BagChainCompatible parts D) {inc : V → E → Prop}
    (local_cover : ∀ i, (D i).Covers inc)
    (localized : ∀ e, ∃ i, ∀ x ∈ whole, inc x e → x ∈ parts i) :
    (assembleBagPath parts D inside cover compatible).Covers inc :=
  OrderedBagPath.toBagPath_covers _
    (assembleOrderedBagPath_covers parts D inside cover compatible local_cover localized)

end FiniteFlow.Hypergraph
