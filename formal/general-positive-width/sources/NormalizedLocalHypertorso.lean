import SaneSingletonNormalization
import SupportedNetworkThinness

namespace StackSorting.PrefixGrowth
open GraphWidth SameVertexForest ConnectedConeNormalization
open FiniteFlow.Hypergraph
variable {n : Nat}

/-- The immediate child on an actual strict ancestry interval is constructed
by descending ranks; it is not a selected-cone existence premise. -/
theorem exists_child_above (O : RankedOrder n) {z w : Fin n} (h : O.rel z w) :
    ∃ c, O.parent c = z ∧ O.parent c ≠ c ∧ Cone O c w := by
  have hpw := (O.parent_of_pred h).1
  rcases cone_parent O h with hzp | hzp
  · obtain ⟨c,hc,hne,hcw⟩ := exists_child_above O hzp
    exact ⟨c,hc,hne,cone_trans O hcw (Or.inl hpw)⟩
  · exact ⟨w,hzp.symm,O.parent_ne_of_pred h,cone_refl O w⟩
termination_by O.rank w
decreasing_by exact O.parent_rank_lt (O.parent_ne_of_pred h)

noncomputable def regionBagSet (G : Graph n) (O : RankedOrder n) (z : Fin n) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter (RegionBag G O z)

noncomputable def regionAdhesionSet (G : Graph n) (O : RankedOrder n) (z : Fin n) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter (RegionAdhesion G O z)

@[simp] theorem mem_regionBagSet (G : Graph n) (O : RankedOrder n) (z x : Fin n) :
    x ∈ regionBagSet G O z ↔ RegionBag G O z x := by
  classical
  simp [regionBagSet]

@[simp] theorem mem_regionAdhesionSet (G : Graph n) (O : RankedOrder n) (z x : Fin n) :
    x ∈ regionAdhesionSet G O z ↔ RegionAdhesion G O z x := by
  classical
  simp [regionAdhesionSet]

/-- Local edge identifiers distinguish original graph edges from child
adhesions, including parallel adhesions with equal vertex sets. Only original
edges incident with the newly introduced vertex are inserted at this stage. -/
def LocalHypertorsoInc (G : Graph n) (O : RankedOrder n) (z : Fin n) :
    Fin n → ((Fin n × Fin n) ⊕ Fin n) → Prop
  | x,.inl e => G.Adj e.1 e.2 ∧ (e.1 = z ∨ e.2 = z) ∧
      RegionBag G O z e.1 ∧ RegionBag G O z e.2 ∧ (x = e.1 ∨ x = e.2)
  | x,.inr c => O.parent c = z ∧ O.parent c ≠ c ∧ RegionAdhesion G O c x

theorem localHypertorso_support (G : Graph n) (O : RankedOrder n) (z x : Fin n)
    (e : (Fin n × Fin n) ⊕ Fin n) (h : LocalHypertorsoInc G O z x e) :
    x ∈ regionBagSet G O z := by
  apply (mem_regionBagSet G O z x).mpr
  cases e with
  | inl e => exact h.2.2.2.2.elim (fun he => he.symm ▸ h.2.2.1) (fun he => he.symm ▸ h.2.2.2.1)
  | inr c =>
    have hparent := h.2.2.2.2
    simpa only [h.1] using hparent

/-- Each strict bag vertex is joined to the margin vertex either by an actual
original edge or by an actual child adhesion. -/
theorem localHypertorso_star (G : Graph n) (O : RankedOrder n)
    (helim : ∀ {u v}, G.Adj u v → O.rel u v ∨ O.rel v u)
    (connected_cones : ∀ v u, Cone O v u → Walk G.Adj (Cone O v) v u)
    (z x : Fin n) (hx : x ∈ regionBagSet G O z) :
    Nonempty (HWalk (LocalHypertorsoInc G O z) z x) := by
  classical
  have hbag := (mem_regionBagSet G O z x).mp hx
  rcases hbag with rfl | ⟨hxz,w,hw,hxw⟩
  · exact ⟨.nil _⟩
  · rcases hw with hzw | hzw
    · obtain ⟨c,hc,hne,hcw⟩ := exists_child_above O hzw
      have hzc : O.rel z c := hc ▸ O.parent_rel hne
      have hxbag : RegionBag G O c x := Or.inr ⟨O.trans hxz hzc,w,hcw,hxw⟩
      have hxne : x ≠ c := by intro he; subst x; exact O.irrefl c (O.trans hxz hzc)
      have hzbag : RegionBag G O c z := by
        simpa only [hc] using connected_parent_in_bag G O helim connected_cones hne
      have hzad : RegionAdhesion G O c z := (regionAdhesion_iff G O c z).mpr
        ⟨hzbag,by intro he; exact hne (hc.trans he)⟩
      have hxad := (regionAdhesion_iff G O c x).mpr ⟨hxbag,hxne⟩
      exact ⟨.cons (.inr c) ⟨hc,hne,hzad⟩ ⟨hc,hne,hxad⟩ (.nil x)⟩
    · subst w
      have hxbag : RegionBag G O z x := Or.inr ⟨hxz,z,cone_refl O z,hxw⟩
      have hzbag : RegionBag G O z z := Or.inl rfl
      exact ⟨.cons (.inl (x,z)) ⟨hxw,Or.inr rfl,hxbag,hzbag,Or.inr rfl⟩
        ⟨hxw,Or.inr rfl,hxbag,hzbag,Or.inl rfl⟩ (.nil x)⟩

theorem localHypertorso_connected (G : Graph n) (O : RankedOrder n)
    (helim : ∀ {u v}, G.Adj u v → O.rel u v ∨ O.rel v u)
    (connected_cones : ∀ v u, Cone O v u → Walk G.Adj (Cone O v) v u)
    (z x y : Fin n) (hx : x ∈ regionBagSet G O z) (hy : y ∈ regionBagSet G O z) :
    Nonempty (HWalk (LocalHypertorsoInc G O z) x y) := by
  obtain ⟨px⟩ := localHypertorso_star G O helim connected_cones z x hx
  obtain ⟨py⟩ := localHypertorso_star G O helim connected_cones z y hy
  exact ⟨px.reverse.append py⟩

/-- The adhesion loses its actual singleton margin vertex, deriving the rank
bound from the original bag bound rather than assuming a separator-size axiom. -/
theorem regionAdhesion_card_le (G : Graph n) (O : RankedOrder n) (k : Nat)
    (width : ∀ z, (regionBagSet G O z).card ≤ k+1) (z : Fin n) :
    (regionAdhesionSet G O z).card ≤ k := by
  classical
  have heq : regionAdhesionSet G O z = (regionBagSet G O z).erase z := by
    ext x
    simp only [mem_regionAdhesionSet,Finset.mem_erase,mem_regionBagSet,regionAdhesion_iff]
    exact and_comm
  have hz : z ∈ regionBagSet G O z := (mem_regionBagSet G O z z).mpr (Or.inl rfl)
  rw [heq,Finset.card_erase_of_mem hz]
  have := width z
  omega

end StackSorting.PrefixGrowth
