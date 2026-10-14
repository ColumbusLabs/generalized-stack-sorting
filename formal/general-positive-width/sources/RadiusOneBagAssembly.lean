import BagPathFiniteAssembly

namespace FiniteFlow.Hypergraph
variable {V E : Type*} [DecidableEq V] [Fintype V] {n w : Nat}

noncomputable def homeCore (home : V → Fin n) (i : Fin n) : Finset V := by
  classical
  exact Finset.univ.filter (fun x => home x = i)

omit [DecidableEq V] in
@[simp] theorem mem_homeCore (home : V → Fin n) (i : Fin n) (x : V) :
    x ∈ homeCore home i ↔ home x = i := by
  classical
  simp [homeCore]

noncomputable def homePart (home : V → Fin n) (extra : Fin n → Finset V) (i : Fin n) : Finset V :=
  homeCore home i ∪ extra i

theorem homePart_bounds (home : V → Fin n) (extra : Fin n → Finset V)
    (radius : ∀ i x, x ∈ extra i → (home x).val ≤ i.val+1 ∧ i.val ≤ (home x).val+1)
    {i : Fin n} {x : V} (hx : x ∈ homePart home extra i) :
    (home x).val ≤ i.val+1 ∧ i.val ≤ (home x).val+1 := by
  rcases Finset.mem_union.mp hx with hx | hx
  · have h := (mem_homeCore home i x).mp hx
    simp only [h]
    omega
  · exact radius i x hx

/-- Core ownership partitions all vertices. Additional separator occurrences
at distance at most one therefore have an interval of piece positions. -/
theorem homePart_interval (home : V → Fin n) (extra : Fin n → Finset V)
    (radius : ∀ i x, x ∈ extra i → (home x).val ≤ i.val+1 ∧ i.val ≤ (home x).val+1)
    (i j k : Fin n) (hij : i ≤ j) (hjk : j ≤ k)
    (x : V) (hxi : x ∈ homePart home extra i) (hxk : x ∈ homePart home extra k) :
    x ∈ homePart home extra j := by
  by_cases heq : i = j
  · exact heq ▸ hxi
  by_cases heq' : j = k
  · exact heq'.symm ▸ hxk
  have hi := homePart_bounds home extra radius hxi
  have hk := homePart_bounds home extra radius hxk
  have hij' : i.val < j.val := by
    have h : i < j := lt_of_le_of_ne hij heq
    exact h
  have hjk' : j.val < k.val := by
    have h : j < k := lt_of_le_of_ne hjk heq'
    exact h
  have home_eq : home x = j := Fin.ext (by omega)
  exact Finset.mem_union_left _ ((mem_homeCore home j x).mpr home_eq)

/-- All cross-piece seams follow from radius-one support and the two local
endpoint conditions. In particular, no prefix-seam witness is assumed. -/
theorem homePart_compatible (home : V → Fin n) (extra : Fin n → Finset V)
    (D : ∀ i, BagPath (homePart home extra i) w)
    (radius : ∀ i x, x ∈ extra i → (home x).val ≤ i.val+1 ∧ i.val ≤ (home x).val+1)
    (extra_bag : ∀ i q, q ≤ (D i).last → extra i ⊆ (D i).bag q)
    (first : ∀ (i j : Fin n) (x : V), j.val+1=i.val → home x=i → x ∈ extra j → x ∈ (D i).bag 0)
    (last : ∀ (i j : Fin n) (x : V), i.val+1=j.val → home x=i → x ∈ extra j → x ∈ (D i).bag (D i).last) :
    BagChainCompatible (homePart home extra) D := by
  refine ⟨homePart_interval home extra radius,?_⟩
  intro i j hij x hxi hxj
  have hlt : i.val < j.val := hij
  constructor
  · by_cases hx : x ∈ extra i
    · exact extra_bag i (D i).last le_rfl hx
    · have hhome : home x = i := (mem_homeCore home i x).mp
        ((Finset.mem_union.mp hxi).resolve_right hx)
      have hxextra : x ∈ extra j := by
        rcases Finset.mem_union.mp hxj with hj | hj
        · have hh := (mem_homeCore home j x).mp hj
          have : i = j := hhome.symm.trans hh
          exact (ne_of_lt hij this).elim
        · exact hj
      have hr := radius j x hxextra
      have hstep : i.val+1=j.val := by rw [hhome] at hr; omega
      exact last i j x hstep hhome hxextra
  · by_cases hx : x ∈ extra j
    · exact extra_bag j 0 (Nat.zero_le _) hx
    · have hhome : home x = j := (mem_homeCore home j x).mp
        ((Finset.mem_union.mp hxj).resolve_right hx)
      have hxextra : x ∈ extra i := by
        rcases Finset.mem_union.mp hxi with hi | hi
        · have hh := (mem_homeCore home i x).mp hi
          have : i = j := hh.symm.trans hhome
          exact (ne_of_lt hij this).elim
        · exact hi
      have hr := radius i x hxextra
      have hstep : i.val+1=j.val := by rw [hhome] at hr; omega
      exact first j i x hstep hhome hxextra

/-- Hyperedges either lie in one separator or have a constant component home.
This yields full-edge localization, including harmless empty hyperedges. -/
theorem homePart_hyperedge_localization (hn : 0 < n)
    (home : V → Fin n) (extra : Fin n → Finset V) (inc : V → E → Prop)
    (edge_cases : ∀ e, (∃ i, ∀ x, inc x e → x ∈ extra i) ∨
      (∀ x y, inc x e → inc y e → home x = home y)) :
    ∀ e, ∃ i, ∀ x ∈ (Finset.univ : Finset V), inc x e → x ∈ homePart home extra i := by
  intro e
  rcases edge_cases e with hextra | hhome
  · obtain ⟨i,hi⟩ := hextra
    exact ⟨i,fun x _ hx => Finset.mem_union_right _ (hi x hx)⟩
  · by_cases he : ∃ x, inc x e
    · obtain ⟨x,hx⟩ := he
      refine ⟨home x,?_⟩
      intro y _ hy
      exact Finset.mem_union_left _ ((mem_homeCore home (home x) y).mpr (hhome y x hy hx))
    · exact ⟨⟨0,hn⟩,fun x _ hx => (he ⟨x,hx⟩).elim⟩

/-- Explicit finite assembly from component homes and their adjacent separators.
All interval, seam, vertex and full-hyperedge laws are constructed. -/
theorem radius_one_bag_assembly (hn : 0 < n)
    (home : V → Fin n) (extra : Fin n → Finset V)
    (D : ∀ i, BagPath (homePart home extra i) w)
    (radius : ∀ i x, x ∈ extra i → (home x).val ≤ i.val+1 ∧ i.val ≤ (home x).val+1)
    (extra_bag : ∀ i q, q ≤ (D i).last → extra i ⊆ (D i).bag q)
    (first : ∀ (i j : Fin n) (x : V), j.val+1=i.val → home x=i → x ∈ extra j → x ∈ (D i).bag 0)
    (last : ∀ (i j : Fin n) (x : V), i.val+1=j.val → home x=i → x ∈ extra j → x ∈ (D i).bag (D i).last)
    {inc : V → E → Prop} (local_cover : ∀ i, (D i).Covers inc)
    (edge_cases : ∀ e, (∃ i, ∀ x, inc x e → x ∈ extra i) ∨
      (∀ x y, inc x e → inc y e → home x = home y)) :
    ∃ D : BagPath (Finset.univ : Finset V) w, D.Covers inc := by
  let : Nonempty (Fin n) := ⟨⟨0,hn⟩⟩
  have inside : ∀ i, homePart home extra i ⊆ (Finset.univ : Finset V) :=
    fun _ => Finset.subset_univ _
  have cover : ∀ x ∈ (Finset.univ : Finset V), ∃ i, x ∈ homePart home extra i := by
    intro x _
    exact ⟨home x,Finset.mem_union_left _ ((mem_homeCore home (home x) x).mpr rfl)⟩
  let hc := homePart_compatible home extra D radius extra_bag first last
  exact ⟨assembleBagPath (homePart home extra) D inside cover hc,
    assembleBagPath_covers (homePart home extra) D inside cover hc local_cover
      (homePart_hyperedge_localization hn home extra inc edge_cases)⟩

end FiniteFlow.Hypergraph
