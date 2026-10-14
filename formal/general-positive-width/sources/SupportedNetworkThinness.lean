import ReplacementGlobalPathwidth

namespace FiniteFlow.Hypergraph
variable {V E F : Type*} {inc : V → E → Prop} {s t : V}

/-- A touched component lies in the actual supported vertex set, even when the
ambient finite type also contains isolated vertices from later prefix stages. -/
theorem componentTouches_supported (O : Set V)
    (support : ∀ x e, inc x e → x ∈ O) (hs : s ∈ O) (ht : t ∈ O)
    (x : V) (b : CutBoundary E)
    (hx : ComponentTouches (inc := inc) (s := s) (t := t) x b) : x ∈ O := by
  cases b with
  | source => exact old_component_supported O support hs (sameCutedgeComponent_symm inc s t hx)
  | sink => exact old_component_supported O support ht (sameCutedgeComponent_symm inc s t hx)
  | cut e =>
    obtain ⟨y,hy,hxy⟩ := hx
    exact old_component_supported O support (support y e hy) (sameCutedgeComponent_symm inc s t hxy)

/-- The one-bag base invariant uses the actual root bag's size, rather than
requiring the entire ambient graph to have bounded cardinality. -/
theorem small_supported_network_is_thin [Fintype V] [DecidableEq E]
    (O : Finset V) (k : Nat) (small : O.card ≤ k+1)
    (support : ∀ x e, inc x e → x ∈ O) (hs : s ∈ O) (ht : t ∈ O)
    (p : Path inc s t) : ThinNetworkLocalWitnesses p k := by
  classical
  have touches : ∀ x b, ComponentTouches (inc := inc) (s := s) (t := t) x b → x ∈ O :=
    componentTouches_supported (inc := inc) (s := s) (t := t) (↑O) support hs ht
  constructor
  · intro e he
    let P := appendixVertices inc s t e
    have hsub : P ⊆ O := by
      intro x hx
      exact touches x (.cut e) (((mem_appendixVertices inc s t e x).mp hx) (.cut e) he |>.mpr rfl)
    let D := (BagPath.single P).weaken ((Finset.card_le_card hsub).trans small)
    exact ⟨D,fun _ => ⟨0,le_rfl,fun _ hx _ => hx⟩,fun _ hx _ => hx⟩
  · intro i j _
    let P := bridgeVertices p i j
    have hv := (mem_boundaryTrace p _).mp (List.get_mem (boundaryTrace p) i)
    have hsub : P ⊆ O := by
      intro x hx
      exact touches x _ (((mem_bridgeVertices p i j x).mp hx) _ hv |>.mpr (Or.inl rfl))
    have bound : P.card ≤ 2*k+2 := by have := (Finset.card_le_card hsub).trans small; omega
    let D := (BagPath.single P).weaken bound
    exact ⟨D,fun _ => ⟨0,le_rfl,fun _ hx _ => hx⟩,fun _ hx _ => hx,fun _ hx _ => hx⟩

namespace ReplacementFrame
variable {old : V → E → Prop} {inserted : V → F → Prop} {removed : E}

theorem touched_replacement_supported (R : ReplacementFrame old inserted s t removed)
    (x : V) (b : CutBoundary ({e : E // e ≠ removed} ⊕ F))
    (hx : ComponentTouches (inc := ReplacementIncidence old inserted removed) (s := s) (t := t) x b) :
    x ∈ R.oldVertices ∨ x ∈ R.newVertices := by
  apply componentTouches_supported (R.oldVertices ∪ R.newVertices) ?_
    (Or.inl R.source_old) (Or.inl R.sink_old) x b hx
  intro y e hy
  cases e with
  | inl e => exact Or.inl (R.old_support y e.val hy)
  | inr f => exact Or.inr (R.new_support y f hy)

end ReplacementFrame
end FiniteFlow.Hypergraph
