import DecompositionRestriction
import DecompositionEmbedding

namespace StackSorting.GuidedPathwidth
universe u
variable {V : Type u} {G : SimpleGraph V} {P : Set V} {c : Nat}

namespace Color
/-- Re-express actual guides supported on P as guides of the induced graph,
without adding roots, edges, colors or paths. -/
noncomputable def induced (C : Color G P) : Color (G.induce P) Set.univ where
  support := fun r => {x | x.val ∈ C.support r.val}
  inside := by intro r x hx; trivial
  reaches := by
    intro r x hx
    obtain ⟨p⟩ := (C.reaches r.val x.val hx).induced
    let S : Set P := {y | y.val ∈ C.support r.val}
    let f : G.induce (C.support r.val) →g (G.induce P).induce S := {
      toFun := fun y => ⟨⟨y.val,C.inside r.val y.property⟩,y.property⟩
      map_rel' := by intro a b hab; exact hab }
    exact reachIn_of_induced ⟨p.map f⟩
  unique := by
    intro r s x hr hs
    exact Subtype.ext (C.unique r.val s.val x.val hr hs)
end Color

namespace System
noncomputable def induced (C : System G P c) : System (G.induce P) Set.univ c :=
  fun i => (C i).induced

theorem induced_captures (C : System G P c) {B : Set V}
    (_hB : B ⊆ P) (h : Captures G C B) :
    Captures (G.induce P) C.induced {x : P | x.val ∈ B} := by
  intro hb
  obtain ⟨r,hr⟩ := hb
  obtain ⟨x,hx⟩ := h ⟨r.val,hr⟩
  obtain ⟨i,hi⟩ := hx r.val hr
  have hxp : x ∈ P := (C i).inside r.val hi
  refine ⟨⟨x,hxp⟩,?_⟩
  intro s hs
  exact hx s.val hs
end System

/-- A concrete allowed-region decomposition is literally a decomposition of
that induced finite graph on the surviving actual vertex names. -/
noncomputable def GuidedDecomposition.induced (D : GuidedDecomposition G P c) :
    GuidedDecomposition (G.induce P) Set.univ c where
  decomposition := {
    Node := D.decomposition.Node
    finiteNode := inferInstance
    forest := D.decomposition.forest
    acyclic := D.decomposition.acyclic
    bag := fun a => {x | x.val ∈ D.decomposition.bag a}
    inside := by intro a x hx; trivial
    vertex := by
      intro x hx
      exact D.decomposition.vertex x.val x.property
    edge := by
      intro x y hxy hx hy
      exact D.decomposition.edge hxy x.property y.property
    running := by
      intro x a b ha hb
      exact D.decomposition.running x.val a b ha hb }
  guides := D.guides.induced
  captured := fun a => System.induced_captures D.guides (D.decomposition.inside a) (D.captured a)

/-- Embed an induced-graph decomposition back into its exact allowed region. -/
noncomputable def GuidedDecomposition.ofInduced
    (D : GuidedDecomposition (G.induce P) Set.univ c) : GuidedDecomposition G P c := by
  let E := D.map (SimpleGraph.Embedding.induce (G := G) P)
  have he : (SimpleGraph.Embedding.induce (G := G) P) '' Set.univ = P := by
    ext x
    simp
  exact he ▸ E

#print axioms GuidedDecomposition.induced
end StackSorting.GuidedPathwidth
