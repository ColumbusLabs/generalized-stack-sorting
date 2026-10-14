import DecompositionForests

namespace StackSorting.GuidedPathwidth
universe u
variable {N : Type u}

/-- Add one isolated index node, without changing any old edge. -/
def withIsolated (T : SimpleGraph N) : SimpleGraph (Option N) where
  Adj x y := match x,y with | some a,some b => T.Adj a b | _,_ => False
  symm := ⟨by intro x y h; cases x <;> cases y <;> simp_all [SimpleGraph.adj_comm]⟩
  loopless := ⟨by intro x; cases x <;> simp⟩

theorem withIsolated_support {T : SimpleGraph N} {x y : Option N}
    (p : (withIsolated T).Walk x y) (hx : x ∈ Set.range (@Option.some N))
    {z : Option N} (hz : z ∈ p.support) : z ∈ Set.range (@Option.some N) := by
  revert hx hz
  induction p with
  | @nil x =>
    intro hx hz
    have he : z = x := by simpa using hz
    exact he.symm ▸ hx
  | @cons x y w hxy p ih =>
    intro hx hz
    have hy : y ∈ Set.range (@Option.some N) := by
      cases x <;> cases y <;> simp_all [withIsolated]
      all_goals exact False.elim hxy
    simp only [SimpleGraph.Walk.support_cons,List.mem_cons] at hz
    rcases hz with rfl | hz
    · exact hx
    · exact ih hy hz

theorem withIsolated_acyclic {T : SimpleGraph N} (hT : T.IsAcyclic) :
    (withIsolated T).IsAcyclic := by
  classical
  intro x p hp
  have hx : x ∈ Set.range (@Option.some N) := by
    cases p with
    | nil => exact (hp.ne_nil rfl).elim
    | @cons x y z hxy p =>
      cases x <;> cases y <;> simp_all [withIsolated]
      all_goals exact False.elim hxy
  let S : Set (Option N) := Set.range (@Option.some N)
  have hs : ∀ z ∈ p.support, z ∈ S := fun _ hz => withIsolated_support p hx hz
  let q := p.induce S hs
  have hq : q.IsCycle := by
    apply SimpleGraph.Walk.IsCycle.of_map
      (f := (SimpleGraph.Embedding.induce (G := withIsolated T) S).toHom)
    simpa [q] using hp
  let f : (withIsolated T).induce S →g T := {
    toFun := fun z => Classical.choose z.property
    map_rel' := by
      intro a b hab
      have ha := Classical.choose_spec a.property
      have hb := Classical.choose_spec b.property
      change (withIsolated T).Adj a.val b.val at hab
      rw [← ha,← hb] at hab
      exact hab }
  have hf : Function.Injective f := by
    intro a b he
    apply Subtype.ext
    exact (Classical.choose_spec a.property).symm.trans
      ((congrArg Option.some he).trans (Classical.choose_spec b.property))
  exact hT (q.map f) (hq.map hf)

/-- The old forest sits literally as the some-indexed subgraph. -/
def withIsolatedHom (T : SimpleGraph N) : T →g withIsolated T where
  toFun := Option.some
  map_rel' := fun h => h

end StackSorting.GuidedPathwidth
