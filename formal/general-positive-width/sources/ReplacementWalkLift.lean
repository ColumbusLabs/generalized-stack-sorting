import ReplacementBagSurgery
import CutedgeClassification

namespace FiniteFlow.Hypergraph.HWalk
variable {V E F : Type*} {inc : V → E → Prop} {inc' : V → F → Prop}

def mapEdges (f : E → F) (h : ∀ x e, inc x e → inc' x (f e)) {s t : V} :
    HWalk inc s t → HWalk inc' s t
  | .nil x => .nil x
  | .cons e hx hy tail => .cons (f e) (h _ _ hx) (h _ _ hy) (tail.mapEdges f h)

@[simp] theorem edges_mapEdges (f : E → F) (h : ∀ x e, inc x e → inc' x (f e))
    {s t : V} (w : HWalk inc s t) : (w.mapEdges f h).edges = w.edges.map f := by
  induction w with
  | nil => rfl
  | cons e hx hy tail ih => exact congrArg (List.cons (f e)) ih
end FiniteFlow.Hypergraph.HWalk

namespace FiniteFlow.Hypergraph
variable {V E F : Type*} {old : V → E → Prop} {inserted : V → F → Prop}

/-- Each use of the removed edge is replaced with an actual inserted walk.
Only connectivity between its incident vertices is required for this direction. -/
noncomputable def liftReplacement (removed : E)
    (connected : ∀ a b, old a removed → old b removed → Nonempty (HWalk inserted a b))
    {s t : V} : HWalk old s t → HWalk (ReplacementIncidence old inserted removed) s t
  | .nil x => .nil x
  | .cons (x := a) (y := b) e ha hb tail => by
    classical
    exact if h : e = removed then
      ((connected a b (h ▸ ha) (h ▸ hb)).some.mapEdges (inc := inserted)
        (inc' := ReplacementIncidence old inserted removed) Sum.inr (fun _ _ h => h)).append
        (liftReplacement removed connected tail)
    else
      .cons (.inl ⟨e,h⟩) ha hb (liftReplacement removed connected tail)

/-- Lifting neither loses nor creates any surviving old edge identifier. -/
theorem liftReplacement_old_mem (removed : E)
    (connected : ∀ a b, old a removed → old b removed → Nonempty (HWalk inserted a b))
    {s t : V} (w : HWalk old s t) (f : {e : E // e ≠ removed}) :
    Sum.inl f ∈ (liftReplacement removed connected w).edges ↔ f.val ∈ w.edges := by
  classical
  induction w with
  | nil => simp [liftReplacement,HWalk.edges]
  | @cons a b t e ha hb tail ih =>
    by_cases h : e = removed
    · subst e
      simp only [liftReplacement, dite_true, HWalk.edges_append, List.mem_append,
        HWalk.edges, List.mem_cons]
      rw [HWalk.edges_mapEdges (inc := inserted) (inc' := ReplacementIncidence old inserted removed)
        Sum.inr (fun _ _ h => h)]
      simp [ih, f.property]
    · simp only [liftReplacement,dite_eq_right h,HWalk.edges,List.mem_cons,Sum.inl.injEq,
        Subtype.ext_iff,ih]

/-- No surviving old noncutedge becomes a cutedge after connected replacement.
This follows from actual walk lifting, not an assumed two-path witness. -/
theorem replacement_cutedge_old_implies (removed : E)
    (connected : ∀ a b, old a removed → old b removed → Nonempty (HWalk inserted a b))
    {s t : V} (f : {e : E // e ≠ removed})
    (hf : Cutedge (ReplacementIncidence old inserted removed) s t (.inl f)) :
    Cutedge old s t f.val := by
  intro p
  have hm := (cutedge_iff_every_walk _ _ _ _).mp hf
    (liftReplacement removed connected p.walk)
  exact (liftReplacement_old_mem removed connected p.walk f).mp hm

end FiniteFlow.Hypergraph
