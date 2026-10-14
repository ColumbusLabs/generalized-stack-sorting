import ReplacementWalkLift

namespace FiniteFlow.Hypergraph.HWalk
variable {V W E F : Type*} {inc : V → E → Prop} {inc' : W → F → Prop}

/-- Map both names and edge identifiers through an incidence-preserving map. -/
def mapIncidence (vertices : V → W) (edges : E → F)
    (h : ∀ x e, inc x e → inc' (vertices x) (edges e)) {s t : V} :
    HWalk inc s t → HWalk inc' (vertices s) (vertices t)
  | .nil x => .nil (vertices x)
  | .cons e hx hy tail => .cons (edges e) (h _ _ hx) (h _ _ hy)
      (tail.mapIncidence vertices edges h)

@[simp] theorem edges_mapIncidence (vertices : V → W) (edges : E → F)
    (h : ∀ x e, inc x e → inc' (vertices x) (edges e))
    {s t : V} (w : HWalk inc s t) :
    (w.mapIncidence vertices edges h).edges = w.edges.map edges := by
  induction w with
  | nil => rfl
  | cons e hx hy tail ih => exact congrArg (List.cons (edges e)) ih
end FiniteFlow.Hypergraph.HWalk

namespace FiniteFlow.Hypergraph
variable {V E F : Type*} {old : V → E → Prop} {inserted : V → F → Prop}

/-- Collapse all new interior vertices to one actual vertex of the removed
edge. Old names are fixed. This sends every inserted edge to the removed ID. -/
noncomputable def replacementRetract (O : Set V) (anchor : V) (x : V) : V := by
  classical
  exact if x ∈ O then x else anchor

def replacementEdgeRetract (removed : E) : ({e : E // e ≠ removed} ⊕ F) → E
  | .inl e => e.val
  | .inr _ => removed

theorem replacementRetract_incidence (removed : E) (O K : Set V) (anchor : V)
    (ha : old anchor removed)
    (old_support : ∀ x e, old x e → x ∈ O)
    (new_support : ∀ x f, inserted x f → x ∈ K)
    (overlap : ∀ x, x ∈ O → x ∈ K → old x removed)
    (x : V) (e : {e : E // e ≠ removed} ⊕ F)
    (h : ReplacementIncidence old inserted removed x e) :
    old (replacementRetract O anchor x) (replacementEdgeRetract removed e) := by
  classical
  cases e with
  | inl e =>
    have hx := old_support x e.val h
    simpa only [replacementRetract,ite_eq_left hx,replacementEdgeRetract, ReplacementIncidence] using h
  | inr f =>
    by_cases hx : x ∈ O
    · simpa only [replacementRetract,ite_eq_left hx,replacementEdgeRetract] using
        overlap x hx (new_support x f h)
    · simpa only [replacementRetract,ite_eq_right hx,replacementEdgeRetract] using ha

/-- A projected walk uses a surviving old ID exactly when the original
replacement walk uses its tagged surviving ID. New edges cannot create it. -/
theorem replacementEdgeRetract_mem (removed : E)
    (es : List ({e : E // e ≠ removed} ⊕ F)) (f : {e : E // e ≠ removed}) :
    f.val ∈ es.map (replacementEdgeRetract removed) ↔ Sum.inl f ∈ es := by
  simp only [List.mem_map]
  constructor
  · rintro ⟨e,he,h⟩
    cases e with
    | inl e =>
      have heq : e = f := Subtype.ext h
      exact heq ▸ he
    | inr e => exact (f.property h.symm).elim
  · intro h
    exact ⟨.inl f,h,rfl⟩

/-- Every surviving old cutedge remains unavoidable after replacement. The
intersection condition is used through an actual incidence retraction. -/
theorem old_cutedge_replacement (removed : E) (O K : Set V) (anchor : V)
    (ha : old anchor removed)
    (old_support : ∀ x e, old x e → x ∈ O)
    (new_support : ∀ x f, inserted x f → x ∈ K)
    (overlap : ∀ x, x ∈ O → x ∈ K → old x removed)
    {s t : V} (hs : s ∈ O) (ht : t ∈ O)
    (f : {e : E // e ≠ removed}) (hf : Cutedge old s t f.val) :
    Cutedge (ReplacementIncidence old inserted removed) s t (.inl f) := by
  classical
  intro p
  let w := p.walk.mapIncidence (inc' := old) (replacementRetract O anchor)
    (replacementEdgeRetract removed)
    (replacementRetract_incidence removed O K anchor ha old_support new_support overlap)
  have hfr : Cutedge old (replacementRetract O anchor s) (replacementRetract O anchor t) f.val := by
    simpa only [replacementRetract,ite_eq_left hs,ite_eq_left ht] using hf
  have hm := (cutedge_iff_every_walk _ _ _ _).mp hfr w
  have hm' : f.val ∈ p.walk.edges.map (replacementEdgeRetract removed) := by
    simpa only [w,HWalk.edges_mapIncidence] using hm
  exact (replacementEdgeRetract_mem removed p.walk.edges f).mp hm'

/-- Exact preservation of all surviving old cutedges. The forward lift also
requires connectedness of the inserted hypergraph along the removed edge. -/
theorem replacement_old_cutedge_iff (removed : E) (O K : Set V) (anchor : V)
    (ha : old anchor removed)
    (old_support : ∀ x e, old x e → x ∈ O)
    (new_support : ∀ x f, inserted x f → x ∈ K)
    (overlap : ∀ x, x ∈ O → x ∈ K → old x removed)
    (connected : ∀ a b, old a removed → old b removed → Nonempty (HWalk inserted a b))
    {s t : V} (hs : s ∈ O) (ht : t ∈ O) (f : {e : E // e ≠ removed}) :
    Cutedge (ReplacementIncidence old inserted removed) s t (.inl f) ↔
      Cutedge old s t f.val :=
  ⟨replacement_cutedge_old_implies removed connected f,
    old_cutedge_replacement removed O K anchor ha old_support new_support overlap hs ht f⟩

end FiniteFlow.Hypergraph
