import ThinnessEdgeTransport
import SupportedReplacementThinness

namespace FiniteFlow.Hypergraph
variable {V E : Type*}

def ActiveEdge (inc : V → E → Prop) := {e : E // ∃ x, inc x e}
def ActiveIncidence (inc : V → E → Prop) (x : V) (e : ActiveEdge inc) : Prop := inc x e.val

/-- Exact replacement relabeling for active edge identifiers. Its hypotheses
are incidence equalities and disjoint actual edge origins, not output paths,
components, thinness, or decomposition existence. -/
noncomputable def activeReplacementEquiv
    (old inserted target : V → E → Prop) (removed : ActiveEdge old)
    (step : ∀ x e, target x e ↔ (old x e ∧ e ≠ removed.val) ∨ inserted x e)
    (disjoint : ∀ x y e, old x e → inserted y e → False) :
    IncidenceEquiv (ReplacementIncidence (ActiveIncidence old) (ActiveIncidence inserted) removed)
      (ActiveIncidence target) := by
  classical
  let raw : ({e : ActiveEdge old // e ≠ removed} ⊕ ActiveEdge inserted) → E :=
    fun e => match e with | .inl e => e.val.val | .inr e => e.val
  have raw_ne : ∀ e : {e : ActiveEdge old // e ≠ removed}, e.val.val ≠ removed.val := by
    intro e he
    exact e.property (Subtype.ext he)
  have active : ∀ e, ∃ x, target x (raw e) := by
    intro e
    cases e with
    | inl e =>
      obtain ⟨x,hx⟩ := e.val.property
      exact ⟨x,(step x _).mpr (Or.inl ⟨hx,raw_ne e⟩)⟩
    | inr e =>
      obtain ⟨x,hx⟩ := e.property
      exact ⟨x,(step x _).mpr (Or.inr hx)⟩
  let f := fun e => (⟨raw e,active e⟩ : ActiveEdge target)
  have inj : Function.Injective f := by
    intro a b hab
    have he := congrArg Subtype.val hab
    cases a with
    | inl a =>
      cases b with
      | inl b =>
        apply congrArg Sum.inl
        apply Subtype.ext
        exact Subtype.ext he
      | inr b =>
        obtain ⟨x,hx⟩ := a.val.property
        obtain ⟨y,hy⟩ := b.property
        exact (disjoint x y a.val.val hx (he.symm ▸ hy)).elim
    | inr a =>
      cases b with
      | inl b =>
        obtain ⟨x,hx⟩ := b.val.property
        obtain ⟨y,hy⟩ := a.property
        exact (disjoint x y b.val.val hx (he ▸ hy)).elim
      | inr b => exact congrArg Sum.inr (Subtype.ext he)
  have surj : Function.Surjective f := by
    intro e
    obtain ⟨x,hx⟩ := e.property
    rcases (step x e.val).mp hx with ⟨hold,hne⟩ | hnew
    · let a : ActiveEdge old := ⟨e.val,⟨x,hold⟩⟩
      have ha : a ≠ removed := fun h => hne (congrArg Subtype.val h)
      exact ⟨.inl ⟨a,ha⟩,Subtype.ext rfl⟩
    · exact ⟨.inr ⟨e.val,⟨x,hnew⟩⟩,Subtype.ext rfl⟩
  refine ⟨Equiv.ofBijective f ⟨inj,surj⟩,?_⟩
  intro x e
  cases e with
  | inl e =>
    change target x e.val.val ↔ old x e.val.val
    constructor
    · intro hx
      rcases (step x e.val.val).mp hx with ⟨hold,_⟩ | hnew
      · exact hold
      · obtain ⟨y,hy⟩ := e.val.property
        exact (disjoint y x e.val.val hy hnew).elim
    · intro hx
      exact (step x e.val.val).mpr (Or.inl ⟨hx,raw_ne e⟩)
  | inr e =>
    change target x e.val ↔ inserted x e.val
    constructor
    · intro hx
      rcases (step x e.val).mp hx with ⟨hold,_⟩ | hnew
      · obtain ⟨y,hy⟩ := e.property
        exact (disjoint x y e.val hold hy).elim
      · exact hnew
    · intro hx
      exact (step x e.val).mpr (Or.inr hx)

end FiniteFlow.Hypergraph
