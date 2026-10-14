import MultiMarginDecoding
import MultiMarginSyntax

set_option backward.isDefEq.respectTransparency false

namespace StackSorting.GraphWidth.MultiMargin
open FinitePort Nested
variable {n t : Nat} {G : Graph n} {T : RootedTree t} {D : Decomposition G T}

/-- Pointwise completed-incidence interface, to be discharged on the explicit
original-incidence plus selected extra-edge carrier. These are local endpoint
and edge-coverage laws, not a whole-formula or decomposition oracle. -/
structure CompletedIncidence (D : Decomposition G T) (α : Type) where
  rel : Syntax.Relations α
  vertex : Fin n → α
  injective : Function.Injective vertex
  vertex_exact : ∀ z, rel.vertex z ↔ ∃ v, z=vertex v
  incidence_vertex : ∀ u e, rel.incidence u e → rel.vertex u
  completed_pair : ∀ u v, u≠v →
    ((Completion D).Adj u v ↔ ∃ e, rel.edge e ∧ rel.incidence (vertex u) e ∧ rel.incidence (vertex v) e)
  original_pair : ∀ u v,
    Syntax.OriginalAdjacent rel (vertex u) (vertex v) ↔ G.Adj u v
  rigid : ∀ e u v a b, rel.edge e → u≠v → a≠b →
    rel.incidence (vertex u) e → rel.incidence (vertex v) e →
    rel.incidence (vertex a) e → rel.incidence (vertex b) e →
    (u=a ∧ v=b) ∨ (u=b ∧ v=a)

def Lift {α : Type} (f : Fin n → α) (E : Fin n → Fin n → Prop) (x y : α) : Prop :=
  ∃ u v, x=f u ∧ y=f v ∧ E u v

/-- All selected-link walks stay on the original vertex embedding, including
length-zero walks and vertex-deletion predicates. -/
theorem lift_walk_iff {α : Type} (f : Fin n → α) (hf : Function.Injective f)
    (E : Fin n → Fin n → Prop) (P : α → Prop) (u v : Fin n) :
    Walk (Lift f E) P (f u) (f v) ↔ Walk E (fun z => P (f z)) u v := by
  constructor
  · have descend : ∀ {x y}, Walk (Lift f E) P x y →
        ∀ a b, x=f a → y=f b → Walk E (fun z => P (f z)) a b := by
      intro x y w
      induction w with
      | refl hp =>
        intro a b ha hb
        have he : a=b := hf (ha.symm.trans hb)
        subst b
        exact .refl (ha ▸ hp)
      | @step x z y hp hxz tail ih =>
        intro a b ha hb
        obtain ⟨c,d,hxc,hzd,hcd⟩ := hxz
        have he : c=a := hf (hxc.symm.trans ha)
        subst c
        exact .step (ha ▸ hp) hcd (ih d b hzd hb)
    exact fun w => descend w u v rfl rfl
  · intro w
    induction w with
    | refl hp => exact .refl hp
    | step hp he _ ih => exact .step hp ⟨_,_,rfl,rfl,he⟩ ih

namespace CompletedIncidence
variable {α : Type} (H : CompletedIncidence D α)

def edgeSet (E : Fin n → Fin n → Prop) : α → Prop :=
  fun e => H.rel.edge e ∧ ∃ u v, E u v ∧ H.rel.incidence (H.vertex u) e ∧ H.rel.incidence (H.vertex v) e

theorem edgeSet_exact (E : Fin n → Fin n → Prop)
    (hs : ∀ {u v}, E u v → E v u) (hl : ∀ u, ¬ E u u)
    (ha : ∀ {u v}, E u v → (Completion D).Adj u v) (x y : α) :
    (H.rel.vertex x ∧ H.rel.vertex y ∧ x≠y ∧ ∃ e, H.rel.edge e ∧ H.edgeSet E e ∧
      H.rel.incidence x e ∧ H.rel.incidence y e) ↔ Lift H.vertex E x y := by
  have ene : ∀ {u v}, E u v → u≠v := by intro u v h he; subst v; exact hl u h
  constructor
  · rintro ⟨hx,hy,hne,e,he,⟨_,u,v,huv,hu,hv⟩,hx',hy'⟩
    obtain ⟨a,rfl⟩ := (H.vertex_exact x).mp hx
    obtain ⟨b,rfl⟩ := (H.vertex_exact y).mp hy
    have hab : a≠b := fun eq => hne (congrArg H.vertex eq)
    rcases H.rigid e a b u v he hab (ene huv) hx' hy' hu hv with ⟨ha,hb⟩ | ⟨ha,hb⟩
    · exact ⟨a,b,rfl,rfl,ha.symm ▸ hb.symm ▸ huv⟩
    · exact ⟨a,b,rfl,rfl,ha.symm ▸ hb.symm ▸ hs huv⟩
  · rintro ⟨u,v,rfl,rfl,he⟩
    obtain ⟨e,hedge,hu,hv⟩ := (H.completed_pair u v (ene he)).mp (ha he)
    exact ⟨(H.vertex_exact _).mpr ⟨u,rfl⟩,(H.vertex_exact _).mpr ⟨v,rfl⟩,
      fun eq => ene he (H.injective eq),e,hedge,⟨hedge,u,v,he,hu,hv⟩,hu,hv⟩

variable (s : Sane D) (ht : 0<t)

noncomputable def rootVertex : Fin n := Encoding.vertex s ht (substitution s ht).root

def parameters : Fin 4 → α → Prop :=
  Fin.cases (H.edgeSet (Encoding.M s ht))
    (Fin.cases (H.edgeSet (Encoding.K s))
      (Fin.cases (fun z => z=H.vertex (rootVertex s ht))
        (fun _ z => ∃ x, z=H.vertex (entry s x))))

def selected : Syntax.Channel → Fin n → Fin n → Prop
  | .marginal => Encoding.M s ht
  | .crossing => Encoding.K s
  | .union => Encoding.Union s ht

theorem selected_completed (c : Syntax.Channel) {u v} (h : selected s ht c u v) :
    (Completion D).Adj u v := by
  cases c with
  | marginal => exact Encoding.M_completed s ht h
  | crossing => exact Encoding.K_completed s h
  | union => exact h.elim (Encoding.M_completed s ht) (Encoding.K_completed s)

theorem selected_symm (c : Syntax.Channel) {u v} (h : selected s ht c u v) :
    selected s ht c v u := by
  cases c with
  | marginal => exact Encoding.M_symm s ht h
  | crossing => exact Encoding.K_symm s h
  | union =>
    exact h.elim (fun h => Or.inl (Encoding.M_symm s ht h))
      (fun h => Or.inr (Encoding.K_symm s h))

theorem selected_loopless (c : Syntax.Channel) (u : Fin n) : ¬ selected s ht c u u :=
  fun h => (Completion D).loopless u (selected_completed s ht c h)

@[simp] theorem selected_parameter (c : Syntax.Channel) (e : α) :
    Syntax.Selected Syntax.fixed (H.parameters s ht) c e ↔ H.edgeSet (selected s ht c) e := by
  cases c with
  | marginal => rfl
  | crossing => rfl
  | union =>
    change (H.edgeSet (Encoding.M s ht) e ∨ H.edgeSet (Encoding.K s) e) ↔ H.edgeSet (Encoding.Union s ht) e
    simp only [edgeSet,Encoding.Union]
    constructor
    · rintro (⟨he,u,v,h,hu,hv⟩ | ⟨he,u,v,h,hu,hv⟩)
      · exact ⟨he,u,v,Or.inl h,hu,hv⟩
      · exact ⟨he,u,v,Or.inr h,hu,hv⟩
    · rintro ⟨he,u,v,h | h,hu,hv⟩
      · exact Or.inl ⟨he,u,v,h,hu,hv⟩
      · exact Or.inr ⟨he,u,v,h,hu,hv⟩

theorem link_exact (c : Syntax.Channel) (x y : α) :
    Syntax.Link H.rel Syntax.fixed (H.parameters s ht) c x y ↔ Lift H.vertex (selected s ht c) x y := by
  unfold Syntax.Link
  simp only [selected_parameter]
  exact H.edgeSet_exact _ (fun {u v} h => selected_symm s ht c (u := u) (v := v) h)
    (selected_loopless s ht c) (fun {u v} h => selected_completed s ht c (u := u) (v := v) h) x y

theorem connected_exact (c : Syntax.Channel) (cut : Option (Fin n)) (u v : Fin n) :
    Syntax.Connected H.rel Syntax.fixed (H.parameters s ht) c (cut.map H.vertex) (H.vertex u) (H.vertex v) ↔
      Walk (selected s ht c) (ConnectedConeNormalization.Avoid cut) u v := by
  have hl : Syntax.Link H.rel Syntax.fixed (H.parameters s ht) c=Lift H.vertex (selected s ht c) :=
    funext (fun x => funext (fun y => propext (H.link_exact s ht c x y)))
  unfold Syntax.Connected
  rw [hl,lift_walk_iff H.vertex H.injective]
  have hx := (H.vertex_exact (H.vertex u)).mpr ⟨u,rfl⟩
  have hy := (H.vertex_exact (H.vertex v)).mpr ⟨v,rfl⟩
  simp only [hx,hy,true_and]
  have hp : (fun z => ConnectedConeNormalization.Avoid (cut.map H.vertex) (H.vertex z))=
      ConnectedConeNormalization.Avoid cut := by
    funext z
    cases cut with
    | none => rfl
    | some x =>
      apply propext
      exact not_congr ⟨fun h => H.injective h,congrArg H.vertex⟩
  rw [hp]

#print axioms edgeSet_exact
#print axioms link_exact
#print axioms connected_exact
end CompletedIncidence
end StackSorting.GraphWidth.MultiMargin
