import RealizedGuidedDecomposition
import ForestDisjointUnion
import GuidanceMSO

/-!
Generic incidence transport for genuine original-edge forests. A marginal
incidence structure is not assumed to be a SparseEndpointMSO.Model.
Its actual edge identifiers may be arbitrary, including separately retained
identifiers with equal endpoint pairs. Simple-graph transport ignores only
parallel adjacency witnesses; no code equality is quotiented.
-/
namespace StackSorting.GuidedPathwidth.GenericIncidence
open SparseEndpointMSO SparseEndpointMSO.FiniteCopy SparseEndpointMSO.IncidenceOwnership
variable {V : Type} {G : SimpleGraph V} {P : Set V}

/-- Exact endpoint interface for an actual incidence graph. Coverage concerns
all edges of the displayed graph, including marginal clique-completion edges. -/
structure System (G : SimpleGraph V) where
  Edge : Type
  left : Edge → V
  right : Edge → V
  sound : ∀ e, G.Adj (left e) (right e)
  complete : ∀ {u v}, G.Adj u v →
    ∃ e, (left e=u ∧ right e=v) ∨ (left e=v ∧ right e=u)

namespace System
variable (S : System G)
abbrev Element := V ⊕ S.Edge
abbrev IncSet := S.Element → Prop

def isVertex : S.Element → Prop
  | .inl _ => True | .inr _ => False

def isEdge : S.Element → Prop
  | .inl _ => False | .inr _ => True

def incident : S.Element → S.Element → Prop
  | .inl u, .inr e => u=S.left e ∨ u=S.right e
  | _, _ => False

/-- Existing incidence syntax can be evaluated on this carrier directly.
The unused sparse insertion/removal predicates are false; local guidance
formulas use only vertex, edge and incidence. -/
def atoms : {r : Nat} → IncidenceAtom r → (Fin r → S.Element) → Prop
  | _, .vertex, env => S.isVertex (env 0)
  | _, .edge, env => S.isEdge (env 0)
  | _, .incidence, env => S.incident (env 0) (env 1)
  | _, .insert, _ => False
  | _, .remove, _ => False

def step (X F : S.IncSet) (u v : S.Element) : Prop :=
  S.isVertex u ∧ X u ∧ S.isVertex v ∧ X v ∧ u≠v ∧
    ∃ e, S.isEdge e ∧ F e ∧ S.incident u e ∧ S.incident v e

theorem step_symm {X F : S.IncSet} {u v : S.Element} (h : S.step X F u v) :
    S.step X F v u := by
  rcases h with ⟨hu,hX,hv,hY,hn,e,he,hF,hi,hj⟩
  exact ⟨hv,hY,hu,hX,hn.symm,e,he,hF,hj,hi⟩

def selectedGraph (X F : S.IncSet) : SimpleGraph S.Element where
  Adj := S.step X F
  symm := ⟨fun _ _ h => S.step_symm h⟩
  loopless := ⟨fun _ h => h.2.2.2.2.1 rfl⟩

def rootRelation (X F R : S.IncSet) (u r : S.Element) : Prop :=
  R r ∧ X u ∧ X r ∧ (S.selectedGraph X F).Reachable u r

structure Typed (X F R : S.IncSet) : Prop where
  vertices : ∀ u, X u → S.isVertex u
  edges : ∀ e, F e → S.isEdge e
  roots : ∀ r, R r → X r
  endpoints : ∀ e u, F e → S.incident u e → X u

structure ColorData where
  vertices : S.IncSet
  edges : S.IncSet
  roots : S.IncSet

def ColorData.Valid (C : S.ColorData) : Prop :=
  S.Typed C.vertices C.edges C.roots ∧
  (∀ u, C.vertices u → ∃! r, S.rootRelation C.vertices C.edges C.roots u r) ∧
  (S.selectedGraph C.vertices C.edges).IsAcyclic

/-- X and R contain only actual vertices. F consists only of actual edge IDs
whose two endpoints are adjacent in the supplied actual forest. -/
def colorData (C : RootedColor G P) : S.ColorData where
  vertices := fun a => match a with
    | .inl v => v ∈ C.selected | .inr _ => False
  edges := fun a => match a with
    | .inl _ => False | .inr e => C.graph.Adj (S.left e) (S.right e)
  roots := fun a => match a with
    | .inl v => v ∈ C.roots | .inr _ => False

theorem color_typed (C : RootedColor G P) :
    S.Typed (S.colorData C).vertices (S.colorData C).edges (S.colorData C).roots := by
  constructor
  · intro a ha
    cases a with
    | inl v => trivial
    | inr e => exact ha.elim
  · intro a ha
    cases a with
    | inl v => exact ha.elim
    | inr e => trivial
  · intro a ha
    cases a with
    | inl v => exact C.rootSelected ha
    | inr e => exact ha.elim
  · intro e a he ha
    cases e with
    | inl v => exact he.elim
    | inr e => cases a with
      | inr f => exact ha.elim
      | inl v =>
        rcases ha with h | h
        · exact h.symm ▸ (C.edgeSelected he).1
        · exact h.symm ▸ (C.edgeSelected he).2

/-- Exact adjacency transport. Edge IDs are kept, including duplicates; the
ordinary selected simple graph has exactly the original forest adjacency. -/
theorem selected_step_iff (C : RootedColor G P) (x y : V) :
    S.step (S.colorData C).vertices (S.colorData C).edges (.inl x) (.inl y) ↔
      C.graph.Adj x y := by
  constructor
  · rintro ⟨_,_,_,_,hne,e,he,hF,hi,hj⟩
    cases e with
    | inl v => exact he.elim
    | inr e =>
      rcases hi with rfl | rfl <;> rcases hj with rfl | rfl
      · exact False.elim (hne rfl)
      · exact hF
      · exact hF.symm
      · exact False.elim (hne rfl)
  · intro hxy
    obtain ⟨e,he⟩ := S.complete (C.subgraph hxy)
    refine ⟨trivial,(C.edgeSelected hxy).1,trivial,(C.edgeSelected hxy).2,
      ?_,.inr e,trivial,?_,?_,?_⟩
    · intro h
      exact hxy.ne (Sum.inl.inj h)
    · rcases he with ⟨hl,hr⟩ | ⟨hl,hr⟩
      · change C.graph.Adj (S.left e) (S.right e)
        rw [hl,hr]
        exact hxy
      · change C.graph.Adj (S.left e) (S.right e)
        rw [hl,hr]
        exact hxy.symm
    · rcases he with ⟨hl,_⟩ | ⟨_,hr⟩
      · exact Or.inl hl.symm
      · exact Or.inr hr.symm
    · rcases he with ⟨_,hr⟩ | ⟨hl,_⟩
      · exact Or.inr hr.symm
      · exact Or.inl hl.symm

theorem selectedGraph_exact (C : RootedColor G P) :
    S.selectedGraph (S.colorData C).vertices (S.colorData C).edges =
      C.graph ⊕g (⊥ : SimpleGraph S.Edge) := by
  ext a b
  cases a with
  | inl x => cases b with
    | inl y => exact S.selected_step_iff C x y
    | inr e => simp [selectedGraph,step,isVertex]
  | inr e => cases b <;> simp [selectedGraph,step,isVertex]

theorem selected_acyclic (C : RootedColor G P) :
    (S.selectedGraph (S.colorData C).vertices (S.colorData C).edges).IsAcyclic := by
  rw [S.selectedGraph_exact C]
  exact sumForest_acyclic C.acyclic SimpleGraph.isAcyclic_bot

private theorem sum_empty_reachable_iff {W : Type} (H : SimpleGraph V) (x y : V) :
    (H ⊕g (⊥ : SimpleGraph W)).Reachable (.inl x) (.inl y) ↔ H.Reachable x y := by
  constructor
  · rintro ⟨w⟩
    let f : (H ⊕g (⊥ : SimpleGraph W)) →g H := {
      toFun := Sum.elim id (fun _ => x)
      map_rel' := by intro a b h; cases a <;> cases b <;> simp_all }
    exact ⟨w.map f⟩
  · intro h
    exact h.map (SimpleGraph.Embedding.sumInl (H := (⊥ : SimpleGraph W))).toHom

theorem rootRelation_iff (C : RootedColor G P) (x r : V) :
    S.rootRelation (S.colorData C).vertices (S.colorData C).edges
      (S.colorData C).roots (.inl x) (.inl r) ↔
    r ∈ C.roots ∧ x ∈ C.selected ∧ r ∈ C.selected ∧ C.graph.Reachable x r := by
  unfold rootRelation
  rw [S.selectedGraph_exact C,sum_empty_reachable_iff]
  rfl

theorem color_valid (C : RootedColor G P) : (S.colorData C).Valid := by
  refine ⟨S.color_typed C,?_,S.selected_acyclic C⟩
  intro a ha
  cases a with
  | inr e => exact ha.elim
  | inl x =>
    obtain ⟨r,hr,hu⟩ := C.uniqueRoot x ha
    refine ⟨.inl r,(S.rootRelation_iff C x r).mpr
      ⟨hr.1,ha,C.rootSelected hr.1,hr.2⟩,?_⟩
    intro b hb
    cases b with
    | inr e => exact hb.1.elim
    | inl y =>
      have hh := (S.rootRelation_iff C x y).mp hb
      exact congrArg Sum.inl (hu y ⟨hh.1,hh.2.2.2⟩)

/-- Exactly three actual incidence sets per forest color. -/
def parameters {c : Nat} (C : Fin c → RootedColor G P) :
    (Fin c × Fin 3) → S.IncSet := fun ij =>
  Fin.cases (S.colorData (C ij.1)).vertices
    (Fin.cases (S.colorData (C ij.1)).edges
      (fun _ => (S.colorData (C ij.1)).roots)) ij.2

theorem capture_to_incidence {c : Nat} (C : Fin c → RootedColor G P)
    {B : Set V} (hB : ForestCaptures C B) :
    B.Nonempty → ∃ z : S.Element, ∀ r ∈ B, ∃ i,
      S.rootRelation (S.colorData (C i)).vertices (S.colorData (C i)).edges
        (S.colorData (C i)).roots z (.inl r) := by
  intro hb
  obtain ⟨x,hx⟩ := hB hb
  refine ⟨.inl x,?_⟩
  intro r hr
  obtain ⟨i,hi⟩ := hx r hr
  exact ⟨i,(S.rootRelation_iff (C i) x r).mpr hi⟩

end System
#print axioms System.selected_step_iff
#print axioms System.selectedGraph_exact
#print axioms System.color_valid
#print axioms System.capture_to_incidence
end StackSorting.GuidedPathwidth.GenericIncidence
