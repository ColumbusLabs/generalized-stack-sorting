import SparseIncidenceRealization
import Mathlib.Combinatorics.SimpleGraph.Acyclic

/-! One color of guidance is represented by three actual incidence sets. No
bounded-width existence theorem is assumed. Acyclicity and root uniqueness are
separate conditions: uniqueness only requires one marked root per component. -/
namespace StackSorting.SparseEndpointMSO.Guidance
open IncidenceOwnership

variable {D : Model}
abbrev IncSet (D : Model) := IncidenceOwnership.Element D → Prop

/-- Selected edges are interpreted as an undirected simple graph. Both ends
must be distinct selected actual vertices. -/
def Step (X F : IncSet D) (u v : IncidenceOwnership.Element D) : Prop :=
  IsVertex u ∧ X u ∧ IsVertex v ∧ X v ∧ u ≠ v ∧
    ∃ e, IsEdge e ∧ F e ∧ ElementIncident u e ∧ ElementIncident v e

theorem step_symm {X F : IncSet D} {u v : IncidenceOwnership.Element D}
    (h : Step X F u v) : Step X F v u := by
  rcases h with ⟨hu, hX, hv, hY, hn, e, he, hF, hi, hj⟩
  exact ⟨hv, hY, hu, hX, Ne.symm hn, e, he, hF, hj, hi⟩

def selectedGraph (X F : IncSet D) : SimpleGraph (IncidenceOwnership.Element D) where
  Adj := Step X F
  symm := ⟨fun _ _ h => step_symm h⟩
  loopless := ⟨fun _ h => h.2.2.2.2.1 rfl⟩

/-- Optional deletion of one undirected pair, used only by forest validation. -/
def PairAllowed {α : Type} (cut : Option (α × α)) (u v : α) : Prop :=
  match cut with
  | none => True
  | some (a, b) => ¬ ((u = a ∧ v = b) ∨ (u = b ∧ v = a))

def filteredGraph (X F : IncSet D) (cut : Option (IncidenceOwnership.Element D ×
    IncidenceOwnership.Element D)) : SimpleGraph (IncidenceOwnership.Element D) where
  Adj u v := Step X F u v ∧ PairAllowed cut u v
  symm := ⟨by
    intro u v h
    refine ⟨step_symm h.1, ?_⟩
    cases cut with
    | none => trivial
    | some p =>
      rcases p with ⟨a, b⟩
      rintro (⟨ha, hb⟩ | ⟨ha, hb⟩)
      · exact h.2 (Or.inr ⟨hb, ha⟩)
      · exact h.2 (Or.inl ⟨hb, ha⟩)⟩
  loopless := ⟨fun _ h => h.1.2.2.2.2.1 rfl⟩

@[simp] theorem filteredGraph_none (X F : IncSet D) :
    filteredGraph X F none = selectedGraph X F := by
  ext u v
  simp [filteredGraph, selectedGraph, PairAllowed]

theorem filteredGraph_pair (X F : IncSet D) (a b : IncidenceOwnership.Element D) :
    filteredGraph X F (some (a, b)) = (selectedGraph X F).deleteEdges {s(a, b)} := by
  ext u v
  simp [filteredGraph, selectedGraph, PairAllowed]

/-- The usual all-closed-subsets definition, with no oracle connectivity atom. -/
def ClosedReach {α : Type} (A : α → α → Prop) (u v : α) : Prop :=
  ∀ Z : α → Prop, Z u → (∀ x y, A x y → Z x → Z y) → Z v

/-- Connectivity is exactly the existence of an ordinary finite graph walk,
including the length-zero walk. No finiteness hypothesis is needed here. -/
theorem closedReach_iff_walk {α : Type} (G : SimpleGraph α) (u v : α) :
    ClosedReach G.Adj u v ↔ Nonempty (G.Walk u v) := by
  constructor
  · intro h
    exact h (fun w => G.Reachable u w) (SimpleGraph.Reachable.refl u)
      (fun _ _ ha hr => hr.trans ha.reachable)
  · rintro ⟨w⟩ Z hu hc
    revert hu
    induction w with
    | nil => exact fun h => h
    | @cons a b c hab w ih => exact fun h => ih (hc a b hab h)

/-- Membership guards are essential: an unselected isolated vertex does not
belong to a selected component merely because it has a length-zero walk. -/
def Connected (X F : IncSet D) (cut : Option (IncidenceOwnership.Element D ×
    IncidenceOwnership.Element D)) (u v : IncidenceOwnership.Element D) : Prop :=
  X u ∧ X v ∧ Nonempty ((filteredGraph X F cut).Walk u v)

def RootRelation (X F R : IncSet D) (u r : IncidenceOwnership.Element D) : Prop :=
  R r ∧ Connected X F none u r

/-- Sort, subset, and endpoint validation on the actual incidence universe. -/
structure Typed (X F R : IncSet D) : Prop where
  vertices : ∀ u, X u → IsVertex u
  edges : ∀ e, F e → IsEdge e
  roots : ∀ r, R r → X r
  endpoints : ∀ e u, F e → ElementIncident u e → X u

/-- Exactly one marked root in each selected connected component. -/
def Rooted (X F R : IncSet D) : Prop :=
  Typed X F R ∧ ∀ u, X u → ∃! r, RootRelation X F R u r

/-- Standard graph acyclicity, separated from the root relation. -/
def Forest (X F R : IncSet D) : Prop :=
  Rooted X F R ∧ (selectedGraph X F).IsAcyclic

theorem root_exists_unique {X F R : IncSet D} (h : Rooted X F R)
    {u : IncidenceOwnership.Element D} (hu : X u) : ∃! r, RootRelation X F R u r :=
  h.2 u hu

theorem root_unique {X F R : IncSet D} (h : Rooted X F R)
    {u r s : IncidenceOwnership.Element D}
    (hr : RootRelation X F R u r) (hs : RootRelation X F R u s) : r = s := by
  obtain ⟨t, _, ht⟩ := h.2 u hr.2.1
  exact (ht r hr).trans (ht s hs).symm

theorem root_refl {X F R : IncSet D} (h : Typed X F R)
    {r : IncidenceOwnership.Element D} (hr : R r) : RootRelation X F R r r :=
  ⟨hr, h.roots r hr, h.roots r hr, ⟨.nil⟩⟩

theorem root_refl_iff {X F R : IncSet D} (h : Typed X F R)
    (r : IncidenceOwnership.Element D) : RootRelation X F R r r ↔ R r :=
  ⟨fun hh => hh.1, root_refl h⟩

theorem root_component {X F R : IncSet D} {u v r : IncidenceOwnership.Element D}
    (huv : Connected X F none u v) (hvr : RootRelation X F R v r) :
    RootRelation X F R u r :=
  ⟨hvr.1, huv.1, hvr.2.2.1, SimpleGraph.Reachable.trans huv.2.2 hvr.2.2.2⟩

theorem root_outside {X F R : IncSet D} {u r : IncidenceOwnership.Element D}
    (hu : ¬ X u) : ¬ RootRelation X F R u r := fun h => hu h.2.1

/-- Fixed finite colors are a product; no cross-color disjointness is required. -/
structure ColorData (D : Model) where
  vertices : IncSet D
  edges : IncSet D
  roots : IncSet D

def ColorData.Valid (C : ColorData D) : Prop := Forest C.vertices C.edges C.roots
abbrev Colors (D : Model) (k : Nat) := Fin k → ColorData D
def Colors.Valid (C : Colors D k) : Prop := ∀ i, (C i).Valid

theorem colors_root_unique {k : Nat} {C : Colors D k} (h : C.Valid) (i : Fin k)
    {u r s : IncidenceOwnership.Element D}
    (hr : RootRelation (C i).vertices (C i).edges (C i).roots u r)
    (hs : RootRelation (C i).vertices (C i).edges (C i).roots u s) : r = s :=
  root_unique (h i).1 hr hs

end StackSorting.SparseEndpointMSO.Guidance
