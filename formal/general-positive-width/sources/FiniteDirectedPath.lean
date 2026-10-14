import Mathlib.Data.List.Nodup
import Mathlib.Logic.Relation

/-! Directed walks, simple paths and arc-preserving loop erasure. -/
namespace FiniteFlow

universe u
variable {V : Type u} {R : V → V → Prop}

inductive DWalk (R : V → V → Prop) : V → V → Type u
  | nil (s : V) : DWalk R s s
  | cons {s a t : V} (edge : R s a) (tail : DWalk R a t) : DWalk R s t

namespace DWalk

def vertices {s t} : DWalk R s t → List V
  | .nil s => [s]
  | .cons (s := s) _ p => s :: p.vertices

def Uses {s t} : DWalk R s t → V → V → Prop
  | .nil _, _, _ => False
  | .cons (s := s) (a := a) _ p, x, y => (x = s ∧ y = a) ∨ p.Uses x y

@[simp] theorem start_mem {s t} (p : DWalk R s t) : s ∈ p.vertices := by
  cases p <;> simp [vertices]

@[simp] theorem end_mem {s t} (p : DWalk R s t) : t ∈ p.vertices := by
  induction p with
  | nil => simp [vertices]
  | cons _ _ ih => exact List.mem_cons_of_mem _ ih

theorem uses_relation {s t} (p : DWalk R s t) {x y} (h : p.Uses x y) : R x y := by
  induction p with
  | nil => exact False.elim h
  | cons edge _ ih =>
    rcases h with ⟨rfl, rfl⟩ | h
    · exact edge
    · exact ih h

theorem uses_vertices {s t} (p : DWalk R s t) {x y} (h : p.Uses x y) :
    x ∈ p.vertices ∧ y ∈ p.vertices := by
  induction p with
  | nil => exact False.elim h
  | cons edge q ih =>
    rcases h with ⟨rfl, rfl⟩ | h
    · exact ⟨by simp [vertices], List.mem_cons_of_mem _ q.start_mem⟩
    · exact ⟨List.mem_cons_of_mem _ (ih h).1, List.mem_cons_of_mem _ (ih h).2⟩

theorem to_reachable {s t} (p : DWalk R s t) : Relation.ReflTransGen R s t := by
  induction p with
  | nil => exact .refl
  | cons edge _ ih => exact ih.head edge

/-- A suffix of a simple path is simple and uses only its original arcs. -/
theorem suffix {s t} (p : DWalk R s t) (hp : p.vertices.Nodup)
    {x} (hx : x ∈ p.vertices) :
    ∃ q : DWalk R x t, q.vertices.Nodup ∧ (∀ a b, q.Uses a b → p.Uses a b) := by
  induction p with
  | nil s =>
    have hxs : x = s := by simpa [vertices] using hx
    subst x
    exact ⟨.nil s, by simp [vertices], by intro a b h; exact h⟩
  | @cons s a t edge p ih =>
    rcases List.mem_cons.mp hx with rfl | hx
    · exact ⟨.cons edge p, hp, by intro a b h; exact h⟩
    · obtain ⟨q, hq, hsub⟩ := ih (List.nodup_cons.mp hp).2 hx
      exact ⟨q, hq, fun a b h => Or.inr (hsub a b h)⟩

/-- Delete closed subwalks without introducing any new arc. -/
theorem erase_loops {s t} (p : DWalk R s t) :
    ∃ q : DWalk R s t, q.vertices.Nodup ∧ (∀ a b, q.Uses a b → p.Uses a b) := by
  classical
  induction p with
  | nil s => exact ⟨.nil s, by simp [vertices], by intro a b h; exact h⟩
  | @cons s a t edge p ih =>
    obtain ⟨q, hq, hsub⟩ := ih
    by_cases hs : s ∈ q.vertices
    · obtain ⟨z, hz, hzsub⟩ := q.suffix hq hs
      exact ⟨z, hz, fun a b h => Or.inr (hsub a b (hzsub a b h))⟩
    · refine ⟨.cons edge q, List.nodup_cons.mpr ⟨hs, hq⟩, ?_⟩
      intro a b h
      exact h.elim Or.inl (fun h => Or.inr (hsub a b h))

theorem exists_of_reachable {s t} (h : Relation.ReflTransGen R s t) :
    Nonempty (DWalk R s t) := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact ⟨.nil _⟩
  | head edge _ ih =>
    obtain ⟨p⟩ := ih
    exact ⟨.cons edge p⟩

theorem exists_simple_of_reachable {s t} (h : Relation.ReflTransGen R s t) :
    ∃ p : DWalk R s t, p.vertices.Nodup := by
  obtain ⟨p⟩ := exists_of_reachable h
  obtain ⟨q, hq, _⟩ := p.erase_loops
  exact ⟨q, hq⟩

end DWalk
end FiniteFlow

namespace FiniteFlow.DWalk
variable {V : Type*} {R Q : V → V → Prop}

def mono (h : ∀ u v, R u v → Q u v) {s t} : DWalk R s t → DWalk Q s t
  | .nil s => .nil s
  | .cons edge p => .cons (h _ _ edge) (p.mono h)

@[simp] theorem vertices_mono (h : ∀ u v, R u v → Q u v) {s t} (p : DWalk R s t) :
    (p.mono h).vertices = p.vertices := by
  induction p with
  | nil => rfl
  | cons edge p ih => exact congrArg (List.cons _) ih

@[simp] theorem uses_mono (h : ∀ u v, R u v → Q u v) {s t} (p : DWalk R s t) (u v) :
    (p.mono h).Uses u v ↔ p.Uses u v := by
  induction p with
  | nil => rfl
  | cons edge p ih => exact or_congr Iff.rfl ih

end FiniteFlow.DWalk

namespace FiniteFlow.DWalk
variable {V : Type*} {R : V → V → Prop}

/-- Re-express a walk using exactly its own directed arc relation. -/
def restrict {s t} : (p : DWalk R s t) → DWalk p.Uses s t
  | .nil s => .nil s
  | .cons edge p => .cons (Or.inl ⟨rfl,rfl⟩) (p.restrict.mono (fun _ _ h => Or.inr h))

end FiniteFlow.DWalk
