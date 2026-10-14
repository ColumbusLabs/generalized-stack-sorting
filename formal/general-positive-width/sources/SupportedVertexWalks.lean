import NormalizedPrefixSaturation

namespace FiniteFlow.Hypergraph
variable {V E : Type*} {inc : V → E → Prop}

def SupportedIncidence (S : Set V) (x : S) (e : E) : Prop := inc x.val e

namespace HWalk
/-- Restrict an actual supported walk, preserving every edge identifier. -/
def onSupport (S : Set V) (support : ∀ x e, inc x e → x ∈ S) :
    {a b : V} → (w : HWalk inc a b) → (ha : a ∈ S) → (hb : b ∈ S) →
    HWalk (SupportedIncidence (inc := inc) S) ⟨a,ha⟩ ⟨b,hb⟩
  | _,_,.nil x,ha,_ => .nil (inc := SupportedIncidence (inc := inc) S) (⟨x,ha⟩ : S)
  | _,_,.cons (y := y) e hx hy tail,ha,hb =>
      .cons (inc := SupportedIncidence (inc := inc) S) (x := (⟨_,ha⟩ : S)) (y := (⟨y,support y e hy⟩ : S)) e hx hy
        (tail.onSupport S support (support y e hy) hb)

def forgetSupport {S : Set V} {a b : S} (w : HWalk (SupportedIncidence (inc := inc) S) a b) :
    HWalk inc a.val b.val :=
  match w with
  | .nil x => .nil x.val
  | .cons e hx hy tail => .cons e hx hy tail.forgetSupport

@[simp] theorem edges_onSupport (S : Set V) (support : ∀ x e, inc x e → x ∈ S)
    {a b : V} (w : HWalk inc a b) (ha : a ∈ S) (hb : b ∈ S) :
    (w.onSupport S support ha hb).edges = w.edges := by
  induction w with
  | nil => rfl
  | cons e hx hy tail ih => exact congrArg (List.cons e) (ih _ _)

@[simp] theorem edges_forgetSupport {S : Set V} {a b : S}
    (w : HWalk (SupportedIncidence (inc := inc) S) a b) : w.forgetSupport.edges = w.edges := by
  induction w with
  | nil => rfl
  | cons e hx hy tail ih => exact congrArg (List.cons e) ih
end HWalk

theorem supported_cutedge_iff (S : Set V) (support : ∀ x e, inc x e → x ∈ S)
    (s t : S) (e : E) :
    Cutedge (SupportedIncidence (inc := inc) S) s t e ↔ Cutedge inc s.val t.val e := by
  rw [cutedge_iff_every_walk,cutedge_iff_every_walk]
  constructor
  · intro h w
    simpa only [HWalk.edges_onSupport] using h (w.onSupport S support s.property t.property)
  · intro h w
    simpa only [HWalk.edges_forgetSupport] using h w.forgetSupport

theorem supported_component_iff (S : Set V) (support : ∀ x e, inc x e → x ∈ S)
    (s t x y : S) :
    SameCutedgeComponent (SupportedIncidence (inc := inc) S) s t x y ↔
      SameCutedgeComponent inc s.val t.val x.val y.val := by
  constructor
  · rintro ⟨w⟩
    let w' := HWalk.forgetSupport
      (inc := fun x e => inc x e ∧ ¬ Cutedge (SupportedIncidence (inc := inc) S) s t e) (S := S) w
    exact ⟨w'.mapEdges (inc := fun x e => inc x e ∧ ¬ Cutedge (SupportedIncidence (inc := inc) S) s t e)
      (inc' := NoncutIncidence inc s.val t.val) id
      (fun x e h => ⟨h.1,fun he => h.2 ((supported_cutedge_iff S support s t e).mpr he)⟩)⟩
  · rintro ⟨w⟩
    let w' := w.onSupport S (fun x e h => support x e h.1) x.property y.property
    exact ⟨w'.mapEdges (inc := SupportedIncidence (inc := NoncutIncidence inc s.val t.val) S)
      (inc' := NoncutIncidence (SupportedIncidence (inc := inc) S) s t) id
      (fun x e h => ⟨h.1,fun he => h.2 ((supported_cutedge_iff S support s t e).mp he)⟩)⟩

theorem supported_touches_iff (S : Set V) (support : ∀ x e, inc x e → x ∈ S)
    (s t x : S) (b : CutBoundary E) :
    ComponentTouches (inc := SupportedIncidence (inc := inc) S) (s := s) (t := t) x b ↔
      ComponentTouches (inc := inc) (s := s.val) (t := t.val) x.val b := by
  cases b with
  | source => exact supported_component_iff S support s t x s
  | sink => exact supported_component_iff S support s t x t
  | cut e =>
    constructor
    · rintro ⟨y,hy,hxy⟩
      exact ⟨y.val,hy,(supported_component_iff S support s t x y).mp hxy⟩
    · rintro ⟨y,hy,hxy⟩
      exact ⟨⟨y,support y e hy⟩,hy,(supported_component_iff S support s t x _).mpr hxy⟩

end FiniteFlow.Hypergraph
