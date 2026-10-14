import DecompositionForests

namespace StackSorting.GuidedPathwidth
universe u v
variable {V : Type u} {W : Type v} {G : SimpleGraph V} {H : SimpleGraph W}
    {P : Set V} {c : Nat}

namespace ReachIn
/-- Map the actual finite path, including all internal vertices. -/
theorem map {S : Set V} {T : Set W} {x y : V} (f : V → W)
    (hf : ∀ {a b}, G.Adj a b → H.Adj (f a) (f b))
    (hS : ∀ a ∈ S, f a ∈ T) (h : ReachIn G S x y) :
    ReachIn H T (f x) (f y) :=
  ⟨hS x h.1,hS y h.2.1,h.2.2.map f (fun _ _ h => hf h) hS⟩
end ReachIn

namespace Color
/-- Injective graph maps transport actual rooted guides and their colors. -/
def map (C : Color G P) (f : V ↪ W)
    (hf : ∀ {a b}, G.Adj a b → H.Adj (f a) (f b)) : Color H (f '' P) where
  support := fun r => {y | ∃ s x, f s = r ∧ f x = y ∧ x ∈ C.support s}
  inside := by
    rintro r y ⟨s,x,_,rfl,hx⟩
    exact ⟨x,C.inside s hx,rfl⟩
  reaches := by
    rintro r y ⟨s,x,rfl,rfl,hx⟩
    exact (C.reaches s x hx).map f hf (fun z hz => ⟨s,z,rfl,rfl,hz⟩)
  unique := by
    rintro r s y ⟨a,x,rfl,hx,hxa⟩ ⟨b,z,rfl,hz,hzb⟩
    have hxz : x = z := f.injective (hx.trans hz.symm)
    subst z
    exact congrArg f (C.unique a b x hxa hzb)
end Color

namespace System
noncomputable def map (C : System G P c) (f : V ↪ W)
    (hf : ∀ {a b}, G.Adj a b → H.Adj (f a) (f b)) : System H (f '' P) c :=
  fun i => (C i).map f hf

theorem map_captures (C : System G P c) (f : V ↪ W)
    (hf : ∀ {a b}, G.Adj a b → H.Adj (f a) (f b)) {B : Set V}
    (h : Captures G C B) : Captures H (C.map f hf) (f '' B) := by
  intro hb
  obtain ⟨y,r,hr,_⟩ := hb
  obtain ⟨x,hx⟩ := h ⟨r,hr⟩
  refine ⟨f x,?_⟩
  rintro s ⟨s,hs,rfl⟩
  obtain ⟨i,hi⟩ := hx s hs
  exact ⟨i,s,x,rfl,rfl,hi⟩
end System
end StackSorting.GuidedPathwidth
