import SubdivisionRealization
import BoundedSourceTree

namespace StackSorting.GraphWidth.UCurve.SubdivisionTree

/-- A finite simple path in an actual target graph. -/
structure GraphPath {m} (H : Graph m) (a b : Fin m) where
  length : Nat
  positive : 0 < length
  atPoint : Fin (length+1) → Fin m
  first : atPoint ⟨0,by omega⟩ = a
  last : atPoint ⟨length,by omega⟩ = b
  injective : Function.Injective atPoint
  step : ∀ i : Fin length, H.Adj (atPoint ⟨i.val,by omega⟩) (atPoint ⟨i.val+1,by omega⟩)

def GraphPath.unit {m} {H : Graph m} {a b : Fin m} (hab : H.Adj a b) : GraphPath H a b where
  length := 1
  positive := by decide
  atPoint := fun i => if i.val=0 then a else b
  first := rfl
  last := rfl
  injective := by
    intro i j he
    have hi := i.isLt
    have hj := j.isLt
    have hn : a≠b := by intro he; subst b; exact H.loopless a hab
    apply Fin.ext
    by_cases h : i.val=0 <;> by_cases h' : j.val=0 <;> simp_all
    all_goals omega
  step := by
    intro i
    have hi : i.val=0 := by have := i.isLt; omega
    simpa [hi] using hab

def Realization.path {n m} {G : Graph n} {H : Graph m} (S : Realization G H)
    (e : OrderedEdge G) : GraphPath H (S.point e.low) (S.point e.high) where
  length := S.length e
  positive := S.positive e
  atPoint := S.pointAt e
  first := S.first e
  last := S.last e
  injective := S.path_injective e
  step := S.step e

def apexPoint {n m} {G : Graph n} {H : Graph m} (S : Realization G H) (a : Fin m) :
    Fin (n+1) → Fin m := Fin.cases a S.point

@[simp] theorem apexPoint_zero {n m} {G : Graph n} {H : Graph m}
    (S : Realization G H) (a : Fin m) : apexPoint S a 0=a := rfl
@[simp] theorem apexPoint_succ {n m} {G : Graph n} {H : Graph m}
    (S : Realization G H) (a : Fin m) (v : Fin n) : apexPoint S a v.succ=S.point v := rfl

noncomputable def apexPath {n m} {G : Graph n} {H : Graph m} (S : Realization G H)
    (anchor : Fin n → Prop) (a : Fin m)
    (ha : ∀ v, anchor v → H.Adj a (S.point v))
    (i j : Fin (n+1)) (ho : i.val<j.val) (he : (SourceApex.graph G anchor).Adj i j) :
    GraphPath H (apexPoint S a i) (apexPoint S a j) := by
  revert ho he
  refine Fin.cases ?_ (fun u => ?_) i
  · refine Fin.cases ?_ (fun v => ?_) j
    · intro ho; exact False.elim (by omega)
    · intro _ he; exact GraphPath.unit (ha v he)
  · refine Fin.cases ?_ (fun v => ?_) j
    · intro ho; exact False.elim (by simp only [Fin.val_zero,Fin.val_succ] at ho; omega)
    · intro ho he
      exact S.path ⟨u,v,by simpa only [Fin.val_succ,Nat.add_lt_add_iff_right] using ho,he⟩

theorem apexPoint_injective {n m} {G : Graph n} {H : Graph m}
    (S : Realization G H) (a : Fin m) (ha : ∀ v, S.point v≠a) :
    Function.Injective (apexPoint S a) := by
  intro i j
  refine Fin.cases ?_ (fun u => ?_) i
  · refine Fin.cases ?_ (fun v => ?_) j
    · intro _; rfl
    · intro he; exact False.elim (ha v he.symm)
  · refine Fin.cases ?_ (fun v => ?_) j
    · intro he; exact False.elim (ha u he)
    · intro he; exact congrArg Fin.succ (S.point_injective he)

theorem apexPath_avoids {n m} {G : Graph n} {H : Graph m} (S : Realization G H)
    (anchor : Fin n → Prop) (a : Fin m)
    (ha : ∀ v, anchor v → H.Adj a (S.point v))
    (hout : ∀ e i, S.pointAt e i≠a)
    (e : OrderedEdge (SourceApex.graph G anchor))
    (i : Fin ((apexPath S anchor a ha e.low e.high e.ordered e.adjacent).length+1))
    (hi : 0<i.val) (hi' : i.val<(apexPath S anchor a ha e.low e.high e.ordered e.adjacent).length)
    (v : Fin (n+1)) :
    (apexPath S anchor a ha e.low e.high e.ordered e.adjacent).atPoint i≠apexPoint S a v := by
  obtain ⟨l,h,ho,he⟩ := e
  revert ho he i hi hi'
  refine Fin.cases ?_ (fun l => ?_) l
  · refine Fin.cases ?_ (fun h => ?_) h
    · intro ho; simp only [Fin.val_zero] at ho; omega
    · intro ho he i hi hi'
      change i.val<1 at hi'
      omega
  · refine Fin.cases ?_ (fun h => ?_) h
    · intro ho; simp only [Fin.val_zero,Fin.val_succ] at ho; omega
    · intro ho he i hi hi'
      let f : OrderedEdge G := ⟨l,h,by simpa only [Fin.val_succ,Nat.add_lt_add_iff_right] using ho,he⟩
      change S.pointAt f i≠apexPoint S a v
      refine Fin.cases ?_ (fun v => ?_) v
      · exact hout f i
      · exact S.avoids f i hi hi' v

theorem apexPath_disjoint {n m} {G : Graph n} {H : Graph m} (S : Realization G H)
    (anchor : Fin n → Prop) (a : Fin m)
    (ha : ∀ v, anchor v → H.Adj a (S.point v))
    (e f : OrderedEdge (SourceApex.graph G anchor))
    (i : Fin ((apexPath S anchor a ha e.low e.high e.ordered e.adjacent).length+1))
    (j : Fin ((apexPath S anchor a ha f.low f.high f.ordered f.adjacent).length+1))
    (hi : 0<i.val) (hi' : i.val<(apexPath S anchor a ha e.low e.high e.ordered e.adjacent).length)
    (hj : 0<j.val) (hj' : j.val<(apexPath S anchor a ha f.low f.high f.ordered f.adjacent).length)
    (hp : (apexPath S anchor a ha e.low e.high e.ordered e.adjacent).atPoint i=
      (apexPath S anchor a ha f.low f.high f.ordered f.adjacent).atPoint j) : e=f := by
  obtain ⟨l,h,ho,he⟩ := e
  obtain ⟨l',h',ho',he'⟩ := f
  revert ho he i hi hi' hp
  refine Fin.cases ?_ (fun l => ?_) l
  · refine Fin.cases ?_ (fun h => ?_) h
    · intro ho; simp only [Fin.val_zero] at ho; omega
    · intro ho he i hi hi'; change i.val<1 at hi'; omega
  · refine Fin.cases ?_ (fun h => ?_) h
    · intro ho; simp only [Fin.val_zero,Fin.val_succ] at ho; omega
    · intro ho he i hi hi' hp
      let e : OrderedEdge G := ⟨l,h,by simpa only [Fin.val_succ,Nat.add_lt_add_iff_right] using ho,he⟩
      revert ho' he' j hj hj' hp
      refine Fin.cases ?_ (fun l' => ?_) l'
      · refine Fin.cases ?_ (fun h' => ?_) h'
        · intro ho'; simp only [Fin.val_zero] at ho'; omega
        · intro ho' he' j hj hj'; change j.val<1 at hj'; omega
      · refine Fin.cases ?_ (fun h' => ?_) h'
        · intro ho'; simp only [Fin.val_zero,Fin.val_succ] at ho'; omega
        · intro ho' he' j hj hj' hp
          let f : OrderedEdge G := ⟨l',h',by simpa only [Fin.val_succ,Nat.add_lt_add_iff_right] using ho',he'⟩
          have hef : e=f := S.disjoint e f i j hi hi' hj hj' hp
          apply OrderedEdge.ext
          · exact congrArg Fin.succ (congrArg OrderedEdge.low hef)
          · exact congrArg Fin.succ (congrArg OrderedEdge.high hef)

/-- Adjoining an apex uses only the actual anchor spokes. Every new route
has length one, so it creates no extra route-interior vertex. -/
noncomputable def Realization.withApex {n m} {G : Graph n} {H : Graph m}
    (S : Realization G H) (anchor : Fin n → Prop) (a : Fin m)
    (hpoint : ∀ v, S.point v≠a) (hout : ∀ e i, S.pointAt e i≠a)
    (ha : ∀ v, anchor v → H.Adj a (S.point v)) :
    Realization (SourceApex.graph G anchor) H where
  length := fun e => (apexPath S anchor a ha e.low e.high e.ordered e.adjacent).length
  positive := fun e => (apexPath S anchor a ha e.low e.high e.ordered e.adjacent).positive
  point := apexPoint S a
  point_injective := apexPoint_injective S a hpoint
  pointAt := fun e => (apexPath S anchor a ha e.low e.high e.ordered e.adjacent).atPoint
  first := fun e => (apexPath S anchor a ha e.low e.high e.ordered e.adjacent).first
  last := fun e => (apexPath S anchor a ha e.low e.high e.ordered e.adjacent).last
  path_injective := fun e => (apexPath S anchor a ha e.low e.high e.ordered e.adjacent).injective
  step := fun e => (apexPath S anchor a ha e.low e.high e.ordered e.adjacent).step
  avoids := apexPath_avoids S anchor a ha hout
  disjoint := apexPath_disjoint S anchor a ha

/-- The original source edges retain their exact route lengths. -/
@[simp] theorem Realization.withApex_source_length {n m} {G : Graph n} {H : Graph m}
    (S : Realization G H) (anchor : Fin n → Prop) (a : Fin m)
    (hpoint : ∀ v, S.point v≠a) (hout : ∀ e i, S.pointAt e i≠a)
    (ha : ∀ v, anchor v → H.Adj a (S.point v)) (e : OrderedEdge G) :
    (S.withApex anchor a hpoint hout ha).length
      ⟨e.low.succ,e.high.succ,by simpa only [Fin.val_succ,Nat.add_lt_add_iff_right] using e.ordered,e.adjacent⟩=
      S.length e := rfl

/-- Every anchor spoke is a single actual target edge. -/
@[simp] theorem Realization.withApex_spoke_length {n m} {G : Graph n} {H : Graph m}
    (S : Realization G H) (anchor : Fin n → Prop) (a : Fin m)
    (hpoint : ∀ v, S.point v≠a) (hout : ∀ e i, S.pointAt e i≠a)
    (ha : ∀ v, anchor v → H.Adj a (S.point v)) (v : Fin n) (hv : anchor v) :
    (S.withApex anchor a hpoint hout ha).length
      ⟨0,v.succ,by simp only [Fin.val_zero,Fin.val_succ]; omega,hv⟩=1 := rfl

end StackSorting.GraphWidth.UCurve.SubdivisionTree
