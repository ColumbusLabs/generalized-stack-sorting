import NearestSelectedAncestor

namespace StackSorting.LowPathwidthParts
open GraphWidth SameVertexForest ConnectedConeNormalization PrefixGrowth
variable {n : Nat}
namespace RootedSelection
variable {O : RankedOrder n} {r : Fin n} (A : RootedSelection O r)

noncomputable def contractedBag (G : Graph n) (a : {x : Fin n // x ∈ A.nodes}) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter (fun u => ∃ v, ∃ hv : Cone O r v,
    (A.owner v hv).val = a.val ∧ RegionBag G O v u)

@[simp] theorem mem_contractedBag (G : Graph n) (a : {x : Fin n // x ∈ A.nodes}) (u : Fin n) :
    u ∈ A.contractedBag G a ↔ ∃ v, ∃ hv : Cone O r v,
      (A.owner v hv).val = a.val ∧ RegionBag G O v u := by
  classical
  simp [contractedBag]

theorem original_bag_subset (G : Graph n) (a : {x : Fin n // x ∈ A.nodes}) :
    regionBagSet G O a.val ⊆ A.contractedBag G a := by
  intro u hu
  exact (A.mem_contractedBag G a u).mpr
    ⟨a.val,A.inside a.val a.property,A.owner_selected _ _ a.property,
      (mem_regionBagSet G O a.val u).mp hu⟩

theorem contractedBag_in_cone (G : Graph n) (a : {x : Fin n // x ∈ A.nodes})
    {u : Fin n} (hu : u ∈ A.contractedBag G a) : BagCone G O a.val u := by
  obtain ⟨v,hv,he,hbag⟩ := (A.mem_contractedBag G a u).mp hu
  exact ⟨v,he ▸ A.owner_ancestor v hv,hbag⟩

noncomputable def contractedParent (a : {x : Fin n // x ∈ A.nodes}) : {x : Fin n // x ∈ A.nodes} := by
  classical
  exact if ha : a.val = r then a else
    A.owner (O.parent a.val) (cone_parent O ((A.inside a.val a.property).resolve_right (Ne.symm ha)))

theorem contractedParent_eq (a : {x : Fin n // x ∈ A.nodes}) (ha : a.val ≠ r)
    (hr : O.rel r a.val) :
    A.contractedParent a = A.owner (O.parent a.val) (cone_parent O hr) := by
  simp [contractedParent,ha]

theorem contractedParent_below (a : {x : Fin n // x ∈ A.nodes}) (ha : a.val ≠ r) :
    O.rel (A.contractedParent a).val a.val := by
  have hr := (A.inside a.val a.property).resolve_right (Ne.symm ha)
  rw [A.contractedParent_eq a ha hr]
  have hc := A.owner_ancestor (O.parent a.val) (cone_parent O hr)
  rcases hc with hc | hc
  · exact O.trans hc (O.parent_of_pred hr).1
  · exact hc.symm ▸ (O.parent_of_pred hr).1

/-- Actual contracted bag intersections are exactly the old selected adhesion,
so their bounded original-bag containment is retained explicitly. -/
theorem contracted_intersection_iff (G : Graph n) (a : {x : Fin n // x ∈ A.nodes})
    (ha : a.val ≠ r) (u : Fin n) :
    u ∈ A.contractedBag G a ∧ u ∈ A.contractedBag G (A.contractedParent a) ↔
      RegionAdhesion G O a.val u := by
  constructor
  · rintro ⟨hu,hp⟩
    by_contra hn
    have hcone : Cone O a.val u := (bagComponent_iff G O a.val u).mp
      ⟨A.contractedBag_in_cone G a hu,hn⟩
    obtain ⟨v,hv,he,hbag⟩ := (A.mem_contractedBag G (A.contractedParent a) u).mp hp
    have hav := cone_trans O hcone (regionBag_ancestor G O hbag)
    have hnear : Cone O a.val (A.contractedParent a).val := he ▸ A.owner_nearest v hv a.property hav
    have hbelow := A.contractedParent_below a ha
    rcases hnear with hnear | hnear
    · exact O.irrefl a.val (O.trans hnear hbelow)
    · exact O.irrefl a.val (hnear.symm ▸ hbelow)
  · intro hu
    have hr := (A.inside a.val a.property).resolve_right (Ne.symm ha)
    refine ⟨A.original_bag_subset G a ((mem_regionBagSet G O a.val u).mpr hu.2.1),?_⟩
    apply (A.mem_contractedBag G (A.contractedParent a) u).mpr
    exact ⟨O.parent a.val,cone_parent O hr,
      congrArg Subtype.val (A.contractedParent_eq a ha hr).symm,hu.2.2⟩

def contractedCone (G : Graph n) (a : {x : Fin n // x ∈ A.nodes}) (u : Fin n) : Prop :=
  ∃ b : {x : Fin n // x ∈ A.nodes}, Cone O a.val b.val ∧ u ∈ A.contractedBag G b

/-- The literal union of descendant contracted bags minus the unchanged
adhesion gives exactly the original component. -/
theorem contractedComponent_iff (G : Graph n) (a : {x : Fin n // x ∈ A.nodes}) (u : Fin n) :
    (A.contractedCone G a u ∧ ¬ RegionAdhesion G O a.val u) ↔ Cone O a.val u := by
  constructor
  · rintro ⟨⟨b,hab,hu⟩,hn⟩
    obtain ⟨v,hv,hbag⟩ := A.contractedBag_in_cone G b hu
    exact (bagComponent_iff G O a.val u).mp ⟨⟨v,cone_trans O hab hv,hbag⟩,hn⟩
  · intro hu
    have hr := cone_trans O (A.inside a.val a.property) hu
    refine ⟨⟨A.owner u hr,A.owner_nearest u hr a.property hu,?_⟩,cone_disjoint_adhesion G O hu⟩
    exact (A.mem_contractedBag G (A.owner u hr) u).mpr ⟨u,hr,rfl,Or.inl rfl⟩

/-- Contracted margins are exactly the nearest-selected-owner fibers. -/
theorem contractedMargin_iff (G : Graph n) (a : {x : Fin n // x ∈ A.nodes}) (u : Fin n) :
    (u ∈ A.contractedBag G a ∧ ¬ RegionAdhesion G O a.val u) ↔
      ∃ hu : Cone O r u, (A.owner u hu).val = a.val := by
  constructor
  · rintro ⟨hbag,hn⟩
    have hau : Cone O a.val u := (bagComponent_iff G O a.val u).mp
      ⟨A.contractedBag_in_cone G a hbag,hn⟩
    obtain ⟨v,hv,he,hvu⟩ := (A.mem_contractedBag G a u).mp hbag
    have huv := regionBag_ancestor G O hvu
    have ho := A.owner_interval v hv (he.symm ▸ hau) huv
    exact ⟨cone_trans O (A.inside a.val a.property) hau,(congrArg Subtype.val ho).trans he⟩
  · rintro ⟨hu,he⟩
    refine ⟨(A.mem_contractedBag G a u).mpr ⟨u,hu,he,Or.inl rfl⟩,?_⟩
    exact cone_disjoint_adhesion G O (he ▸ A.owner_ancestor u hu)

end RootedSelection
end StackSorting.LowPathwidthParts
