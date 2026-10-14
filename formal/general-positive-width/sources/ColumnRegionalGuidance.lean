import IndexedColumnPorts
import GuidanceBiInterface

namespace StackSorting.BiInterface.RepeatedColumn
open PathWord GuidedPathwidth
variable {k : Nat}

/-- Present named roots retain their actual column, port and quotient vertex. -/
structure ColumnRoot (ps : List (Packed k)) where
  column : Fin ps.length
  port : Port k
  vertex : (Packed.eval ps).Vertex
  present : globalPort ps column port = some vertex

noncomputable def regionalColorEquiv (k : Nat) : (Fin 4 × Port k) ≃ Fin (8*k) :=
  Fintype.equivFinOfCardEq (by simp [Port]; omega)

noncomputable def columnRegionalData (ps : List (Packed.{0} k))
    (hd : ∀ P ∈ ps, DisjointInterfaces P.graph) :
    RegionalData (Packed.eval ps).graph.simple Set.univ (8*k) (ColumnRoot ps) where
  window := fun a => columnWindow ps a.column.val 1
  root := ColumnRoot.vertex
  color := fun a => regionalColorEquiv k (⟨a.column.val % 4,Nat.mod_lt _ (by omega)⟩,a.port)
  inside := by intro a x hx; trivial
  noncollision := by
    intro a b hc hr
    have he := (regionalColorEquiv k).injective hc
    have hm : a.column.val % 4 = b.column.val % 4 := congrArg (fun x => x.1.val) he
    have hp : a.port = b.port := congrArg Prod.snd he
    have hi : a.column ≠ b.column := by
      intro hi
      have heq : some a.vertex = some b.vertex := by
        rw [← a.present,← b.present,hi,hp]
      exact hr (Option.some.inj heq)
    exact radius_one_same_residue_disjoint ps hd a.column.val b.column.val
      (fun h => hi (Fin.ext h)) hm

noncomputable def columnGuides (ps : List (Packed.{0} k))
    (hd : ∀ P ∈ ps, DisjointInterfaces P.graph) :
    System (Packed.eval ps).graph.simple Set.univ (8*k) :=
  (columnRegionalData ps hd).guides

/-- Eight interface-width colors suffice for all local named-root routes in
an arbitrary-length idempotent word. Paths and roots are actual graph data. -/
theorem columnGuides_route (e : Abstract k) (he : e*e=e)
    (ps : List (Packed.{0} k)) (hp : ∀ P ∈ ps, abstractGraph P.graph = e)
    (hd : ∀ P ∈ ps, DisjointInterfaces P.graph)
    (i : Fin ps.length) (x : (ps.get i).Vertex) (p : Port k)
    (r : (Packed.eval ps).Vertex) (hr : globalPort ps i p = some r)
    (hxr : Reach (Packed.eval ps).graph.Adj ((occurrenceAt ps i).column x) r) :
    ∃ j, (occurrenceAt ps i).column x ∈ (columnGuides ps hd j).support r := by
  let a : ColumnRoot ps := ⟨i,p,r,hr⟩
  refine ⟨(columnRegionalData ps hd).color a,?_⟩
  apply (columnRegionalData ps hd).routes (j := a)
  refine ⟨?_,globalPort_window ps i p hr,?_⟩
  · exact mem_columnWindow (occurrenceAt ps i) x i.val 1 (by simp) (by simp)
  · exact reachable_globalPort_local e he ps hp i x p r hr hxr

/-- Every component-contained subset of one column's named boundary is
captured by the same globally fixed finite palette. -/
theorem columnGuides_capture_boundary (e : Abstract k) (he : e*e=e)
    (ps : List (Packed.{0} k)) (hp : ∀ P ∈ ps, abstractGraph P.graph = e)
    (hd : ∀ P ∈ ps, DisjointInterfaces P.graph) (i : Fin ps.length)
    (B : Set (Packed.eval ps).Vertex)
    (hb : ∀ r ∈ B, ∃ p, globalPort ps i p = some r)
    (hconn : ∀ r ∈ B, ∀ s ∈ B, Reach (Packed.eval ps).graph.Adj r s) :
    Captures (Packed.eval ps).graph.simple (columnGuides ps hd) B := by
  intro hne
  obtain ⟨b,hbB⟩ := hne
  obtain ⟨p,hpB⟩ := hb b hbB
  obtain ⟨x,_,hx⟩ := Option.map_eq_some_iff.mp hpB
  refine ⟨b,?_⟩
  intro r hrB
  obtain ⟨q,hq⟩ := hb r hrB
  have hxr : Reach (Packed.eval ps).graph.Adj ((occurrenceAt ps i).column x) r :=
    hx.symm ▸ hconn b hbB r hrB
  simpa only [hx] using columnGuides_route e he ps hp hd i x q r hq hxr

#print axioms columnGuides_route
#print axioms columnGuides_capture_boundary
end StackSorting.BiInterface.RepeatedColumn
