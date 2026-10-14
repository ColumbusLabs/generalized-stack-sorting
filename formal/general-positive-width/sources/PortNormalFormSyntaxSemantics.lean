import PortNormalFormSyntax

namespace StackSorting.FinitePort
open TreeAutomaton.Logic SparseTreeCompiler

variable {n colors relations W : Nat}
variable (T : RootedTree n) (G : Diagram n colors relations)
variable (labels : Vertex n → Alphabet colors relations W)
variable (child : Bool → Vertex n → Vertex n → Prop)
variable (parent order : Formula (Alphabet colors relations W) 2)
variable (rel : Fin relations → Formula (Alphabet colors relations W) 2)

private theorem points_two {P : Type} (xs : Fin 2 → P) :
    (fun i => point (xs i))=binaryVal (xs 0) (xs 1) := by
  funext i
  fin_cases i <;> rfl

theorem eval_adjacentFormula
    (hr : ∀ r u v, (rel r).EvalOn labels child (binaryVal u v) ↔ G.rel r u v=true)
    (u v : Vertex n) :
    (adjacentFormula rel).EvalOn labels child (binaryVal u v) ↔ Adjacent G u v := by
  simp only [adjacentFormula,eval_disjoin_map,Finset.mem_toList,Finset.mem_univ,true_and]
  apply exists_congr
  intro r
  simp only [eval_disjoin,List.mem_cons,exists_eq_or_imp]
  rw [eval_atPair labels child _ 1 0 _ v u rfl rfl,hr,hr]
  simp

theorem eval_rootEmptyFormula
    (hp : ExactParent T labels child parent) :
    (rootEmptyFormula parent).EvalOn labels child Fin.elim0 ↔ RootEmpty (labelCode labels) := by
  classical
  rw [rootEmptyFormula,eval_closeAll]
  constructor
  · intro h v hv
    have hh := h (fun _ => v)
    rw [FiniteState.eval_implies,eval_labelTest labels child _ 0 v rfl] at hh
    apply hh
    rw [Formula.EvalOn,Formula.evalOn_existsFirst]
    rintro ⟨p,hp'⟩
    simp_rw [singleton_eq_point] at hp'
    rw [eval_atPair labels child _ 0 1 _ p v rfl rfl,hp] at hp'
    exact hp'.1 hv
  · intro h xs
    rw [FiniteState.eval_implies,eval_labelTest labels child _ 0 (xs 0) rfl]
    intro hn
    apply h
    by_contra hv
    apply hn
    rw [Formula.evalOn_existsFirst]
    simp_rw [singleton_eq_point]
    refine ⟨T.parent (xs 0),?_⟩
    rw [eval_atPair labels child _ 0 1 _ (T.parent (xs 0)) (xs 0) rfl rfl,hp]
    exact ⟨hv,rfl⟩

/-- Every accepted stored slot is a real bounded route. The set-based route
semantics has no assumption that the input code already came from an encoder. -/
theorem eval_validSlotsFormula
    (hp : ExactParent T labels child parent) (hz : RootEmpty (labelCode labels)) :
    (validSlotsFormula parent).EvalOn labels child Fin.elim0 ↔
      ∀ v i, i < (labelCode labels v).ports.length →
        ∃ u, readPort T (labelCode labels) n v (i+1)=some u := by
  classical
  rw [validSlotsFormula,eval_closeAll]
  have one (xs : Fin 1 → Vertex n) :
      (allFinite (fun i : Fin W => FiniteState.implies (slotPresent 0 i)
        (.existsFirst (atPair (portRoute parent (slotNumber i)) 1 0)))).EvalOn
        labels child (fun j => point (xs j)) ↔
      ∀ i : Fin W, i.val < (labelCode labels (xs 0)).ports.length →
        ∃ u, readPort T (labelCode labels) n (xs 0) (i.val+1)=some u := by
    rw [eval_allFinite]
    apply forall_congr'
    intro i
    rw [FiniteState.eval_implies,slotPresent,eval_labelTest labels child _ 0 (xs 0) rfl]
    apply imp_congr_right
    intro _
    rw [Formula.evalOn_existsFirst]
    simp_rw [singleton_eq_point]
    apply exists_congr
    intro u
    rw [eval_atPair labels child _ 1 0 _ (xs 0) u rfl rfl,
      eval_portRoute T labels child parent hp hz]
  simp only [one]
  constructor
  · intro h v i hi
    have hb := (labelCode_bounded labels v).1
    exact h (fun _ => v) ⟨i,by omega⟩ hi
  · intro h xs i hi
    exact h (xs 0) i.val hi

theorem eval_frontierSlotsFormula
    (hp : ExactParent T labels child parent) (hz : RootEmpty (labelCode labels))
    (hr : ∀ r u v, (rel r).EvalOn labels child (binaryVal u v) ↔ G.rel r u v=true) :
    (frontierSlotsFormula parent rel).EvalOn labels child Fin.elim0 ↔
      ∀ v u, Inherited T G v u ↔ ∃ i, i < (labelCode labels v).ports.length ∧
        readPort T (labelCode labels) n v (i+1)=some u := by
  classical
  rw [frontierSlotsFormula,eval_closeAll]
  have one (xs : Fin 2 → Vertex n) :
      (iffFormula (inheritedFormula parent (adjacentFormula rel))
        (disjoin ((Finset.univ : Finset (Fin W)).toList.map (fun i =>
          .conj (slotPresent 0 i) (portRoute parent (slotNumber i)))))).EvalOn
        labels child (fun j => point (xs j)) ↔
      (Inherited T G (xs 0) (xs 1) ↔ ∃ i, i < (labelCode labels (xs 0)).ports.length ∧
        readPort T (labelCode labels) n (xs 0) (i+1)=some (xs 1)) := by
    rw [points_two,eval_iffFormula,eval_inheritedFormula T G labels child parent
      (adjacentFormula rel) hp (eval_adjacentFormula G labels child rel hr)]
    apply iff_congr Iff.rfl
    simp only [eval_disjoin_map,Finset.mem_toList,Finset.mem_univ,true_and,Formula.EvalOn]
    simp only [slotPresent,eval_labelTest labels child (binaryVal (xs 0) (xs 1)) 0 (xs 0) rfl,
      eval_portRoute T labels child parent hp hz]
    constructor
    · rintro ⟨i,hi,hh⟩; exact ⟨i.val,hi,hh⟩
    · rintro ⟨i,hi,hh⟩
      have hb := (labelCode_bounded labels (xs 0)).1
      exact ⟨⟨i,by omega⟩,hi,hh⟩
  simp only [one]
  constructor
  · intro h v u; exact h (Fin.cons v (fun _ => u))
  · intro h xs; exact h (xs 0) (xs 1)

theorem orderedSlotsFormula_sound (O : FixedOrder n)
    (hp : ExactParent T labels child parent) (hz : RootEmpty (labelCode labels))
    (ho : ∀ u v, order.EvalOn labels child (binaryVal u v) ↔
      O.vertices.idxOf u < O.vertices.idxOf v)
    (h : (orderedSlotsFormula parent order).EvalOn labels child Fin.elim0) :
    ∀ v i j, i < j → j < (labelCode labels v).ports.length → ∀ u w,
      readPort T (labelCode labels) n v (i+1)=some u →
      readPort T (labelCode labels) n v (j+1)=some w →
      O.vertices.idxOf u < O.vertices.idxOf w := by
  classical
  rw [orderedSlotsFormula,eval_closeAll] at h
  intro v i j hij hj u w hiR hjR
  have hb := (labelCode_bounded labels v).1
  let ii : Fin W := ⟨i,by omega⟩
  let jj : Fin W := ⟨j,by omega⟩
  let xs : Fin 3 → Vertex n := Fin.cons v (Fin.cons u (fun _ => w))
  have hh := (eval_allFinite labels child _ _).mp (h xs) (ii,jj)
  rw [ite_eq_left (show ii.val < jj.val from hij),FiniteState.eval_implies] at hh
  have hP : (slotPresent 0 jj).EvalOn labels child (fun z => point (xs z)) := by
    rw [slotPresent,eval_labelTest labels child _ 0 v rfl]
    exact hj
  have hI : (atPair (portRoute parent (slotNumber ii)) 0 1).EvalOn labels child
      (fun z => point (xs z)) := by
    rw [eval_atPair labels child _ 0 1 _ v u rfl rfl,
      eval_portRoute T labels child parent hp hz]
    exact hiR
  have hJ : (atPair (portRoute parent (slotNumber jj)) 0 2).EvalOn labels child
      (fun z => point (xs z)) := by
    rw [eval_atPair labels child _ 0 2 _ v w rfl rfl,
      eval_portRoute T labels child parent hp hz]
    exact hjR
  have hout := hh ⟨hP,hI,hJ⟩
  rwa [eval_atPair labels child _ 1 2 _ u w rfl rfl,ho] at hout

theorem bitsSlotsFormula_sound
    (hp : ExactParent T labels child parent) (hz : RootEmpty (labelCode labels))
    (hr : ∀ r u v, (rel r).EvalOn labels child (binaryVal u v) ↔ G.rel r u v=true)
    (h : (bitsSlotsFormula parent rel).EvalOn labels child Fin.elim0) :
    ∀ v i e, (labelCode labels v).ports[i]?=some e → ∀ u,
      readPort T (labelCode labels) n v (i+1)=some u → ∀ r forward,
        e.bit r forward = if forward then G.rel r v u else G.rel r u v := by
  classical
  rw [bitsSlotsFormula,eval_closeAll] at h
  intro v i e he u hu r forward
  obtain ⟨hi,_⟩ := List.getElem?_eq_some_iff.mp he
  have hb := (labelCode_bounded labels v).1
  let ii : Fin W := ⟨i,by omega⟩
  have hh := (eval_allFinite labels child _ _).mp (h (Fin.cons v (fun _ => u))) (ii,r,forward)
  rw [points_two,FiniteState.eval_implies] at hh
  simp only [Fin.cons_zero,Fin.cons_one] at hh
  have hP : (slotPresent 0 ii).EvalOn labels child (binaryVal v u) := by
    rw [slotPresent,eval_labelTest labels child _ 0 v rfl]
    exact hi
  have hR : (portRoute parent (slotNumber ii)).EvalOn labels child (binaryVal v u) :=
    (eval_portRoute T labels child parent hp hz _ v u).mpr hu
  have hout := hh ⟨hP,hR⟩
  rw [eval_iffFormula,slotBits,eval_labelTest labels child _ 0 v rfl] at hout
  have heval : (∃ e', (labels v).toLabel.ports[ii.val]?=some e' ∧
      e'.bit r forward=true) ↔ e.bit r forward=true := by
    change (∃ e', (labelCode labels v).ports[i]?=some e' ∧ e'.bit r forward=true) ↔ _
    rw [he]
    simp
  rw [heval] at hout
  have hiff : (e.bit r forward=true) ↔
      ((if forward then G.rel r v u else G.rel r u v)=true) := by
    cases forward with
    | false =>
      change (e.bit r false=true ↔ (atPair (rel r) 1 0).EvalOn labels child
        (binaryVal v u)) at hout
      rw [eval_atPair labels child _ 1 0 _ u v rfl rfl,hr] at hout
      exact hout
    | true =>
      change (e.bit r true=true ↔ (rel r).EvalOn labels child (binaryVal v u)) at hout
      rw [hr] at hout
      exact hout
  cases hbit : e.bit r forward <;>
    cases hrel : (if forward then G.rel r v u else G.rel r u v) <;> simp_all

/-- Soundness of the literal fixed finite sentence: no normal-form,
recognizability or pre-existing encoder witness is a premise. The primitive
parent/order/relation formulas must denote their stated relations. -/
theorem normalSlotsFormula_sound (O : FixedOrder n)
    (hp : ExactParent T labels child parent)
    (ho : ∀ u v, order.EvalOn labels child (binaryVal u v) ↔
      O.vertices.idxOf u < O.vertices.idxOf v)
    (hr : ∀ r u v, (rel r).EvalOn labels child (binaryVal u v) ↔ G.rel r u v=true)
    (hc : ∀ v, (labels v).toLabel.color=G.color v)
    (h : (normalSlotsFormula parent order rel).EvalOn labels child Fin.elim0) :
    labelCode labels = encode T O G := by
  have hall := (FiniteState.eval_conjoin labels child Fin.elim0 _).mp h
  have root := hall (rootEmptyFormula parent) (by simp)
  have hz := (eval_rootEmptyFormula T labels child parent hp).mp root
  have valid := hall (validSlotsFormula parent) (by simp)
  have frontier := hall (frontierSlotsFormula parent rel) (by simp)
  have ordered := hall (orderedSlotsFormula parent order) (by simp)
  have bits := hall (bitsSlotsFormula parent rel) (by simp)
  apply RelationalPortNormalForm.eq_encode
  exact ⟨hc,(eval_validSlotsFormula T labels child parent hp hz).mp valid,
    (eval_frontierSlotsFormula T G labels child parent rel hp hz hr).mp frontier,
    orderedSlotsFormula_sound T labels child parent order O hp hz ho ordered,
    bitsSlotsFormula_sound T G labels child parent rel hp hz hr bits⟩

#print axioms eval_adjacentFormula
#print axioms eval_rootEmptyFormula
#print axioms eval_validSlotsFormula
#print axioms eval_frontierSlotsFormula
#print axioms normalSlotsFormula_sound
end StackSorting.FinitePort
