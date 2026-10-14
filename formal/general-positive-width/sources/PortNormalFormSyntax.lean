import PortFrontierMSO
import PortRelationalNormalForm

namespace StackSorting.FinitePort
open TreeAutomaton.Logic SparseTreeCompiler

noncomputable def allFinite {α I : Type} [Fintype I] {k} (f : I → Formula α k) : Formula α k :=
  FiniteState.conjoin ((Finset.univ : Finset I).toList.map f)

theorem eval_allFinite {α P I : Type} [Fintype I] {k} (label : P → α)
    (child : Bool → P → P → Prop) (v : Fin k → P → Bool) (f : I → Formula α k) :
    (allFinite f).EvalOn label child v ↔ ∀ i, (f i).EvalOn label child v := by
  simp only [allFinite,FiniteState.eval_conjoin,List.forall_mem_map,Finset.mem_toList,
    Finset.mem_univ,forall_const]

def iffFormula {α : Type} {k} (f g : Formula α k) : Formula α k :=
  .conj (FiniteState.implies f g) (FiniteState.implies g f)

theorem eval_iffFormula {α P : Type} {k} (label : P → α)
    (child : Bool → P → P → Prop) (v : Fin k → P → Bool) (f g : Formula α k) :
    (iffFormula f g).EvalOn label child v ↔
      (f.EvalOn label child v ↔ g.EvalOn label child v) := by
  simp only [iffFormula,Formula.EvalOn,FiniteState.eval_implies]
  tauto

/-- Universal first-order closure, with no reserved or dummy vertex. -/
def closeAll {α : Type} {k} (f : Formula α k) : Formula α 0 := allBlock k f

theorem eval_closeAll {α P : Type} {k} (label : P → α)
    (child : Bool → P → P → Prop) (f : Formula α k) :
    (closeAll f).EvalOn label child Fin.elim0 ↔
      ∀ xs : Fin k → P, f.EvalOn label child (fun i => point (xs i)) := by
  rw [closeAll,eval_allBlock]
  have he (xs : Fin k → P) : Fin.append (fun i => point (xs i))
      (Fin.elim0 : Fin 0 → P → Bool) = (fun i => point (xs i)) := by
    simp
  simp only [he]

abbrev slotNumber {W : Nat} (i : Fin W) : Fin (W+1) := ⟨i.val+1,by omega⟩

noncomputable def slotPresent {colors relations W k} (v : Fin k) (i : Fin W) :
    Formula (Alphabet colors relations W) k :=
  labelTest v (fun a => i.val < a.toLabel.ports.length)

noncomputable def slotBits {colors relations W k} (v : Fin k) (i : Fin W)
    (r : Fin relations) (forward : Bool) : Formula (Alphabet colors relations W) k :=
  labelTest v (fun a => ∃ e, a.toLabel.ports[i.val]?=some e ∧ e.bit r forward=true)

noncomputable def adjacentFormula {α : Type} {relations : Nat}
    (rel : Fin relations → Formula α 2) : Formula α 2 :=
  disjoin ((Finset.univ : Finset (Fin relations)).toList.map
    (fun r => disjoin [rel r,atPair (rel r) 1 0]))

noncomputable def rootEmptyFormula {colors relations W}
    (parent : Formula (Alphabet colors relations W) 2) : Formula (Alphabet colors relations W) 0 :=
  closeAll (k:=1) (FiniteState.implies (.neg (.existsFirst (atPair parent 0 1)))
    (labelTest 0 (fun a => a.toLabel.ports=[])))

noncomputable def validSlotsFormula {colors relations W}
    (parent : Formula (Alphabet colors relations W) 2) : Formula (Alphabet colors relations W) 0 :=
  closeAll (k:=1) (allFinite (fun i : Fin W => FiniteState.implies (slotPresent 0 i)
    (.existsFirst (atPair (portRoute parent (slotNumber i)) 1 0))))

noncomputable def frontierSlotsFormula {colors relations W}
    (parent : Formula (Alphabet colors relations W) 2)
    (rel : Fin relations → Formula (Alphabet colors relations W) 2) :
    Formula (Alphabet colors relations W) 0 :=
  closeAll (k:=2) (iffFormula (inheritedFormula parent (adjacentFormula rel))
    (disjoin ((Finset.univ : Finset (Fin W)).toList.map (fun i =>
      .conj (slotPresent 0 i) (portRoute parent (slotNumber i))))))

noncomputable def orderedSlotsFormula {colors relations W}
    (parent order : Formula (Alphabet colors relations W) 2) : Formula (Alphabet colors relations W) 0 :=
  closeAll (k:=3) (allFinite (fun ij : Fin W × Fin W =>
    if ij.1.val < ij.2.val then
      FiniteState.implies (.conj (slotPresent 0 ij.2)
        (.conj (atPair (portRoute parent (slotNumber ij.1)) 0 1)
          (atPair (portRoute parent (slotNumber ij.2)) 0 2))) (atPair order 1 2)
    else truth))

noncomputable def bitsSlotsFormula {colors relations W}
    (parent : Formula (Alphabet colors relations W) 2)
    (rel : Fin relations → Formula (Alphabet colors relations W) 2) :
    Formula (Alphabet colors relations W) 0 :=
  closeAll (k:=2) (allFinite (fun irf : Fin W × Fin relations × Bool =>
    FiniteState.implies (.conj (slotPresent 0 irf.1) (portRoute parent (slotNumber irf.1)))
      (iffFormula (slotBits 0 irf.1 irf.2.1 irf.2.2)
        (if irf.2.2 then rel irf.2.1 else atPair (rel irf.2.1) 1 0))))

/-- Fixed finite syntax. It checks root support, every stored slot, all frontier
vertices, strict slot ordering and each directional bit, including all-zero
entries. Parent, order and graph relation formulas are explicit syntax inputs. -/
noncomputable def normalSlotsFormula {colors relations W}
    (parent order : Formula (Alphabet colors relations W) 2)
    (rel : Fin relations → Formula (Alphabet colors relations W) 2) :
    Formula (Alphabet colors relations W) 0 :=
  FiniteState.conjoin [rootEmptyFormula parent,validSlotsFormula parent,
    frontierSlotsFormula parent rel,orderedSlotsFormula parent order,bitsSlotsFormula parent rel]

#print axioms normalSlotsFormula
end StackSorting.FinitePort
