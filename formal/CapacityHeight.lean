import CompleteGrammar

/-! Physical occupancy of the exact compressed operation word. A bypass has a
transient extra token, even though its final held size is unchanged. These
predicates do not replace the existing slot/flag legality semantics. -/
namespace StackSorting.Capacity
open StackSorting FirstReturn

def nextHeight (op : Op) (h : Nat) : Nat := match op with
  | .bypass => h
  | .push0 | .push1 => h + 1
  | .pop0 | .pop1 => h - 1

def endHeight : List Op → Nat → Nat
  | [], h => h
  | op :: ops, h => endHeight ops (nextHeight op h)

def Fits (H : Nat) : List Op → Nat → Prop
  | [], h => h ≤ H
  | op :: ops, h => h ≤ H ∧ match op with
    | .bypass => h + 1 ≤ H ∧ Fits H ops h
    | .push0 | .push1 => Fits H ops (h + 1)
    | .pop0 | .pop1 => 0 < h ∧ Fits H ops (h - 1)

instance fitsDecidable (H : Nat) : (ops : List Op) → (h : Nat) → Decidable (Fits H ops h)
  | [], h => inferInstanceAs (Decidable (h ≤ H))
  | op :: ops, h => by
      letI := fitsDecidable H ops h
      letI := fitsDecidable H ops (h + 1)
      letI := fitsDecidable H ops (h - 1)
      cases op <;> simp only [Fits] <;> exact inferInstance

theorem fits_initial {H h : Nat} {ops : List Op} (hf : Fits H ops h) : h ≤ H := by
  cases ops with
  | nil => exact hf
  | cons op ops => exact hf.1

theorem endHeight_append (xs ys : List Op) (h : Nat) :
    endHeight (xs ++ ys) h = endHeight ys (endHeight xs h) := by
  induction xs generalizing h with
  | nil => rfl
  | cons op xs ih => exact ih _

theorem fits_append (H : Nat) (xs ys : List Op) (h : Nat) :
    Fits H (xs ++ ys) h ↔ Fits H xs h ∧ Fits H ys (endHeight xs h) := by
  induction xs generalizing h with
  | nil =>
      simp only [List.nil_append, Fits, endHeight]
      exact ⟨fun hy => ⟨fits_initial hy, hy⟩, fun hy => hy.2⟩
  | cons op xs ih =>
      cases op <;> simp [Fits, endHeight, nextHeight, ih, and_assoc]

def treeExtra : Tree → Nat
  | .pop0 | .pop1 => 0
  | .bypass t => max 1 (treeExtra t)
  | .push0 s t | .push1 s t => max (1 + treeExtra s) (treeExtra t)

def pathPeak : Path → Nat
  | .nil => 0
  | .bypass p => max 1 (pathPeak p)
  | .push t p => max (1 + treeExtra t) (pathPeak p)

theorem endHeight_tree (t : Tree) (h : Nat) :
    endHeight (encode t) (h+1) = h := by
  induction t generalizing h with
  | pop0 | pop1 => simp [encode, endHeight, nextHeight]
  | bypass t ih => simpa [encode, endHeight, nextHeight] using ih h
  | push0 s t ihs iht | push1 s t ihs iht =>
      simp only [encode, endHeight, nextHeight, endHeight_append]
      rw [ihs, iht]

theorem fits_tree (t : Tree) (H h : Nat) :
    Fits H (encode t) (h+1) ↔ h+1+treeExtra t ≤ H := by
  induction t generalizing h with
  | pop0 | pop1 => simp [encode, Fits, treeExtra]; omega
  | bypass t ih =>
      simp only [encode, Fits, treeExtra, ih]
      omega
  | push0 s t ihs iht | push1 s t ihs iht =>
      simp only [encode, Fits, fits_append, endHeight_tree, treeExtra, ihs, iht]
      omega

theorem endHeight_path (p : Path) : endHeight (pathEncode p) 0 = 0 := by
  induction p with
  | nil => rfl
  | bypass p ih => simpa [pathEncode, endHeight, nextHeight] using ih
  | push t p ih =>
      simp only [pathEncode, endHeight, nextHeight, endHeight_append]
      rw [endHeight_tree, ih]

theorem fits_path (p : Path) (H : Nat) :
    Fits H (pathEncode p) 0 ↔ pathPeak p ≤ H := by
  induction p with
  | nil => simp [pathEncode, Fits, pathPeak]
  | bypass p ih => simp [pathEncode, Fits, pathPeak, ih, Nat.max_le]
  | push t p ih =>
      simp only [pathEncode, Fits, fits_append, endHeight_tree, fits_tree,
        pathPeak, ih]
      omega

#print axioms fits_tree
#print axioms fits_path
end StackSorting.Capacity
