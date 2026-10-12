import FiniteQuotient
namespace StackSorting.FiniteGraph
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
variable {R : Type} [Lean.Grind.CommRing R]

theorem dot_sub_right {n} (v a b : Vec R n) :
    dot v (fun i => a i-b i)=dot v a-dot v b := by
  unfold dot
  have h : (fun i => v i*(a i-b i))=(fun i => v i*a i+ -(v i*b i)) := by
    funext i
    grind
  rw [h, sumFin_add, sumFin_neg]
  grind

theorem dot_neg_add_left {n} (a b v : Vec R n) :
    dot (fun i => -a i+b i) v= -dot a v+dot b v := by
  unfold dot
  have h : (fun i => (-a i+b i)*v i)=(fun i => -(a i*v i)+b i*v i) := by
    funext i
    grind
  rw [h, sumFin_add, sumFin_neg]

/-- Exact dual column recurrence for the original 6+19 residual action. -/
def dual19 (M : Letter → Mat R 6 6) (N : Letter → Mat R 19 19)
    (C : Letter → Mat R 6 19) (kappa : Vec R 6) (nu : Vec R 19) :
    List Letter → Vec R 6 × Vec R 19
  | [] => (kappa, nu)
  | a::w =>
    let col := dual19 M N C kappa nu w
    (fun i => mv (M a) col.1 i-mv (C a) col.2 i, mv (N a) col.2)

theorem run19_dual_evaluation (M : Letter → Mat R 6 6) (N : Letter → Mat R 19 19)
    (C : Letter → Mat R 6 19) (kappa : Vec R 6) (nu : Vec R 19)
    (w : List Letter) (row : Vec R 6 × Vec R 19) :
    terminal19 kappa nu (run19 M N C w row)=
      dot row.1 (dual19 M N C kappa nu w).1+dot row.2 (dual19 M N C kappa nu w).2 := by
  induction w generalizing row with
  | nil => rfl
  | cons a w ih =>
    rw [run19, ih]
    simp only [step19, dual19]
    rw [dot_neg_add_left, dot_vm, dot_vm, dot_vm, dot_sub_right]
    grind

#print axioms run19_dual_evaluation
end StackSorting.FiniteGraph
