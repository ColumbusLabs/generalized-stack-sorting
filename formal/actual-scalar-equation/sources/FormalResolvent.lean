import FiniteMatrix

namespace StackSorting.FiniteGraph
open StackSorting.CauchyRing StackSorting.ProperSeries
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

theorem X_mul_coeff (a : FPS) : (X*a).coeff = shift a.coeff := by
  funext n
  cases n with
  | zero =>
    change cauchy X.coeff a.coeff 0 = 0
    rw [cauchy_zero]
    change (0 : Rat)*a 0 = 0
    exact Rat.zero_mul _
  | succ n =>
    change cauchy X.coeff a.coeff (n+1) = a n
    rw [cauchy_head]
    have ht : (fun k => X.coeff (k+1)) = const 1 := by
      funext k
      simp only [X, const]
      by_cases h : k=0
      · subst k; rfl
      · have hh : k+1 ≠ 1 := by omega
        simp only [h, hh, ite_false]
    rw [ht, cauchy_const_left]
    change 0*a (n+1)+1*a n = a n
    grind

theorem sumFin_coeff {n} (f : Vec FPS n) (k : Nat) :
    (sumFin f) k = sumFin (fun i => f i k) := by
  induction n with
  | zero =>
    change const 0 k=0
    unfold const
    split <;> rfl
  | succ n ih => simp only [sumFin, add_apply, ih]

theorem product_coeff_zero (a b : FPS) (n : Nat) (hb : ∀ k, k≤n → b k=0) : (a*b) n=0 := by
  change sumTerms (fun k => a k*b (n-k)) (n+1)=0
  calc
    _ = sumTerms (fun _ => (0:Rat)) (n+1) := by
      apply sumTerms_congr
      intro k hk
      rw [hb (n-k) (Nat.sub_le _ _)]
      exact Rat.mul_zero _
    _ = 0 := sum_zero _

theorem mv_coeff_zero (T : Mat FPS 6 6) (u : Vec FPS 6) (n : Nat)
    (hu : ∀ i k, k≤n → u i k=0) (i : Fin 6) : mv T u i n=0 := by
  unfold mv
  rw [sumFin_coeff]
  have h : (fun j => (T i j*u j) n) = (fun _ => (0:Rat)) := by
    funext j
    exact product_coeff_zero (T i j) (u j) n (hu j)
  rw [h, sumFin_zero]

/-- The formal matrix I-XT is injective for every coefficientwise matrix T. -/
theorem proper_matrix_injective (T : Mat FPS 6 6) (u : Vec FPS 6)
    (hu : ∀ i, u i=X*mv T u i) : u=(fun _ => 0) := by
  have hall : ∀ n i, u i n=0 := by
    intro n
    induction n using Nat.strongRecOn with
    | ind n ih =>
      intro i
      have hc := congrArg FPS.coeff (hu i)
      rw [X_mul_coeff] at hc
      have hc' := congrFun hc n
      cases n with
      | zero => exact hc'
      | succ n =>
        change u i (n+1)=mv T u i n at hc'
        rw [hc']
        apply mv_coeff_zero T u n
        intro j k hk
        exact ih k (by omega) j
  funext i
  apply FPS.ext
  funext n
  change u i n=const 0 n
  rw [hall n i]
  unfold const
  split <;> rfl

variable {R : Type} [Lean.Grind.CommRing R]

theorem mv_add {m n} (A : Mat R m n) (v w : Vec R n) :
    mv A (fun i => v i+w i) = fun i => mv A v i+mv A w i := by
  funext i
  unfold mv
  rw [←sumFin_add]
  apply sumFin_congr
  intro j
  grind

theorem mv_sub {m n} (A : Mat R m n) (v w : Vec R n) :
    mv A (fun i => v i-w i) = fun i => mv A v i-mv A w i := by
  funext i
  unfold mv
  have h : (fun j => A i j*(v j-w j)) = (fun j => A i j*v j + -(A i j*w j)) := by
    funext j
    grind
  rw [h, sumFin_add, sumFin_neg]
  grind

theorem mv_scale {m n} (A : Mat R m n) (s : R) (v : Vec R n) :
    mv A (fun i => s*v i) = fun i => s*mv A v i := by
  funext i
  unfold mv
  rw [←mul_sumFin]
  apply sumFin_congr
  intro j
  grind

/-- Six displayed scalar equations plus the genuine record resolvent imply
terminal annihilation. No graph-terminal identity is assumed here. -/
theorem scalar_equations_terminal (T K : Mat FPS 6 6) (beta r : Vec FPS 6)
    (hrec : ∀ i, r i=beta i+X*mv T r i)
    (hscalar : ∀ i, (beta i+mv K beta i)-X*mv T (fun j => beta j+mv K beta j) i-X*beta i=0) :
    ∀ i, beta i-X*r i+mv K beta i=0 := by
  let u : Vec FPS 6 := fun i => (beta i+mv K beta i)-X*r i
  have hu : ∀ i, u i=X*mv T u i := by
    intro i
    dsimp [u]
    rw [mv_sub, mv_scale]
    have hr := hrec i
    have hs := hscalar i
    grind
  have hz := proper_matrix_injective T u hu
  intro i
  have hi := congrFun hz i
  dsimp [u] at hi
  grind

/-- The six scalar equations construct the resolvent without an existence premise. -/
def recordFromScalar (T K : Mat R 6 6) (beta : Vec R 6) : Vec R 6 :=
  fun i => beta i+mv T (fun j => beta j+mv K beta j) i

theorem scalar_constructs_record (x : R) (T K : Mat R 6 6) (beta : Vec R 6)
    (hscalar : ∀ i, (beta i+mv K beta i)-x*mv T (fun j => beta j+mv K beta j) i-x*beta i=0) :
    (∀ i, x*recordFromScalar T K beta i=beta i+mv K beta i) ∧
    (∀ i, recordFromScalar T K beta i=beta i+x*mv T (recordFromScalar T K beta) i) := by
  have hx : ∀ i, x*recordFromScalar T K beta i=beta i+mv K beta i := by
    intro i
    have h := hscalar i
    dsimp [recordFromScalar]
    grind
  refine ⟨hx, ?_⟩
  intro i
  have heq : (fun j => beta j+mv K beta j) =
      (fun j => x*recordFromScalar T K beta j) := funext (fun j => (hx j).symm)
  change beta i+mv T (fun j => beta j+mv K beta j) i=_
  rw [heq, mv_scale]

theorem scalar_constructs_terminal (x : R) (T K : Mat R 6 6) (beta : Vec R 6)
    (hscalar : ∀ i, (beta i+mv K beta i)-x*mv T (fun j => beta j+mv K beta j) i-x*beta i=0) :
    ∀ i, beta i-x*recordFromScalar T K beta i+mv K beta i=0 := by
  intro i
  have h := (scalar_constructs_record x T K beta hscalar).1 i
  grind

#print axioms scalar_constructs_record
#print axioms scalar_constructs_terminal
#print axioms proper_matrix_injective
#print axioms scalar_equations_terminal
end StackSorting.FiniteGraph
