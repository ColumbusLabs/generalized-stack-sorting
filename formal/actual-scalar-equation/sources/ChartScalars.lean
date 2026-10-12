import GraphLiterals
import FormalResolvent
noncomputable section
namespace StackSorting.FiniteGraph
set_option maxRecDepth 16384
set_option maxHeartbeats 8000000
variable {R : Type} [Lean.Grind.CommRing R]

/-- Exactly the six vector equations from the explicit seven-equation system. -/
def SixScalarEquations (y : Chart R) (x : R) (beta : Vec R 6) : Prop :=
  ∀ i, (beta i+mv (litK y) beta i)-
    x*mv (litT y) (fun j => beta j+mv (litK y) beta j) i-x*beta i=0

def kappa (y : Chart R) (x : R) (beta : Vec R 6) : Vec R 6 :=
  fun i => beta i-x*recordFromScalar (litT y) (litK y) beta i

def normalizedDirection (y : Chart R) (denInverse : R) : Vec R 6 :=
  betaDirection y denInverse

def normalizedScale (denInverse normInverse : R) : R := 2*normInverse*denInverse

theorem direction_zero (y : Chart R) : litdirection y 0 0=litden y 0 0 := rfl

theorem normalized_direction_zero (y : Chart R) (denInverse : R)
    (hd : litden y 0 0*denInverse=1) : normalizedDirection y denInverse 0=1 := by
  dsimp [normalizedDirection, betaDirection, exprEval, chartVars]
  rw [direction_zero]
  grind

theorem scale_direction (y : Chart R) (a b : R) :
    betaDirection y (a*b)=fun i => a*betaDirection y b i := by
  funext i
  dsimp [betaDirection, exprEval, chartVars]
  grind

theorem scalar_equations_scale (y : Chart R) (x a : R) (v : Vec R 6)
    (hs : SixScalarEquations y x v) : SixScalarEquations y x (fun i => a*v i) := by
  intro i
  change a*v i+mv (litK y) (fun j => a*v j) i-
    x*mv (litT y) (fun j => a*v j+mv (litK y) (fun k => a*v k) j) i-x*(a*v i)=0
  rw [mv_scale]
  have hv : (fun j => a*v j+a*mv (litK y) v j) =
      (fun j => a*(v j+mv (litK y) v j)) := by funext j; grind
  rw [hv, mv_scale]
  have h := hs i
  grind

theorem normalized_beta_relation (y : Chart R) (x denInverse normInverse : R)
    (hd : litden y 0 0*denInverse=1)
    (hn : (1-x*normalizedDirection y denInverse 2)*normInverse=1) :
    betaDirection y (normalizedScale denInverse normInverse) 0-
      x*betaDirection y (normalizedScale denInverse normInverse) 2=2 := by
  have h0 := normalized_direction_zero y denInverse hd
  dsimp [normalizedScale, exprEval, chartVars]
  rw [scale_direction]
  change 2*normInverse*normalizedDirection y denInverse 0-
    x*(2*normInverse*normalizedDirection y denInverse 2)=2
  rw [h0]
  grind

/-- The exact seven rational equations, in the normalized direction. -/
def SevenScalarEquations (y : Chart R) (x : R) (v : Vec R 6) : Prop :=
  SixScalarEquations y x v ∧
    dot (litalpha y 0) (mv (litK y) v)-mv (litK y) v 0=0


theorem dot_scale_right {n} (v w : Vec R n) (a : R) :
    dot v (fun i => a*w i)=a*dot v w := by
  unfold dot
  rw [←mul_sumFin]
  apply sumFin_congr
  intro i
  grind

theorem seven_equations_scale (y : Chart R) (x a : R) (v : Vec R 6)
    (hs : SevenScalarEquations y x v) : SevenScalarEquations y x (fun i => a*v i) := by
  refine ⟨scalar_equations_scale y x a v hs.1, ?_⟩
  rw [mv_scale, dot_scale_right]
  have h := hs.2
  grind

end StackSorting.FiniteGraph
