import CauchyRing
import UnivariateDivision

namespace StackSorting.SeriesPolynomialSemantics
open StackSorting.ProperSeries StackSorting.ConcreteEquation StackSorting.CauchyRing
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

@[simp] theorem C_numeral (n : Nat) : C (OfNat.ofNat (α := Rat) n) = OfNat.ofNat (α := FPS) n := rfl

@[simp] theorem C_nat (n : Nat) : C (n : Rat) = (n : FPS) := rfl
@[simp] theorem C_int (n : Int) : C (n : Rat) = (n : FPS) := rfl

def ringEval {I : Type} (e : PolyExpr I Rat) (x : FPS) (u : I → FPS) : FPS :=
  match e with
  | .scalar c => C c
  | .x => x
  | .unknown i => u i
  | .add a b => ringEval a x u + ringEval b x u
  | .mul a b => ringEval a x u * ringEval b x u
  | .neg a => -(ringEval a x u)

def polyEval : QPoly.Poly → FPS → FPS
  | [], _ => 0
  | c::cs, x => C c+x*polyEval cs x

theorem polyEval_add (p q : QPoly.Poly) (x : FPS) :
    polyEval (QPoly.add p q) x = polyEval p x+polyEval q x := by
  induction p generalizing q with
  | nil => simp only [QPoly.add, polyEval]; grind
  | cons a p ih =>
    cases q with
    | nil => simp only [QPoly.add, polyEval]; grind
    | cons b q => simp only [QPoly.add, polyEval, C_add, ih]; grind

theorem polyEval_scale (r : Rat) (p : QPoly.Poly) (x : FPS) :
    polyEval (QPoly.scale r p) x = C r*polyEval p x := by
  induction p with
  | nil => simp only [QPoly.scale, List.map_nil, polyEval]; grind
  | cons a p ih =>
    change C (r*a)+x*polyEval (QPoly.scale r p) x = C r*(C a+x*polyEval p x)
    rw [C_mul, ih]
    grind

theorem polyEval_mul (p q : QPoly.Poly) (x : FPS) :
    polyEval (QPoly.mul p q) x = polyEval p x*polyEval q x := by
  induction p with
  | nil => simp only [QPoly.mul, polyEval]; grind
  | cons a p ih => simp only [QPoly.mul, polyEval_add, polyEval_scale, polyEval, C_zero, ih]; grind

theorem polyEval_neg (p : QPoly.Poly) (x : FPS) :
    polyEval (QPoly.neg p) x = -(polyEval p x) := by
  induction p with
  | nil => simp only [QPoly.neg, List.map_nil, polyEval]; grind
  | cons a p ih =>
    change C (-a)+x*polyEval (QPoly.neg p) x = -(C a+x*polyEval p x)
    rw [C_neg, ih]
    grind

theorem polyEval_take_drop (n : Nat) (p : QPoly.Poly) (x : FPS) :
    polyEval p x = polyEval (p.take n) x+x^n*polyEval (p.drop n) x := by
  induction n generalizing p with
  | zero => simp only [List.take_zero, List.drop_zero, polyEval]; grind
  | succ n ih =>
    cases p with
    | nil => simp only [List.take_nil, List.drop_nil, polyEval]; grind
    | cons a p =>
      simp only [List.take_succ_cons, List.drop_succ_cons, polyEval]
      rw [ih p]
      grind

theorem expression_ringEval (p : QPoly.Poly) (x : FPS) (u : Fin 7 → FPS) :
    ringEval (QPoly.expression p) x u = polyEval p x := by
  induction p with
  | nil => rfl
  | cons a p ih => simp only [QPoly.expression, ringEval, polyEval, ih]

theorem substitute_ringEval (e : Expr) (v : Fin 7 → Expr) (x : FPS) (u : Fin 7 → FPS) :
    ringEval (substitute e v) x u = ringEval e x (fun i => ringEval (v i) x u) := by
  induction e with
  | scalar c => rfl
  | x => rfl
  | unknown i => rfl
  | add a b ha hb => simp only [substitute, ringEval, ha, hb]
  | mul a b ha hb => simp only [substitute, ringEval, ha, hb]
  | neg a ha => simp only [substitute, ringEval, ha]

/-- The same finite rational splitter is sound for Cauchy-product formal
series, not only for point evaluations over the rationals. -/
theorem splitAt_ring_exact (n : Nat) (b : Fin 7 → QPoly.Poly) (e : Expr)
    (x : FPS) (u : Fin 7 → FPS) :
    ringEval e x (fun i => polyEval (b i) x) =
      polyEval (splitAt n b e).low x+x^n*ringEval (splitAt n b e).high x u := by
  induction e with
  | scalar c =>
    simp only [ringEval, splitAt, splitPolynomial, expression_ringEval]
    have h := polyEval_take_drop n [c] x
    simp only [polyEval] at h
    grind
  | x =>
    simp only [ringEval, splitAt, splitPolynomial, expression_ringEval]
    have h := polyEval_take_drop n [0,1] x
    simp only [polyEval, C_zero, C_one] at h
    grind
  | unknown i =>
    simp only [ringEval, splitAt, splitPolynomial, expression_ringEval]
    exact polyEval_take_drop n (b i) x
  | add a c ha hc =>
    simp only [ringEval, splitAt, polyEval_add]
    grind
  | mul a c ha hc =>
    simp only [ringEval, splitAt, expression_ringEval, substitute_ringEval]
    have h := polyEval_take_drop n
      (QPoly.mul (splitAt n b a).low (splitAt n b c).low) x
    rw [polyEval_mul] at h
    grind
  | neg a ha =>
    simp only [ringEval, splitAt, polyEval_neg]
    grind

theorem polyEval_zeros (n : Nat) (x : FPS) : polyEval (List.replicate n 0) x = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [List.replicate_succ, polyEval, C_zero, ih]; grind

theorem splitAt_ring_divisible (n : Nat) (b : Fin 7 → QPoly.Poly) (e : Expr)
    (h : (splitAt n b e).low = List.replicate n 0)
    (x : FPS) (u : Fin 7 → FPS) :
    ringEval e x (fun i => polyEval (b i) x) =
      x^n*ringEval (splitAt n b e).high x u := by
  rw [splitAt_ring_exact n b e x u, h, polyEval_zeros]
  grind

/-- Literal identification with the coefficient semantics used by the
proper fixed-point theorem. -/
theorem ringEval_coefficient_semantics {I : Type} (e : PolyExpr I Rat) (a : Family I Rat) :
    (ringEval e X (fun i => ⟨a i⟩)).coeff = e.eval a := by
  induction e with
  | scalar c => rfl
  | x => rfl
  | unknown i => rfl
  | add e f he hf =>
    change (fun n => (ringEval e X (fun i => ⟨a i⟩)).coeff n+
      (ringEval f X (fun i => ⟨a i⟩)).coeff n) = _
    rw [he, hf]
    rfl
  | mul e f he hf =>
    change cauchy (ringEval e X (fun i => ⟨a i⟩)).coeff
      (ringEval f X (fun i => ⟨a i⟩)).coeff = _
    rw [he, hf]
    rfl
  | neg e he =>
    change (fun n => -((ringEval e X (fun i => ⟨a i⟩)).coeff n)) = _
    rw [he]
    rfl

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
        simp only [h, hh, if_false]
    rw [ht, cauchy_const_left]
    change 0*a (n+1)+1*a n = a n
    grind

#print axioms splitAt_ring_exact
#print axioms ringEval_coefficient_semantics
#print axioms X_mul_coeff
end StackSorting.SeriesPolynomialSemantics
