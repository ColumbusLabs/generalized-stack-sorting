import IntegerExpression

/-! Exact finite integer polynomial arithmetic and Horner semantics in the
actual Cauchy FPS ring. Lists are low-degree first and are never trimmed. -/
namespace StackSorting.RationalLift
open StackSorting.CauchyRing
attribute [local instance] Lean.Grind.Ring.intCast

namespace IntPoly
abbrev Poly := List Int

def eval : Poly → FPS → FPS
  | [], _ => 0
  | c::cs, x => (c : FPS)+x*eval cs x

def add : Poly → Poly → Poly
  | [], q => q
  | p, [] => p
  | a::p, b::q => (a+b)::add p q

def scale (a : Int) (p : Poly) : Poly := p.map (a*·)

def mul : Poly → Poly → Poly
  | [], _ => []
  | a::p, q => add (scale a q) (0::mul p q)

def neg (p : Poly) : Poly := p.map (-·)

def pow (p : Poly) : Nat → Poly
  | 0 => [1]
  | k+1 => mul p (pow p k)

theorem eval_add (p q : Poly) (x : FPS) : eval (add p q) x=eval p x+eval q x := by
  induction p generalizing q with
  | nil => simp only [add, eval]; grind
  | cons a p ih =>
    cases q with
    | nil => simp only [add, eval]; grind
    | cons b q => simp only [add, eval, ih, Lean.Grind.Ring.intCast_add]; grind

theorem eval_scale (a : Int) (p : Poly) (x : FPS) : eval (scale a p) x=(a : FPS)*eval p x := by
  induction p with
  | nil => simp only [scale, List.map_nil, eval]; grind
  | cons b p ih =>
    change ((a*b : Int) : FPS)+x*eval (scale a p) x=(a : FPS)*((b : FPS)+x*eval p x)
    rw [ih, Lean.Grind.Ring.intCast_mul]
    grind

theorem eval_mul (p q : Poly) (x : FPS) : eval (mul p q) x=eval p x*eval q x := by
  induction p with
  | nil => simp only [mul, eval]; grind
  | cons a p ih => simp only [mul, eval_add, eval_scale, eval, ih]; grind

theorem eval_neg (p : Poly) (x : FPS) : eval (neg p) x= -eval p x := by
  induction p with
  | nil => simp only [neg, List.map_nil, eval]; grind
  | cons a p ih =>
    change ((-a : Int) : FPS)+x*eval (neg p) x= -((a : FPS)+x*eval p x)
    rw [ih, Lean.Grind.Ring.intCast_neg]
    grind

theorem eval_pow (p : Poly) (k : Nat) (x : FPS) : eval (pow p k) x=(eval p x)^k := by
  induction k with
  | zero => simp only [pow, eval]; grind
  | succ k ih => simp only [pow, eval_mul, ih]; grind

theorem eval_congr {p q : Poly} (h : p=q) (x : FPS) : eval p x=eval q x :=
  congrArg (fun p => eval p x) h
def zeroCheck : Poly → Bool
  | [] => true
  | c::p => decide (c=0) && zeroCheck p

theorem eval_zero {p : Poly} (h : zeroCheck p=true) (x : FPS) : eval p x=0 := by
  induction p with
  | nil => rfl
  | cons c p ih =>
    simp only [zeroCheck, Bool.and_eq_true, decide_eq_true_eq] at h
    simp only [eval, h.1, ih h.2]
    grind
end IntPoly

namespace BiPoly
abbrev Poly := List IntPoly.Poly

def eval : Poly → FPS → FPS → FPS
  | [], _, _ => 0
  | row::rows, x, y => IntPoly.eval row x+y*eval rows x y

def add : Poly → Poly → Poly
  | [], q => q
  | p, [] => p
  | a::p, b::q => IntPoly.add a b::add p q

def scale (row : IntPoly.Poly) (p : Poly) : Poly := p.map (IntPoly.mul row)

def mul : Poly → Poly → Poly
  | [], _ => []
  | row::p, q => add (scale row q) ([]::mul p q)

def neg (p : Poly) : Poly := p.map IntPoly.neg

def pow (p : Poly) : Nat → Poly
  | 0 => [[1]]
  | k+1 => mul p (pow p k)

theorem eval_add (p q : Poly) (x y : FPS) : eval (add p q) x y=eval p x y+eval q x y := by
  induction p generalizing q with
  | nil => simp only [add, eval]; grind
  | cons row p ih =>
    cases q with
    | nil => simp only [add, eval]; grind
    | cons other q => simp only [add, eval, IntPoly.eval_add, ih]; grind

theorem eval_scale (row : IntPoly.Poly) (p : Poly) (x y : FPS) :
    eval (scale row p) x y=IntPoly.eval row x*eval p x y := by
  induction p with
  | nil => simp only [scale, List.map_nil, eval]; grind
  | cons other p ih =>
    change IntPoly.eval (IntPoly.mul row other) x+y*eval (scale row p) x y=
      IntPoly.eval row x*(IntPoly.eval other x+y*eval p x y)
    rw [IntPoly.eval_mul, ih]
    grind

theorem eval_mul (p q : Poly) (x y : FPS) : eval (mul p q) x y=eval p x y*eval q x y := by
  induction p with
  | nil => simp only [mul, eval]; grind
  | cons row p ih => simp only [mul, eval_add, eval_scale, eval, IntPoly.eval, ih]; grind

theorem eval_neg (p : Poly) (x y : FPS) : eval (neg p) x y= -eval p x y := by
  induction p with
  | nil => simp only [neg, List.map_nil, eval]; grind
  | cons row p ih =>
    change IntPoly.eval (IntPoly.neg row) x+y*eval (neg p) x y=
      -(IntPoly.eval row x+y*eval p x y)
    rw [IntPoly.eval_neg, ih]
    grind

theorem eval_pow (p : Poly) (k : Nat) (x y : FPS) : eval (pow p k) x y=(eval p x y)^k := by
  induction k with
  | zero => simp only [pow, eval, IntPoly.eval]; grind
  | succ k ih => simp only [pow, eval_mul, ih]; grind

theorem eval_integer (n : Int) (x y : FPS) : eval [[n]] x y=(n : FPS) := by
  simp only [eval, IntPoly.eval]
  grind

theorem eval_congr {p q : Poly} (h : p=q) (x y : FPS) : eval p x y=eval q x y :=
  congrArg (fun p => eval p x y) h
def zeroCheck : Poly → Bool
  | [] => true
  | row::p => IntPoly.zeroCheck row && zeroCheck p

theorem eval_zero {p : Poly} (h : zeroCheck p=true) (x y : FPS) : eval p x y=0 := by
  induction p with
  | nil => rfl
  | cons row p ih =>
    simp only [zeroCheck, Bool.and_eq_true] at h
    simp only [eval, IntPoly.eval_zero h.1, ih h.2]
    grind

theorem eval_eq_of_zeroDifference (p q : Poly)
    (h : zeroCheck (add p (neg q))=true) (x y : FPS) : eval p x y=eval q x y := by
  have hz := eval_zero h x y
  rw [eval_add, eval_neg] at hz
  grind
end BiPoly

def IExpr.toBi (env : Nat → BiPoly.Poly) : IExpr → BiPoly.Poly
  | .integer n => [[n]]
  | .var n => env n
  | .add a b => BiPoly.add (a.toBi env) (b.toBi env)
  | .mul a b => BiPoly.mul (a.toBi env) (b.toBi env)
  | .pow a k => BiPoly.pow (a.toBi env) k

theorem IExpr.eval_toBi (env : Nat → BiPoly.Poly) (e : IExpr) (x y : FPS) :
    BiPoly.eval (e.toBi env) x y=e.eval (fun n => BiPoly.eval (env n) x y) := by
  induction e with
  | integer n => exact BiPoly.eval_integer n x y
  | var n => rfl
  | add a b ha hb => simp only [toBi, eval, BiPoly.eval_add, ha, hb]
  | mul a b ha hb => simp only [toBi, eval, BiPoly.eval_mul, ha, hb]
  | pow a k ha => simp only [toBi, eval, BiPoly.eval_pow, ha]

/-- A literal, kernel-checked list equality yields an actual FPS identity. -/
theorem IExpr.eq_of_toBi_eq (env : Nat → BiPoly.Poly) (a b : IExpr)
    (h : a.toBi env=b.toBi env) (x y : FPS) :
    a.eval (fun n => BiPoly.eval (env n) x y)=b.eval (fun n => BiPoly.eval (env n) x y) := by
  rw [←IExpr.eval_toBi, ←IExpr.eval_toBi, h]

#print axioms IntPoly.eval_mul
#print axioms BiPoly.eval_mul
#print axioms IExpr.eval_toBi
#print axioms IExpr.eq_of_toBi_eq
end StackSorting.RationalLift
