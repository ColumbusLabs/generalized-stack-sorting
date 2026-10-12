import ConcreteExpression

namespace StackSorting.ConcreteEquation
open StackSorting.ProperSeries
namespace QPoly
abbrev Poly := List Rat

def eval : Poly → Rat → Rat
  | [], _ => 0
  | c::cs, x => c + x * eval cs x

def add : Poly → Poly → Poly
  | [], q => q
  | p, [] => p
  | a::p, b::q => (a+b)::add p q

def scale (a : Rat) (p : Poly) : Poly := p.map (a * ·)

def mul : Poly → Poly → Poly
  | [], _ => []
  | a::p, q => add (scale a q) (0::mul p q)

def neg (p : Poly) : Poly := p.map (- ·)

def expression : Poly → Expr
  | [] => .scalar 0
  | c::cs => .add (.scalar c) (.mul .x (expression cs))

theorem eval_add (p q : Poly) (x : Rat) : eval (add p q) x = eval p x + eval q x := by
  induction p generalizing q with
  | nil => simp only [add, eval]; grind
  | cons a p ih =>
    cases q with
    | nil => simp only [add, eval]; grind
    | cons b q => simp only [add, eval, ih]; grind

theorem eval_scale (a : Rat) (p : Poly) (x : Rat) : eval (scale a p) x = a * eval p x := by
  induction p with
  | nil => simp only [scale, List.map_nil, eval]; grind
  | cons b p ih =>
    change a*b+x*eval (scale a p) x = a*(b+x*eval p x)
    rw [ih]
    grind

theorem eval_mul (p q : Poly) (x : Rat) : eval (mul p q) x = eval p x * eval q x := by
  induction p with
  | nil => simp only [mul, eval]; grind
  | cons a p ih => simp only [mul, eval_add, eval_scale, eval, ih]; grind

theorem eval_neg (p : Poly) (x : Rat) : eval (neg p) x = -(eval p x) := by
  induction p with
  | nil => simp only [neg, List.map_nil, eval]; grind
  | cons a p ih =>
    change -a+x*eval (neg p) x = -(a+x*eval p x)
    rw [ih]
    grind

theorem expression_eval (p : Poly) (x : Rat) (u : Fin 7 → Rat) :
    pointEval (expression p) x u = eval p x := by
  induction p with
  | nil => rfl
  | cons a p ih => simp only [expression, pointEval, eval, ih]

theorem eval_take_drop (n : Nat) (p : Poly) (x : Rat) :
    eval p x = eval (p.take n) x + x^n * eval (p.drop n) x := by
  induction n generalizing p with
  | zero => simp only [List.take_zero, List.drop_zero, eval]; grind
  | succ n ih =>
    cases p with
    | nil => simp only [List.take_nil, List.drop_nil, eval]; grind
    | cons a p =>
      simp only [List.take_succ_cons, List.drop_succ_cons, eval]
      rw [ih p]
      grind
end QPoly

/-- A finite low polynomial and an exact high polynomial expression. -/
structure Split where
  low : QPoly.Poly
  high : Expr

def splitPolynomial (n : Nat) (p : QPoly.Poly) : Split :=
  ⟨p.take n, QPoly.expression (p.drop n)⟩

/-- A polynomial substitution with exact x^n remainder. Only the low side
uses rational normalization; the high side stays a finite expression. -/
def splitAt (n : Nat) (b : Fin 7 → QPoly.Poly) : Expr → Split
  | .scalar c => splitPolynomial n [c]
  | .x => splitPolynomial n [0,1]
  | .unknown i => splitPolynomial n (b i)
  | .add a c =>
      let aa := splitAt n b a
      let cc := splitAt n b c
      ⟨QPoly.add aa.low cc.low, .add aa.high cc.high⟩
  | .mul a c =>
      let aa := splitAt n b a
      let cc := splitAt n b c
      let prod := QPoly.mul aa.low cc.low
      ⟨prod.take n, .add (QPoly.expression (prod.drop n))
        (.add (.mul aa.high (substitute c (fun i => QPoly.expression (b i))))
          (.mul (QPoly.expression aa.low) cc.high))⟩
  | .neg a =>
      let aa := splitAt n b a
      ⟨QPoly.neg aa.low, .neg aa.high⟩

theorem substitute_eval (e : Expr) (v : Fin 7 → Expr) (x : Rat) (u : Fin 7 → Rat) :
    pointEval (substitute e v) x u = pointEval e x (fun i => pointEval (v i) x u) := by
  induction e with
  | scalar c => rfl
  | x => rfl
  | unknown i => rfl
  | add a b ha hb => simp only [substitute, pointEval, ha, hb]
  | mul a b ha hb => simp only [substitute, pointEval, ha, hb]
  | neg a ha => simp only [substitute, pointEval, ha]

theorem splitAt_exact (n : Nat) (b : Fin 7 → QPoly.Poly) (e : Expr)
    (x : Rat) (u : Fin 7 → Rat) :
    pointEval e x (fun i => QPoly.eval (b i) x) =
      QPoly.eval (splitAt n b e).low x + x^n * pointEval (splitAt n b e).high x u := by
  induction e with
  | scalar c =>
    simp only [pointEval, splitAt, splitPolynomial, QPoly.expression_eval]
    have h := QPoly.eval_take_drop n [c] x
    simp only [QPoly.eval] at h
    grind
  | x =>
    simp only [pointEval, splitAt, splitPolynomial, QPoly.expression_eval]
    have h := QPoly.eval_take_drop n [0,1] x
    simp only [QPoly.eval] at h
    grind
  | unknown i =>
    simp only [pointEval, splitAt, splitPolynomial, QPoly.expression_eval]
    exact QPoly.eval_take_drop n (b i) x
  | add a c ha hc =>
    simp only [pointEval, splitAt, QPoly.eval_add]
    grind
  | mul a c ha hc =>
    simp only [pointEval, splitAt, QPoly.expression_eval, substitute_eval]
    have h := QPoly.eval_take_drop n
      (QPoly.mul (splitAt n b a).low (splitAt n b c).low) x
    rw [QPoly.eval_mul] at h
    grind
  | neg a ha =>
    simp only [pointEval, splitAt, QPoly.eval_neg]
    grind

/-- A kernel-checked zero low coefficient list makes the generated high
expression an exact polynomial division witness. -/
theorem splitAt_divisible (n : Nat) (b : Fin 7 → QPoly.Poly) (e : Expr)
    (h : (splitAt n b e).low = List.replicate n 0)
    (x : Rat) (u : Fin 7 → Rat) :
    pointEval e x (fun i => QPoly.eval (b i) x) =
      x^n * pointEval (splitAt n b e).high x u := by
  have hz : ∀ m, QPoly.eval (List.replicate m 0) x = 0 := by
    intro m
    induction m with
    | zero => rfl
    | succ n ih => simp only [List.replicate_succ, QPoly.eval, ih]; grind
  rw [splitAt_exact n b e x u, h, hz n, Rat.zero_add]

#print axioms splitAt_exact
#print axioms splitAt_divisible
end StackSorting.ConcreteEquation
