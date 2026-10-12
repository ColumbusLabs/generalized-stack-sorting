import ScalarBranchUnique

namespace StackSorting.ConcreteScalar
open StackSorting.ProperSeries StackSorting.ConcreteEquation StackSorting.CauchyRing
open StackSorting.SeriesPolynomialSemantics
set_option maxRecDepth 10000
set_option maxHeartbeats 10000000

/-- Direct sparse reification of all 69 [x-degree,G-degree,integer] input
terms. No Horner regrouping occurs in this definition. -/
def literalQ : Expr := sumExpr [
  .mul (.scalar (-8100 : Rat)) (.mul (powExpr .x 0) (powExpr (.unknown ⟨0, by decide⟩) 0)),
  .mul (.scalar (-11016 : Rat)) (.mul (powExpr .x 1) (powExpr (.unknown ⟨0, by decide⟩) 0)),
  .mul (.scalar (80028 : Rat)) (.mul (powExpr .x 2) (powExpr (.unknown ⟨0, by decide⟩) 0)),
  .mul (.scalar (51444 : Rat)) (.mul (powExpr .x 0) (powExpr (.unknown ⟨0, by decide⟩) 1)),
  .mul (.scalar (18252 : Rat)) (.mul (powExpr .x 1) (powExpr (.unknown ⟨0, by decide⟩) 1)),
  .mul (.scalar (-467820 : Rat)) (.mul (powExpr .x 2) (powExpr (.unknown ⟨0, by decide⟩) 1)),
  .mul (.scalar (121212 : Rat)) (.mul (powExpr .x 3) (powExpr (.unknown ⟨0, by decide⟩) 1)),
  .mul (.scalar (-140841 : Rat)) (.mul (powExpr .x 0) (powExpr (.unknown ⟨0, by decide⟩) 2)),
  .mul (.scalar (94788 : Rat)) (.mul (powExpr .x 1) (powExpr (.unknown ⟨0, by decide⟩) 2)),
  .mul (.scalar (1068822 : Rat)) (.mul (powExpr .x 2) (powExpr (.unknown ⟨0, by decide⟩) 2)),
  .mul (.scalar (-349236 : Rat)) (.mul (powExpr .x 3) (powExpr (.unknown ⟨0, by decide⟩) 2)),
  .mul (.scalar (47583 : Rat)) (.mul (powExpr .x 4) (powExpr (.unknown ⟨0, by decide⟩) 2)),
  .mul (.scalar (216756 : Rat)) (.mul (powExpr .x 0) (powExpr (.unknown ⟨0, by decide⟩) 3)),
  .mul (.scalar (-381312 : Rat)) (.mul (powExpr .x 1) (powExpr (.unknown ⟨0, by decide⟩) 3)),
  .mul (.scalar (-1228464 : Rat)) (.mul (powExpr .x 2) (powExpr (.unknown ⟨0, by decide⟩) 3)),
  .mul (.scalar (-13248 : Rat)) (.mul (powExpr .x 3) (powExpr (.unknown ⟨0, by decide⟩) 3)),
  .mul (.scalar (67968 : Rat)) (.mul (powExpr .x 4) (powExpr (.unknown ⟨0, by decide⟩) 3)),
  .mul (.scalar (5220 : Rat)) (.mul (powExpr .x 5) (powExpr (.unknown ⟨0, by decide⟩) 3)),
  .mul (.scalar (-204775 : Rat)) (.mul (powExpr .x 0) (powExpr (.unknown ⟨0, by decide⟩) 4)),
  .mul (.scalar (609666 : Rat)) (.mul (powExpr .x 1) (powExpr (.unknown ⟨0, by decide⟩) 4)),
  .mul (.scalar (816316 : Rat)) (.mul (powExpr .x 2) (powExpr (.unknown ⟨0, by decide⟩) 4)),
  .mul (.scalar (1059340 : Rat)) (.mul (powExpr .x 3) (powExpr (.unknown ⟨0, by decide⟩) 4)),
  .mul (.scalar (-434593 : Rat)) (.mul (powExpr .x 4) (powExpr (.unknown ⟨0, by decide⟩) 4)),
  .mul (.scalar (48094 : Rat)) (.mul (powExpr .x 5) (powExpr (.unknown ⟨0, by decide⟩) 4)),
  .mul (.scalar (-100 : Rat)) (.mul (powExpr .x 6) (powExpr (.unknown ⟨0, by decide⟩) 4)),
  .mul (.scalar (121420 : Rat)) (.mul (powExpr .x 0) (powExpr (.unknown ⟨0, by decide⟩) 5)),
  .mul (.scalar (-545072 : Rat)) (.mul (powExpr .x 1) (powExpr (.unknown ⟨0, by decide⟩) 5)),
  .mul (.scalar (-514200 : Rat)) (.mul (powExpr .x 2) (powExpr (.unknown ⟨0, by decide⟩) 5)),
  .mul (.scalar (-1441424 : Rat)) (.mul (powExpr .x 3) (powExpr (.unknown ⟨0, by decide⟩) 5)),
  .mul (.scalar (235008 : Rat)) (.mul (powExpr .x 4) (powExpr (.unknown ⟨0, by decide⟩) 5)),
  .mul (.scalar (9376 : Rat)) (.mul (powExpr .x 5) (powExpr (.unknown ⟨0, by decide⟩) 5)),
  .mul (.scalar (3380 : Rat)) (.mul (powExpr .x 6) (powExpr (.unknown ⟨0, by decide⟩) 5)),
  .mul (.scalar (-44079 : Rat)) (.mul (powExpr .x 0) (powExpr (.unknown ⟨0, by decide⟩) 6)),
  .mul (.scalar (295164 : Rat)) (.mul (powExpr .x 1) (powExpr (.unknown ⟨0, by decide⟩) 6)),
  .mul (.scalar (515321 : Rat)) (.mul (powExpr .x 2) (powExpr (.unknown ⟨0, by decide⟩) 6)),
  .mul (.scalar (797680 : Rat)) (.mul (powExpr .x 3) (powExpr (.unknown ⟨0, by decide⟩) 6)),
  .mul (.scalar (524094 : Rat)) (.mul (powExpr .x 4) (powExpr (.unknown ⟨0, by decide⟩) 6)),
  .mul (.scalar (-195284 : Rat)) (.mul (powExpr .x 5) (powExpr (.unknown ⟨0, by decide⟩) 6)),
  .mul (.scalar (15095 : Rat)) (.mul (powExpr .x 6) (powExpr (.unknown ⟨0, by decide⟩) 6)),
  .mul (.scalar (8956 : Rat)) (.mul (powExpr .x 0) (powExpr (.unknown ⟨0, by decide⟩) 7)),
  .mul (.scalar (-97068 : Rat)) (.mul (powExpr .x 1) (powExpr (.unknown ⟨0, by decide⟩) 7)),
  .mul (.scalar (-430040 : Rat)) (.mul (powExpr .x 2) (powExpr (.unknown ⟨0, by decide⟩) 7)),
  .mul (.scalar (-240468 : Rat)) (.mul (powExpr .x 3) (powExpr (.unknown ⟨0, by decide⟩) 7)),
  .mul (.scalar (-671588 : Rat)) (.mul (powExpr .x 4) (powExpr (.unknown ⟨0, by decide⟩) 7)),
  .mul (.scalar (77436 : Rat)) (.mul (powExpr .x 5) (powExpr (.unknown ⟨0, by decide⟩) 7)),
  .mul (.scalar (4044 : Rat)) (.mul (powExpr .x 6) (powExpr (.unknown ⟨0, by decide⟩) 7)),
  .mul (.scalar (-781 : Rat)) (.mul (powExpr .x 0) (powExpr (.unknown ⟨0, by decide⟩) 8)),
  .mul (.scalar (18086 : Rat)) (.mul (powExpr .x 1) (powExpr (.unknown ⟨0, by decide⟩) 8)),
  .mul (.scalar (205778 : Rat)) (.mul (powExpr .x 2) (powExpr (.unknown ⟨0, by decide⟩) 8)),
  .mul (.scalar (136788 : Rat)) (.mul (powExpr .x 3) (powExpr (.unknown ⟨0, by decide⟩) 8)),
  .mul (.scalar (251778 : Rat)) (.mul (powExpr .x 4) (powExpr (.unknown ⟨0, by decide⟩) 8)),
  .mul (.scalar (155040 : Rat)) (.mul (powExpr .x 5) (powExpr (.unknown ⟨0, by decide⟩) 8)),
  .mul (.scalar (-30168 : Rat)) (.mul (powExpr .x 6) (powExpr (.unknown ⟨0, by decide⟩) 8)),
  .mul (.scalar (-1488 : Rat)) (.mul (powExpr .x 1) (powExpr (.unknown ⟨0, by decide⟩) 9)),
  .mul (.scalar (-50844 : Rat)) (.mul (powExpr .x 2) (powExpr (.unknown ⟨0, by decide⟩) 9)),
  .mul (.scalar (-100632 : Rat)) (.mul (powExpr .x 3) (powExpr (.unknown ⟨0, by decide⟩) 9)),
  .mul (.scalar (-23076 : Rat)) (.mul (powExpr .x 4) (powExpr (.unknown ⟨0, by decide⟩) 9)),
  .mul (.scalar (-123804 : Rat)) (.mul (powExpr .x 5) (powExpr (.unknown ⟨0, by decide⟩) 9)),
  .mul (.scalar (648 : Rat)) (.mul (powExpr .x 6) (powExpr (.unknown ⟨0, by decide⟩) 9)),
  .mul (.scalar (5103 : Rat)) (.mul (powExpr .x 2) (powExpr (.unknown ⟨0, by decide⟩) 10)),
  .mul (.scalar (33984 : Rat)) (.mul (powExpr .x 3) (powExpr (.unknown ⟨0, by decide⟩) 10)),
  .mul (.scalar (8604 : Rat)) (.mul (powExpr .x 4) (powExpr (.unknown ⟨0, by decide⟩) 10)),
  .mul (.scalar (20520 : Rat)) (.mul (powExpr .x 5) (powExpr (.unknown ⟨0, by decide⟩) 10)),
  .mul (.scalar (16092 : Rat)) (.mul (powExpr .x 6) (powExpr (.unknown ⟨0, by decide⟩) 10)),
  .mul (.scalar (-3996 : Rat)) (.mul (powExpr .x 3) (powExpr (.unknown ⟨0, by decide⟩) 11)),
  .mul (.scalar (-6912 : Rat)) (.mul (powExpr .x 4) (powExpr (.unknown ⟨0, by decide⟩) 11)),
  .mul (.scalar (1944 : Rat)) (.mul (powExpr .x 5) (powExpr (.unknown ⟨0, by decide⟩) 11)),
  .mul (.scalar (-5184 : Rat)) (.mul (powExpr .x 6) (powExpr (.unknown ⟨0, by decide⟩) 11)),
  .mul (.scalar (972 : Rat)) (.mul (powExpr .x 4) (powExpr (.unknown ⟨0, by decide⟩) 12))]

/-- Kernel-checked agreement of the direct source reification and the
Horner expression used by the finite division certificates. -/
theorem literalQ_reification (x g : FPS) :
    ringEval literalQ x (fun _ => g) = scalarPolynomialRing x g := by
  simp only [literalQ, sumExpr, ringEval, powExpr_ringEval, scalarPolynomialRing,
    f0, expression_ringEval, q0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, polyEval, C_neg, C_zero, C_one]
  change (((-8100 : FPS)*(x^0*g^0))+(((-11016 : FPS)*(x^1*g^0))+(((80028 : FPS)*(x^2*g^0))+(((51444 : FPS)*(x^0*g^1))+(((18252 : FPS)*(x^1*g^1))+(((-467820 : FPS)*(x^2*g^1))+(((121212 : FPS)*(x^3*g^1))+(((-140841 : FPS)*(x^0*g^2))+(((94788 : FPS)*(x^1*g^2))+(((1068822 : FPS)*(x^2*g^2))+(((-349236 : FPS)*(x^3*g^2))+(((47583 : FPS)*(x^4*g^2))+(((216756 : FPS)*(x^0*g^3))+(((-381312 : FPS)*(x^1*g^3))+(((-1228464 : FPS)*(x^2*g^3))+(((-13248 : FPS)*(x^3*g^3))+(((67968 : FPS)*(x^4*g^3))+(((5220 : FPS)*(x^5*g^3))+(((-204775 : FPS)*(x^0*g^4))+(((609666 : FPS)*(x^1*g^4))+(((816316 : FPS)*(x^2*g^4))+(((1059340 : FPS)*(x^3*g^4))+(((-434593 : FPS)*(x^4*g^4))+(((48094 : FPS)*(x^5*g^4))+(((-100 : FPS)*(x^6*g^4))+(((121420 : FPS)*(x^0*g^5))+(((-545072 : FPS)*(x^1*g^5))+(((-514200 : FPS)*(x^2*g^5))+(((-1441424 : FPS)*(x^3*g^5))+(((235008 : FPS)*(x^4*g^5))+(((9376 : FPS)*(x^5*g^5))+(((3380 : FPS)*(x^6*g^5))+(((-44079 : FPS)*(x^0*g^6))+(((295164 : FPS)*(x^1*g^6))+(((515321 : FPS)*(x^2*g^6))+(((797680 : FPS)*(x^3*g^6))+(((524094 : FPS)*(x^4*g^6))+(((-195284 : FPS)*(x^5*g^6))+(((15095 : FPS)*(x^6*g^6))+(((8956 : FPS)*(x^0*g^7))+(((-97068 : FPS)*(x^1*g^7))+(((-430040 : FPS)*(x^2*g^7))+(((-240468 : FPS)*(x^3*g^7))+(((-671588 : FPS)*(x^4*g^7))+(((77436 : FPS)*(x^5*g^7))+(((4044 : FPS)*(x^6*g^7))+(((-781 : FPS)*(x^0*g^8))+(((18086 : FPS)*(x^1*g^8))+(((205778 : FPS)*(x^2*g^8))+(((136788 : FPS)*(x^3*g^8))+(((251778 : FPS)*(x^4*g^8))+(((155040 : FPS)*(x^5*g^8))+(((-30168 : FPS)*(x^6*g^8))+(((-1488 : FPS)*(x^1*g^9))+(((-50844 : FPS)*(x^2*g^9))+(((-100632 : FPS)*(x^3*g^9))+(((-23076 : FPS)*(x^4*g^9))+(((-123804 : FPS)*(x^5*g^9))+(((648 : FPS)*(x^6*g^9))+(((5103 : FPS)*(x^2*g^10))+(((33984 : FPS)*(x^3*g^10))+(((8604 : FPS)*(x^4*g^10))+(((20520 : FPS)*(x^5*g^10))+(((16092 : FPS)*(x^6*g^10))+(((-3996 : FPS)*(x^3*g^11))+(((-6912 : FPS)*(x^4*g^11))+(((1944 : FPS)*(x^5*g^11))+(((-5184 : FPS)*(x^6*g^11))+(((972 : FPS)*(x^4*g^12))+(0 : FPS)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) = ((1 : FPS)*((-8100 : FPS)+x*((-11016 : FPS)+x*((80028 : FPS)+x*(0 : FPS))))+g*((1 : FPS)*((51444 : FPS)+x*((18252 : FPS)+x*((-467820 : FPS)+x*((121212 : FPS)+x*(0 : FPS)))))+g*((1 : FPS)*((-140841 : FPS)+x*((94788 : FPS)+x*((1068822 : FPS)+x*((-349236 : FPS)+x*((47583 : FPS)+x*(0 : FPS))))))+g*((1 : FPS)*((216756 : FPS)+x*((-381312 : FPS)+x*((-1228464 : FPS)+x*((-13248 : FPS)+x*((67968 : FPS)+x*((5220 : FPS)+x*(0 : FPS)))))))+g*((1 : FPS)*((-204775 : FPS)+x*((609666 : FPS)+x*((816316 : FPS)+x*((1059340 : FPS)+x*((-434593 : FPS)+x*((48094 : FPS)+x*((-100 : FPS)+x*(0 : FPS))))))))+g*((1 : FPS)*((121420 : FPS)+x*((-545072 : FPS)+x*((-514200 : FPS)+x*((-1441424 : FPS)+x*((235008 : FPS)+x*((9376 : FPS)+x*((3380 : FPS)+x*(0 : FPS))))))))+g*((1 : FPS)*((-44079 : FPS)+x*((295164 : FPS)+x*((515321 : FPS)+x*((797680 : FPS)+x*((524094 : FPS)+x*((-195284 : FPS)+x*((15095 : FPS)+x*(0 : FPS))))))))+g*((1 : FPS)*((8956 : FPS)+x*((-97068 : FPS)+x*((-430040 : FPS)+x*((-240468 : FPS)+x*((-671588 : FPS)+x*((77436 : FPS)+x*((4044 : FPS)+x*(0 : FPS))))))))+g*((1 : FPS)*((-781 : FPS)+x*((18086 : FPS)+x*((205778 : FPS)+x*((136788 : FPS)+x*((251778 : FPS)+x*((155040 : FPS)+x*((-30168 : FPS)+x*(0 : FPS))))))))+g*((1 : FPS)*((0 : FPS)+x*((-1488 : FPS)+x*((-50844 : FPS)+x*((-100632 : FPS)+x*((-23076 : FPS)+x*((-123804 : FPS)+x*((648 : FPS)+x*(0 : FPS))))))))+g*((1 : FPS)*((0 : FPS)+x*((0 : FPS)+x*((5103 : FPS)+x*((33984 : FPS)+x*((8604 : FPS)+x*((20520 : FPS)+x*((16092 : FPS)+x*(0 : FPS))))))))+g*((1 : FPS)*((0 : FPS)+x*((0 : FPS)+x*((0 : FPS)+x*((-3996 : FPS)+x*((-6912 : FPS)+x*((1944 : FPS)+x*((-5184 : FPS)+x*(0 : FPS))))))))+g*((1 : FPS)*((0 : FPS)+x*((0 : FPS)+x*((0 : FPS)+x*((0 : FPS)+x*((972 : FPS)+x*(0 : FPS))))))+g*(0 : FPS))))))))))))))
  grind

/-- All-length formal coefficient identity for the direct, unchanged
69-term scalar polynomial from the reviewed source file. -/
theorem literalQ_G_all_coefficients :
    literalQ.eval (fun _ => G.coeff) = (fun _ => (0 : Rat)) := by
  have h := ringEval_coefficient_semantics literalQ (fun _ => G.coeff)
  change (ringEval literalQ X (fun _ => G)).coeff = _ at h
  rw [literalQ_reification, formal_G_equation_ring] at h
  rw [← h]
  funext n
  change const 0 n=0
  unfold const
  split <;> rfl

#print axioms literalQ_reification
#print axioms literalQ_G_all_coefficients
end StackSorting.ConcreteScalar
