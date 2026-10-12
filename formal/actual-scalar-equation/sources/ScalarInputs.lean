import UnivariateDivision

namespace StackSorting.ConcreteScalar
open StackSorting.ProperSeries StackSorting.ConcreteEquation
set_option maxRecDepth 10000
set_option maxHeartbeats 20000000

/-- Literal 69-term scalar polynomial, grouped by powers of G. -/
def q0 : QPoly.Poly := [(-8100 : Rat), (-11016 : Rat), (80028 : Rat)]
def q1 : QPoly.Poly := [(51444 : Rat), (18252 : Rat), (-467820 : Rat), (121212 : Rat)]
def q2 : QPoly.Poly := [(-140841 : Rat), (94788 : Rat), (1068822 : Rat), (-349236 : Rat), (47583 : Rat)]
def q3 : QPoly.Poly := [(216756 : Rat), (-381312 : Rat), (-1228464 : Rat), (-13248 : Rat), (67968 : Rat), (5220 : Rat)]
def q4 : QPoly.Poly := [(-204775 : Rat), (609666 : Rat), (816316 : Rat), (1059340 : Rat), (-434593 : Rat), (48094 : Rat), (-100 : Rat)]
def q5 : QPoly.Poly := [(121420 : Rat), (-545072 : Rat), (-514200 : Rat), (-1441424 : Rat), (235008 : Rat), (9376 : Rat), (3380 : Rat)]
def q6 : QPoly.Poly := [(-44079 : Rat), (295164 : Rat), (515321 : Rat), (797680 : Rat), (524094 : Rat), (-195284 : Rat), (15095 : Rat)]
def q7 : QPoly.Poly := [(8956 : Rat), (-97068 : Rat), (-430040 : Rat), (-240468 : Rat), (-671588 : Rat), (77436 : Rat), (4044 : Rat)]
def q8 : QPoly.Poly := [(-781 : Rat), (18086 : Rat), (205778 : Rat), (136788 : Rat), (251778 : Rat), (155040 : Rat), (-30168 : Rat)]
def q9 : QPoly.Poly := [(0 : Rat), (-1488 : Rat), (-50844 : Rat), (-100632 : Rat), (-23076 : Rat), (-123804 : Rat), (648 : Rat)]
def q10 : QPoly.Poly := [(0 : Rat), (0 : Rat), (5103 : Rat), (33984 : Rat), (8604 : Rat), (20520 : Rat), (16092 : Rat)]
def q11 : QPoly.Poly := [(0 : Rat), (0 : Rat), (0 : Rat), (-3996 : Rat), (-6912 : Rat), (1944 : Rat), (-5184 : Rat)]
def q12 : QPoly.Poly := [(0 : Rat), (0 : Rat), (0 : Rat), (0 : Rat), (972 : Rat)]

def center : QPoly.Poly := [(1 : Rat), (1 : Rat), (2 : Rat), (6 : Rat), (24 : Rat), (120 : Rat), (720 : Rat), (5004 : Rat), (38844 : Rat), (325692 : Rat), (2874096 : Rat)]
def centerFamily : Fin 7 → QPoly.Poly := fun _ => center

def f0 : Expr := .add (.mul (.scalar (1 : Rat)) (QPoly.expression q0)) (.mul (.unknown ⟨0, by decide⟩) (.add (.mul (.scalar (1 : Rat)) (QPoly.expression q1)) (.mul (.unknown ⟨0, by decide⟩) (.add (.mul (.scalar (1 : Rat)) (QPoly.expression q2)) (.mul (.unknown ⟨0, by decide⟩) (.add (.mul (.scalar (1 : Rat)) (QPoly.expression q3)) (.mul (.unknown ⟨0, by decide⟩) (.add (.mul (.scalar (1 : Rat)) (QPoly.expression q4)) (.mul (.unknown ⟨0, by decide⟩) (.add (.mul (.scalar (1 : Rat)) (QPoly.expression q5)) (.mul (.unknown ⟨0, by decide⟩) (.add (.mul (.scalar (1 : Rat)) (QPoly.expression q6)) (.mul (.unknown ⟨0, by decide⟩) (.add (.mul (.scalar (1 : Rat)) (QPoly.expression q7)) (.mul (.unknown ⟨0, by decide⟩) (.add (.mul (.scalar (1 : Rat)) (QPoly.expression q8)) (.mul (.unknown ⟨0, by decide⟩) (.add (.mul (.scalar (1 : Rat)) (QPoly.expression q9)) (.mul (.unknown ⟨0, by decide⟩) (.add (.mul (.scalar (1 : Rat)) (QPoly.expression q10)) (.mul (.unknown ⟨0, by decide⟩) (.add (.mul (.scalar (1 : Rat)) (QPoly.expression q11)) (.mul (.unknown ⟨0, by decide⟩) (.add (.mul (.scalar (1 : Rat)) (QPoly.expression q12)) (.mul (.unknown ⟨0, by decide⟩) (.scalar 0))))))))))))))))))))))))))

def f1 : Expr := .add (.mul (.scalar (1 : Rat)) (QPoly.expression q1)) (.mul (.unknown ⟨0, by decide⟩) (.add (.mul (.scalar (2 : Rat)) (QPoly.expression q2)) (.mul (.unknown ⟨0, by decide⟩) (.add (.mul (.scalar (3 : Rat)) (QPoly.expression q3)) (.mul (.unknown ⟨0, by decide⟩) (.add (.mul (.scalar (4 : Rat)) (QPoly.expression q4)) (.mul (.unknown ⟨0, by decide⟩) (.add (.mul (.scalar (5 : Rat)) (QPoly.expression q5)) (.mul (.unknown ⟨0, by decide⟩) (.add (.mul (.scalar (6 : Rat)) (QPoly.expression q6)) (.mul (.unknown ⟨0, by decide⟩) (.add (.mul (.scalar (7 : Rat)) (QPoly.expression q7)) (.mul (.unknown ⟨0, by decide⟩) (.add (.mul (.scalar (8 : Rat)) (QPoly.expression q8)) (.mul (.unknown ⟨0, by decide⟩) (.add (.mul (.scalar (9 : Rat)) (QPoly.expression q9)) (.mul (.unknown ⟨0, by decide⟩) (.add (.mul (.scalar (10 : Rat)) (QPoly.expression q10)) (.mul (.unknown ⟨0, by decide⟩) (.add (.mul (.scalar (11 : Rat)) (QPoly.expression q11)) (.mul (.unknown ⟨0, by decide⟩) (.add (.mul (.scalar (12 : Rat)) (QPoly.expression q12)) (.mul (.unknown ⟨0, by decide⟩) (.scalar 0))))))))))))))))))))))))

def f2 : Expr := .add (.mul (.scalar (1 : Rat)) (QPoly.expression q2)) (.mul (.unknown ⟨0, by decide⟩) (.add (.mul (.scalar (3 : Rat)) (QPoly.expression q3)) (.mul (.unknown ⟨0, by decide⟩) (.add (.mul (.scalar (6 : Rat)) (QPoly.expression q4)) (.mul (.unknown ⟨0, by decide⟩) (.add (.mul (.scalar (10 : Rat)) (QPoly.expression q5)) (.mul (.unknown ⟨0, by decide⟩) (.add (.mul (.scalar (15 : Rat)) (QPoly.expression q6)) (.mul (.unknown ⟨0, by decide⟩) (.add (.mul (.scalar (21 : Rat)) (QPoly.expression q7)) (.mul (.unknown ⟨0, by decide⟩) (.add (.mul (.scalar (28 : Rat)) (QPoly.expression q8)) (.mul (.unknown ⟨0, by decide⟩) (.add (.mul (.scalar (36 : Rat)) (QPoly.expression q9)) (.mul (.unknown ⟨0, by decide⟩) (.add (.mul (.scalar (45 : Rat)) (QPoly.expression q10)) (.mul (.unknown ⟨0, by decide⟩) (.add (.mul (.scalar (55 : Rat)) (QPoly.expression q11)) (.mul (.unknown ⟨0, by decide⟩) (.add (.mul (.scalar (66 : Rat)) (QPoly.expression q12)) (.mul (.unknown ⟨0, by decide⟩) (.scalar 0))))))))))))))))))))))

def f3 : Expr := .add (.mul (.scalar (1 : Rat)) (QPoly.expression q3)) (.mul (.unknown ⟨0, by decide⟩) (.add (.mul (.scalar (4 : Rat)) (QPoly.expression q4)) (.mul (.unknown ⟨0, by decide⟩) (.add (.mul (.scalar (10 : Rat)) (QPoly.expression q5)) (.mul (.unknown ⟨0, by decide⟩) (.add (.mul (.scalar (20 : Rat)) (QPoly.expression q6)) (.mul (.unknown ⟨0, by decide⟩) (.add (.mul (.scalar (35 : Rat)) (QPoly.expression q7)) (.mul (.unknown ⟨0, by decide⟩) (.add (.mul (.scalar (56 : Rat)) (QPoly.expression q8)) (.mul (.unknown ⟨0, by decide⟩) (.add (.mul (.scalar (84 : Rat)) (QPoly.expression q9)) (.mul (.unknown ⟨0, by decide⟩) (.add (.mul (.scalar (120 : Rat)) (QPoly.expression q10)) (.mul (.unknown ⟨0, by decide⟩) (.add (.mul (.scalar (165 : Rat)) (QPoly.expression q11)) (.mul (.unknown ⟨0, by decide⟩) (.add (.mul (.scalar (220 : Rat)) (QPoly.expression q12)) (.mul (.unknown ⟨0, by decide⟩) (.scalar 0))))))))))))))))))))

def f4 : Expr := .add (.mul (.scalar (1 : Rat)) (QPoly.expression q4)) (.mul (.unknown ⟨0, by decide⟩) (.add (.mul (.scalar (5 : Rat)) (QPoly.expression q5)) (.mul (.unknown ⟨0, by decide⟩) (.add (.mul (.scalar (15 : Rat)) (QPoly.expression q6)) (.mul (.unknown ⟨0, by decide⟩) (.add (.mul (.scalar (35 : Rat)) (QPoly.expression q7)) (.mul (.unknown ⟨0, by decide⟩) (.add (.mul (.scalar (70 : Rat)) (QPoly.expression q8)) (.mul (.unknown ⟨0, by decide⟩) (.add (.mul (.scalar (126 : Rat)) (QPoly.expression q9)) (.mul (.unknown ⟨0, by decide⟩) (.add (.mul (.scalar (210 : Rat)) (QPoly.expression q10)) (.mul (.unknown ⟨0, by decide⟩) (.add (.mul (.scalar (330 : Rat)) (QPoly.expression q11)) (.mul (.unknown ⟨0, by decide⟩) (.add (.mul (.scalar (495 : Rat)) (QPoly.expression q12)) (.mul (.unknown ⟨0, by decide⟩) (.scalar 0))))))))))))))))))

def f5 : Expr := .add (.mul (.scalar (1 : Rat)) (QPoly.expression q5)) (.mul (.unknown ⟨0, by decide⟩) (.add (.mul (.scalar (6 : Rat)) (QPoly.expression q6)) (.mul (.unknown ⟨0, by decide⟩) (.add (.mul (.scalar (21 : Rat)) (QPoly.expression q7)) (.mul (.unknown ⟨0, by decide⟩) (.add (.mul (.scalar (56 : Rat)) (QPoly.expression q8)) (.mul (.unknown ⟨0, by decide⟩) (.add (.mul (.scalar (126 : Rat)) (QPoly.expression q9)) (.mul (.unknown ⟨0, by decide⟩) (.add (.mul (.scalar (252 : Rat)) (QPoly.expression q10)) (.mul (.unknown ⟨0, by decide⟩) (.add (.mul (.scalar (462 : Rat)) (QPoly.expression q11)) (.mul (.unknown ⟨0, by decide⟩) (.add (.mul (.scalar (792 : Rat)) (QPoly.expression q12)) (.mul (.unknown ⟨0, by decide⟩) (.scalar 0))))))))))))))))

def f6 : Expr := .add (.mul (.scalar (1 : Rat)) (QPoly.expression q6)) (.mul (.unknown ⟨0, by decide⟩) (.add (.mul (.scalar (7 : Rat)) (QPoly.expression q7)) (.mul (.unknown ⟨0, by decide⟩) (.add (.mul (.scalar (28 : Rat)) (QPoly.expression q8)) (.mul (.unknown ⟨0, by decide⟩) (.add (.mul (.scalar (84 : Rat)) (QPoly.expression q9)) (.mul (.unknown ⟨0, by decide⟩) (.add (.mul (.scalar (210 : Rat)) (QPoly.expression q10)) (.mul (.unknown ⟨0, by decide⟩) (.add (.mul (.scalar (462 : Rat)) (QPoly.expression q11)) (.mul (.unknown ⟨0, by decide⟩) (.add (.mul (.scalar (924 : Rat)) (QPoly.expression q12)) (.mul (.unknown ⟨0, by decide⟩) (.scalar 0))))))))))))))

def f7 : Expr := .add (.mul (.scalar (1 : Rat)) (QPoly.expression q7)) (.mul (.unknown ⟨0, by decide⟩) (.add (.mul (.scalar (8 : Rat)) (QPoly.expression q8)) (.mul (.unknown ⟨0, by decide⟩) (.add (.mul (.scalar (36 : Rat)) (QPoly.expression q9)) (.mul (.unknown ⟨0, by decide⟩) (.add (.mul (.scalar (120 : Rat)) (QPoly.expression q10)) (.mul (.unknown ⟨0, by decide⟩) (.add (.mul (.scalar (330 : Rat)) (QPoly.expression q11)) (.mul (.unknown ⟨0, by decide⟩) (.add (.mul (.scalar (792 : Rat)) (QPoly.expression q12)) (.mul (.unknown ⟨0, by decide⟩) (.scalar 0))))))))))))

def f8 : Expr := .add (.mul (.scalar (1 : Rat)) (QPoly.expression q8)) (.mul (.unknown ⟨0, by decide⟩) (.add (.mul (.scalar (9 : Rat)) (QPoly.expression q9)) (.mul (.unknown ⟨0, by decide⟩) (.add (.mul (.scalar (45 : Rat)) (QPoly.expression q10)) (.mul (.unknown ⟨0, by decide⟩) (.add (.mul (.scalar (165 : Rat)) (QPoly.expression q11)) (.mul (.unknown ⟨0, by decide⟩) (.add (.mul (.scalar (495 : Rat)) (QPoly.expression q12)) (.mul (.unknown ⟨0, by decide⟩) (.scalar 0))))))))))

def f9 : Expr := .add (.mul (.scalar (1 : Rat)) (QPoly.expression q9)) (.mul (.unknown ⟨0, by decide⟩) (.add (.mul (.scalar (10 : Rat)) (QPoly.expression q10)) (.mul (.unknown ⟨0, by decide⟩) (.add (.mul (.scalar (55 : Rat)) (QPoly.expression q11)) (.mul (.unknown ⟨0, by decide⟩) (.add (.mul (.scalar (220 : Rat)) (QPoly.expression q12)) (.mul (.unknown ⟨0, by decide⟩) (.scalar 0))))))))

def f10 : Expr := .add (.mul (.scalar (1 : Rat)) (QPoly.expression q10)) (.mul (.unknown ⟨0, by decide⟩) (.add (.mul (.scalar (11 : Rat)) (QPoly.expression q11)) (.mul (.unknown ⟨0, by decide⟩) (.add (.mul (.scalar (66 : Rat)) (QPoly.expression q12)) (.mul (.unknown ⟨0, by decide⟩) (.scalar 0))))))

def f11 : Expr := .add (.mul (.scalar (1 : Rat)) (QPoly.expression q11)) (.mul (.unknown ⟨0, by decide⟩) (.add (.mul (.scalar (12 : Rat)) (QPoly.expression q12)) (.mul (.unknown ⟨0, by decide⟩) (.scalar 0))))

def f12 : Expr := .add (.mul (.scalar (1 : Rat)) (QPoly.expression q12)) (.mul (.unknown ⟨0, by decide⟩) (.scalar 0))

def a0 : Expr := (splitAt 22 centerFamily f0).high
def a1 : Expr := (splitAt 12 centerFamily f1).high
def a2 : Expr := (splitAt 2 centerFamily f2).high

theorem remainder0 : (splitAt 22 centerFamily f0).low = List.replicate 22 0 := by
  decide +kernel

theorem remainder1 : (splitAt 12 centerFamily f1).low =
    List.replicate 11 0 ++ [(-576 : Rat)] := by
  decide +kernel

theorem remainder2 : (splitAt 2 centerFamily f2).low = List.replicate 2 0 := by
  decide +kernel

#print axioms remainder0
#print axioms remainder1
#print axioms remainder2
end StackSorting.ConcreteScalar
