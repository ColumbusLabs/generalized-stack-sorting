import StagedDirectionPart3
noncomputable section
namespace StackSorting.FiniteGraph
set_option maxRecDepth 65536
set_option maxHeartbeats 32000000
variable {R : Type} [Lean.Grind.CommRing R]

def dz2n320E : RingExpr := (.mul (.int (-18)) (.mul (.var 1) (.pow (.var 3) 2)))
def dz2n320P : Lean.Grind.CommRing.Poly := (.add (-18) (.mult ⟨1,1⟩ (.mult ⟨3,2⟩ .unit)) (.num (0)))
theorem dz2n320_norm : (reflectRing dz2n320E).toPoly=dz2n320P := by
  exact eq_of_beq (by decide : (reflectRing dz2n320E).toPoly == dz2n320P)

def dz2n321E : RingExpr := (.mul (.int (-18)) (.mul (.var 2) (.var 3)))
def dz2n321P : Lean.Grind.CommRing.Poly := (.add (-18) (.mult ⟨2,1⟩ (.mult ⟨3,1⟩ .unit)) (.num (0)))
theorem dz2n321_norm : (reflectRing dz2n321E).toPoly=dz2n321P := by
  exact eq_of_beq (by decide : (reflectRing dz2n321E).toPoly == dz2n321P)

def dz2n322E : RingExpr := (.mul (.int (-72)) (.mul (.var 3) (.mul (.var 4) (.pow (.var 2) 2))))
def dz2n322P : Lean.Grind.CommRing.Poly := (.add (-72) (.mult ⟨2,2⟩ (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ .unit))) (.num (0)))
theorem dz2n322_norm : (reflectRing dz2n322E).toPoly=dz2n322P := by
  exact eq_of_beq (by decide : (reflectRing dz2n322E).toPoly == dz2n322P)

def dz2n323E : RingExpr := (.mul (.int (-18)) (.mul (.var 4) (.mul (.pow (.var 1) 2) (.pow (.var 3) 3))))
def dz2n323P : Lean.Grind.CommRing.Poly := (.add (-18) (.mult ⟨1,2⟩ (.mult ⟨3,3⟩ (.mult ⟨4,1⟩ .unit))) (.num (0)))
theorem dz2n323_norm : (reflectRing dz2n323E).toPoly=dz2n323P := by
  exact eq_of_beq (by decide : (reflectRing dz2n323E).toPoly == dz2n323P)

def dz2n324E : RingExpr := (.mul (.int 6) (.mul (.var 5) (.mul (.var 1) (.pow (.var 3) 2))))
def dz2n324P : Lean.Grind.CommRing.Poly := (.add (6) (.mult ⟨1,1⟩ (.mult ⟨3,2⟩ (.mult ⟨5,1⟩ .unit))) (.num (0)))
theorem dz2n324_norm : (reflectRing dz2n324E).toPoly=dz2n324P := by
  exact eq_of_beq (by decide : (reflectRing dz2n324E).toPoly == dz2n324P)

def dz2n325E : RingExpr := (.mul (.int 6) (.mul (.var 5) (.mul (.var 2) (.var 3))))
def dz2n325P : Lean.Grind.CommRing.Poly := (.add (6) (.mult ⟨2,1⟩ (.mult ⟨3,1⟩ (.mult ⟨5,1⟩ .unit))) (.num (0)))
theorem dz2n325_norm : (reflectRing dz2n325E).toPoly=dz2n325P := by
  exact eq_of_beq (by decide : (reflectRing dz2n325E).toPoly == dz2n325P)

def dz2n326E : RingExpr := (.mul (.int 36) (.mul (.pow (.var 1) 3) (.mul (.pow (.var 3) 4) (.pow (.var 4) 2))))
def dz2n326P : Lean.Grind.CommRing.Poly := (.add (36) (.mult ⟨1,3⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ .unit))) (.num (0)))
theorem dz2n326_norm : (reflectRing dz2n326E).toPoly=dz2n326P := by
  exact eq_of_beq (by decide : (reflectRing dz2n326E).toPoly == dz2n326P)

def dz2n327E : RingExpr := (.mul (.int (-90)) (.mul (.var 1) (.mul (.var 2) (.mul (.var 4) (.pow (.var 3) 2)))))
def dz2n327P : Lean.Grind.CommRing.Poly := (.add (-90) (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ .unit)))) (.num (0)))
theorem dz2n327_norm : (reflectRing dz2n327E).toPoly=dz2n327P := by
  exact eq_of_beq (by decide : (reflectRing dz2n327E).toPoly == dz2n327P)

def dz2n328E : RingExpr := (.mul (.int (-72)) (.mul (.var 1) (.mul (.pow (.var 2) 2) (.mul (.pow (.var 3) 2) (.pow (.var 4) 2)))))
def dz2n328P : Lean.Grind.CommRing.Poly := (.add (-72) (.mult ⟨1,1⟩ (.mult ⟨2,2⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ .unit)))) (.num (0)))
theorem dz2n328_norm : (reflectRing dz2n328E).toPoly=dz2n328P := by
  exact eq_of_beq (by decide : (reflectRing dz2n328E).toPoly == dz2n328P)

def dz2n329E : RingExpr := (.mul (.int (-72)) (.mul (.var 6) (.mul (.pow (.var 2) 2) (.mul (.pow (.var 3) 2) (.pow (.var 4) 2)))))
def dz2n329P : Lean.Grind.CommRing.Poly := (.add (-72) (.mult ⟨2,2⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨6,1⟩ .unit)))) (.num (0)))
theorem dz2n329_norm : (reflectRing dz2n329E).toPoly=dz2n329P := by
  exact eq_of_beq (by decide : (reflectRing dz2n329E).toPoly == dz2n329P)

def dz2n330E : RingExpr := (.mul (.int (-36)) (.mul (.var 0) (.mul (.pow (.var 1) 2) (.mul (.pow (.var 3) 5) (.pow (.var 4) 2)))))
def dz2n330P : Lean.Grind.CommRing.Poly := (.add (-36) (.mult ⟨0,1⟩ (.mult ⟨1,2⟩ (.mult ⟨3,5⟩ (.mult ⟨4,2⟩ .unit)))) (.num (0)))
theorem dz2n330_norm : (reflectRing dz2n330E).toPoly=dz2n330P := by
  exact eq_of_beq (by decide : (reflectRing dz2n330E).toPoly == dz2n330P)

def dz2n331E : RingExpr := (.mul (.int (-36)) (.mul (.var 1) (.mul (.var 6) (.mul (.var 4) (.pow (.var 3) 3)))))
def dz2n331P : Lean.Grind.CommRing.Poly := (.add (-36) (.mult ⟨1,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,1⟩ (.mult ⟨6,1⟩ .unit)))) (.num (0)))
theorem dz2n331_norm : (reflectRing dz2n331E).toPoly=dz2n331P := by
  exact eq_of_beq (by decide : (reflectRing dz2n331E).toPoly == dz2n331P)

def dz2n332E : RingExpr := (.mul (.int (-36)) (.mul (.var 6) (.mul (.var 2) (.mul (.var 4) (.pow (.var 3) 2)))))
def dz2n332P : Lean.Grind.CommRing.Poly := (.add (-36) (.mult ⟨2,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨6,1⟩ .unit)))) (.num (0)))
theorem dz2n332_norm : (reflectRing dz2n332E).toPoly=dz2n332P := by
  exact eq_of_beq (by decide : (reflectRing dz2n332E).toPoly == dz2n332P)

def dz2n333E : RingExpr := (.mul (.int (-36)) (.mul (.var 6) (.mul (.pow (.var 1) 2) (.mul (.pow (.var 3) 4) (.pow (.var 4) 2)))))
def dz2n333P : Lean.Grind.CommRing.Poly := (.add (-36) (.mult ⟨1,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨6,1⟩ .unit)))) (.num (0)))
theorem dz2n333_norm : (reflectRing dz2n333E).toPoly=dz2n333P := by
  exact eq_of_beq (by decide : (reflectRing dz2n333E).toPoly == dz2n333P)

def dz2n334E : RingExpr := (.mul (.int 12) (.mul (.var 5) (.mul (.var 4) (.mul (.pow (.var 1) 2) (.pow (.var 3) 3)))))
def dz2n334P : Lean.Grind.CommRing.Poly := (.add (12) (.mult ⟨1,2⟩ (.mult ⟨3,3⟩ (.mult ⟨4,1⟩ (.mult ⟨5,1⟩ .unit)))) (.num (0)))
theorem dz2n334_norm : (reflectRing dz2n334E).toPoly=dz2n334P := by
  exact eq_of_beq (by decide : (reflectRing dz2n334E).toPoly == dz2n334P)

def dz2n335E : RingExpr := (.mul (.int 24) (.mul (.var 5) (.mul (.var 3) (.mul (.var 4) (.pow (.var 2) 2)))))
def dz2n335P : Lean.Grind.CommRing.Poly := (.add (24) (.mult ⟨2,2⟩ (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨5,1⟩ .unit)))) (.num (0)))
theorem dz2n335_norm : (reflectRing dz2n335E).toPoly=dz2n335P := by
  exact eq_of_beq (by decide : (reflectRing dz2n335E).toPoly == dz2n335P)

def dz2n336E : RingExpr := (.mul (.int 24) (.mul (.var 5) (.mul (.var 3) (.mul (.pow (.var 2) 3) (.pow (.var 4) 2)))))
def dz2n336P : Lean.Grind.CommRing.Poly := (.add (24) (.mult ⟨2,3⟩ (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨5,1⟩ .unit)))) (.num (0)))
theorem dz2n336_norm : (reflectRing dz2n336E).toPoly=dz2n336P := by
  exact eq_of_beq (by decide : (reflectRing dz2n336E).toPoly == dz2n336P)

def dz2n337E : RingExpr := (.mul (.int 24) (.mul (.var 0) (.mul (.var 6) (.mul (.var 4) (.pow (.var 3) 4)))))
def dz2n337P : Lean.Grind.CommRing.Poly := (.add (24) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,1⟩ (.mult ⟨6,1⟩ .unit)))) (.num (0)))
theorem dz2n337_norm : (reflectRing dz2n337E).toPoly=dz2n337P := by
  exact eq_of_beq (by decide : (reflectRing dz2n337E).toPoly == dz2n337P)

def dz2n338E : RingExpr := (.mul (.int 24) (.mul (.var 6) (.mul (.pow (.var 0) 2) (.mul (.pow (.var 3) 6) (.pow (.var 4) 2)))))
def dz2n338P : Lean.Grind.CommRing.Poly := (.add (24) (.mult ⟨0,2⟩ (.mult ⟨3,6⟩ (.mult ⟨4,2⟩ (.mult ⟨6,1⟩ .unit)))) (.num (0)))
theorem dz2n338_norm : (reflectRing dz2n338E).toPoly=dz2n338P := by
  exact eq_of_beq (by decide : (reflectRing dz2n338E).toPoly == dz2n338P)

def dz2n339E : RingExpr := (.mul (.int 36) (.mul (.var 0) (.mul (.var 2) (.mul (.var 4) (.pow (.var 3) 3)))))
def dz2n339P : Lean.Grind.CommRing.Poly := (.add (36) (.mult ⟨0,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,1⟩ .unit)))) (.num (0)))
theorem dz2n339_norm : (reflectRing dz2n339E).toPoly=dz2n339P := by
  exact eq_of_beq (by decide : (reflectRing dz2n339E).toPoly == dz2n339P)

def dz2n340E : RingExpr := (.mul (.int 36) (.mul (.var 2) (.mul (.pow (.var 1) 2) (.mul (.pow (.var 3) 3) (.pow (.var 4) 2)))))
def dz2n340P : Lean.Grind.CommRing.Poly := (.add (36) (.mult ⟨1,2⟩ (.mult ⟨2,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ .unit)))) (.num (0)))
theorem dz2n340_norm : (reflectRing dz2n340E).toPoly=dz2n340P := by
  exact eq_of_beq (by decide : (reflectRing dz2n340E).toPoly == dz2n340P)

def dz2n341E : RingExpr := (.mul (.int 72) (.mul (.var 1) (.mul (.pow (.var 2) 3) (.mul (.pow (.var 3) 2) (.pow (.var 4) 3)))))
def dz2n341P : Lean.Grind.CommRing.Poly := (.add (72) (.mult ⟨1,1⟩ (.mult ⟨2,3⟩ (.mult ⟨3,2⟩ (.mult ⟨4,3⟩ .unit)))) (.num (0)))
theorem dz2n341_norm : (reflectRing dz2n341E).toPoly=dz2n341P := by
  exact eq_of_beq (by decide : (reflectRing dz2n341E).toPoly == dz2n341P)

def dz2n342E : RingExpr := (.mul (.int 72) (.mul (.var 6) (.mul (.pow (.var 1) 3) (.mul (.pow (.var 3) 5) (.pow (.var 4) 3)))))
def dz2n342P : Lean.Grind.CommRing.Poly := (.add (72) (.mult ⟨1,3⟩ (.mult ⟨3,5⟩ (.mult ⟨4,3⟩ (.mult ⟨6,1⟩ .unit)))) (.num (0)))
theorem dz2n342_norm : (reflectRing dz2n342E).toPoly=dz2n342P := by
  exact eq_of_beq (by decide : (reflectRing dz2n342E).toPoly == dz2n342P)

def dz2n343E : RingExpr := (.mul (.int 72) (.mul (.var 2) (.mul (.pow (.var 1) 3) (.mul (.pow (.var 3) 4) (.pow (.var 4) 3)))))
def dz2n343P : Lean.Grind.CommRing.Poly := (.add (72) (.mult ⟨1,3⟩ (.mult ⟨2,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,3⟩ .unit)))) (.num (0)))
theorem dz2n343_norm : (reflectRing dz2n343E).toPoly=dz2n343P := by
  exact eq_of_beq (by decide : (reflectRing dz2n343E).toPoly == dz2n343P)

def dz2n344E : RingExpr := (.mul (.int 144) (.mul (.pow (.var 1) 2) (.mul (.pow (.var 2) 2) (.mul (.pow (.var 3) 3) (.pow (.var 4) 3)))))
def dz2n344P : Lean.Grind.CommRing.Poly := (.add (144) (.mult ⟨1,2⟩ (.mult ⟨2,2⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ .unit)))) (.num (0)))
theorem dz2n344_norm : (reflectRing dz2n344E).toPoly=dz2n344P := by
  exact eq_of_beq (by decide : (reflectRing dz2n344E).toPoly == dz2n344P)

def dz2n345E : RingExpr := (.mul (.int (-144)) (.mul (.var 0) (.mul (.var 1) (.mul (.pow (.var 2) 2) (.mul (.pow (.var 3) 4) (.pow (.var 4) 3))))))
def dz2n345P : Lean.Grind.CommRing.Poly := (.add (-144) (.mult ⟨0,1⟩ (.mult ⟨1,1⟩ (.mult ⟨2,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,3⟩ .unit))))) (.num (0)))
theorem dz2n345_norm : (reflectRing dz2n345E).toPoly=dz2n345P := by
  exact eq_of_beq (by decide : (reflectRing dz2n345E).toPoly == dz2n345P)

def dz2n346E : RingExpr := (.mul (.int (-144)) (.mul (.var 0) (.mul (.var 6) (.mul (.pow (.var 1) 2) (.mul (.pow (.var 3) 6) (.pow (.var 4) 3))))))
def dz2n346P : Lean.Grind.CommRing.Poly := (.add (-144) (.mult ⟨0,1⟩ (.mult ⟨1,2⟩ (.mult ⟨3,6⟩ (.mult ⟨4,3⟩ (.mult ⟨6,1⟩ .unit))))) (.num (0)))
theorem dz2n346_norm : (reflectRing dz2n346E).toPoly=dz2n346P := by
  exact eq_of_beq (by decide : (reflectRing dz2n346E).toPoly == dz2n346P)

def dz2n347E : RingExpr := (.mul (.int (-144)) (.mul (.var 0) (.mul (.var 2) (.mul (.pow (.var 1) 2) (.mul (.pow (.var 3) 5) (.pow (.var 4) 3))))))
def dz2n347P : Lean.Grind.CommRing.Poly := (.add (-144) (.mult ⟨0,1⟩ (.mult ⟨1,2⟩ (.mult ⟨2,1⟩ (.mult ⟨3,5⟩ (.mult ⟨4,3⟩ .unit))))) (.num (0)))
theorem dz2n347_norm : (reflectRing dz2n347E).toPoly=dz2n347P := by
  exact eq_of_beq (by decide : (reflectRing dz2n347E).toPoly == dz2n347P)

def dz2n348E : RingExpr := (.mul (.int (-108)) (.mul (.var 1) (.mul (.var 6) (.mul (.var 2) (.mul (.pow (.var 3) 3) (.pow (.var 4) 2))))))
def dz2n348P : Lean.Grind.CommRing.Poly := (.add (-108) (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨6,1⟩ .unit))))) (.num (0)))
theorem dz2n348_norm : (reflectRing dz2n348E).toPoly=dz2n348P := by
  exact eq_of_beq (by decide : (reflectRing dz2n348E).toPoly == dz2n348P)

def dz2n349E : RingExpr := (.mul (.int (-48)) (.mul (.var 5) (.mul (.var 0) (.mul (.pow (.var 2) 2) (.mul (.pow (.var 3) 3) (.pow (.var 4) 2))))))
def dz2n349P : Lean.Grind.CommRing.Poly := (.add (-48) (.mult ⟨0,1⟩ (.mult ⟨2,2⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨5,1⟩ .unit))))) (.num (0)))
theorem dz2n349_norm : (reflectRing dz2n349E).toPoly=dz2n349P := by
  exact eq_of_beq (by decide : (reflectRing dz2n349E).toPoly == dz2n349P)

def dz2n350E : RingExpr := (.mul (.int (-24)) (.mul (.var 5) (.mul (.var 0) (.mul (.var 2) (.mul (.var 4) (.pow (.var 3) 3))))))
def dz2n350P : Lean.Grind.CommRing.Poly := (.add (-24) (.mult ⟨0,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,1⟩ (.mult ⟨5,1⟩ .unit))))) (.num (0)))
theorem dz2n350_norm : (reflectRing dz2n350E).toPoly=dz2n350P := by
  exact eq_of_beq (by decide : (reflectRing dz2n350E).toPoly == dz2n350P)

def dz2n351E : RingExpr := (.mul (.int (-12)) (.mul (.var 5) (.mul (.var 0) (.mul (.var 1) (.mul (.var 4) (.pow (.var 3) 4))))))
def dz2n351P : Lean.Grind.CommRing.Poly := (.add (-12) (.mult ⟨0,1⟩ (.mult ⟨1,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,1⟩ (.mult ⟨5,1⟩ .unit))))) (.num (0)))
theorem dz2n351_norm : (reflectRing dz2n351E).toPoly=dz2n351P := by
  exact eq_of_beq (by decide : (reflectRing dz2n351E).toPoly == dz2n351P)

def dz2n352E : RingExpr := (.mul (.int (-12)) (.mul (.var 5) (.mul (.var 0) (.mul (.var 6) (.mul (.var 4) (.pow (.var 3) 4))))))
def dz2n352P : Lean.Grind.CommRing.Poly := (.add (-12) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,1⟩ (.mult ⟨5,1⟩ (.mult ⟨6,1⟩ .unit))))) (.num (0)))
theorem dz2n352_norm : (reflectRing dz2n352E).toPoly=dz2n352P := by
  exact eq_of_beq (by decide : (reflectRing dz2n352E).toPoly == dz2n352P)

def dz2n353E : RingExpr := (.mul (.int 12) (.mul (.var 5) (.mul (.var 1) (.mul (.var 6) (.mul (.var 4) (.pow (.var 3) 3))))))
def dz2n353P : Lean.Grind.CommRing.Poly := (.add (12) (.mult ⟨1,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,1⟩ (.mult ⟨5,1⟩ (.mult ⟨6,1⟩ .unit))))) (.num (0)))
theorem dz2n353_norm : (reflectRing dz2n353E).toPoly=dz2n353P := by
  exact eq_of_beq (by decide : (reflectRing dz2n353E).toPoly == dz2n353P)

def dz2n354E : RingExpr := (.mul (.int 12) (.mul (.var 5) (.mul (.var 6) (.mul (.var 2) (.mul (.var 4) (.pow (.var 3) 2))))))
def dz2n354P : Lean.Grind.CommRing.Poly := (.add (12) (.mult ⟨2,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨5,1⟩ (.mult ⟨6,1⟩ .unit))))) (.num (0)))
theorem dz2n354_norm : (reflectRing dz2n354E).toPoly=dz2n354P := by
  exact eq_of_beq (by decide : (reflectRing dz2n354E).toPoly == dz2n354P)

def dz2n355E : RingExpr := (.mul (.int 12) (.mul (.var 0) (.mul (.var 1) (.mul (.var 6) (.mul (.pow (.var 3) 5) (.pow (.var 4) 2))))))
def dz2n355P : Lean.Grind.CommRing.Poly := (.add (12) (.mult ⟨0,1⟩ (.mult ⟨1,1⟩ (.mult ⟨3,5⟩ (.mult ⟨4,2⟩ (.mult ⟨6,1⟩ .unit))))) (.num (0)))
theorem dz2n355_norm : (reflectRing dz2n355E).toPoly=dz2n355P := by
  exact eq_of_beq (by decide : (reflectRing dz2n355E).toPoly == dz2n355P)

def dz2n356E : RingExpr := (.mul (.int 24) (.mul (.var 5) (.mul (.var 6) (.mul (.pow (.var 0) 2) (.mul (.pow (.var 3) 6) (.pow (.var 4) 2))))))
def dz2n356P : Lean.Grind.CommRing.Poly := (.add (24) (.mult ⟨0,2⟩ (.mult ⟨3,6⟩ (.mult ⟨4,2⟩ (.mult ⟨5,1⟩ (.mult ⟨6,1⟩ .unit))))) (.num (0)))
theorem dz2n356_norm : (reflectRing dz2n356E).toPoly=dz2n356P := by
  exact eq_of_beq (by decide : (reflectRing dz2n356E).toPoly == dz2n356P)

def dz2n357E : RingExpr := (.mul (.int 24) (.mul (.var 5) (.mul (.var 6) (.mul (.pow (.var 1) 2) (.mul (.pow (.var 3) 4) (.pow (.var 4) 2))))))
def dz2n357P : Lean.Grind.CommRing.Poly := (.add (24) (.mult ⟨1,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨5,1⟩ (.mult ⟨6,1⟩ .unit))))) (.num (0)))
theorem dz2n357_norm : (reflectRing dz2n357E).toPoly=dz2n357P := by
  exact eq_of_beq (by decide : (reflectRing dz2n357E).toPoly == dz2n357P)

def dz2n358E : RingExpr := (.mul (.int 24) (.mul (.var 5) (.mul (.var 6) (.mul (.pow (.var 2) 2) (.mul (.pow (.var 3) 2) (.pow (.var 4) 2))))))
def dz2n358P : Lean.Grind.CommRing.Poly := (.add (24) (.mult ⟨2,2⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨5,1⟩ (.mult ⟨6,1⟩ .unit))))) (.num (0)))
theorem dz2n358_norm : (reflectRing dz2n358E).toPoly=dz2n358P := by
  exact eq_of_beq (by decide : (reflectRing dz2n358E).toPoly == dz2n358P)

def dz2n359E : RingExpr := (.mul (.int 24) (.mul (.var 5) (.mul (.var 2) (.mul (.pow (.var 0) 2) (.mul (.pow (.var 3) 5) (.pow (.var 4) 2))))))
def dz2n359P : Lean.Grind.CommRing.Poly := (.add (24) (.mult ⟨0,2⟩ (.mult ⟨2,1⟩ (.mult ⟨3,5⟩ (.mult ⟨4,2⟩ (.mult ⟨5,1⟩ .unit))))) (.num (0)))
theorem dz2n359_norm : (reflectRing dz2n359E).toPoly=dz2n359P := by
  exact eq_of_beq (by decide : (reflectRing dz2n359E).toPoly == dz2n359P)

def dz2n360E : RingExpr := (.mul (.int 24) (.mul (.var 5) (.mul (.var 2) (.mul (.pow (.var 1) 2) (.mul (.pow (.var 3) 3) (.pow (.var 4) 2))))))
def dz2n360P : Lean.Grind.CommRing.Poly := (.add (24) (.mult ⟨1,2⟩ (.mult ⟨2,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨5,1⟩ .unit))))) (.num (0)))
theorem dz2n360_norm : (reflectRing dz2n360E).toPoly=dz2n360P := by
  exact eq_of_beq (by decide : (reflectRing dz2n360E).toPoly == dz2n360P)

def dz2n361E : RingExpr := (.mul (.int 36) (.mul (.var 5) (.mul (.var 1) (.mul (.var 2) (.mul (.var 4) (.pow (.var 3) 2))))))
def dz2n361P : Lean.Grind.CommRing.Poly := (.add (36) (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨5,1⟩ .unit))))) (.num (0)))
theorem dz2n361_norm : (reflectRing dz2n361E).toPoly=dz2n361P := by
  exact eq_of_beq (by decide : (reflectRing dz2n361E).toPoly == dz2n361P)

def dz2n362E : RingExpr := (.mul (.int 48) (.mul (.var 5) (.mul (.var 1) (.mul (.pow (.var 2) 2) (.mul (.pow (.var 3) 2) (.pow (.var 4) 2))))))
def dz2n362P : Lean.Grind.CommRing.Poly := (.add (48) (.mult ⟨1,1⟩ (.mult ⟨2,2⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨5,1⟩ .unit))))) (.num (0)))
theorem dz2n362_norm : (reflectRing dz2n362E).toPoly=dz2n362P := by
  exact eq_of_beq (by decide : (reflectRing dz2n362E).toPoly == dz2n362P)

def dz2n363E : RingExpr := (.mul (.int 48) (.mul (.var 0) (.mul (.var 6) (.mul (.var 2) (.mul (.pow (.var 3) 4) (.pow (.var 4) 2))))))
def dz2n363P : Lean.Grind.CommRing.Poly := (.add (48) (.mult ⟨0,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨6,1⟩ .unit))))) (.num (0)))
theorem dz2n363_norm : (reflectRing dz2n363E).toPoly=dz2n363P := by
  exact eq_of_beq (by decide : (reflectRing dz2n363E).toPoly == dz2n363P)

def dz2n364E : RingExpr := (.mul (.int 72) (.mul (.var 1) (.mul (.var 6) (.mul (.pow (.var 0) 2) (.mul (.pow (.var 3) 7) (.pow (.var 4) 3))))))
def dz2n364P : Lean.Grind.CommRing.Poly := (.add (72) (.mult ⟨0,2⟩ (.mult ⟨1,1⟩ (.mult ⟨3,7⟩ (.mult ⟨4,3⟩ (.mult ⟨6,1⟩ .unit))))) (.num (0)))
theorem dz2n364_norm : (reflectRing dz2n364E).toPoly=dz2n364P := by
  exact eq_of_beq (by decide : (reflectRing dz2n364E).toPoly == dz2n364P)

def dz2n365E : RingExpr := (.mul (.int 72) (.mul (.var 1) (.mul (.var 6) (.mul (.pow (.var 2) 2) (.mul (.pow (.var 3) 3) (.pow (.var 4) 3))))))
def dz2n365P : Lean.Grind.CommRing.Poly := (.add (72) (.mult ⟨1,1⟩ (.mult ⟨2,2⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨6,1⟩ .unit))))) (.num (0)))
theorem dz2n365_norm : (reflectRing dz2n365E).toPoly=dz2n365P := by
  exact eq_of_beq (by decide : (reflectRing dz2n365E).toPoly == dz2n365P)

def dz2n366E : RingExpr := (.mul (.int 72) (.mul (.var 1) (.mul (.var 2) (.mul (.pow (.var 0) 2) (.mul (.pow (.var 3) 6) (.pow (.var 4) 3))))))
def dz2n366P : Lean.Grind.CommRing.Poly := (.add (72) (.mult ⟨0,2⟩ (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,6⟩ (.mult ⟨4,3⟩ .unit))))) (.num (0)))
theorem dz2n366_norm : (reflectRing dz2n366E).toPoly=dz2n366P := by
  exact eq_of_beq (by decide : (reflectRing dz2n366E).toPoly == dz2n366P)

def dz2n367E : RingExpr := (.mul (.int 144) (.mul (.var 6) (.mul (.var 2) (.mul (.pow (.var 1) 2) (.mul (.pow (.var 3) 4) (.pow (.var 4) 3))))))
def dz2n367P : Lean.Grind.CommRing.Poly := (.add (144) (.mult ⟨1,2⟩ (.mult ⟨2,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,3⟩ (.mult ⟨6,1⟩ .unit))))) (.num (0)))
theorem dz2n367_norm : (reflectRing dz2n367E).toPoly=dz2n367P := by
  exact eq_of_beq (by decide : (reflectRing dz2n367E).toPoly == dz2n367P)

def dz2n368E : RingExpr := (.add (.mul (.int (-144)) (.mul (.var 0) (.mul (.var 1) (.mul (.var 6) (.mul (.var 2) (.mul (.pow (.var 3) 5) (.pow (.var 4) 3))))))) (.add (.mul (.int (-48)) (.mul (.var 5) (.mul (.var 0) (.mul (.var 1) (.mul (.var 6) (.mul (.pow (.var 3) 5) (.pow (.var 4) 2))))))) (.add (.mul (.int (-48)) (.mul (.var 5) (.mul (.var 0) (.mul (.var 1) (.mul (.var 2) (.mul (.pow (.var 3) 4) (.pow (.var 4) 2))))))) (.add (.mul (.int (-48)) (.mul (.var 5) (.mul (.var 0) (.mul (.var 6) (.mul (.var 2) (.mul (.pow (.var 3) 4) (.pow (.var 4) 2))))))) (.mul (.int 48) (.mul (.var 5) (.mul (.var 1) (.mul (.var 6) (.mul (.var 2) (.mul (.pow (.var 3) 3) (.pow (.var 4) 2)))))))))))
def dz2n368P : Lean.Grind.CommRing.Poly := (.add (-144) (.mult ⟨0,1⟩ (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,5⟩ (.mult ⟨4,3⟩ (.mult ⟨6,1⟩ .unit)))))) (.add (-48) (.mult ⟨0,1⟩ (.mult ⟨1,1⟩ (.mult ⟨3,5⟩ (.mult ⟨4,2⟩ (.mult ⟨5,1⟩ (.mult ⟨6,1⟩ .unit)))))) (.add (-48) (.mult ⟨0,1⟩ (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨5,1⟩ .unit)))))) (.add (-48) (.mult ⟨0,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨5,1⟩ (.mult ⟨6,1⟩ .unit)))))) (.add (48) (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨5,1⟩ (.mult ⟨6,1⟩ .unit)))))) (.num (0)))))))
theorem dz2n368_norm : (reflectRing dz2n368E).toPoly=dz2n368P := by
  exact eq_of_beq (by decide : (reflectRing dz2n368E).toPoly == dz2n368P)

def dz2n369E : RingExpr := (.add dz2n367E dz2n368E)
def dz2n369P : Lean.Grind.CommRing.Poly := (.add (-144) (.mult ⟨0,1⟩ (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,5⟩ (.mult ⟨4,3⟩ (.mult ⟨6,1⟩ .unit)))))) (.add (144) (.mult ⟨1,2⟩ (.mult ⟨2,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,3⟩ (.mult ⟨6,1⟩ .unit))))) (.add (-48) (.mult ⟨0,1⟩ (.mult ⟨1,1⟩ (.mult ⟨3,5⟩ (.mult ⟨4,2⟩ (.mult ⟨5,1⟩ (.mult ⟨6,1⟩ .unit)))))) (.add (-48) (.mult ⟨0,1⟩ (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨5,1⟩ .unit)))))) (.add (-48) (.mult ⟨0,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨5,1⟩ (.mult ⟨6,1⟩ .unit)))))) (.add (48) (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨5,1⟩ (.mult ⟨6,1⟩ .unit)))))) (.num (0))))))))
theorem dz2n369_norm : (reflectRing dz2n369E).toPoly=dz2n369P := by
  change (reflectRing dz2n367E).toPoly.combine (reflectRing dz2n368E).toPoly=dz2n369P
  rw [dz2n367_norm, dz2n368_norm]
  exact eq_of_beq (by decide : dz2n367P.combine dz2n368P == dz2n369P)

def dz2n370E : RingExpr := (.add dz2n366E dz2n369E)
def dz2n370P : Lean.Grind.CommRing.Poly := (.add (72) (.mult ⟨0,2⟩ (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,6⟩ (.mult ⟨4,3⟩ .unit))))) (.add (-144) (.mult ⟨0,1⟩ (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,5⟩ (.mult ⟨4,3⟩ (.mult ⟨6,1⟩ .unit)))))) (.add (144) (.mult ⟨1,2⟩ (.mult ⟨2,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,3⟩ (.mult ⟨6,1⟩ .unit))))) (.add (-48) (.mult ⟨0,1⟩ (.mult ⟨1,1⟩ (.mult ⟨3,5⟩ (.mult ⟨4,2⟩ (.mult ⟨5,1⟩ (.mult ⟨6,1⟩ .unit)))))) (.add (-48) (.mult ⟨0,1⟩ (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨5,1⟩ .unit)))))) (.add (-48) (.mult ⟨0,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨5,1⟩ (.mult ⟨6,1⟩ .unit)))))) (.add (48) (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨5,1⟩ (.mult ⟨6,1⟩ .unit)))))) (.num (0)))))))))
theorem dz2n370_norm : (reflectRing dz2n370E).toPoly=dz2n370P := by
  change (reflectRing dz2n366E).toPoly.combine (reflectRing dz2n369E).toPoly=dz2n370P
  rw [dz2n366_norm, dz2n369_norm]
  exact eq_of_beq (by decide : dz2n366P.combine dz2n369P == dz2n370P)

def dz2n371E : RingExpr := (.add dz2n365E dz2n370E)
def dz2n371P : Lean.Grind.CommRing.Poly := (.add (72) (.mult ⟨0,2⟩ (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,6⟩ (.mult ⟨4,3⟩ .unit))))) (.add (-144) (.mult ⟨0,1⟩ (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,5⟩ (.mult ⟨4,3⟩ (.mult ⟨6,1⟩ .unit)))))) (.add (144) (.mult ⟨1,2⟩ (.mult ⟨2,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,3⟩ (.mult ⟨6,1⟩ .unit))))) (.add (-48) (.mult ⟨0,1⟩ (.mult ⟨1,1⟩ (.mult ⟨3,5⟩ (.mult ⟨4,2⟩ (.mult ⟨5,1⟩ (.mult ⟨6,1⟩ .unit)))))) (.add (-48) (.mult ⟨0,1⟩ (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨5,1⟩ .unit)))))) (.add (72) (.mult ⟨1,1⟩ (.mult ⟨2,2⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨6,1⟩ .unit))))) (.add (-48) (.mult ⟨0,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨5,1⟩ (.mult ⟨6,1⟩ .unit)))))) (.add (48) (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨5,1⟩ (.mult ⟨6,1⟩ .unit)))))) (.num (0))))))))))
theorem dz2n371_norm : (reflectRing dz2n371E).toPoly=dz2n371P := by
  change (reflectRing dz2n365E).toPoly.combine (reflectRing dz2n370E).toPoly=dz2n371P
  rw [dz2n365_norm, dz2n370_norm]
  exact eq_of_beq (by decide : dz2n365P.combine dz2n370P == dz2n371P)

def dz2n372E : RingExpr := (.add dz2n364E dz2n371E)
def dz2n372P : Lean.Grind.CommRing.Poly := (.add (72) (.mult ⟨0,2⟩ (.mult ⟨1,1⟩ (.mult ⟨3,7⟩ (.mult ⟨4,3⟩ (.mult ⟨6,1⟩ .unit))))) (.add (72) (.mult ⟨0,2⟩ (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,6⟩ (.mult ⟨4,3⟩ .unit))))) (.add (-144) (.mult ⟨0,1⟩ (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,5⟩ (.mult ⟨4,3⟩ (.mult ⟨6,1⟩ .unit)))))) (.add (144) (.mult ⟨1,2⟩ (.mult ⟨2,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,3⟩ (.mult ⟨6,1⟩ .unit))))) (.add (-48) (.mult ⟨0,1⟩ (.mult ⟨1,1⟩ (.mult ⟨3,5⟩ (.mult ⟨4,2⟩ (.mult ⟨5,1⟩ (.mult ⟨6,1⟩ .unit)))))) (.add (-48) (.mult ⟨0,1⟩ (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨5,1⟩ .unit)))))) (.add (72) (.mult ⟨1,1⟩ (.mult ⟨2,2⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨6,1⟩ .unit))))) (.add (-48) (.mult ⟨0,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨5,1⟩ (.mult ⟨6,1⟩ .unit)))))) (.add (48) (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨5,1⟩ (.mult ⟨6,1⟩ .unit)))))) (.num (0)))))))))))
theorem dz2n372_norm : (reflectRing dz2n372E).toPoly=dz2n372P := by
  change (reflectRing dz2n364E).toPoly.combine (reflectRing dz2n371E).toPoly=dz2n372P
  rw [dz2n364_norm, dz2n371_norm]
  exact eq_of_beq (by decide : dz2n364P.combine dz2n371P == dz2n372P)

def dz2n373E : RingExpr := (.add dz2n363E dz2n372E)
def dz2n373P : Lean.Grind.CommRing.Poly := (.add (72) (.mult ⟨0,2⟩ (.mult ⟨1,1⟩ (.mult ⟨3,7⟩ (.mult ⟨4,3⟩ (.mult ⟨6,1⟩ .unit))))) (.add (72) (.mult ⟨0,2⟩ (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,6⟩ (.mult ⟨4,3⟩ .unit))))) (.add (-144) (.mult ⟨0,1⟩ (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,5⟩ (.mult ⟨4,3⟩ (.mult ⟨6,1⟩ .unit)))))) (.add (144) (.mult ⟨1,2⟩ (.mult ⟨2,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,3⟩ (.mult ⟨6,1⟩ .unit))))) (.add (-48) (.mult ⟨0,1⟩ (.mult ⟨1,1⟩ (.mult ⟨3,5⟩ (.mult ⟨4,2⟩ (.mult ⟨5,1⟩ (.mult ⟨6,1⟩ .unit)))))) (.add (-48) (.mult ⟨0,1⟩ (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨5,1⟩ .unit)))))) (.add (72) (.mult ⟨1,1⟩ (.mult ⟨2,2⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨6,1⟩ .unit))))) (.add (-48) (.mult ⟨0,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨5,1⟩ (.mult ⟨6,1⟩ .unit)))))) (.add (48) (.mult ⟨0,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨6,1⟩ .unit))))) (.add (48) (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨5,1⟩ (.mult ⟨6,1⟩ .unit)))))) (.num (0))))))))))))
theorem dz2n373_norm : (reflectRing dz2n373E).toPoly=dz2n373P := by
  change (reflectRing dz2n363E).toPoly.combine (reflectRing dz2n372E).toPoly=dz2n373P
  rw [dz2n363_norm, dz2n372_norm]
  exact eq_of_beq (by decide : dz2n363P.combine dz2n372P == dz2n373P)

def dz2n374E : RingExpr := (.add dz2n362E dz2n373E)
def dz2n374P : Lean.Grind.CommRing.Poly := (.add (72) (.mult ⟨0,2⟩ (.mult ⟨1,1⟩ (.mult ⟨3,7⟩ (.mult ⟨4,3⟩ (.mult ⟨6,1⟩ .unit))))) (.add (72) (.mult ⟨0,2⟩ (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,6⟩ (.mult ⟨4,3⟩ .unit))))) (.add (-144) (.mult ⟨0,1⟩ (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,5⟩ (.mult ⟨4,3⟩ (.mult ⟨6,1⟩ .unit)))))) (.add (144) (.mult ⟨1,2⟩ (.mult ⟨2,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,3⟩ (.mult ⟨6,1⟩ .unit))))) (.add (-48) (.mult ⟨0,1⟩ (.mult ⟨1,1⟩ (.mult ⟨3,5⟩ (.mult ⟨4,2⟩ (.mult ⟨5,1⟩ (.mult ⟨6,1⟩ .unit)))))) (.add (-48) (.mult ⟨0,1⟩ (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨5,1⟩ .unit)))))) (.add (72) (.mult ⟨1,1⟩ (.mult ⟨2,2⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨6,1⟩ .unit))))) (.add (-48) (.mult ⟨0,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨5,1⟩ (.mult ⟨6,1⟩ .unit)))))) (.add (48) (.mult ⟨0,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨6,1⟩ .unit))))) (.add (48) (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨5,1⟩ (.mult ⟨6,1⟩ .unit)))))) (.add (48) (.mult ⟨1,1⟩ (.mult ⟨2,2⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨5,1⟩ .unit))))) (.num (0)))))))))))))
theorem dz2n374_norm : (reflectRing dz2n374E).toPoly=dz2n374P := by
  change (reflectRing dz2n362E).toPoly.combine (reflectRing dz2n373E).toPoly=dz2n374P
  rw [dz2n362_norm, dz2n373_norm]
  exact eq_of_beq (by decide : dz2n362P.combine dz2n373P == dz2n374P)

def dz2n375E : RingExpr := (.add dz2n361E dz2n374E)
def dz2n375P : Lean.Grind.CommRing.Poly := (.add (72) (.mult ⟨0,2⟩ (.mult ⟨1,1⟩ (.mult ⟨3,7⟩ (.mult ⟨4,3⟩ (.mult ⟨6,1⟩ .unit))))) (.add (72) (.mult ⟨0,2⟩ (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,6⟩ (.mult ⟨4,3⟩ .unit))))) (.add (-144) (.mult ⟨0,1⟩ (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,5⟩ (.mult ⟨4,3⟩ (.mult ⟨6,1⟩ .unit)))))) (.add (144) (.mult ⟨1,2⟩ (.mult ⟨2,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,3⟩ (.mult ⟨6,1⟩ .unit))))) (.add (-48) (.mult ⟨0,1⟩ (.mult ⟨1,1⟩ (.mult ⟨3,5⟩ (.mult ⟨4,2⟩ (.mult ⟨5,1⟩ (.mult ⟨6,1⟩ .unit)))))) (.add (-48) (.mult ⟨0,1⟩ (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨5,1⟩ .unit)))))) (.add (72) (.mult ⟨1,1⟩ (.mult ⟨2,2⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨6,1⟩ .unit))))) (.add (-48) (.mult ⟨0,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨5,1⟩ (.mult ⟨6,1⟩ .unit)))))) (.add (48) (.mult ⟨0,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨6,1⟩ .unit))))) (.add (48) (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨5,1⟩ (.mult ⟨6,1⟩ .unit)))))) (.add (48) (.mult ⟨1,1⟩ (.mult ⟨2,2⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨5,1⟩ .unit))))) (.add (36) (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨5,1⟩ .unit))))) (.num (0))))))))))))))
theorem dz2n375_norm : (reflectRing dz2n375E).toPoly=dz2n375P := by
  change (reflectRing dz2n361E).toPoly.combine (reflectRing dz2n374E).toPoly=dz2n375P
  rw [dz2n361_norm, dz2n374_norm]
  exact eq_of_beq (by decide : dz2n361P.combine dz2n374P == dz2n375P)

def dz2n376E : RingExpr := (.add dz2n360E dz2n375E)
def dz2n376P : Lean.Grind.CommRing.Poly := (.add (72) (.mult ⟨0,2⟩ (.mult ⟨1,1⟩ (.mult ⟨3,7⟩ (.mult ⟨4,3⟩ (.mult ⟨6,1⟩ .unit))))) (.add (72) (.mult ⟨0,2⟩ (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,6⟩ (.mult ⟨4,3⟩ .unit))))) (.add (-144) (.mult ⟨0,1⟩ (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,5⟩ (.mult ⟨4,3⟩ (.mult ⟨6,1⟩ .unit)))))) (.add (144) (.mult ⟨1,2⟩ (.mult ⟨2,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,3⟩ (.mult ⟨6,1⟩ .unit))))) (.add (-48) (.mult ⟨0,1⟩ (.mult ⟨1,1⟩ (.mult ⟨3,5⟩ (.mult ⟨4,2⟩ (.mult ⟨5,1⟩ (.mult ⟨6,1⟩ .unit)))))) (.add (-48) (.mult ⟨0,1⟩ (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨5,1⟩ .unit)))))) (.add (72) (.mult ⟨1,1⟩ (.mult ⟨2,2⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨6,1⟩ .unit))))) (.add (-48) (.mult ⟨0,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨5,1⟩ (.mult ⟨6,1⟩ .unit)))))) (.add (24) (.mult ⟨1,2⟩ (.mult ⟨2,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨5,1⟩ .unit))))) (.add (48) (.mult ⟨0,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨6,1⟩ .unit))))) (.add (48) (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨5,1⟩ (.mult ⟨6,1⟩ .unit)))))) (.add (48) (.mult ⟨1,1⟩ (.mult ⟨2,2⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨5,1⟩ .unit))))) (.add (36) (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨5,1⟩ .unit))))) (.num (0)))))))))))))))
theorem dz2n376_norm : (reflectRing dz2n376E).toPoly=dz2n376P := by
  change (reflectRing dz2n360E).toPoly.combine (reflectRing dz2n375E).toPoly=dz2n376P
  rw [dz2n360_norm, dz2n375_norm]
  exact eq_of_beq (by decide : dz2n360P.combine dz2n375P == dz2n376P)

def dz2n377E : RingExpr := (.add dz2n359E dz2n376E)
def dz2n377P : Lean.Grind.CommRing.Poly := (.add (72) (.mult ⟨0,2⟩ (.mult ⟨1,1⟩ (.mult ⟨3,7⟩ (.mult ⟨4,3⟩ (.mult ⟨6,1⟩ .unit))))) (.add (72) (.mult ⟨0,2⟩ (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,6⟩ (.mult ⟨4,3⟩ .unit))))) (.add (-144) (.mult ⟨0,1⟩ (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,5⟩ (.mult ⟨4,3⟩ (.mult ⟨6,1⟩ .unit)))))) (.add (24) (.mult ⟨0,2⟩ (.mult ⟨2,1⟩ (.mult ⟨3,5⟩ (.mult ⟨4,2⟩ (.mult ⟨5,1⟩ .unit))))) (.add (144) (.mult ⟨1,2⟩ (.mult ⟨2,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,3⟩ (.mult ⟨6,1⟩ .unit))))) (.add (-48) (.mult ⟨0,1⟩ (.mult ⟨1,1⟩ (.mult ⟨3,5⟩ (.mult ⟨4,2⟩ (.mult ⟨5,1⟩ (.mult ⟨6,1⟩ .unit)))))) (.add (-48) (.mult ⟨0,1⟩ (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨5,1⟩ .unit)))))) (.add (72) (.mult ⟨1,1⟩ (.mult ⟨2,2⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨6,1⟩ .unit))))) (.add (-48) (.mult ⟨0,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨5,1⟩ (.mult ⟨6,1⟩ .unit)))))) (.add (24) (.mult ⟨1,2⟩ (.mult ⟨2,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨5,1⟩ .unit))))) (.add (48) (.mult ⟨0,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨6,1⟩ .unit))))) (.add (48) (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨5,1⟩ (.mult ⟨6,1⟩ .unit)))))) (.add (48) (.mult ⟨1,1⟩ (.mult ⟨2,2⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨5,1⟩ .unit))))) (.add (36) (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨5,1⟩ .unit))))) (.num (0))))))))))))))))
theorem dz2n377_norm : (reflectRing dz2n377E).toPoly=dz2n377P := by
  change (reflectRing dz2n359E).toPoly.combine (reflectRing dz2n376E).toPoly=dz2n377P
  rw [dz2n359_norm, dz2n376_norm]
  exact eq_of_beq (by decide : dz2n359P.combine dz2n376P == dz2n377P)

def dz2n378E : RingExpr := (.add dz2n358E dz2n377E)
def dz2n378P : Lean.Grind.CommRing.Poly := (.add (72) (.mult ⟨0,2⟩ (.mult ⟨1,1⟩ (.mult ⟨3,7⟩ (.mult ⟨4,3⟩ (.mult ⟨6,1⟩ .unit))))) (.add (72) (.mult ⟨0,2⟩ (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,6⟩ (.mult ⟨4,3⟩ .unit))))) (.add (-144) (.mult ⟨0,1⟩ (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,5⟩ (.mult ⟨4,3⟩ (.mult ⟨6,1⟩ .unit)))))) (.add (24) (.mult ⟨0,2⟩ (.mult ⟨2,1⟩ (.mult ⟨3,5⟩ (.mult ⟨4,2⟩ (.mult ⟨5,1⟩ .unit))))) (.add (144) (.mult ⟨1,2⟩ (.mult ⟨2,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,3⟩ (.mult ⟨6,1⟩ .unit))))) (.add (-48) (.mult ⟨0,1⟩ (.mult ⟨1,1⟩ (.mult ⟨3,5⟩ (.mult ⟨4,2⟩ (.mult ⟨5,1⟩ (.mult ⟨6,1⟩ .unit)))))) (.add (-48) (.mult ⟨0,1⟩ (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨5,1⟩ .unit)))))) (.add (72) (.mult ⟨1,1⟩ (.mult ⟨2,2⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨6,1⟩ .unit))))) (.add (-48) (.mult ⟨0,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨5,1⟩ (.mult ⟨6,1⟩ .unit)))))) (.add (24) (.mult ⟨1,2⟩ (.mult ⟨2,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨5,1⟩ .unit))))) (.add (48) (.mult ⟨0,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨6,1⟩ .unit))))) (.add (48) (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨5,1⟩ (.mult ⟨6,1⟩ .unit)))))) (.add (48) (.mult ⟨1,1⟩ (.mult ⟨2,2⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨5,1⟩ .unit))))) (.add (24) (.mult ⟨2,2⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨5,1⟩ (.mult ⟨6,1⟩ .unit))))) (.add (36) (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨5,1⟩ .unit))))) (.num (0)))))))))))))))))
theorem dz2n378_norm : (reflectRing dz2n378E).toPoly=dz2n378P := by
  change (reflectRing dz2n358E).toPoly.combine (reflectRing dz2n377E).toPoly=dz2n378P
  rw [dz2n358_norm, dz2n377_norm]
  exact eq_of_beq (by decide : dz2n358P.combine dz2n377P == dz2n378P)

def dz2n379E : RingExpr := (.add dz2n357E dz2n378E)
def dz2n379P : Lean.Grind.CommRing.Poly := (.add (72) (.mult ⟨0,2⟩ (.mult ⟨1,1⟩ (.mult ⟨3,7⟩ (.mult ⟨4,3⟩ (.mult ⟨6,1⟩ .unit))))) (.add (72) (.mult ⟨0,2⟩ (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,6⟩ (.mult ⟨4,3⟩ .unit))))) (.add (-144) (.mult ⟨0,1⟩ (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,5⟩ (.mult ⟨4,3⟩ (.mult ⟨6,1⟩ .unit)))))) (.add (24) (.mult ⟨0,2⟩ (.mult ⟨2,1⟩ (.mult ⟨3,5⟩ (.mult ⟨4,2⟩ (.mult ⟨5,1⟩ .unit))))) (.add (144) (.mult ⟨1,2⟩ (.mult ⟨2,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,3⟩ (.mult ⟨6,1⟩ .unit))))) (.add (-48) (.mult ⟨0,1⟩ (.mult ⟨1,1⟩ (.mult ⟨3,5⟩ (.mult ⟨4,2⟩ (.mult ⟨5,1⟩ (.mult ⟨6,1⟩ .unit)))))) (.add (-48) (.mult ⟨0,1⟩ (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨5,1⟩ .unit)))))) (.add (72) (.mult ⟨1,1⟩ (.mult ⟨2,2⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨6,1⟩ .unit))))) (.add (24) (.mult ⟨1,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨5,1⟩ (.mult ⟨6,1⟩ .unit))))) (.add (-48) (.mult ⟨0,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨5,1⟩ (.mult ⟨6,1⟩ .unit)))))) (.add (24) (.mult ⟨1,2⟩ (.mult ⟨2,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨5,1⟩ .unit))))) (.add (48) (.mult ⟨0,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨6,1⟩ .unit))))) (.add (48) (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨5,1⟩ (.mult ⟨6,1⟩ .unit)))))) (.add (48) (.mult ⟨1,1⟩ (.mult ⟨2,2⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨5,1⟩ .unit))))) (.add (24) (.mult ⟨2,2⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨5,1⟩ (.mult ⟨6,1⟩ .unit))))) (.add (36) (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨5,1⟩ .unit))))) (.num (0))))))))))))))))))
theorem dz2n379_norm : (reflectRing dz2n379E).toPoly=dz2n379P := by
  change (reflectRing dz2n357E).toPoly.combine (reflectRing dz2n378E).toPoly=dz2n379P
  rw [dz2n357_norm, dz2n378_norm]
  exact eq_of_beq (by decide : dz2n357P.combine dz2n378P == dz2n379P)

def dz2n380E : RingExpr := (.add dz2n356E dz2n379E)
def dz2n380P : Lean.Grind.CommRing.Poly := (.add (72) (.mult ⟨0,2⟩ (.mult ⟨1,1⟩ (.mult ⟨3,7⟩ (.mult ⟨4,3⟩ (.mult ⟨6,1⟩ .unit))))) (.add (72) (.mult ⟨0,2⟩ (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,6⟩ (.mult ⟨4,3⟩ .unit))))) (.add (-144) (.mult ⟨0,1⟩ (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,5⟩ (.mult ⟨4,3⟩ (.mult ⟨6,1⟩ .unit)))))) (.add (24) (.mult ⟨0,2⟩ (.mult ⟨3,6⟩ (.mult ⟨4,2⟩ (.mult ⟨5,1⟩ (.mult ⟨6,1⟩ .unit))))) (.add (24) (.mult ⟨0,2⟩ (.mult ⟨2,1⟩ (.mult ⟨3,5⟩ (.mult ⟨4,2⟩ (.mult ⟨5,1⟩ .unit))))) (.add (144) (.mult ⟨1,2⟩ (.mult ⟨2,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,3⟩ (.mult ⟨6,1⟩ .unit))))) (.add (-48) (.mult ⟨0,1⟩ (.mult ⟨1,1⟩ (.mult ⟨3,5⟩ (.mult ⟨4,2⟩ (.mult ⟨5,1⟩ (.mult ⟨6,1⟩ .unit)))))) (.add (-48) (.mult ⟨0,1⟩ (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨5,1⟩ .unit)))))) (.add (72) (.mult ⟨1,1⟩ (.mult ⟨2,2⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨6,1⟩ .unit))))) (.add (24) (.mult ⟨1,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨5,1⟩ (.mult ⟨6,1⟩ .unit))))) (.add (-48) (.mult ⟨0,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨5,1⟩ (.mult ⟨6,1⟩ .unit)))))) (.add (24) (.mult ⟨1,2⟩ (.mult ⟨2,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨5,1⟩ .unit))))) (.add (48) (.mult ⟨0,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨6,1⟩ .unit))))) (.add (48) (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨5,1⟩ (.mult ⟨6,1⟩ .unit)))))) (.add (48) (.mult ⟨1,1⟩ (.mult ⟨2,2⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨5,1⟩ .unit))))) (.add (24) (.mult ⟨2,2⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨5,1⟩ (.mult ⟨6,1⟩ .unit))))) (.add (36) (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨5,1⟩ .unit))))) (.num (0)))))))))))))))))))
theorem dz2n380_norm : (reflectRing dz2n380E).toPoly=dz2n380P := by
  change (reflectRing dz2n356E).toPoly.combine (reflectRing dz2n379E).toPoly=dz2n380P
  rw [dz2n356_norm, dz2n379_norm]
  exact eq_of_beq (by decide : dz2n356P.combine dz2n379P == dz2n380P)

def dz2n381E : RingExpr := (.add dz2n355E dz2n380E)
def dz2n381P : Lean.Grind.CommRing.Poly := (.add (72) (.mult ⟨0,2⟩ (.mult ⟨1,1⟩ (.mult ⟨3,7⟩ (.mult ⟨4,3⟩ (.mult ⟨6,1⟩ .unit))))) (.add (72) (.mult ⟨0,2⟩ (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,6⟩ (.mult ⟨4,3⟩ .unit))))) (.add (-144) (.mult ⟨0,1⟩ (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,5⟩ (.mult ⟨4,3⟩ (.mult ⟨6,1⟩ .unit)))))) (.add (24) (.mult ⟨0,2⟩ (.mult ⟨3,6⟩ (.mult ⟨4,2⟩ (.mult ⟨5,1⟩ (.mult ⟨6,1⟩ .unit))))) (.add (24) (.mult ⟨0,2⟩ (.mult ⟨2,1⟩ (.mult ⟨3,5⟩ (.mult ⟨4,2⟩ (.mult ⟨5,1⟩ .unit))))) (.add (144) (.mult ⟨1,2⟩ (.mult ⟨2,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,3⟩ (.mult ⟨6,1⟩ .unit))))) (.add (-48) (.mult ⟨0,1⟩ (.mult ⟨1,1⟩ (.mult ⟨3,5⟩ (.mult ⟨4,2⟩ (.mult ⟨5,1⟩ (.mult ⟨6,1⟩ .unit)))))) (.add (-48) (.mult ⟨0,1⟩ (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨5,1⟩ .unit)))))) (.add (12) (.mult ⟨0,1⟩ (.mult ⟨1,1⟩ (.mult ⟨3,5⟩ (.mult ⟨4,2⟩ (.mult ⟨6,1⟩ .unit))))) (.add (72) (.mult ⟨1,1⟩ (.mult ⟨2,2⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨6,1⟩ .unit))))) (.add (24) (.mult ⟨1,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨5,1⟩ (.mult ⟨6,1⟩ .unit))))) (.add (-48) (.mult ⟨0,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨5,1⟩ (.mult ⟨6,1⟩ .unit)))))) (.add (24) (.mult ⟨1,2⟩ (.mult ⟨2,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨5,1⟩ .unit))))) (.add (48) (.mult ⟨0,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨6,1⟩ .unit))))) (.add (48) (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨5,1⟩ (.mult ⟨6,1⟩ .unit)))))) (.add (48) (.mult ⟨1,1⟩ (.mult ⟨2,2⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨5,1⟩ .unit))))) (.add (24) (.mult ⟨2,2⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨5,1⟩ (.mult ⟨6,1⟩ .unit))))) (.add (36) (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨5,1⟩ .unit))))) (.num (0))))))))))))))))))))
theorem dz2n381_norm : (reflectRing dz2n381E).toPoly=dz2n381P := by
  change (reflectRing dz2n355E).toPoly.combine (reflectRing dz2n380E).toPoly=dz2n381P
  rw [dz2n355_norm, dz2n380_norm]
  exact eq_of_beq (by decide : dz2n355P.combine dz2n380P == dz2n381P)

def dz2n382E : RingExpr := (.add dz2n354E dz2n381E)
def dz2n382P : Lean.Grind.CommRing.Poly := (.add (72) (.mult ⟨0,2⟩ (.mult ⟨1,1⟩ (.mult ⟨3,7⟩ (.mult ⟨4,3⟩ (.mult ⟨6,1⟩ .unit))))) (.add (72) (.mult ⟨0,2⟩ (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,6⟩ (.mult ⟨4,3⟩ .unit))))) (.add (-144) (.mult ⟨0,1⟩ (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,5⟩ (.mult ⟨4,3⟩ (.mult ⟨6,1⟩ .unit)))))) (.add (24) (.mult ⟨0,2⟩ (.mult ⟨3,6⟩ (.mult ⟨4,2⟩ (.mult ⟨5,1⟩ (.mult ⟨6,1⟩ .unit))))) (.add (24) (.mult ⟨0,2⟩ (.mult ⟨2,1⟩ (.mult ⟨3,5⟩ (.mult ⟨4,2⟩ (.mult ⟨5,1⟩ .unit))))) (.add (144) (.mult ⟨1,2⟩ (.mult ⟨2,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,3⟩ (.mult ⟨6,1⟩ .unit))))) (.add (-48) (.mult ⟨0,1⟩ (.mult ⟨1,1⟩ (.mult ⟨3,5⟩ (.mult ⟨4,2⟩ (.mult ⟨5,1⟩ (.mult ⟨6,1⟩ .unit)))))) (.add (-48) (.mult ⟨0,1⟩ (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨5,1⟩ .unit)))))) (.add (12) (.mult ⟨0,1⟩ (.mult ⟨1,1⟩ (.mult ⟨3,5⟩ (.mult ⟨4,2⟩ (.mult ⟨6,1⟩ .unit))))) (.add (72) (.mult ⟨1,1⟩ (.mult ⟨2,2⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨6,1⟩ .unit))))) (.add (24) (.mult ⟨1,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨5,1⟩ (.mult ⟨6,1⟩ .unit))))) (.add (-48) (.mult ⟨0,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨5,1⟩ (.mult ⟨6,1⟩ .unit)))))) (.add (24) (.mult ⟨1,2⟩ (.mult ⟨2,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨5,1⟩ .unit))))) (.add (48) (.mult ⟨0,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨6,1⟩ .unit))))) (.add (48) (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨5,1⟩ (.mult ⟨6,1⟩ .unit)))))) (.add (48) (.mult ⟨1,1⟩ (.mult ⟨2,2⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨5,1⟩ .unit))))) (.add (24) (.mult ⟨2,2⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨5,1⟩ (.mult ⟨6,1⟩ .unit))))) (.add (36) (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨5,1⟩ .unit))))) (.add (12) (.mult ⟨2,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨5,1⟩ (.mult ⟨6,1⟩ .unit))))) (.num (0)))))))))))))))))))))
theorem dz2n382_norm : (reflectRing dz2n382E).toPoly=dz2n382P := by
  change (reflectRing dz2n354E).toPoly.combine (reflectRing dz2n381E).toPoly=dz2n382P
  rw [dz2n354_norm, dz2n381_norm]
  exact eq_of_beq (by decide : dz2n354P.combine dz2n381P == dz2n382P)

def dz2n383E : RingExpr := (.add dz2n353E dz2n382E)
def dz2n383P : Lean.Grind.CommRing.Poly := (.add (72) (.mult ⟨0,2⟩ (.mult ⟨1,1⟩ (.mult ⟨3,7⟩ (.mult ⟨4,3⟩ (.mult ⟨6,1⟩ .unit))))) (.add (72) (.mult ⟨0,2⟩ (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,6⟩ (.mult ⟨4,3⟩ .unit))))) (.add (-144) (.mult ⟨0,1⟩ (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,5⟩ (.mult ⟨4,3⟩ (.mult ⟨6,1⟩ .unit)))))) (.add (24) (.mult ⟨0,2⟩ (.mult ⟨3,6⟩ (.mult ⟨4,2⟩ (.mult ⟨5,1⟩ (.mult ⟨6,1⟩ .unit))))) (.add (24) (.mult ⟨0,2⟩ (.mult ⟨2,1⟩ (.mult ⟨3,5⟩ (.mult ⟨4,2⟩ (.mult ⟨5,1⟩ .unit))))) (.add (144) (.mult ⟨1,2⟩ (.mult ⟨2,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,3⟩ (.mult ⟨6,1⟩ .unit))))) (.add (-48) (.mult ⟨0,1⟩ (.mult ⟨1,1⟩ (.mult ⟨3,5⟩ (.mult ⟨4,2⟩ (.mult ⟨5,1⟩ (.mult ⟨6,1⟩ .unit)))))) (.add (-48) (.mult ⟨0,1⟩ (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨5,1⟩ .unit)))))) (.add (12) (.mult ⟨0,1⟩ (.mult ⟨1,1⟩ (.mult ⟨3,5⟩ (.mult ⟨4,2⟩ (.mult ⟨6,1⟩ .unit))))) (.add (72) (.mult ⟨1,1⟩ (.mult ⟨2,2⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨6,1⟩ .unit))))) (.add (24) (.mult ⟨1,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨5,1⟩ (.mult ⟨6,1⟩ .unit))))) (.add (-48) (.mult ⟨0,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨5,1⟩ (.mult ⟨6,1⟩ .unit)))))) (.add (24) (.mult ⟨1,2⟩ (.mult ⟨2,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨5,1⟩ .unit))))) (.add (48) (.mult ⟨0,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨6,1⟩ .unit))))) (.add (48) (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨5,1⟩ (.mult ⟨6,1⟩ .unit)))))) (.add (48) (.mult ⟨1,1⟩ (.mult ⟨2,2⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨5,1⟩ .unit))))) (.add (24) (.mult ⟨2,2⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨5,1⟩ (.mult ⟨6,1⟩ .unit))))) (.add (12) (.mult ⟨1,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,1⟩ (.mult ⟨5,1⟩ (.mult ⟨6,1⟩ .unit))))) (.add (36) (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨5,1⟩ .unit))))) (.add (12) (.mult ⟨2,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨5,1⟩ (.mult ⟨6,1⟩ .unit))))) (.num (0))))))))))))))))))))))
theorem dz2n383_norm : (reflectRing dz2n383E).toPoly=dz2n383P := by
  change (reflectRing dz2n353E).toPoly.combine (reflectRing dz2n382E).toPoly=dz2n383P
  rw [dz2n353_norm, dz2n382_norm]
  exact eq_of_beq (by decide : dz2n353P.combine dz2n382P == dz2n383P)

def dz2n384E : RingExpr := (.add dz2n352E dz2n383E)
def dz2n384P : Lean.Grind.CommRing.Poly := (.add (72) (.mult ⟨0,2⟩ (.mult ⟨1,1⟩ (.mult ⟨3,7⟩ (.mult ⟨4,3⟩ (.mult ⟨6,1⟩ .unit))))) (.add (72) (.mult ⟨0,2⟩ (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,6⟩ (.mult ⟨4,3⟩ .unit))))) (.add (-144) (.mult ⟨0,1⟩ (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,5⟩ (.mult ⟨4,3⟩ (.mult ⟨6,1⟩ .unit)))))) (.add (24) (.mult ⟨0,2⟩ (.mult ⟨3,6⟩ (.mult ⟨4,2⟩ (.mult ⟨5,1⟩ (.mult ⟨6,1⟩ .unit))))) (.add (24) (.mult ⟨0,2⟩ (.mult ⟨2,1⟩ (.mult ⟨3,5⟩ (.mult ⟨4,2⟩ (.mult ⟨5,1⟩ .unit))))) (.add (144) (.mult ⟨1,2⟩ (.mult ⟨2,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,3⟩ (.mult ⟨6,1⟩ .unit))))) (.add (-48) (.mult ⟨0,1⟩ (.mult ⟨1,1⟩ (.mult ⟨3,5⟩ (.mult ⟨4,2⟩ (.mult ⟨5,1⟩ (.mult ⟨6,1⟩ .unit)))))) (.add (-48) (.mult ⟨0,1⟩ (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨5,1⟩ .unit)))))) (.add (12) (.mult ⟨0,1⟩ (.mult ⟨1,1⟩ (.mult ⟨3,5⟩ (.mult ⟨4,2⟩ (.mult ⟨6,1⟩ .unit))))) (.add (72) (.mult ⟨1,1⟩ (.mult ⟨2,2⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨6,1⟩ .unit))))) (.add (24) (.mult ⟨1,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨5,1⟩ (.mult ⟨6,1⟩ .unit))))) (.add (-48) (.mult ⟨0,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨5,1⟩ (.mult ⟨6,1⟩ .unit)))))) (.add (24) (.mult ⟨1,2⟩ (.mult ⟨2,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨5,1⟩ .unit))))) (.add (48) (.mult ⟨0,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨6,1⟩ .unit))))) (.add (48) (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨5,1⟩ (.mult ⟨6,1⟩ .unit)))))) (.add (48) (.mult ⟨1,1⟩ (.mult ⟨2,2⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨5,1⟩ .unit))))) (.add (-12) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,1⟩ (.mult ⟨5,1⟩ (.mult ⟨6,1⟩ .unit))))) (.add (24) (.mult ⟨2,2⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨5,1⟩ (.mult ⟨6,1⟩ .unit))))) (.add (12) (.mult ⟨1,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,1⟩ (.mult ⟨5,1⟩ (.mult ⟨6,1⟩ .unit))))) (.add (36) (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨5,1⟩ .unit))))) (.add (12) (.mult ⟨2,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨5,1⟩ (.mult ⟨6,1⟩ .unit))))) (.num (0)))))))))))))))))))))))
theorem dz2n384_norm : (reflectRing dz2n384E).toPoly=dz2n384P := by
  change (reflectRing dz2n352E).toPoly.combine (reflectRing dz2n383E).toPoly=dz2n384P
  rw [dz2n352_norm, dz2n383_norm]
  exact eq_of_beq (by decide : dz2n352P.combine dz2n383P == dz2n384P)

def dz2n385E : RingExpr := (.add dz2n351E dz2n384E)
def dz2n385P : Lean.Grind.CommRing.Poly := (.add (72) (.mult ⟨0,2⟩ (.mult ⟨1,1⟩ (.mult ⟨3,7⟩ (.mult ⟨4,3⟩ (.mult ⟨6,1⟩ .unit))))) (.add (72) (.mult ⟨0,2⟩ (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,6⟩ (.mult ⟨4,3⟩ .unit))))) (.add (-144) (.mult ⟨0,1⟩ (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,5⟩ (.mult ⟨4,3⟩ (.mult ⟨6,1⟩ .unit)))))) (.add (24) (.mult ⟨0,2⟩ (.mult ⟨3,6⟩ (.mult ⟨4,2⟩ (.mult ⟨5,1⟩ (.mult ⟨6,1⟩ .unit))))) (.add (24) (.mult ⟨0,2⟩ (.mult ⟨2,1⟩ (.mult ⟨3,5⟩ (.mult ⟨4,2⟩ (.mult ⟨5,1⟩ .unit))))) (.add (144) (.mult ⟨1,2⟩ (.mult ⟨2,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,3⟩ (.mult ⟨6,1⟩ .unit))))) (.add (-48) (.mult ⟨0,1⟩ (.mult ⟨1,1⟩ (.mult ⟨3,5⟩ (.mult ⟨4,2⟩ (.mult ⟨5,1⟩ (.mult ⟨6,1⟩ .unit)))))) (.add (-48) (.mult ⟨0,1⟩ (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨5,1⟩ .unit)))))) (.add (12) (.mult ⟨0,1⟩ (.mult ⟨1,1⟩ (.mult ⟨3,5⟩ (.mult ⟨4,2⟩ (.mult ⟨6,1⟩ .unit))))) (.add (72) (.mult ⟨1,1⟩ (.mult ⟨2,2⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨6,1⟩ .unit))))) (.add (24) (.mult ⟨1,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨5,1⟩ (.mult ⟨6,1⟩ .unit))))) (.add (-48) (.mult ⟨0,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨5,1⟩ (.mult ⟨6,1⟩ .unit)))))) (.add (24) (.mult ⟨1,2⟩ (.mult ⟨2,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨5,1⟩ .unit))))) (.add (48) (.mult ⟨0,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨6,1⟩ .unit))))) (.add (48) (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨5,1⟩ (.mult ⟨6,1⟩ .unit)))))) (.add (-12) (.mult ⟨0,1⟩ (.mult ⟨1,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,1⟩ (.mult ⟨5,1⟩ .unit))))) (.add (48) (.mult ⟨1,1⟩ (.mult ⟨2,2⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨5,1⟩ .unit))))) (.add (-12) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,1⟩ (.mult ⟨5,1⟩ (.mult ⟨6,1⟩ .unit))))) (.add (24) (.mult ⟨2,2⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨5,1⟩ (.mult ⟨6,1⟩ .unit))))) (.add (12) (.mult ⟨1,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,1⟩ (.mult ⟨5,1⟩ (.mult ⟨6,1⟩ .unit))))) (.add (36) (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨5,1⟩ .unit))))) (.add (12) (.mult ⟨2,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨5,1⟩ (.mult ⟨6,1⟩ .unit))))) (.num (0))))))))))))))))))))))))
theorem dz2n385_norm : (reflectRing dz2n385E).toPoly=dz2n385P := by
  change (reflectRing dz2n351E).toPoly.combine (reflectRing dz2n384E).toPoly=dz2n385P
  rw [dz2n351_norm, dz2n384_norm]
  exact eq_of_beq (by decide : dz2n351P.combine dz2n384P == dz2n385P)

def dz2n386E : RingExpr := (.add dz2n350E dz2n385E)
def dz2n386P : Lean.Grind.CommRing.Poly := (.add (72) (.mult ⟨0,2⟩ (.mult ⟨1,1⟩ (.mult ⟨3,7⟩ (.mult ⟨4,3⟩ (.mult ⟨6,1⟩ .unit))))) (.add (72) (.mult ⟨0,2⟩ (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,6⟩ (.mult ⟨4,3⟩ .unit))))) (.add (-144) (.mult ⟨0,1⟩ (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,5⟩ (.mult ⟨4,3⟩ (.mult ⟨6,1⟩ .unit)))))) (.add (24) (.mult ⟨0,2⟩ (.mult ⟨3,6⟩ (.mult ⟨4,2⟩ (.mult ⟨5,1⟩ (.mult ⟨6,1⟩ .unit))))) (.add (24) (.mult ⟨0,2⟩ (.mult ⟨2,1⟩ (.mult ⟨3,5⟩ (.mult ⟨4,2⟩ (.mult ⟨5,1⟩ .unit))))) (.add (144) (.mult ⟨1,2⟩ (.mult ⟨2,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,3⟩ (.mult ⟨6,1⟩ .unit))))) (.add (-48) (.mult ⟨0,1⟩ (.mult ⟨1,1⟩ (.mult ⟨3,5⟩ (.mult ⟨4,2⟩ (.mult ⟨5,1⟩ (.mult ⟨6,1⟩ .unit)))))) (.add (-48) (.mult ⟨0,1⟩ (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨5,1⟩ .unit)))))) (.add (12) (.mult ⟨0,1⟩ (.mult ⟨1,1⟩ (.mult ⟨3,5⟩ (.mult ⟨4,2⟩ (.mult ⟨6,1⟩ .unit))))) (.add (72) (.mult ⟨1,1⟩ (.mult ⟨2,2⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨6,1⟩ .unit))))) (.add (24) (.mult ⟨1,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨5,1⟩ (.mult ⟨6,1⟩ .unit))))) (.add (-48) (.mult ⟨0,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨5,1⟩ (.mult ⟨6,1⟩ .unit)))))) (.add (24) (.mult ⟨1,2⟩ (.mult ⟨2,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨5,1⟩ .unit))))) (.add (48) (.mult ⟨0,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨6,1⟩ .unit))))) (.add (48) (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨5,1⟩ (.mult ⟨6,1⟩ .unit)))))) (.add (-12) (.mult ⟨0,1⟩ (.mult ⟨1,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,1⟩ (.mult ⟨5,1⟩ .unit))))) (.add (48) (.mult ⟨1,1⟩ (.mult ⟨2,2⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨5,1⟩ .unit))))) (.add (-12) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,1⟩ (.mult ⟨5,1⟩ (.mult ⟨6,1⟩ .unit))))) (.add (24) (.mult ⟨2,2⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨5,1⟩ (.mult ⟨6,1⟩ .unit))))) (.add (-24) (.mult ⟨0,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,1⟩ (.mult ⟨5,1⟩ .unit))))) (.add (12) (.mult ⟨1,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,1⟩ (.mult ⟨5,1⟩ (.mult ⟨6,1⟩ .unit))))) (.add (36) (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨5,1⟩ .unit))))) (.add (12) (.mult ⟨2,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨5,1⟩ (.mult ⟨6,1⟩ .unit))))) (.num (0)))))))))))))))))))))))))
theorem dz2n386_norm : (reflectRing dz2n386E).toPoly=dz2n386P := by
  change (reflectRing dz2n350E).toPoly.combine (reflectRing dz2n385E).toPoly=dz2n386P
  rw [dz2n350_norm, dz2n385_norm]
  exact eq_of_beq (by decide : dz2n350P.combine dz2n385P == dz2n386P)

def dz2n387E : RingExpr := (.add dz2n349E dz2n386E)
def dz2n387P : Lean.Grind.CommRing.Poly := (.add (72) (.mult ⟨0,2⟩ (.mult ⟨1,1⟩ (.mult ⟨3,7⟩ (.mult ⟨4,3⟩ (.mult ⟨6,1⟩ .unit))))) (.add (72) (.mult ⟨0,2⟩ (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,6⟩ (.mult ⟨4,3⟩ .unit))))) (.add (-144) (.mult ⟨0,1⟩ (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,5⟩ (.mult ⟨4,3⟩ (.mult ⟨6,1⟩ .unit)))))) (.add (24) (.mult ⟨0,2⟩ (.mult ⟨3,6⟩ (.mult ⟨4,2⟩ (.mult ⟨5,1⟩ (.mult ⟨6,1⟩ .unit))))) (.add (24) (.mult ⟨0,2⟩ (.mult ⟨2,1⟩ (.mult ⟨3,5⟩ (.mult ⟨4,2⟩ (.mult ⟨5,1⟩ .unit))))) (.add (144) (.mult ⟨1,2⟩ (.mult ⟨2,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,3⟩ (.mult ⟨6,1⟩ .unit))))) (.add (-48) (.mult ⟨0,1⟩ (.mult ⟨1,1⟩ (.mult ⟨3,5⟩ (.mult ⟨4,2⟩ (.mult ⟨5,1⟩ (.mult ⟨6,1⟩ .unit)))))) (.add (-48) (.mult ⟨0,1⟩ (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨5,1⟩ .unit)))))) (.add (12) (.mult ⟨0,1⟩ (.mult ⟨1,1⟩ (.mult ⟨3,5⟩ (.mult ⟨4,2⟩ (.mult ⟨6,1⟩ .unit))))) (.add (72) (.mult ⟨1,1⟩ (.mult ⟨2,2⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨6,1⟩ .unit))))) (.add (24) (.mult ⟨1,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨5,1⟩ (.mult ⟨6,1⟩ .unit))))) (.add (-48) (.mult ⟨0,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨5,1⟩ (.mult ⟨6,1⟩ .unit)))))) (.add (24) (.mult ⟨1,2⟩ (.mult ⟨2,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨5,1⟩ .unit))))) (.add (-48) (.mult ⟨0,1⟩ (.mult ⟨2,2⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨5,1⟩ .unit))))) (.add (48) (.mult ⟨0,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨6,1⟩ .unit))))) (.add (48) (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨5,1⟩ (.mult ⟨6,1⟩ .unit)))))) (.add (-12) (.mult ⟨0,1⟩ (.mult ⟨1,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,1⟩ (.mult ⟨5,1⟩ .unit))))) (.add (48) (.mult ⟨1,1⟩ (.mult ⟨2,2⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨5,1⟩ .unit))))) (.add (-12) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,1⟩ (.mult ⟨5,1⟩ (.mult ⟨6,1⟩ .unit))))) (.add (24) (.mult ⟨2,2⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨5,1⟩ (.mult ⟨6,1⟩ .unit))))) (.add (-24) (.mult ⟨0,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,1⟩ (.mult ⟨5,1⟩ .unit))))) (.add (12) (.mult ⟨1,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,1⟩ (.mult ⟨5,1⟩ (.mult ⟨6,1⟩ .unit))))) (.add (36) (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨5,1⟩ .unit))))) (.add (12) (.mult ⟨2,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨5,1⟩ (.mult ⟨6,1⟩ .unit))))) (.num (0))))))))))))))))))))))))))
theorem dz2n387_norm : (reflectRing dz2n387E).toPoly=dz2n387P := by
  change (reflectRing dz2n349E).toPoly.combine (reflectRing dz2n386E).toPoly=dz2n387P
  rw [dz2n349_norm, dz2n386_norm]
  exact eq_of_beq (by decide : dz2n349P.combine dz2n386P == dz2n387P)

def dz2n388E : RingExpr := (.add dz2n348E dz2n387E)
def dz2n388P : Lean.Grind.CommRing.Poly := (.add (72) (.mult ⟨0,2⟩ (.mult ⟨1,1⟩ (.mult ⟨3,7⟩ (.mult ⟨4,3⟩ (.mult ⟨6,1⟩ .unit))))) (.add (72) (.mult ⟨0,2⟩ (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,6⟩ (.mult ⟨4,3⟩ .unit))))) (.add (-144) (.mult ⟨0,1⟩ (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,5⟩ (.mult ⟨4,3⟩ (.mult ⟨6,1⟩ .unit)))))) (.add (24) (.mult ⟨0,2⟩ (.mult ⟨3,6⟩ (.mult ⟨4,2⟩ (.mult ⟨5,1⟩ (.mult ⟨6,1⟩ .unit))))) (.add (24) (.mult ⟨0,2⟩ (.mult ⟨2,1⟩ (.mult ⟨3,5⟩ (.mult ⟨4,2⟩ (.mult ⟨5,1⟩ .unit))))) (.add (144) (.mult ⟨1,2⟩ (.mult ⟨2,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,3⟩ (.mult ⟨6,1⟩ .unit))))) (.add (-48) (.mult ⟨0,1⟩ (.mult ⟨1,1⟩ (.mult ⟨3,5⟩ (.mult ⟨4,2⟩ (.mult ⟨5,1⟩ (.mult ⟨6,1⟩ .unit)))))) (.add (-48) (.mult ⟨0,1⟩ (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨5,1⟩ .unit)))))) (.add (12) (.mult ⟨0,1⟩ (.mult ⟨1,1⟩ (.mult ⟨3,5⟩ (.mult ⟨4,2⟩ (.mult ⟨6,1⟩ .unit))))) (.add (72) (.mult ⟨1,1⟩ (.mult ⟨2,2⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨6,1⟩ .unit))))) (.add (24) (.mult ⟨1,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨5,1⟩ (.mult ⟨6,1⟩ .unit))))) (.add (-48) (.mult ⟨0,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨5,1⟩ (.mult ⟨6,1⟩ .unit)))))) (.add (24) (.mult ⟨1,2⟩ (.mult ⟨2,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨5,1⟩ .unit))))) (.add (-48) (.mult ⟨0,1⟩ (.mult ⟨2,2⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨5,1⟩ .unit))))) (.add (48) (.mult ⟨0,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨6,1⟩ .unit))))) (.add (48) (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨5,1⟩ (.mult ⟨6,1⟩ .unit)))))) (.add (-12) (.mult ⟨0,1⟩ (.mult ⟨1,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,1⟩ (.mult ⟨5,1⟩ .unit))))) (.add (48) (.mult ⟨1,1⟩ (.mult ⟨2,2⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨5,1⟩ .unit))))) (.add (-108) (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨6,1⟩ .unit))))) (.add (-12) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,1⟩ (.mult ⟨5,1⟩ (.mult ⟨6,1⟩ .unit))))) (.add (24) (.mult ⟨2,2⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨5,1⟩ (.mult ⟨6,1⟩ .unit))))) (.add (-24) (.mult ⟨0,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,1⟩ (.mult ⟨5,1⟩ .unit))))) (.add (12) (.mult ⟨1,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,1⟩ (.mult ⟨5,1⟩ (.mult ⟨6,1⟩ .unit))))) (.add (36) (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨5,1⟩ .unit))))) (.add (12) (.mult ⟨2,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨5,1⟩ (.mult ⟨6,1⟩ .unit))))) (.num (0)))))))))))))))))))))))))))
theorem dz2n388_norm : (reflectRing dz2n388E).toPoly=dz2n388P := by
  change (reflectRing dz2n348E).toPoly.combine (reflectRing dz2n387E).toPoly=dz2n388P
  rw [dz2n348_norm, dz2n387_norm]
  exact eq_of_beq (by decide : dz2n348P.combine dz2n387P == dz2n388P)

def dz2n389E : RingExpr := (.add dz2n347E dz2n388E)
def dz2n389P : Lean.Grind.CommRing.Poly := (.add (72) (.mult ⟨0,2⟩ (.mult ⟨1,1⟩ (.mult ⟨3,7⟩ (.mult ⟨4,3⟩ (.mult ⟨6,1⟩ .unit))))) (.add (72) (.mult ⟨0,2⟩ (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,6⟩ (.mult ⟨4,3⟩ .unit))))) (.add (-144) (.mult ⟨0,1⟩ (.mult ⟨1,2⟩ (.mult ⟨2,1⟩ (.mult ⟨3,5⟩ (.mult ⟨4,3⟩ .unit))))) (.add (-144) (.mult ⟨0,1⟩ (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,5⟩ (.mult ⟨4,3⟩ (.mult ⟨6,1⟩ .unit)))))) (.add (24) (.mult ⟨0,2⟩ (.mult ⟨3,6⟩ (.mult ⟨4,2⟩ (.mult ⟨5,1⟩ (.mult ⟨6,1⟩ .unit))))) (.add (24) (.mult ⟨0,2⟩ (.mult ⟨2,1⟩ (.mult ⟨3,5⟩ (.mult ⟨4,2⟩ (.mult ⟨5,1⟩ .unit))))) (.add (144) (.mult ⟨1,2⟩ (.mult ⟨2,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,3⟩ (.mult ⟨6,1⟩ .unit))))) (.add (-48) (.mult ⟨0,1⟩ (.mult ⟨1,1⟩ (.mult ⟨3,5⟩ (.mult ⟨4,2⟩ (.mult ⟨5,1⟩ (.mult ⟨6,1⟩ .unit)))))) (.add (-48) (.mult ⟨0,1⟩ (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨5,1⟩ .unit)))))) (.add (12) (.mult ⟨0,1⟩ (.mult ⟨1,1⟩ (.mult ⟨3,5⟩ (.mult ⟨4,2⟩ (.mult ⟨6,1⟩ .unit))))) (.add (72) (.mult ⟨1,1⟩ (.mult ⟨2,2⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨6,1⟩ .unit))))) (.add (24) (.mult ⟨1,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨5,1⟩ (.mult ⟨6,1⟩ .unit))))) (.add (-48) (.mult ⟨0,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨5,1⟩ (.mult ⟨6,1⟩ .unit)))))) (.add (24) (.mult ⟨1,2⟩ (.mult ⟨2,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨5,1⟩ .unit))))) (.add (-48) (.mult ⟨0,1⟩ (.mult ⟨2,2⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨5,1⟩ .unit))))) (.add (48) (.mult ⟨0,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨6,1⟩ .unit))))) (.add (48) (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨5,1⟩ (.mult ⟨6,1⟩ .unit)))))) (.add (-12) (.mult ⟨0,1⟩ (.mult ⟨1,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,1⟩ (.mult ⟨5,1⟩ .unit))))) (.add (48) (.mult ⟨1,1⟩ (.mult ⟨2,2⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨5,1⟩ .unit))))) (.add (-108) (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨6,1⟩ .unit))))) (.add (-12) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,1⟩ (.mult ⟨5,1⟩ (.mult ⟨6,1⟩ .unit))))) (.add (24) (.mult ⟨2,2⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨5,1⟩ (.mult ⟨6,1⟩ .unit))))) (.add (-24) (.mult ⟨0,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,1⟩ (.mult ⟨5,1⟩ .unit))))) (.add (12) (.mult ⟨1,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,1⟩ (.mult ⟨5,1⟩ (.mult ⟨6,1⟩ .unit))))) (.add (36) (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨5,1⟩ .unit))))) (.add (12) (.mult ⟨2,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨5,1⟩ (.mult ⟨6,1⟩ .unit))))) (.num (0))))))))))))))))))))))))))))
theorem dz2n389_norm : (reflectRing dz2n389E).toPoly=dz2n389P := by
  change (reflectRing dz2n347E).toPoly.combine (reflectRing dz2n388E).toPoly=dz2n389P
  rw [dz2n347_norm, dz2n388_norm]
  exact eq_of_beq (by decide : dz2n347P.combine dz2n388P == dz2n389P)

def dz2n390E : RingExpr := (.add dz2n346E dz2n389E)
def dz2n390P : Lean.Grind.CommRing.Poly := (.add (72) (.mult ⟨0,2⟩ (.mult ⟨1,1⟩ (.mult ⟨3,7⟩ (.mult ⟨4,3⟩ (.mult ⟨6,1⟩ .unit))))) (.add (72) (.mult ⟨0,2⟩ (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,6⟩ (.mult ⟨4,3⟩ .unit))))) (.add (-144) (.mult ⟨0,1⟩ (.mult ⟨1,2⟩ (.mult ⟨3,6⟩ (.mult ⟨4,3⟩ (.mult ⟨6,1⟩ .unit))))) (.add (-144) (.mult ⟨0,1⟩ (.mult ⟨1,2⟩ (.mult ⟨2,1⟩ (.mult ⟨3,5⟩ (.mult ⟨4,3⟩ .unit))))) (.add (-144) (.mult ⟨0,1⟩ (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,5⟩ (.mult ⟨4,3⟩ (.mult ⟨6,1⟩ .unit)))))) (.add (24) (.mult ⟨0,2⟩ (.mult ⟨3,6⟩ (.mult ⟨4,2⟩ (.mult ⟨5,1⟩ (.mult ⟨6,1⟩ .unit))))) (.add (24) (.mult ⟨0,2⟩ (.mult ⟨2,1⟩ (.mult ⟨3,5⟩ (.mult ⟨4,2⟩ (.mult ⟨5,1⟩ .unit))))) (.add (144) (.mult ⟨1,2⟩ (.mult ⟨2,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,3⟩ (.mult ⟨6,1⟩ .unit))))) (.add (-48) (.mult ⟨0,1⟩ (.mult ⟨1,1⟩ (.mult ⟨3,5⟩ (.mult ⟨4,2⟩ (.mult ⟨5,1⟩ (.mult ⟨6,1⟩ .unit)))))) (.add (-48) (.mult ⟨0,1⟩ (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨5,1⟩ .unit)))))) (.add (12) (.mult ⟨0,1⟩ (.mult ⟨1,1⟩ (.mult ⟨3,5⟩ (.mult ⟨4,2⟩ (.mult ⟨6,1⟩ .unit))))) (.add (72) (.mult ⟨1,1⟩ (.mult ⟨2,2⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨6,1⟩ .unit))))) (.add (24) (.mult ⟨1,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨5,1⟩ (.mult ⟨6,1⟩ .unit))))) (.add (-48) (.mult ⟨0,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨5,1⟩ (.mult ⟨6,1⟩ .unit)))))) (.add (24) (.mult ⟨1,2⟩ (.mult ⟨2,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨5,1⟩ .unit))))) (.add (-48) (.mult ⟨0,1⟩ (.mult ⟨2,2⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨5,1⟩ .unit))))) (.add (48) (.mult ⟨0,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨6,1⟩ .unit))))) (.add (48) (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨5,1⟩ (.mult ⟨6,1⟩ .unit)))))) (.add (-12) (.mult ⟨0,1⟩ (.mult ⟨1,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,1⟩ (.mult ⟨5,1⟩ .unit))))) (.add (48) (.mult ⟨1,1⟩ (.mult ⟨2,2⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨5,1⟩ .unit))))) (.add (-108) (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨6,1⟩ .unit))))) (.add (-12) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,1⟩ (.mult ⟨5,1⟩ (.mult ⟨6,1⟩ .unit))))) (.add (24) (.mult ⟨2,2⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨5,1⟩ (.mult ⟨6,1⟩ .unit))))) (.add (-24) (.mult ⟨0,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,1⟩ (.mult ⟨5,1⟩ .unit))))) (.add (12) (.mult ⟨1,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,1⟩ (.mult ⟨5,1⟩ (.mult ⟨6,1⟩ .unit))))) (.add (36) (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨5,1⟩ .unit))))) (.add (12) (.mult ⟨2,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨5,1⟩ (.mult ⟨6,1⟩ .unit))))) (.num (0)))))))))))))))))))))))))))))
theorem dz2n390_norm : (reflectRing dz2n390E).toPoly=dz2n390P := by
  change (reflectRing dz2n346E).toPoly.combine (reflectRing dz2n389E).toPoly=dz2n390P
  rw [dz2n346_norm, dz2n389_norm]
  exact eq_of_beq (by decide : dz2n346P.combine dz2n389P == dz2n390P)

def dz2n391E : RingExpr := (.add dz2n345E dz2n390E)
def dz2n391P : Lean.Grind.CommRing.Poly := (.add (72) (.mult ⟨0,2⟩ (.mult ⟨1,1⟩ (.mult ⟨3,7⟩ (.mult ⟨4,3⟩ (.mult ⟨6,1⟩ .unit))))) (.add (72) (.mult ⟨0,2⟩ (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,6⟩ (.mult ⟨4,3⟩ .unit))))) (.add (-144) (.mult ⟨0,1⟩ (.mult ⟨1,2⟩ (.mult ⟨3,6⟩ (.mult ⟨4,3⟩ (.mult ⟨6,1⟩ .unit))))) (.add (-144) (.mult ⟨0,1⟩ (.mult ⟨1,2⟩ (.mult ⟨2,1⟩ (.mult ⟨3,5⟩ (.mult ⟨4,3⟩ .unit))))) (.add (-144) (.mult ⟨0,1⟩ (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,5⟩ (.mult ⟨4,3⟩ (.mult ⟨6,1⟩ .unit)))))) (.add (24) (.mult ⟨0,2⟩ (.mult ⟨3,6⟩ (.mult ⟨4,2⟩ (.mult ⟨5,1⟩ (.mult ⟨6,1⟩ .unit))))) (.add (-144) (.mult ⟨0,1⟩ (.mult ⟨1,1⟩ (.mult ⟨2,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,3⟩ .unit))))) (.add (24) (.mult ⟨0,2⟩ (.mult ⟨2,1⟩ (.mult ⟨3,5⟩ (.mult ⟨4,2⟩ (.mult ⟨5,1⟩ .unit))))) (.add (144) (.mult ⟨1,2⟩ (.mult ⟨2,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,3⟩ (.mult ⟨6,1⟩ .unit))))) (.add (-48) (.mult ⟨0,1⟩ (.mult ⟨1,1⟩ (.mult ⟨3,5⟩ (.mult ⟨4,2⟩ (.mult ⟨5,1⟩ (.mult ⟨6,1⟩ .unit)))))) (.add (-48) (.mult ⟨0,1⟩ (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨5,1⟩ .unit)))))) (.add (12) (.mult ⟨0,1⟩ (.mult ⟨1,1⟩ (.mult ⟨3,5⟩ (.mult ⟨4,2⟩ (.mult ⟨6,1⟩ .unit))))) (.add (72) (.mult ⟨1,1⟩ (.mult ⟨2,2⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨6,1⟩ .unit))))) (.add (24) (.mult ⟨1,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨5,1⟩ (.mult ⟨6,1⟩ .unit))))) (.add (-48) (.mult ⟨0,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨5,1⟩ (.mult ⟨6,1⟩ .unit)))))) (.add (24) (.mult ⟨1,2⟩ (.mult ⟨2,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨5,1⟩ .unit))))) (.add (-48) (.mult ⟨0,1⟩ (.mult ⟨2,2⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨5,1⟩ .unit))))) (.add (48) (.mult ⟨0,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨6,1⟩ .unit))))) (.add (48) (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨5,1⟩ (.mult ⟨6,1⟩ .unit)))))) (.add (-12) (.mult ⟨0,1⟩ (.mult ⟨1,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,1⟩ (.mult ⟨5,1⟩ .unit))))) (.add (48) (.mult ⟨1,1⟩ (.mult ⟨2,2⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨5,1⟩ .unit))))) (.add (-108) (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨6,1⟩ .unit))))) (.add (-12) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,1⟩ (.mult ⟨5,1⟩ (.mult ⟨6,1⟩ .unit))))) (.add (24) (.mult ⟨2,2⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨5,1⟩ (.mult ⟨6,1⟩ .unit))))) (.add (-24) (.mult ⟨0,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,1⟩ (.mult ⟨5,1⟩ .unit))))) (.add (12) (.mult ⟨1,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,1⟩ (.mult ⟨5,1⟩ (.mult ⟨6,1⟩ .unit))))) (.add (36) (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨5,1⟩ .unit))))) (.add (12) (.mult ⟨2,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨5,1⟩ (.mult ⟨6,1⟩ .unit))))) (.num (0))))))))))))))))))))))))))))))
theorem dz2n391_norm : (reflectRing dz2n391E).toPoly=dz2n391P := by
  change (reflectRing dz2n345E).toPoly.combine (reflectRing dz2n390E).toPoly=dz2n391P
  rw [dz2n345_norm, dz2n390_norm]
  exact eq_of_beq (by decide : dz2n345P.combine dz2n390P == dz2n391P)

def dz2n392E : RingExpr := (.add dz2n344E dz2n391E)
def dz2n392P : Lean.Grind.CommRing.Poly := (.add (72) (.mult ⟨0,2⟩ (.mult ⟨1,1⟩ (.mult ⟨3,7⟩ (.mult ⟨4,3⟩ (.mult ⟨6,1⟩ .unit))))) (.add (72) (.mult ⟨0,2⟩ (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,6⟩ (.mult ⟨4,3⟩ .unit))))) (.add (-144) (.mult ⟨0,1⟩ (.mult ⟨1,2⟩ (.mult ⟨3,6⟩ (.mult ⟨4,3⟩ (.mult ⟨6,1⟩ .unit))))) (.add (-144) (.mult ⟨0,1⟩ (.mult ⟨1,2⟩ (.mult ⟨2,1⟩ (.mult ⟨3,5⟩ (.mult ⟨4,3⟩ .unit))))) (.add (-144) (.mult ⟨0,1⟩ (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,5⟩ (.mult ⟨4,3⟩ (.mult ⟨6,1⟩ .unit)))))) (.add (24) (.mult ⟨0,2⟩ (.mult ⟨3,6⟩ (.mult ⟨4,2⟩ (.mult ⟨5,1⟩ (.mult ⟨6,1⟩ .unit))))) (.add (-144) (.mult ⟨0,1⟩ (.mult ⟨1,1⟩ (.mult ⟨2,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,3⟩ .unit))))) (.add (24) (.mult ⟨0,2⟩ (.mult ⟨2,1⟩ (.mult ⟨3,5⟩ (.mult ⟨4,2⟩ (.mult ⟨5,1⟩ .unit))))) (.add (144) (.mult ⟨1,2⟩ (.mult ⟨2,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,3⟩ (.mult ⟨6,1⟩ .unit))))) (.add (-48) (.mult ⟨0,1⟩ (.mult ⟨1,1⟩ (.mult ⟨3,5⟩ (.mult ⟨4,2⟩ (.mult ⟨5,1⟩ (.mult ⟨6,1⟩ .unit)))))) (.add (144) (.mult ⟨1,2⟩ (.mult ⟨2,2⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ .unit)))) (.add (-48) (.mult ⟨0,1⟩ (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨5,1⟩ .unit)))))) (.add (12) (.mult ⟨0,1⟩ (.mult ⟨1,1⟩ (.mult ⟨3,5⟩ (.mult ⟨4,2⟩ (.mult ⟨6,1⟩ .unit))))) (.add (72) (.mult ⟨1,1⟩ (.mult ⟨2,2⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨6,1⟩ .unit))))) (.add (24) (.mult ⟨1,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨5,1⟩ (.mult ⟨6,1⟩ .unit))))) (.add (-48) (.mult ⟨0,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨5,1⟩ (.mult ⟨6,1⟩ .unit)))))) (.add (24) (.mult ⟨1,2⟩ (.mult ⟨2,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨5,1⟩ .unit))))) (.add (-48) (.mult ⟨0,1⟩ (.mult ⟨2,2⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨5,1⟩ .unit))))) (.add (48) (.mult ⟨0,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨6,1⟩ .unit))))) (.add (48) (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨5,1⟩ (.mult ⟨6,1⟩ .unit)))))) (.add (-12) (.mult ⟨0,1⟩ (.mult ⟨1,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,1⟩ (.mult ⟨5,1⟩ .unit))))) (.add (48) (.mult ⟨1,1⟩ (.mult ⟨2,2⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨5,1⟩ .unit))))) (.add (-108) (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨6,1⟩ .unit))))) (.add (-12) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,1⟩ (.mult ⟨5,1⟩ (.mult ⟨6,1⟩ .unit))))) (.add (24) (.mult ⟨2,2⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨5,1⟩ (.mult ⟨6,1⟩ .unit))))) (.add (-24) (.mult ⟨0,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,1⟩ (.mult ⟨5,1⟩ .unit))))) (.add (12) (.mult ⟨1,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,1⟩ (.mult ⟨5,1⟩ (.mult ⟨6,1⟩ .unit))))) (.add (36) (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨5,1⟩ .unit))))) (.add (12) (.mult ⟨2,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨5,1⟩ (.mult ⟨6,1⟩ .unit))))) (.num (0)))))))))))))))))))))))))))))))
theorem dz2n392_norm : (reflectRing dz2n392E).toPoly=dz2n392P := by
  change (reflectRing dz2n344E).toPoly.combine (reflectRing dz2n391E).toPoly=dz2n392P
  rw [dz2n344_norm, dz2n391_norm]
  exact eq_of_beq (by decide : dz2n344P.combine dz2n391P == dz2n392P)

def dz2n393E : RingExpr := (.add dz2n343E dz2n392E)
def dz2n393P : Lean.Grind.CommRing.Poly := (.add (72) (.mult ⟨0,2⟩ (.mult ⟨1,1⟩ (.mult ⟨3,7⟩ (.mult ⟨4,3⟩ (.mult ⟨6,1⟩ .unit))))) (.add (72) (.mult ⟨0,2⟩ (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,6⟩ (.mult ⟨4,3⟩ .unit))))) (.add (-144) (.mult ⟨0,1⟩ (.mult ⟨1,2⟩ (.mult ⟨3,6⟩ (.mult ⟨4,3⟩ (.mult ⟨6,1⟩ .unit))))) (.add (-144) (.mult ⟨0,1⟩ (.mult ⟨1,2⟩ (.mult ⟨2,1⟩ (.mult ⟨3,5⟩ (.mult ⟨4,3⟩ .unit))))) (.add (-144) (.mult ⟨0,1⟩ (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,5⟩ (.mult ⟨4,3⟩ (.mult ⟨6,1⟩ .unit)))))) (.add (24) (.mult ⟨0,2⟩ (.mult ⟨3,6⟩ (.mult ⟨4,2⟩ (.mult ⟨5,1⟩ (.mult ⟨6,1⟩ .unit))))) (.add (72) (.mult ⟨1,3⟩ (.mult ⟨2,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,3⟩ .unit)))) (.add (-144) (.mult ⟨0,1⟩ (.mult ⟨1,1⟩ (.mult ⟨2,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,3⟩ .unit))))) (.add (24) (.mult ⟨0,2⟩ (.mult ⟨2,1⟩ (.mult ⟨3,5⟩ (.mult ⟨4,2⟩ (.mult ⟨5,1⟩ .unit))))) (.add (144) (.mult ⟨1,2⟩ (.mult ⟨2,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,3⟩ (.mult ⟨6,1⟩ .unit))))) (.add (-48) (.mult ⟨0,1⟩ (.mult ⟨1,1⟩ (.mult ⟨3,5⟩ (.mult ⟨4,2⟩ (.mult ⟨5,1⟩ (.mult ⟨6,1⟩ .unit)))))) (.add (144) (.mult ⟨1,2⟩ (.mult ⟨2,2⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ .unit)))) (.add (-48) (.mult ⟨0,1⟩ (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨5,1⟩ .unit)))))) (.add (12) (.mult ⟨0,1⟩ (.mult ⟨1,1⟩ (.mult ⟨3,5⟩ (.mult ⟨4,2⟩ (.mult ⟨6,1⟩ .unit))))) (.add (72) (.mult ⟨1,1⟩ (.mult ⟨2,2⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨6,1⟩ .unit))))) (.add (24) (.mult ⟨1,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨5,1⟩ (.mult ⟨6,1⟩ .unit))))) (.add (-48) (.mult ⟨0,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨5,1⟩ (.mult ⟨6,1⟩ .unit)))))) (.add (24) (.mult ⟨1,2⟩ (.mult ⟨2,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨5,1⟩ .unit))))) (.add (-48) (.mult ⟨0,1⟩ (.mult ⟨2,2⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨5,1⟩ .unit))))) (.add (48) (.mult ⟨0,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨6,1⟩ .unit))))) (.add (48) (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨5,1⟩ (.mult ⟨6,1⟩ .unit)))))) (.add (-12) (.mult ⟨0,1⟩ (.mult ⟨1,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,1⟩ (.mult ⟨5,1⟩ .unit))))) (.add (48) (.mult ⟨1,1⟩ (.mult ⟨2,2⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨5,1⟩ .unit))))) (.add (-108) (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨6,1⟩ .unit))))) (.add (-12) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,1⟩ (.mult ⟨5,1⟩ (.mult ⟨6,1⟩ .unit))))) (.add (24) (.mult ⟨2,2⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨5,1⟩ (.mult ⟨6,1⟩ .unit))))) (.add (-24) (.mult ⟨0,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,1⟩ (.mult ⟨5,1⟩ .unit))))) (.add (12) (.mult ⟨1,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,1⟩ (.mult ⟨5,1⟩ (.mult ⟨6,1⟩ .unit))))) (.add (36) (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨5,1⟩ .unit))))) (.add (12) (.mult ⟨2,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨5,1⟩ (.mult ⟨6,1⟩ .unit))))) (.num (0))))))))))))))))))))))))))))))))
theorem dz2n393_norm : (reflectRing dz2n393E).toPoly=dz2n393P := by
  change (reflectRing dz2n343E).toPoly.combine (reflectRing dz2n392E).toPoly=dz2n393P
  rw [dz2n343_norm, dz2n392_norm]
  exact eq_of_beq (by decide : dz2n343P.combine dz2n392P == dz2n393P)

def dz2n394E : RingExpr := (.add dz2n342E dz2n393E)
def dz2n394P : Lean.Grind.CommRing.Poly := (.add (72) (.mult ⟨0,2⟩ (.mult ⟨1,1⟩ (.mult ⟨3,7⟩ (.mult ⟨4,3⟩ (.mult ⟨6,1⟩ .unit))))) (.add (72) (.mult ⟨0,2⟩ (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,6⟩ (.mult ⟨4,3⟩ .unit))))) (.add (-144) (.mult ⟨0,1⟩ (.mult ⟨1,2⟩ (.mult ⟨3,6⟩ (.mult ⟨4,3⟩ (.mult ⟨6,1⟩ .unit))))) (.add (-144) (.mult ⟨0,1⟩ (.mult ⟨1,2⟩ (.mult ⟨2,1⟩ (.mult ⟨3,5⟩ (.mult ⟨4,3⟩ .unit))))) (.add (72) (.mult ⟨1,3⟩ (.mult ⟨3,5⟩ (.mult ⟨4,3⟩ (.mult ⟨6,1⟩ .unit)))) (.add (-144) (.mult ⟨0,1⟩ (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,5⟩ (.mult ⟨4,3⟩ (.mult ⟨6,1⟩ .unit)))))) (.add (24) (.mult ⟨0,2⟩ (.mult ⟨3,6⟩ (.mult ⟨4,2⟩ (.mult ⟨5,1⟩ (.mult ⟨6,1⟩ .unit))))) (.add (72) (.mult ⟨1,3⟩ (.mult ⟨2,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,3⟩ .unit)))) (.add (-144) (.mult ⟨0,1⟩ (.mult ⟨1,1⟩ (.mult ⟨2,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,3⟩ .unit))))) (.add (24) (.mult ⟨0,2⟩ (.mult ⟨2,1⟩ (.mult ⟨3,5⟩ (.mult ⟨4,2⟩ (.mult ⟨5,1⟩ .unit))))) (.add (144) (.mult ⟨1,2⟩ (.mult ⟨2,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,3⟩ (.mult ⟨6,1⟩ .unit))))) (.add (-48) (.mult ⟨0,1⟩ (.mult ⟨1,1⟩ (.mult ⟨3,5⟩ (.mult ⟨4,2⟩ (.mult ⟨5,1⟩ (.mult ⟨6,1⟩ .unit)))))) (.add (144) (.mult ⟨1,2⟩ (.mult ⟨2,2⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ .unit)))) (.add (-48) (.mult ⟨0,1⟩ (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨5,1⟩ .unit)))))) (.add (12) (.mult ⟨0,1⟩ (.mult ⟨1,1⟩ (.mult ⟨3,5⟩ (.mult ⟨4,2⟩ (.mult ⟨6,1⟩ .unit))))) (.add (72) (.mult ⟨1,1⟩ (.mult ⟨2,2⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨6,1⟩ .unit))))) (.add (24) (.mult ⟨1,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨5,1⟩ (.mult ⟨6,1⟩ .unit))))) (.add (-48) (.mult ⟨0,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨5,1⟩ (.mult ⟨6,1⟩ .unit)))))) (.add (24) (.mult ⟨1,2⟩ (.mult ⟨2,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨5,1⟩ .unit))))) (.add (-48) (.mult ⟨0,1⟩ (.mult ⟨2,2⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨5,1⟩ .unit))))) (.add (48) (.mult ⟨0,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨6,1⟩ .unit))))) (.add (48) (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨5,1⟩ (.mult ⟨6,1⟩ .unit)))))) (.add (-12) (.mult ⟨0,1⟩ (.mult ⟨1,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,1⟩ (.mult ⟨5,1⟩ .unit))))) (.add (48) (.mult ⟨1,1⟩ (.mult ⟨2,2⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨5,1⟩ .unit))))) (.add (-108) (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨6,1⟩ .unit))))) (.add (-12) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,1⟩ (.mult ⟨5,1⟩ (.mult ⟨6,1⟩ .unit))))) (.add (24) (.mult ⟨2,2⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨5,1⟩ (.mult ⟨6,1⟩ .unit))))) (.add (-24) (.mult ⟨0,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,1⟩ (.mult ⟨5,1⟩ .unit))))) (.add (12) (.mult ⟨1,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,1⟩ (.mult ⟨5,1⟩ (.mult ⟨6,1⟩ .unit))))) (.add (36) (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨5,1⟩ .unit))))) (.add (12) (.mult ⟨2,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨5,1⟩ (.mult ⟨6,1⟩ .unit))))) (.num (0)))))))))))))))))))))))))))))))))
theorem dz2n394_norm : (reflectRing dz2n394E).toPoly=dz2n394P := by
  change (reflectRing dz2n342E).toPoly.combine (reflectRing dz2n393E).toPoly=dz2n394P
  rw [dz2n342_norm, dz2n393_norm]
  exact eq_of_beq (by decide : dz2n342P.combine dz2n393P == dz2n394P)

def dz2n395E : RingExpr := (.add dz2n341E dz2n394E)
def dz2n395P : Lean.Grind.CommRing.Poly := (.add (72) (.mult ⟨0,2⟩ (.mult ⟨1,1⟩ (.mult ⟨3,7⟩ (.mult ⟨4,3⟩ (.mult ⟨6,1⟩ .unit))))) (.add (72) (.mult ⟨0,2⟩ (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,6⟩ (.mult ⟨4,3⟩ .unit))))) (.add (-144) (.mult ⟨0,1⟩ (.mult ⟨1,2⟩ (.mult ⟨3,6⟩ (.mult ⟨4,3⟩ (.mult ⟨6,1⟩ .unit))))) (.add (-144) (.mult ⟨0,1⟩ (.mult ⟨1,2⟩ (.mult ⟨2,1⟩ (.mult ⟨3,5⟩ (.mult ⟨4,3⟩ .unit))))) (.add (72) (.mult ⟨1,3⟩ (.mult ⟨3,5⟩ (.mult ⟨4,3⟩ (.mult ⟨6,1⟩ .unit)))) (.add (-144) (.mult ⟨0,1⟩ (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,5⟩ (.mult ⟨4,3⟩ (.mult ⟨6,1⟩ .unit)))))) (.add (24) (.mult ⟨0,2⟩ (.mult ⟨3,6⟩ (.mult ⟨4,2⟩ (.mult ⟨5,1⟩ (.mult ⟨6,1⟩ .unit))))) (.add (72) (.mult ⟨1,3⟩ (.mult ⟨2,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,3⟩ .unit)))) (.add (-144) (.mult ⟨0,1⟩ (.mult ⟨1,1⟩ (.mult ⟨2,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,3⟩ .unit))))) (.add (24) (.mult ⟨0,2⟩ (.mult ⟨2,1⟩ (.mult ⟨3,5⟩ (.mult ⟨4,2⟩ (.mult ⟨5,1⟩ .unit))))) (.add (144) (.mult ⟨1,2⟩ (.mult ⟨2,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,3⟩ (.mult ⟨6,1⟩ .unit))))) (.add (-48) (.mult ⟨0,1⟩ (.mult ⟨1,1⟩ (.mult ⟨3,5⟩ (.mult ⟨4,2⟩ (.mult ⟨5,1⟩ (.mult ⟨6,1⟩ .unit)))))) (.add (144) (.mult ⟨1,2⟩ (.mult ⟨2,2⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ .unit)))) (.add (-48) (.mult ⟨0,1⟩ (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨5,1⟩ .unit)))))) (.add (12) (.mult ⟨0,1⟩ (.mult ⟨1,1⟩ (.mult ⟨3,5⟩ (.mult ⟨4,2⟩ (.mult ⟨6,1⟩ .unit))))) (.add (72) (.mult ⟨1,1⟩ (.mult ⟨2,2⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨6,1⟩ .unit))))) (.add (24) (.mult ⟨1,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨5,1⟩ (.mult ⟨6,1⟩ .unit))))) (.add (-48) (.mult ⟨0,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨5,1⟩ (.mult ⟨6,1⟩ .unit)))))) (.add (72) (.mult ⟨1,1⟩ (.mult ⟨2,3⟩ (.mult ⟨3,2⟩ (.mult ⟨4,3⟩ .unit)))) (.add (24) (.mult ⟨1,2⟩ (.mult ⟨2,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨5,1⟩ .unit))))) (.add (-48) (.mult ⟨0,1⟩ (.mult ⟨2,2⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨5,1⟩ .unit))))) (.add (48) (.mult ⟨0,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨6,1⟩ .unit))))) (.add (48) (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨5,1⟩ (.mult ⟨6,1⟩ .unit)))))) (.add (-12) (.mult ⟨0,1⟩ (.mult ⟨1,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,1⟩ (.mult ⟨5,1⟩ .unit))))) (.add (48) (.mult ⟨1,1⟩ (.mult ⟨2,2⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨5,1⟩ .unit))))) (.add (-108) (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨6,1⟩ .unit))))) (.add (-12) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,1⟩ (.mult ⟨5,1⟩ (.mult ⟨6,1⟩ .unit))))) (.add (24) (.mult ⟨2,2⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨5,1⟩ (.mult ⟨6,1⟩ .unit))))) (.add (-24) (.mult ⟨0,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,1⟩ (.mult ⟨5,1⟩ .unit))))) (.add (12) (.mult ⟨1,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,1⟩ (.mult ⟨5,1⟩ (.mult ⟨6,1⟩ .unit))))) (.add (36) (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨5,1⟩ .unit))))) (.add (12) (.mult ⟨2,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨5,1⟩ (.mult ⟨6,1⟩ .unit))))) (.num (0))))))))))))))))))))))))))))))))))
theorem dz2n395_norm : (reflectRing dz2n395E).toPoly=dz2n395P := by
  change (reflectRing dz2n341E).toPoly.combine (reflectRing dz2n394E).toPoly=dz2n395P
  rw [dz2n341_norm, dz2n394_norm]
  exact eq_of_beq (by decide : dz2n341P.combine dz2n394P == dz2n395P)

def dz2n396E : RingExpr := (.add dz2n269E dz2n395E)
def dz2n396P : Lean.Grind.CommRing.Poly := (.add (72) (.mult ⟨0,2⟩ (.mult ⟨1,1⟩ (.mult ⟨3,7⟩ (.mult ⟨4,3⟩ (.mult ⟨6,1⟩ .unit))))) (.add (72) (.mult ⟨0,2⟩ (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,6⟩ (.mult ⟨4,3⟩ .unit))))) (.add (-144) (.mult ⟨0,1⟩ (.mult ⟨1,2⟩ (.mult ⟨3,6⟩ (.mult ⟨4,3⟩ (.mult ⟨6,1⟩ .unit))))) (.add (-144) (.mult ⟨0,1⟩ (.mult ⟨1,2⟩ (.mult ⟨2,1⟩ (.mult ⟨3,5⟩ (.mult ⟨4,3⟩ .unit))))) (.add (72) (.mult ⟨1,3⟩ (.mult ⟨3,5⟩ (.mult ⟨4,3⟩ (.mult ⟨6,1⟩ .unit)))) (.add (-144) (.mult ⟨0,1⟩ (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,5⟩ (.mult ⟨4,3⟩ (.mult ⟨6,1⟩ .unit)))))) (.add (24) (.mult ⟨0,2⟩ (.mult ⟨3,6⟩ (.mult ⟨4,2⟩ (.mult ⟨5,1⟩ (.mult ⟨6,1⟩ .unit))))) (.add (72) (.mult ⟨1,3⟩ (.mult ⟨2,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,3⟩ .unit)))) (.add (-144) (.mult ⟨0,1⟩ (.mult ⟨1,1⟩ (.mult ⟨2,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,3⟩ .unit))))) (.add (24) (.mult ⟨0,2⟩ (.mult ⟨2,1⟩ (.mult ⟨3,5⟩ (.mult ⟨4,2⟩ (.mult ⟨5,1⟩ .unit))))) (.add (144) (.mult ⟨1,2⟩ (.mult ⟨2,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,3⟩ (.mult ⟨6,1⟩ .unit))))) (.add (-48) (.mult ⟨0,1⟩ (.mult ⟨1,1⟩ (.mult ⟨3,5⟩ (.mult ⟨4,2⟩ (.mult ⟨5,1⟩ (.mult ⟨6,1⟩ .unit)))))) (.add (144) (.mult ⟨1,2⟩ (.mult ⟨2,2⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ .unit)))) (.add (-48) (.mult ⟨0,1⟩ (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨5,1⟩ .unit)))))) (.add (12) (.mult ⟨0,1⟩ (.mult ⟨1,1⟩ (.mult ⟨3,5⟩ (.mult ⟨4,2⟩ (.mult ⟨6,1⟩ .unit))))) (.add (72) (.mult ⟨1,1⟩ (.mult ⟨2,2⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨6,1⟩ .unit))))) (.add (24) (.mult ⟨1,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨5,1⟩ (.mult ⟨6,1⟩ .unit))))) (.add (-48) (.mult ⟨0,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨5,1⟩ (.mult ⟨6,1⟩ .unit)))))) (.add (72) (.mult ⟨1,1⟩ (.mult ⟨2,3⟩ (.mult ⟨3,2⟩ (.mult ⟨4,3⟩ .unit)))) (.add (24) (.mult ⟨1,2⟩ (.mult ⟨2,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨5,1⟩ .unit))))) (.add (-48) (.mult ⟨0,1⟩ (.mult ⟨2,2⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨5,1⟩ .unit))))) (.add (48) (.mult ⟨0,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨6,1⟩ .unit))))) (.add (48) (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨5,1⟩ (.mult ⟨6,1⟩ .unit)))))) (.add (72) (.mult ⟨0,1⟩ (.mult ⟨2,2⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ .unit)))) (.add (-12) (.mult ⟨0,1⟩ (.mult ⟨1,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,1⟩ (.mult ⟨5,1⟩ .unit))))) (.add (48) (.mult ⟨1,1⟩ (.mult ⟨2,2⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨5,1⟩ .unit))))) (.add (-108) (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨6,1⟩ .unit))))) (.add (-12) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,1⟩ (.mult ⟨5,1⟩ (.mult ⟨6,1⟩ .unit))))) (.add (24) (.mult ⟨2,2⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨5,1⟩ (.mult ⟨6,1⟩ .unit))))) (.add (-24) (.mult ⟨0,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,1⟩ (.mult ⟨5,1⟩ .unit))))) (.add (12) (.mult ⟨1,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,1⟩ (.mult ⟨5,1⟩ (.mult ⟨6,1⟩ .unit))))) (.add (36) (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨5,1⟩ .unit))))) (.add (12) (.mult ⟨2,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨5,1⟩ (.mult ⟨6,1⟩ .unit))))) (.num (0)))))))))))))))))))))))))))))))))))
theorem dz2n396_norm : (reflectRing dz2n396E).toPoly=dz2n396P := by
  change (reflectRing dz2n269E).toPoly.combine (reflectRing dz2n395E).toPoly=dz2n396P
  rw [dz2n269_norm, dz2n395_norm]
  exact eq_of_beq (by decide : dz2n269P.combine dz2n395P == dz2n396P)

def dz2n397E : RingExpr := (.add dz2n340E dz2n396E)
def dz2n397P : Lean.Grind.CommRing.Poly := (.add (72) (.mult ⟨0,2⟩ (.mult ⟨1,1⟩ (.mult ⟨3,7⟩ (.mult ⟨4,3⟩ (.mult ⟨6,1⟩ .unit))))) (.add (72) (.mult ⟨0,2⟩ (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,6⟩ (.mult ⟨4,3⟩ .unit))))) (.add (-144) (.mult ⟨0,1⟩ (.mult ⟨1,2⟩ (.mult ⟨3,6⟩ (.mult ⟨4,3⟩ (.mult ⟨6,1⟩ .unit))))) (.add (-144) (.mult ⟨0,1⟩ (.mult ⟨1,2⟩ (.mult ⟨2,1⟩ (.mult ⟨3,5⟩ (.mult ⟨4,3⟩ .unit))))) (.add (72) (.mult ⟨1,3⟩ (.mult ⟨3,5⟩ (.mult ⟨4,3⟩ (.mult ⟨6,1⟩ .unit)))) (.add (-144) (.mult ⟨0,1⟩ (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,5⟩ (.mult ⟨4,3⟩ (.mult ⟨6,1⟩ .unit)))))) (.add (24) (.mult ⟨0,2⟩ (.mult ⟨3,6⟩ (.mult ⟨4,2⟩ (.mult ⟨5,1⟩ (.mult ⟨6,1⟩ .unit))))) (.add (72) (.mult ⟨1,3⟩ (.mult ⟨2,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,3⟩ .unit)))) (.add (-144) (.mult ⟨0,1⟩ (.mult ⟨1,1⟩ (.mult ⟨2,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,3⟩ .unit))))) (.add (24) (.mult ⟨0,2⟩ (.mult ⟨2,1⟩ (.mult ⟨3,5⟩ (.mult ⟨4,2⟩ (.mult ⟨5,1⟩ .unit))))) (.add (144) (.mult ⟨1,2⟩ (.mult ⟨2,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,3⟩ (.mult ⟨6,1⟩ .unit))))) (.add (-48) (.mult ⟨0,1⟩ (.mult ⟨1,1⟩ (.mult ⟨3,5⟩ (.mult ⟨4,2⟩ (.mult ⟨5,1⟩ (.mult ⟨6,1⟩ .unit)))))) (.add (144) (.mult ⟨1,2⟩ (.mult ⟨2,2⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ .unit)))) (.add (-48) (.mult ⟨0,1⟩ (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨5,1⟩ .unit)))))) (.add (12) (.mult ⟨0,1⟩ (.mult ⟨1,1⟩ (.mult ⟨3,5⟩ (.mult ⟨4,2⟩ (.mult ⟨6,1⟩ .unit))))) (.add (72) (.mult ⟨1,1⟩ (.mult ⟨2,2⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨6,1⟩ .unit))))) (.add (24) (.mult ⟨1,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨5,1⟩ (.mult ⟨6,1⟩ .unit))))) (.add (-48) (.mult ⟨0,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨5,1⟩ (.mult ⟨6,1⟩ .unit)))))) (.add (72) (.mult ⟨1,1⟩ (.mult ⟨2,3⟩ (.mult ⟨3,2⟩ (.mult ⟨4,3⟩ .unit)))) (.add (24) (.mult ⟨1,2⟩ (.mult ⟨2,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨5,1⟩ .unit))))) (.add (-48) (.mult ⟨0,1⟩ (.mult ⟨2,2⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨5,1⟩ .unit))))) (.add (48) (.mult ⟨0,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨6,1⟩ .unit))))) (.add (48) (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨5,1⟩ (.mult ⟨6,1⟩ .unit)))))) (.add (36) (.mult ⟨1,2⟩ (.mult ⟨2,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ .unit)))) (.add (72) (.mult ⟨0,1⟩ (.mult ⟨2,2⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ .unit)))) (.add (-12) (.mult ⟨0,1⟩ (.mult ⟨1,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,1⟩ (.mult ⟨5,1⟩ .unit))))) (.add (48) (.mult ⟨1,1⟩ (.mult ⟨2,2⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨5,1⟩ .unit))))) (.add (-108) (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨6,1⟩ .unit))))) (.add (-12) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,1⟩ (.mult ⟨5,1⟩ (.mult ⟨6,1⟩ .unit))))) (.add (24) (.mult ⟨2,2⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨5,1⟩ (.mult ⟨6,1⟩ .unit))))) (.add (-24) (.mult ⟨0,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,1⟩ (.mult ⟨5,1⟩ .unit))))) (.add (12) (.mult ⟨1,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,1⟩ (.mult ⟨5,1⟩ (.mult ⟨6,1⟩ .unit))))) (.add (36) (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨5,1⟩ .unit))))) (.add (12) (.mult ⟨2,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨5,1⟩ (.mult ⟨6,1⟩ .unit))))) (.num (0))))))))))))))))))))))))))))))))))))
theorem dz2n397_norm : (reflectRing dz2n397E).toPoly=dz2n397P := by
  change (reflectRing dz2n340E).toPoly.combine (reflectRing dz2n396E).toPoly=dz2n397P
  rw [dz2n340_norm, dz2n396_norm]
  exact eq_of_beq (by decide : dz2n340P.combine dz2n396P == dz2n397P)

def dz2n398E : RingExpr := (.add dz2n339E dz2n397E)
def dz2n398P : Lean.Grind.CommRing.Poly := (.add (72) (.mult ⟨0,2⟩ (.mult ⟨1,1⟩ (.mult ⟨3,7⟩ (.mult ⟨4,3⟩ (.mult ⟨6,1⟩ .unit))))) (.add (72) (.mult ⟨0,2⟩ (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,6⟩ (.mult ⟨4,3⟩ .unit))))) (.add (-144) (.mult ⟨0,1⟩ (.mult ⟨1,2⟩ (.mult ⟨3,6⟩ (.mult ⟨4,3⟩ (.mult ⟨6,1⟩ .unit))))) (.add (-144) (.mult ⟨0,1⟩ (.mult ⟨1,2⟩ (.mult ⟨2,1⟩ (.mult ⟨3,5⟩ (.mult ⟨4,3⟩ .unit))))) (.add (72) (.mult ⟨1,3⟩ (.mult ⟨3,5⟩ (.mult ⟨4,3⟩ (.mult ⟨6,1⟩ .unit)))) (.add (-144) (.mult ⟨0,1⟩ (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,5⟩ (.mult ⟨4,3⟩ (.mult ⟨6,1⟩ .unit)))))) (.add (24) (.mult ⟨0,2⟩ (.mult ⟨3,6⟩ (.mult ⟨4,2⟩ (.mult ⟨5,1⟩ (.mult ⟨6,1⟩ .unit))))) (.add (72) (.mult ⟨1,3⟩ (.mult ⟨2,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,3⟩ .unit)))) (.add (-144) (.mult ⟨0,1⟩ (.mult ⟨1,1⟩ (.mult ⟨2,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,3⟩ .unit))))) (.add (24) (.mult ⟨0,2⟩ (.mult ⟨2,1⟩ (.mult ⟨3,5⟩ (.mult ⟨4,2⟩ (.mult ⟨5,1⟩ .unit))))) (.add (144) (.mult ⟨1,2⟩ (.mult ⟨2,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,3⟩ (.mult ⟨6,1⟩ .unit))))) (.add (-48) (.mult ⟨0,1⟩ (.mult ⟨1,1⟩ (.mult ⟨3,5⟩ (.mult ⟨4,2⟩ (.mult ⟨5,1⟩ (.mult ⟨6,1⟩ .unit)))))) (.add (144) (.mult ⟨1,2⟩ (.mult ⟨2,2⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ .unit)))) (.add (-48) (.mult ⟨0,1⟩ (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨5,1⟩ .unit)))))) (.add (12) (.mult ⟨0,1⟩ (.mult ⟨1,1⟩ (.mult ⟨3,5⟩ (.mult ⟨4,2⟩ (.mult ⟨6,1⟩ .unit))))) (.add (72) (.mult ⟨1,1⟩ (.mult ⟨2,2⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨6,1⟩ .unit))))) (.add (24) (.mult ⟨1,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨5,1⟩ (.mult ⟨6,1⟩ .unit))))) (.add (-48) (.mult ⟨0,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨5,1⟩ (.mult ⟨6,1⟩ .unit)))))) (.add (72) (.mult ⟨1,1⟩ (.mult ⟨2,3⟩ (.mult ⟨3,2⟩ (.mult ⟨4,3⟩ .unit)))) (.add (24) (.mult ⟨1,2⟩ (.mult ⟨2,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨5,1⟩ .unit))))) (.add (-48) (.mult ⟨0,1⟩ (.mult ⟨2,2⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨5,1⟩ .unit))))) (.add (48) (.mult ⟨0,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨6,1⟩ .unit))))) (.add (48) (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨5,1⟩ (.mult ⟨6,1⟩ .unit)))))) (.add (36) (.mult ⟨1,2⟩ (.mult ⟨2,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ .unit)))) (.add (72) (.mult ⟨0,1⟩ (.mult ⟨2,2⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ .unit)))) (.add (-12) (.mult ⟨0,1⟩ (.mult ⟨1,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,1⟩ (.mult ⟨5,1⟩ .unit))))) (.add (48) (.mult ⟨1,1⟩ (.mult ⟨2,2⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨5,1⟩ .unit))))) (.add (-108) (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨6,1⟩ .unit))))) (.add (-12) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,1⟩ (.mult ⟨5,1⟩ (.mult ⟨6,1⟩ .unit))))) (.add (24) (.mult ⟨2,2⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨5,1⟩ (.mult ⟨6,1⟩ .unit))))) (.add (-24) (.mult ⟨0,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,1⟩ (.mult ⟨5,1⟩ .unit))))) (.add (12) (.mult ⟨1,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,1⟩ (.mult ⟨5,1⟩ (.mult ⟨6,1⟩ .unit))))) (.add (36) (.mult ⟨0,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,1⟩ .unit)))) (.add (36) (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨5,1⟩ .unit))))) (.add (12) (.mult ⟨2,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨5,1⟩ (.mult ⟨6,1⟩ .unit))))) (.num (0)))))))))))))))))))))))))))))))))))))
theorem dz2n398_norm : (reflectRing dz2n398E).toPoly=dz2n398P := by
  change (reflectRing dz2n339E).toPoly.combine (reflectRing dz2n397E).toPoly=dz2n398P
  rw [dz2n339_norm, dz2n397_norm]
  exact eq_of_beq (by decide : dz2n339P.combine dz2n397P == dz2n398P)

def dz2n399E : RingExpr := (.add dz2n338E dz2n398E)
def dz2n399P : Lean.Grind.CommRing.Poly := (.add (72) (.mult ⟨0,2⟩ (.mult ⟨1,1⟩ (.mult ⟨3,7⟩ (.mult ⟨4,3⟩ (.mult ⟨6,1⟩ .unit))))) (.add (72) (.mult ⟨0,2⟩ (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,6⟩ (.mult ⟨4,3⟩ .unit))))) (.add (-144) (.mult ⟨0,1⟩ (.mult ⟨1,2⟩ (.mult ⟨3,6⟩ (.mult ⟨4,3⟩ (.mult ⟨6,1⟩ .unit))))) (.add (-144) (.mult ⟨0,1⟩ (.mult ⟨1,2⟩ (.mult ⟨2,1⟩ (.mult ⟨3,5⟩ (.mult ⟨4,3⟩ .unit))))) (.add (72) (.mult ⟨1,3⟩ (.mult ⟨3,5⟩ (.mult ⟨4,3⟩ (.mult ⟨6,1⟩ .unit)))) (.add (-144) (.mult ⟨0,1⟩ (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,5⟩ (.mult ⟨4,3⟩ (.mult ⟨6,1⟩ .unit)))))) (.add (24) (.mult ⟨0,2⟩ (.mult ⟨3,6⟩ (.mult ⟨4,2⟩ (.mult ⟨5,1⟩ (.mult ⟨6,1⟩ .unit))))) (.add (72) (.mult ⟨1,3⟩ (.mult ⟨2,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,3⟩ .unit)))) (.add (-144) (.mult ⟨0,1⟩ (.mult ⟨1,1⟩ (.mult ⟨2,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,3⟩ .unit))))) (.add (24) (.mult ⟨0,2⟩ (.mult ⟨2,1⟩ (.mult ⟨3,5⟩ (.mult ⟨4,2⟩ (.mult ⟨5,1⟩ .unit))))) (.add (24) (.mult ⟨0,2⟩ (.mult ⟨3,6⟩ (.mult ⟨4,2⟩ (.mult ⟨6,1⟩ .unit)))) (.add (144) (.mult ⟨1,2⟩ (.mult ⟨2,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,3⟩ (.mult ⟨6,1⟩ .unit))))) (.add (-48) (.mult ⟨0,1⟩ (.mult ⟨1,1⟩ (.mult ⟨3,5⟩ (.mult ⟨4,2⟩ (.mult ⟨5,1⟩ (.mult ⟨6,1⟩ .unit)))))) (.add (144) (.mult ⟨1,2⟩ (.mult ⟨2,2⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ .unit)))) (.add (-48) (.mult ⟨0,1⟩ (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨5,1⟩ .unit)))))) (.add (12) (.mult ⟨0,1⟩ (.mult ⟨1,1⟩ (.mult ⟨3,5⟩ (.mult ⟨4,2⟩ (.mult ⟨6,1⟩ .unit))))) (.add (72) (.mult ⟨1,1⟩ (.mult ⟨2,2⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨6,1⟩ .unit))))) (.add (24) (.mult ⟨1,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨5,1⟩ (.mult ⟨6,1⟩ .unit))))) (.add (-48) (.mult ⟨0,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨5,1⟩ (.mult ⟨6,1⟩ .unit)))))) (.add (72) (.mult ⟨1,1⟩ (.mult ⟨2,3⟩ (.mult ⟨3,2⟩ (.mult ⟨4,3⟩ .unit)))) (.add (24) (.mult ⟨1,2⟩ (.mult ⟨2,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨5,1⟩ .unit))))) (.add (-48) (.mult ⟨0,1⟩ (.mult ⟨2,2⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨5,1⟩ .unit))))) (.add (48) (.mult ⟨0,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨6,1⟩ .unit))))) (.add (48) (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨5,1⟩ (.mult ⟨6,1⟩ .unit)))))) (.add (36) (.mult ⟨1,2⟩ (.mult ⟨2,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ .unit)))) (.add (72) (.mult ⟨0,1⟩ (.mult ⟨2,2⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ .unit)))) (.add (-12) (.mult ⟨0,1⟩ (.mult ⟨1,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,1⟩ (.mult ⟨5,1⟩ .unit))))) (.add (48) (.mult ⟨1,1⟩ (.mult ⟨2,2⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨5,1⟩ .unit))))) (.add (-108) (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨6,1⟩ .unit))))) (.add (-12) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,1⟩ (.mult ⟨5,1⟩ (.mult ⟨6,1⟩ .unit))))) (.add (24) (.mult ⟨2,2⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨5,1⟩ (.mult ⟨6,1⟩ .unit))))) (.add (-24) (.mult ⟨0,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,1⟩ (.mult ⟨5,1⟩ .unit))))) (.add (12) (.mult ⟨1,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,1⟩ (.mult ⟨5,1⟩ (.mult ⟨6,1⟩ .unit))))) (.add (36) (.mult ⟨0,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,1⟩ .unit)))) (.add (36) (.mult ⟨1,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨5,1⟩ .unit))))) (.add (12) (.mult ⟨2,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨5,1⟩ (.mult ⟨6,1⟩ .unit))))) (.num (0))))))))))))))))))))))))))))))))))))))
theorem dz2n399_norm : (reflectRing dz2n399E).toPoly=dz2n399P := by
  change (reflectRing dz2n338E).toPoly.combine (reflectRing dz2n398E).toPoly=dz2n399P
  rw [dz2n338_norm, dz2n398_norm]
  exact eq_of_beq (by decide : dz2n338P.combine dz2n398P == dz2n399P)

#check dz2n399_norm

end StackSorting.FiniteGraph
