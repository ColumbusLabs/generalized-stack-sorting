import UnitSplitFactorSharedNodes005
noncomputable section
namespace StackSorting.FiniteGraph.UnitSplitFactorCertificates
set_option maxRecDepth 65536
set_option maxHeartbeats 32000000
variable {R : Type} [Lean.Grind.CommRing R]

def usfn452E : RingExpr := (.mul (.var 15) (.var 1))
def usfn452P : Lean.Grind.CommRing.Poly := (.add (1) (.mult ⟨1,1⟩ (.mult ⟨15,1⟩ .unit)) (.num (0)))
theorem usfn452_norm : (reflectRing usfn452E).toPoly=usfn452P := by
  exact eq_of_beq (by decide : (reflectRing usfn452E).toPoly == usfn452P)

def usfn453E : RingExpr := (.mul (.var 4) (.mul (.var 9) (.mul (.pow (.var 7) 2) (.mul (.pow (.var 10) 2) (.mul (.pow (.var 3) 3) (.mul (.pow (.var 8) 4) (.add (.var 8) (.add (.mul (.int 4) (.pow (.var 4) 2)) (.add (.mul (.int (-4)) (.mul (.var 0) (.mul (.var 3) (.var 4)))) (.add (.mul (.int (-2)) (.mul (.var 10) (.mul (.var 8) (.mul (.var 4) (.var 9))))) (.add (.mul (.int 2) (.mul (.var 0) (.mul (.var 8) (.mul (.var 4) (.pow (.var 3) 2))))) (.add (.mul (.int (-8)) (.mul (.var 10) (.mul (.var 3) (.mul (.var 8) (.mul (.var 9) (.pow (.var 4) 3)))))) (.mul (.int 4) (.mul (.var 0) (.mul (.var 10) (.mul (.var 8) (.mul (.var 9) (.mul (.pow (.var 3) 2) (.pow (.var 4) 2)))))))))))))))))))
def usfn453P : Lean.Grind.CommRing.Poly := (.add (4) (.mult ⟨0,1⟩ (.mult ⟨3,5⟩ (.mult ⟨4,3⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (-8) (.mult ⟨3,4⟩ (.mult ⟨4,4⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ .unit)))))) (.add (2) (.mult ⟨0,1⟩ (.mult ⟨3,5⟩ (.mult ⟨4,2⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (-2) (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ .unit)))))) (.add (-4) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨7,2⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (4) (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨7,2⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (1) (.mult ⟨3,3⟩ (.mult ⟨4,1⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.num (0)))))))))
theorem usfn453_norm : (reflectRing usfn453E).toPoly=usfn453P := by
  exact eq_of_beq (by decide : (reflectRing usfn453E).toPoly == usfn453P)

def usfn454E : RingExpr := (.mul usfn408E usfn453E)
def usfn454P : Lean.Grind.CommRing.Poly := (.add (-8) (.mult ⟨0,1⟩ (.mult ⟨3,5⟩ (.mult ⟨4,3⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (16) (.mult ⟨3,4⟩ (.mult ⟨4,4⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ .unit)))))) (.add (-4) (.mult ⟨0,1⟩ (.mult ⟨3,5⟩ (.mult ⟨4,2⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (4) (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ .unit)))))) (.add (8) (.mult ⟨0,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨7,2⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (-8) (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨7,2⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (-2) (.mult ⟨3,3⟩ (.mult ⟨4,1⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.num (0)))))))))
theorem usfn454_norm : (reflectRing usfn454E).toPoly=usfn454P := by
  change (reflectRing usfn408E).toPoly.mul (reflectRing usfn453E).toPoly=usfn454P
  rw [usfn408_norm, usfn453_norm]
  exact eq_of_beq (by decide : usfn408P.mul usfn453P == usfn454P)

def usfn455E : RingExpr := (.mul usfn452E usfn454E)
def usfn455P : Lean.Grind.CommRing.Poly := (.add (-8) (.mult ⟨0,1⟩ (.mult ⟨1,1⟩ (.mult ⟨3,5⟩ (.mult ⟨4,3⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ (.mult ⟨15,1⟩ .unit))))))))) (.add (16) (.mult ⟨1,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,4⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ (.mult ⟨15,1⟩ .unit)))))))) (.add (-4) (.mult ⟨0,1⟩ (.mult ⟨1,1⟩ (.mult ⟨3,5⟩ (.mult ⟨4,2⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ (.mult ⟨15,1⟩ .unit))))))))) (.add (4) (.mult ⟨1,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ (.mult ⟨15,1⟩ .unit)))))))) (.add (8) (.mult ⟨0,1⟩ (.mult ⟨1,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨7,2⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ (.mult ⟨15,1⟩ .unit))))))))) (.add (-8) (.mult ⟨1,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨7,2⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ (.mult ⟨15,1⟩ .unit)))))))) (.add (-2) (.mult ⟨1,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,1⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ (.mult ⟨15,1⟩ .unit)))))))) (.num (0)))))))))
theorem usfn455_norm : (reflectRing usfn455E).toPoly=usfn455P := by
  change (reflectRing usfn452E).toPoly.mul (reflectRing usfn454E).toPoly=usfn455P
  rw [usfn452_norm, usfn454_norm]
  exact eq_of_beq (by decide : usfn452P.mul usfn454P == usfn455P)

def usfn456E : RingExpr := (.mul (.mul (.var 16) (.var 1)) (.mul (.int 8) (.mul (.var 0) (.mul (.var 9) (.mul (.pow (.var 7) 2) (.mul (.pow (.var 10) 2) (.mul (.pow (.var 3) 4) (.mul (.pow (.var 8) 4) (.mul (.pow (.var 4) 2) (.add (.int (-1)) (.mul (.int 2) (.mul (.var 10) (.mul (.var 3) (.mul (.var 8) (.mul (.var 4) (.var 9))))))))))))))))
def usfn456P : Lean.Grind.CommRing.Poly := (.add (16) (.mult ⟨0,1⟩ (.mult ⟨1,1⟩ (.mult ⟨3,5⟩ (.mult ⟨4,3⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ (.mult ⟨16,1⟩ .unit))))))))) (.add (-8) (.mult ⟨0,1⟩ (.mult ⟨1,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨7,2⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ (.mult ⟨16,1⟩ .unit))))))))) (.num (0))))
theorem usfn456_norm : (reflectRing usfn456E).toPoly=usfn456P := by
  exact eq_of_beq (by decide : (reflectRing usfn456E).toPoly == usfn456P)

def usfn457E : RingExpr := (.mul (.mul (.var 11) (.pow (.var 2) 5)) (.mul (.int (-8)) (.mul (.var 9) (.mul (.pow (.var 7) 2) (.mul (.pow (.var 10) 2) (.mul (.pow (.var 8) 5) (.mul (.pow (.var 4) 3) (.add (.int (-1)) (.mul (.int 2) (.mul (.var 10) (.mul (.var 4) (.var 9))))))))))))
def usfn457P : Lean.Grind.CommRing.Poly := (.add (-16) (.mult ⟨2,5⟩ (.mult ⟨4,4⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ (.mult ⟨11,1⟩ .unit))))))) (.add (8) (.mult ⟨2,5⟩ (.mult ⟨4,3⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ (.mult ⟨11,1⟩ .unit))))))) (.num (0))))
theorem usfn457_norm : (reflectRing usfn457E).toPoly=usfn457P := by
  exact eq_of_beq (by decide : (reflectRing usfn457E).toPoly == usfn457P)

def usfn458E : RingExpr := (.mul (.mul (.var 11) (.pow (.var 2) 4)) (.mul (.int 4) (.mul (.var 9) (.mul (.pow (.var 7) 2) (.mul (.pow (.var 10) 2) (.mul (.pow (.var 8) 4) (.mul (.pow (.var 4) 2) (.add (.mul (.int 3) (.var 8)) (.add (.mul (.int 2) (.mul (.var 0) (.mul (.var 3) (.var 4)))) (.add (.mul (.int (-6)) (.mul (.var 10) (.mul (.var 8) (.mul (.var 4) (.var 9))))) (.add (.mul (.int (-4)) (.mul (.var 0) (.mul (.var 8) (.mul (.var 4) (.pow (.var 3) 2))))) (.mul (.int 4) (.mul (.var 0) (.mul (.var 10) (.mul (.var 8) (.mul (.var 9) (.mul (.pow (.var 3) 2) (.pow (.var 4) 2))))))))))))))))))
def usfn458P : Lean.Grind.CommRing.Poly := (.add (16) (.mult ⟨0,1⟩ (.mult ⟨2,4⟩ (.mult ⟨3,2⟩ (.mult ⟨4,4⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ (.mult ⟨11,1⟩ .unit))))))))) (.add (-16) (.mult ⟨0,1⟩ (.mult ⟨2,4⟩ (.mult ⟨3,2⟩ (.mult ⟨4,3⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ (.mult ⟨11,1⟩ .unit))))))))) (.add (-24) (.mult ⟨2,4⟩ (.mult ⟨4,3⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ (.mult ⟨11,1⟩ .unit))))))) (.add (8) (.mult ⟨0,1⟩ (.mult ⟨2,4⟩ (.mult ⟨3,1⟩ (.mult ⟨4,3⟩ (.mult ⟨7,2⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ (.mult ⟨11,1⟩ .unit))))))))) (.add (12) (.mult ⟨2,4⟩ (.mult ⟨4,2⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ (.mult ⟨11,1⟩ .unit))))))) (.num (0)))))))
theorem usfn458_norm : (reflectRing usfn458E).toPoly=usfn458P := by
  exact eq_of_beq (by decide : (reflectRing usfn458E).toPoly == usfn458P)

def usfn459E : RingExpr := (.mul (.var 11) (.pow (.var 2) 3))
def usfn459P : Lean.Grind.CommRing.Poly := (.add (1) (.mult ⟨2,3⟩ (.mult ⟨11,1⟩ .unit)) (.num (0)))
theorem usfn459_norm : (reflectRing usfn459E).toPoly=usfn459P := by
  exact eq_of_beq (by decide : (reflectRing usfn459E).toPoly == usfn459P)

def usfn460E : RingExpr := (.mul (.int 3) (.mul (.var 7) (.mul (.var 10) (.pow (.var 8) 2))))
def usfn460P : Lean.Grind.CommRing.Poly := (.add (3) (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨10,1⟩ .unit))) (.num (0)))
theorem usfn460_norm : (reflectRing usfn460E).toPoly=usfn460P := by
  exact eq_of_beq (by decide : (reflectRing usfn460E).toPoly == usfn460P)

def usfn461E : RingExpr := (.mul (.int (-6)) (.mul (.var 7) (.mul (.var 4) (.mul (.var 9) (.mul (.pow (.var 10) 2) (.pow (.var 8) 2))))))
def usfn461P : Lean.Grind.CommRing.Poly := (.add (-6) (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))) (.num (0)))
theorem usfn461_norm : (reflectRing usfn461E).toPoly=usfn461P := by
  exact eq_of_beq (by decide : (reflectRing usfn461E).toPoly == usfn461P)

def usfn462E : RingExpr := (.mul (.int (-12)) (.mul (.var 0) (.mul (.var 7) (.mul (.var 10) (.mul (.var 4) (.mul (.pow (.var 3) 2) (.pow (.var 8) 2)))))))
def usfn462P : Lean.Grind.CommRing.Poly := (.add (-12) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨10,1⟩ .unit)))))) (.num (0)))
theorem usfn462_norm : (reflectRing usfn462E).toPoly=usfn462P := by
  exact eq_of_beq (by decide : (reflectRing usfn462E).toPoly == usfn462P)

def usfn463E : RingExpr := (.mul (.int (-4)) (.mul (.var 7) (.mul (.var 10) (.mul (.var 8) (.mul (.pow (.var 0) 2) (.mul (.pow (.var 3) 3) (.pow (.var 4) 2)))))))
def usfn463P : Lean.Grind.CommRing.Poly := (.add (-4) (.mult ⟨0,2⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.num (0)))
theorem usfn463_norm : (reflectRing usfn463E).toPoly=usfn463P := by
  exact eq_of_beq (by decide : (reflectRing usfn463E).toPoly == usfn463P)

def usfn464E : RingExpr := (.add (.mul (.int 4) (.mul (.var 0) (.mul (.var 7) (.mul (.var 10) (.mul (.var 3) (.mul (.var 8) (.var 4))))))) (.add (.mul (.int 4) (.mul (.var 7) (.mul (.var 10) (.mul (.pow (.var 0) 2) (.mul (.pow (.var 3) 4) (.mul (.pow (.var 8) 2) (.pow (.var 4) 2))))))) (.add (.mul (.int 16) (.mul (.var 7) (.mul (.var 3) (.mul (.var 9) (.mul (.pow (.var 10) 2) (.mul (.pow (.var 8) 2) (.pow (.var 4) 3))))))) (.mul (.int 8) (.mul (.var 0) (.mul (.var 7) (.mul (.var 9) (.mul (.pow (.var 10) 2) (.mul (.pow (.var 3) 2) (.mul (.pow (.var 8) 2) (.pow (.var 4) 2)))))))))))
def usfn464P : Lean.Grind.CommRing.Poly := (.add (4) (.mult ⟨0,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (8) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (16) (.mult ⟨3,1⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (4) (.mult ⟨0,1⟩ (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.num (0))))))
theorem usfn464_norm : (reflectRing usfn464E).toPoly=usfn464P := by
  exact eq_of_beq (by decide : (reflectRing usfn464E).toPoly == usfn464P)

def usfn465E : RingExpr := (.add usfn463E usfn464E)
def usfn465P : Lean.Grind.CommRing.Poly := (.add (4) (.mult ⟨0,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (8) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (-4) (.mult ⟨0,2⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (16) (.mult ⟨3,1⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (4) (.mult ⟨0,1⟩ (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.num (0)))))))
theorem usfn465_norm : (reflectRing usfn465E).toPoly=usfn465P := by
  change (reflectRing usfn463E).toPoly.combine (reflectRing usfn464E).toPoly=usfn465P
  rw [usfn463_norm, usfn464_norm]
  exact eq_of_beq (by decide : usfn463P.combine usfn464P == usfn465P)

def usfn466E : RingExpr := (.add usfn462E usfn465E)
def usfn466P : Lean.Grind.CommRing.Poly := (.add (4) (.mult ⟨0,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (8) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (-4) (.mult ⟨0,2⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (16) (.mult ⟨3,1⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (-12) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (4) (.mult ⟨0,1⟩ (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.num (0))))))))
theorem usfn466_norm : (reflectRing usfn466E).toPoly=usfn466P := by
  change (reflectRing usfn462E).toPoly.combine (reflectRing usfn465E).toPoly=usfn466P
  rw [usfn462_norm, usfn465_norm]
  exact eq_of_beq (by decide : usfn462P.combine usfn465P == usfn466P)

def usfn467E : RingExpr := (.add usfn461E usfn466E)
def usfn467P : Lean.Grind.CommRing.Poly := (.add (4) (.mult ⟨0,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (8) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (-4) (.mult ⟨0,2⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (16) (.mult ⟨3,1⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (-12) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (-6) (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))) (.add (4) (.mult ⟨0,1⟩ (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.num (0)))))))))
theorem usfn467_norm : (reflectRing usfn467E).toPoly=usfn467P := by
  change (reflectRing usfn461E).toPoly.combine (reflectRing usfn466E).toPoly=usfn467P
  rw [usfn461_norm, usfn466_norm]
  exact eq_of_beq (by decide : usfn461P.combine usfn466P == usfn467P)

def usfn468E : RingExpr := (.add usfn386E usfn467E)
def usfn468P : Lean.Grind.CommRing.Poly := (.add (4) (.mult ⟨0,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (8) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (-4) (.mult ⟨0,2⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (16) (.mult ⟨3,1⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (-12) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (-8) (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨10,1⟩ .unit))))) (.add (-6) (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))) (.add (4) (.mult ⟨0,1⟩ (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.num (0))))))))))
theorem usfn468_norm : (reflectRing usfn468E).toPoly=usfn468P := by
  change (reflectRing usfn386E).toPoly.combine (reflectRing usfn467E).toPoly=usfn468P
  rw [usfn386_norm, usfn467_norm]
  exact eq_of_beq (by decide : usfn386P.combine usfn467P == usfn468P)

def usfn469E : RingExpr := (.add usfn460E usfn468E)
def usfn469P : Lean.Grind.CommRing.Poly := (.add (4) (.mult ⟨0,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (8) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (-4) (.mult ⟨0,2⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (16) (.mult ⟨3,1⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (-12) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (-8) (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨10,1⟩ .unit))))) (.add (-6) (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))) (.add (4) (.mult ⟨0,1⟩ (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (3) (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨10,1⟩ .unit))) (.num (0)))))))))))
theorem usfn469_norm : (reflectRing usfn469E).toPoly=usfn469P := by
  change (reflectRing usfn460E).toPoly.combine (reflectRing usfn468E).toPoly=usfn469P
  rw [usfn460_norm, usfn468_norm]
  exact eq_of_beq (by decide : usfn460P.combine usfn468P == usfn469P)

def usfn470E : RingExpr := (.add usfn383E usfn469E)
def usfn470P : Lean.Grind.CommRing.Poly := (.add (4) (.mult ⟨0,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (8) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (-4) (.mult ⟨0,2⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (16) (.mult ⟨3,1⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (-12) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (-8) (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨10,1⟩ .unit))))) (.add (-6) (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))) (.add (4) (.mult ⟨0,1⟩ (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (3) (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨10,1⟩ .unit))) (.add (2) (.mult ⟨4,1⟩ .unit) (.num (0))))))))))))
theorem usfn470_norm : (reflectRing usfn470E).toPoly=usfn470P := by
  change (reflectRing usfn383E).toPoly.combine (reflectRing usfn469E).toPoly=usfn470P
  rw [usfn383_norm, usfn469_norm]
  exact eq_of_beq (by decide : usfn383P.combine usfn469P == usfn470P)

def usfn471E : RingExpr := (.mul usfn52E usfn470E)
def usfn471P : Lean.Grind.CommRing.Poly := (.add (4) (.mult ⟨0,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,5⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (8) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (-4) (.mult ⟨0,2⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (16) (.mult ⟨3,1⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (-12) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,5⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (-8) (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,5⟩ (.mult ⟨10,1⟩ .unit))))) (.add (-6) (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))) (.add (4) (.mult ⟨0,1⟩ (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (3) (.mult ⟨7,1⟩ (.mult ⟨8,5⟩ (.mult ⟨10,1⟩ .unit))) (.add (2) (.mult ⟨4,1⟩ (.mult ⟨8,3⟩ .unit)) (.num (0))))))))))))
theorem usfn471_norm : (reflectRing usfn471E).toPoly=usfn471P := by
  change (reflectRing usfn52E).toPoly.mul (reflectRing usfn470E).toPoly=usfn471P
  rw [usfn52_norm, usfn470_norm]
  exact eq_of_beq (by decide : usfn52P.mul usfn470P == usfn471P)

def usfn472E : RingExpr := (.mul usfn3E usfn471E)
def usfn472P : Lean.Grind.CommRing.Poly := (.add (4) (.mult ⟨0,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))))) (.add (8) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,5⟩ (.mult ⟨9,2⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (-4) (.mult ⟨0,2⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))))) (.add (16) (.mult ⟨3,1⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,5⟩ (.mult ⟨9,2⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (-12) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))))) (.add (-8) (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (-6) (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,5⟩ (.mult ⟨9,2⟩ (.mult ⟨10,2⟩ .unit))))) (.add (4) (.mult ⟨0,1⟩ (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))))) (.add (3) (.mult ⟨7,1⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))) (.add (2) (.mult ⟨4,1⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ .unit))) (.num (0))))))))))))
theorem usfn472_norm : (reflectRing usfn472E).toPoly=usfn472P := by
  change (reflectRing usfn3E).toPoly.mul (reflectRing usfn471E).toPoly=usfn472P
  rw [usfn3_norm, usfn471_norm]
  exact eq_of_beq (by decide : usfn3P.mul usfn471P == usfn472P)

def usfn473E : RingExpr := (.mul usfn362E usfn472E)
def usfn473P : Lean.Grind.CommRing.Poly := (.add (4) (.mult ⟨0,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))))) (.add (8) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,5⟩ (.mult ⟨9,2⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (-4) (.mult ⟨0,2⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))))) (.add (16) (.mult ⟨3,1⟩ (.mult ⟨4,4⟩ (.mult ⟨7,1⟩ (.mult ⟨8,5⟩ (.mult ⟨9,2⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (-12) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))))) (.add (-8) (.mult ⟨3,1⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (-6) (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,5⟩ (.mult ⟨9,2⟩ (.mult ⟨10,2⟩ .unit))))) (.add (4) (.mult ⟨0,1⟩ (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))))) (.add (3) (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))) (.add (2) (.mult ⟨4,2⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ .unit))) (.num (0))))))))))))
theorem usfn473_norm : (reflectRing usfn473E).toPoly=usfn473P := by
  change (reflectRing usfn362E).toPoly.mul (reflectRing usfn472E).toPoly=usfn473P
  rw [usfn362_norm, usfn472_norm]
  exact eq_of_beq (by decide : usfn362P.mul usfn472P == usfn473P)

def usfn474E : RingExpr := (.mul usfn2E usfn473E)
def usfn474P : Lean.Grind.CommRing.Poly := (.add (4) (.mult ⟨0,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (8) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,5⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (-4) (.mult ⟨0,2⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (16) (.mult ⟨3,1⟩ (.mult ⟨4,4⟩ (.mult ⟨7,1⟩ (.mult ⟨8,5⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ .unit)))))) (.add (-12) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (-8) (.mult ⟨3,1⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (-6) (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,5⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ .unit))))) (.add (4) (.mult ⟨0,1⟩ (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (3) (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))) (.add (2) (.mult ⟨4,2⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))) (.num (0))))))))))))
theorem usfn474_norm : (reflectRing usfn474E).toPoly=usfn474P := by
  change (reflectRing usfn2E).toPoly.mul (reflectRing usfn473E).toPoly=usfn474P
  rw [usfn2_norm, usfn473_norm]
  exact eq_of_beq (by decide : usfn2P.mul usfn473P == usfn474P)

def usfn475E : RingExpr := (.mul usfn1E usfn474E)
def usfn475P : Lean.Grind.CommRing.Poly := (.add (4) (.mult ⟨0,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,3⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (8) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,3⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (-4) (.mult ⟨0,2⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨7,2⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (16) (.mult ⟨3,1⟩ (.mult ⟨4,4⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ .unit)))))) (.add (-12) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (-8) (.mult ⟨3,1⟩ (.mult ⟨4,3⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (-6) (.mult ⟨4,2⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ .unit))))) (.add (4) (.mult ⟨0,1⟩ (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨7,2⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (3) (.mult ⟨4,1⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))) (.add (2) (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))) (.num (0))))))))))))
theorem usfn475_norm : (reflectRing usfn475E).toPoly=usfn475P := by
  change (reflectRing usfn1E).toPoly.mul (reflectRing usfn474E).toPoly=usfn475P
  rw [usfn1_norm, usfn474_norm]
  exact eq_of_beq (by decide : usfn1P.mul usfn474P == usfn475P)

def usfn476E : RingExpr := (.mul usfn361E usfn475E)
def usfn476P : Lean.Grind.CommRing.Poly := (.add (8) (.mult ⟨0,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,3⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (16) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,3⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (-8) (.mult ⟨0,2⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨7,2⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (32) (.mult ⟨3,1⟩ (.mult ⟨4,4⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ .unit)))))) (.add (-24) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (-16) (.mult ⟨3,1⟩ (.mult ⟨4,3⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (-12) (.mult ⟨4,2⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ .unit))))) (.add (8) (.mult ⟨0,1⟩ (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨7,2⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (6) (.mult ⟨4,1⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))) (.add (4) (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))) (.num (0))))))))))))
theorem usfn476_norm : (reflectRing usfn476E).toPoly=usfn476P := by
  change (reflectRing usfn361E).toPoly.mul (reflectRing usfn475E).toPoly=usfn476P
  rw [usfn361_norm, usfn475_norm]
  exact eq_of_beq (by decide : usfn361P.mul usfn475P == usfn476P)

def usfn477E : RingExpr := (.mul usfn459E usfn476E)
def usfn477P : Lean.Grind.CommRing.Poly := (.add (8) (.mult ⟨0,2⟩ (.mult ⟨2,3⟩ (.mult ⟨3,4⟩ (.mult ⟨4,3⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ (.mult ⟨11,1⟩ .unit))))))))) (.add (16) (.mult ⟨0,1⟩ (.mult ⟨2,3⟩ (.mult ⟨3,2⟩ (.mult ⟨4,3⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ (.mult ⟨11,1⟩ .unit))))))))) (.add (-8) (.mult ⟨0,2⟩ (.mult ⟨2,3⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨7,2⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ (.mult ⟨11,1⟩ .unit))))))))) (.add (32) (.mult ⟨2,3⟩ (.mult ⟨3,1⟩ (.mult ⟨4,4⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ (.mult ⟨11,1⟩ .unit)))))))) (.add (-24) (.mult ⟨0,1⟩ (.mult ⟨2,3⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ (.mult ⟨11,1⟩ .unit))))))))) (.add (-16) (.mult ⟨2,3⟩ (.mult ⟨3,1⟩ (.mult ⟨4,3⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ (.mult ⟨11,1⟩ .unit)))))))) (.add (-12) (.mult ⟨2,3⟩ (.mult ⟨4,2⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ (.mult ⟨11,1⟩ .unit))))))) (.add (8) (.mult ⟨0,1⟩ (.mult ⟨2,3⟩ (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨7,2⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ (.mult ⟨11,1⟩ .unit))))))))) (.add (6) (.mult ⟨2,3⟩ (.mult ⟨4,1⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ (.mult ⟨11,1⟩ .unit))))))) (.add (4) (.mult ⟨2,3⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ (.mult ⟨11,1⟩ .unit))))))) (.num (0))))))))))))
theorem usfn477_norm : (reflectRing usfn477E).toPoly=usfn477P := by
  change (reflectRing usfn459E).toPoly.mul (reflectRing usfn476E).toPoly=usfn477P
  rw [usfn459_norm, usfn476_norm]
  exact eq_of_beq (by decide : usfn459P.mul usfn476P == usfn477P)

def usfn478E : RingExpr := (.mul (.mul (.var 12) (.pow (.var 2) 3)) (.mul (.int 16) (.mul (.var 0) (.mul (.var 9) (.mul (.pow (.var 7) 2) (.mul (.pow (.var 10) 2) (.mul (.pow (.var 3) 3) (.mul (.pow (.var 8) 5) (.mul (.pow (.var 4) 3) (.add (.int (-1)) (.mul (.int 2) (.mul (.var 10) (.mul (.var 4) (.var 9))))))))))))))
def usfn478P : Lean.Grind.CommRing.Poly := (.add (32) (.mult ⟨0,1⟩ (.mult ⟨2,3⟩ (.mult ⟨3,3⟩ (.mult ⟨4,4⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ (.mult ⟨12,1⟩ .unit))))))))) (.add (-16) (.mult ⟨0,1⟩ (.mult ⟨2,3⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ (.mult ⟨12,1⟩ .unit))))))))) (.num (0))))
theorem usfn478_norm : (reflectRing usfn478E).toPoly=usfn478P := by
  exact eq_of_beq (by decide : (reflectRing usfn478E).toPoly == usfn478P)

def usfn479E : RingExpr := (.mul (.mul (.var 15) (.pow (.var 2) 3)) (.mul (.int 8) (.mul (.var 9) (.mul (.pow (.var 7) 2) (.mul (.pow (.var 10) 2) (.mul (.pow (.var 3) 2) (.mul (.pow (.var 8) 5) (.mul (.pow (.var 4) 3) (.add (.int (-1)) (.mul (.int 2) (.mul (.var 10) (.mul (.var 4) (.var 9)))))))))))))
def usfn479P : Lean.Grind.CommRing.Poly := (.add (16) (.mult ⟨2,3⟩ (.mult ⟨3,2⟩ (.mult ⟨4,4⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ (.mult ⟨15,1⟩ .unit)))))))) (.add (-8) (.mult ⟨2,3⟩ (.mult ⟨3,2⟩ (.mult ⟨4,3⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ (.mult ⟨15,1⟩ .unit)))))))) (.num (0))))
theorem usfn479_norm : (reflectRing usfn479E).toPoly=usfn479P := by
  exact eq_of_beq (by decide : (reflectRing usfn479E).toPoly == usfn479P)

def usfn480E : RingExpr := (.mul (.int 4) (.var 4))
def usfn480P : Lean.Grind.CommRing.Poly := (.add (4) (.mult ⟨4,1⟩ .unit) (.num (0)))
theorem usfn480_norm : (reflectRing usfn480E).toPoly=usfn480P := by
  exact eq_of_beq (by decide : (reflectRing usfn480E).toPoly == usfn480P)

def usfn481E : RingExpr := (.mul (.int (-4)) (.mul (.var 0) (.mul (.pow (.var 3) 2) (.pow (.var 4) 2))))
def usfn481P : Lean.Grind.CommRing.Poly := (.add (-4) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ .unit))) (.num (0)))
theorem usfn481_norm : (reflectRing usfn481E).toPoly=usfn481P := by
  exact eq_of_beq (by decide : (reflectRing usfn481E).toPoly == usfn481P)

def usfn482E : RingExpr := (.mul (.int (-16)) (.mul (.var 7) (.mul (.var 10) (.mul (.var 3) (.mul (.pow (.var 8) 2) (.pow (.var 4) 2))))))
def usfn482P : Lean.Grind.CommRing.Poly := (.add (-16) (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨10,1⟩ .unit))))) (.num (0)))
theorem usfn482_norm : (reflectRing usfn482E).toPoly=usfn482P := by
  exact eq_of_beq (by decide : (reflectRing usfn482E).toPoly == usfn482P)

def usfn483E : RingExpr := (.mul (.int (-16)) (.mul (.var 0) (.mul (.var 7) (.mul (.var 10) (.mul (.var 8) (.mul (.pow (.var 3) 2) (.pow (.var 4) 3)))))))
def usfn483P : Lean.Grind.CommRing.Poly := (.add (-16) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.num (0)))
theorem usfn483_norm : (reflectRing usfn483E).toPoly=usfn483P := by
  exact eq_of_beq (by decide : (reflectRing usfn483E).toPoly == usfn483P)

def usfn484E : RingExpr := (.mul (.int 2) (.mul (.var 0) (.mul (.var 7) (.mul (.var 10) (.mul (.var 3) (.mul (.var 8) (.var 4)))))))
def usfn484P : Lean.Grind.CommRing.Poly := (.add (2) (.mult ⟨0,1⟩ (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.num (0)))
theorem usfn484_norm : (reflectRing usfn484E).toPoly=usfn484P := by
  exact eq_of_beq (by decide : (reflectRing usfn484E).toPoly == usfn484P)

def usfn485E : RingExpr := (.mul (.int 8) (.mul (.var 0) (.mul (.var 7) (.mul (.var 10) (.mul (.pow (.var 3) 3) (.mul (.pow (.var 8) 2) (.pow (.var 4) 3)))))))
def usfn485P : Lean.Grind.CommRing.Poly := (.add (8) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨10,1⟩ .unit)))))) (.num (0)))
theorem usfn485_norm : (reflectRing usfn485E).toPoly=usfn485P := by
  exact eq_of_beq (by decide : (reflectRing usfn485E).toPoly == usfn485P)

def usfn486E : RingExpr := (.add (.mul (.int 12) (.mul (.var 7) (.mul (.var 10) (.mul (.pow (.var 0) 2) (.mul (.pow (.var 3) 4) (.mul (.pow (.var 8) 2) (.pow (.var 4) 2))))))) (.add (.mul (.int 32) (.mul (.var 7) (.mul (.var 3) (.mul (.var 9) (.mul (.pow (.var 10) 2) (.mul (.pow (.var 8) 2) (.pow (.var 4) 3))))))) (.add (.mul (.int 4) (.mul (.var 0) (.mul (.var 7) (.mul (.var 9) (.mul (.pow (.var 10) 2) (.mul (.pow (.var 3) 2) (.mul (.pow (.var 8) 2) (.pow (.var 4) 2)))))))) (.mul (.int 16) (.mul (.var 0) (.mul (.var 7) (.mul (.var 9) (.mul (.pow (.var 10) 2) (.mul (.pow (.var 3) 3) (.mul (.pow (.var 8) 2) (.pow (.var 4) 4)))))))))))
def usfn486P : Lean.Grind.CommRing.Poly := (.add (16) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,4⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (12) (.mult ⟨0,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (4) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (32) (.mult ⟨3,1⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.num (0))))))
theorem usfn486_norm : (reflectRing usfn486E).toPoly=usfn486P := by
  exact eq_of_beq (by decide : (reflectRing usfn486E).toPoly == usfn486P)

def usfn487E : RingExpr := (.add usfn485E usfn486E)
def usfn487P : Lean.Grind.CommRing.Poly := (.add (16) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,4⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (12) (.mult ⟨0,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (8) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (4) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (32) (.mult ⟨3,1⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.num (0)))))))
theorem usfn487_norm : (reflectRing usfn487E).toPoly=usfn487P := by
  change (reflectRing usfn485E).toPoly.combine (reflectRing usfn486E).toPoly=usfn487P
  rw [usfn485_norm, usfn486_norm]
  exact eq_of_beq (by decide : usfn485P.combine usfn486P == usfn487P)

def usfn488E : RingExpr := (.add usfn484E usfn487E)
def usfn488P : Lean.Grind.CommRing.Poly := (.add (16) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,4⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (12) (.mult ⟨0,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (8) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (4) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (32) (.mult ⟨3,1⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (2) (.mult ⟨0,1⟩ (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.num (0))))))))
theorem usfn488_norm : (reflectRing usfn488E).toPoly=usfn488P := by
  change (reflectRing usfn484E).toPoly.combine (reflectRing usfn487E).toPoly=usfn488P
  rw [usfn484_norm, usfn487_norm]
  exact eq_of_beq (by decide : usfn484P.combine usfn487P == usfn488P)

def usfn489E : RingExpr := (.add usfn463E usfn488E)
def usfn489P : Lean.Grind.CommRing.Poly := (.add (16) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,4⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (12) (.mult ⟨0,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (8) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (4) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (-4) (.mult ⟨0,2⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (32) (.mult ⟨3,1⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (2) (.mult ⟨0,1⟩ (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.num (0)))))))))
theorem usfn489_norm : (reflectRing usfn489E).toPoly=usfn489P := by
  change (reflectRing usfn463E).toPoly.combine (reflectRing usfn488E).toPoly=usfn489P
  rw [usfn463_norm, usfn488_norm]
  exact eq_of_beq (by decide : usfn463P.combine usfn488P == usfn489P)

def usfn490E : RingExpr := (.add usfn462E usfn489E)
def usfn490P : Lean.Grind.CommRing.Poly := (.add (16) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,4⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (12) (.mult ⟨0,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (8) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (4) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (-4) (.mult ⟨0,2⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (32) (.mult ⟨3,1⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (-12) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (2) (.mult ⟨0,1⟩ (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.num (0))))))))))
theorem usfn490_norm : (reflectRing usfn490E).toPoly=usfn490P := by
  change (reflectRing usfn462E).toPoly.combine (reflectRing usfn489E).toPoly=usfn490P
  rw [usfn462_norm, usfn489_norm]
  exact eq_of_beq (by decide : usfn462P.combine usfn489P == usfn490P)

def usfn491E : RingExpr := (.add usfn483E usfn490E)
def usfn491P : Lean.Grind.CommRing.Poly := (.add (16) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,4⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (12) (.mult ⟨0,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (8) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (4) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (-4) (.mult ⟨0,2⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (32) (.mult ⟨3,1⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (-16) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (-12) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (2) (.mult ⟨0,1⟩ (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.num (0)))))))))))
theorem usfn491_norm : (reflectRing usfn491E).toPoly=usfn491P := by
  change (reflectRing usfn483E).toPoly.combine (reflectRing usfn490E).toPoly=usfn491P
  rw [usfn483_norm, usfn490_norm]
  exact eq_of_beq (by decide : usfn483P.combine usfn490P == usfn491P)

def usfn492E : RingExpr := (.add usfn387E usfn491E)
def usfn492P : Lean.Grind.CommRing.Poly := (.add (16) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,4⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (12) (.mult ⟨0,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (8) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (4) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (-4) (.mult ⟨0,2⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (32) (.mult ⟨3,1⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (-16) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (-12) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (-2) (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))) (.add (2) (.mult ⟨0,1⟩ (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.num (0))))))))))))
theorem usfn492_norm : (reflectRing usfn492E).toPoly=usfn492P := by
  change (reflectRing usfn387E).toPoly.combine (reflectRing usfn491E).toPoly=usfn492P
  rw [usfn387_norm, usfn491_norm]
  exact eq_of_beq (by decide : usfn387P.combine usfn491P == usfn492P)

def usfn493E : RingExpr := (.add usfn482E usfn492E)
def usfn493P : Lean.Grind.CommRing.Poly := (.add (16) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,4⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (12) (.mult ⟨0,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (8) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (4) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (-4) (.mult ⟨0,2⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (32) (.mult ⟨3,1⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (-16) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (-12) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (-16) (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨10,1⟩ .unit))))) (.add (-2) (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))) (.add (2) (.mult ⟨0,1⟩ (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.num (0)))))))))))))
theorem usfn493_norm : (reflectRing usfn493E).toPoly=usfn493P := by
  change (reflectRing usfn482E).toPoly.combine (reflectRing usfn492E).toPoly=usfn493P
  rw [usfn482_norm, usfn492_norm]
  exact eq_of_beq (by decide : usfn482P.combine usfn492P == usfn493P)

def usfn494E : RingExpr := (.add usfn481E usfn493E)
def usfn494P : Lean.Grind.CommRing.Poly := (.add (16) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,4⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (12) (.mult ⟨0,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (8) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (4) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (-4) (.mult ⟨0,2⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (32) (.mult ⟨3,1⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (-16) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (-12) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (-16) (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨10,1⟩ .unit))))) (.add (-2) (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))) (.add (2) (.mult ⟨0,1⟩ (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (-4) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ .unit))) (.num (0))))))))))))))
theorem usfn494_norm : (reflectRing usfn494E).toPoly=usfn494P := by
  change (reflectRing usfn481E).toPoly.combine (reflectRing usfn493E).toPoly=usfn494P
  rw [usfn481_norm, usfn493_norm]
  exact eq_of_beq (by decide : usfn481P.combine usfn493P == usfn494P)

def usfn495E : RingExpr := (.add usfn384E usfn494E)
def usfn495P : Lean.Grind.CommRing.Poly := (.add (16) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,4⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (12) (.mult ⟨0,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (8) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (4) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (-4) (.mult ⟨0,2⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (32) (.mult ⟨3,1⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (-16) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (-12) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (-16) (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨10,1⟩ .unit))))) (.add (-2) (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))) (.add (2) (.mult ⟨0,1⟩ (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (-4) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ .unit))) (.add (1) (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨10,1⟩ .unit))) (.num (0)))))))))))))))
theorem usfn495_norm : (reflectRing usfn495E).toPoly=usfn495P := by
  change (reflectRing usfn384E).toPoly.combine (reflectRing usfn494E).toPoly=usfn495P
  rw [usfn384_norm, usfn494_norm]
  exact eq_of_beq (by decide : usfn384P.combine usfn494P == usfn495P)

def usfn496E : RingExpr := (.add usfn480E usfn495E)
def usfn496P : Lean.Grind.CommRing.Poly := (.add (16) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,4⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (12) (.mult ⟨0,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (8) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (4) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (-4) (.mult ⟨0,2⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (32) (.mult ⟨3,1⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (-16) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (-12) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (-16) (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨10,1⟩ .unit))))) (.add (-2) (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))) (.add (2) (.mult ⟨0,1⟩ (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (-4) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ .unit))) (.add (1) (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨10,1⟩ .unit))) (.add (4) (.mult ⟨4,1⟩ .unit) (.num (0))))))))))))))))
theorem usfn496_norm : (reflectRing usfn496E).toPoly=usfn496P := by
  change (reflectRing usfn480E).toPoly.combine (reflectRing usfn495E).toPoly=usfn496P
  rw [usfn480_norm, usfn495_norm]
  exact eq_of_beq (by decide : usfn480P.combine usfn495P == usfn496P)

def usfn497E : RingExpr := (.mul usfn52E usfn496E)
def usfn497P : Lean.Grind.CommRing.Poly := (.add (16) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,4⟩ (.mult ⟨7,1⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (12) (.mult ⟨0,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,5⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (8) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,5⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (4) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (-4) (.mult ⟨0,2⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (32) (.mult ⟨3,1⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (-16) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (-12) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,5⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (-16) (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,5⟩ (.mult ⟨10,1⟩ .unit))))) (.add (-2) (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))) (.add (2) (.mult ⟨0,1⟩ (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (-4) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨8,3⟩ .unit)))) (.add (1) (.mult ⟨7,1⟩ (.mult ⟨8,5⟩ (.mult ⟨10,1⟩ .unit))) (.add (4) (.mult ⟨4,1⟩ (.mult ⟨8,3⟩ .unit)) (.num (0))))))))))))))))
theorem usfn497_norm : (reflectRing usfn497E).toPoly=usfn497P := by
  change (reflectRing usfn52E).toPoly.mul (reflectRing usfn496E).toPoly=usfn497P
  rw [usfn52_norm, usfn496_norm]
  exact eq_of_beq (by decide : usfn52P.mul usfn496P == usfn497P)

def usfn498E : RingExpr := (.mul usfn3E usfn497E)
def usfn498P : Lean.Grind.CommRing.Poly := (.add (16) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,4⟩ (.mult ⟨7,1⟩ (.mult ⟨8,5⟩ (.mult ⟨9,2⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (12) (.mult ⟨0,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))))) (.add (8) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))))) (.add (4) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,5⟩ (.mult ⟨9,2⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (-4) (.mult ⟨0,2⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))))) (.add (32) (.mult ⟨3,1⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,5⟩ (.mult ⟨9,2⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (-16) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))))) (.add (-12) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))))) (.add (-16) (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (-2) (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,5⟩ (.mult ⟨9,2⟩ (.mult ⟨10,2⟩ .unit))))) (.add (2) (.mult ⟨0,1⟩ (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))))) (.add (-4) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ .unit))))) (.add (1) (.mult ⟨7,1⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))) (.add (4) (.mult ⟨4,1⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ .unit))) (.num (0))))))))))))))))
theorem usfn498_norm : (reflectRing usfn498E).toPoly=usfn498P := by
  change (reflectRing usfn3E).toPoly.mul (reflectRing usfn497E).toPoly=usfn498P
  rw [usfn3_norm, usfn497_norm]
  exact eq_of_beq (by decide : usfn3P.mul usfn497P == usfn498P)

def usfn499E : RingExpr := (.mul usfn2E usfn498E)
def usfn499P : Lean.Grind.CommRing.Poly := (.add (16) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,4⟩ (.mult ⟨7,1⟩ (.mult ⟨8,5⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (12) (.mult ⟨0,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (8) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (4) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,5⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (-4) (.mult ⟨0,2⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (32) (.mult ⟨3,1⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,5⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ .unit)))))) (.add (-16) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (-12) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (-16) (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (-2) (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,5⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ .unit))))) (.add (2) (.mult ⟨0,1⟩ (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (-4) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (1) (.mult ⟨7,1⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))) (.add (4) (.mult ⟨4,1⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))) (.num (0))))))))))))))))
theorem usfn499_norm : (reflectRing usfn499E).toPoly=usfn499P := by
  change (reflectRing usfn2E).toPoly.mul (reflectRing usfn498E).toPoly=usfn499P
  rw [usfn2_norm, usfn498_norm]
  exact eq_of_beq (by decide : usfn2P.mul usfn498P == usfn499P)

def usfn500E : RingExpr := (.mul usfn1E usfn499E)
def usfn500P : Lean.Grind.CommRing.Poly := (.add (16) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,4⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (12) (.mult ⟨0,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (8) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (4) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (-4) (.mult ⟨0,2⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨7,2⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (32) (.mult ⟨3,1⟩ (.mult ⟨4,3⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ .unit)))))) (.add (-16) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,3⟩ (.mult ⟨7,2⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (-12) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (-16) (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (-2) (.mult ⟨4,1⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ .unit))))) (.add (2) (.mult ⟨0,1⟩ (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨7,2⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (-4) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))))) (.add (1) (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))) (.add (4) (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))) (.num (0))))))))))))))))
theorem usfn500_norm : (reflectRing usfn500E).toPoly=usfn500P := by
  change (reflectRing usfn1E).toPoly.mul (reflectRing usfn499E).toPoly=usfn500P
  rw [usfn1_norm, usfn499_norm]
  exact eq_of_beq (by decide : usfn1P.mul usfn499P == usfn500P)

def usfn501E : RingExpr := (.mul usfn134E usfn500E)
def usfn501P : Lean.Grind.CommRing.Poly := (.add (16) (.mult ⟨0,1⟩ (.mult ⟨2,2⟩ (.mult ⟨3,3⟩ (.mult ⟨4,4⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ (.mult ⟨11,1⟩ .unit))))))))) (.add (12) (.mult ⟨0,2⟩ (.mult ⟨2,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,2⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ (.mult ⟨11,1⟩ .unit))))))))) (.add (8) (.mult ⟨0,1⟩ (.mult ⟨2,2⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ (.mult ⟨11,1⟩ .unit))))))))) (.add (4) (.mult ⟨0,1⟩ (.mult ⟨2,2⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ (.mult ⟨11,1⟩ .unit))))))))) (.add (-4) (.mult ⟨0,2⟩ (.mult ⟨2,2⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨7,2⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ (.mult ⟨11,1⟩ .unit))))))))) (.add (32) (.mult ⟨2,2⟩ (.mult ⟨3,1⟩ (.mult ⟨4,3⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ (.mult ⟨11,1⟩ .unit)))))))) (.add (-16) (.mult ⟨0,1⟩ (.mult ⟨2,2⟩ (.mult ⟨3,2⟩ (.mult ⟨4,3⟩ (.mult ⟨7,2⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ (.mult ⟨11,1⟩ .unit))))))))) (.add (-12) (.mult ⟨0,1⟩ (.mult ⟨2,2⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ (.mult ⟨11,1⟩ .unit))))))))) (.add (-16) (.mult ⟨2,2⟩ (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ (.mult ⟨11,1⟩ .unit)))))))) (.add (-2) (.mult ⟨2,2⟩ (.mult ⟨4,1⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ (.mult ⟨11,1⟩ .unit))))))) (.add (2) (.mult ⟨0,1⟩ (.mult ⟨2,2⟩ (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨7,2⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ (.mult ⟨11,1⟩ .unit))))))))) (.add (-4) (.mult ⟨0,1⟩ (.mult ⟨2,2⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ (.mult ⟨11,1⟩ .unit))))))))) (.add (1) (.mult ⟨2,2⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ (.mult ⟨11,1⟩ .unit)))))) (.add (4) (.mult ⟨2,2⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ (.mult ⟨11,1⟩ .unit))))))) (.num (0))))))))))))))))
theorem usfn501_norm : (reflectRing usfn501E).toPoly=usfn501P := by
  change (reflectRing usfn134E).toPoly.mul (reflectRing usfn500E).toPoly=usfn501P
  rw [usfn134_norm, usfn500_norm]
  exact eq_of_beq (by decide : usfn134P.mul usfn500P == usfn501P)

def usfn502E : RingExpr := (.mul (.mul (.var 12) (.pow (.var 2) 2)) (.mul (.int 8) (.mul (.var 0) (.mul (.var 9) (.mul (.pow (.var 7) 2) (.mul (.pow (.var 10) 2) (.mul (.pow (.var 3) 3) (.mul (.pow (.var 8) 4) (.mul (.pow (.var 4) 2) (.add (.mul (.int (-1)) (.var 8)) (.add (.mul (.int (-2)) (.mul (.var 0) (.mul (.var 3) (.var 4)))) (.add (.mul (.int 2) (.mul (.var 0) (.mul (.var 8) (.mul (.var 4) (.pow (.var 3) 2))))) (.mul (.int 2) (.mul (.var 10) (.mul (.var 8) (.mul (.var 4) (.var 9)))))))))))))))))
def usfn502P : Lean.Grind.CommRing.Poly := (.add (16) (.mult ⟨0,2⟩ (.mult ⟨2,2⟩ (.mult ⟨3,5⟩ (.mult ⟨4,3⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ (.mult ⟨12,1⟩ .unit))))))))) (.add (16) (.mult ⟨0,1⟩ (.mult ⟨2,2⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ (.mult ⟨12,1⟩ .unit))))))))) (.add (-16) (.mult ⟨0,2⟩ (.mult ⟨2,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,3⟩ (.mult ⟨7,2⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ (.mult ⟨12,1⟩ .unit))))))))) (.add (-8) (.mult ⟨0,1⟩ (.mult ⟨2,2⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ (.mult ⟨12,1⟩ .unit))))))))) (.num (0))))))
theorem usfn502_norm : (reflectRing usfn502E).toPoly=usfn502P := by
  exact eq_of_beq (by decide : (reflectRing usfn502E).toPoly == usfn502P)

def usfn503E : RingExpr := (.mul (.mul (.var 14) (.pow (.var 2) 2)) (.mul (.int 8) (.mul (.var 0) (.mul (.var 9) (.mul (.pow (.var 7) 2) (.mul (.pow (.var 10) 2) (.mul (.pow (.var 3) 3) (.mul (.pow (.var 8) 5) (.mul (.pow (.var 4) 2) (.add (.int (-1)) (.mul (.int 2) (.mul (.var 10) (.mul (.var 4) (.var 9))))))))))))))
def usfn503P : Lean.Grind.CommRing.Poly := (.add (16) (.mult ⟨0,1⟩ (.mult ⟨2,2⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ (.mult ⟨14,1⟩ .unit))))))))) (.add (-8) (.mult ⟨0,1⟩ (.mult ⟨2,2⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ (.mult ⟨14,1⟩ .unit))))))))) (.num (0))))
theorem usfn503_norm : (reflectRing usfn503E).toPoly=usfn503P := by
  exact eq_of_beq (by decide : (reflectRing usfn503E).toPoly == usfn503P)

def usfn504E : RingExpr := (.mul (.mul (.var 15) (.pow (.var 2) 2)) (.mul (.int 8) (.mul (.var 9) (.mul (.pow (.var 7) 2) (.mul (.pow (.var 10) 2) (.mul (.pow (.var 3) 2) (.mul (.pow (.var 8) 4) (.mul (.pow (.var 4) 2) (.add (.mul (.int (-1)) (.var 8)) (.add (.mul (.int (-1)) (.mul (.var 0) (.mul (.var 3) (.var 4)))) (.add (.mul (.int 2) (.mul (.var 10) (.mul (.var 8) (.mul (.var 4) (.var 9))))) (.mul (.int 2) (.mul (.var 0) (.mul (.var 10) (.mul (.var 8) (.mul (.var 9) (.mul (.pow (.var 3) 2) (.pow (.var 4) 2))))))))))))))))))
def usfn504P : Lean.Grind.CommRing.Poly := (.add (16) (.mult ⟨0,1⟩ (.mult ⟨2,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,4⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ (.mult ⟨15,1⟩ .unit))))))))) (.add (16) (.mult ⟨2,2⟩ (.mult ⟨3,2⟩ (.mult ⟨4,3⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ (.mult ⟨15,1⟩ .unit)))))))) (.add (-8) (.mult ⟨0,1⟩ (.mult ⟨2,2⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨7,2⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ (.mult ⟨15,1⟩ .unit))))))))) (.add (-8) (.mult ⟨2,2⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ (.mult ⟨15,1⟩ .unit)))))))) (.num (0))))))
theorem usfn504_norm : (reflectRing usfn504E).toPoly=usfn504P := by
  exact eq_of_beq (by decide : (reflectRing usfn504E).toPoly == usfn504P)

def usfn505E : RingExpr := (.mul (.int 4) (.mul (.var 3) (.pow (.var 4) 2)))
def usfn505P : Lean.Grind.CommRing.Poly := (.add (4) (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ .unit)) (.num (0)))
theorem usfn505_norm : (reflectRing usfn505E).toPoly=usfn505P := by
  exact eq_of_beq (by decide : (reflectRing usfn505E).toPoly == usfn505P)

def usfn506E : RingExpr := (.mul (.int 2) (.mul (.var 0) (.mul (.var 4) (.pow (.var 3) 2))))
def usfn506P : Lean.Grind.CommRing.Poly := (.add (2) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ .unit))) (.num (0)))
theorem usfn506_norm : (reflectRing usfn506E).toPoly=usfn506P := by
  exact eq_of_beq (by decide : (reflectRing usfn506E).toPoly == usfn506P)

def usfn507E : RingExpr := (.mul (.int (-8)) (.mul (.var 7) (.mul (.var 10) (.mul (.pow (.var 3) 2) (.mul (.pow (.var 8) 2) (.pow (.var 4) 3))))))
def usfn507P : Lean.Grind.CommRing.Poly := (.add (-8) (.mult ⟨3,2⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨10,1⟩ .unit))))) (.num (0)))
theorem usfn507_norm : (reflectRing usfn507E).toPoly=usfn507P := by
  exact eq_of_beq (by decide : (reflectRing usfn507E).toPoly == usfn507P)

def usfn508E : RingExpr := (.mul (.int 2) (.mul (.var 0) (.mul (.var 7) (.mul (.var 10) (.mul (.pow (.var 3) 2) (.pow (.var 8) 2))))))
def usfn508P : Lean.Grind.CommRing.Poly := (.add (2) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨10,1⟩ .unit))))) (.num (0)))
theorem usfn508_norm : (reflectRing usfn508E).toPoly=usfn508P := by
  exact eq_of_beq (by decide : (reflectRing usfn508E).toPoly == usfn508P)

def usfn509E : RingExpr := (.mul (.int 4) (.mul (.var 7) (.mul (.var 10) (.mul (.var 3) (.mul (.var 4) (.pow (.var 8) 2))))))
def usfn509P : Lean.Grind.CommRing.Poly := (.add (4) (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨10,1⟩ .unit))))) (.num (0)))
theorem usfn509_norm : (reflectRing usfn509E).toPoly=usfn509P := by
  exact eq_of_beq (by decide : (reflectRing usfn509E).toPoly == usfn509P)

def usfn510E : RingExpr := (.mul (.int (-12)) (.mul (.var 0) (.mul (.var 7) (.mul (.var 10) (.mul (.pow (.var 3) 3) (.mul (.pow (.var 8) 2) (.pow (.var 4) 2)))))))
def usfn510P : Lean.Grind.CommRing.Poly := (.add (-12) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨10,1⟩ .unit)))))) (.num (0)))
theorem usfn510_norm : (reflectRing usfn510E).toPoly=usfn510P := by
  exact eq_of_beq (by decide : (reflectRing usfn510E).toPoly == usfn510P)

def usfn511E : RingExpr := (.mul (.int (-8)) (.mul (.var 7) (.mul (.var 10) (.mul (.pow (.var 0) 2) (.mul (.pow (.var 3) 5) (.mul (.pow (.var 8) 2) (.pow (.var 4) 3)))))))
def usfn511P : Lean.Grind.CommRing.Poly := (.add (-8) (.mult ⟨0,2⟩ (.mult ⟨3,5⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨10,1⟩ .unit)))))) (.num (0)))
theorem usfn511_norm : (reflectRing usfn511E).toPoly=usfn511P := by
  exact eq_of_beq (by decide : (reflectRing usfn511E).toPoly == usfn511P)

def usfn512E : RingExpr := (.mul (.int (-8)) (.mul (.var 7) (.mul (.var 3) (.mul (.var 9) (.mul (.pow (.var 10) 2) (.mul (.pow (.var 8) 2) (.pow (.var 4) 2)))))))
def usfn512P : Lean.Grind.CommRing.Poly := (.add (-8) (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.num (0)))
theorem usfn512_norm : (reflectRing usfn512E).toPoly=usfn512P := by
  exact eq_of_beq (by decide : (reflectRing usfn512E).toPoly == usfn512P)

def usfn513E : RingExpr := (.mul (.int (-4)) (.mul (.var 7) (.mul (.var 10) (.mul (.var 4) (.mul (.pow (.var 0) 2) (.mul (.pow (.var 3) 4) (.pow (.var 8) 2)))))))
def usfn513P : Lean.Grind.CommRing.Poly := (.add (-4) (.mult ⟨0,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨10,1⟩ .unit)))))) (.num (0)))
theorem usfn513_norm : (reflectRing usfn513E).toPoly=usfn513P := by
  exact eq_of_beq (by decide : (reflectRing usfn513E).toPoly == usfn513P)

def usfn514E : RingExpr := (.add (.mul (.int 8) (.mul (.var 0) (.mul (.var 7) (.mul (.var 10) (.mul (.var 8) (.mul (.pow (.var 3) 2) (.pow (.var 4) 2))))))) (.add (.mul (.int 16) (.mul (.var 7) (.mul (.var 9) (.mul (.pow (.var 10) 2) (.mul (.pow (.var 3) 2) (.mul (.pow (.var 8) 2) (.pow (.var 4) 4))))))) (.add (.mul (.int (-8)) (.mul (.var 0) (.mul (.var 7) (.mul (.var 9) (.mul (.pow (.var 10) 2) (.mul (.pow (.var 3) 3) (.mul (.pow (.var 8) 2) (.pow (.var 4) 3)))))))) (.mul (.int 16) (.mul (.var 7) (.mul (.var 9) (.mul (.pow (.var 0) 2) (.mul (.pow (.var 10) 2) (.mul (.pow (.var 3) 5) (.mul (.pow (.var 8) 2) (.pow (.var 4) 4)))))))))))
def usfn514P : Lean.Grind.CommRing.Poly := (.add (16) (.mult ⟨0,2⟩ (.mult ⟨3,5⟩ (.mult ⟨4,4⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (-8) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (16) (.mult ⟨3,2⟩ (.mult ⟨4,4⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (8) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.num (0))))))
theorem usfn514_norm : (reflectRing usfn514E).toPoly=usfn514P := by
  exact eq_of_beq (by decide : (reflectRing usfn514E).toPoly == usfn514P)

def usfn515E : RingExpr := (.add usfn513E usfn514E)
def usfn515P : Lean.Grind.CommRing.Poly := (.add (16) (.mult ⟨0,2⟩ (.mult ⟨3,5⟩ (.mult ⟨4,4⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (-8) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (16) (.mult ⟨3,2⟩ (.mult ⟨4,4⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (-4) (.mult ⟨0,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (8) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.num (0)))))))
theorem usfn515_norm : (reflectRing usfn515E).toPoly=usfn515P := by
  change (reflectRing usfn513E).toPoly.combine (reflectRing usfn514E).toPoly=usfn515P
  rw [usfn513_norm, usfn514_norm]
  exact eq_of_beq (by decide : usfn513P.combine usfn514P == usfn515P)

def usfn516E : RingExpr := (.add usfn512E usfn515E)
def usfn516P : Lean.Grind.CommRing.Poly := (.add (16) (.mult ⟨0,2⟩ (.mult ⟨3,5⟩ (.mult ⟨4,4⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (-8) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (16) (.mult ⟨3,2⟩ (.mult ⟨4,4⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (-4) (.mult ⟨0,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (-8) (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (8) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.num (0))))))))
theorem usfn516_norm : (reflectRing usfn516E).toPoly=usfn516P := by
  change (reflectRing usfn512E).toPoly.combine (reflectRing usfn515E).toPoly=usfn516P
  rw [usfn512_norm, usfn515_norm]
  exact eq_of_beq (by decide : usfn512P.combine usfn515P == usfn516P)

def usfn517E : RingExpr := (.add usfn511E usfn516E)
def usfn517P : Lean.Grind.CommRing.Poly := (.add (16) (.mult ⟨0,2⟩ (.mult ⟨3,5⟩ (.mult ⟨4,4⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (-8) (.mult ⟨0,2⟩ (.mult ⟨3,5⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (-8) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (16) (.mult ⟨3,2⟩ (.mult ⟨4,4⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (-4) (.mult ⟨0,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (-8) (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (8) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.num (0)))))))))
theorem usfn517_norm : (reflectRing usfn517E).toPoly=usfn517P := by
  change (reflectRing usfn511E).toPoly.combine (reflectRing usfn516E).toPoly=usfn517P
  rw [usfn511_norm, usfn516_norm]
  exact eq_of_beq (by decide : usfn511P.combine usfn516P == usfn517P)

def usfn518E : RingExpr := (.add usfn510E usfn517E)
def usfn518P : Lean.Grind.CommRing.Poly := (.add (16) (.mult ⟨0,2⟩ (.mult ⟨3,5⟩ (.mult ⟨4,4⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (-8) (.mult ⟨0,2⟩ (.mult ⟨3,5⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (-8) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (16) (.mult ⟨3,2⟩ (.mult ⟨4,4⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (-4) (.mult ⟨0,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (-12) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (-8) (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (8) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.num (0))))))))))
theorem usfn518_norm : (reflectRing usfn518E).toPoly=usfn518P := by
  change (reflectRing usfn510E).toPoly.combine (reflectRing usfn517E).toPoly=usfn518P
  rw [usfn510_norm, usfn517_norm]
  exact eq_of_beq (by decide : usfn510P.combine usfn517P == usfn518P)

def usfn519E : RingExpr := (.add usfn509E usfn518E)
def usfn519P : Lean.Grind.CommRing.Poly := (.add (16) (.mult ⟨0,2⟩ (.mult ⟨3,5⟩ (.mult ⟨4,4⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (-8) (.mult ⟨0,2⟩ (.mult ⟨3,5⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (-8) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (16) (.mult ⟨3,2⟩ (.mult ⟨4,4⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (-4) (.mult ⟨0,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (-12) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (-8) (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (8) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (4) (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨10,1⟩ .unit))))) (.num (0)))))))))))
theorem usfn519_norm : (reflectRing usfn519E).toPoly=usfn519P := by
  change (reflectRing usfn509E).toPoly.combine (reflectRing usfn518E).toPoly=usfn519P
  rw [usfn509_norm, usfn518_norm]
  exact eq_of_beq (by decide : usfn509P.combine usfn518P == usfn519P)

def usfn520E : RingExpr := (.add usfn508E usfn519E)
def usfn520P : Lean.Grind.CommRing.Poly := (.add (16) (.mult ⟨0,2⟩ (.mult ⟨3,5⟩ (.mult ⟨4,4⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (-8) (.mult ⟨0,2⟩ (.mult ⟨3,5⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (-8) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (16) (.mult ⟨3,2⟩ (.mult ⟨4,4⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (-4) (.mult ⟨0,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (-12) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (-8) (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (8) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (2) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨10,1⟩ .unit))))) (.add (4) (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨10,1⟩ .unit))))) (.num (0))))))))))))
theorem usfn520_norm : (reflectRing usfn520E).toPoly=usfn520P := by
  change (reflectRing usfn508E).toPoly.combine (reflectRing usfn519E).toPoly=usfn520P
  rw [usfn508_norm, usfn519_norm]
  exact eq_of_beq (by decide : usfn508P.combine usfn519P == usfn520P)

def usfn521E : RingExpr := (.add usfn507E usfn520E)
def usfn521P : Lean.Grind.CommRing.Poly := (.add (16) (.mult ⟨0,2⟩ (.mult ⟨3,5⟩ (.mult ⟨4,4⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (-8) (.mult ⟨0,2⟩ (.mult ⟨3,5⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (-8) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (16) (.mult ⟨3,2⟩ (.mult ⟨4,4⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (-4) (.mult ⟨0,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (-12) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (-8) (.mult ⟨3,2⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨10,1⟩ .unit))))) (.add (-8) (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (8) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (2) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨10,1⟩ .unit))))) (.add (4) (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨10,1⟩ .unit))))) (.num (0)))))))))))))
theorem usfn521_norm : (reflectRing usfn521E).toPoly=usfn521P := by
  change (reflectRing usfn507E).toPoly.combine (reflectRing usfn520E).toPoly=usfn521P
  rw [usfn507_norm, usfn520_norm]
  exact eq_of_beq (by decide : usfn507P.combine usfn520P == usfn521P)

def usfn522E : RingExpr := (.add usfn506E usfn521E)
def usfn522P : Lean.Grind.CommRing.Poly := (.add (16) (.mult ⟨0,2⟩ (.mult ⟨3,5⟩ (.mult ⟨4,4⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (-8) (.mult ⟨0,2⟩ (.mult ⟨3,5⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (-8) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (16) (.mult ⟨3,2⟩ (.mult ⟨4,4⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (-4) (.mult ⟨0,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (-12) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (-8) (.mult ⟨3,2⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨10,1⟩ .unit))))) (.add (-8) (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (8) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (2) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨10,1⟩ .unit))))) (.add (4) (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨10,1⟩ .unit))))) (.add (2) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ .unit))) (.num (0))))))))))))))
theorem usfn522_norm : (reflectRing usfn522E).toPoly=usfn522P := by
  change (reflectRing usfn506E).toPoly.combine (reflectRing usfn521E).toPoly=usfn522P
  rw [usfn506_norm, usfn521_norm]
  exact eq_of_beq (by decide : usfn506P.combine usfn521P == usfn522P)

def usfn523E : RingExpr := (.add usfn505E usfn522E)
def usfn523P : Lean.Grind.CommRing.Poly := (.add (16) (.mult ⟨0,2⟩ (.mult ⟨3,5⟩ (.mult ⟨4,4⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (-8) (.mult ⟨0,2⟩ (.mult ⟨3,5⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (-8) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (16) (.mult ⟨3,2⟩ (.mult ⟨4,4⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (-4) (.mult ⟨0,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (-12) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (-8) (.mult ⟨3,2⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨10,1⟩ .unit))))) (.add (-8) (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (8) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (2) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨10,1⟩ .unit))))) (.add (4) (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨10,1⟩ .unit))))) (.add (2) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ .unit))) (.add (4) (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ .unit)) (.num (0)))))))))))))))
theorem usfn523_norm : (reflectRing usfn523E).toPoly=usfn523P := by
  change (reflectRing usfn505E).toPoly.combine (reflectRing usfn522E).toPoly=usfn523P
  rw [usfn505_norm, usfn522_norm]
  exact eq_of_beq (by decide : usfn505P.combine usfn522P == usfn523P)

def usfn524E : RingExpr := (.add usfn100E usfn523E)
def usfn524P : Lean.Grind.CommRing.Poly := (.add (16) (.mult ⟨0,2⟩ (.mult ⟨3,5⟩ (.mult ⟨4,4⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (-8) (.mult ⟨0,2⟩ (.mult ⟨3,5⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (-8) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (16) (.mult ⟨3,2⟩ (.mult ⟨4,4⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (-4) (.mult ⟨0,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (-12) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (-8) (.mult ⟨3,2⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨10,1⟩ .unit))))) (.add (-8) (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (8) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (2) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨10,1⟩ .unit))))) (.add (4) (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,2⟩ (.mult ⟨10,1⟩ .unit))))) (.add (2) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ .unit))) (.add (4) (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ .unit)) (.num (-1)))))))))))))))
theorem usfn524_norm : (reflectRing usfn524E).toPoly=usfn524P := by
  change (reflectRing usfn100E).toPoly.combine (reflectRing usfn523E).toPoly=usfn524P
  rw [usfn100_norm, usfn523_norm]
  exact eq_of_beq (by decide : usfn100P.combine usfn523P == usfn524P)

def usfn525E : RingExpr := (.mul usfn52E usfn524E)
def usfn525P : Lean.Grind.CommRing.Poly := (.add (16) (.mult ⟨0,2⟩ (.mult ⟨3,5⟩ (.mult ⟨4,4⟩ (.mult ⟨7,1⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (-8) (.mult ⟨0,2⟩ (.mult ⟨3,5⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,5⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (-8) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (16) (.mult ⟨3,2⟩ (.mult ⟨4,4⟩ (.mult ⟨7,1⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (-4) (.mult ⟨0,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,5⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (-12) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,5⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (-8) (.mult ⟨3,2⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,5⟩ (.mult ⟨10,1⟩ .unit))))) (.add (-8) (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (8) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (2) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,5⟩ (.mult ⟨10,1⟩ .unit))))) (.add (4) (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,5⟩ (.mult ⟨10,1⟩ .unit))))) (.add (2) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨8,3⟩ .unit)))) (.add (4) (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨8,3⟩ .unit))) (.add (-1) (.mult ⟨8,3⟩ .unit) (.num (0))))))))))))))))
theorem usfn525_norm : (reflectRing usfn525E).toPoly=usfn525P := by
  change (reflectRing usfn52E).toPoly.mul (reflectRing usfn524E).toPoly=usfn525P
  rw [usfn52_norm, usfn524_norm]
  exact eq_of_beq (by decide : usfn52P.mul usfn524P == usfn525P)

def usfn526E : RingExpr := (.mul usfn3E usfn525E)
def usfn526P : Lean.Grind.CommRing.Poly := (.add (16) (.mult ⟨0,2⟩ (.mult ⟨3,5⟩ (.mult ⟨4,4⟩ (.mult ⟨7,1⟩ (.mult ⟨8,5⟩ (.mult ⟨9,2⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (-8) (.mult ⟨0,2⟩ (.mult ⟨3,5⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))))) (.add (-8) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,5⟩ (.mult ⟨9,2⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (16) (.mult ⟨3,2⟩ (.mult ⟨4,4⟩ (.mult ⟨7,1⟩ (.mult ⟨8,5⟩ (.mult ⟨9,2⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (-4) (.mult ⟨0,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))))) (.add (-12) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))))) (.add (-8) (.mult ⟨3,2⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (-8) (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,5⟩ (.mult ⟨9,2⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (8) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))))) (.add (2) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (4) (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (2) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ .unit))))) (.add (4) (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ .unit)))) (.add (-1) (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ .unit)) (.num (0))))))))))))))))
theorem usfn526_norm : (reflectRing usfn526E).toPoly=usfn526P := by
  change (reflectRing usfn3E).toPoly.mul (reflectRing usfn525E).toPoly=usfn526P
  rw [usfn3_norm, usfn525_norm]
  exact eq_of_beq (by decide : usfn3P.mul usfn525P == usfn526P)

def usfn527E : RingExpr := (.mul usfn2E usfn526E)
def usfn527P : Lean.Grind.CommRing.Poly := (.add (16) (.mult ⟨0,2⟩ (.mult ⟨3,5⟩ (.mult ⟨4,4⟩ (.mult ⟨7,1⟩ (.mult ⟨8,5⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (-8) (.mult ⟨0,2⟩ (.mult ⟨3,5⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (-8) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,5⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (16) (.mult ⟨3,2⟩ (.mult ⟨4,4⟩ (.mult ⟨7,1⟩ (.mult ⟨8,5⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ .unit)))))) (.add (-4) (.mult ⟨0,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (-12) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (-8) (.mult ⟨3,2⟩ (.mult ⟨4,3⟩ (.mult ⟨7,1⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (-8) (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,5⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ .unit)))))) (.add (8) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (2) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (4) (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (2) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (4) (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))) (.add (-1) (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))) (.num (0))))))))))))))))
theorem usfn527_norm : (reflectRing usfn527E).toPoly=usfn527P := by
  change (reflectRing usfn2E).toPoly.mul (reflectRing usfn526E).toPoly=usfn527P
  rw [usfn2_norm, usfn526_norm]
  exact eq_of_beq (by decide : usfn2P.mul usfn526P == usfn527P)

def usfn528E : RingExpr := (.mul usfn1E usfn527E)
def usfn528P : Lean.Grind.CommRing.Poly := (.add (16) (.mult ⟨0,2⟩ (.mult ⟨3,5⟩ (.mult ⟨4,4⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (-8) (.mult ⟨0,2⟩ (.mult ⟨3,5⟩ (.mult ⟨4,3⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (-8) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (16) (.mult ⟨3,2⟩ (.mult ⟨4,4⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ .unit)))))) (.add (-4) (.mult ⟨0,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,1⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (-12) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (-8) (.mult ⟨3,2⟩ (.mult ⟨4,3⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (-8) (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ .unit)))))) (.add (8) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨7,2⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (2) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (4) (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (2) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))))) (.add (4) (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (-1) (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))) (.num (0))))))))))))))))
theorem usfn528_norm : (reflectRing usfn528E).toPoly=usfn528P := by
  change (reflectRing usfn1E).toPoly.mul (reflectRing usfn527E).toPoly=usfn528P
  rw [usfn1_norm, usfn527_norm]
  exact eq_of_beq (by decide : usfn1P.mul usfn527P == usfn528P)

def usfn529E : RingExpr := (.mul usfn100E usfn528E)
def usfn529P : Lean.Grind.CommRing.Poly := (.add (-16) (.mult ⟨0,2⟩ (.mult ⟨3,5⟩ (.mult ⟨4,4⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (8) (.mult ⟨0,2⟩ (.mult ⟨3,5⟩ (.mult ⟨4,3⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (8) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ .unit))))))) (.add (-16) (.mult ⟨3,2⟩ (.mult ⟨4,4⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ .unit)))))) (.add (4) (.mult ⟨0,2⟩ (.mult ⟨3,4⟩ (.mult ⟨4,1⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (12) (.mult ⟨0,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (8) (.mult ⟨3,2⟩ (.mult ⟨4,3⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (8) (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ .unit)))))) (.add (-8) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨7,2⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit))))))) (.add (-2) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (-4) (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ .unit)))))) (.add (-2) (.mult ⟨0,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit))))))) (.add (-4) (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))))) (.add (1) (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ .unit)))) (.num (0))))))))))))))))
theorem usfn529_norm : (reflectRing usfn529E).toPoly=usfn529P := by
  change (reflectRing usfn100E).toPoly.mul (reflectRing usfn528E).toPoly=usfn529P
  rw [usfn100_norm, usfn528_norm]
  exact eq_of_beq (by decide : usfn100P.mul usfn528P == usfn529P)

def usfn530E : RingExpr := (.mul usfn5E usfn529E)
def usfn530P : Lean.Grind.CommRing.Poly := (.add (-16) (.mult ⟨0,2⟩ (.mult ⟨2,1⟩ (.mult ⟨3,5⟩ (.mult ⟨4,4⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ (.mult ⟨11,1⟩ .unit))))))))) (.add (8) (.mult ⟨0,2⟩ (.mult ⟨2,1⟩ (.mult ⟨3,5⟩ (.mult ⟨4,3⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ (.mult ⟨11,1⟩ .unit))))))))) (.add (8) (.mult ⟨0,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,3⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ (.mult ⟨11,1⟩ .unit))))))))) (.add (-16) (.mult ⟨2,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,4⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ (.mult ⟨11,1⟩ .unit)))))))) (.add (4) (.mult ⟨0,2⟩ (.mult ⟨2,1⟩ (.mult ⟨3,4⟩ (.mult ⟨4,1⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ (.mult ⟨11,1⟩ .unit))))))))) (.add (12) (.mult ⟨0,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,3⟩ (.mult ⟨4,2⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ (.mult ⟨11,1⟩ .unit))))))))) (.add (8) (.mult ⟨2,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,3⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ (.mult ⟨11,1⟩ .unit)))))))) (.add (8) (.mult ⟨2,1⟩ (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,2⟩ (.mult ⟨10,3⟩ (.mult ⟨11,1⟩ .unit)))))))) (.add (-8) (.mult ⟨0,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,2⟩ (.mult ⟨7,2⟩ (.mult ⟨8,4⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ (.mult ⟨11,1⟩ .unit))))))))) (.add (-2) (.mult ⟨0,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,2⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ (.mult ⟨11,1⟩ .unit)))))))) (.add (-4) (.mult ⟨2,1⟩ (.mult ⟨3,1⟩ (.mult ⟨4,1⟩ (.mult ⟨7,2⟩ (.mult ⟨8,5⟩ (.mult ⟨9,1⟩ (.mult ⟨10,2⟩ (.mult ⟨11,1⟩ .unit)))))))) (.add (-2) (.mult ⟨0,1⟩ (.mult ⟨2,1⟩ (.mult ⟨3,2⟩ (.mult ⟨4,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ (.mult ⟨11,1⟩ .unit))))))))) (.add (-4) (.mult ⟨2,1⟩ (.mult ⟨3,1⟩ (.mult ⟨4,2⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ (.mult ⟨11,1⟩ .unit)))))))) (.add (1) (.mult ⟨2,1⟩ (.mult ⟨7,1⟩ (.mult ⟨8,3⟩ (.mult ⟨9,1⟩ (.mult ⟨10,1⟩ (.mult ⟨11,1⟩ .unit)))))) (.num (0))))))))))))))))
theorem usfn530_norm : (reflectRing usfn530E).toPoly=usfn530P := by
  change (reflectRing usfn5E).toPoly.mul (reflectRing usfn529E).toPoly=usfn530P
  rw [usfn5_norm, usfn529_norm]
  exact eq_of_beq (by decide : usfn5P.mul usfn529P == usfn530P)

def usfn531E : RingExpr := (.mul (.var 12) (.var 2))
def usfn531P : Lean.Grind.CommRing.Poly := (.add (1) (.mult ⟨2,1⟩ (.mult ⟨12,1⟩ .unit)) (.num (0)))
theorem usfn531_norm : (reflectRing usfn531E).toPoly=usfn531P := by
  exact eq_of_beq (by decide : (reflectRing usfn531E).toPoly == usfn531P)

#print axioms usfn531_norm
end StackSorting.FiniteGraph.UnitSplitFactorCertificates
