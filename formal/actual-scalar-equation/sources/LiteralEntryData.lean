import GraphLiterals
namespace StackSorting.FiniteGraph
set_option maxRecDepth 32768

def dataA_0_1 : RingExpr := (.int 1)
theorem dataA_0_1_binding : litAExpr 0 1=dataA_0_1 := rfl

def dataA_1_2 : RingExpr := (.int 1)
theorem dataA_1_2_binding : litAExpr 1 2=dataA_1_2 := rfl

def dataA_2_0 : RingExpr := (.mul (.var 10) (.mul (.var 8) (.add (.int (-3)) (.add (.mul (.int 2) (.var 5)) (.add (.mul (.int 6) (.mul (.var 2) (.var 4))) (.add (.mul (.int (-6)) (.mul (.var 0) (.mul (.var 4) (.pow (.var 3) 2)))) (.mul (.int 6) (.mul (.var 1) (.mul (.var 3) (.var 4))))))))))
theorem dataA_2_0_binding : litAExpr 2 0=dataA_2_0 := rfl

def dataA_2_1 : RingExpr := (.mul (.var 10) (.mul (.var 8) (.add (.mul (.int (-6)) (.var 2)) (.add (.mul (.int (-3)) (.mul (.var 1) (.var 3))) (.mul (.int 2) (.mul (.var 5) (.var 2)))))))
theorem dataA_2_1_binding : litAExpr 2 1=dataA_2_1 := rfl

def dataA_2_2 : RingExpr := (.var 5)
theorem dataA_2_2_binding : litAExpr 2 2=dataA_2_2 := rfl

def dataA_3_0 : RingExpr := (.mul (.var 10) (.mul (.var 8) (.add (.int (-1)) (.add (.mul (.int (-2)) (.mul (.var 2) (.var 4))) (.mul (.int (-2)) (.mul (.var 0) (.mul (.var 4) (.pow (.var 3) 2))))))))
theorem dataA_3_0_binding : litAExpr 3 0=dataA_3_0 := rfl

def dataA_3_1 : RingExpr := (.mul (.var 10) (.mul (.var 8) (.add (.mul (.int (-2)) (.var 2)) (.add (.mul (.int (-1)) (.mul (.var 1) (.var 3))) (.add (.mul (.int (-4)) (.mul (.var 4) (.pow (.var 2) 2))) (.mul (.int (-2)) (.mul (.var 1) (.mul (.var 2) (.mul (.var 3) (.var 4))))))))))
theorem dataA_3_1_binding : litAExpr 3 1=dataA_3_1 := rfl

def dataA_3_2 : RingExpr := (.add (.mul (.int (-2)) (.mul (.var 2) (.var 4))) (.mul (.int (-1)) (.mul (.var 1) (.mul (.var 3) (.var 4)))))
theorem dataA_3_2_binding : litAExpr 3 2=dataA_3_2 := rfl

def dataA_4_0 : RingExpr := (.var 0)
theorem dataA_4_0_binding : litAExpr 4 0=dataA_4_0 := rfl

def dataA_4_1 : RingExpr := (.mul (.var 10) (.mul (.var 9) (.mul (.pow (.var 8) 2) (.add (.var 2) (.add (.mul (.var 1) (.var 3)) (.add (.mul (.int (-2)) (.mul (.var 3) (.var 4))) (.add (.mul (.int 2) (.mul (.var 4) (.pow (.var 2) 2))) (.mul (.int 2) (.mul (.var 1) (.mul (.var 2) (.mul (.var 3) (.var 4))))))))))))
theorem dataA_4_1_binding : litAExpr 4 1=dataA_4_1 := rfl

def dataA_4_2 : RingExpr := (.var 1)
theorem dataA_4_2_binding : litAExpr 4 2=dataA_4_2 := rfl

def dataA_5_0 : RingExpr := (.mul (.var 10) (.mul (.pow (.var 8) 2) (.add (.var 2) (.add (.mul (.int (-2)) (.mul (.var 3) (.var 4))) (.add (.mul (.int 2) (.mul (.var 0) (.pow (.var 3) 2))) (.add (.mul (.int 2) (.mul (.var 4) (.pow (.var 2) 2))) (.mul (.int 2) (.mul (.var 0) (.mul (.var 2) (.mul (.var 4) (.pow (.var 3) 2)))))))))))
theorem dataA_5_0_binding : litAExpr 5 0=dataA_5_0 := rfl

def dataA_5_1 : RingExpr := (.mul (.var 10) (.mul (.var 9) (.mul (.pow (.var 8) 2) (.add (.var 2) (.add (.mul (.var 1) (.var 3)) (.add (.mul (.int (-1)) (.mul (.var 3) (.var 4))) (.add (.mul (.int 4) (.mul (.var 4) (.pow (.var 2) 2))) (.add (.mul (.int 4) (.mul (.pow (.var 2) 3) (.pow (.var 4) 2))) (.add (.mul (.int (-2)) (.mul (.var 2) (.mul (.var 3) (.pow (.var 4) 2)))) (.add (.mul (.int 2) (.mul (.var 1) (.mul (.var 3) (.mul (.pow (.var 2) 2) (.pow (.var 4) 2))))) (.mul (.int 3) (.mul (.var 1) (.mul (.var 2) (.mul (.var 3) (.var 4)))))))))))))))
theorem dataA_5_1_binding : litAExpr 5 1=dataA_5_1 := rfl

def dataA_5_2 : RingExpr := (.mul (.var 8) (.add (.var 2) (.add (.mul (.var 1) (.var 3)) (.add (.mul (.int (-1)) (.mul (.var 3) (.var 4))) (.add (.mul (.int 2) (.mul (.var 4) (.pow (.var 2) 2))) (.mul (.var 1) (.mul (.var 2) (.mul (.var 3) (.var 4)))))))))
theorem dataA_5_2_binding : litAExpr 5 2=dataA_5_2 := rfl

def dataB_0_1 : RingExpr := (.int 1)
theorem dataB_0_1_binding : litBExpr 0 1=dataB_0_1 := rfl

def dataB_1_4 : RingExpr := (.int 1)
theorem dataB_1_4_binding : litBExpr 1 4=dataB_1_4 := rfl

def dataB_2_0 : RingExpr := (.mul (.var 10) (.mul (.var 8) (.add (.int (-3)) (.add (.mul (.int 2) (.var 5)) (.add (.mul (.int 6) (.mul (.var 2) (.var 4))) (.add (.mul (.int (-6)) (.mul (.var 0) (.mul (.var 4) (.pow (.var 3) 2)))) (.mul (.int 6) (.mul (.var 1) (.mul (.var 3) (.var 4))))))))))
theorem dataB_2_0_binding : litBExpr 2 0=dataB_2_0 := rfl

def dataB_2_1 : RingExpr := (.mul (.var 10) (.mul (.var 8) (.add (.mul (.int (-6)) (.var 2)) (.add (.mul (.int (-3)) (.mul (.var 1) (.var 3))) (.mul (.int 2) (.mul (.var 5) (.var 2)))))))
theorem dataB_2_1_binding : litBExpr 2 1=dataB_2_1 := rfl

def dataB_2_4 : RingExpr := (.var 5)
theorem dataB_2_4_binding : litBExpr 2 4=dataB_2_4 := rfl

def dataB_3_0 : RingExpr := (.mul (.var 10) (.mul (.var 8) (.add (.int (-1)) (.add (.mul (.int (-2)) (.mul (.var 2) (.var 4))) (.mul (.int (-2)) (.mul (.var 0) (.mul (.var 4) (.pow (.var 3) 2))))))))
theorem dataB_3_0_binding : litBExpr 3 0=dataB_3_0 := rfl

def dataB_3_1 : RingExpr := (.mul (.var 10) (.mul (.var 8) (.add (.mul (.int (-2)) (.var 2)) (.add (.mul (.int (-1)) (.mul (.var 1) (.var 3))) (.add (.mul (.int (-4)) (.mul (.var 4) (.pow (.var 2) 2))) (.mul (.int (-2)) (.mul (.var 1) (.mul (.var 2) (.mul (.var 3) (.var 4))))))))))
theorem dataB_3_1_binding : litBExpr 3 1=dataB_3_1 := rfl

def dataB_3_4 : RingExpr := (.add (.mul (.int (-2)) (.mul (.var 2) (.var 4))) (.mul (.int (-1)) (.mul (.var 1) (.mul (.var 3) (.var 4)))))
theorem dataB_3_4_binding : litBExpr 3 4=dataB_3_4 := rfl

def dataB_4_0 : RingExpr := (.var 0)
theorem dataB_4_0_binding : litBExpr 4 0=dataB_4_0 := rfl

def dataB_4_1 : RingExpr := (.mul (.var 10) (.mul (.var 9) (.mul (.pow (.var 8) 2) (.add (.var 2) (.add (.mul (.var 1) (.var 3)) (.add (.mul (.int (-2)) (.mul (.var 3) (.var 4))) (.add (.mul (.int 2) (.mul (.var 4) (.pow (.var 2) 2))) (.mul (.int 2) (.mul (.var 1) (.mul (.var 2) (.mul (.var 3) (.var 4))))))))))))
theorem dataB_4_1_binding : litBExpr 4 1=dataB_4_1 := rfl

def dataB_4_4 : RingExpr := (.var 1)
theorem dataB_4_4_binding : litBExpr 4 4=dataB_4_4 := rfl

def dataB_5_0 : RingExpr := (.mul (.var 10) (.mul (.pow (.var 8) 2) (.add (.var 2) (.add (.mul (.int (-2)) (.mul (.var 3) (.var 4))) (.add (.mul (.int 2) (.mul (.var 0) (.pow (.var 3) 2))) (.add (.mul (.int 2) (.mul (.var 4) (.pow (.var 2) 2))) (.mul (.int 2) (.mul (.var 0) (.mul (.var 2) (.mul (.var 4) (.pow (.var 3) 2)))))))))))
theorem dataB_5_0_binding : litBExpr 5 0=dataB_5_0 := rfl

def dataB_5_1 : RingExpr := (.mul (.var 10) (.mul (.var 9) (.mul (.pow (.var 8) 2) (.add (.var 2) (.add (.mul (.var 1) (.var 3)) (.add (.mul (.int (-1)) (.mul (.var 3) (.var 4))) (.add (.mul (.int 4) (.mul (.var 4) (.pow (.var 2) 2))) (.add (.mul (.int 4) (.mul (.pow (.var 2) 3) (.pow (.var 4) 2))) (.add (.mul (.int (-2)) (.mul (.var 2) (.mul (.var 3) (.pow (.var 4) 2)))) (.add (.mul (.int 2) (.mul (.var 1) (.mul (.var 3) (.mul (.pow (.var 2) 2) (.pow (.var 4) 2))))) (.mul (.int 3) (.mul (.var 1) (.mul (.var 2) (.mul (.var 3) (.var 4)))))))))))))))
theorem dataB_5_1_binding : litBExpr 5 1=dataB_5_1 := rfl

def dataB_5_4 : RingExpr := (.mul (.var 8) (.add (.var 2) (.add (.mul (.var 1) (.var 3)) (.add (.mul (.int (-1)) (.mul (.var 3) (.var 4))) (.add (.mul (.int 2) (.mul (.var 4) (.pow (.var 2) 2))) (.mul (.var 1) (.mul (.var 2) (.mul (.var 3) (.var 4)))))))))
theorem dataB_5_4_binding : litBExpr 5 4=dataB_5_4 := rfl

def dataZ_0_3 : RingExpr := (.int 1)
theorem dataZ_0_3_binding : litZExpr 0 3=dataZ_0_3 := rfl

def dataZ_1_5 : RingExpr := (.int 1)
theorem dataZ_1_5_binding : litZExpr 1 5=dataZ_1_5 := rfl

def dataZ_2_0 : RingExpr := (.mul (.var 10) (.mul (.var 8) (.add (.int (-3)) (.add (.mul (.int 2) (.var 5)) (.add (.mul (.int 6) (.mul (.var 2) (.var 4))) (.add (.mul (.int (-6)) (.mul (.var 0) (.mul (.var 4) (.pow (.var 3) 2)))) (.mul (.int 6) (.mul (.var 1) (.mul (.var 3) (.var 4))))))))))
theorem dataZ_2_0_binding : litZExpr 2 0=dataZ_2_0 := rfl

def dataZ_2_1 : RingExpr := (.mul (.var 10) (.mul (.var 8) (.add (.mul (.int (-3)) (.var 2)) (.add (.mul (.int 2) (.mul (.var 5) (.var 2))) (.add (.mul (.int 6) (.mul (.var 4) (.pow (.var 2) 2))) (.add (.mul (.int (-6)) (.mul (.var 0) (.mul (.var 2) (.mul (.var 4) (.pow (.var 3) 2))))) (.mul (.int 6) (.mul (.var 1) (.mul (.var 2) (.mul (.var 3) (.var 4)))))))))))
theorem dataZ_2_1_binding : litZExpr 2 1=dataZ_2_1 := rfl

def dataZ_2_3 : RingExpr := (.mul (.var 10) (.mul (.var 8) (.add (.mul (.int (-3)) (.var 2)) (.add (.mul (.int (-6)) (.mul (.var 4) (.pow (.var 2) 2))) (.add (.mul (.int (-3)) (.mul (.var 1) (.var 3))) (.add (.mul (.int (-6)) (.mul (.var 1) (.mul (.var 2) (.mul (.var 3) (.var 4))))) (.mul (.int 6) (.mul (.var 0) (.mul (.var 2) (.mul (.var 4) (.pow (.var 3) 2)))))))))))
theorem dataZ_2_3_binding : litZExpr 2 3=dataZ_2_3 := rfl

def dataZ_2_4 : RingExpr := (.add (.mul (.int (-3)) (.pow (.var 10) 1)) (.add (.var 5) (.add (.mul (.int 3) (.mul (.var 2) (.var 4))) (.add (.mul (.int (-3)) (.mul (.var 0) (.mul (.var 4) (.pow (.var 3) 2)))) (.mul (.int 3) (.mul (.var 1) (.mul (.var 3) (.var 4))))))))
theorem dataZ_2_4_binding : litZExpr 2 4=dataZ_2_4 := rfl

def dataZ_2_5 : RingExpr := (.add (.mul (.int (3)) (.pow (.var 10) 1)) (.add (.mul (.int (-3)) (.mul (.var 2) (.var 4))) (.add (.mul (.int (-3)) (.mul (.var 1) (.mul (.var 3) (.var 4)))) (.mul (.int 3) (.mul (.var 0) (.mul (.var 4) (.pow (.var 3) 2)))))))
theorem dataZ_2_5_binding : litZExpr 2 5=dataZ_2_5 := rfl

def dataZ_3_0 : RingExpr := (.mul (.var 10) (.mul (.var 8) (.add (.int (-1)) (.add (.mul (.int (-2)) (.mul (.var 2) (.var 4))) (.mul (.int (-2)) (.mul (.var 0) (.mul (.var 4) (.pow (.var 3) 2))))))))
theorem dataZ_3_0_binding : litZExpr 3 0=dataZ_3_0 := rfl

def dataZ_3_1 : RingExpr := (.mul (.var 10) (.mul (.var 8) (.add (.mul (.int (-1)) (.var 2)) (.add (.mul (.int (-2)) (.mul (.var 4) (.pow (.var 2) 2))) (.mul (.int (-2)) (.mul (.var 0) (.mul (.var 2) (.mul (.var 4) (.pow (.var 3) 2)))))))))
theorem dataZ_3_1_binding : litZExpr 3 1=dataZ_3_1 := rfl

def dataZ_3_3 : RingExpr := (.mul (.var 10) (.mul (.var 8) (.add (.mul (.int (-1)) (.var 2)) (.add (.mul (.int (-1)) (.mul (.var 1) (.var 3))) (.add (.mul (.int (-2)) (.mul (.var 4) (.pow (.var 2) 2))) (.add (.mul (.int (-2)) (.mul (.var 1) (.mul (.var 2) (.mul (.var 3) (.var 4))))) (.mul (.int 2) (.mul (.var 0) (.mul (.var 2) (.mul (.var 4) (.pow (.var 3) 2)))))))))))
theorem dataZ_3_3_binding : litZExpr 3 3=dataZ_3_3 := rfl

def dataZ_3_4 : RingExpr := (.add (.mul (.int (-1)) (.pow (.var 10) 1)) (.add (.mul (.int (-1)) (.mul (.var 2) (.var 4))) (.mul (.int (-1)) (.mul (.var 0) (.mul (.var 4) (.pow (.var 3) 2))))))
theorem dataZ_3_4_binding : litZExpr 3 4=dataZ_3_4 := rfl

def dataZ_3_5 : RingExpr := (.add (.mul (.int (1)) (.pow (.var 10) 1)) (.add (.mul (.int (-1)) (.mul (.var 2) (.var 4))) (.add (.mul (.var 0) (.mul (.var 4) (.pow (.var 3) 2))) (.mul (.int (-1)) (.mul (.var 1) (.mul (.var 3) (.var 4)))))))
theorem dataZ_3_5_binding : litZExpr 3 5=dataZ_3_5 := rfl

def dataZ_4_0 : RingExpr := (.var 0)
theorem dataZ_4_0_binding : litZExpr 4 0=dataZ_4_0 := rfl

def dataZ_4_1 : RingExpr := (.mul (.var 0) (.var 2))
theorem dataZ_4_1_binding : litZExpr 4 1=dataZ_4_1 := rfl

def dataZ_4_3 : RingExpr := (.mul (.var 10) (.mul (.var 9) (.mul (.pow (.var 8) 2) (.add (.var 2) (.add (.mul (.var 1) (.var 3)) (.add (.mul (.int (-2)) (.mul (.var 3) (.var 4))) (.add (.mul (.int 2) (.mul (.var 4) (.pow (.var 2) 2))) (.add (.mul (.int (-2)) (.mul (.var 0) (.mul (.var 2) (.mul (.var 4) (.pow (.var 3) 2))))) (.mul (.int 2) (.mul (.var 1) (.mul (.var 2) (.mul (.var 3) (.var 4)))))))))))))
theorem dataZ_4_3_binding : litZExpr 4 3=dataZ_4_3 := rfl

def dataZ_4_4 : RingExpr := (.mul (.var 0) (.var 3))
theorem dataZ_4_4_binding : litZExpr 4 4=dataZ_4_4 := rfl

def dataZ_4_5 : RingExpr := (.add (.var 1) (.mul (.int (-1)) (.mul (.var 0) (.var 3))))
theorem dataZ_4_5_binding : litZExpr 4 5=dataZ_4_5 := rfl

def dataZ_5_0 : RingExpr := (.mul (.var 10) (.mul (.pow (.var 8) 2) (.add (.var 2) (.add (.mul (.int (-2)) (.mul (.var 3) (.var 4))) (.add (.mul (.int 2) (.mul (.var 0) (.pow (.var 3) 2))) (.add (.mul (.int 2) (.mul (.var 4) (.pow (.var 2) 2))) (.mul (.int 2) (.mul (.var 0) (.mul (.var 2) (.mul (.var 4) (.pow (.var 3) 2)))))))))))
theorem dataZ_5_0_binding : litZExpr 5 0=dataZ_5_0 := rfl

def dataZ_5_1 : RingExpr := (.mul (.var 10) (.mul (.pow (.var 8) 2) (.add (.pow (.var 2) 2) (.add (.mul (.int 2) (.mul (.var 4) (.pow (.var 2) 3))) (.add (.mul (.int (-2)) (.mul (.var 2) (.mul (.var 3) (.var 4)))) (.add (.mul (.int 2) (.mul (.var 0) (.mul (.var 2) (.pow (.var 3) 2)))) (.mul (.int 2) (.mul (.var 0) (.mul (.var 4) (.mul (.pow (.var 2) 2) (.pow (.var 3) 2)))))))))))
theorem dataZ_5_1_binding : litZExpr 5 1=dataZ_5_1 := rfl

def dataZ_5_3 : RingExpr := (.mul (.var 10) (.mul (.var 9) (.mul (.pow (.var 8) 2) (.add (.var 2) (.add (.mul (.var 1) (.var 3)) (.add (.mul (.int (-1)) (.mul (.var 3) (.var 4))) (.add (.mul (.int 2) (.mul (.pow (.var 2) 3) (.pow (.var 4) 2))) (.add (.mul (.int 3) (.mul (.var 4) (.pow (.var 2) 2))) (.add (.mul (.int (-2)) (.mul (.var 0) (.mul (.var 2) (.mul (.var 4) (.pow (.var 3) 2))))) (.add (.mul (.int (-2)) (.mul (.var 0) (.mul (.pow (.var 2) 2) (.mul (.pow (.var 3) 2) (.pow (.var 4) 2))))) (.add (.mul (.int 2) (.mul (.var 1) (.mul (.var 3) (.mul (.pow (.var 2) 2) (.pow (.var 4) 2))))) (.mul (.int 3) (.mul (.var 1) (.mul (.var 2) (.mul (.var 3) (.var 4))))))))))))))))
theorem dataZ_5_3_binding : litZExpr 5 3=dataZ_5_3 := rfl

def dataZ_5_4 : RingExpr := (.mul (.var 10) (.mul (.var 8) (.add (.var 2) (.add (.mul (.int (-2)) (.mul (.var 3) (.var 4))) (.add (.mul (.int 2) (.mul (.var 0) (.pow (.var 3) 2))) (.add (.mul (.int 2) (.mul (.var 4) (.pow (.var 2) 2))) (.mul (.int 2) (.mul (.var 0) (.mul (.var 2) (.mul (.var 4) (.pow (.var 3) 2)))))))))))
theorem dataZ_5_4_binding : litZExpr 5 4=dataZ_5_4 := rfl

def dataZ_5_5 : RingExpr := (.mul (.var 10) (.mul (.var 8) (.add (.var 2) (.add (.mul (.int (-2)) (.mul (.var 0) (.pow (.var 3) 2))) (.add (.mul (.int 2) (.mul (.var 1) (.var 3))) (.add (.mul (.int 2) (.mul (.var 4) (.pow (.var 2) 2))) (.add (.mul (.int (-2)) (.mul (.var 0) (.mul (.var 2) (.mul (.var 4) (.pow (.var 3) 2))))) (.mul (.int 2) (.mul (.var 1) (.mul (.var 2) (.mul (.var 3) (.var 4))))))))))))
theorem dataZ_5_5_binding : litZExpr 5 5=dataZ_5_5 := rfl

def dataT_0_2 : RingExpr := (.int 1)
theorem dataT_0_2_binding : litTExpr 0 2=dataT_0_2 := rfl

def dataT_1_0 : RingExpr := (.mul (.var 10) (.mul (.var 8) (.add (.int 3) (.add (.mul (.int 6) (.mul (.var 2) (.var 4))) (.add (.mul (.int 2) (.mul (.var 0) (.mul (.var 4) (.pow (.var 3) 2)))) (.mul (.int 6) (.mul (.var 6) (.mul (.var 3) (.var 4)))))))))
theorem dataT_1_0_binding : litTExpr 1 0=dataT_1_0 := rfl

def dataT_1_1 : RingExpr := (.mul (.var 10) (.mul (.var 8) (.add (.mul (.int 4) (.var 2)) (.add (.mul (.var 1) (.var 3)) (.add (.mul (.int (-3)) (.mul (.var 6) (.var 3))) (.add (.mul (.int 8) (.mul (.var 4) (.pow (.var 2) 2))) (.add (.mul (.int 2) (.mul (.var 1) (.mul (.var 2) (.mul (.var 3) (.var 4))))) (.mul (.int 6) (.mul (.var 6) (.mul (.var 2) (.mul (.var 3) (.var 4))))))))))))
theorem dataT_1_1_binding : litTExpr 1 1=dataT_1_1 := rfl

def dataT_1_2 : RingExpr := (.var 6)
theorem dataT_1_2_binding : litTExpr 1 2=dataT_1_2 := rfl

def dataT_1_4 : RingExpr := (.add (.int 3) (.add (.mul (.int 4) (.mul (.var 2) (.var 4))) (.add (.mul (.var 1) (.mul (.var 3) (.var 4))) (.mul (.int 3) (.mul (.var 6) (.mul (.var 3) (.var 4)))))))
theorem dataT_1_4_binding : litTExpr 1 4=dataT_1_4 := rfl

def dataT_2_0 : RingExpr := (.mul (.var 8) (.mul (.pow (.var 10) 2) (.add (.int 3) (.add (.mul (.int 4) (.var 5)) (.add (.mul (.int 30) (.mul (.var 2) (.var 4))) (.add (.mul (.int (-6)) (.mul (.var 0) (.mul (.var 4) (.pow (.var 3) 2)))) (.add (.mul (.int 12) (.mul (.var 1) (.mul (.var 3) (.var 4)))) (.mul (.int 18) (.mul (.var 6) (.mul (.var 3) (.var 4)))))))))))
theorem dataT_2_0_binding : litTExpr 2 0=dataT_2_0 := rfl

def dataT_2_1 : RingExpr := (.mul (.var 8) (.mul (.pow (.var 10) 2) (.add (.mul (.int (-9)) (.mul (.var 6) (.var 3))) (.add (.mul (.int (-3)) (.mul (.var 1) (.var 3))) (.add (.mul (.int 4) (.mul (.var 5) (.var 2))) (.add (.mul (.int 24) (.mul (.var 4) (.pow (.var 2) 2))) (.add (.mul (.int 6) (.mul (.var 1) (.mul (.var 2) (.mul (.var 3) (.var 4))))) (.mul (.int 18) (.mul (.var 6) (.mul (.var 2) (.mul (.var 3) (.var 4))))))))))))
theorem dataT_2_1_binding : litTExpr 2 1=dataT_2_1 := rfl

def dataT_2_2 : RingExpr := (.mul (.int 3) (.mul (.var 10) (.var 6)))
theorem dataT_2_2_binding : litTExpr 2 2=dataT_2_2 := rfl

def dataT_2_4 : RingExpr := (.add (.int 3) (.add (.var 5) (.add (.mul (.int 6) (.mul (.var 2) (.var 4))) (.add (.mul (.mul (.int (3)) (.pow (.var 10) 1)) (.mul (.var 1) (.mul (.var 3) (.var 4)))) (.mul (.mul (.int (9)) (.pow (.var 10) 1)) (.mul (.var 6) (.mul (.var 3) (.var 4))))))))
theorem dataT_2_4_binding : litTExpr 2 4=dataT_2_4 := rfl

def dataT_3_1 : RingExpr := (.mul (.var 10) (.mul (.var 8) (.add (.mul (.int (-1)) (.var 2)) (.add (.mul (.int (-1)) (.mul (.var 1) (.var 3))) (.add (.mul (.int (-2)) (.mul (.var 4) (.pow (.var 2) 2))) (.add (.mul (.int (-2)) (.mul (.var 1) (.mul (.var 2) (.mul (.var 3) (.var 4))))) (.mul (.int 2) (.mul (.var 0) (.mul (.var 2) (.mul (.var 4) (.pow (.var 3) 2)))))))))))
theorem dataT_3_1_binding : litTExpr 3 1=dataT_3_1 := rfl

def dataT_3_3 : RingExpr := (.mul (.var 10) (.mul (.var 8) (.add (.var 2) (.add (.mul (.var 1) (.var 3)) (.add (.mul (.int 2) (.mul (.var 4) (.pow (.var 2) 2))) (.add (.mul (.int (-2)) (.mul (.var 0) (.mul (.var 2) (.mul (.var 4) (.pow (.var 3) 2))))) (.mul (.int 2) (.mul (.var 1) (.mul (.var 2) (.mul (.var 3) (.var 4)))))))))))
theorem dataT_3_3_binding : litTExpr 3 3=dataT_3_3 := rfl

def dataT_3_4 : RingExpr := (.add (.mul (.int (1)) (.pow (.var 10) 1)) (.add (.mul (.int (-1)) (.mul (.var 2) (.var 4))) (.add (.mul (.var 0) (.mul (.var 4) (.pow (.var 3) 2))) (.mul (.int (-1)) (.mul (.var 1) (.mul (.var 3) (.var 4)))))))
theorem dataT_3_4_binding : litTExpr 3 4=dataT_3_4 := rfl

def dataT_3_5 : RingExpr := (.add (.mul (.int (1)) (.pow (.var 10) 1)) (.add (.mul (.var 2) (.var 4)) (.add (.mul (.var 1) (.mul (.var 3) (.var 4))) (.mul (.int (-1)) (.mul (.var 0) (.mul (.var 4) (.pow (.var 3) 2)))))))
theorem dataT_3_5_binding : litTExpr 3 5=dataT_3_5 := rfl

def dataT_4_0 : RingExpr := (.mul (.var 10) (.mul (.pow (.var 8) 2) (.add (.mul (.int (-3)) (.var 2)) (.add (.mul (.int (-6)) (.mul (.var 4) (.pow (.var 2) 2))) (.add (.mul (.int 2) (.mul (.var 0) (.pow (.var 3) 2))) (.add (.mul (.int (-6)) (.mul (.var 6) (.mul (.var 2) (.mul (.var 3) (.var 4))))) (.mul (.int (-2)) (.mul (.var 0) (.mul (.var 2) (.mul (.var 4) (.pow (.var 3) 2)))))))))))
theorem dataT_4_0_binding : litTExpr 4 0=dataT_4_0 := rfl

def dataT_4_1 : RingExpr := (.mul (.var 10) (.mul (.var 9) (.mul (.pow (.var 8) 2) (.add (.var 2) (.add (.mul (.var 1) (.var 3)) (.add (.mul (.int (-8)) (.mul (.pow (.var 2) 3) (.pow (.var 4) 2))) (.add (.mul (.int (-2)) (.mul (.var 4) (.pow (.var 2) 2))) (.add (.mul (.var 1) (.mul (.var 2) (.mul (.var 3) (.var 4)))) (.add (.mul (.int (-6)) (.mul (.var 6) (.mul (.var 3) (.mul (.pow (.var 2) 2) (.pow (.var 4) 2))))) (.add (.mul (.int (-2)) (.mul (.var 1) (.mul (.var 3) (.mul (.pow (.var 2) 2) (.pow (.var 4) 2))))) (.mul (.int 3) (.mul (.var 6) (.mul (.var 2) (.mul (.var 3) (.var 4)))))))))))))))
theorem dataT_4_1_binding : litTExpr 4 1=dataT_4_1 := rfl

def dataT_4_2 : RingExpr := (.mul (.var 8) (.add (.int (-1)) (.mul (.int (-1)) (.mul (.var 6) (.var 2)))))
theorem dataT_4_2_binding : litTExpr 4 2=dataT_4_2 := rfl

def dataT_4_4 : RingExpr := (.mul (.var 8) (.add (.mul (.int (-2)) (.var 2)) (.add (.mul (.var 1) (.var 3)) (.add (.mul (.int (-4)) (.mul (.var 4) (.pow (.var 2) 2))) (.add (.mul (.int (-1)) (.mul (.var 1) (.mul (.var 2) (.mul (.var 3) (.var 4))))) (.mul (.int (-3)) (.mul (.var 6) (.mul (.var 2) (.mul (.var 3) (.var 4))))))))))
theorem dataT_4_4_binding : litTExpr 4 4=dataT_4_4 := rfl

def dataT_5_0 : RingExpr := (.var 0)
theorem dataT_5_0_binding : litTExpr 5 0=dataT_5_0 := rfl

def dataT_5_1 : RingExpr := (.mul (.var 10) (.mul (.var 9) (.mul (.pow (.var 8) 2) (.add (.var 2) (.add (.mul (.var 1) (.var 3)) (.add (.mul (.int (-1)) (.mul (.var 3) (.var 4))) (.add (.mul (.int 2) (.mul (.pow (.var 2) 3) (.pow (.var 4) 2))) (.add (.mul (.int 3) (.mul (.var 4) (.pow (.var 2) 2))) (.add (.mul (.int (-2)) (.mul (.var 0) (.mul (.pow (.var 2) 2) (.mul (.pow (.var 3) 2) (.pow (.var 4) 2))))) (.add (.mul (.int 2) (.mul (.var 1) (.mul (.var 3) (.mul (.pow (.var 2) 2) (.pow (.var 4) 2))))) (.mul (.int 3) (.mul (.var 1) (.mul (.var 2) (.mul (.var 3) (.var 4)))))))))))))))
theorem dataT_5_1_binding : litTExpr 5 1=dataT_5_1 := rfl

def dataT_5_3 : RingExpr := (.mul (.var 10) (.mul (.pow (.var 8) 2) (.add (.mul (.int (-1)) (.var 3)) (.add (.mul (.int (-1)) (.pow (.var 2) 2)) (.add (.mul (.int (-2)) (.mul (.var 4) (.pow (.var 2) 3))) (.add (.mul (.int (-1)) (.mul (.var 1) (.mul (.var 2) (.var 3)))) (.add (.mul (.int (-2)) (.mul (.var 1) (.mul (.var 3) (.mul (.var 4) (.pow (.var 2) 2))))) (.mul (.int 2) (.mul (.var 0) (.mul (.var 4) (.mul (.pow (.var 2) 2) (.pow (.var 3) 2))))))))))))
theorem dataT_5_3_binding : litTExpr 5 3=dataT_5_3 := rfl

def dataT_5_4 : RingExpr := (.mul (.var 10) (.mul (.var 8) (.add (.var 2) (.add (.mul (.int 2) (.mul (.var 1) (.var 3))) (.add (.mul (.int 2) (.mul (.var 4) (.pow (.var 2) 2))) (.add (.mul (.int (-2)) (.mul (.var 0) (.mul (.var 2) (.mul (.var 4) (.pow (.var 3) 2))))) (.mul (.int 2) (.mul (.var 1) (.mul (.var 2) (.mul (.var 3) (.var 4)))))))))))
theorem dataT_5_4_binding : litTExpr 5 4=dataT_5_4 := rfl

def dataT_5_5 : RingExpr := (.mul (.var 10) (.mul (.var 8) (.add (.mul (.int (-1)) (.var 2)) (.add (.mul (.int (-2)) (.mul (.var 4) (.pow (.var 2) 2))) (.add (.mul (.int (-2)) (.mul (.var 1) (.mul (.var 2) (.mul (.var 3) (.var 4))))) (.mul (.int 2) (.mul (.var 0) (.mul (.var 2) (.mul (.var 4) (.pow (.var 3) 2))))))))))
theorem dataT_5_5_binding : litTExpr 5 5=dataT_5_5 := rfl

def dataV_0_0 : RingExpr := (.int 1)
theorem dataV_0_0_binding : litVExpr 0 0=dataV_0_0 := rfl

def dataV_1_1 : RingExpr := (.int 1)
theorem dataV_1_1_binding : litVExpr 1 1=dataV_1_1 := rfl

def dataV_2_0 : RingExpr := (.mul (.var 7) (.mul (.var 9) (.mul (.pow (.var 10) 2) (.mul (.pow (.var 8) 3) (.add (.mul (.int 3) (.var 2)) (.add (.mul (.int (-12)) (.mul (.pow (.var 2) 3) (.pow (.var 4) 2))) (.add (.mul (.int (-6)) (.mul (.var 3) (.var 4))) (.add (.mul (.int (-2)) (.mul (.var 5) (.var 2))) (.add (.mul (.int 3) (.mul (.var 1) (.var 3))) (.add (.mul (.int (-12)) (.mul (.var 0) (.mul (.pow (.var 3) 3) (.pow (.var 4) 2)))) (.add (.mul (.int (-6)) (.mul (.var 4) (.mul (.pow (.var 1) 2) (.pow (.var 3) 2)))) (.add (.mul (.int (-4)) (.mul (.var 5) (.mul (.var 4) (.pow (.var 2) 2)))) (.add (.mul (.int (-2)) (.mul (.var 5) (.mul (.var 1) (.var 3)))) (.add (.mul (.int 4) (.mul (.var 5) (.mul (.var 3) (.var 4)))) (.add (.mul (.int 12) (.mul (.var 1) (.mul (.pow (.var 3) 2) (.pow (.var 4) 2)))) (.add (.mul (.int 12) (.mul (.var 2) (.mul (.var 3) (.pow (.var 4) 2)))) (.add (.mul (.int (-24)) (.mul (.var 1) (.mul (.var 3) (.mul (.pow (.var 2) 2) (.pow (.var 4) 2))))) (.add (.mul (.int (-12)) (.mul (.var 2) (.mul (.pow (.var 1) 2) (.mul (.pow (.var 3) 2) (.pow (.var 4) 2))))) (.add (.mul (.int (-6)) (.mul (.var 0) (.mul (.var 2) (.mul (.var 4) (.pow (.var 3) 2))))) (.add (.mul (.int (-6)) (.mul (.var 1) (.mul (.var 2) (.mul (.var 3) (.var 4))))) (.add (.mul (.int 12) (.mul (.var 0) (.mul (.pow (.var 2) 2) (.mul (.pow (.var 3) 2) (.pow (.var 4) 2))))) (.add (.mul (.int (-4)) (.mul (.var 5) (.mul (.var 1) (.mul (.var 2) (.mul (.var 3) (.var 4)))))) (.add (.mul (.int 4) (.mul (.var 5) (.mul (.var 0) (.mul (.var 2) (.mul (.var 4) (.pow (.var 3) 2)))))) (.mul (.int 12) (.mul (.var 0) (.mul (.var 1) (.mul (.var 2) (.mul (.pow (.var 3) 3) (.pow (.var 4) 2)))))))))))))))))))))))))))))
theorem dataV_2_0_binding : litVExpr 2 0=dataV_2_0 := rfl

def dataV_2_1 : RingExpr := (.mul (.var 7) (.mul (.var 10) (.mul (.var 8) (.add (.mul (.int 3) (.var 1)) (.add (.mul (.int (-2)) (.mul (.var 5) (.var 1))) (.add (.mul (.int (-6)) (.mul (.var 1) (.mul (.var 2) (.var 4)))) (.add (.mul (.int (-6)) (.mul (.var 3) (.mul (.var 4) (.pow (.var 1) 2)))) (.add (.mul (.int 2) (.mul (.var 5) (.mul (.var 0) (.var 3)))) (.mul (.int 6) (.mul (.var 0) (.mul (.var 1) (.mul (.var 4) (.pow (.var 3) 2)))))))))))))
theorem dataV_2_1_binding : litVExpr 2 1=dataV_2_1 := rfl

def dataV_2_2 : RingExpr := (.mul (.var 7) (.mul (.var 10) (.mul (.var 8) (.add (.int (-3)) (.add (.mul (.int 2) (.var 5)) (.add (.mul (.int 6) (.mul (.var 2) (.var 4))) (.add (.mul (.int (-6)) (.mul (.var 0) (.mul (.var 4) (.pow (.var 3) 2)))) (.mul (.int 6) (.mul (.var 1) (.mul (.var 3) (.var 4)))))))))))
theorem dataV_2_2_binding : litVExpr 2 2=dataV_2_2 := rfl

def dataV_3_0 : RingExpr := (.mul (.var 7) (.mul (.var 9) (.mul (.pow (.var 10) 2) (.mul (.pow (.var 8) 3) (.add (.var 2) (.add (.mul (.var 1) (.var 3)) (.add (.mul (.int (-2)) (.mul (.var 3) (.var 4))) (.add (.mul (.int 4) (.mul (.var 4) (.pow (.var 2) 2))) (.add (.mul (.int 4) (.mul (.pow (.var 2) 3) (.pow (.var 4) 2))) (.add (.mul (.int (-4)) (.mul (.var 0) (.mul (.pow (.var 3) 3) (.pow (.var 4) 2)))) (.add (.mul (.int (-4)) (.mul (.var 2) (.mul (.var 3) (.pow (.var 4) 2)))) (.add (.mul (.int (-4)) (.mul (.var 0) (.mul (.pow (.var 2) 2) (.mul (.pow (.var 3) 2) (.pow (.var 4) 2))))) (.add (.mul (.int (-2)) (.mul (.var 0) (.mul (.var 2) (.mul (.var 4) (.pow (.var 3) 2))))) (.add (.mul (.int 4) (.mul (.var 1) (.mul (.var 2) (.mul (.var 3) (.var 4))))) (.mul (.int 4) (.mul (.var 1) (.mul (.var 3) (.mul (.pow (.var 2) 2) (.pow (.var 4) 2)))))))))))))))))))
theorem dataV_3_0_binding : litVExpr 3 0=dataV_3_0 := rfl

def dataV_3_1 : RingExpr := (.mul (.var 7) (.mul (.var 10) (.mul (.var 8) (.add (.var 1) (.add (.mul (.int 2) (.mul (.var 1) (.mul (.var 2) (.var 4)))) (.mul (.int (-4)) (.mul (.var 0) (.mul (.var 2) (.mul (.var 3) (.var 4))))))))))
theorem dataV_3_1_binding : litVExpr 3 1=dataV_3_1 := rfl

def dataV_3_2 : RingExpr := (.mul (.var 7) (.mul (.var 10) (.mul (.var 8) (.add (.int (-1)) (.add (.mul (.int (-2)) (.mul (.var 2) (.var 4))) (.mul (.int (-2)) (.mul (.var 0) (.mul (.var 4) (.pow (.var 3) 2)))))))))
theorem dataV_3_2_binding : litVExpr 3 2=dataV_3_2 := rfl

def dataV_4_2 : RingExpr := (.int 1)
theorem dataV_4_2_binding : litVExpr 4 2=dataV_4_2 := rfl

def dataV_5_0 : RingExpr := (.mul (.var 7) (.mul (.var 9) (.mul (.pow (.var 10) 2) (.mul (.pow (.var 8) 4) (.add (.mul (.int (-1)) (.pow (.var 2) 2)) (.add (.mul (.int (-4)) (.mul (.var 4) (.pow (.var 2) 3))) (.add (.mul (.int (-4)) (.mul (.pow (.var 2) 4) (.pow (.var 4) 2))) (.add (.mul (.int (-4)) (.mul (.pow (.var 3) 2) (.pow (.var 4) 2))) (.add (.mul (.int (-1)) (.mul (.var 1) (.mul (.var 2) (.var 3)))) (.add (.mul (.int 2) (.mul (.var 0) (.mul (.var 4) (.pow (.var 3) 3)))) (.add (.mul (.int 2) (.mul (.var 1) (.mul (.var 4) (.pow (.var 3) 2)))) (.add (.mul (.int 4) (.mul (.var 2) (.mul (.var 3) (.var 4)))) (.add (.mul (.int 8) (.mul (.var 3) (.mul (.pow (.var 2) 2) (.pow (.var 4) 2)))) (.add (.mul (.int (-4)) (.mul (.var 1) (.mul (.var 3) (.mul (.var 4) (.pow (.var 2) 2))))) (.add (.mul (.int (-4)) (.mul (.var 1) (.mul (.var 3) (.mul (.pow (.var 2) 3) (.pow (.var 4) 2))))) (.add (.mul (.int 2) (.mul (.var 0) (.mul (.var 4) (.mul (.pow (.var 2) 2) (.pow (.var 3) 2))))) (.add (.mul (.int 4) (.mul (.var 0) (.mul (.pow (.var 2) 3) (.mul (.pow (.var 3) 2) (.pow (.var 4) 2))))) (.mul (.int 4) (.mul (.var 1) (.mul (.var 2) (.mul (.pow (.var 3) 2) (.pow (.var 4) 2))))))))))))))))))))))
theorem dataV_5_0_binding : litVExpr 5 0=dataV_5_0 := rfl

def dataV_5_1 : RingExpr := (.mul (.var 7) (.mul (.var 10) (.mul (.pow (.var 8) 2) (.add (.mul (.int (-1)) (.mul (.var 1) (.var 2))) (.add (.mul (.int (-2)) (.mul (.var 0) (.mul (.var 4) (.pow (.var 3) 2)))) (.add (.mul (.int (-2)) (.mul (.var 1) (.mul (.var 4) (.pow (.var 2) 2)))) (.add (.mul (.int 2) (.mul (.var 0) (.mul (.var 2) (.var 3)))) (.add (.mul (.int 2) (.mul (.var 1) (.mul (.var 3) (.var 4)))) (.mul (.int 4) (.mul (.var 0) (.mul (.var 3) (.mul (.var 4) (.pow (.var 2) 2)))))))))))))
theorem dataV_5_1_binding : litVExpr 5 1=dataV_5_1 := rfl

def dataV_5_2 : RingExpr := (.mul (.var 7) (.mul (.var 10) (.mul (.pow (.var 8) 2) (.add (.var 2) (.add (.mul (.int (-2)) (.mul (.var 3) (.var 4))) (.add (.mul (.int 2) (.mul (.var 0) (.pow (.var 3) 2))) (.add (.mul (.int 2) (.mul (.var 4) (.pow (.var 2) 2))) (.mul (.int 2) (.mul (.var 0) (.mul (.var 2) (.mul (.var 4) (.pow (.var 3) 2))))))))))))
theorem dataV_5_2_binding : litVExpr 5 2=dataV_5_2 := rfl

def dataW_0_0 : RingExpr := (.int 1)
theorem dataW_0_0_binding : litWExpr 0 0=dataW_0_0 := rfl

def dataW_1_1 : RingExpr := (.int 1)
theorem dataW_1_1_binding : litWExpr 1 1=dataW_1_1 := rfl

def dataW_2_0 : RingExpr := (.mul (.var 10) (.mul (.var 8) (.add (.mul (.int (-3)) (.var 2)) (.add (.mul (.int (-6)) (.mul (.var 4) (.pow (.var 2) 2))) (.add (.mul (.int (-3)) (.mul (.var 1) (.var 3))) (.add (.mul (.int (-6)) (.mul (.var 1) (.mul (.var 2) (.mul (.var 3) (.var 4))))) (.mul (.int 6) (.mul (.var 0) (.mul (.var 2) (.mul (.var 4) (.pow (.var 3) 2)))))))))))
theorem dataW_2_0_binding : litWExpr 2 0=dataW_2_0 := rfl

def dataW_2_1 : RingExpr := (.add (.mul (.int (3)) (.pow (.var 10) 1)) (.add (.mul (.int (-3)) (.mul (.var 2) (.var 4))) (.add (.mul (.int (-3)) (.mul (.var 1) (.mul (.var 3) (.var 4)))) (.mul (.int 3) (.mul (.var 0) (.mul (.var 4) (.pow (.var 3) 2)))))))
theorem dataW_2_1_binding : litWExpr 2 1=dataW_2_1 := rfl

def dataW_3_0 : RingExpr := (.mul (.var 10) (.mul (.var 8) (.add (.mul (.int (-1)) (.var 2)) (.add (.mul (.int (-1)) (.mul (.var 1) (.var 3))) (.add (.mul (.int (-2)) (.mul (.var 4) (.pow (.var 2) 2))) (.add (.mul (.int (-2)) (.mul (.var 1) (.mul (.var 2) (.mul (.var 3) (.var 4))))) (.mul (.int 2) (.mul (.var 0) (.mul (.var 2) (.mul (.var 4) (.pow (.var 3) 2)))))))))))
theorem dataW_3_0_binding : litWExpr 3 0=dataW_3_0 := rfl

def dataW_3_1 : RingExpr := (.add (.mul (.int (1)) (.pow (.var 10) 1)) (.add (.mul (.int (-1)) (.mul (.var 2) (.var 4))) (.add (.mul (.var 0) (.mul (.var 4) (.pow (.var 3) 2))) (.mul (.int (-1)) (.mul (.var 1) (.mul (.var 3) (.var 4)))))))
theorem dataW_3_1_binding : litWExpr 3 1=dataW_3_1 := rfl

def dataW_4_0 : RingExpr := (.mul (.var 10) (.mul (.var 9) (.mul (.pow (.var 8) 2) (.add (.var 2) (.add (.mul (.var 1) (.var 3)) (.add (.mul (.int (-2)) (.mul (.var 3) (.var 4))) (.add (.mul (.int 2) (.mul (.var 4) (.pow (.var 2) 2))) (.add (.mul (.int (-2)) (.mul (.var 0) (.mul (.var 2) (.mul (.var 4) (.pow (.var 3) 2))))) (.mul (.int 2) (.mul (.var 1) (.mul (.var 2) (.mul (.var 3) (.var 4)))))))))))))
theorem dataW_4_0_binding : litWExpr 4 0=dataW_4_0 := rfl

def dataW_4_1 : RingExpr := (.add (.var 1) (.mul (.int (-1)) (.mul (.var 0) (.var 3))))
theorem dataW_4_1_binding : litWExpr 4 1=dataW_4_1 := rfl

def dataW_5_0 : RingExpr := (.mul (.var 10) (.mul (.var 9) (.mul (.pow (.var 8) 2) (.add (.var 2) (.add (.mul (.var 1) (.var 3)) (.add (.mul (.int (-1)) (.mul (.var 3) (.var 4))) (.add (.mul (.int 2) (.mul (.pow (.var 2) 3) (.pow (.var 4) 2))) (.add (.mul (.int 3) (.mul (.var 4) (.pow (.var 2) 2))) (.add (.mul (.int (-2)) (.mul (.var 0) (.mul (.var 2) (.mul (.var 4) (.pow (.var 3) 2))))) (.add (.mul (.int (-2)) (.mul (.var 0) (.mul (.pow (.var 2) 2) (.mul (.pow (.var 3) 2) (.pow (.var 4) 2))))) (.add (.mul (.int 2) (.mul (.var 1) (.mul (.var 3) (.mul (.pow (.var 2) 2) (.pow (.var 4) 2))))) (.mul (.int 3) (.mul (.var 1) (.mul (.var 2) (.mul (.var 3) (.var 4))))))))))))))))
theorem dataW_5_0_binding : litWExpr 5 0=dataW_5_0 := rfl

def dataW_5_1 : RingExpr := (.mul (.var 10) (.mul (.var 8) (.add (.var 2) (.add (.mul (.int (-2)) (.mul (.var 0) (.pow (.var 3) 2))) (.add (.mul (.int 2) (.mul (.var 1) (.var 3))) (.add (.mul (.int 2) (.mul (.var 4) (.pow (.var 2) 2))) (.add (.mul (.int (-2)) (.mul (.var 0) (.mul (.var 2) (.mul (.var 4) (.pow (.var 3) 2))))) (.mul (.int 2) (.mul (.var 1) (.mul (.var 2) (.mul (.var 3) (.var 4))))))))))))
theorem dataW_5_1_binding : litWExpr 5 1=dataW_5_1 := rfl

def dataHF_0_0 : RingExpr := (.mul (.var 7) (.mul (.var 9) (.mul (.pow (.var 8) 2) (.add (.var 2) (.add (.mul (.var 1) (.var 3)) (.add (.mul (.int (-2)) (.mul (.var 3) (.var 4))) (.add (.mul (.int 2) (.mul (.var 4) (.pow (.var 2) 2))) (.mul (.int 2) (.mul (.var 1) (.mul (.var 2) (.mul (.var 3) (.var 4))))))))))))
theorem dataHF_0_0_binding : litHFExpr 0 0=dataHF_0_0 := rfl

def dataHF_0_1 : RingExpr := (.mul (.int 2) (.mul (.var 7) (.var 1)))
theorem dataHF_0_1_binding : litHFExpr 0 1=dataHF_0_1 := rfl

def dataHF_0_2 : RingExpr := (.mul (.int (-2)) (.var 7))
theorem dataHF_0_2_binding : litHFExpr 0 2=dataHF_0_2 := rfl

def dataHF_1_0 : RingExpr := (.mul (.var 7) (.mul (.pow (.var 8) 2) (.add (.var 2) (.add (.mul (.var 1) (.var 3)) (.add (.mul (.int (-2)) (.mul (.var 0) (.pow (.var 3) 2))) (.add (.mul (.int (-2)) (.mul (.var 3) (.var 4))) (.add (.mul (.int 2) (.mul (.var 4) (.pow (.var 2) 2))) (.add (.mul (.int (-2)) (.mul (.var 0) (.mul (.var 2) (.mul (.var 4) (.pow (.var 3) 2))))) (.mul (.int 2) (.mul (.var 1) (.mul (.var 2) (.mul (.var 3) (.var 4)))))))))))))
theorem dataHF_1_0_binding : litHFExpr 1 0=dataHF_1_0 := rfl

def dataHF_1_1 : RingExpr := (.mul (.var 7) (.add (.mul (.int 2) (.mul (.var 1) (.var 4))) (.mul (.int (-2)) (.mul (.var 0) (.mul (.var 3) (.var 4))))))
theorem dataHF_1_1_binding : litHFExpr 1 1=dataHF_1_1 := rfl

def dataHF_1_2 : RingExpr := (.mul (.int (-2)) (.mul (.var 7) (.var 4)))
theorem dataHF_1_2_binding : litHFExpr 1 2=dataHF_1_2 := rfl

def dataHF_2_0 : RingExpr := (.int (-3))
theorem dataHF_2_0_binding : litHFExpr 2 0=dataHF_2_0 := rfl

def dataHF_3_0 : RingExpr := (.int (-1))
theorem dataHF_3_0_binding : litHFExpr 3 0=dataHF_3_0 := rfl

def dataHF_4_0 : RingExpr := (.mul (.var 7) (.mul (.var 10) (.mul (.var 9) (.mul (.pow (.var 8) 3) (.add (.mul (.int (-1)) (.var 2)) (.add (.mul (.int (-1)) (.mul (.var 1) (.var 3))) (.add (.mul (.int (-4)) (.mul (.var 4) (.pow (.var 2) 2))) (.add (.mul (.int (-4)) (.mul (.pow (.var 2) 3) (.pow (.var 4) 2))) (.add (.mul (.int 2) (.mul (.var 3) (.var 4))) (.add (.mul (.int 4) (.mul (.var 2) (.mul (.var 3) (.pow (.var 4) 2)))) (.add (.mul (.int (-4)) (.mul (.var 1) (.mul (.var 2) (.mul (.var 3) (.var 4))))) (.add (.mul (.int (-4)) (.mul (.var 1) (.mul (.var 3) (.mul (.pow (.var 2) 2) (.pow (.var 4) 2))))) (.add (.mul (.int 2) (.mul (.var 0) (.mul (.var 2) (.mul (.var 4) (.pow (.var 3) 2))))) (.mul (.int 4) (.mul (.var 0) (.mul (.pow (.var 2) 2) (.mul (.pow (.var 3) 2) (.pow (.var 4) 2))))))))))))))))))
theorem dataHF_4_0_binding : litHFExpr 4 0=dataHF_4_0 := rfl

def dataHF_4_1 : RingExpr := (.mul (.var 7) (.mul (.var 8) (.add (.mul (.int (-1)) (.var 1)) (.add (.mul (.int (-1)) (.mul (.var 0) (.var 3))) (.add (.mul (.int (-2)) (.mul (.var 1) (.mul (.var 2) (.var 4)))) (.mul (.int 2) (.mul (.var 0) (.mul (.var 2) (.mul (.var 3) (.var 4))))))))))
theorem dataHF_4_1_binding : litHFExpr 4 1=dataHF_4_1 := rfl

def dataHF_4_2 : RingExpr := (.mul (.var 7) (.mul (.var 8) (.add (.int 1) (.mul (.int 2) (.mul (.var 2) (.var 4))))))
theorem dataHF_4_2_binding : litHFExpr 4 2=dataHF_4_2 := rfl

def dataHF_5_1 : RingExpr := (.int (-1))
theorem dataHF_5_1_binding : litHFExpr 5 1=dataHF_5_1 := rfl

def dataHJ_3_0 : RingExpr := (.mul (.var 7) (.mul (.pow (.var 8) 2) (.add (.var 2) (.add (.mul (.var 1) (.var 3)) (.add (.mul (.int (-1)) (.mul (.var 0) (.pow (.var 3) 2))) (.add (.mul (.int (-2)) (.mul (.var 3) (.var 4))) (.add (.mul (.int 2) (.mul (.var 4) (.pow (.var 2) 2))) (.add (.mul (.int (-2)) (.mul (.var 0) (.mul (.var 2) (.mul (.var 4) (.pow (.var 3) 2))))) (.mul (.int 2) (.mul (.var 1) (.mul (.var 2) (.mul (.var 3) (.var 4)))))))))))))
theorem dataHJ_3_0_binding : litHJExpr 3 0=dataHJ_3_0 := rfl

def dataHJ_3_1 : RingExpr := (.mul (.var 7) (.add (.mul (.int 2) (.mul (.var 1) (.var 4))) (.mul (.int (-2)) (.mul (.var 0) (.mul (.var 3) (.var 4))))))
theorem dataHJ_3_1_binding : litHJExpr 3 1=dataHJ_3_1 := rfl

def dataHJ_3_2 : RingExpr := (.mul (.int (-2)) (.mul (.var 7) (.var 4)))
theorem dataHJ_3_2_binding : litHJExpr 3 2=dataHJ_3_2 := rfl

def dataHJ_5_0 : RingExpr := (.mul (.var 7) (.mul (.var 10) (.mul (.var 9) (.mul (.pow (.var 8) 3) (.add (.mul (.int (-1)) (.var 2)) (.add (.mul (.int (-1)) (.mul (.var 1) (.var 3))) (.add (.mul (.int (-4)) (.mul (.var 4) (.pow (.var 2) 2))) (.add (.mul (.int (-4)) (.mul (.pow (.var 2) 3) (.pow (.var 4) 2))) (.add (.mul (.int 2) (.mul (.var 3) (.var 4))) (.add (.mul (.int 4) (.mul (.var 2) (.mul (.var 3) (.pow (.var 4) 2)))) (.add (.mul (.int (-4)) (.mul (.var 1) (.mul (.var 2) (.mul (.var 3) (.var 4))))) (.add (.mul (.int (-4)) (.mul (.var 1) (.mul (.var 3) (.mul (.pow (.var 2) 2) (.pow (.var 4) 2))))) (.add (.mul (.int 2) (.mul (.var 0) (.mul (.var 2) (.mul (.var 4) (.pow (.var 3) 2))))) (.mul (.int 4) (.mul (.var 0) (.mul (.pow (.var 2) 2) (.mul (.pow (.var 3) 2) (.pow (.var 4) 2))))))))))))))))))
theorem dataHJ_5_0_binding : litHJExpr 5 0=dataHJ_5_0 := rfl

def dataHJ_5_1 : RingExpr := (.mul (.var 7) (.mul (.var 8) (.add (.mul (.int (-1)) (.var 1)) (.add (.mul (.int (-2)) (.mul (.var 1) (.mul (.var 2) (.var 4)))) (.mul (.int 2) (.mul (.var 0) (.mul (.var 2) (.mul (.var 3) (.var 4)))))))))
theorem dataHJ_5_1_binding : litHJExpr 5 1=dataHJ_5_1 := rfl

def dataHJ_5_2 : RingExpr := (.mul (.var 7) (.mul (.var 8) (.add (.int 1) (.mul (.int 2) (.mul (.var 2) (.var 4))))))
theorem dataHJ_5_2_binding : litHJExpr 5 2=dataHJ_5_2 := rfl

def dataHK_0_0 : RingExpr := (.mul (.int 2) (.var 2))
theorem dataHK_0_0_binding : litHKExpr 0 0=dataHK_0_0 := rfl

def dataHK_0_1 : RingExpr := (.mul (.int 2) (.var 3))
theorem dataHK_0_1_binding : litHKExpr 0 1=dataHK_0_1 := rfl

def dataHK_1_0 : RingExpr := (.int (-2))
theorem dataHK_1_0_binding : litHKExpr 1 0=dataHK_1_0 := rfl

def dataHK_2_0 : RingExpr := (.int (-3))
theorem dataHK_2_0_binding : litHKExpr 2 0=dataHK_2_0 := rfl

def dataHK_4_1 : RingExpr := (.int (-2))
theorem dataHK_4_1_binding : litHKExpr 4 1=dataHK_4_1 := rfl

def dataU_0_0 : RingExpr := (.mul (.var 7) (.mul (.var 10) (.mul (.var 9) (.mul (.pow (.var 8) 2) (.add (.var 2) (.add (.mul (.var 1) (.var 3)) (.add (.mul (.int 2) (.mul (.var 4) (.pow (.var 2) 2))) (.add (.mul (.int 4) (.mul (.var 1) (.mul (.pow (.var 3) 2) (.pow (.var 4) 2)))) (.add (.mul (.int 4) (.mul (.var 2) (.mul (.var 3) (.pow (.var 4) 2)))) (.mul (.int 2) (.mul (.var 1) (.mul (.var 2) (.mul (.var 3) (.var 4))))))))))))))
theorem dataU_0_0_binding : litUExpr 0 0=dataU_0_0 := rfl

def dataU_0_1 : RingExpr := (.mul (.var 7) (.mul (.var 8) (.add (.var 2) (.add (.mul (.var 1) (.var 3)) (.add (.mul (.int 2) (.mul (.var 4) (.pow (.var 2) 2))) (.mul (.int 2) (.mul (.var 1) (.mul (.var 2) (.mul (.var 3) (.var 4))))))))))
theorem dataU_0_1_binding : litUExpr 0 1=dataU_0_1 := rfl

def dataU_0_4 : RingExpr := (.mul (.var 7) (.add (.mul (.int 2) (.mul (.var 2) (.var 4))) (.mul (.int 2) (.mul (.var 1) (.mul (.var 3) (.var 4))))))
theorem dataU_0_4_binding : litUExpr 0 4=dataU_0_4 := rfl

def dataU_1_0 : RingExpr := (.mul (.var 7) (.mul (.pow (.var 8) 2) (.add (.mul (.int (-1)) (.var 2)) (.add (.mul (.int (-1)) (.mul (.var 0) (.pow (.var 3) 2))) (.add (.mul (.int (-1)) (.mul (.var 1) (.var 3))) (.add (.mul (.int (-2)) (.mul (.var 4) (.pow (.var 2) 2))) (.add (.mul (.int 2) (.mul (.var 3) (.var 4))) (.add (.mul (.int (-2)) (.mul (.var 1) (.mul (.var 2) (.mul (.var 3) (.var 4))))) (.mul (.int 2) (.mul (.var 0) (.mul (.var 2) (.mul (.var 4) (.pow (.var 3) 2)))))))))))))
theorem dataU_1_0_binding : litUExpr 1 0=dataU_1_0 := rfl

def dataU_1_1 : RingExpr := (.mul (.var 7) (.add (.mul (.int (-2)) (.mul (.var 1) (.var 4))) (.mul (.int 2) (.mul (.var 0) (.mul (.var 3) (.var 4))))))
theorem dataU_1_1_binding : litUExpr 1 1=dataU_1_1 := rfl

def dataU_1_4 : RingExpr := (.mul (.int 2) (.mul (.var 7) (.var 4)))
theorem dataU_1_4_binding : litUExpr 1 4=dataU_1_4 := rfl

def dataU_3_0 : RingExpr := (.mul (.var 7) (.mul (.pow (.var 8) 2) (.add (.mul (.int (-1)) (.var 2)) (.add (.mul (.int (-1)) (.mul (.var 0) (.pow (.var 3) 2))) (.add (.mul (.int (-1)) (.mul (.var 1) (.var 3))) (.add (.mul (.int (-2)) (.mul (.var 4) (.pow (.var 2) 2))) (.add (.mul (.int 2) (.mul (.var 3) (.var 4))) (.add (.mul (.int (-2)) (.mul (.var 1) (.mul (.var 2) (.mul (.var 3) (.var 4))))) (.mul (.int 2) (.mul (.var 0) (.mul (.var 2) (.mul (.var 4) (.pow (.var 3) 2)))))))))))))
theorem dataU_3_0_binding : litUExpr 3 0=dataU_3_0 := rfl

def dataU_3_1 : RingExpr := (.mul (.var 7) (.add (.mul (.int (-2)) (.mul (.var 0) (.var 2))) (.add (.mul (.int (-2)) (.mul (.var 1) (.var 4))) (.mul (.int 2) (.mul (.var 0) (.mul (.var 3) (.var 4)))))))
theorem dataU_3_1_binding : litUExpr 3 1=dataU_3_1 := rfl

def dataU_3_3 : RingExpr := (.mul (.int 2) (.var 2))
theorem dataU_3_3_binding : litUExpr 3 3=dataU_3_3 := rfl

def dataU_3_4 : RingExpr := (.mul (.var 7) (.add (.mul (.int 2) (.var 4)) (.mul (.int (-2)) (.mul (.var 0) (.var 3)))))
theorem dataU_3_4_binding : litUExpr 3 4=dataU_3_4 := rfl

def dataU_3_5 : RingExpr := (.mul (.int 2) (.var 3))
theorem dataU_3_5_binding : litUExpr 3 5=dataU_3_5 := rfl

def dataU_4_0 : RingExpr := (.mul (.var 7) (.mul (.var 10) (.mul (.var 9) (.mul (.pow (.var 8) 3) (.add (.var 2) (.add (.mul (.var 1) (.var 3)) (.add (.mul (.int (-2)) (.mul (.var 3) (.var 4))) (.add (.mul (.int 4) (.mul (.var 4) (.pow (.var 2) 2))) (.add (.mul (.int 4) (.mul (.pow (.var 2) 3) (.pow (.var 4) 2))) (.add (.mul (.int (-4)) (.mul (.var 0) (.mul (.pow (.var 3) 3) (.pow (.var 4) 2)))) (.add (.mul (.int (-4)) (.mul (.var 2) (.mul (.var 3) (.pow (.var 4) 2)))) (.add (.mul (.int (-4)) (.mul (.var 0) (.mul (.pow (.var 2) 2) (.mul (.pow (.var 3) 2) (.pow (.var 4) 2))))) (.add (.mul (.int (-2)) (.mul (.var 0) (.mul (.var 2) (.mul (.var 4) (.pow (.var 3) 2))))) (.add (.mul (.int 4) (.mul (.var 1) (.mul (.var 2) (.mul (.var 3) (.var 4))))) (.mul (.int 4) (.mul (.var 1) (.mul (.var 3) (.mul (.pow (.var 2) 2) (.pow (.var 4) 2)))))))))))))))))))
theorem dataU_4_0_binding : litUExpr 4 0=dataU_4_0 := rfl

def dataU_4_1 : RingExpr := (.mul (.var 7) (.mul (.var 8) (.add (.var 1) (.add (.mul (.int (-2)) (.mul (.var 0) (.var 3))) (.add (.mul (.int 2) (.mul (.var 1) (.mul (.var 2) (.var 4)))) (.mul (.int (-4)) (.mul (.var 0) (.mul (.var 2) (.mul (.var 3) (.var 4))))))))))
theorem dataU_4_1_binding : litUExpr 4 1=dataU_4_1 := rfl

def dataU_4_4 : RingExpr := (.mul (.var 7) (.mul (.var 8) (.add (.int (-1)) (.add (.mul (.int (-2)) (.mul (.var 2) (.var 4))) (.mul (.int (-2)) (.mul (.var 0) (.mul (.var 4) (.pow (.var 3) 2))))))))
theorem dataU_4_4_binding : litUExpr 4 4=dataU_4_4 := rfl

def dataU_5_0 : RingExpr := (.mul (.var 7) (.mul (.var 10) (.mul (.var 9) (.mul (.pow (.var 8) 3) (.add (.var 2) (.add (.mul (.var 1) (.var 3)) (.add (.mul (.int (-2)) (.mul (.var 3) (.var 4))) (.add (.mul (.int 4) (.mul (.var 4) (.pow (.var 2) 2))) (.add (.mul (.int 4) (.mul (.pow (.var 2) 3) (.pow (.var 4) 2))) (.add (.mul (.int (-4)) (.mul (.var 0) (.mul (.pow (.var 3) 3) (.pow (.var 4) 2)))) (.add (.mul (.int (-4)) (.mul (.var 2) (.mul (.var 3) (.pow (.var 4) 2)))) (.add (.mul (.int (-4)) (.mul (.var 0) (.mul (.pow (.var 2) 2) (.mul (.pow (.var 3) 2) (.pow (.var 4) 2))))) (.add (.mul (.int (-2)) (.mul (.var 0) (.mul (.var 2) (.mul (.var 4) (.pow (.var 3) 2))))) (.add (.mul (.int 4) (.mul (.var 1) (.mul (.var 2) (.mul (.var 3) (.var 4))))) (.mul (.int 4) (.mul (.var 1) (.mul (.var 3) (.mul (.pow (.var 2) 2) (.pow (.var 4) 2)))))))))))))))))))
theorem dataU_5_0_binding : litUExpr 5 0=dataU_5_0 := rfl

def dataU_5_1 : RingExpr := (.mul (.var 7) (.mul (.var 8) (.add (.var 1) (.add (.mul (.int 2) (.mul (.var 1) (.mul (.var 2) (.var 4)))) (.mul (.int (-4)) (.mul (.var 0) (.mul (.var 2) (.mul (.var 3) (.var 4)))))))))
theorem dataU_5_1_binding : litUExpr 5 1=dataU_5_1 := rfl

def dataU_5_3 : RingExpr := (.int (-2))
theorem dataU_5_3_binding : litUExpr 5 3=dataU_5_3 := rfl

def dataU_5_4 : RingExpr := (.mul (.var 7) (.mul (.var 8) (.add (.int (-1)) (.add (.mul (.int (-2)) (.mul (.var 2) (.var 4))) (.mul (.int (-2)) (.mul (.var 0) (.mul (.var 4) (.pow (.var 3) 2))))))))
theorem dataU_5_4_binding : litUExpr 5 4=dataU_5_4 := rfl

def dataK_0_0 : RingExpr := (.mul (.var 7) (.mul (.var 10) (.mul (.var 9) (.mul (.pow (.var 8) 2) (.add (.mul (.int 3) (.var 2)) (.add (.mul (.int (-4)) (.mul (.var 3) (.var 4))) (.add (.mul (.int 3) (.mul (.var 1) (.var 3))) (.add (.mul (.int 6) (.mul (.var 4) (.pow (.var 2) 2))) (.add (.mul (.int 4) (.mul (.var 1) (.mul (.pow (.var 3) 2) (.pow (.var 4) 2)))) (.add (.mul (.int 4) (.mul (.var 2) (.mul (.var 3) (.pow (.var 4) 2)))) (.mul (.int 6) (.mul (.var 1) (.mul (.var 2) (.mul (.var 3) (.var 4)))))))))))))))
theorem dataK_0_0_binding : litKExpr 0 0=dataK_0_0 := rfl

def dataK_0_1 : RingExpr := (.mul (.var 7) (.mul (.var 8) (.add (.var 2) (.add (.mul (.int 2) (.mul (.var 4) (.pow (.var 2) 2))) (.add (.mul (.int 3) (.mul (.var 1) (.var 3))) (.mul (.int 2) (.mul (.var 1) (.mul (.var 2) (.mul (.var 3) (.var 4))))))))))
theorem dataK_0_1_binding : litKExpr 0 1=dataK_0_1 := rfl

def dataK_0_4 : RingExpr := (.mul (.var 7) (.add (.int (-2)) (.add (.mul (.int 2) (.mul (.var 2) (.var 4))) (.mul (.int 2) (.mul (.var 1) (.mul (.var 3) (.var 4)))))))
theorem dataK_0_4_binding : litKExpr 0 4=dataK_0_4 := rfl

def dataK_1_0 : RingExpr := (.int (-3))
theorem dataK_1_0_binding : litKExpr 1 0=dataK_1_0 := rfl

def dataK_2_0 : RingExpr := (.int (-3))
theorem dataK_2_0_binding : litKExpr 2 0=dataK_2_0 := rfl

def dataK_3_0 : RingExpr := (.int (-3))
theorem dataK_3_0_binding : litKExpr 3 0=dataK_3_0 := rfl

def dataK_3_1 : RingExpr := (.mul (.int (-2)) (.var 2))
theorem dataK_3_1_binding : litKExpr 3 1=dataK_3_1 := rfl

def dataK_3_3 : RingExpr := (.mul (.int 2) (.var 2))
theorem dataK_3_3_binding : litKExpr 3 3=dataK_3_3 := rfl

def dataK_3_4 : RingExpr := (.mul (.int (-2)) (.var 3))
theorem dataK_3_4_binding : litKExpr 3 4=dataK_3_4 := rfl

def dataK_3_5 : RingExpr := (.mul (.int 2) (.var 3))
theorem dataK_3_5_binding : litKExpr 3 5=dataK_3_5 := rfl

def dataK_4_0 : RingExpr := (.mul (.int (-2)) (.var 4))
theorem dataK_4_0_binding : litKExpr 4 0=dataK_4_0 := rfl

def dataK_4_1 : RingExpr := (.add (.int (-3)) (.mul (.int (-2)) (.mul (.var 2) (.var 4))))
theorem dataK_4_1_binding : litKExpr 4 1=dataK_4_1 := rfl

def dataK_4_4 : RingExpr := (.mul (.int (-2)) (.mul (.var 3) (.var 4)))
theorem dataK_4_4_binding : litKExpr 4 4=dataK_4_4 := rfl

def dataK_5_0 : RingExpr := (.mul (.int (-2)) (.var 4))
theorem dataK_5_0_binding : litKExpr 5 0=dataK_5_0 := rfl

def dataK_5_1 : RingExpr := (.add (.int (-1)) (.mul (.int (-2)) (.mul (.var 2) (.var 4))))
theorem dataK_5_1_binding : litKExpr 5 1=dataK_5_1 := rfl

def dataK_5_3 : RingExpr := (.int (-2))
theorem dataK_5_3_binding : litKExpr 5 3=dataK_5_3 := rfl

def dataK_5_4 : RingExpr := (.mul (.int (-2)) (.mul (.var 3) (.var 4)))
theorem dataK_5_4_binding : litKExpr 5 4=dataK_5_4 := rfl

def dataH_0_0 : RingExpr := (.mul (.var 7) (.mul (.var 9) (.mul (.pow (.var 8) 2) (.add (.var 2) (.add (.mul (.var 1) (.var 3)) (.add (.mul (.int (-2)) (.mul (.var 3) (.var 4))) (.add (.mul (.int 2) (.mul (.var 4) (.pow (.var 2) 2))) (.mul (.int 2) (.mul (.var 1) (.mul (.var 2) (.mul (.var 3) (.var 4))))))))))))
theorem dataH_0_0_binding : litHExpr 0 0=dataH_0_0 := rfl

def dataH_0_1 : RingExpr := (.mul (.int 2) (.mul (.var 7) (.var 1)))
theorem dataH_0_1_binding : litHExpr 0 1=dataH_0_1 := rfl

def dataH_0_2 : RingExpr := (.mul (.int (-2)) (.var 7))
theorem dataH_0_2_binding : litHExpr 0 2=dataH_0_2 := rfl

def dataH_0_6 : RingExpr := (.mul (.int 2) (.var 2))
theorem dataH_0_6_binding : litHExpr 0 6=dataH_0_6 := rfl

def dataH_0_7 : RingExpr := (.mul (.int 2) (.var 3))
theorem dataH_0_7_binding : litHExpr 0 7=dataH_0_7 := rfl

def dataH_0_8 : RingExpr := (.mul (.var 7) (.mul (.var 10) (.mul (.var 9) (.mul (.pow (.var 8) 2) (.add (.mul (.var 11) (.var 2)) (.add (.mul (.var 11) (.mul (.var 1) (.var 3))) (.add (.mul (.int 2) (.mul (.var 11) (.mul (.var 4) (.pow (.var 2) 2)))) (.add (.mul (.int 2) (.mul (.var 12) (.mul (.var 1) (.mul (.var 4) (.pow (.var 3) 2))))) (.add (.mul (.int 2) (.mul (.var 12) (.mul (.var 2) (.mul (.var 3) (.var 4))))) (.add (.mul (.int 4) (.mul (.var 11) (.mul (.var 1) (.mul (.pow (.var 3) 2) (.pow (.var 4) 2))))) (.add (.mul (.int 4) (.mul (.var 11) (.mul (.var 2) (.mul (.var 3) (.pow (.var 4) 2))))) (.add (.mul (.int 4) (.mul (.var 12) (.mul (.var 3) (.mul (.pow (.var 2) 2) (.pow (.var 4) 2))))) (.add (.mul (.int 4) (.mul (.var 15) (.mul (.var 1) (.mul (.pow (.var 3) 3) (.pow (.var 4) 2))))) (.add (.mul (.int 4) (.mul (.var 15) (.mul (.var 2) (.mul (.pow (.var 3) 2) (.pow (.var 4) 2))))) (.add (.mul (.int 2) (.mul (.var 11) (.mul (.var 1) (.mul (.var 2) (.mul (.var 3) (.var 4)))))) (.mul (.int 4) (.mul (.var 12) (.mul (.var 1) (.mul (.var 2) (.mul (.pow (.var 3) 2) (.pow (.var 4) 2)))))))))))))))))))))
theorem dataH_0_8_binding : litHExpr 0 8=dataH_0_8 := rfl

def dataH_1_0 : RingExpr := (.mul (.var 7) (.mul (.pow (.var 8) 2) (.add (.var 2) (.add (.mul (.var 1) (.var 3)) (.add (.mul (.int (-2)) (.mul (.var 0) (.pow (.var 3) 2))) (.add (.mul (.int (-2)) (.mul (.var 3) (.var 4))) (.add (.mul (.int 2) (.mul (.var 4) (.pow (.var 2) 2))) (.add (.mul (.int (-2)) (.mul (.var 0) (.mul (.var 2) (.mul (.var 4) (.pow (.var 3) 2))))) (.mul (.int 2) (.mul (.var 1) (.mul (.var 2) (.mul (.var 3) (.var 4)))))))))))))
theorem dataH_1_0_binding : litHExpr 1 0=dataH_1_0 := rfl

def dataH_1_1 : RingExpr := (.mul (.var 7) (.add (.mul (.int 2) (.mul (.var 1) (.var 4))) (.mul (.int (-2)) (.mul (.var 0) (.mul (.var 3) (.var 4))))))
theorem dataH_1_1_binding : litHExpr 1 1=dataH_1_1 := rfl

def dataH_1_2 : RingExpr := (.mul (.int (-2)) (.mul (.var 7) (.var 4)))
theorem dataH_1_2_binding : litHExpr 1 2=dataH_1_2 := rfl

def dataH_1_6 : RingExpr := (.int (-2))
theorem dataH_1_6_binding : litHExpr 1 6=dataH_1_6 := rfl

def dataH_1_8 : RingExpr := (.mul (.var 7) (.mul (.pow (.var 8) 2) (.add (.mul (.int (-1)) (.mul (.var 11) (.var 2))) (.add (.mul (.int (-1)) (.mul (.var 11) (.mul (.var 0) (.pow (.var 3) 2)))) (.add (.mul (.int (-1)) (.mul (.var 11) (.mul (.var 1) (.var 3)))) (.add (.mul (.int (-2)) (.mul (.var 11) (.mul (.var 4) (.pow (.var 2) 2)))) (.add (.mul (.int 2) (.mul (.var 11) (.mul (.var 3) (.var 4)))) (.add (.mul (.int 2) (.mul (.var 15) (.mul (.var 4) (.pow (.var 3) 2)))) (.add (.mul (.int (-2)) (.mul (.var 12) (.mul (.var 1) (.mul (.var 4) (.pow (.var 3) 2))))) (.add (.mul (.int 2) (.mul (.var 12) (.mul (.var 0) (.mul (.var 4) (.pow (.var 3) 3))))) (.add (.mul (.int (-2)) (.mul (.var 11) (.mul (.var 1) (.mul (.var 2) (.mul (.var 3) (.var 4)))))) (.mul (.int 2) (.mul (.var 11) (.mul (.var 0) (.mul (.var 2) (.mul (.var 4) (.pow (.var 3) 2)))))))))))))))))
theorem dataH_1_8_binding : litHExpr 1 8=dataH_1_8 := rfl

def dataH_2_0 : RingExpr := (.int (-3))
theorem dataH_2_0_binding : litHExpr 2 0=dataH_2_0 := rfl

def dataH_2_6 : RingExpr := (.int (-3))
theorem dataH_2_6_binding : litHExpr 2 6=dataH_2_6 := rfl

def dataH_3_0 : RingExpr := (.int (-1))
theorem dataH_3_0_binding : litHExpr 3 0=dataH_3_0 := rfl

def dataH_3_3 : RingExpr := (.mul (.var 7) (.mul (.pow (.var 8) 2) (.add (.var 2) (.add (.mul (.var 1) (.var 3)) (.add (.mul (.int (-1)) (.mul (.var 0) (.pow (.var 3) 2))) (.add (.mul (.int (-2)) (.mul (.var 3) (.var 4))) (.add (.mul (.int 2) (.mul (.var 4) (.pow (.var 2) 2))) (.add (.mul (.int (-2)) (.mul (.var 0) (.mul (.var 2) (.mul (.var 4) (.pow (.var 3) 2))))) (.mul (.int 2) (.mul (.var 1) (.mul (.var 2) (.mul (.var 3) (.var 4)))))))))))))
theorem dataH_3_3_binding : litHExpr 3 3=dataH_3_3 := rfl

def dataH_3_4 : RingExpr := (.mul (.var 7) (.add (.mul (.int 2) (.mul (.var 1) (.var 4))) (.mul (.int (-2)) (.mul (.var 0) (.mul (.var 3) (.var 4))))))
theorem dataH_3_4_binding : litHExpr 3 4=dataH_3_4 := rfl

def dataH_3_5 : RingExpr := (.mul (.int (-2)) (.mul (.var 7) (.var 4)))
theorem dataH_3_5_binding : litHExpr 3 5=dataH_3_5 := rfl

def dataH_3_8 : RingExpr := (.mul (.var 7) (.mul (.pow (.var 8) 2) (.add (.mul (.int (-1)) (.mul (.var 11) (.var 2))) (.add (.mul (.int (-1)) (.mul (.var 11) (.mul (.var 0) (.pow (.var 3) 2)))) (.add (.mul (.int (-1)) (.mul (.var 11) (.mul (.var 1) (.var 3)))) (.add (.mul (.int (-2)) (.mul (.var 11) (.mul (.var 4) (.pow (.var 2) 2)))) (.add (.mul (.int (-2)) (.mul (.var 15) (.mul (.var 0) (.pow (.var 3) 3)))) (.add (.mul (.int 2) (.mul (.var 11) (.mul (.var 3) (.var 4)))) (.add (.mul (.int 2) (.mul (.var 15) (.mul (.var 4) (.pow (.var 3) 2)))) (.add (.mul (.int 2) (.mul (.var 16) (.mul (.var 0) (.pow (.var 3) 3)))) (.add (.mul (.int (-2)) (.mul (.var 12) (.mul (.var 0) (.mul (.var 2) (.pow (.var 3) 2))))) (.add (.mul (.int (-2)) (.mul (.var 12) (.mul (.var 1) (.mul (.var 4) (.pow (.var 3) 2))))) (.add (.mul (.int 2) (.mul (.var 12) (.mul (.var 0) (.mul (.var 4) (.pow (.var 3) 3))))) (.add (.mul (.int 2) (.mul (.var 14) (.mul (.var 0) (.mul (.var 2) (.pow (.var 3) 2))))) (.add (.mul (.int (-2)) (.mul (.var 11) (.mul (.var 1) (.mul (.var 2) (.mul (.var 3) (.var 4)))))) (.mul (.int 2) (.mul (.var 11) (.mul (.var 0) (.mul (.var 2) (.mul (.var 4) (.pow (.var 3) 2)))))))))))))))))))))
theorem dataH_3_8_binding : litHExpr 3 8=dataH_3_8 := rfl

def dataH_4_0 : RingExpr := (.mul (.var 7) (.mul (.var 10) (.mul (.var 9) (.mul (.pow (.var 8) 3) (.add (.mul (.int (-1)) (.var 2)) (.add (.mul (.int (-1)) (.mul (.var 1) (.var 3))) (.add (.mul (.int (-4)) (.mul (.var 4) (.pow (.var 2) 2))) (.add (.mul (.int (-4)) (.mul (.pow (.var 2) 3) (.pow (.var 4) 2))) (.add (.mul (.int 2) (.mul (.var 3) (.var 4))) (.add (.mul (.int 4) (.mul (.var 2) (.mul (.var 3) (.pow (.var 4) 2)))) (.add (.mul (.int (-4)) (.mul (.var 1) (.mul (.var 2) (.mul (.var 3) (.var 4))))) (.add (.mul (.int (-4)) (.mul (.var 1) (.mul (.var 3) (.mul (.pow (.var 2) 2) (.pow (.var 4) 2))))) (.add (.mul (.int 2) (.mul (.var 0) (.mul (.var 2) (.mul (.var 4) (.pow (.var 3) 2))))) (.mul (.int 4) (.mul (.var 0) (.mul (.pow (.var 2) 2) (.mul (.pow (.var 3) 2) (.pow (.var 4) 2))))))))))))))))))
theorem dataH_4_0_binding : litHExpr 4 0=dataH_4_0 := rfl

def dataH_4_1 : RingExpr := (.mul (.var 7) (.mul (.var 8) (.add (.mul (.int (-1)) (.var 1)) (.add (.mul (.int (-1)) (.mul (.var 0) (.var 3))) (.add (.mul (.int (-2)) (.mul (.var 1) (.mul (.var 2) (.var 4)))) (.mul (.int 2) (.mul (.var 0) (.mul (.var 2) (.mul (.var 3) (.var 4))))))))))
theorem dataH_4_1_binding : litHExpr 4 1=dataH_4_1 := rfl

def dataH_4_2 : RingExpr := (.mul (.var 7) (.mul (.var 8) (.add (.int 1) (.mul (.int 2) (.mul (.var 2) (.var 4))))))
theorem dataH_4_2_binding : litHExpr 4 2=dataH_4_2 := rfl

def dataH_4_7 : RingExpr := (.int (-2))
theorem dataH_4_7_binding : litHExpr 4 7=dataH_4_7 := rfl

def dataH_4_8 : RingExpr := (.mul (.var 7) (.mul (.var 10) (.mul (.var 9) (.mul (.pow (.var 8) 3) (.add (.mul (.var 11) (.var 2)) (.add (.mul (.var 11) (.mul (.var 1) (.var 3))) (.add (.mul (.int (-2)) (.mul (.var 11) (.mul (.var 3) (.var 4)))) (.add (.mul (.int (-2)) (.mul (.var 15) (.mul (.var 4) (.pow (.var 3) 2)))) (.add (.mul (.int 4) (.mul (.var 11) (.mul (.var 4) (.pow (.var 2) 2)))) (.add (.mul (.int 4) (.mul (.var 11) (.mul (.pow (.var 2) 3) (.pow (.var 4) 2)))) (.add (.mul (.int (-4)) (.mul (.var 11) (.mul (.var 0) (.mul (.pow (.var 3) 3) (.pow (.var 4) 2))))) (.add (.mul (.int (-4)) (.mul (.var 11) (.mul (.var 2) (.mul (.var 3) (.pow (.var 4) 2))))) (.add (.mul (.int (-4)) (.mul (.var 12) (.mul (.var 0) (.mul (.var 4) (.pow (.var 3) 3))))) (.add (.mul (.int (-4)) (.mul (.var 15) (.mul (.var 0) (.mul (.pow (.var 3) 4) (.pow (.var 4) 2))))) (.add (.mul (.int (-4)) (.mul (.var 15) (.mul (.var 2) (.mul (.pow (.var 3) 2) (.pow (.var 4) 2))))) (.add (.mul (.int 2) (.mul (.var 12) (.mul (.var 1) (.mul (.var 4) (.pow (.var 3) 2))))) (.add (.mul (.int (-8)) (.mul (.var 12) (.mul (.var 0) (.mul (.var 2) (.mul (.pow (.var 3) 3) (.pow (.var 4) 2)))))) (.add (.mul (.int (-4)) (.mul (.var 11) (.mul (.var 0) (.mul (.pow (.var 2) 2) (.mul (.pow (.var 3) 2) (.pow (.var 4) 2)))))) (.add (.mul (.int (-2)) (.mul (.var 11) (.mul (.var 0) (.mul (.var 2) (.mul (.var 4) (.pow (.var 3) 2)))))) (.add (.mul (.int 4) (.mul (.var 11) (.mul (.var 1) (.mul (.var 2) (.mul (.var 3) (.var 4)))))) (.add (.mul (.int 4) (.mul (.var 11) (.mul (.var 1) (.mul (.var 3) (.mul (.pow (.var 2) 2) (.pow (.var 4) 2)))))) (.mul (.int 4) (.mul (.var 12) (.mul (.var 1) (.mul (.var 2) (.mul (.pow (.var 3) 2) (.pow (.var 4) 2)))))))))))))))))))))))))))
theorem dataH_4_8_binding : litHExpr 4 8=dataH_4_8 := rfl

def dataH_5_1 : RingExpr := (.int (-1))
theorem dataH_5_1_binding : litHExpr 5 1=dataH_5_1 := rfl

def dataH_5_3 : RingExpr := (.mul (.var 7) (.mul (.var 10) (.mul (.var 9) (.mul (.pow (.var 8) 3) (.add (.mul (.int (-1)) (.var 2)) (.add (.mul (.int (-1)) (.mul (.var 1) (.var 3))) (.add (.mul (.int (-4)) (.mul (.var 4) (.pow (.var 2) 2))) (.add (.mul (.int (-4)) (.mul (.pow (.var 2) 3) (.pow (.var 4) 2))) (.add (.mul (.int 2) (.mul (.var 3) (.var 4))) (.add (.mul (.int 4) (.mul (.var 2) (.mul (.var 3) (.pow (.var 4) 2)))) (.add (.mul (.int (-4)) (.mul (.var 1) (.mul (.var 2) (.mul (.var 3) (.var 4))))) (.add (.mul (.int (-4)) (.mul (.var 1) (.mul (.var 3) (.mul (.pow (.var 2) 2) (.pow (.var 4) 2))))) (.add (.mul (.int 2) (.mul (.var 0) (.mul (.var 2) (.mul (.var 4) (.pow (.var 3) 2))))) (.mul (.int 4) (.mul (.var 0) (.mul (.pow (.var 2) 2) (.mul (.pow (.var 3) 2) (.pow (.var 4) 2))))))))))))))))))
theorem dataH_5_3_binding : litHExpr 5 3=dataH_5_3 := rfl

def dataH_5_4 : RingExpr := (.mul (.var 7) (.mul (.var 8) (.add (.mul (.int (-1)) (.var 1)) (.add (.mul (.int (-2)) (.mul (.var 1) (.mul (.var 2) (.var 4)))) (.mul (.int 2) (.mul (.var 0) (.mul (.var 2) (.mul (.var 3) (.var 4)))))))))
theorem dataH_5_4_binding : litHExpr 5 4=dataH_5_4 := rfl

def dataH_5_5 : RingExpr := (.mul (.var 7) (.mul (.var 8) (.add (.int 1) (.mul (.int 2) (.mul (.var 2) (.var 4))))))
theorem dataH_5_5_binding : litHExpr 5 5=dataH_5_5 := rfl

def dataH_5_8 : RingExpr := (.mul (.var 7) (.mul (.var 10) (.mul (.var 9) (.mul (.pow (.var 8) 3) (.add (.mul (.var 11) (.var 2)) (.add (.mul (.var 11) (.mul (.var 1) (.var 3))) (.add (.mul (.int (-2)) (.mul (.var 11) (.mul (.var 3) (.var 4)))) (.add (.mul (.int (-2)) (.mul (.var 15) (.mul (.var 4) (.pow (.var 3) 2)))) (.add (.mul (.int 4) (.mul (.var 11) (.mul (.var 4) (.pow (.var 2) 2)))) (.add (.mul (.int 4) (.mul (.var 11) (.mul (.pow (.var 2) 3) (.pow (.var 4) 2)))) (.add (.mul (.int (-4)) (.mul (.var 11) (.mul (.var 0) (.mul (.pow (.var 3) 3) (.pow (.var 4) 2))))) (.add (.mul (.int (-4)) (.mul (.var 11) (.mul (.var 2) (.mul (.var 3) (.pow (.var 4) 2))))) (.add (.mul (.int (-4)) (.mul (.var 14) (.mul (.var 0) (.mul (.var 4) (.pow (.var 3) 3))))) (.add (.mul (.int (-4)) (.mul (.var 15) (.mul (.var 0) (.mul (.pow (.var 3) 4) (.pow (.var 4) 2))))) (.add (.mul (.int (-4)) (.mul (.var 15) (.mul (.var 2) (.mul (.pow (.var 3) 2) (.pow (.var 4) 2))))) (.add (.mul (.int 2) (.mul (.var 12) (.mul (.var 1) (.mul (.var 4) (.pow (.var 3) 2))))) (.add (.mul (.int (-8)) (.mul (.var 12) (.mul (.var 0) (.mul (.var 2) (.mul (.pow (.var 3) 3) (.pow (.var 4) 2)))))) (.add (.mul (.int (-4)) (.mul (.var 11) (.mul (.var 0) (.mul (.pow (.var 2) 2) (.mul (.pow (.var 3) 2) (.pow (.var 4) 2)))))) (.add (.mul (.int (-2)) (.mul (.var 11) (.mul (.var 0) (.mul (.var 2) (.mul (.var 4) (.pow (.var 3) 2)))))) (.add (.mul (.int 4) (.mul (.var 11) (.mul (.var 1) (.mul (.var 2) (.mul (.var 3) (.var 4)))))) (.add (.mul (.int 4) (.mul (.var 11) (.mul (.var 1) (.mul (.var 3) (.mul (.pow (.var 2) 2) (.pow (.var 4) 2)))))) (.mul (.int 4) (.mul (.var 12) (.mul (.var 1) (.mul (.var 2) (.mul (.pow (.var 3) 2) (.pow (.var 4) 2)))))))))))))))))))))))))))
theorem dataH_5_8_binding : litHExpr 5 8=dataH_5_8 := rfl

def dataS_0_0 : RingExpr := (.int 1)
theorem dataS_0_0_binding : litSExpr 0 0=dataS_0_0 := rfl

def dataS_1_1 : RingExpr := (.int 1)
theorem dataS_1_1_binding : litSExpr 1 1=dataS_1_1 := rfl

def dataS_2_0 : RingExpr := (.mul (.var 7) (.mul (.var 9) (.mul (.pow (.var 10) 2) (.mul (.pow (.var 8) 3) (.add (.mul (.int 3) (.var 2)) (.add (.mul (.int (-12)) (.mul (.pow (.var 2) 3) (.pow (.var 4) 2))) (.add (.mul (.int (-6)) (.mul (.var 3) (.var 4))) (.add (.mul (.int (-2)) (.mul (.var 5) (.var 2))) (.add (.mul (.int 3) (.mul (.var 1) (.var 3))) (.add (.mul (.int (-12)) (.mul (.var 0) (.mul (.pow (.var 3) 3) (.pow (.var 4) 2)))) (.add (.mul (.int (-6)) (.mul (.var 4) (.mul (.pow (.var 1) 2) (.pow (.var 3) 2)))) (.add (.mul (.int (-4)) (.mul (.var 5) (.mul (.var 4) (.pow (.var 2) 2)))) (.add (.mul (.int (-2)) (.mul (.var 5) (.mul (.var 1) (.var 3)))) (.add (.mul (.int 4) (.mul (.var 5) (.mul (.var 3) (.var 4)))) (.add (.mul (.int 12) (.mul (.var 1) (.mul (.pow (.var 3) 2) (.pow (.var 4) 2)))) (.add (.mul (.int 12) (.mul (.var 2) (.mul (.var 3) (.pow (.var 4) 2)))) (.add (.mul (.int (-24)) (.mul (.var 1) (.mul (.var 3) (.mul (.pow (.var 2) 2) (.pow (.var 4) 2))))) (.add (.mul (.int (-12)) (.mul (.var 2) (.mul (.pow (.var 1) 2) (.mul (.pow (.var 3) 2) (.pow (.var 4) 2))))) (.add (.mul (.int (-6)) (.mul (.var 0) (.mul (.var 2) (.mul (.var 4) (.pow (.var 3) 2))))) (.add (.mul (.int (-6)) (.mul (.var 1) (.mul (.var 2) (.mul (.var 3) (.var 4))))) (.add (.mul (.int 12) (.mul (.var 0) (.mul (.pow (.var 2) 2) (.mul (.pow (.var 3) 2) (.pow (.var 4) 2))))) (.add (.mul (.int (-4)) (.mul (.var 5) (.mul (.var 1) (.mul (.var 2) (.mul (.var 3) (.var 4)))))) (.add (.mul (.int 4) (.mul (.var 5) (.mul (.var 0) (.mul (.var 2) (.mul (.var 4) (.pow (.var 3) 2)))))) (.mul (.int 12) (.mul (.var 0) (.mul (.var 1) (.mul (.var 2) (.mul (.pow (.var 3) 3) (.pow (.var 4) 2)))))))))))))))))))))))))))))
theorem dataS_2_0_binding : litSExpr 2 0=dataS_2_0 := rfl

def dataS_2_1 : RingExpr := (.mul (.var 7) (.mul (.var 10) (.mul (.var 8) (.add (.mul (.int 3) (.var 1)) (.add (.mul (.int (-2)) (.mul (.var 5) (.var 1))) (.add (.mul (.int (-6)) (.mul (.var 1) (.mul (.var 2) (.var 4)))) (.add (.mul (.int (-6)) (.mul (.var 3) (.mul (.var 4) (.pow (.var 1) 2)))) (.add (.mul (.int 2) (.mul (.var 5) (.mul (.var 0) (.var 3)))) (.mul (.int 6) (.mul (.var 0) (.mul (.var 1) (.mul (.var 4) (.pow (.var 3) 2)))))))))))))
theorem dataS_2_1_binding : litSExpr 2 1=dataS_2_1 := rfl

def dataS_2_2 : RingExpr := (.mul (.var 7) (.mul (.var 10) (.mul (.var 8) (.add (.int (-3)) (.add (.mul (.int 2) (.var 5)) (.add (.mul (.int 6) (.mul (.var 2) (.var 4))) (.add (.mul (.int (-6)) (.mul (.var 0) (.mul (.var 4) (.pow (.var 3) 2)))) (.mul (.int 6) (.mul (.var 1) (.mul (.var 3) (.var 4)))))))))))
theorem dataS_2_2_binding : litSExpr 2 2=dataS_2_2 := rfl

def dataS_2_8 : RingExpr := (.mul (.var 7) (.mul (.var 9) (.mul (.pow (.var 10) 2) (.mul (.pow (.var 8) 3) (.add (.mul (.int (-3)) (.mul (.var 11) (.var 2))) (.add (.mul (.int (-3)) (.mul (.var 11) (.mul (.var 1) (.var 3)))) (.add (.mul (.int 2) (.mul (.var 11) (.mul (.var 5) (.var 2)))) (.add (.mul (.int 6) (.mul (.var 11) (.mul (.var 3) (.var 4)))) (.add (.mul (.int 6) (.mul (.var 15) (.mul (.var 4) (.pow (.var 3) 2)))) (.add (.mul (.int 12) (.mul (.var 11) (.mul (.pow (.var 2) 3) (.pow (.var 4) 2)))) (.add (.mul (.int (-12)) (.mul (.var 11) (.mul (.var 1) (.mul (.pow (.var 3) 2) (.pow (.var 4) 2))))) (.add (.mul (.int (-12)) (.mul (.var 11) (.mul (.var 2) (.mul (.var 3) (.pow (.var 4) 2))))) (.add (.mul (.int (-12)) (.mul (.var 15) (.mul (.var 1) (.mul (.pow (.var 3) 3) (.pow (.var 4) 2))))) (.add (.mul (.int (-12)) (.mul (.var 15) (.mul (.var 2) (.mul (.pow (.var 3) 2) (.pow (.var 4) 2))))) (.add (.mul (.int (-6)) (.mul (.var 12) (.mul (.var 1) (.mul (.var 4) (.pow (.var 3) 2))))) (.add (.mul (.int (-4)) (.mul (.var 11) (.mul (.var 5) (.mul (.var 3) (.var 4))))) (.add (.mul (.int (-4)) (.mul (.var 15) (.mul (.var 5) (.mul (.var 4) (.pow (.var 3) 2))))) (.add (.mul (.int 2) (.mul (.var 11) (.mul (.var 5) (.mul (.var 1) (.var 3))))) (.add (.mul (.int 4) (.mul (.var 11) (.mul (.var 5) (.mul (.var 4) (.pow (.var 2) 2))))) (.add (.mul (.int 4) (.mul (.var 13) (.mul (.var 0) (.mul (.var 4) (.pow (.var 3) 3))))) (.add (.mul (.int 6) (.mul (.var 11) (.mul (.var 4) (.mul (.pow (.var 1) 2) (.pow (.var 3) 2))))) (.add (.mul (.int 12) (.mul (.var 11) (.mul (.var 0) (.mul (.pow (.var 3) 3) (.pow (.var 4) 2))))) (.add (.mul (.int 12) (.mul (.var 12) (.mul (.pow (.var 1) 2) (.mul (.pow (.var 3) 3) (.pow (.var 4) 2))))) (.add (.mul (.int 12) (.mul (.var 15) (.mul (.var 0) (.mul (.pow (.var 3) 4) (.pow (.var 4) 2))))) (.add (.mul (.int (-12)) (.mul (.var 11) (.mul (.var 0) (.mul (.pow (.var 2) 2) (.mul (.pow (.var 3) 2) (.pow (.var 4) 2)))))) (.add (.mul (.int (-12)) (.mul (.var 12) (.mul (.var 0) (.mul (.var 1) (.mul (.pow (.var 3) 4) (.pow (.var 4) 2)))))) (.add (.mul (.int (-4)) (.mul (.var 12) (.mul (.var 5) (.mul (.var 0) (.mul (.var 4) (.pow (.var 3) 3)))))) (.add (.mul (.int 4) (.mul (.var 12) (.mul (.var 5) (.mul (.var 1) (.mul (.var 4) (.pow (.var 3) 2)))))) (.add (.mul (.int 6) (.mul (.var 11) (.mul (.var 0) (.mul (.var 2) (.mul (.var 4) (.pow (.var 3) 2)))))) (.add (.mul (.int 6) (.mul (.var 11) (.mul (.var 1) (.mul (.var 2) (.mul (.var 3) (.var 4)))))) (.add (.mul (.int 12) (.mul (.var 11) (.mul (.var 2) (.mul (.pow (.var 1) 2) (.mul (.pow (.var 3) 2) (.pow (.var 4) 2)))))) (.add (.mul (.int 12) (.mul (.var 12) (.mul (.var 1) (.mul (.var 2) (.mul (.pow (.var 3) 2) (.pow (.var 4) 2)))))) (.add (.mul (.int 24) (.mul (.var 11) (.mul (.var 1) (.mul (.var 3) (.mul (.pow (.var 2) 2) (.pow (.var 4) 2)))))) (.add (.mul (.int (-12)) (.mul (.var 11) (.mul (.var 0) (.mul (.var 1) (.mul (.var 2) (.mul (.pow (.var 3) 3) (.pow (.var 4) 2))))))) (.add (.mul (.int (-4)) (.mul (.var 11) (.mul (.var 5) (.mul (.var 0) (.mul (.var 2) (.mul (.var 4) (.pow (.var 3) 2))))))) (.mul (.int 4) (.mul (.var 11) (.mul (.var 5) (.mul (.var 1) (.mul (.var 2) (.mul (.var 3) (.var 4))))))))))))))))))))))))))))))))))))))))))
theorem dataS_2_8_binding : litSExpr 2 8=dataS_2_8 := rfl

def dataS_3_0 : RingExpr := (.mul (.var 7) (.mul (.var 9) (.mul (.pow (.var 10) 2) (.mul (.pow (.var 8) 3) (.add (.var 2) (.add (.mul (.var 1) (.var 3)) (.add (.mul (.int (-2)) (.mul (.var 3) (.var 4))) (.add (.mul (.int 4) (.mul (.var 4) (.pow (.var 2) 2))) (.add (.mul (.int 4) (.mul (.pow (.var 2) 3) (.pow (.var 4) 2))) (.add (.mul (.int (-4)) (.mul (.var 0) (.mul (.pow (.var 3) 3) (.pow (.var 4) 2)))) (.add (.mul (.int (-4)) (.mul (.var 2) (.mul (.var 3) (.pow (.var 4) 2)))) (.add (.mul (.int (-4)) (.mul (.var 0) (.mul (.pow (.var 2) 2) (.mul (.pow (.var 3) 2) (.pow (.var 4) 2))))) (.add (.mul (.int (-2)) (.mul (.var 0) (.mul (.var 2) (.mul (.var 4) (.pow (.var 3) 2))))) (.add (.mul (.int 4) (.mul (.var 1) (.mul (.var 2) (.mul (.var 3) (.var 4))))) (.mul (.int 4) (.mul (.var 1) (.mul (.var 3) (.mul (.pow (.var 2) 2) (.pow (.var 4) 2)))))))))))))))))))
theorem dataS_3_0_binding : litSExpr 3 0=dataS_3_0 := rfl

def dataS_3_1 : RingExpr := (.mul (.var 7) (.mul (.var 10) (.mul (.var 8) (.add (.var 1) (.add (.mul (.int 2) (.mul (.var 1) (.mul (.var 2) (.var 4)))) (.mul (.int (-4)) (.mul (.var 0) (.mul (.var 2) (.mul (.var 3) (.var 4))))))))))
theorem dataS_3_1_binding : litSExpr 3 1=dataS_3_1 := rfl

def dataS_3_2 : RingExpr := (.mul (.var 7) (.mul (.var 10) (.mul (.var 8) (.add (.int (-1)) (.add (.mul (.int (-2)) (.mul (.var 2) (.var 4))) (.mul (.int (-2)) (.mul (.var 0) (.mul (.var 4) (.pow (.var 3) 2)))))))))
theorem dataS_3_2_binding : litSExpr 3 2=dataS_3_2 := rfl

def dataS_3_8 : RingExpr := (.mul (.var 7) (.mul (.var 9) (.mul (.pow (.var 10) 2) (.mul (.pow (.var 8) 3) (.add (.mul (.int (-1)) (.mul (.var 11) (.var 2))) (.add (.mul (.int (-1)) (.mul (.var 11) (.mul (.var 1) (.var 3)))) (.add (.mul (.int (-4)) (.mul (.var 11) (.mul (.var 4) (.pow (.var 2) 2)))) (.add (.mul (.int (-4)) (.mul (.var 11) (.mul (.pow (.var 2) 3) (.pow (.var 4) 2)))) (.add (.mul (.int 2) (.mul (.var 11) (.mul (.var 3) (.var 4)))) (.add (.mul (.int 2) (.mul (.var 15) (.mul (.var 4) (.pow (.var 3) 2)))) (.add (.mul (.int (-2)) (.mul (.var 12) (.mul (.var 1) (.mul (.var 4) (.pow (.var 3) 2))))) (.add (.mul (.int 4) (.mul (.var 11) (.mul (.var 0) (.mul (.pow (.var 3) 3) (.pow (.var 4) 2))))) (.add (.mul (.int 4) (.mul (.var 11) (.mul (.var 2) (.mul (.var 3) (.pow (.var 4) 2))))) (.add (.mul (.int 4) (.mul (.var 14) (.mul (.var 0) (.mul (.var 4) (.pow (.var 3) 3))))) (.add (.mul (.int 4) (.mul (.var 15) (.mul (.var 0) (.mul (.pow (.var 3) 4) (.pow (.var 4) 2))))) (.add (.mul (.int 4) (.mul (.var 15) (.mul (.var 2) (.mul (.pow (.var 3) 2) (.pow (.var 4) 2))))) (.add (.mul (.int (-4)) (.mul (.var 11) (.mul (.var 1) (.mul (.var 2) (.mul (.var 3) (.var 4)))))) (.add (.mul (.int (-4)) (.mul (.var 11) (.mul (.var 1) (.mul (.var 3) (.mul (.pow (.var 2) 2) (.pow (.var 4) 2)))))) (.add (.mul (.int (-4)) (.mul (.var 12) (.mul (.var 1) (.mul (.var 2) (.mul (.pow (.var 3) 2) (.pow (.var 4) 2)))))) (.add (.mul (.int 2) (.mul (.var 11) (.mul (.var 0) (.mul (.var 2) (.mul (.var 4) (.pow (.var 3) 2)))))) (.add (.mul (.int 4) (.mul (.var 11) (.mul (.var 0) (.mul (.pow (.var 2) 2) (.mul (.pow (.var 3) 2) (.pow (.var 4) 2)))))) (.mul (.int 8) (.mul (.var 12) (.mul (.var 0) (.mul (.var 2) (.mul (.pow (.var 3) 3) (.pow (.var 4) 2)))))))))))))))))))))))))))
theorem dataS_3_8_binding : litSExpr 3 8=dataS_3_8 := rfl

def dataS_4_2 : RingExpr := (.int 1)
theorem dataS_4_2_binding : litSExpr 4 2=dataS_4_2 := rfl

def dataS_5_0 : RingExpr := (.mul (.var 7) (.mul (.var 9) (.mul (.pow (.var 10) 2) (.mul (.pow (.var 8) 4) (.add (.mul (.int (-1)) (.pow (.var 2) 2)) (.add (.mul (.int (-4)) (.mul (.var 4) (.pow (.var 2) 3))) (.add (.mul (.int (-4)) (.mul (.pow (.var 2) 4) (.pow (.var 4) 2))) (.add (.mul (.int (-4)) (.mul (.pow (.var 3) 2) (.pow (.var 4) 2))) (.add (.mul (.int (-1)) (.mul (.var 1) (.mul (.var 2) (.var 3)))) (.add (.mul (.int 2) (.mul (.var 0) (.mul (.var 4) (.pow (.var 3) 3)))) (.add (.mul (.int 2) (.mul (.var 1) (.mul (.var 4) (.pow (.var 3) 2)))) (.add (.mul (.int 4) (.mul (.var 2) (.mul (.var 3) (.var 4)))) (.add (.mul (.int 8) (.mul (.var 3) (.mul (.pow (.var 2) 2) (.pow (.var 4) 2)))) (.add (.mul (.int (-4)) (.mul (.var 1) (.mul (.var 3) (.mul (.var 4) (.pow (.var 2) 2))))) (.add (.mul (.int (-4)) (.mul (.var 1) (.mul (.var 3) (.mul (.pow (.var 2) 3) (.pow (.var 4) 2))))) (.add (.mul (.int 2) (.mul (.var 0) (.mul (.var 4) (.mul (.pow (.var 2) 2) (.pow (.var 3) 2))))) (.add (.mul (.int 4) (.mul (.var 0) (.mul (.pow (.var 2) 3) (.mul (.pow (.var 3) 2) (.pow (.var 4) 2))))) (.mul (.int 4) (.mul (.var 1) (.mul (.var 2) (.mul (.pow (.var 3) 2) (.pow (.var 4) 2))))))))))))))))))))))
theorem dataS_5_0_binding : litSExpr 5 0=dataS_5_0 := rfl

def dataS_5_1 : RingExpr := (.mul (.var 7) (.mul (.var 10) (.mul (.pow (.var 8) 2) (.add (.mul (.int (-1)) (.mul (.var 1) (.var 2))) (.add (.mul (.int (-2)) (.mul (.var 0) (.mul (.var 4) (.pow (.var 3) 2)))) (.add (.mul (.int (-2)) (.mul (.var 1) (.mul (.var 4) (.pow (.var 2) 2)))) (.add (.mul (.int 2) (.mul (.var 0) (.mul (.var 2) (.var 3)))) (.add (.mul (.int 2) (.mul (.var 1) (.mul (.var 3) (.var 4)))) (.mul (.int 4) (.mul (.var 0) (.mul (.var 3) (.mul (.var 4) (.pow (.var 2) 2)))))))))))))
theorem dataS_5_1_binding : litSExpr 5 1=dataS_5_1 := rfl

def dataS_5_2 : RingExpr := (.mul (.var 7) (.mul (.var 10) (.mul (.pow (.var 8) 2) (.add (.var 2) (.add (.mul (.int (-2)) (.mul (.var 3) (.var 4))) (.add (.mul (.int 2) (.mul (.var 0) (.pow (.var 3) 2))) (.add (.mul (.int 2) (.mul (.var 4) (.pow (.var 2) 2))) (.mul (.int 2) (.mul (.var 0) (.mul (.var 2) (.mul (.var 4) (.pow (.var 3) 2))))))))))))
theorem dataS_5_2_binding : litSExpr 5 2=dataS_5_2 := rfl

def dataS_5_8 : RingExpr := (.mul (.var 7) (.mul (.var 9) (.mul (.pow (.var 10) 2) (.mul (.pow (.var 8) 4) (.add (.mul (.var 11) (.pow (.var 2) 2)) (.add (.mul (.int 4) (.mul (.var 11) (.mul (.var 4) (.pow (.var 2) 3)))) (.add (.mul (.int 4) (.mul (.var 11) (.mul (.pow (.var 2) 4) (.pow (.var 4) 2)))) (.add (.mul (.int 4) (.mul (.var 11) (.mul (.pow (.var 3) 2) (.pow (.var 4) 2)))) (.add (.mul (.int 4) (.mul (.var 15) (.mul (.pow (.var 3) 3) (.pow (.var 4) 2)))) (.add (.mul (.var 11) (.mul (.var 1) (.mul (.var 2) (.var 3)))) (.add (.mul (.int (-8)) (.mul (.var 11) (.mul (.var 3) (.mul (.pow (.var 2) 2) (.pow (.var 4) 2))))) (.add (.mul (.int (-4)) (.mul (.var 11) (.mul (.var 2) (.mul (.var 3) (.var 4))))) (.add (.mul (.int (-4)) (.mul (.var 12) (.mul (.var 1) (.mul (.pow (.var 3) 3) (.pow (.var 4) 2))))) (.add (.mul (.int (-4)) (.mul (.var 15) (.mul (.var 0) (.mul (.var 4) (.pow (.var 3) 4))))) (.add (.mul (.int (-4)) (.mul (.var 15) (.mul (.pow (.var 2) 2) (.mul (.pow (.var 3) 2) (.pow (.var 4) 2))))) (.add (.mul (.int (-2)) (.mul (.var 11) (.mul (.var 0) (.mul (.var 4) (.pow (.var 3) 3))))) (.add (.mul (.int (-2)) (.mul (.var 11) (.mul (.var 1) (.mul (.var 4) (.pow (.var 3) 2))))) (.add (.mul (.int (-2)) (.mul (.var 15) (.mul (.var 2) (.mul (.var 4) (.pow (.var 3) 2))))) (.add (.mul (.int 4) (.mul (.var 12) (.mul (.var 0) (.mul (.pow (.var 3) 4) (.pow (.var 4) 2))))) (.add (.mul (.int 4) (.mul (.var 16) (.mul (.var 0) (.mul (.var 4) (.pow (.var 3) 4))))) (.add (.mul (.int (-8)) (.mul (.var 12) (.mul (.var 0) (.mul (.pow (.var 2) 2) (.mul (.pow (.var 3) 3) (.pow (.var 4) 2)))))) (.add (.mul (.int (-4)) (.mul (.var 11) (.mul (.var 0) (.mul (.pow (.var 2) 3) (.mul (.pow (.var 3) 2) (.pow (.var 4) 2)))))) (.add (.mul (.int (-4)) (.mul (.var 11) (.mul (.var 1) (.mul (.var 2) (.mul (.pow (.var 3) 2) (.pow (.var 4) 2)))))) (.add (.mul (.int (-4)) (.mul (.var 12) (.mul (.var 0) (.mul (.var 2) (.mul (.var 4) (.pow (.var 3) 3)))))) (.add (.mul (.int (-4)) (.mul (.var 15) (.mul (.var 0) (.mul (.var 2) (.mul (.pow (.var 3) 4) (.pow (.var 4) 2)))))) (.add (.mul (.int (-2)) (.mul (.var 11) (.mul (.var 0) (.mul (.var 4) (.mul (.pow (.var 2) 2) (.pow (.var 3) 2)))))) (.add (.mul (.int 2) (.mul (.var 12) (.mul (.var 1) (.mul (.var 2) (.mul (.var 4) (.pow (.var 3) 2)))))) (.add (.mul (.int 4) (.mul (.var 11) (.mul (.var 1) (.mul (.var 3) (.mul (.var 4) (.pow (.var 2) 2)))))) (.add (.mul (.int 4) (.mul (.var 11) (.mul (.var 1) (.mul (.var 3) (.mul (.pow (.var 2) 3) (.pow (.var 4) 2)))))) (.mul (.int 4) (.mul (.var 12) (.mul (.var 1) (.mul (.pow (.var 2) 2) (.mul (.pow (.var 3) 2) (.pow (.var 4) 2)))))))))))))))))))))))))))))))))))
theorem dataS_5_8_binding : litSExpr 5 8=dataS_5_8 := rfl

def dataS_6_3 : RingExpr := (.int 1)
theorem dataS_6_3_binding : litSExpr 6 3=dataS_6_3 := rfl

def dataS_7_4 : RingExpr := (.int 1)
theorem dataS_7_4_binding : litSExpr 7 4=dataS_7_4 := rfl

def dataS_8_3 : RingExpr := (.mul (.var 7) (.mul (.var 9) (.mul (.pow (.var 10) 2) (.mul (.pow (.var 8) 3) (.add (.mul (.int 3) (.var 2)) (.add (.mul (.int (-12)) (.mul (.pow (.var 2) 3) (.pow (.var 4) 2))) (.add (.mul (.int (-6)) (.mul (.var 3) (.var 4))) (.add (.mul (.int (-2)) (.mul (.var 5) (.var 2))) (.add (.mul (.int 3) (.mul (.var 1) (.var 3))) (.add (.mul (.int (-12)) (.mul (.var 0) (.mul (.pow (.var 3) 3) (.pow (.var 4) 2)))) (.add (.mul (.int (-6)) (.mul (.var 4) (.mul (.pow (.var 1) 2) (.pow (.var 3) 2)))) (.add (.mul (.int (-4)) (.mul (.var 5) (.mul (.var 4) (.pow (.var 2) 2)))) (.add (.mul (.int (-2)) (.mul (.var 5) (.mul (.var 1) (.var 3)))) (.add (.mul (.int 4) (.mul (.var 5) (.mul (.var 3) (.var 4)))) (.add (.mul (.int 12) (.mul (.var 1) (.mul (.pow (.var 3) 2) (.pow (.var 4) 2)))) (.add (.mul (.int 12) (.mul (.var 2) (.mul (.var 3) (.pow (.var 4) 2)))) (.add (.mul (.int (-24)) (.mul (.var 1) (.mul (.var 3) (.mul (.pow (.var 2) 2) (.pow (.var 4) 2))))) (.add (.mul (.int (-12)) (.mul (.var 2) (.mul (.pow (.var 1) 2) (.mul (.pow (.var 3) 2) (.pow (.var 4) 2))))) (.add (.mul (.int (-6)) (.mul (.var 0) (.mul (.var 2) (.mul (.var 4) (.pow (.var 3) 2))))) (.add (.mul (.int (-6)) (.mul (.var 1) (.mul (.var 2) (.mul (.var 3) (.var 4))))) (.add (.mul (.int 12) (.mul (.var 0) (.mul (.pow (.var 2) 2) (.mul (.pow (.var 3) 2) (.pow (.var 4) 2))))) (.add (.mul (.int (-4)) (.mul (.var 5) (.mul (.var 1) (.mul (.var 2) (.mul (.var 3) (.var 4)))))) (.add (.mul (.int 4) (.mul (.var 5) (.mul (.var 0) (.mul (.var 2) (.mul (.var 4) (.pow (.var 3) 2)))))) (.mul (.int 12) (.mul (.var 0) (.mul (.var 1) (.mul (.var 2) (.mul (.pow (.var 3) 3) (.pow (.var 4) 2)))))))))))))))))))))))))))))
theorem dataS_8_3_binding : litSExpr 8 3=dataS_8_3 := rfl

def dataS_8_4 : RingExpr := (.mul (.var 7) (.mul (.var 10) (.mul (.var 8) (.add (.mul (.int 3) (.var 1)) (.add (.mul (.int (-2)) (.mul (.var 5) (.var 1))) (.add (.mul (.int (-6)) (.mul (.var 1) (.mul (.var 2) (.var 4)))) (.add (.mul (.int (-6)) (.mul (.var 3) (.mul (.var 4) (.pow (.var 1) 2)))) (.add (.mul (.int 2) (.mul (.var 5) (.mul (.var 0) (.var 3)))) (.mul (.int 6) (.mul (.var 0) (.mul (.var 1) (.mul (.var 4) (.pow (.var 3) 2)))))))))))))
theorem dataS_8_4_binding : litSExpr 8 4=dataS_8_4 := rfl

def dataS_8_5 : RingExpr := (.mul (.var 7) (.mul (.var 10) (.mul (.var 8) (.add (.int (-3)) (.add (.mul (.int 2) (.var 5)) (.add (.mul (.int 6) (.mul (.var 2) (.var 4))) (.add (.mul (.int (-6)) (.mul (.var 0) (.mul (.var 4) (.pow (.var 3) 2)))) (.mul (.int 6) (.mul (.var 1) (.mul (.var 3) (.var 4)))))))))))
theorem dataS_8_5_binding : litSExpr 8 5=dataS_8_5 := rfl

def dataS_8_8 : RingExpr := (.mul (.var 7) (.mul (.var 9) (.mul (.pow (.var 10) 2) (.mul (.pow (.var 8) 3) (.add (.mul (.int (-3)) (.mul (.var 11) (.var 2))) (.add (.mul (.int (-3)) (.mul (.var 11) (.mul (.var 1) (.var 3)))) (.add (.mul (.int 2) (.mul (.var 11) (.mul (.var 5) (.var 2)))) (.add (.mul (.int 6) (.mul (.var 11) (.mul (.var 3) (.var 4)))) (.add (.mul (.int 6) (.mul (.var 15) (.mul (.var 4) (.pow (.var 3) 2)))) (.add (.mul (.int 12) (.mul (.var 11) (.mul (.pow (.var 2) 3) (.pow (.var 4) 2)))) (.add (.mul (.int (-12)) (.mul (.var 11) (.mul (.var 1) (.mul (.pow (.var 3) 2) (.pow (.var 4) 2))))) (.add (.mul (.int (-12)) (.mul (.var 11) (.mul (.var 2) (.mul (.var 3) (.pow (.var 4) 2))))) (.add (.mul (.int (-12)) (.mul (.var 15) (.mul (.var 1) (.mul (.pow (.var 3) 3) (.pow (.var 4) 2))))) (.add (.mul (.int (-12)) (.mul (.var 15) (.mul (.var 2) (.mul (.pow (.var 3) 2) (.pow (.var 4) 2))))) (.add (.mul (.int (-6)) (.mul (.var 12) (.mul (.var 1) (.mul (.var 4) (.pow (.var 3) 2))))) (.add (.mul (.int (-4)) (.mul (.var 11) (.mul (.var 5) (.mul (.var 3) (.var 4))))) (.add (.mul (.int (-4)) (.mul (.var 15) (.mul (.var 5) (.mul (.var 4) (.pow (.var 3) 2))))) (.add (.mul (.int 2) (.mul (.var 11) (.mul (.var 5) (.mul (.var 1) (.var 3))))) (.add (.mul (.int 4) (.mul (.var 11) (.mul (.var 5) (.mul (.var 4) (.pow (.var 2) 2))))) (.add (.mul (.int 4) (.mul (.var 13) (.mul (.var 0) (.mul (.var 4) (.pow (.var 3) 3))))) (.add (.mul (.int 6) (.mul (.var 11) (.mul (.var 4) (.mul (.pow (.var 1) 2) (.pow (.var 3) 2))))) (.add (.mul (.int 12) (.mul (.var 11) (.mul (.var 0) (.mul (.pow (.var 3) 3) (.pow (.var 4) 2))))) (.add (.mul (.int 12) (.mul (.var 12) (.mul (.pow (.var 1) 2) (.mul (.pow (.var 3) 3) (.pow (.var 4) 2))))) (.add (.mul (.int 12) (.mul (.var 15) (.mul (.var 0) (.mul (.pow (.var 3) 4) (.pow (.var 4) 2))))) (.add (.mul (.int (-12)) (.mul (.var 11) (.mul (.var 0) (.mul (.pow (.var 2) 2) (.mul (.pow (.var 3) 2) (.pow (.var 4) 2)))))) (.add (.mul (.int (-12)) (.mul (.var 12) (.mul (.var 0) (.mul (.var 1) (.mul (.pow (.var 3) 4) (.pow (.var 4) 2)))))) (.add (.mul (.int (-4)) (.mul (.var 12) (.mul (.var 5) (.mul (.var 0) (.mul (.var 4) (.pow (.var 3) 3)))))) (.add (.mul (.int 4) (.mul (.var 12) (.mul (.var 5) (.mul (.var 1) (.mul (.var 4) (.pow (.var 3) 2)))))) (.add (.mul (.int 6) (.mul (.var 11) (.mul (.var 0) (.mul (.var 2) (.mul (.var 4) (.pow (.var 3) 2)))))) (.add (.mul (.int 6) (.mul (.var 11) (.mul (.var 1) (.mul (.var 2) (.mul (.var 3) (.var 4)))))) (.add (.mul (.int 12) (.mul (.var 11) (.mul (.var 2) (.mul (.pow (.var 1) 2) (.mul (.pow (.var 3) 2) (.pow (.var 4) 2)))))) (.add (.mul (.int 12) (.mul (.var 12) (.mul (.var 1) (.mul (.var 2) (.mul (.pow (.var 3) 2) (.pow (.var 4) 2)))))) (.add (.mul (.int 24) (.mul (.var 11) (.mul (.var 1) (.mul (.var 3) (.mul (.pow (.var 2) 2) (.pow (.var 4) 2)))))) (.add (.mul (.int (-12)) (.mul (.var 11) (.mul (.var 0) (.mul (.var 1) (.mul (.var 2) (.mul (.pow (.var 3) 3) (.pow (.var 4) 2))))))) (.add (.mul (.int (-4)) (.mul (.var 11) (.mul (.var 5) (.mul (.var 0) (.mul (.var 2) (.mul (.var 4) (.pow (.var 3) 2))))))) (.mul (.int 4) (.mul (.var 11) (.mul (.var 5) (.mul (.var 1) (.mul (.var 2) (.mul (.var 3) (.var 4))))))))))))))))))))))))))))))))))))))))))
theorem dataS_8_8_binding : litSExpr 8 8=dataS_8_8 := rfl

def dataS_9_3 : RingExpr := (.mul (.var 7) (.mul (.var 9) (.mul (.pow (.var 10) 2) (.mul (.pow (.var 8) 3) (.add (.var 2) (.add (.mul (.var 1) (.var 3)) (.add (.mul (.int (-2)) (.mul (.var 3) (.var 4))) (.add (.mul (.int 4) (.mul (.var 4) (.pow (.var 2) 2))) (.add (.mul (.int 4) (.mul (.pow (.var 2) 3) (.pow (.var 4) 2))) (.add (.mul (.int (-4)) (.mul (.var 0) (.mul (.pow (.var 3) 3) (.pow (.var 4) 2)))) (.add (.mul (.int (-4)) (.mul (.var 2) (.mul (.var 3) (.pow (.var 4) 2)))) (.add (.mul (.int (-4)) (.mul (.var 0) (.mul (.pow (.var 2) 2) (.mul (.pow (.var 3) 2) (.pow (.var 4) 2))))) (.add (.mul (.int (-2)) (.mul (.var 0) (.mul (.var 2) (.mul (.var 4) (.pow (.var 3) 2))))) (.add (.mul (.int 4) (.mul (.var 1) (.mul (.var 2) (.mul (.var 3) (.var 4))))) (.mul (.int 4) (.mul (.var 1) (.mul (.var 3) (.mul (.pow (.var 2) 2) (.pow (.var 4) 2)))))))))))))))))))
theorem dataS_9_3_binding : litSExpr 9 3=dataS_9_3 := rfl

def dataS_9_4 : RingExpr := (.mul (.var 7) (.mul (.var 10) (.mul (.var 8) (.add (.var 1) (.add (.mul (.int 2) (.mul (.var 1) (.mul (.var 2) (.var 4)))) (.mul (.int (-4)) (.mul (.var 0) (.mul (.var 2) (.mul (.var 3) (.var 4))))))))))
theorem dataS_9_4_binding : litSExpr 9 4=dataS_9_4 := rfl

def dataS_9_5 : RingExpr := (.mul (.var 7) (.mul (.var 10) (.mul (.var 8) (.add (.int (-1)) (.add (.mul (.int (-2)) (.mul (.var 2) (.var 4))) (.mul (.int (-2)) (.mul (.var 0) (.mul (.var 4) (.pow (.var 3) 2)))))))))
theorem dataS_9_5_binding : litSExpr 9 5=dataS_9_5 := rfl

def dataS_9_8 : RingExpr := (.mul (.var 7) (.mul (.var 9) (.mul (.pow (.var 10) 2) (.mul (.pow (.var 8) 3) (.add (.mul (.int (-1)) (.mul (.var 11) (.var 2))) (.add (.mul (.int (-1)) (.mul (.var 11) (.mul (.var 1) (.var 3)))) (.add (.mul (.int (-4)) (.mul (.var 11) (.mul (.var 4) (.pow (.var 2) 2)))) (.add (.mul (.int (-4)) (.mul (.var 11) (.mul (.pow (.var 2) 3) (.pow (.var 4) 2)))) (.add (.mul (.int 2) (.mul (.var 11) (.mul (.var 3) (.var 4)))) (.add (.mul (.int 2) (.mul (.var 15) (.mul (.var 4) (.pow (.var 3) 2)))) (.add (.mul (.int (-2)) (.mul (.var 12) (.mul (.var 1) (.mul (.var 4) (.pow (.var 3) 2))))) (.add (.mul (.int 4) (.mul (.var 11) (.mul (.var 0) (.mul (.pow (.var 3) 3) (.pow (.var 4) 2))))) (.add (.mul (.int 4) (.mul (.var 11) (.mul (.var 2) (.mul (.var 3) (.pow (.var 4) 2))))) (.add (.mul (.int 4) (.mul (.var 14) (.mul (.var 0) (.mul (.var 4) (.pow (.var 3) 3))))) (.add (.mul (.int 4) (.mul (.var 15) (.mul (.var 0) (.mul (.pow (.var 3) 4) (.pow (.var 4) 2))))) (.add (.mul (.int 4) (.mul (.var 15) (.mul (.var 2) (.mul (.pow (.var 3) 2) (.pow (.var 4) 2))))) (.add (.mul (.int (-4)) (.mul (.var 11) (.mul (.var 1) (.mul (.var 2) (.mul (.var 3) (.var 4)))))) (.add (.mul (.int (-4)) (.mul (.var 11) (.mul (.var 1) (.mul (.var 3) (.mul (.pow (.var 2) 2) (.pow (.var 4) 2)))))) (.add (.mul (.int (-4)) (.mul (.var 12) (.mul (.var 1) (.mul (.var 2) (.mul (.pow (.var 3) 2) (.pow (.var 4) 2)))))) (.add (.mul (.int 2) (.mul (.var 11) (.mul (.var 0) (.mul (.var 2) (.mul (.var 4) (.pow (.var 3) 2)))))) (.add (.mul (.int 4) (.mul (.var 11) (.mul (.var 0) (.mul (.pow (.var 2) 2) (.mul (.pow (.var 3) 2) (.pow (.var 4) 2)))))) (.mul (.int 8) (.mul (.var 12) (.mul (.var 0) (.mul (.var 2) (.mul (.pow (.var 3) 3) (.pow (.var 4) 2)))))))))))))))))))))))))))
theorem dataS_9_8_binding : litSExpr 9 8=dataS_9_8 := rfl

def dataS_10_5 : RingExpr := (.int 1)
theorem dataS_10_5_binding : litSExpr 10 5=dataS_10_5 := rfl

def dataS_11_3 : RingExpr := (.mul (.var 7) (.mul (.var 9) (.mul (.pow (.var 10) 2) (.mul (.pow (.var 8) 4) (.add (.mul (.int (-1)) (.pow (.var 2) 2)) (.add (.mul (.int (-4)) (.mul (.var 4) (.pow (.var 2) 3))) (.add (.mul (.int (-4)) (.mul (.pow (.var 2) 4) (.pow (.var 4) 2))) (.add (.mul (.int (-4)) (.mul (.pow (.var 3) 2) (.pow (.var 4) 2))) (.add (.mul (.int (-1)) (.mul (.var 1) (.mul (.var 2) (.var 3)))) (.add (.mul (.int 2) (.mul (.var 0) (.mul (.var 4) (.pow (.var 3) 3)))) (.add (.mul (.int 2) (.mul (.var 1) (.mul (.var 4) (.pow (.var 3) 2)))) (.add (.mul (.int 4) (.mul (.var 2) (.mul (.var 3) (.var 4)))) (.add (.mul (.int 8) (.mul (.var 3) (.mul (.pow (.var 2) 2) (.pow (.var 4) 2)))) (.add (.mul (.int (-4)) (.mul (.var 1) (.mul (.var 3) (.mul (.var 4) (.pow (.var 2) 2))))) (.add (.mul (.int (-4)) (.mul (.var 1) (.mul (.var 3) (.mul (.pow (.var 2) 3) (.pow (.var 4) 2))))) (.add (.mul (.int 2) (.mul (.var 0) (.mul (.var 4) (.mul (.pow (.var 2) 2) (.pow (.var 3) 2))))) (.add (.mul (.int 4) (.mul (.var 0) (.mul (.pow (.var 2) 3) (.mul (.pow (.var 3) 2) (.pow (.var 4) 2))))) (.mul (.int 4) (.mul (.var 1) (.mul (.var 2) (.mul (.pow (.var 3) 2) (.pow (.var 4) 2))))))))))))))))))))))
theorem dataS_11_3_binding : litSExpr 11 3=dataS_11_3 := rfl

def dataS_11_4 : RingExpr := (.mul (.var 7) (.mul (.var 10) (.mul (.pow (.var 8) 2) (.add (.mul (.int (-1)) (.mul (.var 1) (.var 2))) (.add (.mul (.int (-2)) (.mul (.var 0) (.mul (.var 4) (.pow (.var 3) 2)))) (.add (.mul (.int (-2)) (.mul (.var 1) (.mul (.var 4) (.pow (.var 2) 2)))) (.add (.mul (.int 2) (.mul (.var 0) (.mul (.var 2) (.var 3)))) (.add (.mul (.int 2) (.mul (.var 1) (.mul (.var 3) (.var 4)))) (.mul (.int 4) (.mul (.var 0) (.mul (.var 3) (.mul (.var 4) (.pow (.var 2) 2)))))))))))))
theorem dataS_11_4_binding : litSExpr 11 4=dataS_11_4 := rfl

def dataS_11_5 : RingExpr := (.mul (.var 7) (.mul (.var 10) (.mul (.pow (.var 8) 2) (.add (.var 2) (.add (.mul (.int (-2)) (.mul (.var 3) (.var 4))) (.add (.mul (.int 2) (.mul (.var 0) (.pow (.var 3) 2))) (.add (.mul (.int 2) (.mul (.var 4) (.pow (.var 2) 2))) (.mul (.int 2) (.mul (.var 0) (.mul (.var 2) (.mul (.var 4) (.pow (.var 3) 2))))))))))))
theorem dataS_11_5_binding : litSExpr 11 5=dataS_11_5 := rfl

def dataS_11_8 : RingExpr := (.mul (.var 7) (.mul (.var 9) (.mul (.pow (.var 10) 2) (.mul (.pow (.var 8) 4) (.add (.mul (.var 11) (.pow (.var 2) 2)) (.add (.mul (.int 4) (.mul (.var 11) (.mul (.var 4) (.pow (.var 2) 3)))) (.add (.mul (.int 4) (.mul (.var 11) (.mul (.pow (.var 2) 4) (.pow (.var 4) 2)))) (.add (.mul (.int 4) (.mul (.var 11) (.mul (.pow (.var 3) 2) (.pow (.var 4) 2)))) (.add (.mul (.int 4) (.mul (.var 15) (.mul (.pow (.var 3) 3) (.pow (.var 4) 2)))) (.add (.mul (.var 11) (.mul (.var 1) (.mul (.var 2) (.var 3)))) (.add (.mul (.int (-8)) (.mul (.var 11) (.mul (.var 3) (.mul (.pow (.var 2) 2) (.pow (.var 4) 2))))) (.add (.mul (.int (-4)) (.mul (.var 11) (.mul (.var 2) (.mul (.var 3) (.var 4))))) (.add (.mul (.int (-4)) (.mul (.var 12) (.mul (.var 1) (.mul (.pow (.var 3) 3) (.pow (.var 4) 2))))) (.add (.mul (.int (-4)) (.mul (.var 15) (.mul (.var 0) (.mul (.var 4) (.pow (.var 3) 4))))) (.add (.mul (.int (-4)) (.mul (.var 15) (.mul (.pow (.var 2) 2) (.mul (.pow (.var 3) 2) (.pow (.var 4) 2))))) (.add (.mul (.int (-2)) (.mul (.var 11) (.mul (.var 0) (.mul (.var 4) (.pow (.var 3) 3))))) (.add (.mul (.int (-2)) (.mul (.var 11) (.mul (.var 1) (.mul (.var 4) (.pow (.var 3) 2))))) (.add (.mul (.int (-2)) (.mul (.var 15) (.mul (.var 2) (.mul (.var 4) (.pow (.var 3) 2))))) (.add (.mul (.int 4) (.mul (.var 12) (.mul (.var 0) (.mul (.pow (.var 3) 4) (.pow (.var 4) 2))))) (.add (.mul (.int 4) (.mul (.var 16) (.mul (.var 0) (.mul (.var 4) (.pow (.var 3) 4))))) (.add (.mul (.int (-8)) (.mul (.var 12) (.mul (.var 0) (.mul (.pow (.var 2) 2) (.mul (.pow (.var 3) 3) (.pow (.var 4) 2)))))) (.add (.mul (.int (-4)) (.mul (.var 11) (.mul (.var 0) (.mul (.pow (.var 2) 3) (.mul (.pow (.var 3) 2) (.pow (.var 4) 2)))))) (.add (.mul (.int (-4)) (.mul (.var 11) (.mul (.var 1) (.mul (.var 2) (.mul (.pow (.var 3) 2) (.pow (.var 4) 2)))))) (.add (.mul (.int (-4)) (.mul (.var 12) (.mul (.var 0) (.mul (.var 2) (.mul (.var 4) (.pow (.var 3) 3)))))) (.add (.mul (.int (-4)) (.mul (.var 15) (.mul (.var 0) (.mul (.var 2) (.mul (.pow (.var 3) 4) (.pow (.var 4) 2)))))) (.add (.mul (.int (-2)) (.mul (.var 11) (.mul (.var 0) (.mul (.var 4) (.mul (.pow (.var 2) 2) (.pow (.var 3) 2)))))) (.add (.mul (.int 2) (.mul (.var 12) (.mul (.var 1) (.mul (.var 2) (.mul (.var 4) (.pow (.var 3) 2)))))) (.add (.mul (.int 4) (.mul (.var 11) (.mul (.var 1) (.mul (.var 3) (.mul (.var 4) (.pow (.var 2) 2)))))) (.add (.mul (.int 4) (.mul (.var 11) (.mul (.var 1) (.mul (.var 3) (.mul (.pow (.var 2) 3) (.pow (.var 4) 2)))))) (.mul (.int 4) (.mul (.var 12) (.mul (.var 1) (.mul (.pow (.var 2) 2) (.mul (.pow (.var 3) 2) (.pow (.var 4) 2)))))))))))))))))))))))))))))))))))
theorem dataS_11_8_binding : litSExpr 11 8=dataS_11_8 := rfl

def dataS_12_6 : RingExpr := (.int 1)
theorem dataS_12_6_binding : litSExpr 12 6=dataS_12_6 := rfl

def dataS_13_7 : RingExpr := (.int 1)
theorem dataS_13_7_binding : litSExpr 13 7=dataS_13_7 := rfl

def dataS_14_6 : RingExpr := (.mul (.var 10) (.mul (.var 8) (.add (.mul (.int (-3)) (.var 2)) (.add (.mul (.int (-6)) (.mul (.var 4) (.pow (.var 2) 2))) (.add (.mul (.int (-3)) (.mul (.var 1) (.var 3))) (.add (.mul (.int (-6)) (.mul (.var 1) (.mul (.var 2) (.mul (.var 3) (.var 4))))) (.mul (.int 6) (.mul (.var 0) (.mul (.var 2) (.mul (.var 4) (.pow (.var 3) 2)))))))))))
theorem dataS_14_6_binding : litSExpr 14 6=dataS_14_6 := rfl

def dataS_14_7 : RingExpr := (.add (.mul (.int (3)) (.pow (.var 10) 1)) (.add (.mul (.int (-3)) (.mul (.var 2) (.var 4))) (.add (.mul (.int (-3)) (.mul (.var 1) (.mul (.var 3) (.var 4)))) (.mul (.int 3) (.mul (.var 0) (.mul (.var 4) (.pow (.var 3) 2)))))))
theorem dataS_14_7_binding : litSExpr 14 7=dataS_14_7 := rfl

def dataS_15_6 : RingExpr := (.mul (.var 10) (.mul (.var 8) (.add (.mul (.int (-1)) (.var 2)) (.add (.mul (.int (-1)) (.mul (.var 1) (.var 3))) (.add (.mul (.int (-2)) (.mul (.var 4) (.pow (.var 2) 2))) (.add (.mul (.int (-2)) (.mul (.var 1) (.mul (.var 2) (.mul (.var 3) (.var 4))))) (.mul (.int 2) (.mul (.var 0) (.mul (.var 2) (.mul (.var 4) (.pow (.var 3) 2)))))))))))
theorem dataS_15_6_binding : litSExpr 15 6=dataS_15_6 := rfl

def dataS_15_7 : RingExpr := (.add (.mul (.int (1)) (.pow (.var 10) 1)) (.add (.mul (.int (-1)) (.mul (.var 2) (.var 4))) (.add (.mul (.var 0) (.mul (.var 4) (.pow (.var 3) 2))) (.mul (.int (-1)) (.mul (.var 1) (.mul (.var 3) (.var 4)))))))
theorem dataS_15_7_binding : litSExpr 15 7=dataS_15_7 := rfl

def dataS_16_6 : RingExpr := (.mul (.var 10) (.mul (.var 9) (.mul (.pow (.var 8) 2) (.add (.var 2) (.add (.mul (.var 1) (.var 3)) (.add (.mul (.int (-2)) (.mul (.var 3) (.var 4))) (.add (.mul (.int 2) (.mul (.var 4) (.pow (.var 2) 2))) (.add (.mul (.int (-2)) (.mul (.var 0) (.mul (.var 2) (.mul (.var 4) (.pow (.var 3) 2))))) (.mul (.int 2) (.mul (.var 1) (.mul (.var 2) (.mul (.var 3) (.var 4)))))))))))))
theorem dataS_16_6_binding : litSExpr 16 6=dataS_16_6 := rfl

def dataS_16_7 : RingExpr := (.add (.var 1) (.mul (.int (-1)) (.mul (.var 0) (.var 3))))
theorem dataS_16_7_binding : litSExpr 16 7=dataS_16_7 := rfl

def dataS_17_6 : RingExpr := (.mul (.var 10) (.mul (.var 9) (.mul (.pow (.var 8) 2) (.add (.var 2) (.add (.mul (.var 1) (.var 3)) (.add (.mul (.int (-1)) (.mul (.var 3) (.var 4))) (.add (.mul (.int 2) (.mul (.pow (.var 2) 3) (.pow (.var 4) 2))) (.add (.mul (.int 3) (.mul (.var 4) (.pow (.var 2) 2))) (.add (.mul (.int (-2)) (.mul (.var 0) (.mul (.var 2) (.mul (.var 4) (.pow (.var 3) 2))))) (.add (.mul (.int (-2)) (.mul (.var 0) (.mul (.pow (.var 2) 2) (.mul (.pow (.var 3) 2) (.pow (.var 4) 2))))) (.add (.mul (.int 2) (.mul (.var 1) (.mul (.var 3) (.mul (.pow (.var 2) 2) (.pow (.var 4) 2))))) (.mul (.int 3) (.mul (.var 1) (.mul (.var 2) (.mul (.var 3) (.var 4))))))))))))))))
theorem dataS_17_6_binding : litSExpr 17 6=dataS_17_6 := rfl

def dataS_17_7 : RingExpr := (.mul (.var 10) (.mul (.var 8) (.add (.var 2) (.add (.mul (.int (-2)) (.mul (.var 0) (.pow (.var 3) 2))) (.add (.mul (.int 2) (.mul (.var 1) (.var 3))) (.add (.mul (.int 2) (.mul (.var 4) (.pow (.var 2) 2))) (.add (.mul (.int (-2)) (.mul (.var 0) (.mul (.var 2) (.mul (.var 4) (.pow (.var 3) 2))))) (.mul (.int 2) (.mul (.var 1) (.mul (.var 2) (.mul (.var 3) (.var 4))))))))))))
theorem dataS_17_7_binding : litSExpr 17 7=dataS_17_7 := rfl

def dataS_18_8 : RingExpr := (.int 1)
theorem dataS_18_8_binding : litSExpr 18 8=dataS_18_8 := rfl

def dataalpha_0_0 : RingExpr := (.int 1)
theorem dataalpha_0_0_binding : litalphaExpr 0 0=dataalpha_0_0 := rfl

def dataalpha_0_1 : RingExpr := (.var 2)
theorem dataalpha_0_1_binding : litalphaExpr 0 1=dataalpha_0_1 := rfl

def dataalpha_0_3 : RingExpr := (.mul (.int (-1)) (.var 2))
theorem dataalpha_0_3_binding : litalphaExpr 0 3=dataalpha_0_3 := rfl

def dataalpha_0_4 : RingExpr := (.var 3)
theorem dataalpha_0_4_binding : litalphaExpr 0 4=dataalpha_0_4 := rfl

def dataalpha_0_5 : RingExpr := (.mul (.int (-1)) (.var 3))
theorem dataalpha_0_5_binding : litalphaExpr 0 5=dataalpha_0_5 := rfl

def datadirection_0_0 : RingExpr := (.add (.mul (.int (-8)) (.mul (.var 0) (.mul (.var 4) (.pow (.var 3) 4)))) (.add (.mul (.int 12) (.mul (.var 1) (.mul (.var 4) (.pow (.var 3) 3)))) (.add (.mul (.int 12) (.mul (.var 2) (.mul (.var 4) (.pow (.var 3) 2)))) (.add (.mul (.int 16) (.mul (.pow (.var 0) 2) (.mul (.pow (.var 3) 6) (.pow (.var 4) 2)))) (.add (.mul (.int 24) (.mul (.pow (.var 1) 2) (.mul (.pow (.var 3) 4) (.pow (.var 4) 2)))) (.add (.mul (.int 48) (.mul (.pow (.var 2) 2) (.mul (.pow (.var 3) 2) (.pow (.var 4) 2)))) (.add (.mul (.int 48) (.mul (.pow (.var 2) 3) (.mul (.pow (.var 3) 2) (.pow (.var 4) 3)))) (.add (.mul (.int (-96)) (.mul (.var 0) (.mul (.pow (.var 2) 2) (.mul (.pow (.var 3) 4) (.pow (.var 4) 3))))) (.add (.mul (.int (-64)) (.mul (.var 0) (.mul (.var 2) (.mul (.pow (.var 3) 4) (.pow (.var 4) 2))))) (.add (.mul (.int (-40)) (.mul (.var 0) (.mul (.var 1) (.mul (.pow (.var 3) 5) (.pow (.var 4) 2))))) (.add (.mul (.int (-24)) (.mul (.var 0) (.mul (.var 6) (.mul (.pow (.var 3) 5) (.pow (.var 4) 2))))) (.add (.mul (.int 24) (.mul (.var 1) (.mul (.var 6) (.mul (.pow (.var 3) 4) (.pow (.var 4) 2))))) (.add (.mul (.int 24) (.mul (.var 6) (.mul (.var 2) (.mul (.pow (.var 3) 3) (.pow (.var 4) 2))))) (.add (.mul (.int 48) (.mul (.var 6) (.mul (.pow (.var 0) 2) (.mul (.pow (.var 3) 7) (.pow (.var 4) 3))))) (.add (.mul (.int 48) (.mul (.var 6) (.mul (.pow (.var 1) 2) (.mul (.pow (.var 3) 5) (.pow (.var 4) 3))))) (.add (.mul (.int 48) (.mul (.var 6) (.mul (.pow (.var 2) 2) (.mul (.pow (.var 3) 3) (.pow (.var 4) 3))))) (.add (.mul (.int 48) (.mul (.var 2) (.mul (.pow (.var 0) 2) (.mul (.pow (.var 3) 6) (.pow (.var 4) 3))))) (.add (.mul (.int 48) (.mul (.var 2) (.mul (.pow (.var 1) 2) (.mul (.pow (.var 3) 4) (.pow (.var 4) 3))))) (.add (.mul (.int 72) (.mul (.var 1) (.mul (.var 2) (.mul (.pow (.var 3) 3) (.pow (.var 4) 2))))) (.add (.mul (.int 96) (.mul (.var 1) (.mul (.pow (.var 2) 2) (.mul (.pow (.var 3) 3) (.pow (.var 4) 3))))) (.add (.mul (.int (-96)) (.mul (.var 0) (.mul (.var 1) (.mul (.var 6) (.mul (.pow (.var 3) 6) (.pow (.var 4) 3)))))) (.add (.mul (.int (-96)) (.mul (.var 0) (.mul (.var 1) (.mul (.var 2) (.mul (.pow (.var 3) 5) (.pow (.var 4) 3)))))) (.add (.mul (.int (-96)) (.mul (.var 0) (.mul (.var 6) (.mul (.var 2) (.mul (.pow (.var 3) 5) (.pow (.var 4) 3)))))) (.mul (.int 96) (.mul (.var 1) (.mul (.var 6) (.mul (.var 2) (.mul (.pow (.var 3) 4) (.pow (.var 4) 3)))))))))))))))))))))))))))))
theorem datadirection_0_0_binding : litdirectionExpr 0 0=datadirection_0_0 := rfl

def datadirection_1_0 : RingExpr := (.add (.mul (.int (-6)) (.mul (.var 1) (.pow (.var 3) 2))) (.add (.mul (.int (-6)) (.mul (.var 2) (.var 3))) (.add (.mul (.int (-72)) (.mul (.var 3) (.mul (.pow (.var 2) 3) (.pow (.var 4) 2)))) (.add (.mul (.int (-48)) (.mul (.var 3) (.mul (.pow (.var 2) 4) (.pow (.var 4) 3)))) (.add (.mul (.int (-36)) (.mul (.var 3) (.mul (.var 4) (.pow (.var 2) 2)))) (.add (.mul (.int (-12)) (.mul (.var 4) (.mul (.pow (.var 1) 2) (.pow (.var 3) 3)))) (.add (.mul (.int (-120)) (.mul (.var 1) (.mul (.pow (.var 2) 2) (.mul (.pow (.var 3) 2) (.pow (.var 4) 2))))) (.add (.mul (.int (-96)) (.mul (.var 1) (.mul (.pow (.var 2) 3) (.mul (.pow (.var 3) 2) (.pow (.var 4) 3))))) (.add (.mul (.int (-48)) (.mul (.var 1) (.mul (.var 2) (.mul (.var 4) (.pow (.var 3) 2))))) (.add (.mul (.int (-48)) (.mul (.var 6) (.mul (.pow (.var 2) 2) (.mul (.pow (.var 3) 2) (.pow (.var 4) 2))))) (.add (.mul (.int (-48)) (.mul (.var 6) (.mul (.pow (.var 2) 3) (.mul (.pow (.var 3) 2) (.pow (.var 4) 3))))) (.add (.mul (.int (-48)) (.mul (.var 2) (.mul (.pow (.var 1) 2) (.mul (.pow (.var 3) 3) (.pow (.var 4) 2))))) (.add (.mul (.int (-48)) (.mul (.pow (.var 0) 2) (.mul (.pow (.var 2) 2) (.mul (.pow (.var 3) 5) (.pow (.var 4) 3))))) (.add (.mul (.int (-48)) (.mul (.pow (.var 1) 2) (.mul (.pow (.var 2) 2) (.mul (.pow (.var 3) 3) (.pow (.var 4) 3))))) (.add (.mul (.int (-24)) (.mul (.var 6) (.mul (.pow (.var 1) 2) (.mul (.pow (.var 3) 4) (.pow (.var 4) 2))))) (.add (.mul (.int (-12)) (.mul (.var 1) (.mul (.var 6) (.mul (.var 4) (.pow (.var 3) 3))))) (.add (.mul (.int (-12)) (.mul (.var 6) (.mul (.var 2) (.mul (.var 4) (.pow (.var 3) 2))))) (.add (.mul (.int 4) (.mul (.var 0) (.mul (.var 6) (.mul (.var 4) (.pow (.var 3) 4))))) (.add (.mul (.int 12) (.mul (.var 0) (.mul (.var 2) (.mul (.var 4) (.pow (.var 3) 3))))) (.add (.mul (.int 16) (.mul (.var 6) (.mul (.pow (.var 0) 2) (.mul (.pow (.var 3) 6) (.pow (.var 4) 2))))) (.add (.mul (.int 72) (.mul (.var 0) (.mul (.pow (.var 2) 2) (.mul (.pow (.var 3) 3) (.pow (.var 4) 2))))) (.add (.mul (.int 96) (.mul (.var 0) (.mul (.pow (.var 2) 3) (.mul (.pow (.var 3) 3) (.pow (.var 4) 3))))) (.add (.mul (.int (-96)) (.mul (.var 1) (.mul (.var 6) (.mul (.pow (.var 2) 2) (.mul (.pow (.var 3) 3) (.pow (.var 4) 3)))))) (.add (.mul (.int (-72)) (.mul (.var 1) (.mul (.var 6) (.mul (.var 2) (.mul (.pow (.var 3) 3) (.pow (.var 4) 2)))))) (.add (.mul (.int (-48)) (.mul (.var 6) (.mul (.var 2) (.mul (.pow (.var 0) 2) (.mul (.pow (.var 3) 6) (.pow (.var 4) 3)))))) (.add (.mul (.int (-48)) (.mul (.var 6) (.mul (.var 2) (.mul (.pow (.var 1) 2) (.mul (.pow (.var 3) 4) (.pow (.var 4) 3)))))) (.add (.mul (.int 8) (.mul (.var 0) (.mul (.var 1) (.mul (.var 6) (.mul (.pow (.var 3) 5) (.pow (.var 4) 2)))))) (.add (.mul (.int 32) (.mul (.var 0) (.mul (.var 6) (.mul (.var 2) (.mul (.pow (.var 3) 4) (.pow (.var 4) 2)))))) (.add (.mul (.int 48) (.mul (.var 0) (.mul (.var 1) (.mul (.var 2) (.mul (.pow (.var 3) 4) (.pow (.var 4) 2)))))) (.add (.mul (.int 96) (.mul (.var 0) (.mul (.var 1) (.mul (.pow (.var 2) 2) (.mul (.pow (.var 3) 4) (.pow (.var 4) 3)))))) (.add (.mul (.int 96) (.mul (.var 0) (.mul (.var 6) (.mul (.pow (.var 2) 2) (.mul (.pow (.var 3) 4) (.pow (.var 4) 3)))))) (.mul (.int 96) (.mul (.var 0) (.mul (.var 1) (.mul (.var 6) (.mul (.var 2) (.mul (.pow (.var 3) 5) (.pow (.var 4) 3))))))))))))))))))))))))))))))))))))))
theorem datadirection_1_0_binding : litdirectionExpr 1 0=datadirection_1_0 := rfl

def datadirection_2_0 : RingExpr := (.add (.mul (.int (-18)) (.mul (.var 1) (.pow (.var 3) 2))) (.add (.mul (.int (-18)) (.mul (.var 2) (.var 3))) (.add (.mul (.int (-72)) (.mul (.var 3) (.mul (.var 4) (.pow (.var 2) 2)))) (.add (.mul (.int (-72)) (.mul (.var 3) (.mul (.pow (.var 2) 3) (.pow (.var 4) 2)))) (.add (.mul (.int (-18)) (.mul (.var 4) (.mul (.pow (.var 1) 2) (.pow (.var 3) 3)))) (.add (.mul (.int 6) (.mul (.var 5) (.mul (.var 1) (.pow (.var 3) 2)))) (.add (.mul (.int 6) (.mul (.var 5) (.mul (.var 2) (.var 3)))) (.add (.mul (.int 36) (.mul (.pow (.var 1) 3) (.mul (.pow (.var 3) 4) (.pow (.var 4) 2)))) (.add (.mul (.int (-90)) (.mul (.var 1) (.mul (.var 2) (.mul (.var 4) (.pow (.var 3) 2))))) (.add (.mul (.int (-72)) (.mul (.var 1) (.mul (.pow (.var 2) 2) (.mul (.pow (.var 3) 2) (.pow (.var 4) 2))))) (.add (.mul (.int (-72)) (.mul (.var 6) (.mul (.pow (.var 2) 2) (.mul (.pow (.var 3) 2) (.pow (.var 4) 2))))) (.add (.mul (.int (-36)) (.mul (.var 0) (.mul (.pow (.var 1) 2) (.mul (.pow (.var 3) 5) (.pow (.var 4) 2))))) (.add (.mul (.int (-36)) (.mul (.var 1) (.mul (.var 6) (.mul (.var 4) (.pow (.var 3) 3))))) (.add (.mul (.int (-36)) (.mul (.var 6) (.mul (.var 2) (.mul (.var 4) (.pow (.var 3) 2))))) (.add (.mul (.int (-36)) (.mul (.var 6) (.mul (.pow (.var 1) 2) (.mul (.pow (.var 3) 4) (.pow (.var 4) 2))))) (.add (.mul (.int 12) (.mul (.var 5) (.mul (.var 4) (.mul (.pow (.var 1) 2) (.pow (.var 3) 3))))) (.add (.mul (.int 24) (.mul (.var 5) (.mul (.var 3) (.mul (.var 4) (.pow (.var 2) 2))))) (.add (.mul (.int 24) (.mul (.var 5) (.mul (.var 3) (.mul (.pow (.var 2) 3) (.pow (.var 4) 2))))) (.add (.mul (.int 24) (.mul (.var 0) (.mul (.var 6) (.mul (.var 4) (.pow (.var 3) 4))))) (.add (.mul (.int 24) (.mul (.var 6) (.mul (.pow (.var 0) 2) (.mul (.pow (.var 3) 6) (.pow (.var 4) 2))))) (.add (.mul (.int 36) (.mul (.var 0) (.mul (.var 2) (.mul (.var 4) (.pow (.var 3) 3))))) (.add (.mul (.int 36) (.mul (.var 2) (.mul (.pow (.var 1) 2) (.mul (.pow (.var 3) 3) (.pow (.var 4) 2))))) (.add (.mul (.int 72) (.mul (.var 0) (.mul (.pow (.var 2) 2) (.mul (.pow (.var 3) 3) (.pow (.var 4) 2))))) (.add (.mul (.int 72) (.mul (.var 1) (.mul (.pow (.var 2) 3) (.mul (.pow (.var 3) 2) (.pow (.var 4) 3))))) (.add (.mul (.int 72) (.mul (.var 6) (.mul (.pow (.var 1) 3) (.mul (.pow (.var 3) 5) (.pow (.var 4) 3))))) (.add (.mul (.int 72) (.mul (.var 2) (.mul (.pow (.var 1) 3) (.mul (.pow (.var 3) 4) (.pow (.var 4) 3))))) (.add (.mul (.int 144) (.mul (.pow (.var 1) 2) (.mul (.pow (.var 2) 2) (.mul (.pow (.var 3) 3) (.pow (.var 4) 3))))) (.add (.mul (.int (-144)) (.mul (.var 0) (.mul (.var 1) (.mul (.pow (.var 2) 2) (.mul (.pow (.var 3) 4) (.pow (.var 4) 3)))))) (.add (.mul (.int (-144)) (.mul (.var 0) (.mul (.var 6) (.mul (.pow (.var 1) 2) (.mul (.pow (.var 3) 6) (.pow (.var 4) 3)))))) (.add (.mul (.int (-144)) (.mul (.var 0) (.mul (.var 2) (.mul (.pow (.var 1) 2) (.mul (.pow (.var 3) 5) (.pow (.var 4) 3)))))) (.add (.mul (.int (-108)) (.mul (.var 1) (.mul (.var 6) (.mul (.var 2) (.mul (.pow (.var 3) 3) (.pow (.var 4) 2)))))) (.add (.mul (.int (-48)) (.mul (.var 5) (.mul (.var 0) (.mul (.pow (.var 2) 2) (.mul (.pow (.var 3) 3) (.pow (.var 4) 2)))))) (.add (.mul (.int (-24)) (.mul (.var 5) (.mul (.var 0) (.mul (.var 2) (.mul (.var 4) (.pow (.var 3) 3)))))) (.add (.mul (.int (-12)) (.mul (.var 5) (.mul (.var 0) (.mul (.var 1) (.mul (.var 4) (.pow (.var 3) 4)))))) (.add (.mul (.int (-12)) (.mul (.var 5) (.mul (.var 0) (.mul (.var 6) (.mul (.var 4) (.pow (.var 3) 4)))))) (.add (.mul (.int 12) (.mul (.var 5) (.mul (.var 1) (.mul (.var 6) (.mul (.var 4) (.pow (.var 3) 3)))))) (.add (.mul (.int 12) (.mul (.var 5) (.mul (.var 6) (.mul (.var 2) (.mul (.var 4) (.pow (.var 3) 2)))))) (.add (.mul (.int 12) (.mul (.var 0) (.mul (.var 1) (.mul (.var 6) (.mul (.pow (.var 3) 5) (.pow (.var 4) 2)))))) (.add (.mul (.int 24) (.mul (.var 5) (.mul (.var 6) (.mul (.pow (.var 0) 2) (.mul (.pow (.var 3) 6) (.pow (.var 4) 2)))))) (.add (.mul (.int 24) (.mul (.var 5) (.mul (.var 6) (.mul (.pow (.var 1) 2) (.mul (.pow (.var 3) 4) (.pow (.var 4) 2)))))) (.add (.mul (.int 24) (.mul (.var 5) (.mul (.var 6) (.mul (.pow (.var 2) 2) (.mul (.pow (.var 3) 2) (.pow (.var 4) 2)))))) (.add (.mul (.int 24) (.mul (.var 5) (.mul (.var 2) (.mul (.pow (.var 0) 2) (.mul (.pow (.var 3) 5) (.pow (.var 4) 2)))))) (.add (.mul (.int 24) (.mul (.var 5) (.mul (.var 2) (.mul (.pow (.var 1) 2) (.mul (.pow (.var 3) 3) (.pow (.var 4) 2)))))) (.add (.mul (.int 36) (.mul (.var 5) (.mul (.var 1) (.mul (.var 2) (.mul (.var 4) (.pow (.var 3) 2)))))) (.add (.mul (.int 48) (.mul (.var 5) (.mul (.var 1) (.mul (.pow (.var 2) 2) (.mul (.pow (.var 3) 2) (.pow (.var 4) 2)))))) (.add (.mul (.int 48) (.mul (.var 0) (.mul (.var 6) (.mul (.var 2) (.mul (.pow (.var 3) 4) (.pow (.var 4) 2)))))) (.add (.mul (.int 72) (.mul (.var 1) (.mul (.var 6) (.mul (.pow (.var 0) 2) (.mul (.pow (.var 3) 7) (.pow (.var 4) 3)))))) (.add (.mul (.int 72) (.mul (.var 1) (.mul (.var 6) (.mul (.pow (.var 2) 2) (.mul (.pow (.var 3) 3) (.pow (.var 4) 3)))))) (.add (.mul (.int 72) (.mul (.var 1) (.mul (.var 2) (.mul (.pow (.var 0) 2) (.mul (.pow (.var 3) 6) (.pow (.var 4) 3)))))) (.add (.mul (.int 144) (.mul (.var 6) (.mul (.var 2) (.mul (.pow (.var 1) 2) (.mul (.pow (.var 3) 4) (.pow (.var 4) 3)))))) (.add (.mul (.int (-144)) (.mul (.var 0) (.mul (.var 1) (.mul (.var 6) (.mul (.var 2) (.mul (.pow (.var 3) 5) (.pow (.var 4) 3))))))) (.add (.mul (.int (-48)) (.mul (.var 5) (.mul (.var 0) (.mul (.var 1) (.mul (.var 6) (.mul (.pow (.var 3) 5) (.pow (.var 4) 2))))))) (.add (.mul (.int (-48)) (.mul (.var 5) (.mul (.var 0) (.mul (.var 1) (.mul (.var 2) (.mul (.pow (.var 3) 4) (.pow (.var 4) 2))))))) (.add (.mul (.int (-48)) (.mul (.var 5) (.mul (.var 0) (.mul (.var 6) (.mul (.var 2) (.mul (.pow (.var 3) 4) (.pow (.var 4) 2))))))) (.mul (.int 48) (.mul (.var 5) (.mul (.var 1) (.mul (.var 6) (.mul (.var 2) (.mul (.pow (.var 3) 3) (.pow (.var 4) 2)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
theorem datadirection_2_0_binding : litdirectionExpr 2 0=datadirection_2_0 := rfl

def datadirection_3_0 : RingExpr := (.add (.mul (.int (-3)) (.mul (.var 1) (.pow (.var 3) 2))) (.add (.mul (.int (-3)) (.mul (.var 2) (.var 3))) (.add (.mul (.int (-36)) (.mul (.var 3) (.mul (.pow (.var 2) 3) (.pow (.var 4) 2)))) (.add (.mul (.int (-24)) (.mul (.var 3) (.mul (.pow (.var 2) 4) (.pow (.var 4) 3)))) (.add (.mul (.int (-18)) (.mul (.var 3) (.mul (.var 4) (.pow (.var 2) 2)))) (.add (.mul (.int (-6)) (.mul (.var 4) (.mul (.pow (.var 1) 2) (.pow (.var 3) 3)))) (.add (.mul (.int (-60)) (.mul (.var 1) (.mul (.pow (.var 2) 2) (.mul (.pow (.var 3) 2) (.pow (.var 4) 2))))) (.add (.mul (.int (-48)) (.mul (.var 1) (.mul (.pow (.var 2) 3) (.mul (.pow (.var 3) 2) (.pow (.var 4) 3))))) (.add (.mul (.int (-24)) (.mul (.var 1) (.mul (.var 2) (.mul (.var 4) (.pow (.var 3) 2))))) (.add (.mul (.int (-24)) (.mul (.var 6) (.mul (.pow (.var 2) 2) (.mul (.pow (.var 3) 2) (.pow (.var 4) 2))))) (.add (.mul (.int (-24)) (.mul (.var 6) (.mul (.pow (.var 2) 3) (.mul (.pow (.var 3) 2) (.pow (.var 4) 3))))) (.add (.mul (.int (-24)) (.mul (.var 2) (.mul (.pow (.var 1) 2) (.mul (.pow (.var 3) 3) (.pow (.var 4) 2))))) (.add (.mul (.int (-24)) (.mul (.pow (.var 0) 2) (.mul (.pow (.var 2) 2) (.mul (.pow (.var 3) 5) (.pow (.var 4) 3))))) (.add (.mul (.int (-24)) (.mul (.pow (.var 1) 2) (.mul (.pow (.var 2) 2) (.mul (.pow (.var 3) 3) (.pow (.var 4) 3))))) (.add (.mul (.int (-12)) (.mul (.var 6) (.mul (.pow (.var 1) 2) (.mul (.pow (.var 3) 4) (.pow (.var 4) 2))))) (.add (.mul (.int (-6)) (.mul (.var 0) (.mul (.var 1) (.mul (.var 4) (.pow (.var 3) 4))))) (.add (.mul (.int (-6)) (.mul (.var 1) (.mul (.var 6) (.mul (.var 4) (.pow (.var 3) 3))))) (.add (.mul (.int (-6)) (.mul (.var 6) (.mul (.var 2) (.mul (.var 4) (.pow (.var 3) 2))))) (.add (.mul (.int 4) (.mul (.var 0) (.mul (.var 6) (.mul (.var 4) (.pow (.var 3) 4))))) (.add (.mul (.int 12) (.mul (.var 2) (.mul (.pow (.var 0) 2) (.mul (.pow (.var 3) 5) (.pow (.var 4) 2))))) (.add (.mul (.int 16) (.mul (.var 6) (.mul (.pow (.var 0) 2) (.mul (.pow (.var 3) 6) (.pow (.var 4) 2))))) (.add (.mul (.int 24) (.mul (.var 0) (.mul (.pow (.var 2) 2) (.mul (.pow (.var 3) 3) (.pow (.var 4) 2))))) (.add (.mul (.int 48) (.mul (.var 0) (.mul (.pow (.var 2) 3) (.mul (.pow (.var 3) 3) (.pow (.var 4) 3))))) (.add (.mul (.int (-48)) (.mul (.var 1) (.mul (.var 6) (.mul (.pow (.var 2) 2) (.mul (.pow (.var 3) 3) (.pow (.var 4) 3)))))) (.add (.mul (.int (-36)) (.mul (.var 1) (.mul (.var 6) (.mul (.var 2) (.mul (.pow (.var 3) 3) (.pow (.var 4) 2)))))) (.add (.mul (.int (-24)) (.mul (.var 6) (.mul (.var 2) (.mul (.pow (.var 0) 2) (.mul (.pow (.var 3) 6) (.pow (.var 4) 3)))))) (.add (.mul (.int (-24)) (.mul (.var 6) (.mul (.var 2) (.mul (.pow (.var 1) 2) (.mul (.pow (.var 3) 4) (.pow (.var 4) 3)))))) (.add (.mul (.int (-4)) (.mul (.var 0) (.mul (.var 1) (.mul (.var 6) (.mul (.pow (.var 3) 5) (.pow (.var 4) 2)))))) (.add (.mul (.int 8) (.mul (.var 0) (.mul (.var 6) (.mul (.var 2) (.mul (.pow (.var 3) 4) (.pow (.var 4) 2)))))) (.add (.mul (.int 12) (.mul (.var 0) (.mul (.var 1) (.mul (.var 2) (.mul (.pow (.var 3) 4) (.pow (.var 4) 2)))))) (.add (.mul (.int 48) (.mul (.var 0) (.mul (.var 1) (.mul (.pow (.var 2) 2) (.mul (.pow (.var 3) 4) (.pow (.var 4) 3)))))) (.add (.mul (.int 48) (.mul (.var 0) (.mul (.var 6) (.mul (.pow (.var 2) 2) (.mul (.pow (.var 3) 4) (.pow (.var 4) 3)))))) (.mul (.int 48) (.mul (.var 0) (.mul (.var 1) (.mul (.var 6) (.mul (.var 2) (.mul (.pow (.var 3) 5) (.pow (.var 4) 3)))))))))))))))))))))))))))))))))))))))
theorem datadirection_3_0_binding : litdirectionExpr 3 0=datadirection_3_0 := rfl

def datadirection_4_0 : RingExpr := (.add (.mul (.int 6) (.pow (.var 2) 2)) (.add (.mul (.int 36) (.mul (.var 4) (.pow (.var 2) 3))) (.add (.mul (.int 48) (.mul (.pow (.var 2) 5) (.pow (.var 4) 3))) (.add (.mul (.int 72) (.mul (.pow (.var 2) 4) (.pow (.var 4) 2))) (.add (.mul (.int (-48)) (.mul (.var 3) (.mul (.pow (.var 2) 2) (.pow (.var 4) 2)))) (.add (.mul (.int (-48)) (.mul (.var 3) (.mul (.pow (.var 2) 3) (.pow (.var 4) 3)))) (.add (.mul (.int (-24)) (.mul (.pow (.var 1) 2) (.mul (.pow (.var 3) 3) (.pow (.var 4) 2)))) (.add (.mul (.int (-16)) (.mul (.pow (.var 0) 2) (.mul (.pow (.var 3) 5) (.pow (.var 4) 2)))) (.add (.mul (.int (-12)) (.mul (.var 1) (.mul (.var 4) (.pow (.var 3) 2)))) (.add (.mul (.int (-12)) (.mul (.var 2) (.mul (.var 3) (.var 4)))) (.add (.mul (.int 6) (.mul (.var 0) (.mul (.var 1) (.pow (.var 3) 3)))) (.add (.mul (.int 6) (.mul (.var 0) (.mul (.var 2) (.pow (.var 3) 2)))) (.add (.mul (.int 6) (.mul (.var 1) (.mul (.var 2) (.var 3)))) (.add (.mul (.int 8) (.mul (.var 0) (.mul (.var 4) (.pow (.var 3) 3)))) (.add (.mul (.int (-96)) (.mul (.var 0) (.mul (.pow (.var 2) 4) (.mul (.pow (.var 3) 2) (.pow (.var 4) 3))))) (.add (.mul (.int (-96)) (.mul (.var 1) (.mul (.pow (.var 2) 2) (.mul (.pow (.var 3) 2) (.pow (.var 4) 3))))) (.add (.mul (.int (-72)) (.mul (.var 0) (.mul (.pow (.var 2) 3) (.mul (.pow (.var 3) 2) (.pow (.var 4) 2))))) (.add (.mul (.int (-72)) (.mul (.var 1) (.mul (.var 2) (.mul (.pow (.var 3) 2) (.pow (.var 4) 2))))) (.add (.mul (.int (-48)) (.mul (.var 6) (.mul (.pow (.var 0) 2) (.mul (.pow (.var 3) 6) (.pow (.var 4) 3))))) (.add (.mul (.int (-48)) (.mul (.var 6) (.mul (.pow (.var 1) 2) (.mul (.pow (.var 3) 4) (.pow (.var 4) 3))))) (.add (.mul (.int (-48)) (.mul (.var 6) (.mul (.pow (.var 2) 2) (.mul (.pow (.var 3) 2) (.pow (.var 4) 3))))) (.add (.mul (.int (-48)) (.mul (.var 2) (.mul (.pow (.var 0) 2) (.mul (.pow (.var 3) 5) (.pow (.var 4) 3))))) (.add (.mul (.int (-48)) (.mul (.var 2) (.mul (.pow (.var 1) 2) (.mul (.pow (.var 3) 3) (.pow (.var 4) 3))))) (.add (.mul (.int (-24)) (.mul (.var 1) (.mul (.var 6) (.mul (.pow (.var 3) 3) (.pow (.var 4) 2))))) (.add (.mul (.int (-24)) (.mul (.var 6) (.mul (.var 2) (.mul (.pow (.var 3) 2) (.pow (.var 4) 2))))) (.add (.mul (.int (-12)) (.mul (.var 6) (.mul (.var 4) (.mul (.pow (.var 0) 2) (.pow (.var 3) 5))))) (.add (.mul (.int (-12)) (.mul (.var 2) (.mul (.var 4) (.mul (.pow (.var 0) 2) (.pow (.var 3) 4))))) (.add (.mul (.int 12) (.mul (.var 6) (.mul (.var 3) (.mul (.var 4) (.pow (.var 2) 2))))) (.add (.mul (.int 12) (.mul (.var 2) (.mul (.var 4) (.mul (.pow (.var 1) 2) (.pow (.var 3) 2))))) (.add (.mul (.int 24) (.mul (.var 0) (.mul (.var 6) (.mul (.pow (.var 3) 4) (.pow (.var 4) 2))))) (.add (.mul (.int 40) (.mul (.var 0) (.mul (.var 1) (.mul (.pow (.var 3) 4) (.pow (.var 4) 2))))) (.add (.mul (.int 48) (.mul (.var 1) (.mul (.var 3) (.mul (.var 4) (.pow (.var 2) 2))))) (.add (.mul (.int 48) (.mul (.var 6) (.mul (.var 3) (.mul (.pow (.var 2) 3) (.pow (.var 4) 2))))) (.add (.mul (.int 48) (.mul (.var 6) (.mul (.var 3) (.mul (.pow (.var 2) 4) (.pow (.var 4) 3))))) (.add (.mul (.int 48) (.mul (.pow (.var 0) 2) (.mul (.pow (.var 2) 3) (.mul (.pow (.var 3) 4) (.pow (.var 4) 3))))) (.add (.mul (.int 48) (.mul (.pow (.var 1) 2) (.mul (.pow (.var 2) 2) (.mul (.pow (.var 3) 2) (.pow (.var 4) 2))))) (.add (.mul (.int 48) (.mul (.pow (.var 1) 2) (.mul (.pow (.var 2) 3) (.mul (.pow (.var 3) 2) (.pow (.var 4) 3))))) (.add (.mul (.int 64) (.mul (.var 0) (.mul (.var 2) (.mul (.pow (.var 3) 3) (.pow (.var 4) 2))))) (.add (.mul (.int 96) (.mul (.var 0) (.mul (.pow (.var 2) 2) (.mul (.pow (.var 3) 3) (.pow (.var 4) 3))))) (.add (.mul (.int 96) (.mul (.var 1) (.mul (.var 3) (.mul (.pow (.var 2) 4) (.pow (.var 4) 3))))) (.add (.mul (.int 120) (.mul (.var 1) (.mul (.var 3) (.mul (.pow (.var 2) 3) (.pow (.var 4) 2))))) (.add (.mul (.int (-96)) (.mul (.var 0) (.mul (.var 1) (.mul (.pow (.var 2) 3) (.mul (.pow (.var 3) 3) (.pow (.var 4) 3)))))) (.add (.mul (.int (-96)) (.mul (.var 0) (.mul (.var 6) (.mul (.pow (.var 2) 3) (.mul (.pow (.var 3) 3) (.pow (.var 4) 3)))))) (.add (.mul (.int (-96)) (.mul (.var 1) (.mul (.var 6) (.mul (.var 2) (.mul (.pow (.var 3) 3) (.pow (.var 4) 3)))))) (.add (.mul (.int (-48)) (.mul (.var 0) (.mul (.var 1) (.mul (.pow (.var 2) 2) (.mul (.pow (.var 3) 3) (.pow (.var 4) 2)))))) (.add (.mul (.int (-32)) (.mul (.var 0) (.mul (.var 6) (.mul (.pow (.var 2) 2) (.mul (.pow (.var 3) 3) (.pow (.var 4) 2)))))) (.add (.mul (.int (-16)) (.mul (.var 6) (.mul (.var 2) (.mul (.pow (.var 0) 2) (.mul (.pow (.var 3) 5) (.pow (.var 4) 2)))))) (.add (.mul (.int 8) (.mul (.var 0) (.mul (.var 6) (.mul (.var 2) (.mul (.var 4) (.pow (.var 3) 3)))))) (.add (.mul (.int 12) (.mul (.var 0) (.mul (.var 1) (.mul (.var 6) (.mul (.var 4) (.pow (.var 3) 4)))))) (.add (.mul (.int 12) (.mul (.var 0) (.mul (.var 1) (.mul (.var 2) (.mul (.var 4) (.pow (.var 3) 3)))))) (.add (.mul (.int 12) (.mul (.var 1) (.mul (.var 6) (.mul (.var 2) (.mul (.var 4) (.pow (.var 3) 2)))))) (.add (.mul (.int 24) (.mul (.var 6) (.mul (.var 2) (.mul (.pow (.var 1) 2) (.mul (.pow (.var 3) 3) (.pow (.var 4) 2)))))) (.add (.mul (.int 48) (.mul (.var 6) (.mul (.pow (.var 0) 2) (.mul (.pow (.var 2) 2) (.mul (.pow (.var 3) 5) (.pow (.var 4) 3)))))) (.add (.mul (.int 48) (.mul (.var 6) (.mul (.pow (.var 1) 2) (.mul (.pow (.var 2) 2) (.mul (.pow (.var 3) 3) (.pow (.var 4) 3)))))) (.add (.mul (.int 72) (.mul (.var 1) (.mul (.var 6) (.mul (.pow (.var 2) 2) (.mul (.pow (.var 3) 2) (.pow (.var 4) 2)))))) (.add (.mul (.int 96) (.mul (.var 0) (.mul (.var 1) (.mul (.var 6) (.mul (.pow (.var 3) 5) (.pow (.var 4) 3)))))) (.add (.mul (.int 96) (.mul (.var 0) (.mul (.var 1) (.mul (.var 2) (.mul (.pow (.var 3) 4) (.pow (.var 4) 3)))))) (.add (.mul (.int 96) (.mul (.var 0) (.mul (.var 6) (.mul (.var 2) (.mul (.pow (.var 3) 4) (.pow (.var 4) 3)))))) (.add (.mul (.int 96) (.mul (.var 1) (.mul (.var 6) (.mul (.pow (.var 2) 3) (.mul (.pow (.var 3) 2) (.pow (.var 4) 3)))))) (.add (.mul (.int (-96)) (.mul (.var 0) (.mul (.var 1) (.mul (.var 6) (.mul (.pow (.var 2) 2) (.mul (.pow (.var 3) 4) (.pow (.var 4) 3))))))) (.mul (.int (-8)) (.mul (.var 0) (.mul (.var 1) (.mul (.var 6) (.mul (.var 2) (.mul (.pow (.var 3) 4) (.pow (.var 4) 2)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
theorem datadirection_4_0_binding : litdirectionExpr 4 0=datadirection_4_0 := rfl

def datadirection_5_0 : RingExpr := (.add (.mul (.int 3) (.pow (.var 2) 2)) (.add (.mul (.int 18) (.mul (.var 4) (.pow (.var 2) 3))) (.add (.mul (.int 24) (.mul (.pow (.var 2) 5) (.pow (.var 4) 3))) (.add (.mul (.int 36) (.mul (.pow (.var 2) 4) (.pow (.var 4) 2))) (.add (.mul (.int (-24)) (.mul (.var 3) (.mul (.pow (.var 2) 2) (.pow (.var 4) 2)))) (.add (.mul (.int (-24)) (.mul (.var 3) (.mul (.pow (.var 2) 3) (.pow (.var 4) 3)))) (.add (.mul (.int (-12)) (.mul (.pow (.var 1) 2) (.mul (.pow (.var 3) 3) (.pow (.var 4) 2)))) (.add (.mul (.int (-6)) (.mul (.var 1) (.mul (.var 4) (.pow (.var 3) 2)))) (.add (.mul (.int (-6)) (.mul (.var 2) (.mul (.var 3) (.var 4)))) (.add (.mul (.int (-4)) (.mul (.pow (.var 0) 2) (.mul (.pow (.var 3) 5) (.pow (.var 4) 2)))) (.add (.mul (.int 2) (.mul (.var 0) (.mul (.var 4) (.pow (.var 3) 3)))) (.add (.mul (.int 3) (.mul (.var 1) (.mul (.var 2) (.var 3)))) (.add (.mul (.int 6) (.mul (.var 0) (.mul (.var 1) (.pow (.var 3) 3)))) (.add (.mul (.int 6) (.mul (.var 0) (.mul (.var 2) (.pow (.var 3) 2)))) (.add (.mul (.int (-48)) (.mul (.var 0) (.mul (.pow (.var 2) 4) (.mul (.pow (.var 3) 2) (.pow (.var 4) 3))))) (.add (.mul (.int (-48)) (.mul (.var 1) (.mul (.pow (.var 2) 2) (.mul (.pow (.var 3) 2) (.pow (.var 4) 3))))) (.add (.mul (.int (-36)) (.mul (.var 1) (.mul (.var 2) (.mul (.pow (.var 3) 2) (.pow (.var 4) 2))))) (.add (.mul (.int (-24)) (.mul (.var 0) (.mul (.pow (.var 2) 3) (.mul (.pow (.var 3) 2) (.pow (.var 4) 2))))) (.add (.mul (.int (-24)) (.mul (.var 6) (.mul (.pow (.var 0) 2) (.mul (.pow (.var 3) 6) (.pow (.var 4) 3))))) (.add (.mul (.int (-24)) (.mul (.var 6) (.mul (.pow (.var 1) 2) (.mul (.pow (.var 3) 4) (.pow (.var 4) 3))))) (.add (.mul (.int (-24)) (.mul (.var 6) (.mul (.pow (.var 2) 2) (.mul (.pow (.var 3) 2) (.pow (.var 4) 3))))) (.add (.mul (.int (-24)) (.mul (.var 2) (.mul (.pow (.var 0) 2) (.mul (.pow (.var 3) 5) (.pow (.var 4) 3))))) (.add (.mul (.int (-24)) (.mul (.var 2) (.mul (.pow (.var 1) 2) (.mul (.pow (.var 3) 3) (.pow (.var 4) 3))))) (.add (.mul (.int (-12)) (.mul (.var 1) (.mul (.var 6) (.mul (.pow (.var 3) 3) (.pow (.var 4) 2))))) (.add (.mul (.int (-12)) (.mul (.var 6) (.mul (.var 2) (.mul (.pow (.var 3) 2) (.pow (.var 4) 2))))) (.add (.mul (.int (-12)) (.mul (.var 6) (.mul (.var 4) (.mul (.pow (.var 0) 2) (.pow (.var 3) 5))))) (.add (.mul (.int (-12)) (.mul (.var 2) (.mul (.var 4) (.mul (.pow (.var 0) 2) (.pow (.var 3) 4))))) (.add (.mul (.int (-12)) (.mul (.pow (.var 0) 2) (.mul (.pow (.var 2) 2) (.mul (.pow (.var 3) 4) (.pow (.var 4) 2))))) (.add (.mul (.int 6) (.mul (.var 6) (.mul (.var 3) (.mul (.var 4) (.pow (.var 2) 2))))) (.add (.mul (.int 6) (.mul (.var 2) (.mul (.var 4) (.mul (.pow (.var 1) 2) (.pow (.var 3) 2))))) (.add (.mul (.int 12) (.mul (.var 0) (.mul (.var 6) (.mul (.pow (.var 3) 4) (.pow (.var 4) 2))))) (.add (.mul (.int 12) (.mul (.var 0) (.mul (.var 4) (.mul (.pow (.var 2) 2) (.pow (.var 3) 2))))) (.add (.mul (.int 16) (.mul (.var 0) (.mul (.var 1) (.mul (.pow (.var 3) 4) (.pow (.var 4) 2))))) (.add (.mul (.int 24) (.mul (.var 1) (.mul (.var 3) (.mul (.var 4) (.pow (.var 2) 2))))) (.add (.mul (.int 24) (.mul (.var 6) (.mul (.var 3) (.mul (.pow (.var 2) 3) (.pow (.var 4) 2))))) (.add (.mul (.int 24) (.mul (.var 6) (.mul (.var 3) (.mul (.pow (.var 2) 4) (.pow (.var 4) 3))))) (.add (.mul (.int 24) (.mul (.pow (.var 0) 2) (.mul (.pow (.var 2) 3) (.mul (.pow (.var 3) 4) (.pow (.var 4) 3))))) (.add (.mul (.int 24) (.mul (.pow (.var 1) 2) (.mul (.pow (.var 2) 2) (.mul (.pow (.var 3) 2) (.pow (.var 4) 2))))) (.add (.mul (.int 24) (.mul (.pow (.var 1) 2) (.mul (.pow (.var 2) 3) (.mul (.pow (.var 3) 2) (.pow (.var 4) 3))))) (.add (.mul (.int 28) (.mul (.var 0) (.mul (.var 2) (.mul (.pow (.var 3) 3) (.pow (.var 4) 2))))) (.add (.mul (.int 48) (.mul (.var 0) (.mul (.pow (.var 2) 2) (.mul (.pow (.var 3) 3) (.pow (.var 4) 3))))) (.add (.mul (.int 48) (.mul (.var 1) (.mul (.var 3) (.mul (.pow (.var 2) 4) (.pow (.var 4) 3))))) (.add (.mul (.int 60) (.mul (.var 1) (.mul (.var 3) (.mul (.pow (.var 2) 3) (.pow (.var 4) 2))))) (.add (.mul (.int (-48)) (.mul (.var 0) (.mul (.var 1) (.mul (.pow (.var 2) 3) (.mul (.pow (.var 3) 3) (.pow (.var 4) 3)))))) (.add (.mul (.int (-48)) (.mul (.var 0) (.mul (.var 6) (.mul (.pow (.var 2) 3) (.mul (.pow (.var 3) 3) (.pow (.var 4) 3)))))) (.add (.mul (.int (-48)) (.mul (.var 1) (.mul (.var 6) (.mul (.var 2) (.mul (.pow (.var 3) 3) (.pow (.var 4) 3)))))) (.add (.mul (.int (-16)) (.mul (.var 6) (.mul (.var 2) (.mul (.pow (.var 0) 2) (.mul (.pow (.var 3) 5) (.pow (.var 4) 2)))))) (.add (.mul (.int (-12)) (.mul (.var 0) (.mul (.var 1) (.mul (.pow (.var 2) 2) (.mul (.pow (.var 3) 3) (.pow (.var 4) 2)))))) (.add (.mul (.int (-8)) (.mul (.var 0) (.mul (.var 6) (.mul (.pow (.var 2) 2) (.mul (.pow (.var 3) 3) (.pow (.var 4) 2)))))) (.add (.mul (.int 6) (.mul (.var 1) (.mul (.var 6) (.mul (.var 2) (.mul (.var 4) (.pow (.var 3) 2)))))) (.add (.mul (.int 8) (.mul (.var 0) (.mul (.var 6) (.mul (.var 2) (.mul (.var 4) (.pow (.var 3) 3)))))) (.add (.mul (.int 12) (.mul (.var 0) (.mul (.var 1) (.mul (.var 6) (.mul (.var 4) (.pow (.var 3) 4)))))) (.add (.mul (.int 12) (.mul (.var 6) (.mul (.var 2) (.mul (.pow (.var 1) 2) (.mul (.pow (.var 3) 3) (.pow (.var 4) 2)))))) (.add (.mul (.int 18) (.mul (.var 0) (.mul (.var 1) (.mul (.var 2) (.mul (.var 4) (.pow (.var 3) 3)))))) (.add (.mul (.int 24) (.mul (.var 6) (.mul (.pow (.var 0) 2) (.mul (.pow (.var 2) 2) (.mul (.pow (.var 3) 5) (.pow (.var 4) 3)))))) (.add (.mul (.int 24) (.mul (.var 6) (.mul (.pow (.var 1) 2) (.mul (.pow (.var 2) 2) (.mul (.pow (.var 3) 3) (.pow (.var 4) 3)))))) (.add (.mul (.int 36) (.mul (.var 1) (.mul (.var 6) (.mul (.pow (.var 2) 2) (.mul (.pow (.var 3) 2) (.pow (.var 4) 2)))))) (.add (.mul (.int 48) (.mul (.var 0) (.mul (.var 1) (.mul (.var 6) (.mul (.pow (.var 3) 5) (.pow (.var 4) 3)))))) (.add (.mul (.int 48) (.mul (.var 0) (.mul (.var 1) (.mul (.var 2) (.mul (.pow (.var 3) 4) (.pow (.var 4) 3)))))) (.add (.mul (.int 48) (.mul (.var 0) (.mul (.var 6) (.mul (.var 2) (.mul (.pow (.var 3) 4) (.pow (.var 4) 3)))))) (.add (.mul (.int 48) (.mul (.var 1) (.mul (.var 6) (.mul (.pow (.var 2) 3) (.mul (.pow (.var 3) 2) (.pow (.var 4) 3)))))) (.add (.mul (.int (-48)) (.mul (.var 0) (.mul (.var 1) (.mul (.var 6) (.mul (.pow (.var 2) 2) (.mul (.pow (.var 3) 4) (.pow (.var 4) 3))))))) (.mul (.int 4) (.mul (.var 0) (.mul (.var 1) (.mul (.var 6) (.mul (.var 2) (.mul (.pow (.var 3) 4) (.pow (.var 4) 2)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
theorem datadirection_5_0_binding : litdirectionExpr 5 0=datadirection_5_0 := rfl

def dataden_0_0 : RingExpr := (.add (.mul (.int (-8)) (.mul (.var 0) (.mul (.var 4) (.pow (.var 3) 4)))) (.add (.mul (.int 12) (.mul (.var 1) (.mul (.var 4) (.pow (.var 3) 3)))) (.add (.mul (.int 12) (.mul (.var 2) (.mul (.var 4) (.pow (.var 3) 2)))) (.add (.mul (.int 16) (.mul (.pow (.var 0) 2) (.mul (.pow (.var 3) 6) (.pow (.var 4) 2)))) (.add (.mul (.int 24) (.mul (.pow (.var 1) 2) (.mul (.pow (.var 3) 4) (.pow (.var 4) 2)))) (.add (.mul (.int 48) (.mul (.pow (.var 2) 2) (.mul (.pow (.var 3) 2) (.pow (.var 4) 2)))) (.add (.mul (.int 48) (.mul (.pow (.var 2) 3) (.mul (.pow (.var 3) 2) (.pow (.var 4) 3)))) (.add (.mul (.int (-96)) (.mul (.var 0) (.mul (.pow (.var 2) 2) (.mul (.pow (.var 3) 4) (.pow (.var 4) 3))))) (.add (.mul (.int (-64)) (.mul (.var 0) (.mul (.var 2) (.mul (.pow (.var 3) 4) (.pow (.var 4) 2))))) (.add (.mul (.int (-40)) (.mul (.var 0) (.mul (.var 1) (.mul (.pow (.var 3) 5) (.pow (.var 4) 2))))) (.add (.mul (.int (-24)) (.mul (.var 0) (.mul (.var 6) (.mul (.pow (.var 3) 5) (.pow (.var 4) 2))))) (.add (.mul (.int 24) (.mul (.var 1) (.mul (.var 6) (.mul (.pow (.var 3) 4) (.pow (.var 4) 2))))) (.add (.mul (.int 24) (.mul (.var 6) (.mul (.var 2) (.mul (.pow (.var 3) 3) (.pow (.var 4) 2))))) (.add (.mul (.int 48) (.mul (.var 6) (.mul (.pow (.var 0) 2) (.mul (.pow (.var 3) 7) (.pow (.var 4) 3))))) (.add (.mul (.int 48) (.mul (.var 6) (.mul (.pow (.var 1) 2) (.mul (.pow (.var 3) 5) (.pow (.var 4) 3))))) (.add (.mul (.int 48) (.mul (.var 6) (.mul (.pow (.var 2) 2) (.mul (.pow (.var 3) 3) (.pow (.var 4) 3))))) (.add (.mul (.int 48) (.mul (.var 2) (.mul (.pow (.var 0) 2) (.mul (.pow (.var 3) 6) (.pow (.var 4) 3))))) (.add (.mul (.int 48) (.mul (.var 2) (.mul (.pow (.var 1) 2) (.mul (.pow (.var 3) 4) (.pow (.var 4) 3))))) (.add (.mul (.int 72) (.mul (.var 1) (.mul (.var 2) (.mul (.pow (.var 3) 3) (.pow (.var 4) 2))))) (.add (.mul (.int 96) (.mul (.var 1) (.mul (.pow (.var 2) 2) (.mul (.pow (.var 3) 3) (.pow (.var 4) 3))))) (.add (.mul (.int (-96)) (.mul (.var 0) (.mul (.var 1) (.mul (.var 6) (.mul (.pow (.var 3) 6) (.pow (.var 4) 3)))))) (.add (.mul (.int (-96)) (.mul (.var 0) (.mul (.var 1) (.mul (.var 2) (.mul (.pow (.var 3) 5) (.pow (.var 4) 3)))))) (.add (.mul (.int (-96)) (.mul (.var 0) (.mul (.var 6) (.mul (.var 2) (.mul (.pow (.var 3) 5) (.pow (.var 4) 3)))))) (.mul (.int 96) (.mul (.var 1) (.mul (.var 6) (.mul (.var 2) (.mul (.pow (.var 3) 4) (.pow (.var 4) 3)))))))))))))))))))))))))))))
theorem dataden_0_0_binding : litdenExpr 0 0=dataden_0_0 := rfl

def datanu9_0_0 : RingExpr := (.var 11)
theorem datanu9_0_0_binding : litnu9Expr 0 0=datanu9_0_0 := rfl

def datanu9_1_0 : RingExpr := (.var 12)
theorem datanu9_1_0_binding : litnu9Expr 1 0=datanu9_1_0 := rfl

def datanu9_2_0 : RingExpr := (.var 15)
theorem datanu9_2_0_binding : litnu9Expr 2 0=datanu9_2_0 := rfl

def datanu9_3_0 : RingExpr := (.var 11)
theorem datanu9_3_0_binding : litnu9Expr 3 0=datanu9_3_0 := rfl

def datanu9_4_0 : RingExpr := (.var 12)
theorem datanu9_4_0_binding : litnu9Expr 4 0=datanu9_4_0 := rfl

def datanu9_5_0 : RingExpr := (.var 15)
theorem datanu9_5_0_binding : litnu9Expr 5 0=datanu9_5_0 := rfl

def datanu9_8_0 : RingExpr := (.int 1)
theorem datanu9_8_0_binding : litnu9Expr 8 0=datanu9_8_0 := rfl

def datanu19_0_0 : RingExpr := (.var 11)
theorem datanu19_0_0_binding : litnu19Expr 0 0=datanu19_0_0 := rfl

def datanu19_1_0 : RingExpr := (.var 12)
theorem datanu19_1_0_binding : litnu19Expr 1 0=datanu19_1_0 := rfl

def datanu19_2_0 : RingExpr := (.var 13)
theorem datanu19_2_0_binding : litnu19Expr 2 0=datanu19_2_0 := rfl

def datanu19_3_0 : RingExpr := (.var 14)
theorem datanu19_3_0_binding : litnu19Expr 3 0=datanu19_3_0 := rfl

def datanu19_4_0 : RingExpr := (.var 15)
theorem datanu19_4_0_binding : litnu19Expr 4 0=datanu19_4_0 := rfl

def datanu19_5_0 : RingExpr := (.var 16)
theorem datanu19_5_0_binding : litnu19Expr 5 0=datanu19_5_0 := rfl

def datanu19_6_0 : RingExpr := (.var 11)
theorem datanu19_6_0_binding : litnu19Expr 6 0=datanu19_6_0 := rfl

def datanu19_7_0 : RingExpr := (.var 12)
theorem datanu19_7_0_binding : litnu19Expr 7 0=datanu19_7_0 := rfl

def datanu19_8_0 : RingExpr := (.var 13)
theorem datanu19_8_0_binding : litnu19Expr 8 0=datanu19_8_0 := rfl

def datanu19_9_0 : RingExpr := (.var 14)
theorem datanu19_9_0_binding : litnu19Expr 9 0=datanu19_9_0 := rfl

def datanu19_10_0 : RingExpr := (.var 15)
theorem datanu19_10_0_binding : litnu19Expr 10 0=datanu19_10_0 := rfl

def datanu19_11_0 : RingExpr := (.var 16)
theorem datanu19_11_0_binding : litnu19Expr 11 0=datanu19_11_0 := rfl

def datanu19_18_0 : RingExpr := (.int 1)
theorem datanu19_18_0_binding : litnu19Expr 18 0=datanu19_18_0 := rfl

def datasection_0_0 : RingExpr := (.int 1)
theorem datasection_0_0_binding : litsectionExpr 0 0=datasection_0_0 := rfl

def datasection_1_1 : RingExpr := (.int 1)
theorem datasection_1_1_binding : litsectionExpr 1 1=datasection_1_1 := rfl

def datasection_2_4 : RingExpr := (.int 1)
theorem datasection_2_4_binding : litsectionExpr 2 4=datasection_2_4 := rfl

def datasection_3_6 : RingExpr := (.int 1)
theorem datasection_3_6_binding : litsectionExpr 3 6=datasection_3_6 := rfl

def datasection_4_7 : RingExpr := (.int 1)
theorem datasection_4_7_binding : litsectionExpr 4 7=datasection_4_7 := rfl

def datasection_5_10 : RingExpr := (.int 1)
theorem datasection_5_10_binding : litsectionExpr 5 10=datasection_5_10 := rfl

def datasection_6_12 : RingExpr := (.int 1)
theorem datasection_6_12_binding : litsectionExpr 6 12=datasection_6_12 := rfl

def datasection_7_13 : RingExpr := (.int 1)
theorem datasection_7_13_binding : litsectionExpr 7 13=datasection_7_13 := rfl

def datasection_8_18 : RingExpr := (.int 1)
theorem datasection_8_18_binding : litsectionExpr 8 18=datasection_8_18 := rfl

def dataN19z_0_9 : RingExpr := (.int 1)
theorem dataN19z_0_9_binding : litN19zExpr 0 9=dataN19z_0_9 := rfl

def dataN19z_1_11 : RingExpr := (.int 1)
theorem dataN19z_1_11_binding : litN19zExpr 1 11=dataN19z_1_11 := rfl

def dataN19z_2_6 : RingExpr := (.mul (.var 10) (.mul (.var 8) (.add (.int (-3)) (.add (.mul (.int 2) (.var 5)) (.add (.mul (.int 6) (.mul (.var 2) (.var 4))) (.add (.mul (.int (-6)) (.mul (.var 0) (.mul (.var 4) (.pow (.var 3) 2)))) (.mul (.int 6) (.mul (.var 1) (.mul (.var 3) (.var 4))))))))))
theorem dataN19z_2_6_binding : litN19zExpr 2 6=dataN19z_2_6 := rfl

def dataN19z_2_7 : RingExpr := (.mul (.var 10) (.mul (.var 8) (.add (.mul (.int (-3)) (.var 2)) (.add (.mul (.int 2) (.mul (.var 5) (.var 2))) (.add (.mul (.int 6) (.mul (.var 4) (.pow (.var 2) 2))) (.add (.mul (.int (-6)) (.mul (.var 0) (.mul (.var 2) (.mul (.var 4) (.pow (.var 3) 2))))) (.mul (.int 6) (.mul (.var 1) (.mul (.var 2) (.mul (.var 3) (.var 4)))))))))))
theorem dataN19z_2_7_binding : litN19zExpr 2 7=dataN19z_2_7 := rfl

def dataN19z_2_9 : RingExpr := (.mul (.var 10) (.mul (.var 8) (.add (.mul (.int (-3)) (.var 2)) (.add (.mul (.int (-6)) (.mul (.var 4) (.pow (.var 2) 2))) (.add (.mul (.int (-3)) (.mul (.var 1) (.var 3))) (.add (.mul (.int (-6)) (.mul (.var 1) (.mul (.var 2) (.mul (.var 3) (.var 4))))) (.mul (.int 6) (.mul (.var 0) (.mul (.var 2) (.mul (.var 4) (.pow (.var 3) 2)))))))))))
theorem dataN19z_2_9_binding : litN19zExpr 2 9=dataN19z_2_9 := rfl

def dataN19z_2_10 : RingExpr := (.add (.mul (.int (-3)) (.pow (.var 10) 1)) (.add (.var 5) (.add (.mul (.int 3) (.mul (.var 2) (.var 4))) (.add (.mul (.int (-3)) (.mul (.var 0) (.mul (.var 4) (.pow (.var 3) 2)))) (.mul (.int 3) (.mul (.var 1) (.mul (.var 3) (.var 4))))))))
theorem dataN19z_2_10_binding : litN19zExpr 2 10=dataN19z_2_10 := rfl

def dataN19z_2_11 : RingExpr := (.add (.mul (.int (3)) (.pow (.var 10) 1)) (.add (.mul (.int (-3)) (.mul (.var 2) (.var 4))) (.add (.mul (.int (-3)) (.mul (.var 1) (.mul (.var 3) (.var 4)))) (.mul (.int 3) (.mul (.var 0) (.mul (.var 4) (.pow (.var 3) 2)))))))
theorem dataN19z_2_11_binding : litN19zExpr 2 11=dataN19z_2_11 := rfl

def dataN19z_3_6 : RingExpr := (.mul (.var 10) (.mul (.var 8) (.add (.int (-1)) (.add (.mul (.int (-2)) (.mul (.var 2) (.var 4))) (.mul (.int (-2)) (.mul (.var 0) (.mul (.var 4) (.pow (.var 3) 2))))))))
theorem dataN19z_3_6_binding : litN19zExpr 3 6=dataN19z_3_6 := rfl

def dataN19z_3_7 : RingExpr := (.mul (.var 10) (.mul (.var 8) (.add (.mul (.int (-1)) (.var 2)) (.add (.mul (.int (-2)) (.mul (.var 4) (.pow (.var 2) 2))) (.mul (.int (-2)) (.mul (.var 0) (.mul (.var 2) (.mul (.var 4) (.pow (.var 3) 2)))))))))
theorem dataN19z_3_7_binding : litN19zExpr 3 7=dataN19z_3_7 := rfl

def dataN19z_3_9 : RingExpr := (.mul (.var 10) (.mul (.var 8) (.add (.mul (.int (-1)) (.var 2)) (.add (.mul (.int (-1)) (.mul (.var 1) (.var 3))) (.add (.mul (.int (-2)) (.mul (.var 4) (.pow (.var 2) 2))) (.add (.mul (.int (-2)) (.mul (.var 1) (.mul (.var 2) (.mul (.var 3) (.var 4))))) (.mul (.int 2) (.mul (.var 0) (.mul (.var 2) (.mul (.var 4) (.pow (.var 3) 2)))))))))))
theorem dataN19z_3_9_binding : litN19zExpr 3 9=dataN19z_3_9 := rfl

def dataN19z_3_10 : RingExpr := (.add (.mul (.int (-1)) (.pow (.var 10) 1)) (.add (.mul (.int (-1)) (.mul (.var 2) (.var 4))) (.mul (.int (-1)) (.mul (.var 0) (.mul (.var 4) (.pow (.var 3) 2))))))
theorem dataN19z_3_10_binding : litN19zExpr 3 10=dataN19z_3_10 := rfl

def dataN19z_3_11 : RingExpr := (.add (.mul (.int (1)) (.pow (.var 10) 1)) (.add (.mul (.int (-1)) (.mul (.var 2) (.var 4))) (.add (.mul (.var 0) (.mul (.var 4) (.pow (.var 3) 2))) (.mul (.int (-1)) (.mul (.var 1) (.mul (.var 3) (.var 4)))))))
theorem dataN19z_3_11_binding : litN19zExpr 3 11=dataN19z_3_11 := rfl

def dataN19z_4_6 : RingExpr := (.var 0)
theorem dataN19z_4_6_binding : litN19zExpr 4 6=dataN19z_4_6 := rfl

def dataN19z_4_7 : RingExpr := (.mul (.var 0) (.var 2))
theorem dataN19z_4_7_binding : litN19zExpr 4 7=dataN19z_4_7 := rfl

def dataN19z_4_9 : RingExpr := (.mul (.var 10) (.mul (.var 9) (.mul (.pow (.var 8) 2) (.add (.var 2) (.add (.mul (.var 1) (.var 3)) (.add (.mul (.int (-2)) (.mul (.var 3) (.var 4))) (.add (.mul (.int 2) (.mul (.var 4) (.pow (.var 2) 2))) (.add (.mul (.int (-2)) (.mul (.var 0) (.mul (.var 2) (.mul (.var 4) (.pow (.var 3) 2))))) (.mul (.int 2) (.mul (.var 1) (.mul (.var 2) (.mul (.var 3) (.var 4)))))))))))))
theorem dataN19z_4_9_binding : litN19zExpr 4 9=dataN19z_4_9 := rfl

def dataN19z_4_10 : RingExpr := (.mul (.var 0) (.var 3))
theorem dataN19z_4_10_binding : litN19zExpr 4 10=dataN19z_4_10 := rfl

def dataN19z_4_11 : RingExpr := (.add (.var 1) (.mul (.int (-1)) (.mul (.var 0) (.var 3))))
theorem dataN19z_4_11_binding : litN19zExpr 4 11=dataN19z_4_11 := rfl

def dataN19z_5_6 : RingExpr := (.mul (.var 10) (.mul (.pow (.var 8) 2) (.add (.var 2) (.add (.mul (.int (-2)) (.mul (.var 3) (.var 4))) (.add (.mul (.int 2) (.mul (.var 0) (.pow (.var 3) 2))) (.add (.mul (.int 2) (.mul (.var 4) (.pow (.var 2) 2))) (.mul (.int 2) (.mul (.var 0) (.mul (.var 2) (.mul (.var 4) (.pow (.var 3) 2)))))))))))
theorem dataN19z_5_6_binding : litN19zExpr 5 6=dataN19z_5_6 := rfl

def dataN19z_5_7 : RingExpr := (.mul (.var 10) (.mul (.pow (.var 8) 2) (.add (.pow (.var 2) 2) (.add (.mul (.int 2) (.mul (.var 4) (.pow (.var 2) 3))) (.add (.mul (.int (-2)) (.mul (.var 2) (.mul (.var 3) (.var 4)))) (.add (.mul (.int 2) (.mul (.var 0) (.mul (.var 2) (.pow (.var 3) 2)))) (.mul (.int 2) (.mul (.var 0) (.mul (.var 4) (.mul (.pow (.var 2) 2) (.pow (.var 3) 2)))))))))))
theorem dataN19z_5_7_binding : litN19zExpr 5 7=dataN19z_5_7 := rfl

def dataN19z_5_9 : RingExpr := (.mul (.var 10) (.mul (.var 9) (.mul (.pow (.var 8) 2) (.add (.var 2) (.add (.mul (.var 1) (.var 3)) (.add (.mul (.int (-1)) (.mul (.var 3) (.var 4))) (.add (.mul (.int 2) (.mul (.pow (.var 2) 3) (.pow (.var 4) 2))) (.add (.mul (.int 3) (.mul (.var 4) (.pow (.var 2) 2))) (.add (.mul (.int (-2)) (.mul (.var 0) (.mul (.var 2) (.mul (.var 4) (.pow (.var 3) 2))))) (.add (.mul (.int (-2)) (.mul (.var 0) (.mul (.pow (.var 2) 2) (.mul (.pow (.var 3) 2) (.pow (.var 4) 2))))) (.add (.mul (.int 2) (.mul (.var 1) (.mul (.var 3) (.mul (.pow (.var 2) 2) (.pow (.var 4) 2))))) (.mul (.int 3) (.mul (.var 1) (.mul (.var 2) (.mul (.var 3) (.var 4))))))))))))))))
theorem dataN19z_5_9_binding : litN19zExpr 5 9=dataN19z_5_9 := rfl

def dataN19z_5_10 : RingExpr := (.mul (.var 10) (.mul (.var 8) (.add (.var 2) (.add (.mul (.int (-2)) (.mul (.var 3) (.var 4))) (.add (.mul (.int 2) (.mul (.var 0) (.pow (.var 3) 2))) (.add (.mul (.int 2) (.mul (.var 4) (.pow (.var 2) 2))) (.mul (.int 2) (.mul (.var 0) (.mul (.var 2) (.mul (.var 4) (.pow (.var 3) 2)))))))))))
theorem dataN19z_5_10_binding : litN19zExpr 5 10=dataN19z_5_10 := rfl

def dataN19z_5_11 : RingExpr := (.mul (.var 10) (.mul (.var 8) (.add (.var 2) (.add (.mul (.int (-2)) (.mul (.var 0) (.pow (.var 3) 2))) (.add (.mul (.int 2) (.mul (.var 1) (.var 3))) (.add (.mul (.int 2) (.mul (.var 4) (.pow (.var 2) 2))) (.add (.mul (.int (-2)) (.mul (.var 0) (.mul (.var 2) (.mul (.var 4) (.pow (.var 3) 2))))) (.mul (.int 2) (.mul (.var 1) (.mul (.var 2) (.mul (.var 3) (.var 4))))))))))))
theorem dataN19z_5_11_binding : litN19zExpr 5 11=dataN19z_5_11 := rfl

def dataN19z_6_18 : RingExpr := (.var 14)
theorem dataN19z_6_18_binding : litN19zExpr 6 18=dataN19z_6_18 := rfl

def dataN19z_7_18 : RingExpr := (.var 16)
theorem dataN19z_7_18_binding : litN19zExpr 7 18=dataN19z_7_18 := rfl

def dataN19z_8_18 : RingExpr := (.mul (.var 10) (.mul (.var 8) (.add (.mul (.int (-3)) (.var 11)) (.add (.mul (.int (-3)) (.mul (.var 12) (.var 2))) (.add (.mul (.int (-3)) (.mul (.var 14) (.var 2))) (.add (.mul (.int (-3)) (.mul (.var 15) (.var 3))) (.add (.mul (.int 2) (.mul (.var 11) (.var 5))) (.add (.mul (.int 3) (.mul (.var 16) (.var 3))) (.add (.mul (.int (-6)) (.mul (.var 14) (.mul (.var 4) (.pow (.var 2) 2)))) (.add (.mul (.int (-3)) (.mul (.var 14) (.mul (.var 1) (.var 3)))) (.add (.mul (.int 2) (.mul (.var 12) (.mul (.var 5) (.var 2)))) (.add (.mul (.int 2) (.mul (.var 15) (.mul (.var 5) (.var 3)))) (.add (.mul (.int 6) (.mul (.var 11) (.mul (.var 2) (.var 4)))) (.add (.mul (.int 6) (.mul (.var 12) (.mul (.var 4) (.pow (.var 2) 2)))) (.add (.mul (.int (-6)) (.mul (.var 11) (.mul (.var 0) (.mul (.var 4) (.pow (.var 3) 2))))) (.add (.mul (.int (-6)) (.mul (.var 15) (.mul (.var 0) (.mul (.var 4) (.pow (.var 3) 3))))) (.add (.mul (.int (-6)) (.mul (.var 16) (.mul (.var 1) (.mul (.var 4) (.pow (.var 3) 2))))) (.add (.mul (.int (-6)) (.mul (.var 16) (.mul (.var 2) (.mul (.var 3) (.var 4))))) (.add (.mul (.int 6) (.mul (.var 11) (.mul (.var 1) (.mul (.var 3) (.var 4))))) (.add (.mul (.int 6) (.mul (.var 15) (.mul (.var 1) (.mul (.var 4) (.pow (.var 3) 2))))) (.add (.mul (.int 6) (.mul (.var 15) (.mul (.var 2) (.mul (.var 3) (.var 4))))) (.add (.mul (.int 6) (.mul (.var 16) (.mul (.var 0) (.mul (.var 4) (.pow (.var 3) 3))))) (.add (.mul (.int (-6)) (.mul (.var 12) (.mul (.var 0) (.mul (.var 2) (.mul (.var 4) (.pow (.var 3) 2)))))) (.add (.mul (.int (-6)) (.mul (.var 14) (.mul (.var 1) (.mul (.var 2) (.mul (.var 3) (.var 4)))))) (.add (.mul (.int 6) (.mul (.var 12) (.mul (.var 1) (.mul (.var 2) (.mul (.var 3) (.var 4)))))) (.mul (.int 6) (.mul (.var 14) (.mul (.var 0) (.mul (.var 2) (.mul (.var 4) (.pow (.var 3) 2)))))))))))))))))))))))))))))))
theorem dataN19z_8_18_binding : litN19zExpr 8 18=dataN19z_8_18 := rfl

def dataN19z_9_18 : RingExpr := (.mul (.var 10) (.mul (.var 8) (.add (.mul (.int (-1)) (.var 11)) (.add (.mul (.var 16) (.var 3)) (.add (.mul (.int (-1)) (.mul (.var 12) (.var 2))) (.add (.mul (.int (-1)) (.mul (.var 14) (.var 2))) (.add (.mul (.int (-1)) (.mul (.var 15) (.var 3))) (.add (.mul (.int (-1)) (.mul (.var 14) (.mul (.var 1) (.var 3)))) (.add (.mul (.int (-2)) (.mul (.var 11) (.mul (.var 2) (.var 4)))) (.add (.mul (.int (-2)) (.mul (.var 12) (.mul (.var 4) (.pow (.var 2) 2)))) (.add (.mul (.int (-2)) (.mul (.var 14) (.mul (.var 4) (.pow (.var 2) 2)))) (.add (.mul (.int (-2)) (.mul (.var 11) (.mul (.var 0) (.mul (.var 4) (.pow (.var 3) 2))))) (.add (.mul (.int (-2)) (.mul (.var 15) (.mul (.var 0) (.mul (.var 4) (.pow (.var 3) 3))))) (.add (.mul (.int (-2)) (.mul (.var 15) (.mul (.var 2) (.mul (.var 3) (.var 4))))) (.add (.mul (.int (-2)) (.mul (.var 16) (.mul (.var 1) (.mul (.var 4) (.pow (.var 3) 2))))) (.add (.mul (.int (-2)) (.mul (.var 16) (.mul (.var 2) (.mul (.var 3) (.var 4))))) (.add (.mul (.int 2) (.mul (.var 16) (.mul (.var 0) (.mul (.var 4) (.pow (.var 3) 3))))) (.add (.mul (.int (-2)) (.mul (.var 12) (.mul (.var 0) (.mul (.var 2) (.mul (.var 4) (.pow (.var 3) 2)))))) (.add (.mul (.int (-2)) (.mul (.var 14) (.mul (.var 1) (.mul (.var 2) (.mul (.var 3) (.var 4)))))) (.mul (.int 2) (.mul (.var 14) (.mul (.var 0) (.mul (.var 2) (.mul (.var 4) (.pow (.var 3) 2)))))))))))))))))))))))))
theorem dataN19z_9_18_binding : litN19zExpr 9 18=dataN19z_9_18 := rfl

def dataN19z_10_18 : RingExpr := (.mul (.var 10) (.mul (.var 9) (.mul (.pow (.var 8) 2) (.add (.mul (.var 14) (.var 2)) (.add (.mul (.var 14) (.mul (.var 1) (.var 3))) (.add (.mul (.int (-2)) (.mul (.var 14) (.mul (.var 3) (.var 4)))) (.add (.mul (.int 2) (.mul (.var 14) (.mul (.var 4) (.pow (.var 2) 2)))) (.add (.mul (.int (-2)) (.mul (.var 16) (.mul (.var 0) (.mul (.var 4) (.pow (.var 3) 3))))) (.add (.mul (.int 2) (.mul (.var 11) (.mul (.var 0) (.mul (.var 4) (.pow (.var 3) 2))))) (.add (.mul (.int 2) (.mul (.var 15) (.mul (.var 0) (.mul (.var 4) (.pow (.var 3) 3))))) (.add (.mul (.int 2) (.mul (.var 16) (.mul (.var 1) (.mul (.var 4) (.pow (.var 3) 2))))) (.add (.mul (.int (-2)) (.mul (.var 14) (.mul (.var 0) (.mul (.var 2) (.mul (.var 4) (.pow (.var 3) 2)))))) (.add (.mul (.int 2) (.mul (.var 12) (.mul (.var 0) (.mul (.var 2) (.mul (.var 4) (.pow (.var 3) 2)))))) (.mul (.int 2) (.mul (.var 14) (.mul (.var 1) (.mul (.var 2) (.mul (.var 3) (.var 4)))))))))))))))))))
theorem dataN19z_10_18_binding : litN19zExpr 10 18=dataN19z_10_18 := rfl

def dataN19z_11_18 : RingExpr := (.mul (.var 10) (.mul (.var 9) (.mul (.pow (.var 8) 2) (.add (.mul (.var 14) (.var 2)) (.add (.mul (.var 11) (.mul (.var 2) (.var 4))) (.add (.mul (.var 12) (.mul (.var 4) (.pow (.var 2) 2))) (.add (.mul (.var 14) (.mul (.var 1) (.var 3))) (.add (.mul (.int (-1)) (.mul (.var 14) (.mul (.var 3) (.var 4)))) (.add (.mul (.int (-2)) (.mul (.var 11) (.mul (.var 3) (.pow (.var 4) 2)))) (.add (.mul (.int (-2)) (.mul (.var 15) (.mul (.pow (.var 3) 2) (.pow (.var 4) 2)))) (.add (.mul (.int 2) (.mul (.var 11) (.mul (.pow (.var 2) 2) (.pow (.var 4) 2)))) (.add (.mul (.int 2) (.mul (.var 12) (.mul (.pow (.var 2) 3) (.pow (.var 4) 2)))) (.add (.mul (.int 2) (.mul (.var 14) (.mul (.pow (.var 2) 3) (.pow (.var 4) 2)))) (.add (.mul (.int 3) (.mul (.var 14) (.mul (.var 4) (.pow (.var 2) 2)))) (.add (.mul (.var 15) (.mul (.var 2) (.mul (.var 3) (.var 4)))) (.add (.mul (.var 16) (.mul (.var 2) (.mul (.var 3) (.var 4)))) (.add (.mul (.int (-2)) (.mul (.var 12) (.mul (.var 2) (.mul (.var 3) (.pow (.var 4) 2))))) (.add (.mul (.int (-2)) (.mul (.var 16) (.mul (.var 0) (.mul (.var 4) (.pow (.var 3) 3))))) (.add (.mul (.int 2) (.mul (.var 11) (.mul (.var 0) (.mul (.var 4) (.pow (.var 3) 2))))) (.add (.mul (.int 2) (.mul (.var 15) (.mul (.var 0) (.mul (.var 4) (.pow (.var 3) 3))))) (.add (.mul (.int 2) (.mul (.var 15) (.mul (.var 3) (.mul (.pow (.var 2) 2) (.pow (.var 4) 2))))) (.add (.mul (.int 2) (.mul (.var 16) (.mul (.var 1) (.mul (.var 4) (.pow (.var 3) 2))))) (.add (.mul (.int 2) (.mul (.var 16) (.mul (.var 3) (.mul (.pow (.var 2) 2) (.pow (.var 4) 2))))) (.add (.mul (.int (-2)) (.mul (.var 14) (.mul (.var 0) (.mul (.var 2) (.mul (.var 4) (.pow (.var 3) 2)))))) (.add (.mul (.int (-2)) (.mul (.var 14) (.mul (.var 0) (.mul (.pow (.var 2) 2) (.mul (.pow (.var 3) 2) (.pow (.var 4) 2)))))) (.add (.mul (.int (-2)) (.mul (.var 16) (.mul (.var 0) (.mul (.var 2) (.mul (.pow (.var 3) 3) (.pow (.var 4) 2)))))) (.add (.mul (.int 2) (.mul (.var 11) (.mul (.var 0) (.mul (.var 2) (.mul (.pow (.var 3) 2) (.pow (.var 4) 2)))))) (.add (.mul (.int 2) (.mul (.var 12) (.mul (.var 0) (.mul (.var 2) (.mul (.var 4) (.pow (.var 3) 2)))))) (.add (.mul (.int 2) (.mul (.var 12) (.mul (.var 0) (.mul (.pow (.var 2) 2) (.mul (.pow (.var 3) 2) (.pow (.var 4) 2)))))) (.add (.mul (.int 2) (.mul (.var 14) (.mul (.var 1) (.mul (.var 3) (.mul (.pow (.var 2) 2) (.pow (.var 4) 2)))))) (.add (.mul (.int 2) (.mul (.var 15) (.mul (.var 0) (.mul (.var 2) (.mul (.pow (.var 3) 3) (.pow (.var 4) 2)))))) (.add (.mul (.int 2) (.mul (.var 16) (.mul (.var 1) (.mul (.var 2) (.mul (.pow (.var 3) 2) (.pow (.var 4) 2)))))) (.mul (.int 3) (.mul (.var 14) (.mul (.var 1) (.mul (.var 2) (.mul (.var 3) (.var 4))))))))))))))))))))))))))))))))))))))
theorem dataN19z_11_18_binding : litN19zExpr 11 18=dataN19z_11_18 := rfl

def dataN19b_0_3 : RingExpr := (.int 1)
theorem dataN19b_0_3_binding : litN19bExpr 0 3=dataN19b_0_3 := rfl

def dataN19b_0_15 : RingExpr := (.int 1)
theorem dataN19b_0_15_binding : litN19bExpr 0 15=dataN19b_0_15 := rfl

def dataN19b_1_5 : RingExpr := (.int 1)
theorem dataN19b_1_5_binding : litN19bExpr 1 5=dataN19b_1_5 := rfl

def dataN19b_1_17 : RingExpr := (.int 1)
theorem dataN19b_1_17_binding : litN19bExpr 1 17=dataN19b_1_17 := rfl

def dataN19b_2_0 : RingExpr := (.mul (.var 10) (.mul (.var 8) (.add (.int (-3)) (.add (.mul (.int 2) (.var 5)) (.add (.mul (.int 6) (.mul (.var 2) (.var 4))) (.add (.mul (.int (-6)) (.mul (.var 0) (.mul (.var 4) (.pow (.var 3) 2)))) (.mul (.int 6) (.mul (.var 1) (.mul (.var 3) (.var 4))))))))))
theorem dataN19b_2_0_binding : litN19bExpr 2 0=dataN19b_2_0 := rfl

def dataN19b_2_1 : RingExpr := (.mul (.var 10) (.mul (.var 8) (.add (.mul (.int (-3)) (.var 2)) (.add (.mul (.int 2) (.mul (.var 5) (.var 2))) (.add (.mul (.int 6) (.mul (.var 4) (.pow (.var 2) 2))) (.add (.mul (.int (-6)) (.mul (.var 0) (.mul (.var 2) (.mul (.var 4) (.pow (.var 3) 2))))) (.mul (.int 6) (.mul (.var 1) (.mul (.var 2) (.mul (.var 3) (.var 4)))))))))))
theorem dataN19b_2_1_binding : litN19bExpr 2 1=dataN19b_2_1 := rfl

def dataN19b_2_3 : RingExpr := (.mul (.var 10) (.mul (.var 8) (.add (.mul (.int (-3)) (.var 2)) (.add (.mul (.int (-6)) (.mul (.var 4) (.pow (.var 2) 2))) (.add (.mul (.int (-3)) (.mul (.var 1) (.var 3))) (.add (.mul (.int (-6)) (.mul (.var 1) (.mul (.var 2) (.mul (.var 3) (.var 4))))) (.mul (.int 6) (.mul (.var 0) (.mul (.var 2) (.mul (.var 4) (.pow (.var 3) 2)))))))))))
theorem dataN19b_2_3_binding : litN19bExpr 2 3=dataN19b_2_3 := rfl

def dataN19b_2_4 : RingExpr := (.add (.mul (.int (-3)) (.pow (.var 10) 1)) (.add (.var 5) (.add (.mul (.int 3) (.mul (.var 2) (.var 4))) (.add (.mul (.int (-3)) (.mul (.var 0) (.mul (.var 4) (.pow (.var 3) 2)))) (.mul (.int 3) (.mul (.var 1) (.mul (.var 3) (.var 4))))))))
theorem dataN19b_2_4_binding : litN19bExpr 2 4=dataN19b_2_4 := rfl

def dataN19b_2_5 : RingExpr := (.add (.mul (.int (3)) (.pow (.var 10) 1)) (.add (.mul (.int (-3)) (.mul (.var 2) (.var 4))) (.add (.mul (.int (-3)) (.mul (.var 1) (.mul (.var 3) (.var 4)))) (.mul (.int 3) (.mul (.var 0) (.mul (.var 4) (.pow (.var 3) 2)))))))
theorem dataN19b_2_5_binding : litN19bExpr 2 5=dataN19b_2_5 := rfl

def dataN19b_2_12 : RingExpr := (.mul (.var 10) (.mul (.var 8) (.add (.int (-3)) (.add (.mul (.int 2) (.var 5)) (.add (.mul (.int 6) (.mul (.var 2) (.var 4))) (.add (.mul (.int (-6)) (.mul (.var 0) (.mul (.var 4) (.pow (.var 3) 2)))) (.mul (.int 6) (.mul (.var 1) (.mul (.var 3) (.var 4))))))))))
theorem dataN19b_2_12_binding : litN19bExpr 2 12=dataN19b_2_12 := rfl

def dataN19b_2_13 : RingExpr := (.mul (.var 10) (.mul (.var 8) (.add (.mul (.int (-3)) (.var 2)) (.add (.mul (.int 2) (.mul (.var 5) (.var 2))) (.add (.mul (.int 6) (.mul (.var 4) (.pow (.var 2) 2))) (.add (.mul (.int (-6)) (.mul (.var 0) (.mul (.var 2) (.mul (.var 4) (.pow (.var 3) 2))))) (.mul (.int 6) (.mul (.var 1) (.mul (.var 2) (.mul (.var 3) (.var 4)))))))))))
theorem dataN19b_2_13_binding : litN19bExpr 2 13=dataN19b_2_13 := rfl

def dataN19b_2_15 : RingExpr := (.mul (.var 10) (.mul (.var 8) (.add (.mul (.int (-3)) (.var 2)) (.add (.mul (.int (-6)) (.mul (.var 4) (.pow (.var 2) 2))) (.add (.mul (.int (-3)) (.mul (.var 1) (.var 3))) (.add (.mul (.int (-6)) (.mul (.var 1) (.mul (.var 2) (.mul (.var 3) (.var 4))))) (.mul (.int 6) (.mul (.var 0) (.mul (.var 2) (.mul (.var 4) (.pow (.var 3) 2)))))))))))
theorem dataN19b_2_15_binding : litN19bExpr 2 15=dataN19b_2_15 := rfl

def dataN19b_2_16 : RingExpr := (.add (.mul (.int (-3)) (.pow (.var 10) 1)) (.add (.var 5) (.add (.mul (.int 3) (.mul (.var 2) (.var 4))) (.add (.mul (.int (-3)) (.mul (.var 0) (.mul (.var 4) (.pow (.var 3) 2)))) (.mul (.int 3) (.mul (.var 1) (.mul (.var 3) (.var 4))))))))
theorem dataN19b_2_16_binding : litN19bExpr 2 16=dataN19b_2_16 := rfl

def dataN19b_2_17 : RingExpr := (.add (.mul (.int (3)) (.pow (.var 10) 1)) (.add (.mul (.int (-3)) (.mul (.var 2) (.var 4))) (.add (.mul (.int (-3)) (.mul (.var 1) (.mul (.var 3) (.var 4)))) (.mul (.int 3) (.mul (.var 0) (.mul (.var 4) (.pow (.var 3) 2)))))))
theorem dataN19b_2_17_binding : litN19bExpr 2 17=dataN19b_2_17 := rfl

def dataN19b_3_0 : RingExpr := (.mul (.var 10) (.mul (.var 8) (.add (.int (-1)) (.add (.mul (.int (-2)) (.mul (.var 2) (.var 4))) (.mul (.int (-2)) (.mul (.var 0) (.mul (.var 4) (.pow (.var 3) 2))))))))
theorem dataN19b_3_0_binding : litN19bExpr 3 0=dataN19b_3_0 := rfl

def dataN19b_3_1 : RingExpr := (.mul (.var 10) (.mul (.var 8) (.add (.mul (.int (-1)) (.var 2)) (.add (.mul (.int (-2)) (.mul (.var 4) (.pow (.var 2) 2))) (.mul (.int (-2)) (.mul (.var 0) (.mul (.var 2) (.mul (.var 4) (.pow (.var 3) 2)))))))))
theorem dataN19b_3_1_binding : litN19bExpr 3 1=dataN19b_3_1 := rfl

def dataN19b_3_3 : RingExpr := (.mul (.var 10) (.mul (.var 8) (.add (.mul (.int (-1)) (.var 2)) (.add (.mul (.int (-1)) (.mul (.var 1) (.var 3))) (.add (.mul (.int (-2)) (.mul (.var 4) (.pow (.var 2) 2))) (.add (.mul (.int (-2)) (.mul (.var 1) (.mul (.var 2) (.mul (.var 3) (.var 4))))) (.mul (.int 2) (.mul (.var 0) (.mul (.var 2) (.mul (.var 4) (.pow (.var 3) 2)))))))))))
theorem dataN19b_3_3_binding : litN19bExpr 3 3=dataN19b_3_3 := rfl

def dataN19b_3_4 : RingExpr := (.add (.mul (.int (-1)) (.pow (.var 10) 1)) (.add (.mul (.int (-1)) (.mul (.var 2) (.var 4))) (.mul (.int (-1)) (.mul (.var 0) (.mul (.var 4) (.pow (.var 3) 2))))))
theorem dataN19b_3_4_binding : litN19bExpr 3 4=dataN19b_3_4 := rfl

def dataN19b_3_5 : RingExpr := (.add (.mul (.int (1)) (.pow (.var 10) 1)) (.add (.mul (.int (-1)) (.mul (.var 2) (.var 4))) (.add (.mul (.var 0) (.mul (.var 4) (.pow (.var 3) 2))) (.mul (.int (-1)) (.mul (.var 1) (.mul (.var 3) (.var 4)))))))
theorem dataN19b_3_5_binding : litN19bExpr 3 5=dataN19b_3_5 := rfl

def dataN19b_3_12 : RingExpr := (.mul (.var 10) (.mul (.var 8) (.add (.int (-1)) (.add (.mul (.int (-2)) (.mul (.var 2) (.var 4))) (.mul (.int (-2)) (.mul (.var 0) (.mul (.var 4) (.pow (.var 3) 2))))))))
theorem dataN19b_3_12_binding : litN19bExpr 3 12=dataN19b_3_12 := rfl

def dataN19b_3_13 : RingExpr := (.mul (.var 10) (.mul (.var 8) (.add (.mul (.int (-1)) (.var 2)) (.add (.mul (.int (-2)) (.mul (.var 4) (.pow (.var 2) 2))) (.mul (.int (-2)) (.mul (.var 0) (.mul (.var 2) (.mul (.var 4) (.pow (.var 3) 2)))))))))
theorem dataN19b_3_13_binding : litN19bExpr 3 13=dataN19b_3_13 := rfl

def dataN19b_3_15 : RingExpr := (.mul (.var 10) (.mul (.var 8) (.add (.mul (.int (-1)) (.var 2)) (.add (.mul (.int (-1)) (.mul (.var 1) (.var 3))) (.add (.mul (.int (-2)) (.mul (.var 4) (.pow (.var 2) 2))) (.add (.mul (.int (-2)) (.mul (.var 1) (.mul (.var 2) (.mul (.var 3) (.var 4))))) (.mul (.int 2) (.mul (.var 0) (.mul (.var 2) (.mul (.var 4) (.pow (.var 3) 2)))))))))))
theorem dataN19b_3_15_binding : litN19bExpr 3 15=dataN19b_3_15 := rfl

def dataN19b_3_16 : RingExpr := (.add (.mul (.int (-1)) (.pow (.var 10) 1)) (.add (.mul (.int (-1)) (.mul (.var 2) (.var 4))) (.mul (.int (-1)) (.mul (.var 0) (.mul (.var 4) (.pow (.var 3) 2))))))
theorem dataN19b_3_16_binding : litN19bExpr 3 16=dataN19b_3_16 := rfl

def dataN19b_3_17 : RingExpr := (.add (.mul (.int (1)) (.pow (.var 10) 1)) (.add (.mul (.int (-1)) (.mul (.var 2) (.var 4))) (.add (.mul (.var 0) (.mul (.var 4) (.pow (.var 3) 2))) (.mul (.int (-1)) (.mul (.var 1) (.mul (.var 3) (.var 4)))))))
theorem dataN19b_3_17_binding : litN19bExpr 3 17=dataN19b_3_17 := rfl

def dataN19b_4_0 : RingExpr := (.var 0)
theorem dataN19b_4_0_binding : litN19bExpr 4 0=dataN19b_4_0 := rfl

def dataN19b_4_1 : RingExpr := (.mul (.var 0) (.var 2))
theorem dataN19b_4_1_binding : litN19bExpr 4 1=dataN19b_4_1 := rfl

def dataN19b_4_3 : RingExpr := (.mul (.var 10) (.mul (.var 9) (.mul (.pow (.var 8) 2) (.add (.var 2) (.add (.mul (.var 1) (.var 3)) (.add (.mul (.int (-2)) (.mul (.var 3) (.var 4))) (.add (.mul (.int 2) (.mul (.var 4) (.pow (.var 2) 2))) (.add (.mul (.int (-2)) (.mul (.var 0) (.mul (.var 2) (.mul (.var 4) (.pow (.var 3) 2))))) (.mul (.int 2) (.mul (.var 1) (.mul (.var 2) (.mul (.var 3) (.var 4)))))))))))))
theorem dataN19b_4_3_binding : litN19bExpr 4 3=dataN19b_4_3 := rfl

def dataN19b_4_4 : RingExpr := (.mul (.var 0) (.var 3))
theorem dataN19b_4_4_binding : litN19bExpr 4 4=dataN19b_4_4 := rfl

def dataN19b_4_5 : RingExpr := (.add (.var 1) (.mul (.int (-1)) (.mul (.var 0) (.var 3))))
theorem dataN19b_4_5_binding : litN19bExpr 4 5=dataN19b_4_5 := rfl

def dataN19b_4_12 : RingExpr := (.var 0)
theorem dataN19b_4_12_binding : litN19bExpr 4 12=dataN19b_4_12 := rfl

def dataN19b_4_13 : RingExpr := (.mul (.var 0) (.var 2))
theorem dataN19b_4_13_binding : litN19bExpr 4 13=dataN19b_4_13 := rfl

def dataN19b_4_15 : RingExpr := (.mul (.var 10) (.mul (.var 9) (.mul (.pow (.var 8) 2) (.add (.var 2) (.add (.mul (.var 1) (.var 3)) (.add (.mul (.int (-2)) (.mul (.var 3) (.var 4))) (.add (.mul (.int 2) (.mul (.var 4) (.pow (.var 2) 2))) (.add (.mul (.int (-2)) (.mul (.var 0) (.mul (.var 2) (.mul (.var 4) (.pow (.var 3) 2))))) (.mul (.int 2) (.mul (.var 1) (.mul (.var 2) (.mul (.var 3) (.var 4)))))))))))))
theorem dataN19b_4_15_binding : litN19bExpr 4 15=dataN19b_4_15 := rfl

def dataN19b_4_16 : RingExpr := (.mul (.var 0) (.var 3))
theorem dataN19b_4_16_binding : litN19bExpr 4 16=dataN19b_4_16 := rfl

def dataN19b_4_17 : RingExpr := (.add (.var 1) (.mul (.int (-1)) (.mul (.var 0) (.var 3))))
theorem dataN19b_4_17_binding : litN19bExpr 4 17=dataN19b_4_17 := rfl

def dataN19b_5_0 : RingExpr := (.mul (.var 10) (.mul (.pow (.var 8) 2) (.add (.var 2) (.add (.mul (.int (-2)) (.mul (.var 3) (.var 4))) (.add (.mul (.int 2) (.mul (.var 0) (.pow (.var 3) 2))) (.add (.mul (.int 2) (.mul (.var 4) (.pow (.var 2) 2))) (.mul (.int 2) (.mul (.var 0) (.mul (.var 2) (.mul (.var 4) (.pow (.var 3) 2)))))))))))
theorem dataN19b_5_0_binding : litN19bExpr 5 0=dataN19b_5_0 := rfl

def dataN19b_5_1 : RingExpr := (.mul (.var 10) (.mul (.pow (.var 8) 2) (.add (.pow (.var 2) 2) (.add (.mul (.int 2) (.mul (.var 4) (.pow (.var 2) 3))) (.add (.mul (.int (-2)) (.mul (.var 2) (.mul (.var 3) (.var 4)))) (.add (.mul (.int 2) (.mul (.var 0) (.mul (.var 2) (.pow (.var 3) 2)))) (.mul (.int 2) (.mul (.var 0) (.mul (.var 4) (.mul (.pow (.var 2) 2) (.pow (.var 3) 2)))))))))))
theorem dataN19b_5_1_binding : litN19bExpr 5 1=dataN19b_5_1 := rfl

def dataN19b_5_3 : RingExpr := (.mul (.var 10) (.mul (.var 9) (.mul (.pow (.var 8) 2) (.add (.var 2) (.add (.mul (.var 1) (.var 3)) (.add (.mul (.int (-1)) (.mul (.var 3) (.var 4))) (.add (.mul (.int 2) (.mul (.pow (.var 2) 3) (.pow (.var 4) 2))) (.add (.mul (.int 3) (.mul (.var 4) (.pow (.var 2) 2))) (.add (.mul (.int (-2)) (.mul (.var 0) (.mul (.var 2) (.mul (.var 4) (.pow (.var 3) 2))))) (.add (.mul (.int (-2)) (.mul (.var 0) (.mul (.pow (.var 2) 2) (.mul (.pow (.var 3) 2) (.pow (.var 4) 2))))) (.add (.mul (.int 2) (.mul (.var 1) (.mul (.var 3) (.mul (.pow (.var 2) 2) (.pow (.var 4) 2))))) (.mul (.int 3) (.mul (.var 1) (.mul (.var 2) (.mul (.var 3) (.var 4))))))))))))))))
theorem dataN19b_5_3_binding : litN19bExpr 5 3=dataN19b_5_3 := rfl

def dataN19b_5_4 : RingExpr := (.mul (.var 10) (.mul (.var 8) (.add (.var 2) (.add (.mul (.int (-2)) (.mul (.var 3) (.var 4))) (.add (.mul (.int 2) (.mul (.var 0) (.pow (.var 3) 2))) (.add (.mul (.int 2) (.mul (.var 4) (.pow (.var 2) 2))) (.mul (.int 2) (.mul (.var 0) (.mul (.var 2) (.mul (.var 4) (.pow (.var 3) 2)))))))))))
theorem dataN19b_5_4_binding : litN19bExpr 5 4=dataN19b_5_4 := rfl

def dataN19b_5_5 : RingExpr := (.mul (.var 10) (.mul (.var 8) (.add (.var 2) (.add (.mul (.int (-2)) (.mul (.var 0) (.pow (.var 3) 2))) (.add (.mul (.int 2) (.mul (.var 1) (.var 3))) (.add (.mul (.int 2) (.mul (.var 4) (.pow (.var 2) 2))) (.add (.mul (.int (-2)) (.mul (.var 0) (.mul (.var 2) (.mul (.var 4) (.pow (.var 3) 2))))) (.mul (.int 2) (.mul (.var 1) (.mul (.var 2) (.mul (.var 3) (.var 4))))))))))))
theorem dataN19b_5_5_binding : litN19bExpr 5 5=dataN19b_5_5 := rfl

def dataN19b_5_12 : RingExpr := (.mul (.var 10) (.mul (.pow (.var 8) 2) (.add (.var 2) (.add (.mul (.int (-2)) (.mul (.var 3) (.var 4))) (.add (.mul (.int 2) (.mul (.var 0) (.pow (.var 3) 2))) (.add (.mul (.int 2) (.mul (.var 4) (.pow (.var 2) 2))) (.mul (.int 2) (.mul (.var 0) (.mul (.var 2) (.mul (.var 4) (.pow (.var 3) 2)))))))))))
theorem dataN19b_5_12_binding : litN19bExpr 5 12=dataN19b_5_12 := rfl

def dataN19b_5_13 : RingExpr := (.mul (.var 10) (.mul (.pow (.var 8) 2) (.add (.pow (.var 2) 2) (.add (.mul (.int 2) (.mul (.var 4) (.pow (.var 2) 3))) (.add (.mul (.int (-2)) (.mul (.var 2) (.mul (.var 3) (.var 4)))) (.add (.mul (.int 2) (.mul (.var 0) (.mul (.var 2) (.pow (.var 3) 2)))) (.mul (.int 2) (.mul (.var 0) (.mul (.var 4) (.mul (.pow (.var 2) 2) (.pow (.var 3) 2)))))))))))
theorem dataN19b_5_13_binding : litN19bExpr 5 13=dataN19b_5_13 := rfl

def dataN19b_5_15 : RingExpr := (.mul (.var 10) (.mul (.var 9) (.mul (.pow (.var 8) 2) (.add (.var 2) (.add (.mul (.var 1) (.var 3)) (.add (.mul (.int (-1)) (.mul (.var 3) (.var 4))) (.add (.mul (.int 2) (.mul (.pow (.var 2) 3) (.pow (.var 4) 2))) (.add (.mul (.int 3) (.mul (.var 4) (.pow (.var 2) 2))) (.add (.mul (.int (-2)) (.mul (.var 0) (.mul (.var 2) (.mul (.var 4) (.pow (.var 3) 2))))) (.add (.mul (.int (-2)) (.mul (.var 0) (.mul (.pow (.var 2) 2) (.mul (.pow (.var 3) 2) (.pow (.var 4) 2))))) (.add (.mul (.int 2) (.mul (.var 1) (.mul (.var 3) (.mul (.pow (.var 2) 2) (.pow (.var 4) 2))))) (.mul (.int 3) (.mul (.var 1) (.mul (.var 2) (.mul (.var 3) (.var 4))))))))))))))))
theorem dataN19b_5_15_binding : litN19bExpr 5 15=dataN19b_5_15 := rfl

def dataN19b_5_16 : RingExpr := (.mul (.var 10) (.mul (.var 8) (.add (.var 2) (.add (.mul (.int (-2)) (.mul (.var 3) (.var 4))) (.add (.mul (.int 2) (.mul (.var 0) (.pow (.var 3) 2))) (.add (.mul (.int 2) (.mul (.var 4) (.pow (.var 2) 2))) (.mul (.int 2) (.mul (.var 0) (.mul (.var 2) (.mul (.var 4) (.pow (.var 3) 2)))))))))))
theorem dataN19b_5_16_binding : litN19bExpr 5 16=dataN19b_5_16 := rfl

def dataN19b_5_17 : RingExpr := (.mul (.var 10) (.mul (.var 8) (.add (.var 2) (.add (.mul (.int (-2)) (.mul (.var 0) (.pow (.var 3) 2))) (.add (.mul (.int 2) (.mul (.var 1) (.var 3))) (.add (.mul (.int 2) (.mul (.var 4) (.pow (.var 2) 2))) (.add (.mul (.int (-2)) (.mul (.var 0) (.mul (.var 2) (.mul (.var 4) (.pow (.var 3) 2))))) (.mul (.int 2) (.mul (.var 1) (.mul (.var 2) (.mul (.var 3) (.var 4))))))))))))
theorem dataN19b_5_17_binding : litN19bExpr 5 17=dataN19b_5_17 := rfl

def dataN19b_6_18 : RingExpr := (.var 12)
theorem dataN19b_6_18_binding : litN19bExpr 6 18=dataN19b_6_18 := rfl

def dataN19b_7_18 : RingExpr := (.var 15)
theorem dataN19b_7_18_binding : litN19bExpr 7 18=dataN19b_7_18 := rfl

def dataN19b_8_18 : RingExpr := (.mul (.var 10) (.mul (.var 8) (.add (.mul (.int (-3)) (.var 11)) (.add (.mul (.int (-6)) (.mul (.var 12) (.var 2))) (.add (.mul (.int 2) (.mul (.var 11) (.var 5))) (.add (.mul (.int (-3)) (.mul (.var 12) (.mul (.var 1) (.var 3)))) (.add (.mul (.int 2) (.mul (.var 12) (.mul (.var 5) (.var 2)))) (.add (.mul (.int 2) (.mul (.var 15) (.mul (.var 5) (.var 3)))) (.add (.mul (.int 6) (.mul (.var 11) (.mul (.var 2) (.var 4)))) (.add (.mul (.int (-6)) (.mul (.var 11) (.mul (.var 0) (.mul (.var 4) (.pow (.var 3) 2))))) (.mul (.int 6) (.mul (.var 11) (.mul (.var 1) (.mul (.var 3) (.var 4)))))))))))))))
theorem dataN19b_8_18_binding : litN19bExpr 8 18=dataN19b_8_18 := rfl

def dataN19b_9_18 : RingExpr := (.mul (.var 10) (.mul (.var 8) (.add (.mul (.int (-1)) (.var 11)) (.add (.mul (.int (-2)) (.mul (.var 12) (.var 2))) (.add (.mul (.int (-1)) (.mul (.var 12) (.mul (.var 1) (.var 3)))) (.add (.mul (.int (-4)) (.mul (.var 12) (.mul (.var 4) (.pow (.var 2) 2)))) (.add (.mul (.int (-2)) (.mul (.var 11) (.mul (.var 2) (.var 4)))) (.add (.mul (.int (-4)) (.mul (.var 15) (.mul (.var 2) (.mul (.var 3) (.var 4))))) (.add (.mul (.int (-2)) (.mul (.var 11) (.mul (.var 0) (.mul (.var 4) (.pow (.var 3) 2))))) (.add (.mul (.int (-2)) (.mul (.var 15) (.mul (.var 1) (.mul (.var 4) (.pow (.var 3) 2))))) (.mul (.int (-2)) (.mul (.var 12) (.mul (.var 1) (.mul (.var 2) (.mul (.var 3) (.var 4))))))))))))))))
theorem dataN19b_9_18_binding : litN19bExpr 9 18=dataN19b_9_18 := rfl

def dataN19b_10_18 : RingExpr := (.mul (.var 10) (.mul (.var 9) (.mul (.pow (.var 8) 2) (.add (.mul (.var 12) (.var 2)) (.add (.mul (.var 12) (.mul (.var 1) (.var 3))) (.add (.mul (.int (-2)) (.mul (.var 12) (.mul (.var 3) (.var 4)))) (.add (.mul (.int 2) (.mul (.var 12) (.mul (.var 4) (.pow (.var 2) 2)))) (.add (.mul (.int 2) (.mul (.var 11) (.mul (.var 0) (.mul (.var 4) (.pow (.var 3) 2))))) (.add (.mul (.int 2) (.mul (.var 15) (.mul (.var 1) (.mul (.var 4) (.pow (.var 3) 2))))) (.mul (.int 2) (.mul (.var 12) (.mul (.var 1) (.mul (.var 2) (.mul (.var 3) (.var 4)))))))))))))))
theorem dataN19b_10_18_binding : litN19bExpr 10 18=dataN19b_10_18 := rfl

def dataN19b_11_18 : RingExpr := (.mul (.var 10) (.mul (.var 9) (.mul (.pow (.var 8) 2) (.add (.mul (.var 12) (.var 2)) (.add (.mul (.var 11) (.mul (.var 2) (.var 4))) (.add (.mul (.var 12) (.mul (.var 1) (.var 3))) (.add (.mul (.int (-1)) (.mul (.var 12) (.mul (.var 3) (.var 4)))) (.add (.mul (.int (-2)) (.mul (.var 11) (.mul (.var 3) (.pow (.var 4) 2)))) (.add (.mul (.int (-2)) (.mul (.var 15) (.mul (.pow (.var 3) 2) (.pow (.var 4) 2)))) (.add (.mul (.int 2) (.mul (.var 11) (.mul (.pow (.var 2) 2) (.pow (.var 4) 2)))) (.add (.mul (.int 4) (.mul (.var 12) (.mul (.var 4) (.pow (.var 2) 2)))) (.add (.mul (.int 4) (.mul (.var 12) (.mul (.pow (.var 2) 3) (.pow (.var 4) 2)))) (.add (.mul (.int (-2)) (.mul (.var 12) (.mul (.var 2) (.mul (.var 3) (.pow (.var 4) 2))))) (.add (.mul (.int 2) (.mul (.var 11) (.mul (.var 0) (.mul (.var 4) (.pow (.var 3) 2))))) (.add (.mul (.int 2) (.mul (.var 15) (.mul (.var 1) (.mul (.var 4) (.pow (.var 3) 2))))) (.add (.mul (.int 2) (.mul (.var 15) (.mul (.var 2) (.mul (.var 3) (.var 4))))) (.add (.mul (.int 4) (.mul (.var 15) (.mul (.var 3) (.mul (.pow (.var 2) 2) (.pow (.var 4) 2))))) (.add (.mul (.int 2) (.mul (.var 11) (.mul (.var 0) (.mul (.var 2) (.mul (.pow (.var 3) 2) (.pow (.var 4) 2)))))) (.add (.mul (.int 2) (.mul (.var 12) (.mul (.var 1) (.mul (.var 3) (.mul (.pow (.var 2) 2) (.pow (.var 4) 2)))))) (.add (.mul (.int 2) (.mul (.var 15) (.mul (.var 1) (.mul (.var 2) (.mul (.pow (.var 3) 2) (.pow (.var 4) 2)))))) (.mul (.int 3) (.mul (.var 12) (.mul (.var 1) (.mul (.var 2) (.mul (.var 3) (.var 4))))))))))))))))))))))))))
theorem dataN19b_11_18_binding : litN19bExpr 11 18=dataN19b_11_18 := rfl

def dataN19b_12_18 : RingExpr := (.add (.var 12) (.mul (.int (-1)) (.var 14)))
theorem dataN19b_12_18_binding : litN19bExpr 12 18=dataN19b_12_18 := rfl

def dataN19b_13_18 : RingExpr := (.add (.var 15) (.mul (.int (-1)) (.var 16)))
theorem dataN19b_13_18_binding : litN19bExpr 13 18=dataN19b_13_18 := rfl

def dataN19b_14_18 : RingExpr := (.mul (.var 10) (.mul (.var 8) (.add (.mul (.int (-3)) (.mul (.var 12) (.var 2))) (.add (.mul (.int (-3)) (.mul (.var 16) (.var 3))) (.add (.mul (.int 3) (.mul (.var 14) (.var 2))) (.add (.mul (.int 3) (.mul (.var 15) (.var 3))) (.add (.mul (.int (-6)) (.mul (.var 12) (.mul (.var 4) (.pow (.var 2) 2)))) (.add (.mul (.int (-3)) (.mul (.var 12) (.mul (.var 1) (.var 3)))) (.add (.mul (.int 3) (.mul (.var 14) (.mul (.var 1) (.var 3)))) (.add (.mul (.int 6) (.mul (.var 14) (.mul (.var 4) (.pow (.var 2) 2)))) (.add (.mul (.int (-6)) (.mul (.var 15) (.mul (.var 1) (.mul (.var 4) (.pow (.var 3) 2))))) (.add (.mul (.int (-6)) (.mul (.var 15) (.mul (.var 2) (.mul (.var 3) (.var 4))))) (.add (.mul (.int (-6)) (.mul (.var 16) (.mul (.var 0) (.mul (.var 4) (.pow (.var 3) 3))))) (.add (.mul (.int 6) (.mul (.var 15) (.mul (.var 0) (.mul (.var 4) (.pow (.var 3) 3))))) (.add (.mul (.int 6) (.mul (.var 16) (.mul (.var 1) (.mul (.var 4) (.pow (.var 3) 2))))) (.add (.mul (.int 6) (.mul (.var 16) (.mul (.var 2) (.mul (.var 3) (.var 4))))) (.add (.mul (.int (-6)) (.mul (.var 12) (.mul (.var 1) (.mul (.var 2) (.mul (.var 3) (.var 4)))))) (.add (.mul (.int (-6)) (.mul (.var 14) (.mul (.var 0) (.mul (.var 2) (.mul (.var 4) (.pow (.var 3) 2)))))) (.add (.mul (.int 6) (.mul (.var 12) (.mul (.var 0) (.mul (.var 2) (.mul (.var 4) (.pow (.var 3) 2)))))) (.mul (.int 6) (.mul (.var 14) (.mul (.var 1) (.mul (.var 2) (.mul (.var 3) (.var 4)))))))))))))))))))))))))
theorem dataN19b_14_18_binding : litN19bExpr 14 18=dataN19b_14_18 := rfl

def dataN19b_15_18 : RingExpr := (.mul (.var 10) (.mul (.var 8) (.add (.mul (.var 14) (.var 2)) (.add (.mul (.var 15) (.var 3)) (.add (.mul (.int (-1)) (.mul (.var 12) (.var 2))) (.add (.mul (.int (-1)) (.mul (.var 16) (.var 3))) (.add (.mul (.var 14) (.mul (.var 1) (.var 3))) (.add (.mul (.int (-1)) (.mul (.var 12) (.mul (.var 1) (.var 3)))) (.add (.mul (.int (-2)) (.mul (.var 12) (.mul (.var 4) (.pow (.var 2) 2)))) (.add (.mul (.int 2) (.mul (.var 14) (.mul (.var 4) (.pow (.var 2) 2)))) (.add (.mul (.int (-2)) (.mul (.var 15) (.mul (.var 1) (.mul (.var 4) (.pow (.var 3) 2))))) (.add (.mul (.int (-2)) (.mul (.var 15) (.mul (.var 2) (.mul (.var 3) (.var 4))))) (.add (.mul (.int (-2)) (.mul (.var 16) (.mul (.var 0) (.mul (.var 4) (.pow (.var 3) 3))))) (.add (.mul (.int 2) (.mul (.var 15) (.mul (.var 0) (.mul (.var 4) (.pow (.var 3) 3))))) (.add (.mul (.int 2) (.mul (.var 16) (.mul (.var 1) (.mul (.var 4) (.pow (.var 3) 2))))) (.add (.mul (.int 2) (.mul (.var 16) (.mul (.var 2) (.mul (.var 3) (.var 4))))) (.add (.mul (.int (-2)) (.mul (.var 12) (.mul (.var 1) (.mul (.var 2) (.mul (.var 3) (.var 4)))))) (.add (.mul (.int (-2)) (.mul (.var 14) (.mul (.var 0) (.mul (.var 2) (.mul (.var 4) (.pow (.var 3) 2)))))) (.add (.mul (.int 2) (.mul (.var 12) (.mul (.var 0) (.mul (.var 2) (.mul (.var 4) (.pow (.var 3) 2)))))) (.mul (.int 2) (.mul (.var 14) (.mul (.var 1) (.mul (.var 2) (.mul (.var 3) (.var 4)))))))))))))))))))))))))
theorem dataN19b_15_18_binding : litN19bExpr 15 18=dataN19b_15_18 := rfl

def dataN19b_16_18 : RingExpr := (.mul (.var 10) (.mul (.var 9) (.mul (.pow (.var 8) 2) (.add (.mul (.var 12) (.var 2)) (.add (.mul (.int (-1)) (.mul (.var 14) (.var 2))) (.add (.mul (.var 12) (.mul (.var 1) (.var 3))) (.add (.mul (.int (-1)) (.mul (.var 14) (.mul (.var 1) (.var 3)))) (.add (.mul (.int (-2)) (.mul (.var 12) (.mul (.var 3) (.var 4)))) (.add (.mul (.int (-2)) (.mul (.var 14) (.mul (.var 4) (.pow (.var 2) 2)))) (.add (.mul (.int 2) (.mul (.var 12) (.mul (.var 4) (.pow (.var 2) 2)))) (.add (.mul (.int 2) (.mul (.var 14) (.mul (.var 3) (.var 4)))) (.add (.mul (.int (-2)) (.mul (.var 15) (.mul (.var 0) (.mul (.var 4) (.pow (.var 3) 3))))) (.add (.mul (.int (-2)) (.mul (.var 16) (.mul (.var 1) (.mul (.var 4) (.pow (.var 3) 2))))) (.add (.mul (.int 2) (.mul (.var 15) (.mul (.var 1) (.mul (.var 4) (.pow (.var 3) 2))))) (.add (.mul (.int 2) (.mul (.var 16) (.mul (.var 0) (.mul (.var 4) (.pow (.var 3) 3))))) (.add (.mul (.int (-2)) (.mul (.var 12) (.mul (.var 0) (.mul (.var 2) (.mul (.var 4) (.pow (.var 3) 2)))))) (.add (.mul (.int (-2)) (.mul (.var 14) (.mul (.var 1) (.mul (.var 2) (.mul (.var 3) (.var 4)))))) (.add (.mul (.int 2) (.mul (.var 12) (.mul (.var 1) (.mul (.var 2) (.mul (.var 3) (.var 4)))))) (.mul (.int 2) (.mul (.var 14) (.mul (.var 0) (.mul (.var 2) (.mul (.var 4) (.pow (.var 3) 2))))))))))))))))))))))))
theorem dataN19b_16_18_binding : litN19bExpr 16 18=dataN19b_16_18 := rfl

def dataN19b_17_18 : RingExpr := (.mul (.var 10) (.mul (.var 9) (.mul (.pow (.var 8) 2) (.add (.mul (.var 12) (.var 2)) (.add (.mul (.int (-1)) (.mul (.var 14) (.var 2))) (.add (.mul (.var 12) (.mul (.var 1) (.var 3))) (.add (.mul (.var 14) (.mul (.var 3) (.var 4))) (.add (.mul (.int (-1)) (.mul (.var 12) (.mul (.var 3) (.var 4)))) (.add (.mul (.int (-1)) (.mul (.var 14) (.mul (.var 1) (.var 3)))) (.add (.mul (.int (-3)) (.mul (.var 14) (.mul (.var 4) (.pow (.var 2) 2)))) (.add (.mul (.int (-2)) (.mul (.var 14) (.mul (.pow (.var 2) 3) (.pow (.var 4) 2)))) (.add (.mul (.int 2) (.mul (.var 12) (.mul (.pow (.var 2) 3) (.pow (.var 4) 2)))) (.add (.mul (.int 3) (.mul (.var 12) (.mul (.var 4) (.pow (.var 2) 2)))) (.add (.mul (.var 15) (.mul (.var 2) (.mul (.var 3) (.var 4)))) (.add (.mul (.int (-1)) (.mul (.var 16) (.mul (.var 2) (.mul (.var 3) (.var 4))))) (.add (.mul (.int (-2)) (.mul (.var 15) (.mul (.var 0) (.mul (.var 4) (.pow (.var 3) 3))))) (.add (.mul (.int (-2)) (.mul (.var 16) (.mul (.var 1) (.mul (.var 4) (.pow (.var 3) 2))))) (.add (.mul (.int (-2)) (.mul (.var 16) (.mul (.var 3) (.mul (.pow (.var 2) 2) (.pow (.var 4) 2))))) (.add (.mul (.int 2) (.mul (.var 15) (.mul (.var 1) (.mul (.var 4) (.pow (.var 3) 2))))) (.add (.mul (.int 2) (.mul (.var 15) (.mul (.var 3) (.mul (.pow (.var 2) 2) (.pow (.var 4) 2))))) (.add (.mul (.int 2) (.mul (.var 16) (.mul (.var 0) (.mul (.var 4) (.pow (.var 3) 3))))) (.add (.mul (.int (-3)) (.mul (.var 14) (.mul (.var 1) (.mul (.var 2) (.mul (.var 3) (.var 4)))))) (.add (.mul (.int (-2)) (.mul (.var 12) (.mul (.var 0) (.mul (.var 2) (.mul (.var 4) (.pow (.var 3) 2)))))) (.add (.mul (.int (-2)) (.mul (.var 12) (.mul (.var 0) (.mul (.pow (.var 2) 2) (.mul (.pow (.var 3) 2) (.pow (.var 4) 2)))))) (.add (.mul (.int (-2)) (.mul (.var 14) (.mul (.var 1) (.mul (.var 3) (.mul (.pow (.var 2) 2) (.pow (.var 4) 2)))))) (.add (.mul (.int (-2)) (.mul (.var 15) (.mul (.var 0) (.mul (.var 2) (.mul (.pow (.var 3) 3) (.pow (.var 4) 2)))))) (.add (.mul (.int (-2)) (.mul (.var 16) (.mul (.var 1) (.mul (.var 2) (.mul (.pow (.var 3) 2) (.pow (.var 4) 2)))))) (.add (.mul (.int 2) (.mul (.var 12) (.mul (.var 1) (.mul (.var 3) (.mul (.pow (.var 2) 2) (.pow (.var 4) 2)))))) (.add (.mul (.int 2) (.mul (.var 14) (.mul (.var 0) (.mul (.var 2) (.mul (.var 4) (.pow (.var 3) 2)))))) (.add (.mul (.int 2) (.mul (.var 14) (.mul (.var 0) (.mul (.pow (.var 2) 2) (.mul (.pow (.var 3) 2) (.pow (.var 4) 2)))))) (.add (.mul (.int 2) (.mul (.var 15) (.mul (.var 1) (.mul (.var 2) (.mul (.pow (.var 3) 2) (.pow (.var 4) 2)))))) (.add (.mul (.int 2) (.mul (.var 16) (.mul (.var 0) (.mul (.var 2) (.mul (.pow (.var 3) 3) (.pow (.var 4) 2)))))) (.mul (.int 3) (.mul (.var 12) (.mul (.var 1) (.mul (.var 2) (.mul (.var 3) (.var 4))))))))))))))))))))))))))))))))))))))
theorem dataN19b_17_18_binding : litN19bExpr 17 18=dataN19b_17_18 := rfl

def dataN19t_0_1 : RingExpr := (.int 1)
theorem dataN19t_0_1_binding : litN19tExpr 0 1=dataN19t_0_1 := rfl

def dataN19t_0_15 : RingExpr := (.int 1)
theorem dataN19t_0_15_binding : litN19tExpr 0 15=dataN19t_0_15 := rfl

def dataN19t_1_4 : RingExpr := (.int 1)
theorem dataN19t_1_4_binding : litN19tExpr 1 4=dataN19t_1_4 := rfl

def dataN19t_1_17 : RingExpr := (.int 1)
theorem dataN19t_1_17_binding : litN19tExpr 1 17=dataN19t_1_17 := rfl

def dataN19t_2_0 : RingExpr := (.mul (.var 10) (.mul (.var 8) (.add (.int (-3)) (.add (.mul (.int 2) (.var 5)) (.add (.mul (.int 6) (.mul (.var 2) (.var 4))) (.add (.mul (.int (-6)) (.mul (.var 0) (.mul (.var 4) (.pow (.var 3) 2)))) (.mul (.int 6) (.mul (.var 1) (.mul (.var 3) (.var 4))))))))))
theorem dataN19t_2_0_binding : litN19tExpr 2 0=dataN19t_2_0 := rfl

def dataN19t_2_1 : RingExpr := (.mul (.var 10) (.mul (.var 8) (.add (.mul (.int (-6)) (.var 2)) (.add (.mul (.int (-3)) (.mul (.var 1) (.var 3))) (.mul (.int 2) (.mul (.var 5) (.var 2)))))))
theorem dataN19t_2_1_binding : litN19tExpr 2 1=dataN19t_2_1 := rfl

def dataN19t_2_4 : RingExpr := (.var 5)
theorem dataN19t_2_4_binding : litN19tExpr 2 4=dataN19t_2_4 := rfl

def dataN19t_2_12 : RingExpr := (.mul (.var 10) (.mul (.var 8) (.add (.int (-3)) (.add (.mul (.int 2) (.var 5)) (.add (.mul (.int 6) (.mul (.var 2) (.var 4))) (.add (.mul (.int (-6)) (.mul (.var 0) (.mul (.var 4) (.pow (.var 3) 2)))) (.mul (.int 6) (.mul (.var 1) (.mul (.var 3) (.var 4))))))))))
theorem dataN19t_2_12_binding : litN19tExpr 2 12=dataN19t_2_12 := rfl

def dataN19t_2_13 : RingExpr := (.mul (.var 10) (.mul (.var 8) (.add (.mul (.int (-3)) (.var 2)) (.add (.mul (.int 2) (.mul (.var 5) (.var 2))) (.add (.mul (.int 6) (.mul (.var 4) (.pow (.var 2) 2))) (.add (.mul (.int (-6)) (.mul (.var 0) (.mul (.var 2) (.mul (.var 4) (.pow (.var 3) 2))))) (.mul (.int 6) (.mul (.var 1) (.mul (.var 2) (.mul (.var 3) (.var 4)))))))))))
theorem dataN19t_2_13_binding : litN19tExpr 2 13=dataN19t_2_13 := rfl

def dataN19t_2_15 : RingExpr := (.mul (.var 10) (.mul (.var 8) (.add (.mul (.int (-3)) (.var 2)) (.add (.mul (.int (-6)) (.mul (.var 4) (.pow (.var 2) 2))) (.add (.mul (.int (-3)) (.mul (.var 1) (.var 3))) (.add (.mul (.int (-6)) (.mul (.var 1) (.mul (.var 2) (.mul (.var 3) (.var 4))))) (.mul (.int 6) (.mul (.var 0) (.mul (.var 2) (.mul (.var 4) (.pow (.var 3) 2)))))))))))
theorem dataN19t_2_15_binding : litN19tExpr 2 15=dataN19t_2_15 := rfl

def dataN19t_2_16 : RingExpr := (.add (.mul (.int (-3)) (.pow (.var 10) 1)) (.add (.var 5) (.add (.mul (.int 3) (.mul (.var 2) (.var 4))) (.add (.mul (.int (-3)) (.mul (.var 0) (.mul (.var 4) (.pow (.var 3) 2)))) (.mul (.int 3) (.mul (.var 1) (.mul (.var 3) (.var 4))))))))
theorem dataN19t_2_16_binding : litN19tExpr 2 16=dataN19t_2_16 := rfl

def dataN19t_2_17 : RingExpr := (.add (.mul (.int (3)) (.pow (.var 10) 1)) (.add (.mul (.int (-3)) (.mul (.var 2) (.var 4))) (.add (.mul (.int (-3)) (.mul (.var 1) (.mul (.var 3) (.var 4)))) (.mul (.int 3) (.mul (.var 0) (.mul (.var 4) (.pow (.var 3) 2)))))))
theorem dataN19t_2_17_binding : litN19tExpr 2 17=dataN19t_2_17 := rfl

def dataN19t_3_0 : RingExpr := (.mul (.var 10) (.mul (.var 8) (.add (.int (-1)) (.add (.mul (.int (-2)) (.mul (.var 2) (.var 4))) (.mul (.int (-2)) (.mul (.var 0) (.mul (.var 4) (.pow (.var 3) 2))))))))
theorem dataN19t_3_0_binding : litN19tExpr 3 0=dataN19t_3_0 := rfl

def dataN19t_3_1 : RingExpr := (.mul (.var 10) (.mul (.var 8) (.add (.mul (.int (-2)) (.var 2)) (.add (.mul (.int (-1)) (.mul (.var 1) (.var 3))) (.add (.mul (.int (-4)) (.mul (.var 4) (.pow (.var 2) 2))) (.mul (.int (-2)) (.mul (.var 1) (.mul (.var 2) (.mul (.var 3) (.var 4))))))))))
theorem dataN19t_3_1_binding : litN19tExpr 3 1=dataN19t_3_1 := rfl

def dataN19t_3_4 : RingExpr := (.add (.mul (.int (-2)) (.mul (.var 2) (.var 4))) (.mul (.int (-1)) (.mul (.var 1) (.mul (.var 3) (.var 4)))))
theorem dataN19t_3_4_binding : litN19tExpr 3 4=dataN19t_3_4 := rfl

def dataN19t_3_12 : RingExpr := (.mul (.var 10) (.mul (.var 8) (.add (.int (-1)) (.add (.mul (.int (-2)) (.mul (.var 2) (.var 4))) (.mul (.int (-2)) (.mul (.var 0) (.mul (.var 4) (.pow (.var 3) 2))))))))
theorem dataN19t_3_12_binding : litN19tExpr 3 12=dataN19t_3_12 := rfl

def dataN19t_3_13 : RingExpr := (.mul (.var 10) (.mul (.var 8) (.add (.mul (.int (-1)) (.var 2)) (.add (.mul (.int (-2)) (.mul (.var 4) (.pow (.var 2) 2))) (.mul (.int (-2)) (.mul (.var 0) (.mul (.var 2) (.mul (.var 4) (.pow (.var 3) 2)))))))))
theorem dataN19t_3_13_binding : litN19tExpr 3 13=dataN19t_3_13 := rfl

def dataN19t_3_15 : RingExpr := (.mul (.var 10) (.mul (.var 8) (.add (.mul (.int (-1)) (.var 2)) (.add (.mul (.int (-1)) (.mul (.var 1) (.var 3))) (.add (.mul (.int (-2)) (.mul (.var 4) (.pow (.var 2) 2))) (.add (.mul (.int (-2)) (.mul (.var 1) (.mul (.var 2) (.mul (.var 3) (.var 4))))) (.mul (.int 2) (.mul (.var 0) (.mul (.var 2) (.mul (.var 4) (.pow (.var 3) 2)))))))))))
theorem dataN19t_3_15_binding : litN19tExpr 3 15=dataN19t_3_15 := rfl

def dataN19t_3_16 : RingExpr := (.add (.mul (.int (-1)) (.pow (.var 10) 1)) (.add (.mul (.int (-1)) (.mul (.var 2) (.var 4))) (.mul (.int (-1)) (.mul (.var 0) (.mul (.var 4) (.pow (.var 3) 2))))))
theorem dataN19t_3_16_binding : litN19tExpr 3 16=dataN19t_3_16 := rfl

def dataN19t_3_17 : RingExpr := (.add (.mul (.int (1)) (.pow (.var 10) 1)) (.add (.mul (.int (-1)) (.mul (.var 2) (.var 4))) (.add (.mul (.var 0) (.mul (.var 4) (.pow (.var 3) 2))) (.mul (.int (-1)) (.mul (.var 1) (.mul (.var 3) (.var 4)))))))
theorem dataN19t_3_17_binding : litN19tExpr 3 17=dataN19t_3_17 := rfl

def dataN19t_4_0 : RingExpr := (.var 0)
theorem dataN19t_4_0_binding : litN19tExpr 4 0=dataN19t_4_0 := rfl

def dataN19t_4_1 : RingExpr := (.mul (.var 10) (.mul (.var 9) (.mul (.pow (.var 8) 2) (.add (.var 2) (.add (.mul (.var 1) (.var 3)) (.add (.mul (.int (-2)) (.mul (.var 3) (.var 4))) (.add (.mul (.int 2) (.mul (.var 4) (.pow (.var 2) 2))) (.mul (.int 2) (.mul (.var 1) (.mul (.var 2) (.mul (.var 3) (.var 4))))))))))))
theorem dataN19t_4_1_binding : litN19tExpr 4 1=dataN19t_4_1 := rfl

def dataN19t_4_4 : RingExpr := (.var 1)
theorem dataN19t_4_4_binding : litN19tExpr 4 4=dataN19t_4_4 := rfl

def dataN19t_4_12 : RingExpr := (.var 0)
theorem dataN19t_4_12_binding : litN19tExpr 4 12=dataN19t_4_12 := rfl

def dataN19t_4_13 : RingExpr := (.mul (.var 0) (.var 2))
theorem dataN19t_4_13_binding : litN19tExpr 4 13=dataN19t_4_13 := rfl

def dataN19t_4_15 : RingExpr := (.mul (.var 10) (.mul (.var 9) (.mul (.pow (.var 8) 2) (.add (.var 2) (.add (.mul (.var 1) (.var 3)) (.add (.mul (.int (-2)) (.mul (.var 3) (.var 4))) (.add (.mul (.int 2) (.mul (.var 4) (.pow (.var 2) 2))) (.add (.mul (.int (-2)) (.mul (.var 0) (.mul (.var 2) (.mul (.var 4) (.pow (.var 3) 2))))) (.mul (.int 2) (.mul (.var 1) (.mul (.var 2) (.mul (.var 3) (.var 4)))))))))))))
theorem dataN19t_4_15_binding : litN19tExpr 4 15=dataN19t_4_15 := rfl

def dataN19t_4_16 : RingExpr := (.mul (.var 0) (.var 3))
theorem dataN19t_4_16_binding : litN19tExpr 4 16=dataN19t_4_16 := rfl

def dataN19t_4_17 : RingExpr := (.add (.var 1) (.mul (.int (-1)) (.mul (.var 0) (.var 3))))
theorem dataN19t_4_17_binding : litN19tExpr 4 17=dataN19t_4_17 := rfl

def dataN19t_5_0 : RingExpr := (.mul (.var 10) (.mul (.pow (.var 8) 2) (.add (.var 2) (.add (.mul (.int (-2)) (.mul (.var 3) (.var 4))) (.add (.mul (.int 2) (.mul (.var 0) (.pow (.var 3) 2))) (.add (.mul (.int 2) (.mul (.var 4) (.pow (.var 2) 2))) (.mul (.int 2) (.mul (.var 0) (.mul (.var 2) (.mul (.var 4) (.pow (.var 3) 2)))))))))))
theorem dataN19t_5_0_binding : litN19tExpr 5 0=dataN19t_5_0 := rfl

def dataN19t_5_1 : RingExpr := (.mul (.var 10) (.mul (.var 9) (.mul (.pow (.var 8) 2) (.add (.var 2) (.add (.mul (.var 1) (.var 3)) (.add (.mul (.int (-1)) (.mul (.var 3) (.var 4))) (.add (.mul (.int 4) (.mul (.var 4) (.pow (.var 2) 2))) (.add (.mul (.int 4) (.mul (.pow (.var 2) 3) (.pow (.var 4) 2))) (.add (.mul (.int (-2)) (.mul (.var 2) (.mul (.var 3) (.pow (.var 4) 2)))) (.add (.mul (.int 2) (.mul (.var 1) (.mul (.var 3) (.mul (.pow (.var 2) 2) (.pow (.var 4) 2))))) (.mul (.int 3) (.mul (.var 1) (.mul (.var 2) (.mul (.var 3) (.var 4)))))))))))))))
theorem dataN19t_5_1_binding : litN19tExpr 5 1=dataN19t_5_1 := rfl

def dataN19t_5_4 : RingExpr := (.mul (.var 8) (.add (.var 2) (.add (.mul (.var 1) (.var 3)) (.add (.mul (.int (-1)) (.mul (.var 3) (.var 4))) (.add (.mul (.int 2) (.mul (.var 4) (.pow (.var 2) 2))) (.mul (.var 1) (.mul (.var 2) (.mul (.var 3) (.var 4)))))))))
theorem dataN19t_5_4_binding : litN19tExpr 5 4=dataN19t_5_4 := rfl

def dataN19t_5_12 : RingExpr := (.mul (.var 10) (.mul (.pow (.var 8) 2) (.add (.var 2) (.add (.mul (.int (-2)) (.mul (.var 3) (.var 4))) (.add (.mul (.int 2) (.mul (.var 0) (.pow (.var 3) 2))) (.add (.mul (.int 2) (.mul (.var 4) (.pow (.var 2) 2))) (.mul (.int 2) (.mul (.var 0) (.mul (.var 2) (.mul (.var 4) (.pow (.var 3) 2)))))))))))
theorem dataN19t_5_12_binding : litN19tExpr 5 12=dataN19t_5_12 := rfl

def dataN19t_5_13 : RingExpr := (.mul (.var 10) (.mul (.pow (.var 8) 2) (.add (.pow (.var 2) 2) (.add (.mul (.int 2) (.mul (.var 4) (.pow (.var 2) 3))) (.add (.mul (.int (-2)) (.mul (.var 2) (.mul (.var 3) (.var 4)))) (.add (.mul (.int 2) (.mul (.var 0) (.mul (.var 2) (.pow (.var 3) 2)))) (.mul (.int 2) (.mul (.var 0) (.mul (.var 4) (.mul (.pow (.var 2) 2) (.pow (.var 3) 2)))))))))))
theorem dataN19t_5_13_binding : litN19tExpr 5 13=dataN19t_5_13 := rfl

def dataN19t_5_15 : RingExpr := (.mul (.var 10) (.mul (.var 9) (.mul (.pow (.var 8) 2) (.add (.var 2) (.add (.mul (.var 1) (.var 3)) (.add (.mul (.int (-1)) (.mul (.var 3) (.var 4))) (.add (.mul (.int 2) (.mul (.pow (.var 2) 3) (.pow (.var 4) 2))) (.add (.mul (.int 3) (.mul (.var 4) (.pow (.var 2) 2))) (.add (.mul (.int (-2)) (.mul (.var 0) (.mul (.var 2) (.mul (.var 4) (.pow (.var 3) 2))))) (.add (.mul (.int (-2)) (.mul (.var 0) (.mul (.pow (.var 2) 2) (.mul (.pow (.var 3) 2) (.pow (.var 4) 2))))) (.add (.mul (.int 2) (.mul (.var 1) (.mul (.var 3) (.mul (.pow (.var 2) 2) (.pow (.var 4) 2))))) (.mul (.int 3) (.mul (.var 1) (.mul (.var 2) (.mul (.var 3) (.var 4))))))))))))))))
theorem dataN19t_5_15_binding : litN19tExpr 5 15=dataN19t_5_15 := rfl

def dataN19t_5_16 : RingExpr := (.mul (.var 10) (.mul (.var 8) (.add (.var 2) (.add (.mul (.int (-2)) (.mul (.var 3) (.var 4))) (.add (.mul (.int 2) (.mul (.var 0) (.pow (.var 3) 2))) (.add (.mul (.int 2) (.mul (.var 4) (.pow (.var 2) 2))) (.mul (.int 2) (.mul (.var 0) (.mul (.var 2) (.mul (.var 4) (.pow (.var 3) 2)))))))))))
theorem dataN19t_5_16_binding : litN19tExpr 5 16=dataN19t_5_16 := rfl

def dataN19t_5_17 : RingExpr := (.mul (.var 10) (.mul (.var 8) (.add (.var 2) (.add (.mul (.int (-2)) (.mul (.var 0) (.pow (.var 3) 2))) (.add (.mul (.int 2) (.mul (.var 1) (.var 3))) (.add (.mul (.int 2) (.mul (.var 4) (.pow (.var 2) 2))) (.add (.mul (.int (-2)) (.mul (.var 0) (.mul (.var 2) (.mul (.var 4) (.pow (.var 3) 2))))) (.mul (.int 2) (.mul (.var 1) (.mul (.var 2) (.mul (.var 3) (.var 4))))))))))))
theorem dataN19t_5_17_binding : litN19tExpr 5 17=dataN19t_5_17 := rfl

def dataN19t_6_9 : RingExpr := (.int 1)
theorem dataN19t_6_9_binding : litN19tExpr 6 9=dataN19t_6_9 := rfl

def dataN19t_6_18 : RingExpr := (.add (.var 12) (.mul (.int (-1)) (.var 14)))
theorem dataN19t_6_18_binding : litN19tExpr 6 18=dataN19t_6_18 := rfl

def dataN19t_7_11 : RingExpr := (.int 1)
theorem dataN19t_7_11_binding : litN19tExpr 7 11=dataN19t_7_11 := rfl

def dataN19t_7_18 : RingExpr := (.add (.var 15) (.mul (.int (-1)) (.var 16)))
theorem dataN19t_7_18_binding : litN19tExpr 7 18=dataN19t_7_18 := rfl

def dataN19t_8_6 : RingExpr := (.mul (.var 10) (.mul (.var 8) (.add (.int (-3)) (.add (.mul (.int 2) (.var 5)) (.add (.mul (.int 6) (.mul (.var 2) (.var 4))) (.add (.mul (.int (-6)) (.mul (.var 0) (.mul (.var 4) (.pow (.var 3) 2)))) (.mul (.int 6) (.mul (.var 1) (.mul (.var 3) (.var 4))))))))))
theorem dataN19t_8_6_binding : litN19tExpr 8 6=dataN19t_8_6 := rfl

def dataN19t_8_7 : RingExpr := (.mul (.var 10) (.mul (.var 8) (.add (.mul (.int (-3)) (.var 2)) (.add (.mul (.int 2) (.mul (.var 5) (.var 2))) (.add (.mul (.int 6) (.mul (.var 4) (.pow (.var 2) 2))) (.add (.mul (.int (-6)) (.mul (.var 0) (.mul (.var 2) (.mul (.var 4) (.pow (.var 3) 2))))) (.mul (.int 6) (.mul (.var 1) (.mul (.var 2) (.mul (.var 3) (.var 4)))))))))))
theorem dataN19t_8_7_binding : litN19tExpr 8 7=dataN19t_8_7 := rfl

def dataN19t_8_9 : RingExpr := (.mul (.var 10) (.mul (.var 8) (.add (.mul (.int (-3)) (.var 2)) (.add (.mul (.int (-6)) (.mul (.var 4) (.pow (.var 2) 2))) (.add (.mul (.int (-3)) (.mul (.var 1) (.var 3))) (.add (.mul (.int (-6)) (.mul (.var 1) (.mul (.var 2) (.mul (.var 3) (.var 4))))) (.mul (.int 6) (.mul (.var 0) (.mul (.var 2) (.mul (.var 4) (.pow (.var 3) 2)))))))))))
theorem dataN19t_8_9_binding : litN19tExpr 8 9=dataN19t_8_9 := rfl

def dataN19t_8_10 : RingExpr := (.add (.mul (.int (-3)) (.pow (.var 10) 1)) (.add (.var 5) (.add (.mul (.int 3) (.mul (.var 2) (.var 4))) (.add (.mul (.int (-3)) (.mul (.var 0) (.mul (.var 4) (.pow (.var 3) 2)))) (.mul (.int 3) (.mul (.var 1) (.mul (.var 3) (.var 4))))))))
theorem dataN19t_8_10_binding : litN19tExpr 8 10=dataN19t_8_10 := rfl

def dataN19t_8_11 : RingExpr := (.add (.mul (.int (3)) (.pow (.var 10) 1)) (.add (.mul (.int (-3)) (.mul (.var 2) (.var 4))) (.add (.mul (.int (-3)) (.mul (.var 1) (.mul (.var 3) (.var 4)))) (.mul (.int 3) (.mul (.var 0) (.mul (.var 4) (.pow (.var 3) 2)))))))
theorem dataN19t_8_11_binding : litN19tExpr 8 11=dataN19t_8_11 := rfl

def dataN19t_8_18 : RingExpr := (.mul (.var 10) (.mul (.var 8) (.add (.mul (.int (-3)) (.mul (.var 12) (.var 2))) (.add (.mul (.int (-3)) (.mul (.var 16) (.var 3))) (.add (.mul (.int 3) (.mul (.var 14) (.var 2))) (.add (.mul (.int 3) (.mul (.var 15) (.var 3))) (.add (.mul (.int (-6)) (.mul (.var 12) (.mul (.var 4) (.pow (.var 2) 2)))) (.add (.mul (.int (-3)) (.mul (.var 12) (.mul (.var 1) (.var 3)))) (.add (.mul (.int 3) (.mul (.var 14) (.mul (.var 1) (.var 3)))) (.add (.mul (.int 6) (.mul (.var 14) (.mul (.var 4) (.pow (.var 2) 2)))) (.add (.mul (.int (-6)) (.mul (.var 15) (.mul (.var 1) (.mul (.var 4) (.pow (.var 3) 2))))) (.add (.mul (.int (-6)) (.mul (.var 15) (.mul (.var 2) (.mul (.var 3) (.var 4))))) (.add (.mul (.int (-6)) (.mul (.var 16) (.mul (.var 0) (.mul (.var 4) (.pow (.var 3) 3))))) (.add (.mul (.int 6) (.mul (.var 15) (.mul (.var 0) (.mul (.var 4) (.pow (.var 3) 3))))) (.add (.mul (.int 6) (.mul (.var 16) (.mul (.var 1) (.mul (.var 4) (.pow (.var 3) 2))))) (.add (.mul (.int 6) (.mul (.var 16) (.mul (.var 2) (.mul (.var 3) (.var 4))))) (.add (.mul (.int (-6)) (.mul (.var 12) (.mul (.var 1) (.mul (.var 2) (.mul (.var 3) (.var 4)))))) (.add (.mul (.int (-6)) (.mul (.var 14) (.mul (.var 0) (.mul (.var 2) (.mul (.var 4) (.pow (.var 3) 2)))))) (.add (.mul (.int 6) (.mul (.var 12) (.mul (.var 0) (.mul (.var 2) (.mul (.var 4) (.pow (.var 3) 2)))))) (.mul (.int 6) (.mul (.var 14) (.mul (.var 1) (.mul (.var 2) (.mul (.var 3) (.var 4)))))))))))))))))))))))))
theorem dataN19t_8_18_binding : litN19tExpr 8 18=dataN19t_8_18 := rfl

def dataN19t_9_6 : RingExpr := (.mul (.var 10) (.mul (.var 8) (.add (.int (-1)) (.add (.mul (.int (-2)) (.mul (.var 2) (.var 4))) (.mul (.int (-2)) (.mul (.var 0) (.mul (.var 4) (.pow (.var 3) 2))))))))
theorem dataN19t_9_6_binding : litN19tExpr 9 6=dataN19t_9_6 := rfl

def dataN19t_9_7 : RingExpr := (.mul (.var 10) (.mul (.var 8) (.add (.mul (.int (-1)) (.var 2)) (.add (.mul (.int (-2)) (.mul (.var 4) (.pow (.var 2) 2))) (.mul (.int (-2)) (.mul (.var 0) (.mul (.var 2) (.mul (.var 4) (.pow (.var 3) 2)))))))))
theorem dataN19t_9_7_binding : litN19tExpr 9 7=dataN19t_9_7 := rfl

def dataN19t_9_9 : RingExpr := (.mul (.var 10) (.mul (.var 8) (.add (.mul (.int (-1)) (.var 2)) (.add (.mul (.int (-1)) (.mul (.var 1) (.var 3))) (.add (.mul (.int (-2)) (.mul (.var 4) (.pow (.var 2) 2))) (.add (.mul (.int (-2)) (.mul (.var 1) (.mul (.var 2) (.mul (.var 3) (.var 4))))) (.mul (.int 2) (.mul (.var 0) (.mul (.var 2) (.mul (.var 4) (.pow (.var 3) 2)))))))))))
theorem dataN19t_9_9_binding : litN19tExpr 9 9=dataN19t_9_9 := rfl

def dataN19t_9_10 : RingExpr := (.add (.mul (.int (-1)) (.pow (.var 10) 1)) (.add (.mul (.int (-1)) (.mul (.var 2) (.var 4))) (.mul (.int (-1)) (.mul (.var 0) (.mul (.var 4) (.pow (.var 3) 2))))))
theorem dataN19t_9_10_binding : litN19tExpr 9 10=dataN19t_9_10 := rfl

def dataN19t_9_11 : RingExpr := (.add (.mul (.int (1)) (.pow (.var 10) 1)) (.add (.mul (.int (-1)) (.mul (.var 2) (.var 4))) (.add (.mul (.var 0) (.mul (.var 4) (.pow (.var 3) 2))) (.mul (.int (-1)) (.mul (.var 1) (.mul (.var 3) (.var 4)))))))
theorem dataN19t_9_11_binding : litN19tExpr 9 11=dataN19t_9_11 := rfl

def dataN19t_9_18 : RingExpr := (.mul (.var 10) (.mul (.var 8) (.add (.mul (.var 14) (.var 2)) (.add (.mul (.var 15) (.var 3)) (.add (.mul (.int (-1)) (.mul (.var 12) (.var 2))) (.add (.mul (.int (-1)) (.mul (.var 16) (.var 3))) (.add (.mul (.var 14) (.mul (.var 1) (.var 3))) (.add (.mul (.int (-1)) (.mul (.var 12) (.mul (.var 1) (.var 3)))) (.add (.mul (.int (-2)) (.mul (.var 12) (.mul (.var 4) (.pow (.var 2) 2)))) (.add (.mul (.int 2) (.mul (.var 14) (.mul (.var 4) (.pow (.var 2) 2)))) (.add (.mul (.int (-2)) (.mul (.var 15) (.mul (.var 1) (.mul (.var 4) (.pow (.var 3) 2))))) (.add (.mul (.int (-2)) (.mul (.var 15) (.mul (.var 2) (.mul (.var 3) (.var 4))))) (.add (.mul (.int (-2)) (.mul (.var 16) (.mul (.var 0) (.mul (.var 4) (.pow (.var 3) 3))))) (.add (.mul (.int 2) (.mul (.var 15) (.mul (.var 0) (.mul (.var 4) (.pow (.var 3) 3))))) (.add (.mul (.int 2) (.mul (.var 16) (.mul (.var 1) (.mul (.var 4) (.pow (.var 3) 2))))) (.add (.mul (.int 2) (.mul (.var 16) (.mul (.var 2) (.mul (.var 3) (.var 4))))) (.add (.mul (.int (-2)) (.mul (.var 12) (.mul (.var 1) (.mul (.var 2) (.mul (.var 3) (.var 4)))))) (.add (.mul (.int (-2)) (.mul (.var 14) (.mul (.var 0) (.mul (.var 2) (.mul (.var 4) (.pow (.var 3) 2)))))) (.add (.mul (.int 2) (.mul (.var 12) (.mul (.var 0) (.mul (.var 2) (.mul (.var 4) (.pow (.var 3) 2)))))) (.mul (.int 2) (.mul (.var 14) (.mul (.var 1) (.mul (.var 2) (.mul (.var 3) (.var 4)))))))))))))))))))))))))
theorem dataN19t_9_18_binding : litN19tExpr 9 18=dataN19t_9_18 := rfl

def dataN19t_10_6 : RingExpr := (.var 0)
theorem dataN19t_10_6_binding : litN19tExpr 10 6=dataN19t_10_6 := rfl

def dataN19t_10_7 : RingExpr := (.mul (.var 0) (.var 2))
theorem dataN19t_10_7_binding : litN19tExpr 10 7=dataN19t_10_7 := rfl

def dataN19t_10_9 : RingExpr := (.mul (.var 10) (.mul (.var 9) (.mul (.pow (.var 8) 2) (.add (.var 2) (.add (.mul (.var 1) (.var 3)) (.add (.mul (.int (-2)) (.mul (.var 3) (.var 4))) (.add (.mul (.int 2) (.mul (.var 4) (.pow (.var 2) 2))) (.add (.mul (.int (-2)) (.mul (.var 0) (.mul (.var 2) (.mul (.var 4) (.pow (.var 3) 2))))) (.mul (.int 2) (.mul (.var 1) (.mul (.var 2) (.mul (.var 3) (.var 4)))))))))))))
theorem dataN19t_10_9_binding : litN19tExpr 10 9=dataN19t_10_9 := rfl

def dataN19t_10_10 : RingExpr := (.mul (.var 0) (.var 3))
theorem dataN19t_10_10_binding : litN19tExpr 10 10=dataN19t_10_10 := rfl

def dataN19t_10_11 : RingExpr := (.add (.var 1) (.mul (.int (-1)) (.mul (.var 0) (.var 3))))
theorem dataN19t_10_11_binding : litN19tExpr 10 11=dataN19t_10_11 := rfl

def dataN19t_10_18 : RingExpr := (.mul (.var 10) (.mul (.var 9) (.mul (.pow (.var 8) 2) (.add (.mul (.var 12) (.var 2)) (.add (.mul (.int (-1)) (.mul (.var 14) (.var 2))) (.add (.mul (.var 12) (.mul (.var 1) (.var 3))) (.add (.mul (.int (-1)) (.mul (.var 14) (.mul (.var 1) (.var 3)))) (.add (.mul (.int (-2)) (.mul (.var 12) (.mul (.var 3) (.var 4)))) (.add (.mul (.int (-2)) (.mul (.var 14) (.mul (.var 4) (.pow (.var 2) 2)))) (.add (.mul (.int 2) (.mul (.var 12) (.mul (.var 4) (.pow (.var 2) 2)))) (.add (.mul (.int 2) (.mul (.var 14) (.mul (.var 3) (.var 4)))) (.add (.mul (.int (-2)) (.mul (.var 15) (.mul (.var 0) (.mul (.var 4) (.pow (.var 3) 3))))) (.add (.mul (.int (-2)) (.mul (.var 16) (.mul (.var 1) (.mul (.var 4) (.pow (.var 3) 2))))) (.add (.mul (.int 2) (.mul (.var 15) (.mul (.var 1) (.mul (.var 4) (.pow (.var 3) 2))))) (.add (.mul (.int 2) (.mul (.var 16) (.mul (.var 0) (.mul (.var 4) (.pow (.var 3) 3))))) (.add (.mul (.int (-2)) (.mul (.var 12) (.mul (.var 0) (.mul (.var 2) (.mul (.var 4) (.pow (.var 3) 2)))))) (.add (.mul (.int (-2)) (.mul (.var 14) (.mul (.var 1) (.mul (.var 2) (.mul (.var 3) (.var 4)))))) (.add (.mul (.int 2) (.mul (.var 12) (.mul (.var 1) (.mul (.var 2) (.mul (.var 3) (.var 4)))))) (.mul (.int 2) (.mul (.var 14) (.mul (.var 0) (.mul (.var 2) (.mul (.var 4) (.pow (.var 3) 2))))))))))))))))))))))))
theorem dataN19t_10_18_binding : litN19tExpr 10 18=dataN19t_10_18 := rfl

def dataN19t_11_6 : RingExpr := (.mul (.var 10) (.mul (.pow (.var 8) 2) (.add (.var 2) (.add (.mul (.int (-2)) (.mul (.var 3) (.var 4))) (.add (.mul (.int 2) (.mul (.var 0) (.pow (.var 3) 2))) (.add (.mul (.int 2) (.mul (.var 4) (.pow (.var 2) 2))) (.mul (.int 2) (.mul (.var 0) (.mul (.var 2) (.mul (.var 4) (.pow (.var 3) 2)))))))))))
theorem dataN19t_11_6_binding : litN19tExpr 11 6=dataN19t_11_6 := rfl

def dataN19t_11_7 : RingExpr := (.mul (.var 10) (.mul (.pow (.var 8) 2) (.add (.pow (.var 2) 2) (.add (.mul (.int 2) (.mul (.var 4) (.pow (.var 2) 3))) (.add (.mul (.int (-2)) (.mul (.var 2) (.mul (.var 3) (.var 4)))) (.add (.mul (.int 2) (.mul (.var 0) (.mul (.var 2) (.pow (.var 3) 2)))) (.mul (.int 2) (.mul (.var 0) (.mul (.var 4) (.mul (.pow (.var 2) 2) (.pow (.var 3) 2)))))))))))
theorem dataN19t_11_7_binding : litN19tExpr 11 7=dataN19t_11_7 := rfl

def dataN19t_11_9 : RingExpr := (.mul (.var 10) (.mul (.var 9) (.mul (.pow (.var 8) 2) (.add (.var 2) (.add (.mul (.var 1) (.var 3)) (.add (.mul (.int (-1)) (.mul (.var 3) (.var 4))) (.add (.mul (.int 2) (.mul (.pow (.var 2) 3) (.pow (.var 4) 2))) (.add (.mul (.int 3) (.mul (.var 4) (.pow (.var 2) 2))) (.add (.mul (.int (-2)) (.mul (.var 0) (.mul (.var 2) (.mul (.var 4) (.pow (.var 3) 2))))) (.add (.mul (.int (-2)) (.mul (.var 0) (.mul (.pow (.var 2) 2) (.mul (.pow (.var 3) 2) (.pow (.var 4) 2))))) (.add (.mul (.int 2) (.mul (.var 1) (.mul (.var 3) (.mul (.pow (.var 2) 2) (.pow (.var 4) 2))))) (.mul (.int 3) (.mul (.var 1) (.mul (.var 2) (.mul (.var 3) (.var 4))))))))))))))))
theorem dataN19t_11_9_binding : litN19tExpr 11 9=dataN19t_11_9 := rfl

def dataN19t_11_10 : RingExpr := (.mul (.var 10) (.mul (.var 8) (.add (.var 2) (.add (.mul (.int (-2)) (.mul (.var 3) (.var 4))) (.add (.mul (.int 2) (.mul (.var 0) (.pow (.var 3) 2))) (.add (.mul (.int 2) (.mul (.var 4) (.pow (.var 2) 2))) (.mul (.int 2) (.mul (.var 0) (.mul (.var 2) (.mul (.var 4) (.pow (.var 3) 2)))))))))))
theorem dataN19t_11_10_binding : litN19tExpr 11 10=dataN19t_11_10 := rfl

def dataN19t_11_11 : RingExpr := (.mul (.var 10) (.mul (.var 8) (.add (.var 2) (.add (.mul (.int (-2)) (.mul (.var 0) (.pow (.var 3) 2))) (.add (.mul (.int 2) (.mul (.var 1) (.var 3))) (.add (.mul (.int 2) (.mul (.var 4) (.pow (.var 2) 2))) (.add (.mul (.int (-2)) (.mul (.var 0) (.mul (.var 2) (.mul (.var 4) (.pow (.var 3) 2))))) (.mul (.int 2) (.mul (.var 1) (.mul (.var 2) (.mul (.var 3) (.var 4))))))))))))
theorem dataN19t_11_11_binding : litN19tExpr 11 11=dataN19t_11_11 := rfl

def dataN19t_11_18 : RingExpr := (.mul (.var 10) (.mul (.var 9) (.mul (.pow (.var 8) 2) (.add (.mul (.var 12) (.var 2)) (.add (.mul (.int (-1)) (.mul (.var 14) (.var 2))) (.add (.mul (.var 12) (.mul (.var 1) (.var 3))) (.add (.mul (.var 14) (.mul (.var 3) (.var 4))) (.add (.mul (.int (-1)) (.mul (.var 12) (.mul (.var 3) (.var 4)))) (.add (.mul (.int (-1)) (.mul (.var 14) (.mul (.var 1) (.var 3)))) (.add (.mul (.int (-3)) (.mul (.var 14) (.mul (.var 4) (.pow (.var 2) 2)))) (.add (.mul (.int (-2)) (.mul (.var 14) (.mul (.pow (.var 2) 3) (.pow (.var 4) 2)))) (.add (.mul (.int 2) (.mul (.var 12) (.mul (.pow (.var 2) 3) (.pow (.var 4) 2)))) (.add (.mul (.int 3) (.mul (.var 12) (.mul (.var 4) (.pow (.var 2) 2)))) (.add (.mul (.var 15) (.mul (.var 2) (.mul (.var 3) (.var 4)))) (.add (.mul (.int (-1)) (.mul (.var 16) (.mul (.var 2) (.mul (.var 3) (.var 4))))) (.add (.mul (.int (-2)) (.mul (.var 15) (.mul (.var 0) (.mul (.var 4) (.pow (.var 3) 3))))) (.add (.mul (.int (-2)) (.mul (.var 16) (.mul (.var 1) (.mul (.var 4) (.pow (.var 3) 2))))) (.add (.mul (.int (-2)) (.mul (.var 16) (.mul (.var 3) (.mul (.pow (.var 2) 2) (.pow (.var 4) 2))))) (.add (.mul (.int 2) (.mul (.var 15) (.mul (.var 1) (.mul (.var 4) (.pow (.var 3) 2))))) (.add (.mul (.int 2) (.mul (.var 15) (.mul (.var 3) (.mul (.pow (.var 2) 2) (.pow (.var 4) 2))))) (.add (.mul (.int 2) (.mul (.var 16) (.mul (.var 0) (.mul (.var 4) (.pow (.var 3) 3))))) (.add (.mul (.int (-3)) (.mul (.var 14) (.mul (.var 1) (.mul (.var 2) (.mul (.var 3) (.var 4)))))) (.add (.mul (.int (-2)) (.mul (.var 12) (.mul (.var 0) (.mul (.var 2) (.mul (.var 4) (.pow (.var 3) 2)))))) (.add (.mul (.int (-2)) (.mul (.var 12) (.mul (.var 0) (.mul (.pow (.var 2) 2) (.mul (.pow (.var 3) 2) (.pow (.var 4) 2)))))) (.add (.mul (.int (-2)) (.mul (.var 14) (.mul (.var 1) (.mul (.var 3) (.mul (.pow (.var 2) 2) (.pow (.var 4) 2)))))) (.add (.mul (.int (-2)) (.mul (.var 15) (.mul (.var 0) (.mul (.var 2) (.mul (.pow (.var 3) 3) (.pow (.var 4) 2)))))) (.add (.mul (.int (-2)) (.mul (.var 16) (.mul (.var 1) (.mul (.var 2) (.mul (.pow (.var 3) 2) (.pow (.var 4) 2)))))) (.add (.mul (.int 2) (.mul (.var 12) (.mul (.var 1) (.mul (.var 3) (.mul (.pow (.var 2) 2) (.pow (.var 4) 2)))))) (.add (.mul (.int 2) (.mul (.var 14) (.mul (.var 0) (.mul (.var 2) (.mul (.var 4) (.pow (.var 3) 2)))))) (.add (.mul (.int 2) (.mul (.var 14) (.mul (.var 0) (.mul (.pow (.var 2) 2) (.mul (.pow (.var 3) 2) (.pow (.var 4) 2)))))) (.add (.mul (.int 2) (.mul (.var 15) (.mul (.var 1) (.mul (.var 2) (.mul (.pow (.var 3) 2) (.pow (.var 4) 2)))))) (.add (.mul (.int 2) (.mul (.var 16) (.mul (.var 0) (.mul (.var 2) (.mul (.pow (.var 3) 3) (.pow (.var 4) 2)))))) (.mul (.int 3) (.mul (.var 12) (.mul (.var 1) (.mul (.var 2) (.mul (.var 3) (.var 4))))))))))))))))))))))))))))))))))))))
theorem dataN19t_11_18_binding : litN19tExpr 11 18=dataN19t_11_18 := rfl

def dataN19t_12_13 : RingExpr := (.int 1)
theorem dataN19t_12_13_binding : litN19tExpr 12 13=dataN19t_12_13 := rfl

def dataN19t_12_15 : RingExpr := (.int (-1))
theorem dataN19t_12_15_binding : litN19tExpr 12 15=dataN19t_12_15 := rfl

def dataN19t_13_16 : RingExpr := (.int 1)
theorem dataN19t_13_16_binding : litN19tExpr 13 16=dataN19t_13_16 := rfl

def dataN19t_13_17 : RingExpr := (.int (-1))
theorem dataN19t_13_17_binding : litN19tExpr 13 17=dataN19t_13_17 := rfl

def dataN19t_14_13 : RingExpr := (.mul (.var 10) (.mul (.var 8) (.add (.mul (.int (-3)) (.var 2)) (.add (.mul (.int (-6)) (.mul (.var 4) (.pow (.var 2) 2))) (.add (.mul (.int (-3)) (.mul (.var 1) (.var 3))) (.add (.mul (.int (-6)) (.mul (.var 1) (.mul (.var 2) (.mul (.var 3) (.var 4))))) (.mul (.int 6) (.mul (.var 0) (.mul (.var 2) (.mul (.var 4) (.pow (.var 3) 2)))))))))))
theorem dataN19t_14_13_binding : litN19tExpr 14 13=dataN19t_14_13 := rfl

def dataN19t_14_15 : RingExpr := (.mul (.var 10) (.mul (.var 8) (.add (.mul (.int 3) (.var 2)) (.add (.mul (.int 3) (.mul (.var 1) (.var 3))) (.add (.mul (.int 6) (.mul (.var 4) (.pow (.var 2) 2))) (.add (.mul (.int (-6)) (.mul (.var 0) (.mul (.var 2) (.mul (.var 4) (.pow (.var 3) 2))))) (.mul (.int 6) (.mul (.var 1) (.mul (.var 2) (.mul (.var 3) (.var 4)))))))))))
theorem dataN19t_14_15_binding : litN19tExpr 14 15=dataN19t_14_15 := rfl

def dataN19t_14_16 : RingExpr := (.add (.mul (.int (3)) (.pow (.var 10) 1)) (.add (.mul (.int (-3)) (.mul (.var 2) (.var 4))) (.add (.mul (.int (-3)) (.mul (.var 1) (.mul (.var 3) (.var 4)))) (.mul (.int 3) (.mul (.var 0) (.mul (.var 4) (.pow (.var 3) 2)))))))
theorem dataN19t_14_16_binding : litN19tExpr 14 16=dataN19t_14_16 := rfl

def dataN19t_14_17 : RingExpr := (.add (.mul (.int (-3)) (.pow (.var 10) 1)) (.add (.mul (.int 3) (.mul (.var 2) (.var 4))) (.add (.mul (.int (-3)) (.mul (.var 0) (.mul (.var 4) (.pow (.var 3) 2)))) (.mul (.int 3) (.mul (.var 1) (.mul (.var 3) (.var 4)))))))
theorem dataN19t_14_17_binding : litN19tExpr 14 17=dataN19t_14_17 := rfl

def dataN19t_15_13 : RingExpr := (.mul (.var 10) (.mul (.var 8) (.add (.mul (.int (-1)) (.var 2)) (.add (.mul (.int (-1)) (.mul (.var 1) (.var 3))) (.add (.mul (.int (-2)) (.mul (.var 4) (.pow (.var 2) 2))) (.add (.mul (.int (-2)) (.mul (.var 1) (.mul (.var 2) (.mul (.var 3) (.var 4))))) (.mul (.int 2) (.mul (.var 0) (.mul (.var 2) (.mul (.var 4) (.pow (.var 3) 2)))))))))))
theorem dataN19t_15_13_binding : litN19tExpr 15 13=dataN19t_15_13 := rfl

def dataN19t_15_15 : RingExpr := (.mul (.var 10) (.mul (.var 8) (.add (.var 2) (.add (.mul (.var 1) (.var 3)) (.add (.mul (.int 2) (.mul (.var 4) (.pow (.var 2) 2))) (.add (.mul (.int (-2)) (.mul (.var 0) (.mul (.var 2) (.mul (.var 4) (.pow (.var 3) 2))))) (.mul (.int 2) (.mul (.var 1) (.mul (.var 2) (.mul (.var 3) (.var 4)))))))))))
theorem dataN19t_15_15_binding : litN19tExpr 15 15=dataN19t_15_15 := rfl

def dataN19t_15_16 : RingExpr := (.add (.mul (.int (1)) (.pow (.var 10) 1)) (.add (.mul (.int (-1)) (.mul (.var 2) (.var 4))) (.add (.mul (.var 0) (.mul (.var 4) (.pow (.var 3) 2))) (.mul (.int (-1)) (.mul (.var 1) (.mul (.var 3) (.var 4)))))))
theorem dataN19t_15_16_binding : litN19tExpr 15 16=dataN19t_15_16 := rfl

def dataN19t_15_17 : RingExpr := (.add (.mul (.int (-1)) (.pow (.var 10) 1)) (.add (.mul (.var 2) (.var 4)) (.add (.mul (.var 1) (.mul (.var 3) (.var 4))) (.mul (.int (-1)) (.mul (.var 0) (.mul (.var 4) (.pow (.var 3) 2)))))))
theorem dataN19t_15_17_binding : litN19tExpr 15 17=dataN19t_15_17 := rfl

def dataN19t_16_13 : RingExpr := (.mul (.var 10) (.mul (.var 9) (.mul (.pow (.var 8) 2) (.add (.var 2) (.add (.mul (.var 1) (.var 3)) (.add (.mul (.int (-2)) (.mul (.var 3) (.var 4))) (.add (.mul (.int 2) (.mul (.var 4) (.pow (.var 2) 2))) (.add (.mul (.int (-2)) (.mul (.var 0) (.mul (.var 2) (.mul (.var 4) (.pow (.var 3) 2))))) (.mul (.int 2) (.mul (.var 1) (.mul (.var 2) (.mul (.var 3) (.var 4)))))))))))))
theorem dataN19t_16_13_binding : litN19tExpr 16 13=dataN19t_16_13 := rfl

def dataN19t_16_15 : RingExpr := (.mul (.var 10) (.mul (.var 9) (.mul (.pow (.var 8) 2) (.add (.mul (.int (-1)) (.var 2)) (.add (.mul (.int (-1)) (.mul (.var 1) (.var 3))) (.add (.mul (.int (-2)) (.mul (.var 4) (.pow (.var 2) 2))) (.add (.mul (.int 2) (.mul (.var 3) (.var 4))) (.add (.mul (.int (-2)) (.mul (.var 1) (.mul (.var 2) (.mul (.var 3) (.var 4))))) (.mul (.int 2) (.mul (.var 0) (.mul (.var 2) (.mul (.var 4) (.pow (.var 3) 2)))))))))))))
theorem dataN19t_16_15_binding : litN19tExpr 16 15=dataN19t_16_15 := rfl

def dataN19t_16_16 : RingExpr := (.add (.var 1) (.mul (.int (-1)) (.mul (.var 0) (.var 3))))
theorem dataN19t_16_16_binding : litN19tExpr 16 16=dataN19t_16_16 := rfl

def dataN19t_16_17 : RingExpr := (.add (.mul (.int (-1)) (.var 1)) (.mul (.var 0) (.var 3)))
theorem dataN19t_16_17_binding : litN19tExpr 16 17=dataN19t_16_17 := rfl

def dataN19t_17_13 : RingExpr := (.mul (.var 10) (.mul (.var 9) (.mul (.pow (.var 8) 2) (.add (.var 2) (.add (.mul (.var 1) (.var 3)) (.add (.mul (.int (-1)) (.mul (.var 3) (.var 4))) (.add (.mul (.int 2) (.mul (.pow (.var 2) 3) (.pow (.var 4) 2))) (.add (.mul (.int 3) (.mul (.var 4) (.pow (.var 2) 2))) (.add (.mul (.int (-2)) (.mul (.var 0) (.mul (.var 2) (.mul (.var 4) (.pow (.var 3) 2))))) (.add (.mul (.int (-2)) (.mul (.var 0) (.mul (.pow (.var 2) 2) (.mul (.pow (.var 3) 2) (.pow (.var 4) 2))))) (.add (.mul (.int 2) (.mul (.var 1) (.mul (.var 3) (.mul (.pow (.var 2) 2) (.pow (.var 4) 2))))) (.mul (.int 3) (.mul (.var 1) (.mul (.var 2) (.mul (.var 3) (.var 4))))))))))))))))
theorem dataN19t_17_13_binding : litN19tExpr 17 13=dataN19t_17_13 := rfl

def dataN19t_17_15 : RingExpr := (.mul (.var 10) (.mul (.var 9) (.mul (.pow (.var 8) 2) (.add (.mul (.int (-1)) (.var 2)) (.add (.mul (.var 3) (.var 4)) (.add (.mul (.int (-1)) (.mul (.var 1) (.var 3))) (.add (.mul (.int (-3)) (.mul (.var 4) (.pow (.var 2) 2))) (.add (.mul (.int (-2)) (.mul (.pow (.var 2) 3) (.pow (.var 4) 2))) (.add (.mul (.int (-3)) (.mul (.var 1) (.mul (.var 2) (.mul (.var 3) (.var 4))))) (.add (.mul (.int (-2)) (.mul (.var 1) (.mul (.var 3) (.mul (.pow (.var 2) 2) (.pow (.var 4) 2))))) (.add (.mul (.int 2) (.mul (.var 0) (.mul (.var 2) (.mul (.var 4) (.pow (.var 3) 2))))) (.mul (.int 2) (.mul (.var 0) (.mul (.pow (.var 2) 2) (.mul (.pow (.var 3) 2) (.pow (.var 4) 2))))))))))))))))
theorem dataN19t_17_15_binding : litN19tExpr 17 15=dataN19t_17_15 := rfl

def dataN19t_17_16 : RingExpr := (.mul (.var 10) (.mul (.var 8) (.add (.var 2) (.add (.mul (.int (-2)) (.mul (.var 0) (.pow (.var 3) 2))) (.add (.mul (.int 2) (.mul (.var 1) (.var 3))) (.add (.mul (.int 2) (.mul (.var 4) (.pow (.var 2) 2))) (.add (.mul (.int (-2)) (.mul (.var 0) (.mul (.var 2) (.mul (.var 4) (.pow (.var 3) 2))))) (.mul (.int 2) (.mul (.var 1) (.mul (.var 2) (.mul (.var 3) (.var 4))))))))))))
theorem dataN19t_17_16_binding : litN19tExpr 17 16=dataN19t_17_16 := rfl

def dataN19t_17_17 : RingExpr := (.mul (.var 10) (.mul (.var 8) (.add (.mul (.int (-1)) (.var 2)) (.add (.mul (.int (-2)) (.mul (.var 1) (.var 3))) (.add (.mul (.int (-2)) (.mul (.var 4) (.pow (.var 2) 2))) (.add (.mul (.int 2) (.mul (.var 0) (.pow (.var 3) 2))) (.add (.mul (.int (-2)) (.mul (.var 1) (.mul (.var 2) (.mul (.var 3) (.var 4))))) (.mul (.int 2) (.mul (.var 0) (.mul (.var 2) (.mul (.var 4) (.pow (.var 3) 2))))))))))))
theorem dataN19t_17_17_binding : litN19tExpr 17 17=dataN19t_17_17 := rfl

def dataCz_0_0 : RingExpr := (.int 1)
theorem dataCz_0_0_binding : litCzExpr 0 0=dataCz_0_0 := rfl

def dataCz_1_1 : RingExpr := (.int 1)
theorem dataCz_1_1_binding : litCzExpr 1 1=dataCz_1_1 := rfl

def dataCz_2_2 : RingExpr := (.int 1)
theorem dataCz_2_2_binding : litCzExpr 2 2=dataCz_2_2 := rfl

def dataCz_3_3 : RingExpr := (.int 1)
theorem dataCz_3_3_binding : litCzExpr 3 3=dataCz_3_3 := rfl

def dataCz_4_4 : RingExpr := (.int 1)
theorem dataCz_4_4_binding : litCzExpr 4 4=dataCz_4_4 := rfl

def dataCz_5_5 : RingExpr := (.int 1)
theorem dataCz_5_5_binding : litCzExpr 5 5=dataCz_5_5 := rfl

def dataCb_0_0 : RingExpr := (.int 1)
theorem dataCb_0_0_binding : litCbExpr 0 0=dataCb_0_0 := rfl

def dataCb_0_12 : RingExpr := (.int 1)
theorem dataCb_0_12_binding : litCbExpr 0 12=dataCb_0_12 := rfl

def dataCb_1_1 : RingExpr := (.int 1)
theorem dataCb_1_1_binding : litCbExpr 1 1=dataCb_1_1 := rfl

def dataCb_1_13 : RingExpr := (.int 1)
theorem dataCb_1_13_binding : litCbExpr 1 13=dataCb_1_13 := rfl

def dataCb_2_2 : RingExpr := (.int 1)
theorem dataCb_2_2_binding : litCbExpr 2 2=dataCb_2_2 := rfl

def dataCb_2_14 : RingExpr := (.int 1)
theorem dataCb_2_14_binding : litCbExpr 2 14=dataCb_2_14 := rfl

def dataCb_3_3 : RingExpr := (.int 1)
theorem dataCb_3_3_binding : litCbExpr 3 3=dataCb_3_3 := rfl

def dataCb_3_15 : RingExpr := (.int 1)
theorem dataCb_3_15_binding : litCbExpr 3 15=dataCb_3_15 := rfl

def dataCb_4_4 : RingExpr := (.int 1)
theorem dataCb_4_4_binding : litCbExpr 4 4=dataCb_4_4 := rfl

def dataCb_4_16 : RingExpr := (.int 1)
theorem dataCb_4_16_binding : litCbExpr 4 16=dataCb_4_16 := rfl

def dataCb_5_5 : RingExpr := (.int 1)
theorem dataCb_5_5_binding : litCbExpr 5 5=dataCb_5_5 := rfl

def dataCb_5_17 : RingExpr := (.int 1)
theorem dataCb_5_17_binding : litCbExpr 5 17=dataCb_5_17 := rfl

def dataCt_0_0 : RingExpr := (.int 1)
theorem dataCt_0_0_binding : litCtExpr 0 0=dataCt_0_0 := rfl

def dataCt_0_12 : RingExpr := (.int 1)
theorem dataCt_0_12_binding : litCtExpr 0 12=dataCt_0_12 := rfl

def dataCt_1_1 : RingExpr := (.int 1)
theorem dataCt_1_1_binding : litCtExpr 1 1=dataCt_1_1 := rfl

def dataCt_1_13 : RingExpr := (.int 1)
theorem dataCt_1_13_binding : litCtExpr 1 13=dataCt_1_13 := rfl

def dataCt_2_2 : RingExpr := (.int 1)
theorem dataCt_2_2_binding : litCtExpr 2 2=dataCt_2_2 := rfl

def dataCt_2_14 : RingExpr := (.int 1)
theorem dataCt_2_14_binding : litCtExpr 2 14=dataCt_2_14 := rfl

def dataCt_3_3 : RingExpr := (.int 1)
theorem dataCt_3_3_binding : litCtExpr 3 3=dataCt_3_3 := rfl

def dataCt_3_15 : RingExpr := (.int 1)
theorem dataCt_3_15_binding : litCtExpr 3 15=dataCt_3_15 := rfl

def dataCt_4_4 : RingExpr := (.int 1)
theorem dataCt_4_4_binding : litCtExpr 4 4=dataCt_4_4 := rfl

def dataCt_4_16 : RingExpr := (.int 1)
theorem dataCt_4_16_binding : litCtExpr 4 16=dataCt_4_16 := rfl

def dataCt_5_5 : RingExpr := (.int 1)
theorem dataCt_5_5_binding : litCtExpr 5 5=dataCt_5_5 := rfl

def dataCt_5_17 : RingExpr := (.int 1)
theorem dataCt_5_17_binding : litCtExpr 5 17=dataCt_5_17 := rfl

def datapFz_0_6 : RingExpr := (.int 1)
theorem datapFz_0_6_binding : litpFzExpr 0 6=datapFz_0_6 := rfl

def datapFz_0_7 : RingExpr := (.var 2)
theorem datapFz_0_7_binding : litpFzExpr 0 7=datapFz_0_7 := rfl

def datapFz_0_9 : RingExpr := (.mul (.int (-1)) (.var 2))
theorem datapFz_0_9_binding : litpFzExpr 0 9=datapFz_0_9 := rfl

def datapFz_0_10 : RingExpr := (.var 3)
theorem datapFz_0_10_binding : litpFzExpr 0 10=datapFz_0_10 := rfl

def datapFz_0_11 : RingExpr := (.mul (.int (-1)) (.var 3))
theorem datapFz_0_11_binding : litpFzExpr 0 11=datapFz_0_11 := rfl

def datapFb_0_0 : RingExpr := (.int 1)
theorem datapFb_0_0_binding : litpFbExpr 0 0=datapFb_0_0 := rfl

def datapFb_0_1 : RingExpr := (.var 2)
theorem datapFb_0_1_binding : litpFbExpr 0 1=datapFb_0_1 := rfl

def datapFb_0_3 : RingExpr := (.mul (.int (-1)) (.var 2))
theorem datapFb_0_3_binding : litpFbExpr 0 3=datapFb_0_3 := rfl

def datapFb_0_4 : RingExpr := (.var 3)
theorem datapFb_0_4_binding : litpFbExpr 0 4=datapFb_0_4 := rfl

def datapFb_0_5 : RingExpr := (.mul (.int (-1)) (.var 3))
theorem datapFb_0_5_binding : litpFbExpr 0 5=datapFb_0_5 := rfl

def datapFb_0_12 : RingExpr := (.int 1)
theorem datapFb_0_12_binding : litpFbExpr 0 12=datapFb_0_12 := rfl

def datapFb_0_13 : RingExpr := (.var 2)
theorem datapFb_0_13_binding : litpFbExpr 0 13=datapFb_0_13 := rfl

def datapFb_0_15 : RingExpr := (.mul (.int (-1)) (.var 2))
theorem datapFb_0_15_binding : litpFbExpr 0 15=datapFb_0_15 := rfl

def datapFb_0_16 : RingExpr := (.var 3)
theorem datapFb_0_16_binding : litpFbExpr 0 16=datapFb_0_16 := rfl

def datapFb_0_17 : RingExpr := (.mul (.int (-1)) (.var 3))
theorem datapFb_0_17_binding : litpFbExpr 0 17=datapFb_0_17 := rfl

def datapFt_0_0 : RingExpr := (.int 1)
theorem datapFt_0_0_binding : litpFtExpr 0 0=datapFt_0_0 := rfl

def datapFt_0_12 : RingExpr := (.int 1)
theorem datapFt_0_12_binding : litpFtExpr 0 12=datapFt_0_12 := rfl

def datapFt_0_13 : RingExpr := (.var 2)
theorem datapFt_0_13_binding : litpFtExpr 0 13=datapFt_0_13 := rfl

def datapFt_0_15 : RingExpr := (.mul (.int (-1)) (.var 2))
theorem datapFt_0_15_binding : litpFtExpr 0 15=datapFt_0_15 := rfl

def datapFt_0_16 : RingExpr := (.var 3)
theorem datapFt_0_16_binding : litpFtExpr 0 16=datapFt_0_16 := rfl

def datapFt_0_17 : RingExpr := (.mul (.int (-1)) (.var 3))
theorem datapFt_0_17_binding : litpFtExpr 0 17=datapFt_0_17 := rfl

def datapJz_0_18 : RingExpr := (.add (.var 11) (.add (.mul (.var 12) (.var 2)) (.add (.mul (.var 15) (.var 3)) (.add (.mul (.int (-1)) (.mul (.var 14) (.var 2))) (.mul (.int (-1)) (.mul (.var 16) (.var 3)))))))
theorem datapJz_0_18_binding : litpJzExpr 0 18=datapJz_0_18 := rfl

def datapJb_0_18 : RingExpr := (.var 11)
theorem datapJb_0_18_binding : litpJbExpr 0 18=datapJb_0_18 := rfl

def datapJt_0_6 : RingExpr := (.int 1)
theorem datapJt_0_6_binding : litpJtExpr 0 6=datapJt_0_6 := rfl

def datapJt_0_7 : RingExpr := (.var 2)
theorem datapJt_0_7_binding : litpJtExpr 0 7=datapJt_0_7 := rfl

def datapJt_0_9 : RingExpr := (.mul (.int (-1)) (.var 2))
theorem datapJt_0_9_binding : litpJtExpr 0 9=datapJt_0_9 := rfl

def datapJt_0_10 : RingExpr := (.var 3)
theorem datapJt_0_10_binding : litpJtExpr 0 10=datapJt_0_10 := rfl

def datapJt_0_11 : RingExpr := (.mul (.int (-1)) (.var 3))
theorem datapJt_0_11_binding : litpJtExpr 0 11=datapJt_0_11 := rfl

def datapJt_0_18 : RingExpr := (.add (.mul (.var 14) (.var 2)) (.add (.mul (.var 16) (.var 3)) (.add (.mul (.int (-1)) (.mul (.var 12) (.var 2))) (.mul (.int (-1)) (.mul (.var 15) (.var 3))))))
theorem datapJt_0_18_binding : litpJtExpr 0 18=datapJt_0_18 := rfl

def datapKb_0_18 : RingExpr := (.add (.mul (.var 14) (.var 2)) (.add (.mul (.var 16) (.var 3)) (.add (.mul (.int (-1)) (.mul (.var 12) (.var 2))) (.mul (.int (-1)) (.mul (.var 15) (.var 3))))))
theorem datapKb_0_18_binding : litpKbExpr 0 18=datapKb_0_18 := rfl

def datapKt_0_13 : RingExpr := (.mul (.int (-1)) (.var 2))
theorem datapKt_0_13_binding : litpKtExpr 0 13=datapKt_0_13 := rfl

def datapKt_0_15 : RingExpr := (.var 2)
theorem datapKt_0_15_binding : litpKtExpr 0 15=datapKt_0_15 := rfl

def datapKt_0_16 : RingExpr := (.mul (.int (-1)) (.var 3))
theorem datapKt_0_16_binding : litpKtExpr 0 16=datapKt_0_16 := rfl

def datapKt_0_17 : RingExpr := (.var 3)
theorem datapKt_0_17_binding : litpKtExpr 0 17=datapKt_0_17 := rfl

def dataN9z_0_3 : RingExpr := (.mul (.var 7) (.mul (.var 9) (.mul (.pow (.var 10) 2) (.mul (.pow (.var 8) 3) (.add (.var 2) (.add (.mul (.var 1) (.var 3)) (.add (.mul (.int (-2)) (.mul (.var 3) (.var 4))) (.add (.mul (.int 4) (.mul (.var 4) (.pow (.var 2) 2))) (.add (.mul (.int 4) (.mul (.pow (.var 2) 3) (.pow (.var 4) 2))) (.add (.mul (.int (-4)) (.mul (.var 0) (.mul (.pow (.var 3) 3) (.pow (.var 4) 2)))) (.add (.mul (.int (-4)) (.mul (.var 2) (.mul (.var 3) (.pow (.var 4) 2)))) (.add (.mul (.int (-4)) (.mul (.var 0) (.mul (.pow (.var 2) 2) (.mul (.pow (.var 3) 2) (.pow (.var 4) 2))))) (.add (.mul (.int (-2)) (.mul (.var 0) (.mul (.var 2) (.mul (.var 4) (.pow (.var 3) 2))))) (.add (.mul (.int 4) (.mul (.var 1) (.mul (.var 2) (.mul (.var 3) (.var 4))))) (.mul (.int 4) (.mul (.var 1) (.mul (.var 3) (.mul (.pow (.var 2) 2) (.pow (.var 4) 2)))))))))))))))))))
theorem dataN9z_0_3_binding : litN9zExpr 0 3=dataN9z_0_3 := rfl

def dataN9z_0_4 : RingExpr := (.mul (.var 7) (.mul (.var 10) (.mul (.var 8) (.add (.var 1) (.add (.mul (.int 2) (.mul (.var 1) (.mul (.var 2) (.var 4)))) (.mul (.int (-4)) (.mul (.var 0) (.mul (.var 2) (.mul (.var 3) (.var 4))))))))))
theorem dataN9z_0_4_binding : litN9zExpr 0 4=dataN9z_0_4 := rfl

def dataN9z_0_5 : RingExpr := (.mul (.var 7) (.mul (.var 10) (.mul (.var 8) (.add (.int (-1)) (.add (.mul (.int (-2)) (.mul (.var 2) (.var 4))) (.mul (.int (-2)) (.mul (.var 0) (.mul (.var 4) (.pow (.var 3) 2)))))))))
theorem dataN9z_0_5_binding : litN9zExpr 0 5=dataN9z_0_5 := rfl

def dataN9z_0_8 : RingExpr := (.mul (.var 7) (.mul (.var 9) (.mul (.pow (.var 10) 2) (.mul (.pow (.var 8) 3) (.add (.mul (.int (-1)) (.mul (.var 11) (.var 2))) (.add (.mul (.int (-1)) (.mul (.var 11) (.mul (.var 1) (.var 3)))) (.add (.mul (.int (-4)) (.mul (.var 11) (.mul (.var 4) (.pow (.var 2) 2)))) (.add (.mul (.int (-4)) (.mul (.var 11) (.mul (.pow (.var 2) 3) (.pow (.var 4) 2)))) (.add (.mul (.int 2) (.mul (.var 11) (.mul (.var 3) (.var 4)))) (.add (.mul (.int 2) (.mul (.var 15) (.mul (.var 4) (.pow (.var 3) 2)))) (.add (.mul (.int (-2)) (.mul (.var 12) (.mul (.var 1) (.mul (.var 4) (.pow (.var 3) 2))))) (.add (.mul (.int 4) (.mul (.var 11) (.mul (.var 0) (.mul (.pow (.var 3) 3) (.pow (.var 4) 2))))) (.add (.mul (.int 4) (.mul (.var 11) (.mul (.var 2) (.mul (.var 3) (.pow (.var 4) 2))))) (.add (.mul (.int 4) (.mul (.var 14) (.mul (.var 0) (.mul (.var 4) (.pow (.var 3) 3))))) (.add (.mul (.int 4) (.mul (.var 15) (.mul (.var 0) (.mul (.pow (.var 3) 4) (.pow (.var 4) 2))))) (.add (.mul (.int 4) (.mul (.var 15) (.mul (.var 2) (.mul (.pow (.var 3) 2) (.pow (.var 4) 2))))) (.add (.mul (.int (-4)) (.mul (.var 11) (.mul (.var 1) (.mul (.var 2) (.mul (.var 3) (.var 4)))))) (.add (.mul (.int (-4)) (.mul (.var 11) (.mul (.var 1) (.mul (.var 3) (.mul (.pow (.var 2) 2) (.pow (.var 4) 2)))))) (.add (.mul (.int (-4)) (.mul (.var 12) (.mul (.var 1) (.mul (.var 2) (.mul (.pow (.var 3) 2) (.pow (.var 4) 2)))))) (.add (.mul (.int 2) (.mul (.var 11) (.mul (.var 0) (.mul (.var 2) (.mul (.var 4) (.pow (.var 3) 2)))))) (.add (.mul (.int 4) (.mul (.var 11) (.mul (.var 0) (.mul (.pow (.var 2) 2) (.mul (.pow (.var 3) 2) (.pow (.var 4) 2)))))) (.mul (.int 8) (.mul (.var 12) (.mul (.var 0) (.mul (.var 2) (.mul (.pow (.var 3) 3) (.pow (.var 4) 2)))))))))))))))))))))))))))
theorem dataN9z_0_8_binding : litN9zExpr 0 8=dataN9z_0_8 := rfl

def dataN9z_1_3 : RingExpr := (.mul (.var 7) (.mul (.var 9) (.mul (.pow (.var 10) 2) (.mul (.pow (.var 8) 4) (.add (.mul (.int (-1)) (.pow (.var 2) 2)) (.add (.mul (.int (-4)) (.mul (.var 4) (.pow (.var 2) 3))) (.add (.mul (.int (-4)) (.mul (.pow (.var 2) 4) (.pow (.var 4) 2))) (.add (.mul (.int (-4)) (.mul (.pow (.var 3) 2) (.pow (.var 4) 2))) (.add (.mul (.int (-1)) (.mul (.var 1) (.mul (.var 2) (.var 3)))) (.add (.mul (.int 2) (.mul (.var 0) (.mul (.var 4) (.pow (.var 3) 3)))) (.add (.mul (.int 2) (.mul (.var 1) (.mul (.var 4) (.pow (.var 3) 2)))) (.add (.mul (.int 4) (.mul (.var 2) (.mul (.var 3) (.var 4)))) (.add (.mul (.int 8) (.mul (.var 3) (.mul (.pow (.var 2) 2) (.pow (.var 4) 2)))) (.add (.mul (.int (-4)) (.mul (.var 1) (.mul (.var 3) (.mul (.var 4) (.pow (.var 2) 2))))) (.add (.mul (.int (-4)) (.mul (.var 1) (.mul (.var 3) (.mul (.pow (.var 2) 3) (.pow (.var 4) 2))))) (.add (.mul (.int 2) (.mul (.var 0) (.mul (.var 4) (.mul (.pow (.var 2) 2) (.pow (.var 3) 2))))) (.add (.mul (.int 4) (.mul (.var 0) (.mul (.pow (.var 2) 3) (.mul (.pow (.var 3) 2) (.pow (.var 4) 2))))) (.mul (.int 4) (.mul (.var 1) (.mul (.var 2) (.mul (.pow (.var 3) 2) (.pow (.var 4) 2))))))))))))))))))))))
theorem dataN9z_1_3_binding : litN9zExpr 1 3=dataN9z_1_3 := rfl

def dataN9z_1_4 : RingExpr := (.mul (.var 7) (.mul (.var 10) (.mul (.pow (.var 8) 2) (.add (.mul (.int (-1)) (.mul (.var 1) (.var 2))) (.add (.mul (.int (-2)) (.mul (.var 0) (.mul (.var 4) (.pow (.var 3) 2)))) (.add (.mul (.int (-2)) (.mul (.var 1) (.mul (.var 4) (.pow (.var 2) 2)))) (.add (.mul (.int 2) (.mul (.var 0) (.mul (.var 2) (.var 3)))) (.add (.mul (.int 2) (.mul (.var 1) (.mul (.var 3) (.var 4)))) (.mul (.int 4) (.mul (.var 0) (.mul (.var 3) (.mul (.var 4) (.pow (.var 2) 2)))))))))))))
theorem dataN9z_1_4_binding : litN9zExpr 1 4=dataN9z_1_4 := rfl

def dataN9z_1_5 : RingExpr := (.mul (.var 7) (.mul (.var 10) (.mul (.pow (.var 8) 2) (.add (.var 2) (.add (.mul (.int (-2)) (.mul (.var 3) (.var 4))) (.add (.mul (.int 2) (.mul (.var 0) (.pow (.var 3) 2))) (.add (.mul (.int 2) (.mul (.var 4) (.pow (.var 2) 2))) (.mul (.int 2) (.mul (.var 0) (.mul (.var 2) (.mul (.var 4) (.pow (.var 3) 2))))))))))))
theorem dataN9z_1_5_binding : litN9zExpr 1 5=dataN9z_1_5 := rfl

def dataN9z_1_8 : RingExpr := (.mul (.var 7) (.mul (.var 9) (.mul (.pow (.var 10) 2) (.mul (.pow (.var 8) 4) (.add (.mul (.var 11) (.pow (.var 2) 2)) (.add (.mul (.int 4) (.mul (.var 11) (.mul (.var 4) (.pow (.var 2) 3)))) (.add (.mul (.int 4) (.mul (.var 11) (.mul (.pow (.var 2) 4) (.pow (.var 4) 2)))) (.add (.mul (.int 4) (.mul (.var 11) (.mul (.pow (.var 3) 2) (.pow (.var 4) 2)))) (.add (.mul (.int 4) (.mul (.var 15) (.mul (.pow (.var 3) 3) (.pow (.var 4) 2)))) (.add (.mul (.var 11) (.mul (.var 1) (.mul (.var 2) (.var 3)))) (.add (.mul (.int (-8)) (.mul (.var 11) (.mul (.var 3) (.mul (.pow (.var 2) 2) (.pow (.var 4) 2))))) (.add (.mul (.int (-4)) (.mul (.var 11) (.mul (.var 2) (.mul (.var 3) (.var 4))))) (.add (.mul (.int (-4)) (.mul (.var 12) (.mul (.var 1) (.mul (.pow (.var 3) 3) (.pow (.var 4) 2))))) (.add (.mul (.int (-4)) (.mul (.var 15) (.mul (.var 0) (.mul (.var 4) (.pow (.var 3) 4))))) (.add (.mul (.int (-4)) (.mul (.var 15) (.mul (.pow (.var 2) 2) (.mul (.pow (.var 3) 2) (.pow (.var 4) 2))))) (.add (.mul (.int (-2)) (.mul (.var 11) (.mul (.var 0) (.mul (.var 4) (.pow (.var 3) 3))))) (.add (.mul (.int (-2)) (.mul (.var 11) (.mul (.var 1) (.mul (.var 4) (.pow (.var 3) 2))))) (.add (.mul (.int (-2)) (.mul (.var 15) (.mul (.var 2) (.mul (.var 4) (.pow (.var 3) 2))))) (.add (.mul (.int 4) (.mul (.var 12) (.mul (.var 0) (.mul (.pow (.var 3) 4) (.pow (.var 4) 2))))) (.add (.mul (.int 4) (.mul (.var 16) (.mul (.var 0) (.mul (.var 4) (.pow (.var 3) 4))))) (.add (.mul (.int (-8)) (.mul (.var 12) (.mul (.var 0) (.mul (.pow (.var 2) 2) (.mul (.pow (.var 3) 3) (.pow (.var 4) 2)))))) (.add (.mul (.int (-4)) (.mul (.var 11) (.mul (.var 0) (.mul (.pow (.var 2) 3) (.mul (.pow (.var 3) 2) (.pow (.var 4) 2)))))) (.add (.mul (.int (-4)) (.mul (.var 11) (.mul (.var 1) (.mul (.var 2) (.mul (.pow (.var 3) 2) (.pow (.var 4) 2)))))) (.add (.mul (.int (-4)) (.mul (.var 12) (.mul (.var 0) (.mul (.var 2) (.mul (.var 4) (.pow (.var 3) 3)))))) (.add (.mul (.int (-4)) (.mul (.var 15) (.mul (.var 0) (.mul (.var 2) (.mul (.pow (.var 3) 4) (.pow (.var 4) 2)))))) (.add (.mul (.int (-2)) (.mul (.var 11) (.mul (.var 0) (.mul (.var 4) (.mul (.pow (.var 2) 2) (.pow (.var 3) 2)))))) (.add (.mul (.int 2) (.mul (.var 12) (.mul (.var 1) (.mul (.var 2) (.mul (.var 4) (.pow (.var 3) 2)))))) (.add (.mul (.int 4) (.mul (.var 11) (.mul (.var 1) (.mul (.var 3) (.mul (.var 4) (.pow (.var 2) 2)))))) (.add (.mul (.int 4) (.mul (.var 11) (.mul (.var 1) (.mul (.var 3) (.mul (.pow (.var 2) 3) (.pow (.var 4) 2)))))) (.mul (.int 4) (.mul (.var 12) (.mul (.var 1) (.mul (.pow (.var 2) 2) (.mul (.pow (.var 3) 2) (.pow (.var 4) 2)))))))))))))))))))))))))))))))))))
theorem dataN9z_1_8_binding : litN9zExpr 1 8=dataN9z_1_8 := rfl

def dataN9z_2_3 : RingExpr := (.mul (.var 7) (.mul (.pow (.var 10) 3) (.mul (.pow (.var 8) 5) (.mul (.pow (.var 9) 2) (.add (.pow (.var 2) 2) (.add (.mul (.pow (.var 1) 2) (.pow (.var 3) 2)) (.add (.mul (.int 4) (.mul (.pow (.var 3) 2) (.pow (.var 4) 2))) (.add (.mul (.int 6) (.mul (.var 4) (.pow (.var 2) 3))) (.add (.mul (.int 8) (.mul (.pow (.var 2) 5) (.pow (.var 4) 3))) (.add (.mul (.int 12) (.mul (.pow (.var 2) 4) (.pow (.var 4) 2))) (.add (.mul (.int (-16)) (.mul (.var 3) (.mul (.pow (.var 2) 2) (.pow (.var 4) 2)))) (.add (.mul (.int (-16)) (.mul (.var 3) (.mul (.pow (.var 2) 3) (.pow (.var 4) 3)))) (.add (.mul (.int (-8)) (.mul (.var 1) (.mul (.pow (.var 3) 3) (.pow (.var 4) 3)))) (.add (.mul (.int (-4)) (.mul (.var 1) (.mul (.var 4) (.pow (.var 3) 2)))) (.add (.mul (.int (-4)) (.mul (.var 2) (.mul (.var 3) (.var 4)))) (.add (.mul (.int 2) (.mul (.var 1) (.mul (.var 2) (.var 3)))) (.add (.mul (.int 4) (.mul (.pow (.var 0) 2) (.mul (.pow (.var 3) 5) (.pow (.var 4) 2)))) (.add (.mul (.int 4) (.mul (.pow (.var 1) 2) (.mul (.pow (.var 3) 3) (.pow (.var 4) 2)))) (.add (.mul (.int 8) (.mul (.var 2) (.mul (.pow (.var 3) 2) (.pow (.var 4) 3)))) (.add (.mul (.int 16) (.mul (.var 0) (.mul (.pow (.var 3) 4) (.pow (.var 4) 3)))) (.add (.mul (.int (-8)) (.mul (.var 0) (.mul (.pow (.var 2) 2) (.mul (.pow (.var 3) 3) (.pow (.var 4) 3))))) (.add (.mul (.int (-8)) (.mul (.var 0) (.mul (.pow (.var 2) 3) (.mul (.pow (.var 3) 2) (.pow (.var 4) 2))))) (.add (.mul (.int (-8)) (.mul (.var 0) (.mul (.pow (.var 2) 4) (.mul (.pow (.var 3) 2) (.pow (.var 4) 3))))) (.add (.mul (.int (-8)) (.mul (.var 1) (.mul (.var 2) (.mul (.pow (.var 3) 2) (.pow (.var 4) 2))))) (.add (.mul (.int (-4)) (.mul (.var 0) (.mul (.var 1) (.mul (.pow (.var 3) 4) (.pow (.var 4) 2))))) (.add (.mul (.int (-4)) (.mul (.var 0) (.mul (.var 2) (.mul (.pow (.var 3) 3) (.pow (.var 4) 2))))) (.add (.mul (.int (-2)) (.mul (.var 0) (.mul (.var 4) (.mul (.pow (.var 2) 2) (.pow (.var 3) 2))))) (.add (.mul (.int 4) (.mul (.var 2) (.mul (.var 4) (.mul (.pow (.var 1) 2) (.pow (.var 3) 2))))) (.add (.mul (.int 4) (.mul (.pow (.var 1) 2) (.mul (.pow (.var 2) 2) (.mul (.pow (.var 3) 2) (.pow (.var 4) 2))))) (.add (.mul (.int 8) (.mul (.var 1) (.mul (.var 3) (.mul (.pow (.var 2) 4) (.pow (.var 4) 3))))) (.add (.mul (.int 8) (.mul (.var 2) (.mul (.pow (.var 0) 2) (.mul (.pow (.var 3) 5) (.pow (.var 4) 3))))) (.add (.mul (.int 8) (.mul (.var 2) (.mul (.pow (.var 1) 2) (.mul (.pow (.var 3) 3) (.pow (.var 4) 3))))) (.add (.mul (.int 10) (.mul (.var 1) (.mul (.var 3) (.mul (.var 4) (.pow (.var 2) 2))))) (.add (.mul (.int 16) (.mul (.var 1) (.mul (.var 3) (.mul (.pow (.var 2) 3) (.pow (.var 4) 2))))) (.add (.mul (.int (-16)) (.mul (.var 0) (.mul (.var 1) (.mul (.var 2) (.mul (.pow (.var 3) 4) (.pow (.var 4) 3)))))) (.add (.mul (.int (-4)) (.mul (.var 0) (.mul (.var 1) (.mul (.pow (.var 2) 2) (.mul (.pow (.var 3) 3) (.pow (.var 4) 2)))))) (.mul (.int (-2)) (.mul (.var 0) (.mul (.var 1) (.mul (.var 2) (.mul (.var 4) (.pow (.var 3) 3))))))))))))))))))))))))))))))))))))))))))
theorem dataN9z_2_3_binding : litN9zExpr 2 3=dataN9z_2_3 := rfl

def dataN9z_2_4 : RingExpr := (.mul (.var 7) (.mul (.var 9) (.mul (.pow (.var 10) 2) (.mul (.pow (.var 8) 3) (.add (.mul (.var 1) (.var 2)) (.add (.mul (.var 3) (.pow (.var 1) 2)) (.add (.mul (.int (-2)) (.mul (.var 1) (.mul (.var 3) (.var 4)))) (.add (.mul (.int 4) (.mul (.var 1) (.mul (.var 4) (.pow (.var 2) 2)))) (.add (.mul (.int 4) (.mul (.var 1) (.mul (.pow (.var 2) 3) (.pow (.var 4) 2)))) (.add (.mul (.int 4) (.mul (.pow (.var 0) 2) (.mul (.pow (.var 3) 4) (.pow (.var 4) 2)))) (.add (.mul (.int 4) (.mul (.pow (.var 1) 2) (.mul (.pow (.var 3) 2) (.pow (.var 4) 2)))) (.add (.mul (.int (-8)) (.mul (.var 0) (.mul (.var 1) (.mul (.pow (.var 3) 3) (.pow (.var 4) 2))))) (.add (.mul (.int (-8)) (.mul (.var 0) (.mul (.var 3) (.mul (.pow (.var 2) 3) (.pow (.var 4) 2))))) (.add (.mul (.int (-4)) (.mul (.var 0) (.mul (.var 3) (.mul (.var 4) (.pow (.var 2) 2))))) (.add (.mul (.int (-4)) (.mul (.var 1) (.mul (.var 2) (.mul (.var 3) (.pow (.var 4) 2))))) (.add (.mul (.int 2) (.mul (.var 2) (.mul (.var 3) (.mul (.var 4) (.pow (.var 1) 2))))) (.mul (.int 8) (.mul (.var 0) (.mul (.var 2) (.mul (.pow (.var 3) 2) (.pow (.var 4) 2)))))))))))))))))))))
theorem dataN9z_2_4_binding : litN9zExpr 2 4=dataN9z_2_4 := rfl

def dataN9z_2_5 : RingExpr := (.mul (.var 7) (.mul (.var 9) (.mul (.pow (.var 10) 2) (.mul (.pow (.var 8) 3) (.add (.mul (.int (-1)) (.var 2)) (.add (.mul (.int (-1)) (.mul (.var 1) (.var 3))) (.add (.mul (.int (-4)) (.mul (.var 4) (.pow (.var 2) 2))) (.add (.mul (.int (-4)) (.mul (.pow (.var 2) 3) (.pow (.var 4) 2))) (.add (.mul (.int 2) (.mul (.var 3) (.var 4))) (.add (.mul (.int (-4)) (.mul (.var 1) (.mul (.pow (.var 3) 2) (.pow (.var 4) 2)))) (.add (.mul (.int 4) (.mul (.var 2) (.mul (.var 3) (.pow (.var 4) 2)))) (.add (.mul (.int 8) (.mul (.var 0) (.mul (.pow (.var 3) 3) (.pow (.var 4) 2)))) (.add (.mul (.int (-4)) (.mul (.var 0) (.mul (.pow (.var 2) 2) (.mul (.pow (.var 3) 2) (.pow (.var 4) 2))))) (.add (.mul (.int (-2)) (.mul (.var 0) (.mul (.var 2) (.mul (.var 4) (.pow (.var 3) 2))))) (.add (.mul (.int (-2)) (.mul (.var 1) (.mul (.var 2) (.mul (.var 3) (.var 4))))) (.mul (.int 2) (.mul (.var 0) (.mul (.var 1) (.mul (.var 4) (.pow (.var 3) 3))))))))))))))))))))
theorem dataN9z_2_5_binding : litN9zExpr 2 5=dataN9z_2_5 := rfl

def dataN9z_2_8 : RingExpr := (.mul (.var 7) (.mul (.pow (.var 10) 3) (.mul (.pow (.var 8) 5) (.mul (.pow (.var 9) 2) (.add (.mul (.int (-1)) (.mul (.var 11) (.pow (.var 2) 2))) (.add (.mul (.int (-1)) (.mul (.var 11) (.mul (.pow (.var 1) 2) (.pow (.var 3) 2)))) (.add (.mul (.int (-12)) (.mul (.var 11) (.mul (.pow (.var 2) 4) (.pow (.var 4) 2)))) (.add (.mul (.int (-8)) (.mul (.var 11) (.mul (.pow (.var 2) 5) (.pow (.var 4) 3)))) (.add (.mul (.int (-6)) (.mul (.var 11) (.mul (.var 4) (.pow (.var 2) 3)))) (.add (.mul (.int (-4)) (.mul (.var 11) (.mul (.pow (.var 3) 2) (.pow (.var 4) 2)))) (.add (.mul (.int (-4)) (.mul (.var 15) (.mul (.pow (.var 3) 3) (.pow (.var 4) 2)))) (.add (.mul (.int (-16)) (.mul (.var 11) (.mul (.var 0) (.mul (.pow (.var 3) 4) (.pow (.var 4) 3))))) (.add (.mul (.int (-16)) (.mul (.var 15) (.mul (.var 0) (.mul (.pow (.var 3) 5) (.pow (.var 4) 3))))) (.add (.mul (.int (-8)) (.mul (.var 11) (.mul (.var 2) (.mul (.pow (.var 3) 2) (.pow (.var 4) 3))))) (.add (.mul (.int (-8)) (.mul (.var 12) (.mul (.pow (.var 0) 2) (.mul (.pow (.var 3) 6) (.pow (.var 4) 3))))) (.add (.mul (.int (-8)) (.mul (.var 12) (.mul (.pow (.var 1) 2) (.mul (.pow (.var 3) 4) (.pow (.var 4) 3))))) (.add (.mul (.int (-8)) (.mul (.var 14) (.mul (.var 0) (.mul (.pow (.var 3) 4) (.pow (.var 4) 2))))) (.add (.mul (.int (-8)) (.mul (.var 15) (.mul (.var 2) (.mul (.pow (.var 3) 3) (.pow (.var 4) 3))))) (.add (.mul (.int (-8)) (.mul (.var 16) (.mul (.pow (.var 0) 2) (.mul (.pow (.var 3) 6) (.pow (.var 4) 2))))) (.add (.mul (.int (-4)) (.mul (.var 11) (.mul (.pow (.var 1) 2) (.mul (.pow (.var 3) 3) (.pow (.var 4) 2))))) (.add (.mul (.int (-2)) (.mul (.var 11) (.mul (.var 1) (.mul (.var 2) (.var 3))))) (.add (.mul (.int (-2)) (.mul (.var 12) (.mul (.var 4) (.mul (.pow (.var 1) 2) (.pow (.var 3) 3))))) (.add (.mul (.int 2) (.mul (.var 15) (.mul (.var 1) (.mul (.var 4) (.pow (.var 3) 3))))) (.add (.mul (.int 2) (.mul (.var 15) (.mul (.var 2) (.mul (.var 4) (.pow (.var 3) 2))))) (.add (.mul (.int 4) (.mul (.var 11) (.mul (.var 1) (.mul (.var 4) (.pow (.var 3) 2))))) (.add (.mul (.int 4) (.mul (.var 11) (.mul (.var 2) (.mul (.var 3) (.var 4))))) (.add (.mul (.int 4) (.mul (.var 11) (.mul (.pow (.var 0) 2) (.mul (.pow (.var 3) 5) (.pow (.var 4) 2))))) (.add (.mul (.int 4) (.mul (.var 12) (.mul (.var 1) (.mul (.pow (.var 3) 3) (.pow (.var 4) 2))))) (.add (.mul (.int 8) (.mul (.var 11) (.mul (.var 1) (.mul (.pow (.var 3) 3) (.pow (.var 4) 3))))) (.add (.mul (.int 8) (.mul (.var 15) (.mul (.var 1) (.mul (.pow (.var 3) 4) (.pow (.var 4) 3))))) (.add (.mul (.int 8) (.mul (.var 15) (.mul (.pow (.var 0) 2) (.mul (.pow (.var 3) 6) (.pow (.var 4) 2))))) (.add (.mul (.int 8) (.mul (.var 15) (.mul (.pow (.var 2) 2) (.mul (.pow (.var 3) 2) (.pow (.var 4) 2))))) (.add (.mul (.int 8) (.mul (.var 15) (.mul (.pow (.var 2) 3) (.mul (.pow (.var 3) 2) (.pow (.var 4) 3))))) (.add (.mul (.int 16) (.mul (.var 11) (.mul (.var 3) (.mul (.pow (.var 2) 2) (.pow (.var 4) 2))))) (.add (.mul (.int 16) (.mul (.var 11) (.mul (.var 3) (.mul (.pow (.var 2) 3) (.pow (.var 4) 3))))) (.add (.mul (.int (-16)) (.mul (.var 11) (.mul (.var 1) (.mul (.var 3) (.mul (.pow (.var 2) 3) (.pow (.var 4) 2)))))) (.add (.mul (.int (-16)) (.mul (.var 12) (.mul (.var 0) (.mul (.var 2) (.mul (.pow (.var 3) 4) (.pow (.var 4) 3)))))) (.add (.mul (.int (-10)) (.mul (.var 11) (.mul (.var 1) (.mul (.var 3) (.mul (.var 4) (.pow (.var 2) 2)))))) (.add (.mul (.int (-8)) (.mul (.var 11) (.mul (.var 1) (.mul (.var 3) (.mul (.pow (.var 2) 4) (.pow (.var 4) 3)))))) (.add (.mul (.int (-8)) (.mul (.var 11) (.mul (.var 2) (.mul (.pow (.var 0) 2) (.mul (.pow (.var 3) 5) (.pow (.var 4) 3)))))) (.add (.mul (.int (-8)) (.mul (.var 11) (.mul (.var 2) (.mul (.pow (.var 1) 2) (.mul (.pow (.var 3) 3) (.pow (.var 4) 3)))))) (.add (.mul (.int (-8)) (.mul (.var 12) (.mul (.var 1) (.mul (.pow (.var 2) 2) (.mul (.pow (.var 3) 2) (.pow (.var 4) 2)))))) (.add (.mul (.int (-8)) (.mul (.var 12) (.mul (.var 1) (.mul (.pow (.var 2) 3) (.mul (.pow (.var 3) 2) (.pow (.var 4) 3)))))) (.add (.mul (.int (-8)) (.mul (.var 14) (.mul (.var 2) (.mul (.pow (.var 0) 2) (.mul (.pow (.var 3) 5) (.pow (.var 4) 2)))))) (.add (.mul (.int (-4)) (.mul (.var 11) (.mul (.var 2) (.mul (.var 4) (.mul (.pow (.var 1) 2) (.pow (.var 3) 2)))))) (.add (.mul (.int (-4)) (.mul (.var 11) (.mul (.pow (.var 1) 2) (.mul (.pow (.var 2) 2) (.mul (.pow (.var 3) 2) (.pow (.var 4) 2)))))) (.add (.mul (.int (-4)) (.mul (.var 12) (.mul (.var 2) (.mul (.pow (.var 1) 2) (.mul (.pow (.var 3) 3) (.pow (.var 4) 2)))))) (.add (.mul (.int (-4)) (.mul (.var 15) (.mul (.var 0) (.mul (.var 1) (.mul (.pow (.var 3) 5) (.pow (.var 4) 2)))))) (.add (.mul (.int (-2)) (.mul (.var 12) (.mul (.var 1) (.mul (.var 2) (.mul (.var 4) (.pow (.var 3) 2)))))) (.add (.mul (.int 2) (.mul (.var 11) (.mul (.var 0) (.mul (.var 4) (.mul (.pow (.var 2) 2) (.pow (.var 3) 2)))))) (.add (.mul (.int 4) (.mul (.var 11) (.mul (.var 0) (.mul (.var 1) (.mul (.pow (.var 3) 4) (.pow (.var 4) 2)))))) (.add (.mul (.int 4) (.mul (.var 11) (.mul (.var 0) (.mul (.var 2) (.mul (.pow (.var 3) 3) (.pow (.var 4) 2)))))) (.add (.mul (.int 4) (.mul (.var 14) (.mul (.var 0) (.mul (.var 1) (.mul (.var 4) (.pow (.var 3) 4)))))) (.add (.mul (.int 4) (.mul (.var 14) (.mul (.var 0) (.mul (.var 2) (.mul (.var 4) (.pow (.var 3) 3)))))) (.add (.mul (.int 4) (.mul (.var 15) (.mul (.var 0) (.mul (.var 2) (.mul (.pow (.var 3) 4) (.pow (.var 4) 2)))))) (.add (.mul (.int 4) (.mul (.var 15) (.mul (.var 1) (.mul (.var 2) (.mul (.pow (.var 3) 3) (.pow (.var 4) 2)))))) (.add (.mul (.int 8) (.mul (.var 11) (.mul (.var 0) (.mul (.pow (.var 2) 2) (.mul (.pow (.var 3) 3) (.pow (.var 4) 3)))))) (.add (.mul (.int 8) (.mul (.var 11) (.mul (.var 0) (.mul (.pow (.var 2) 3) (.mul (.pow (.var 3) 2) (.pow (.var 4) 2)))))) (.add (.mul (.int 8) (.mul (.var 11) (.mul (.var 0) (.mul (.pow (.var 2) 4) (.mul (.pow (.var 3) 2) (.pow (.var 4) 3)))))) (.add (.mul (.int 8) (.mul (.var 11) (.mul (.var 1) (.mul (.var 2) (.mul (.pow (.var 3) 2) (.pow (.var 4) 2)))))) (.add (.mul (.int 8) (.mul (.var 12) (.mul (.var 0) (.mul (.pow (.var 2) 2) (.mul (.pow (.var 3) 3) (.pow (.var 4) 2)))))) (.add (.mul (.int 8) (.mul (.var 12) (.mul (.var 1) (.mul (.var 2) (.mul (.pow (.var 3) 3) (.pow (.var 4) 3)))))) (.add (.mul (.int 8) (.mul (.var 12) (.mul (.var 2) (.mul (.pow (.var 0) 2) (.mul (.pow (.var 3) 5) (.pow (.var 4) 2)))))) (.add (.mul (.int 8) (.mul (.var 14) (.mul (.var 0) (.mul (.pow (.var 2) 2) (.mul (.pow (.var 3) 3) (.pow (.var 4) 2)))))) (.add (.mul (.int 8) (.mul (.var 15) (.mul (.var 0) (.mul (.pow (.var 2) 2) (.mul (.pow (.var 3) 4) (.pow (.var 4) 3)))))) (.add (.mul (.int 8) (.mul (.var 16) (.mul (.var 0) (.mul (.var 1) (.mul (.pow (.var 3) 5) (.pow (.var 4) 2)))))) (.add (.mul (.int 16) (.mul (.var 12) (.mul (.var 0) (.mul (.var 1) (.mul (.pow (.var 3) 5) (.pow (.var 4) 3)))))) (.add (.mul (.int 16) (.mul (.var 12) (.mul (.var 0) (.mul (.pow (.var 2) 3) (.mul (.pow (.var 3) 3) (.pow (.var 4) 3)))))) (.add (.mul (.int 2) (.mul (.var 11) (.mul (.var 0) (.mul (.var 1) (.mul (.var 2) (.mul (.var 4) (.pow (.var 3) 3))))))) (.add (.mul (.int 4) (.mul (.var 11) (.mul (.var 0) (.mul (.var 1) (.mul (.pow (.var 2) 2) (.mul (.pow (.var 3) 3) (.pow (.var 4) 2))))))) (.add (.mul (.int 8) (.mul (.var 14) (.mul (.var 0) (.mul (.var 1) (.mul (.var 2) (.mul (.pow (.var 3) 4) (.pow (.var 4) 2))))))) (.mul (.int 16) (.mul (.var 11) (.mul (.var 0) (.mul (.var 1) (.mul (.var 2) (.mul (.pow (.var 3) 4) (.pow (.var 4) 3))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
theorem dataN9z_2_8_binding : litN9zExpr 2 8=dataN9z_2_8 := rfl

def dataN9z_3_8 : RingExpr := (.var 14)
theorem dataN9z_3_8_binding : litN9zExpr 3 8=dataN9z_3_8 := rfl

def dataN9z_4_8 : RingExpr := (.var 16)
theorem dataN9z_4_8_binding : litN9zExpr 4 8=dataN9z_4_8 := rfl

def dataN9z_5_8 : RingExpr := (.mul (.var 10) (.mul (.var 9) (.mul (.pow (.var 8) 2) (.add (.mul (.var 14) (.var 2)) (.add (.mul (.var 14) (.mul (.var 1) (.var 3))) (.add (.mul (.int (-2)) (.mul (.var 14) (.mul (.var 3) (.var 4)))) (.add (.mul (.int 2) (.mul (.var 14) (.mul (.var 4) (.pow (.var 2) 2)))) (.add (.mul (.int (-2)) (.mul (.var 16) (.mul (.var 0) (.mul (.var 4) (.pow (.var 3) 3))))) (.add (.mul (.int 2) (.mul (.var 11) (.mul (.var 0) (.mul (.var 4) (.pow (.var 3) 2))))) (.add (.mul (.int 2) (.mul (.var 15) (.mul (.var 0) (.mul (.var 4) (.pow (.var 3) 3))))) (.add (.mul (.int 2) (.mul (.var 16) (.mul (.var 1) (.mul (.var 4) (.pow (.var 3) 2))))) (.add (.mul (.int (-2)) (.mul (.var 14) (.mul (.var 0) (.mul (.var 2) (.mul (.var 4) (.pow (.var 3) 2)))))) (.add (.mul (.int 2) (.mul (.var 12) (.mul (.var 0) (.mul (.var 2) (.mul (.var 4) (.pow (.var 3) 2)))))) (.mul (.int 2) (.mul (.var 14) (.mul (.var 1) (.mul (.var 2) (.mul (.var 3) (.var 4)))))))))))))))))))
theorem dataN9z_5_8_binding : litN9zExpr 5 8=dataN9z_5_8 := rfl

def dataN9b_0_0 : RingExpr := (.mul (.var 7) (.mul (.var 9) (.mul (.pow (.var 10) 2) (.mul (.pow (.var 8) 3) (.add (.var 2) (.add (.mul (.var 1) (.var 3)) (.add (.mul (.int (-2)) (.mul (.var 3) (.var 4))) (.add (.mul (.int 4) (.mul (.var 4) (.pow (.var 2) 2))) (.add (.mul (.int 4) (.mul (.pow (.var 2) 3) (.pow (.var 4) 2))) (.add (.mul (.int (-4)) (.mul (.var 0) (.mul (.pow (.var 3) 3) (.pow (.var 4) 2)))) (.add (.mul (.int (-4)) (.mul (.var 2) (.mul (.var 3) (.pow (.var 4) 2)))) (.add (.mul (.int (-4)) (.mul (.var 0) (.mul (.pow (.var 2) 2) (.mul (.pow (.var 3) 2) (.pow (.var 4) 2))))) (.add (.mul (.int (-2)) (.mul (.var 0) (.mul (.var 2) (.mul (.var 4) (.pow (.var 3) 2))))) (.add (.mul (.int 4) (.mul (.var 1) (.mul (.var 2) (.mul (.var 3) (.var 4))))) (.mul (.int 4) (.mul (.var 1) (.mul (.var 3) (.mul (.pow (.var 2) 2) (.pow (.var 4) 2)))))))))))))))))))
theorem dataN9b_0_0_binding : litN9bExpr 0 0=dataN9b_0_0 := rfl

def dataN9b_0_1 : RingExpr := (.mul (.var 7) (.mul (.var 10) (.mul (.var 8) (.add (.var 1) (.add (.mul (.int 2) (.mul (.var 1) (.mul (.var 2) (.var 4)))) (.mul (.int (-4)) (.mul (.var 0) (.mul (.var 2) (.mul (.var 3) (.var 4))))))))))
theorem dataN9b_0_1_binding : litN9bExpr 0 1=dataN9b_0_1 := rfl

def dataN9b_0_2 : RingExpr := (.mul (.var 7) (.mul (.var 10) (.mul (.var 8) (.add (.int (-1)) (.add (.mul (.int (-2)) (.mul (.var 2) (.var 4))) (.mul (.int (-2)) (.mul (.var 0) (.mul (.var 4) (.pow (.var 3) 2)))))))))
theorem dataN9b_0_2_binding : litN9bExpr 0 2=dataN9b_0_2 := rfl

def dataN9b_0_6 : RingExpr := (.mul (.var 10) (.mul (.var 8) (.add (.mul (.int (-1)) (.var 2)) (.add (.mul (.int (-1)) (.mul (.var 1) (.var 3))) (.add (.mul (.int (-2)) (.mul (.var 4) (.pow (.var 2) 2))) (.add (.mul (.int (-2)) (.mul (.var 1) (.mul (.var 2) (.mul (.var 3) (.var 4))))) (.mul (.int 2) (.mul (.var 0) (.mul (.var 2) (.mul (.var 4) (.pow (.var 3) 2)))))))))))
theorem dataN9b_0_6_binding : litN9bExpr 0 6=dataN9b_0_6 := rfl

def dataN9b_0_7 : RingExpr := (.add (.mul (.int (1)) (.pow (.var 10) 1)) (.add (.mul (.int (-1)) (.mul (.var 2) (.var 4))) (.add (.mul (.var 0) (.mul (.var 4) (.pow (.var 3) 2))) (.mul (.int (-1)) (.mul (.var 1) (.mul (.var 3) (.var 4)))))))
theorem dataN9b_0_7_binding : litN9bExpr 0 7=dataN9b_0_7 := rfl

def dataN9b_0_8 : RingExpr := (.mul (.var 7) (.mul (.var 9) (.mul (.pow (.var 10) 2) (.mul (.pow (.var 8) 3) (.add (.mul (.int (-1)) (.mul (.var 11) (.var 2))) (.add (.mul (.int (-1)) (.mul (.var 11) (.mul (.var 1) (.var 3)))) (.add (.mul (.int (-4)) (.mul (.var 11) (.mul (.var 4) (.pow (.var 2) 2)))) (.add (.mul (.int (-4)) (.mul (.var 11) (.mul (.pow (.var 2) 3) (.pow (.var 4) 2)))) (.add (.mul (.int 2) (.mul (.var 11) (.mul (.var 3) (.var 4)))) (.add (.mul (.int 2) (.mul (.var 15) (.mul (.var 4) (.pow (.var 3) 2)))) (.add (.mul (.int (-2)) (.mul (.var 12) (.mul (.var 1) (.mul (.var 4) (.pow (.var 3) 2))))) (.add (.mul (.int 4) (.mul (.var 11) (.mul (.var 0) (.mul (.pow (.var 3) 3) (.pow (.var 4) 2))))) (.add (.mul (.int 4) (.mul (.var 11) (.mul (.var 2) (.mul (.var 3) (.pow (.var 4) 2))))) (.add (.mul (.int 4) (.mul (.var 14) (.mul (.var 0) (.mul (.var 4) (.pow (.var 3) 3))))) (.add (.mul (.int 4) (.mul (.var 15) (.mul (.var 0) (.mul (.pow (.var 3) 4) (.pow (.var 4) 2))))) (.add (.mul (.int 4) (.mul (.var 15) (.mul (.var 2) (.mul (.pow (.var 3) 2) (.pow (.var 4) 2))))) (.add (.mul (.int (-4)) (.mul (.var 11) (.mul (.var 1) (.mul (.var 2) (.mul (.var 3) (.var 4)))))) (.add (.mul (.int (-4)) (.mul (.var 11) (.mul (.var 1) (.mul (.var 3) (.mul (.pow (.var 2) 2) (.pow (.var 4) 2)))))) (.add (.mul (.int (-4)) (.mul (.var 12) (.mul (.var 1) (.mul (.var 2) (.mul (.pow (.var 3) 2) (.pow (.var 4) 2)))))) (.add (.mul (.int 2) (.mul (.var 11) (.mul (.var 0) (.mul (.var 2) (.mul (.var 4) (.pow (.var 3) 2)))))) (.add (.mul (.int 4) (.mul (.var 11) (.mul (.var 0) (.mul (.pow (.var 2) 2) (.mul (.pow (.var 3) 2) (.pow (.var 4) 2)))))) (.mul (.int 8) (.mul (.var 12) (.mul (.var 0) (.mul (.var 2) (.mul (.pow (.var 3) 3) (.pow (.var 4) 2)))))))))))))))))))))))))))
theorem dataN9b_0_8_binding : litN9bExpr 0 8=dataN9b_0_8 := rfl

def dataN9b_1_0 : RingExpr := (.mul (.var 7) (.mul (.var 9) (.mul (.pow (.var 10) 2) (.mul (.pow (.var 8) 4) (.add (.mul (.int (-1)) (.pow (.var 2) 2)) (.add (.mul (.int (-4)) (.mul (.var 4) (.pow (.var 2) 3))) (.add (.mul (.int (-4)) (.mul (.pow (.var 2) 4) (.pow (.var 4) 2))) (.add (.mul (.int (-4)) (.mul (.pow (.var 3) 2) (.pow (.var 4) 2))) (.add (.mul (.int (-1)) (.mul (.var 1) (.mul (.var 2) (.var 3)))) (.add (.mul (.int 2) (.mul (.var 0) (.mul (.var 4) (.pow (.var 3) 3)))) (.add (.mul (.int 2) (.mul (.var 1) (.mul (.var 4) (.pow (.var 3) 2)))) (.add (.mul (.int 4) (.mul (.var 2) (.mul (.var 3) (.var 4)))) (.add (.mul (.int 8) (.mul (.var 3) (.mul (.pow (.var 2) 2) (.pow (.var 4) 2)))) (.add (.mul (.int (-4)) (.mul (.var 1) (.mul (.var 3) (.mul (.var 4) (.pow (.var 2) 2))))) (.add (.mul (.int (-4)) (.mul (.var 1) (.mul (.var 3) (.mul (.pow (.var 2) 3) (.pow (.var 4) 2))))) (.add (.mul (.int 2) (.mul (.var 0) (.mul (.var 4) (.mul (.pow (.var 2) 2) (.pow (.var 3) 2))))) (.add (.mul (.int 4) (.mul (.var 0) (.mul (.pow (.var 2) 3) (.mul (.pow (.var 3) 2) (.pow (.var 4) 2))))) (.mul (.int 4) (.mul (.var 1) (.mul (.var 2) (.mul (.pow (.var 3) 2) (.pow (.var 4) 2))))))))))))))))))))))
theorem dataN9b_1_0_binding : litN9bExpr 1 0=dataN9b_1_0 := rfl

def dataN9b_1_1 : RingExpr := (.mul (.var 7) (.mul (.var 10) (.mul (.pow (.var 8) 2) (.add (.mul (.int (-1)) (.mul (.var 1) (.var 2))) (.add (.mul (.int (-2)) (.mul (.var 0) (.mul (.var 4) (.pow (.var 3) 2)))) (.add (.mul (.int (-2)) (.mul (.var 1) (.mul (.var 4) (.pow (.var 2) 2)))) (.add (.mul (.int 2) (.mul (.var 0) (.mul (.var 2) (.var 3)))) (.add (.mul (.int 2) (.mul (.var 1) (.mul (.var 3) (.var 4)))) (.mul (.int 4) (.mul (.var 0) (.mul (.var 3) (.mul (.var 4) (.pow (.var 2) 2)))))))))))))
theorem dataN9b_1_1_binding : litN9bExpr 1 1=dataN9b_1_1 := rfl

def dataN9b_1_2 : RingExpr := (.mul (.var 7) (.mul (.var 10) (.mul (.pow (.var 8) 2) (.add (.var 2) (.add (.mul (.int (-2)) (.mul (.var 3) (.var 4))) (.add (.mul (.int 2) (.mul (.var 0) (.pow (.var 3) 2))) (.add (.mul (.int 2) (.mul (.var 4) (.pow (.var 2) 2))) (.mul (.int 2) (.mul (.var 0) (.mul (.var 2) (.mul (.var 4) (.pow (.var 3) 2))))))))))))
theorem dataN9b_1_2_binding : litN9bExpr 1 2=dataN9b_1_2 := rfl

def dataN9b_1_6 : RingExpr := (.mul (.var 10) (.mul (.var 9) (.mul (.pow (.var 8) 2) (.add (.var 2) (.add (.mul (.var 1) (.var 3)) (.add (.mul (.int (-1)) (.mul (.var 3) (.var 4))) (.add (.mul (.int 2) (.mul (.pow (.var 2) 3) (.pow (.var 4) 2))) (.add (.mul (.int 3) (.mul (.var 4) (.pow (.var 2) 2))) (.add (.mul (.int (-2)) (.mul (.var 0) (.mul (.var 2) (.mul (.var 4) (.pow (.var 3) 2))))) (.add (.mul (.int (-2)) (.mul (.var 0) (.mul (.pow (.var 2) 2) (.mul (.pow (.var 3) 2) (.pow (.var 4) 2))))) (.add (.mul (.int 2) (.mul (.var 1) (.mul (.var 3) (.mul (.pow (.var 2) 2) (.pow (.var 4) 2))))) (.mul (.int 3) (.mul (.var 1) (.mul (.var 2) (.mul (.var 3) (.var 4))))))))))))))))
theorem dataN9b_1_6_binding : litN9bExpr 1 6=dataN9b_1_6 := rfl

def dataN9b_1_7 : RingExpr := (.mul (.var 10) (.mul (.var 8) (.add (.var 2) (.add (.mul (.int (-2)) (.mul (.var 0) (.pow (.var 3) 2))) (.add (.mul (.int 2) (.mul (.var 1) (.var 3))) (.add (.mul (.int 2) (.mul (.var 4) (.pow (.var 2) 2))) (.add (.mul (.int (-2)) (.mul (.var 0) (.mul (.var 2) (.mul (.var 4) (.pow (.var 3) 2))))) (.mul (.int 2) (.mul (.var 1) (.mul (.var 2) (.mul (.var 3) (.var 4))))))))))))
theorem dataN9b_1_7_binding : litN9bExpr 1 7=dataN9b_1_7 := rfl

def dataN9b_1_8 : RingExpr := (.mul (.var 7) (.mul (.var 9) (.mul (.pow (.var 10) 2) (.mul (.pow (.var 8) 4) (.add (.mul (.var 11) (.pow (.var 2) 2)) (.add (.mul (.int 4) (.mul (.var 11) (.mul (.var 4) (.pow (.var 2) 3)))) (.add (.mul (.int 4) (.mul (.var 11) (.mul (.pow (.var 2) 4) (.pow (.var 4) 2)))) (.add (.mul (.int 4) (.mul (.var 11) (.mul (.pow (.var 3) 2) (.pow (.var 4) 2)))) (.add (.mul (.int 4) (.mul (.var 15) (.mul (.pow (.var 3) 3) (.pow (.var 4) 2)))) (.add (.mul (.var 11) (.mul (.var 1) (.mul (.var 2) (.var 3)))) (.add (.mul (.int (-8)) (.mul (.var 11) (.mul (.var 3) (.mul (.pow (.var 2) 2) (.pow (.var 4) 2))))) (.add (.mul (.int (-4)) (.mul (.var 11) (.mul (.var 2) (.mul (.var 3) (.var 4))))) (.add (.mul (.int (-4)) (.mul (.var 12) (.mul (.var 1) (.mul (.pow (.var 3) 3) (.pow (.var 4) 2))))) (.add (.mul (.int (-4)) (.mul (.var 15) (.mul (.var 0) (.mul (.var 4) (.pow (.var 3) 4))))) (.add (.mul (.int (-4)) (.mul (.var 15) (.mul (.pow (.var 2) 2) (.mul (.pow (.var 3) 2) (.pow (.var 4) 2))))) (.add (.mul (.int (-2)) (.mul (.var 11) (.mul (.var 0) (.mul (.var 4) (.pow (.var 3) 3))))) (.add (.mul (.int (-2)) (.mul (.var 11) (.mul (.var 1) (.mul (.var 4) (.pow (.var 3) 2))))) (.add (.mul (.int (-2)) (.mul (.var 15) (.mul (.var 2) (.mul (.var 4) (.pow (.var 3) 2))))) (.add (.mul (.int 4) (.mul (.var 12) (.mul (.var 0) (.mul (.pow (.var 3) 4) (.pow (.var 4) 2))))) (.add (.mul (.int 4) (.mul (.var 16) (.mul (.var 0) (.mul (.var 4) (.pow (.var 3) 4))))) (.add (.mul (.int (-8)) (.mul (.var 12) (.mul (.var 0) (.mul (.pow (.var 2) 2) (.mul (.pow (.var 3) 3) (.pow (.var 4) 2)))))) (.add (.mul (.int (-4)) (.mul (.var 11) (.mul (.var 0) (.mul (.pow (.var 2) 3) (.mul (.pow (.var 3) 2) (.pow (.var 4) 2)))))) (.add (.mul (.int (-4)) (.mul (.var 11) (.mul (.var 1) (.mul (.var 2) (.mul (.pow (.var 3) 2) (.pow (.var 4) 2)))))) (.add (.mul (.int (-4)) (.mul (.var 12) (.mul (.var 0) (.mul (.var 2) (.mul (.var 4) (.pow (.var 3) 3)))))) (.add (.mul (.int (-4)) (.mul (.var 15) (.mul (.var 0) (.mul (.var 2) (.mul (.pow (.var 3) 4) (.pow (.var 4) 2)))))) (.add (.mul (.int (-2)) (.mul (.var 11) (.mul (.var 0) (.mul (.var 4) (.mul (.pow (.var 2) 2) (.pow (.var 3) 2)))))) (.add (.mul (.int 2) (.mul (.var 12) (.mul (.var 1) (.mul (.var 2) (.mul (.var 4) (.pow (.var 3) 2)))))) (.add (.mul (.int 4) (.mul (.var 11) (.mul (.var 1) (.mul (.var 3) (.mul (.var 4) (.pow (.var 2) 2)))))) (.add (.mul (.int 4) (.mul (.var 11) (.mul (.var 1) (.mul (.var 3) (.mul (.pow (.var 2) 3) (.pow (.var 4) 2)))))) (.mul (.int 4) (.mul (.var 12) (.mul (.var 1) (.mul (.pow (.var 2) 2) (.mul (.pow (.var 3) 2) (.pow (.var 4) 2)))))))))))))))))))))))))))))))))))
theorem dataN9b_1_8_binding : litN9bExpr 1 8=dataN9b_1_8 := rfl

def dataN9b_2_0 : RingExpr := (.mul (.var 7) (.mul (.pow (.var 10) 3) (.mul (.pow (.var 8) 5) (.mul (.pow (.var 9) 2) (.add (.pow (.var 2) 2) (.add (.mul (.pow (.var 1) 2) (.pow (.var 3) 2)) (.add (.mul (.int 4) (.mul (.pow (.var 3) 2) (.pow (.var 4) 2))) (.add (.mul (.int 6) (.mul (.var 4) (.pow (.var 2) 3))) (.add (.mul (.int 8) (.mul (.pow (.var 2) 5) (.pow (.var 4) 3))) (.add (.mul (.int 12) (.mul (.pow (.var 2) 4) (.pow (.var 4) 2))) (.add (.mul (.int (-16)) (.mul (.var 3) (.mul (.pow (.var 2) 2) (.pow (.var 4) 2)))) (.add (.mul (.int (-16)) (.mul (.var 3) (.mul (.pow (.var 2) 3) (.pow (.var 4) 3)))) (.add (.mul (.int (-8)) (.mul (.var 1) (.mul (.pow (.var 3) 3) (.pow (.var 4) 3)))) (.add (.mul (.int (-4)) (.mul (.var 1) (.mul (.var 4) (.pow (.var 3) 2)))) (.add (.mul (.int (-4)) (.mul (.var 2) (.mul (.var 3) (.var 4)))) (.add (.mul (.int 2) (.mul (.var 1) (.mul (.var 2) (.var 3)))) (.add (.mul (.int 4) (.mul (.pow (.var 0) 2) (.mul (.pow (.var 3) 5) (.pow (.var 4) 2)))) (.add (.mul (.int 4) (.mul (.pow (.var 1) 2) (.mul (.pow (.var 3) 3) (.pow (.var 4) 2)))) (.add (.mul (.int 8) (.mul (.var 2) (.mul (.pow (.var 3) 2) (.pow (.var 4) 3)))) (.add (.mul (.int 16) (.mul (.var 0) (.mul (.pow (.var 3) 4) (.pow (.var 4) 3)))) (.add (.mul (.int (-8)) (.mul (.var 0) (.mul (.pow (.var 2) 2) (.mul (.pow (.var 3) 3) (.pow (.var 4) 3))))) (.add (.mul (.int (-8)) (.mul (.var 0) (.mul (.pow (.var 2) 3) (.mul (.pow (.var 3) 2) (.pow (.var 4) 2))))) (.add (.mul (.int (-8)) (.mul (.var 0) (.mul (.pow (.var 2) 4) (.mul (.pow (.var 3) 2) (.pow (.var 4) 3))))) (.add (.mul (.int (-8)) (.mul (.var 1) (.mul (.var 2) (.mul (.pow (.var 3) 2) (.pow (.var 4) 2))))) (.add (.mul (.int (-4)) (.mul (.var 0) (.mul (.var 1) (.mul (.pow (.var 3) 4) (.pow (.var 4) 2))))) (.add (.mul (.int (-4)) (.mul (.var 0) (.mul (.var 2) (.mul (.pow (.var 3) 3) (.pow (.var 4) 2))))) (.add (.mul (.int (-2)) (.mul (.var 0) (.mul (.var 4) (.mul (.pow (.var 2) 2) (.pow (.var 3) 2))))) (.add (.mul (.int 4) (.mul (.var 2) (.mul (.var 4) (.mul (.pow (.var 1) 2) (.pow (.var 3) 2))))) (.add (.mul (.int 4) (.mul (.pow (.var 1) 2) (.mul (.pow (.var 2) 2) (.mul (.pow (.var 3) 2) (.pow (.var 4) 2))))) (.add (.mul (.int 8) (.mul (.var 1) (.mul (.var 3) (.mul (.pow (.var 2) 4) (.pow (.var 4) 3))))) (.add (.mul (.int 8) (.mul (.var 2) (.mul (.pow (.var 0) 2) (.mul (.pow (.var 3) 5) (.pow (.var 4) 3))))) (.add (.mul (.int 8) (.mul (.var 2) (.mul (.pow (.var 1) 2) (.mul (.pow (.var 3) 3) (.pow (.var 4) 3))))) (.add (.mul (.int 10) (.mul (.var 1) (.mul (.var 3) (.mul (.var 4) (.pow (.var 2) 2))))) (.add (.mul (.int 16) (.mul (.var 1) (.mul (.var 3) (.mul (.pow (.var 2) 3) (.pow (.var 4) 2))))) (.add (.mul (.int (-16)) (.mul (.var 0) (.mul (.var 1) (.mul (.var 2) (.mul (.pow (.var 3) 4) (.pow (.var 4) 3)))))) (.add (.mul (.int (-4)) (.mul (.var 0) (.mul (.var 1) (.mul (.pow (.var 2) 2) (.mul (.pow (.var 3) 3) (.pow (.var 4) 2)))))) (.mul (.int (-2)) (.mul (.var 0) (.mul (.var 1) (.mul (.var 2) (.mul (.var 4) (.pow (.var 3) 3))))))))))))))))))))))))))))))))))))))))))
theorem dataN9b_2_0_binding : litN9bExpr 2 0=dataN9b_2_0 := rfl

def dataN9b_2_1 : RingExpr := (.mul (.var 7) (.mul (.var 9) (.mul (.pow (.var 10) 2) (.mul (.pow (.var 8) 3) (.add (.mul (.var 1) (.var 2)) (.add (.mul (.var 3) (.pow (.var 1) 2)) (.add (.mul (.int (-2)) (.mul (.var 1) (.mul (.var 3) (.var 4)))) (.add (.mul (.int 4) (.mul (.var 1) (.mul (.var 4) (.pow (.var 2) 2)))) (.add (.mul (.int 4) (.mul (.var 1) (.mul (.pow (.var 2) 3) (.pow (.var 4) 2)))) (.add (.mul (.int 4) (.mul (.pow (.var 0) 2) (.mul (.pow (.var 3) 4) (.pow (.var 4) 2)))) (.add (.mul (.int 4) (.mul (.pow (.var 1) 2) (.mul (.pow (.var 3) 2) (.pow (.var 4) 2)))) (.add (.mul (.int (-8)) (.mul (.var 0) (.mul (.var 1) (.mul (.pow (.var 3) 3) (.pow (.var 4) 2))))) (.add (.mul (.int (-8)) (.mul (.var 0) (.mul (.var 3) (.mul (.pow (.var 2) 3) (.pow (.var 4) 2))))) (.add (.mul (.int (-4)) (.mul (.var 0) (.mul (.var 3) (.mul (.var 4) (.pow (.var 2) 2))))) (.add (.mul (.int (-4)) (.mul (.var 1) (.mul (.var 2) (.mul (.var 3) (.pow (.var 4) 2))))) (.add (.mul (.int 2) (.mul (.var 2) (.mul (.var 3) (.mul (.var 4) (.pow (.var 1) 2))))) (.mul (.int 8) (.mul (.var 0) (.mul (.var 2) (.mul (.pow (.var 3) 2) (.pow (.var 4) 2)))))))))))))))))))))
theorem dataN9b_2_1_binding : litN9bExpr 2 1=dataN9b_2_1 := rfl

def dataN9b_2_2 : RingExpr := (.mul (.var 7) (.mul (.var 9) (.mul (.pow (.var 10) 2) (.mul (.pow (.var 8) 3) (.add (.mul (.int (-1)) (.var 2)) (.add (.mul (.int (-1)) (.mul (.var 1) (.var 3))) (.add (.mul (.int (-4)) (.mul (.var 4) (.pow (.var 2) 2))) (.add (.mul (.int (-4)) (.mul (.pow (.var 2) 3) (.pow (.var 4) 2))) (.add (.mul (.int 2) (.mul (.var 3) (.var 4))) (.add (.mul (.int (-4)) (.mul (.var 1) (.mul (.pow (.var 3) 2) (.pow (.var 4) 2)))) (.add (.mul (.int 4) (.mul (.var 2) (.mul (.var 3) (.pow (.var 4) 2)))) (.add (.mul (.int 8) (.mul (.var 0) (.mul (.pow (.var 3) 3) (.pow (.var 4) 2)))) (.add (.mul (.int (-4)) (.mul (.var 0) (.mul (.pow (.var 2) 2) (.mul (.pow (.var 3) 2) (.pow (.var 4) 2))))) (.add (.mul (.int (-2)) (.mul (.var 0) (.mul (.var 2) (.mul (.var 4) (.pow (.var 3) 2))))) (.add (.mul (.int (-2)) (.mul (.var 1) (.mul (.var 2) (.mul (.var 3) (.var 4))))) (.mul (.int 2) (.mul (.var 0) (.mul (.var 1) (.mul (.var 4) (.pow (.var 3) 3))))))))))))))))))))
theorem dataN9b_2_2_binding : litN9bExpr 2 2=dataN9b_2_2 := rfl

def dataN9b_2_6 : RingExpr := (.mul (.var 9) (.mul (.pow (.var 10) 2) (.mul (.pow (.var 8) 3) (.add (.mul (.int (-1)) (.pow (.var 2) 2)) (.add (.mul (.pow (.var 1) 2) (.pow (.var 3) 2)) (.add (.mul (.int (-4)) (.mul (.var 4) (.pow (.var 2) 3))) (.add (.mul (.int (-4)) (.mul (.pow (.var 2) 4) (.pow (.var 4) 2))) (.add (.mul (.int 2) (.mul (.var 0) (.mul (.var 4) (.pow (.var 3) 3)))) (.add (.mul (.int 2) (.mul (.var 2) (.mul (.var 3) (.var 4)))) (.add (.mul (.int 4) (.mul (.var 3) (.mul (.pow (.var 2) 2) (.pow (.var 4) 2)))) (.add (.mul (.int (-4)) (.mul (.var 0) (.mul (.var 2) (.mul (.pow (.var 3) 3) (.pow (.var 4) 2))))) (.add (.mul (.int (-4)) (.mul (.var 1) (.mul (.var 3) (.mul (.pow (.var 2) 3) (.pow (.var 4) 2))))) (.add (.mul (.int (-2)) (.mul (.var 1) (.mul (.var 3) (.mul (.var 4) (.pow (.var 2) 2))))) (.add (.mul (.int 2) (.mul (.var 0) (.mul (.var 4) (.mul (.pow (.var 2) 2) (.pow (.var 3) 2))))) (.add (.mul (.int 2) (.mul (.var 2) (.mul (.var 4) (.mul (.pow (.var 1) 2) (.pow (.var 3) 2))))) (.add (.mul (.int 4) (.mul (.var 0) (.mul (.pow (.var 2) 3) (.mul (.pow (.var 3) 2) (.pow (.var 4) 2))))) (.add (.mul (.int 4) (.mul (.var 1) (.mul (.var 2) (.mul (.pow (.var 3) 2) (.pow (.var 4) 2))))) (.mul (.int (-2)) (.mul (.var 0) (.mul (.var 1) (.mul (.var 2) (.mul (.var 4) (.pow (.var 3) 3)))))))))))))))))))))))
theorem dataN9b_2_6_binding : litN9bExpr 2 6=dataN9b_2_6 := rfl

def dataN9b_2_7 : RingExpr := (.mul (.var 9) (.mul (.pow (.var 10) 2) (.mul (.pow (.var 8) 2) (.add (.var 2) (.add (.mul (.var 1) (.var 3)) (.add (.mul (.int (-4)) (.mul (.pow (.var 2) 3) (.pow (.var 4) 2))) (.add (.mul (.int (-2)) (.mul (.var 3) (.var 4))) (.add (.mul (.int (-4)) (.mul (.var 0) (.mul (.pow (.var 3) 3) (.pow (.var 4) 2)))) (.add (.mul (.int 2) (.mul (.var 4) (.mul (.pow (.var 1) 2) (.pow (.var 3) 2)))) (.add (.mul (.int 4) (.mul (.var 1) (.mul (.pow (.var 3) 2) (.pow (.var 4) 2)))) (.add (.mul (.int 4) (.mul (.var 2) (.mul (.var 3) (.pow (.var 4) 2)))) (.add (.mul (.int (-4)) (.mul (.var 1) (.mul (.var 3) (.mul (.pow (.var 2) 2) (.pow (.var 4) 2))))) (.add (.mul (.int (-2)) (.mul (.var 0) (.mul (.var 1) (.mul (.var 4) (.pow (.var 3) 3))))) (.add (.mul (.int 2) (.mul (.var 0) (.mul (.var 2) (.mul (.var 4) (.pow (.var 3) 2))))) (.mul (.int 4) (.mul (.var 0) (.mul (.pow (.var 2) 2) (.mul (.pow (.var 3) 2) (.pow (.var 4) 2)))))))))))))))))))
theorem dataN9b_2_7_binding : litN9bExpr 2 7=dataN9b_2_7 := rfl

def dataN9b_2_8 : RingExpr := (.mul (.var 7) (.mul (.pow (.var 10) 3) (.mul (.pow (.var 8) 5) (.mul (.pow (.var 9) 2) (.add (.mul (.int (-1)) (.mul (.var 11) (.pow (.var 2) 2))) (.add (.mul (.int (-1)) (.mul (.var 11) (.mul (.pow (.var 1) 2) (.pow (.var 3) 2)))) (.add (.mul (.int (-12)) (.mul (.var 11) (.mul (.pow (.var 2) 4) (.pow (.var 4) 2)))) (.add (.mul (.int (-8)) (.mul (.var 11) (.mul (.pow (.var 2) 5) (.pow (.var 4) 3)))) (.add (.mul (.int (-6)) (.mul (.var 11) (.mul (.var 4) (.pow (.var 2) 3)))) (.add (.mul (.int (-4)) (.mul (.var 11) (.mul (.pow (.var 3) 2) (.pow (.var 4) 2)))) (.add (.mul (.int (-4)) (.mul (.var 15) (.mul (.pow (.var 3) 3) (.pow (.var 4) 2)))) (.add (.mul (.int (-16)) (.mul (.var 11) (.mul (.var 0) (.mul (.pow (.var 3) 4) (.pow (.var 4) 3))))) (.add (.mul (.int (-16)) (.mul (.var 15) (.mul (.var 0) (.mul (.pow (.var 3) 5) (.pow (.var 4) 3))))) (.add (.mul (.int (-8)) (.mul (.var 11) (.mul (.var 2) (.mul (.pow (.var 3) 2) (.pow (.var 4) 3))))) (.add (.mul (.int (-8)) (.mul (.var 12) (.mul (.pow (.var 0) 2) (.mul (.pow (.var 3) 6) (.pow (.var 4) 3))))) (.add (.mul (.int (-8)) (.mul (.var 12) (.mul (.pow (.var 1) 2) (.mul (.pow (.var 3) 4) (.pow (.var 4) 3))))) (.add (.mul (.int (-8)) (.mul (.var 14) (.mul (.var 0) (.mul (.pow (.var 3) 4) (.pow (.var 4) 2))))) (.add (.mul (.int (-8)) (.mul (.var 15) (.mul (.var 2) (.mul (.pow (.var 3) 3) (.pow (.var 4) 3))))) (.add (.mul (.int (-8)) (.mul (.var 16) (.mul (.pow (.var 0) 2) (.mul (.pow (.var 3) 6) (.pow (.var 4) 2))))) (.add (.mul (.int (-4)) (.mul (.var 11) (.mul (.pow (.var 1) 2) (.mul (.pow (.var 3) 3) (.pow (.var 4) 2))))) (.add (.mul (.int (-2)) (.mul (.var 11) (.mul (.var 1) (.mul (.var 2) (.var 3))))) (.add (.mul (.int (-2)) (.mul (.var 12) (.mul (.var 4) (.mul (.pow (.var 1) 2) (.pow (.var 3) 3))))) (.add (.mul (.int 2) (.mul (.var 15) (.mul (.var 1) (.mul (.var 4) (.pow (.var 3) 3))))) (.add (.mul (.int 2) (.mul (.var 15) (.mul (.var 2) (.mul (.var 4) (.pow (.var 3) 2))))) (.add (.mul (.int 4) (.mul (.var 11) (.mul (.var 1) (.mul (.var 4) (.pow (.var 3) 2))))) (.add (.mul (.int 4) (.mul (.var 11) (.mul (.var 2) (.mul (.var 3) (.var 4))))) (.add (.mul (.int 4) (.mul (.var 11) (.mul (.pow (.var 0) 2) (.mul (.pow (.var 3) 5) (.pow (.var 4) 2))))) (.add (.mul (.int 4) (.mul (.var 12) (.mul (.var 1) (.mul (.pow (.var 3) 3) (.pow (.var 4) 2))))) (.add (.mul (.int 8) (.mul (.var 11) (.mul (.var 1) (.mul (.pow (.var 3) 3) (.pow (.var 4) 3))))) (.add (.mul (.int 8) (.mul (.var 15) (.mul (.var 1) (.mul (.pow (.var 3) 4) (.pow (.var 4) 3))))) (.add (.mul (.int 8) (.mul (.var 15) (.mul (.pow (.var 0) 2) (.mul (.pow (.var 3) 6) (.pow (.var 4) 2))))) (.add (.mul (.int 8) (.mul (.var 15) (.mul (.pow (.var 2) 2) (.mul (.pow (.var 3) 2) (.pow (.var 4) 2))))) (.add (.mul (.int 8) (.mul (.var 15) (.mul (.pow (.var 2) 3) (.mul (.pow (.var 3) 2) (.pow (.var 4) 3))))) (.add (.mul (.int 16) (.mul (.var 11) (.mul (.var 3) (.mul (.pow (.var 2) 2) (.pow (.var 4) 2))))) (.add (.mul (.int 16) (.mul (.var 11) (.mul (.var 3) (.mul (.pow (.var 2) 3) (.pow (.var 4) 3))))) (.add (.mul (.int (-16)) (.mul (.var 11) (.mul (.var 1) (.mul (.var 3) (.mul (.pow (.var 2) 3) (.pow (.var 4) 2)))))) (.add (.mul (.int (-16)) (.mul (.var 12) (.mul (.var 0) (.mul (.var 2) (.mul (.pow (.var 3) 4) (.pow (.var 4) 3)))))) (.add (.mul (.int (-10)) (.mul (.var 11) (.mul (.var 1) (.mul (.var 3) (.mul (.var 4) (.pow (.var 2) 2)))))) (.add (.mul (.int (-8)) (.mul (.var 11) (.mul (.var 1) (.mul (.var 3) (.mul (.pow (.var 2) 4) (.pow (.var 4) 3)))))) (.add (.mul (.int (-8)) (.mul (.var 11) (.mul (.var 2) (.mul (.pow (.var 0) 2) (.mul (.pow (.var 3) 5) (.pow (.var 4) 3)))))) (.add (.mul (.int (-8)) (.mul (.var 11) (.mul (.var 2) (.mul (.pow (.var 1) 2) (.mul (.pow (.var 3) 3) (.pow (.var 4) 3)))))) (.add (.mul (.int (-8)) (.mul (.var 12) (.mul (.var 1) (.mul (.pow (.var 2) 2) (.mul (.pow (.var 3) 2) (.pow (.var 4) 2)))))) (.add (.mul (.int (-8)) (.mul (.var 12) (.mul (.var 1) (.mul (.pow (.var 2) 3) (.mul (.pow (.var 3) 2) (.pow (.var 4) 3)))))) (.add (.mul (.int (-8)) (.mul (.var 14) (.mul (.var 2) (.mul (.pow (.var 0) 2) (.mul (.pow (.var 3) 5) (.pow (.var 4) 2)))))) (.add (.mul (.int (-4)) (.mul (.var 11) (.mul (.var 2) (.mul (.var 4) (.mul (.pow (.var 1) 2) (.pow (.var 3) 2)))))) (.add (.mul (.int (-4)) (.mul (.var 11) (.mul (.pow (.var 1) 2) (.mul (.pow (.var 2) 2) (.mul (.pow (.var 3) 2) (.pow (.var 4) 2)))))) (.add (.mul (.int (-4)) (.mul (.var 12) (.mul (.var 2) (.mul (.pow (.var 1) 2) (.mul (.pow (.var 3) 3) (.pow (.var 4) 2)))))) (.add (.mul (.int (-4)) (.mul (.var 15) (.mul (.var 0) (.mul (.var 1) (.mul (.pow (.var 3) 5) (.pow (.var 4) 2)))))) (.add (.mul (.int (-2)) (.mul (.var 12) (.mul (.var 1) (.mul (.var 2) (.mul (.var 4) (.pow (.var 3) 2)))))) (.add (.mul (.int 2) (.mul (.var 11) (.mul (.var 0) (.mul (.var 4) (.mul (.pow (.var 2) 2) (.pow (.var 3) 2)))))) (.add (.mul (.int 4) (.mul (.var 11) (.mul (.var 0) (.mul (.var 1) (.mul (.pow (.var 3) 4) (.pow (.var 4) 2)))))) (.add (.mul (.int 4) (.mul (.var 11) (.mul (.var 0) (.mul (.var 2) (.mul (.pow (.var 3) 3) (.pow (.var 4) 2)))))) (.add (.mul (.int 4) (.mul (.var 14) (.mul (.var 0) (.mul (.var 1) (.mul (.var 4) (.pow (.var 3) 4)))))) (.add (.mul (.int 4) (.mul (.var 14) (.mul (.var 0) (.mul (.var 2) (.mul (.var 4) (.pow (.var 3) 3)))))) (.add (.mul (.int 4) (.mul (.var 15) (.mul (.var 0) (.mul (.var 2) (.mul (.pow (.var 3) 4) (.pow (.var 4) 2)))))) (.add (.mul (.int 4) (.mul (.var 15) (.mul (.var 1) (.mul (.var 2) (.mul (.pow (.var 3) 3) (.pow (.var 4) 2)))))) (.add (.mul (.int 8) (.mul (.var 11) (.mul (.var 0) (.mul (.pow (.var 2) 2) (.mul (.pow (.var 3) 3) (.pow (.var 4) 3)))))) (.add (.mul (.int 8) (.mul (.var 11) (.mul (.var 0) (.mul (.pow (.var 2) 3) (.mul (.pow (.var 3) 2) (.pow (.var 4) 2)))))) (.add (.mul (.int 8) (.mul (.var 11) (.mul (.var 0) (.mul (.pow (.var 2) 4) (.mul (.pow (.var 3) 2) (.pow (.var 4) 3)))))) (.add (.mul (.int 8) (.mul (.var 11) (.mul (.var 1) (.mul (.var 2) (.mul (.pow (.var 3) 2) (.pow (.var 4) 2)))))) (.add (.mul (.int 8) (.mul (.var 12) (.mul (.var 0) (.mul (.pow (.var 2) 2) (.mul (.pow (.var 3) 3) (.pow (.var 4) 2)))))) (.add (.mul (.int 8) (.mul (.var 12) (.mul (.var 1) (.mul (.var 2) (.mul (.pow (.var 3) 3) (.pow (.var 4) 3)))))) (.add (.mul (.int 8) (.mul (.var 12) (.mul (.var 2) (.mul (.pow (.var 0) 2) (.mul (.pow (.var 3) 5) (.pow (.var 4) 2)))))) (.add (.mul (.int 8) (.mul (.var 14) (.mul (.var 0) (.mul (.pow (.var 2) 2) (.mul (.pow (.var 3) 3) (.pow (.var 4) 2)))))) (.add (.mul (.int 8) (.mul (.var 15) (.mul (.var 0) (.mul (.pow (.var 2) 2) (.mul (.pow (.var 3) 4) (.pow (.var 4) 3)))))) (.add (.mul (.int 8) (.mul (.var 16) (.mul (.var 0) (.mul (.var 1) (.mul (.pow (.var 3) 5) (.pow (.var 4) 2)))))) (.add (.mul (.int 16) (.mul (.var 12) (.mul (.var 0) (.mul (.var 1) (.mul (.pow (.var 3) 5) (.pow (.var 4) 3)))))) (.add (.mul (.int 16) (.mul (.var 12) (.mul (.var 0) (.mul (.pow (.var 2) 3) (.mul (.pow (.var 3) 3) (.pow (.var 4) 3)))))) (.add (.mul (.int 2) (.mul (.var 11) (.mul (.var 0) (.mul (.var 1) (.mul (.var 2) (.mul (.var 4) (.pow (.var 3) 3))))))) (.add (.mul (.int 4) (.mul (.var 11) (.mul (.var 0) (.mul (.var 1) (.mul (.pow (.var 2) 2) (.mul (.pow (.var 3) 3) (.pow (.var 4) 2))))))) (.add (.mul (.int 8) (.mul (.var 14) (.mul (.var 0) (.mul (.var 1) (.mul (.var 2) (.mul (.pow (.var 3) 4) (.pow (.var 4) 2))))))) (.mul (.int 16) (.mul (.var 11) (.mul (.var 0) (.mul (.var 1) (.mul (.var 2) (.mul (.pow (.var 3) 4) (.pow (.var 4) 3))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
theorem dataN9b_2_8_binding : litN9bExpr 2 8=dataN9b_2_8 := rfl

def dataN9b_3_8 : RingExpr := (.var 12)
theorem dataN9b_3_8_binding : litN9bExpr 3 8=dataN9b_3_8 := rfl

def dataN9b_4_8 : RingExpr := (.var 15)
theorem dataN9b_4_8_binding : litN9bExpr 4 8=dataN9b_4_8 := rfl

def dataN9b_5_8 : RingExpr := (.mul (.var 10) (.mul (.var 9) (.mul (.pow (.var 8) 2) (.add (.mul (.var 12) (.var 2)) (.add (.mul (.var 12) (.mul (.var 1) (.var 3))) (.add (.mul (.int (-2)) (.mul (.var 12) (.mul (.var 3) (.var 4)))) (.add (.mul (.int 2) (.mul (.var 12) (.mul (.var 4) (.pow (.var 2) 2)))) (.add (.mul (.int 2) (.mul (.var 11) (.mul (.var 0) (.mul (.var 4) (.pow (.var 3) 2))))) (.add (.mul (.int 2) (.mul (.var 15) (.mul (.var 1) (.mul (.var 4) (.pow (.var 3) 2))))) (.mul (.int 2) (.mul (.var 12) (.mul (.var 1) (.mul (.var 2) (.mul (.var 3) (.var 4)))))))))))))))
theorem dataN9b_5_8_binding : litN9bExpr 5 8=dataN9b_5_8 := rfl

def dataN9b_6_8 : RingExpr := (.add (.var 12) (.mul (.int (-1)) (.var 14)))
theorem dataN9b_6_8_binding : litN9bExpr 6 8=dataN9b_6_8 := rfl

def dataN9b_7_8 : RingExpr := (.add (.var 15) (.mul (.int (-1)) (.var 16)))
theorem dataN9b_7_8_binding : litN9bExpr 7 8=dataN9b_7_8 := rfl

def dataN9t_0_1 : RingExpr := (.int 1)
theorem dataN9t_0_1_binding : litN9tExpr 0 1=dataN9t_0_1 := rfl

def dataN9t_0_6 : RingExpr := (.mul (.var 10) (.mul (.var 8) (.add (.mul (.int (-1)) (.var 2)) (.add (.mul (.int (-1)) (.mul (.var 1) (.var 3))) (.add (.mul (.int (-2)) (.mul (.var 4) (.pow (.var 2) 2))) (.add (.mul (.int (-2)) (.mul (.var 1) (.mul (.var 2) (.mul (.var 3) (.var 4))))) (.mul (.int 2) (.mul (.var 0) (.mul (.var 2) (.mul (.var 4) (.pow (.var 3) 2)))))))))))
theorem dataN9t_0_6_binding : litN9tExpr 0 6=dataN9t_0_6 := rfl

def dataN9t_0_7 : RingExpr := (.add (.mul (.int (1)) (.pow (.var 10) 1)) (.add (.mul (.int (-1)) (.mul (.var 2) (.var 4))) (.add (.mul (.var 0) (.mul (.var 4) (.pow (.var 3) 2))) (.mul (.int (-1)) (.mul (.var 1) (.mul (.var 3) (.var 4)))))))
theorem dataN9t_0_7_binding : litN9tExpr 0 7=dataN9t_0_7 := rfl

def dataN9t_1_2 : RingExpr := (.int 1)
theorem dataN9t_1_2_binding : litN9tExpr 1 2=dataN9t_1_2 := rfl

def dataN9t_1_6 : RingExpr := (.mul (.var 10) (.mul (.var 9) (.mul (.pow (.var 8) 2) (.add (.var 2) (.add (.mul (.var 1) (.var 3)) (.add (.mul (.int (-1)) (.mul (.var 3) (.var 4))) (.add (.mul (.int 2) (.mul (.pow (.var 2) 3) (.pow (.var 4) 2))) (.add (.mul (.int 3) (.mul (.var 4) (.pow (.var 2) 2))) (.add (.mul (.int (-2)) (.mul (.var 0) (.mul (.var 2) (.mul (.var 4) (.pow (.var 3) 2))))) (.add (.mul (.int (-2)) (.mul (.var 0) (.mul (.pow (.var 2) 2) (.mul (.pow (.var 3) 2) (.pow (.var 4) 2))))) (.add (.mul (.int 2) (.mul (.var 1) (.mul (.var 3) (.mul (.pow (.var 2) 2) (.pow (.var 4) 2))))) (.mul (.int 3) (.mul (.var 1) (.mul (.var 2) (.mul (.var 3) (.var 4))))))))))))))))
theorem dataN9t_1_6_binding : litN9tExpr 1 6=dataN9t_1_6 := rfl

def dataN9t_1_7 : RingExpr := (.mul (.var 10) (.mul (.var 8) (.add (.var 2) (.add (.mul (.int (-2)) (.mul (.var 0) (.pow (.var 3) 2))) (.add (.mul (.int 2) (.mul (.var 1) (.var 3))) (.add (.mul (.int 2) (.mul (.var 4) (.pow (.var 2) 2))) (.add (.mul (.int (-2)) (.mul (.var 0) (.mul (.var 2) (.mul (.var 4) (.pow (.var 3) 2))))) (.mul (.int 2) (.mul (.var 1) (.mul (.var 2) (.mul (.var 3) (.var 4))))))))))))
theorem dataN9t_1_7_binding : litN9tExpr 1 7=dataN9t_1_7 := rfl

def dataN9t_2_0 : RingExpr := (.var 0)
theorem dataN9t_2_0_binding : litN9tExpr 2 0=dataN9t_2_0 := rfl

def dataN9t_2_1 : RingExpr := (.mul (.var 10) (.mul (.var 9) (.mul (.pow (.var 8) 2) (.add (.var 2) (.add (.mul (.var 1) (.var 3)) (.add (.mul (.int (-2)) (.mul (.var 3) (.var 4))) (.add (.mul (.int 2) (.mul (.var 4) (.pow (.var 2) 2))) (.mul (.int 2) (.mul (.var 1) (.mul (.var 2) (.mul (.var 3) (.var 4))))))))))))
theorem dataN9t_2_1_binding : litN9tExpr 2 1=dataN9t_2_1 := rfl

def dataN9t_2_2 : RingExpr := (.var 1)
theorem dataN9t_2_2_binding : litN9tExpr 2 2=dataN9t_2_2 := rfl

def dataN9t_2_6 : RingExpr := (.mul (.var 9) (.mul (.pow (.var 10) 2) (.mul (.pow (.var 8) 3) (.add (.mul (.int (-1)) (.pow (.var 2) 2)) (.add (.mul (.pow (.var 1) 2) (.pow (.var 3) 2)) (.add (.mul (.int (-4)) (.mul (.var 4) (.pow (.var 2) 3))) (.add (.mul (.int (-4)) (.mul (.pow (.var 2) 4) (.pow (.var 4) 2))) (.add (.mul (.int 2) (.mul (.var 0) (.mul (.var 4) (.pow (.var 3) 3)))) (.add (.mul (.int 2) (.mul (.var 2) (.mul (.var 3) (.var 4)))) (.add (.mul (.int 4) (.mul (.var 3) (.mul (.pow (.var 2) 2) (.pow (.var 4) 2)))) (.add (.mul (.int (-4)) (.mul (.var 0) (.mul (.var 2) (.mul (.pow (.var 3) 3) (.pow (.var 4) 2))))) (.add (.mul (.int (-4)) (.mul (.var 1) (.mul (.var 3) (.mul (.pow (.var 2) 3) (.pow (.var 4) 2))))) (.add (.mul (.int (-2)) (.mul (.var 1) (.mul (.var 3) (.mul (.var 4) (.pow (.var 2) 2))))) (.add (.mul (.int 2) (.mul (.var 0) (.mul (.var 4) (.mul (.pow (.var 2) 2) (.pow (.var 3) 2))))) (.add (.mul (.int 2) (.mul (.var 2) (.mul (.var 4) (.mul (.pow (.var 1) 2) (.pow (.var 3) 2))))) (.add (.mul (.int 4) (.mul (.var 0) (.mul (.pow (.var 2) 3) (.mul (.pow (.var 3) 2) (.pow (.var 4) 2))))) (.add (.mul (.int 4) (.mul (.var 1) (.mul (.var 2) (.mul (.pow (.var 3) 2) (.pow (.var 4) 2))))) (.mul (.int (-2)) (.mul (.var 0) (.mul (.var 1) (.mul (.var 2) (.mul (.var 4) (.pow (.var 3) 3)))))))))))))))))))))))
theorem dataN9t_2_6_binding : litN9tExpr 2 6=dataN9t_2_6 := rfl

def dataN9t_2_7 : RingExpr := (.mul (.var 9) (.mul (.pow (.var 10) 2) (.mul (.pow (.var 8) 2) (.add (.var 2) (.add (.mul (.var 1) (.var 3)) (.add (.mul (.int (-4)) (.mul (.pow (.var 2) 3) (.pow (.var 4) 2))) (.add (.mul (.int (-2)) (.mul (.var 3) (.var 4))) (.add (.mul (.int (-4)) (.mul (.var 0) (.mul (.pow (.var 3) 3) (.pow (.var 4) 2)))) (.add (.mul (.int 2) (.mul (.var 4) (.mul (.pow (.var 1) 2) (.pow (.var 3) 2)))) (.add (.mul (.int 4) (.mul (.var 1) (.mul (.pow (.var 3) 2) (.pow (.var 4) 2)))) (.add (.mul (.int 4) (.mul (.var 2) (.mul (.var 3) (.pow (.var 4) 2)))) (.add (.mul (.int (-4)) (.mul (.var 1) (.mul (.var 3) (.mul (.pow (.var 2) 2) (.pow (.var 4) 2))))) (.add (.mul (.int (-2)) (.mul (.var 0) (.mul (.var 1) (.mul (.var 4) (.pow (.var 3) 3))))) (.add (.mul (.int 2) (.mul (.var 0) (.mul (.var 2) (.mul (.var 4) (.pow (.var 3) 2))))) (.mul (.int 4) (.mul (.var 0) (.mul (.pow (.var 2) 2) (.mul (.pow (.var 3) 2) (.pow (.var 4) 2)))))))))))))))))))
theorem dataN9t_2_7_binding : litN9tExpr 2 7=dataN9t_2_7 := rfl

def dataN9t_3_3 : RingExpr := (.mul (.var 7) (.mul (.var 9) (.mul (.pow (.var 10) 2) (.mul (.pow (.var 8) 3) (.add (.var 2) (.add (.mul (.var 1) (.var 3)) (.add (.mul (.int (-2)) (.mul (.var 3) (.var 4))) (.add (.mul (.int 4) (.mul (.var 4) (.pow (.var 2) 2))) (.add (.mul (.int 4) (.mul (.pow (.var 2) 3) (.pow (.var 4) 2))) (.add (.mul (.int (-4)) (.mul (.var 0) (.mul (.pow (.var 3) 3) (.pow (.var 4) 2)))) (.add (.mul (.int (-4)) (.mul (.var 2) (.mul (.var 3) (.pow (.var 4) 2)))) (.add (.mul (.int (-4)) (.mul (.var 0) (.mul (.pow (.var 2) 2) (.mul (.pow (.var 3) 2) (.pow (.var 4) 2))))) (.add (.mul (.int (-2)) (.mul (.var 0) (.mul (.var 2) (.mul (.var 4) (.pow (.var 3) 2))))) (.add (.mul (.int 4) (.mul (.var 1) (.mul (.var 2) (.mul (.var 3) (.var 4))))) (.mul (.int 4) (.mul (.var 1) (.mul (.var 3) (.mul (.pow (.var 2) 2) (.pow (.var 4) 2)))))))))))))))))))
theorem dataN9t_3_3_binding : litN9tExpr 3 3=dataN9t_3_3 := rfl

def dataN9t_3_4 : RingExpr := (.mul (.var 7) (.mul (.var 10) (.mul (.var 8) (.add (.var 1) (.add (.mul (.int 2) (.mul (.var 1) (.mul (.var 2) (.var 4)))) (.mul (.int (-4)) (.mul (.var 0) (.mul (.var 2) (.mul (.var 3) (.var 4))))))))))
theorem dataN9t_3_4_binding : litN9tExpr 3 4=dataN9t_3_4 := rfl

def dataN9t_3_5 : RingExpr := (.mul (.var 7) (.mul (.var 10) (.mul (.var 8) (.add (.int (-1)) (.add (.mul (.int (-2)) (.mul (.var 2) (.var 4))) (.mul (.int (-2)) (.mul (.var 0) (.mul (.var 4) (.pow (.var 3) 2)))))))))
theorem dataN9t_3_5_binding : litN9tExpr 3 5=dataN9t_3_5 := rfl

def dataN9t_3_8 : RingExpr := (.mul (.var 7) (.mul (.var 9) (.mul (.pow (.var 10) 2) (.mul (.pow (.var 8) 3) (.add (.mul (.int (-1)) (.mul (.var 11) (.var 2))) (.add (.mul (.int (-1)) (.mul (.var 11) (.mul (.var 1) (.var 3)))) (.add (.mul (.int (-4)) (.mul (.var 11) (.mul (.var 4) (.pow (.var 2) 2)))) (.add (.mul (.int (-4)) (.mul (.var 11) (.mul (.pow (.var 2) 3) (.pow (.var 4) 2)))) (.add (.mul (.int 2) (.mul (.var 11) (.mul (.var 3) (.var 4)))) (.add (.mul (.int 2) (.mul (.var 15) (.mul (.var 4) (.pow (.var 3) 2)))) (.add (.mul (.int (-2)) (.mul (.var 12) (.mul (.var 1) (.mul (.var 4) (.pow (.var 3) 2))))) (.add (.mul (.int 4) (.mul (.var 11) (.mul (.var 0) (.mul (.pow (.var 3) 3) (.pow (.var 4) 2))))) (.add (.mul (.int 4) (.mul (.var 11) (.mul (.var 2) (.mul (.var 3) (.pow (.var 4) 2))))) (.add (.mul (.int 4) (.mul (.var 12) (.mul (.var 0) (.mul (.var 4) (.pow (.var 3) 3))))) (.add (.mul (.int 4) (.mul (.var 15) (.mul (.var 0) (.mul (.pow (.var 3) 4) (.pow (.var 4) 2))))) (.add (.mul (.int 4) (.mul (.var 15) (.mul (.var 2) (.mul (.pow (.var 3) 2) (.pow (.var 4) 2))))) (.add (.mul (.int (-4)) (.mul (.var 11) (.mul (.var 1) (.mul (.var 2) (.mul (.var 3) (.var 4)))))) (.add (.mul (.int (-4)) (.mul (.var 11) (.mul (.var 1) (.mul (.var 3) (.mul (.pow (.var 2) 2) (.pow (.var 4) 2)))))) (.add (.mul (.int (-4)) (.mul (.var 12) (.mul (.var 1) (.mul (.var 2) (.mul (.pow (.var 3) 2) (.pow (.var 4) 2)))))) (.add (.mul (.int 2) (.mul (.var 11) (.mul (.var 0) (.mul (.var 2) (.mul (.var 4) (.pow (.var 3) 2)))))) (.add (.mul (.int 4) (.mul (.var 11) (.mul (.var 0) (.mul (.pow (.var 2) 2) (.mul (.pow (.var 3) 2) (.pow (.var 4) 2)))))) (.mul (.int 8) (.mul (.var 12) (.mul (.var 0) (.mul (.var 2) (.mul (.pow (.var 3) 3) (.pow (.var 4) 2)))))))))))))))))))))))))))
theorem dataN9t_3_8_binding : litN9tExpr 3 8=dataN9t_3_8 := rfl

def dataN9t_4_3 : RingExpr := (.mul (.var 7) (.mul (.var 9) (.mul (.pow (.var 10) 2) (.mul (.pow (.var 8) 4) (.add (.mul (.int (-1)) (.pow (.var 2) 2)) (.add (.mul (.int (-4)) (.mul (.var 4) (.pow (.var 2) 3))) (.add (.mul (.int (-4)) (.mul (.pow (.var 2) 4) (.pow (.var 4) 2))) (.add (.mul (.int (-4)) (.mul (.pow (.var 3) 2) (.pow (.var 4) 2))) (.add (.mul (.int (-1)) (.mul (.var 1) (.mul (.var 2) (.var 3)))) (.add (.mul (.int 2) (.mul (.var 0) (.mul (.var 4) (.pow (.var 3) 3)))) (.add (.mul (.int 2) (.mul (.var 1) (.mul (.var 4) (.pow (.var 3) 2)))) (.add (.mul (.int 4) (.mul (.var 2) (.mul (.var 3) (.var 4)))) (.add (.mul (.int 8) (.mul (.var 3) (.mul (.pow (.var 2) 2) (.pow (.var 4) 2)))) (.add (.mul (.int (-4)) (.mul (.var 1) (.mul (.var 3) (.mul (.var 4) (.pow (.var 2) 2))))) (.add (.mul (.int (-4)) (.mul (.var 1) (.mul (.var 3) (.mul (.pow (.var 2) 3) (.pow (.var 4) 2))))) (.add (.mul (.int 2) (.mul (.var 0) (.mul (.var 4) (.mul (.pow (.var 2) 2) (.pow (.var 3) 2))))) (.add (.mul (.int 4) (.mul (.var 0) (.mul (.pow (.var 2) 3) (.mul (.pow (.var 3) 2) (.pow (.var 4) 2))))) (.mul (.int 4) (.mul (.var 1) (.mul (.var 2) (.mul (.pow (.var 3) 2) (.pow (.var 4) 2))))))))))))))))))))))
theorem dataN9t_4_3_binding : litN9tExpr 4 3=dataN9t_4_3 := rfl

def dataN9t_4_4 : RingExpr := (.mul (.var 7) (.mul (.var 10) (.mul (.pow (.var 8) 2) (.add (.mul (.int (-1)) (.mul (.var 1) (.var 2))) (.add (.mul (.int (-2)) (.mul (.var 0) (.mul (.var 4) (.pow (.var 3) 2)))) (.add (.mul (.int (-2)) (.mul (.var 1) (.mul (.var 4) (.pow (.var 2) 2)))) (.add (.mul (.int 2) (.mul (.var 0) (.mul (.var 2) (.var 3)))) (.add (.mul (.int 2) (.mul (.var 1) (.mul (.var 3) (.var 4)))) (.mul (.int 4) (.mul (.var 0) (.mul (.var 3) (.mul (.var 4) (.pow (.var 2) 2)))))))))))))
theorem dataN9t_4_4_binding : litN9tExpr 4 4=dataN9t_4_4 := rfl

def dataN9t_4_5 : RingExpr := (.mul (.var 7) (.mul (.var 10) (.mul (.pow (.var 8) 2) (.add (.var 2) (.add (.mul (.int (-2)) (.mul (.var 3) (.var 4))) (.add (.mul (.int 2) (.mul (.var 0) (.pow (.var 3) 2))) (.add (.mul (.int 2) (.mul (.var 4) (.pow (.var 2) 2))) (.mul (.int 2) (.mul (.var 0) (.mul (.var 2) (.mul (.var 4) (.pow (.var 3) 2))))))))))))
theorem dataN9t_4_5_binding : litN9tExpr 4 5=dataN9t_4_5 := rfl

def dataN9t_4_8 : RingExpr := (.mul (.var 7) (.mul (.var 9) (.mul (.pow (.var 10) 2) (.mul (.pow (.var 8) 4) (.add (.mul (.var 11) (.pow (.var 2) 2)) (.add (.mul (.int 4) (.mul (.var 11) (.mul (.var 4) (.pow (.var 2) 3)))) (.add (.mul (.int 4) (.mul (.var 11) (.mul (.pow (.var 2) 4) (.pow (.var 4) 2)))) (.add (.mul (.int 4) (.mul (.var 11) (.mul (.pow (.var 3) 2) (.pow (.var 4) 2)))) (.add (.mul (.int 4) (.mul (.var 15) (.mul (.pow (.var 3) 3) (.pow (.var 4) 2)))) (.add (.mul (.var 11) (.mul (.var 1) (.mul (.var 2) (.var 3)))) (.add (.mul (.int (-8)) (.mul (.var 11) (.mul (.var 3) (.mul (.pow (.var 2) 2) (.pow (.var 4) 2))))) (.add (.mul (.int (-4)) (.mul (.var 11) (.mul (.var 2) (.mul (.var 3) (.var 4))))) (.add (.mul (.int (-4)) (.mul (.var 12) (.mul (.var 1) (.mul (.pow (.var 3) 3) (.pow (.var 4) 2))))) (.add (.mul (.int (-4)) (.mul (.var 15) (.mul (.pow (.var 2) 2) (.mul (.pow (.var 3) 2) (.pow (.var 4) 2))))) (.add (.mul (.int (-2)) (.mul (.var 11) (.mul (.var 0) (.mul (.var 4) (.pow (.var 3) 3))))) (.add (.mul (.int (-2)) (.mul (.var 11) (.mul (.var 1) (.mul (.var 4) (.pow (.var 3) 2))))) (.add (.mul (.int (-2)) (.mul (.var 15) (.mul (.var 2) (.mul (.var 4) (.pow (.var 3) 2))))) (.add (.mul (.int 4) (.mul (.var 12) (.mul (.var 0) (.mul (.pow (.var 3) 4) (.pow (.var 4) 2))))) (.add (.mul (.int (-8)) (.mul (.var 12) (.mul (.var 0) (.mul (.pow (.var 2) 2) (.mul (.pow (.var 3) 3) (.pow (.var 4) 2)))))) (.add (.mul (.int (-4)) (.mul (.var 11) (.mul (.var 0) (.mul (.pow (.var 2) 3) (.mul (.pow (.var 3) 2) (.pow (.var 4) 2)))))) (.add (.mul (.int (-4)) (.mul (.var 11) (.mul (.var 1) (.mul (.var 2) (.mul (.pow (.var 3) 2) (.pow (.var 4) 2)))))) (.add (.mul (.int (-4)) (.mul (.var 12) (.mul (.var 0) (.mul (.var 2) (.mul (.var 4) (.pow (.var 3) 3)))))) (.add (.mul (.int (-4)) (.mul (.var 15) (.mul (.var 0) (.mul (.var 2) (.mul (.pow (.var 3) 4) (.pow (.var 4) 2)))))) (.add (.mul (.int (-2)) (.mul (.var 11) (.mul (.var 0) (.mul (.var 4) (.mul (.pow (.var 2) 2) (.pow (.var 3) 2)))))) (.add (.mul (.int 2) (.mul (.var 12) (.mul (.var 1) (.mul (.var 2) (.mul (.var 4) (.pow (.var 3) 2)))))) (.add (.mul (.int 4) (.mul (.var 11) (.mul (.var 1) (.mul (.var 3) (.mul (.var 4) (.pow (.var 2) 2)))))) (.add (.mul (.int 4) (.mul (.var 11) (.mul (.var 1) (.mul (.var 3) (.mul (.pow (.var 2) 3) (.pow (.var 4) 2)))))) (.mul (.int 4) (.mul (.var 12) (.mul (.var 1) (.mul (.pow (.var 2) 2) (.mul (.pow (.var 3) 2) (.pow (.var 4) 2)))))))))))))))))))))))))))))))))
theorem dataN9t_4_8_binding : litN9tExpr 4 8=dataN9t_4_8 := rfl

def dataN9t_5_3 : RingExpr := (.mul (.var 7) (.mul (.pow (.var 10) 3) (.mul (.pow (.var 8) 5) (.mul (.pow (.var 9) 2) (.add (.pow (.var 2) 2) (.add (.mul (.pow (.var 1) 2) (.pow (.var 3) 2)) (.add (.mul (.int 4) (.mul (.pow (.var 3) 2) (.pow (.var 4) 2))) (.add (.mul (.int 6) (.mul (.var 4) (.pow (.var 2) 3))) (.add (.mul (.int 8) (.mul (.pow (.var 2) 5) (.pow (.var 4) 3))) (.add (.mul (.int 12) (.mul (.pow (.var 2) 4) (.pow (.var 4) 2))) (.add (.mul (.int (-16)) (.mul (.var 3) (.mul (.pow (.var 2) 2) (.pow (.var 4) 2)))) (.add (.mul (.int (-16)) (.mul (.var 3) (.mul (.pow (.var 2) 3) (.pow (.var 4) 3)))) (.add (.mul (.int (-8)) (.mul (.var 1) (.mul (.pow (.var 3) 3) (.pow (.var 4) 3)))) (.add (.mul (.int (-4)) (.mul (.var 1) (.mul (.var 4) (.pow (.var 3) 2)))) (.add (.mul (.int (-4)) (.mul (.var 2) (.mul (.var 3) (.var 4)))) (.add (.mul (.int 2) (.mul (.var 1) (.mul (.var 2) (.var 3)))) (.add (.mul (.int 4) (.mul (.pow (.var 0) 2) (.mul (.pow (.var 3) 5) (.pow (.var 4) 2)))) (.add (.mul (.int 4) (.mul (.pow (.var 1) 2) (.mul (.pow (.var 3) 3) (.pow (.var 4) 2)))) (.add (.mul (.int 8) (.mul (.var 2) (.mul (.pow (.var 3) 2) (.pow (.var 4) 3)))) (.add (.mul (.int 16) (.mul (.var 0) (.mul (.pow (.var 3) 4) (.pow (.var 4) 3)))) (.add (.mul (.int (-8)) (.mul (.var 0) (.mul (.pow (.var 2) 2) (.mul (.pow (.var 3) 3) (.pow (.var 4) 3))))) (.add (.mul (.int (-8)) (.mul (.var 0) (.mul (.pow (.var 2) 3) (.mul (.pow (.var 3) 2) (.pow (.var 4) 2))))) (.add (.mul (.int (-8)) (.mul (.var 0) (.mul (.pow (.var 2) 4) (.mul (.pow (.var 3) 2) (.pow (.var 4) 3))))) (.add (.mul (.int (-8)) (.mul (.var 1) (.mul (.var 2) (.mul (.pow (.var 3) 2) (.pow (.var 4) 2))))) (.add (.mul (.int (-4)) (.mul (.var 0) (.mul (.var 1) (.mul (.pow (.var 3) 4) (.pow (.var 4) 2))))) (.add (.mul (.int (-4)) (.mul (.var 0) (.mul (.var 2) (.mul (.pow (.var 3) 3) (.pow (.var 4) 2))))) (.add (.mul (.int (-2)) (.mul (.var 0) (.mul (.var 4) (.mul (.pow (.var 2) 2) (.pow (.var 3) 2))))) (.add (.mul (.int 4) (.mul (.var 2) (.mul (.var 4) (.mul (.pow (.var 1) 2) (.pow (.var 3) 2))))) (.add (.mul (.int 4) (.mul (.pow (.var 1) 2) (.mul (.pow (.var 2) 2) (.mul (.pow (.var 3) 2) (.pow (.var 4) 2))))) (.add (.mul (.int 8) (.mul (.var 1) (.mul (.var 3) (.mul (.pow (.var 2) 4) (.pow (.var 4) 3))))) (.add (.mul (.int 8) (.mul (.var 2) (.mul (.pow (.var 0) 2) (.mul (.pow (.var 3) 5) (.pow (.var 4) 3))))) (.add (.mul (.int 8) (.mul (.var 2) (.mul (.pow (.var 1) 2) (.mul (.pow (.var 3) 3) (.pow (.var 4) 3))))) (.add (.mul (.int 10) (.mul (.var 1) (.mul (.var 3) (.mul (.var 4) (.pow (.var 2) 2))))) (.add (.mul (.int 16) (.mul (.var 1) (.mul (.var 3) (.mul (.pow (.var 2) 3) (.pow (.var 4) 2))))) (.add (.mul (.int (-16)) (.mul (.var 0) (.mul (.var 1) (.mul (.var 2) (.mul (.pow (.var 3) 4) (.pow (.var 4) 3)))))) (.add (.mul (.int (-4)) (.mul (.var 0) (.mul (.var 1) (.mul (.pow (.var 2) 2) (.mul (.pow (.var 3) 3) (.pow (.var 4) 2)))))) (.mul (.int (-2)) (.mul (.var 0) (.mul (.var 1) (.mul (.var 2) (.mul (.var 4) (.pow (.var 3) 3))))))))))))))))))))))))))))))))))))))))))
theorem dataN9t_5_3_binding : litN9tExpr 5 3=dataN9t_5_3 := rfl

def dataN9t_5_4 : RingExpr := (.mul (.var 7) (.mul (.var 9) (.mul (.pow (.var 10) 2) (.mul (.pow (.var 8) 3) (.add (.mul (.var 1) (.var 2)) (.add (.mul (.var 3) (.pow (.var 1) 2)) (.add (.mul (.int (-2)) (.mul (.var 1) (.mul (.var 3) (.var 4)))) (.add (.mul (.int 4) (.mul (.var 1) (.mul (.var 4) (.pow (.var 2) 2)))) (.add (.mul (.int 4) (.mul (.var 1) (.mul (.pow (.var 2) 3) (.pow (.var 4) 2)))) (.add (.mul (.int 4) (.mul (.pow (.var 0) 2) (.mul (.pow (.var 3) 4) (.pow (.var 4) 2)))) (.add (.mul (.int 4) (.mul (.pow (.var 1) 2) (.mul (.pow (.var 3) 2) (.pow (.var 4) 2)))) (.add (.mul (.int (-8)) (.mul (.var 0) (.mul (.var 1) (.mul (.pow (.var 3) 3) (.pow (.var 4) 2))))) (.add (.mul (.int (-8)) (.mul (.var 0) (.mul (.var 3) (.mul (.pow (.var 2) 3) (.pow (.var 4) 2))))) (.add (.mul (.int (-4)) (.mul (.var 0) (.mul (.var 3) (.mul (.var 4) (.pow (.var 2) 2))))) (.add (.mul (.int (-4)) (.mul (.var 1) (.mul (.var 2) (.mul (.var 3) (.pow (.var 4) 2))))) (.add (.mul (.int 2) (.mul (.var 2) (.mul (.var 3) (.mul (.var 4) (.pow (.var 1) 2))))) (.mul (.int 8) (.mul (.var 0) (.mul (.var 2) (.mul (.pow (.var 3) 2) (.pow (.var 4) 2)))))))))))))))))))))
theorem dataN9t_5_4_binding : litN9tExpr 5 4=dataN9t_5_4 := rfl

def dataN9t_5_5 : RingExpr := (.mul (.var 7) (.mul (.var 9) (.mul (.pow (.var 10) 2) (.mul (.pow (.var 8) 3) (.add (.mul (.int (-1)) (.var 2)) (.add (.mul (.int (-1)) (.mul (.var 1) (.var 3))) (.add (.mul (.int (-4)) (.mul (.var 4) (.pow (.var 2) 2))) (.add (.mul (.int (-4)) (.mul (.pow (.var 2) 3) (.pow (.var 4) 2))) (.add (.mul (.int 2) (.mul (.var 3) (.var 4))) (.add (.mul (.int (-4)) (.mul (.var 1) (.mul (.pow (.var 3) 2) (.pow (.var 4) 2)))) (.add (.mul (.int 4) (.mul (.var 2) (.mul (.var 3) (.pow (.var 4) 2)))) (.add (.mul (.int 8) (.mul (.var 0) (.mul (.pow (.var 3) 3) (.pow (.var 4) 2)))) (.add (.mul (.int (-4)) (.mul (.var 0) (.mul (.pow (.var 2) 2) (.mul (.pow (.var 3) 2) (.pow (.var 4) 2))))) (.add (.mul (.int (-2)) (.mul (.var 0) (.mul (.var 2) (.mul (.var 4) (.pow (.var 3) 2))))) (.add (.mul (.int (-2)) (.mul (.var 1) (.mul (.var 2) (.mul (.var 3) (.var 4))))) (.mul (.int 2) (.mul (.var 0) (.mul (.var 1) (.mul (.var 4) (.pow (.var 3) 3))))))))))))))))))))
theorem dataN9t_5_5_binding : litN9tExpr 5 5=dataN9t_5_5 := rfl

def dataN9t_5_8 : RingExpr := (.mul (.var 7) (.mul (.pow (.var 10) 3) (.mul (.pow (.var 8) 5) (.mul (.pow (.var 9) 2) (.add (.mul (.int (-1)) (.mul (.var 11) (.pow (.var 2) 2))) (.add (.mul (.int (-1)) (.mul (.var 11) (.mul (.pow (.var 1) 2) (.pow (.var 3) 2)))) (.add (.mul (.int (-12)) (.mul (.var 11) (.mul (.pow (.var 2) 4) (.pow (.var 4) 2)))) (.add (.mul (.int (-8)) (.mul (.var 11) (.mul (.pow (.var 2) 5) (.pow (.var 4) 3)))) (.add (.mul (.int (-6)) (.mul (.var 11) (.mul (.var 4) (.pow (.var 2) 3)))) (.add (.mul (.int (-4)) (.mul (.var 11) (.mul (.pow (.var 3) 2) (.pow (.var 4) 2)))) (.add (.mul (.int (-4)) (.mul (.var 15) (.mul (.pow (.var 3) 3) (.pow (.var 4) 2)))) (.add (.mul (.int (-16)) (.mul (.var 11) (.mul (.var 0) (.mul (.pow (.var 3) 4) (.pow (.var 4) 3))))) (.add (.mul (.int (-16)) (.mul (.var 15) (.mul (.var 0) (.mul (.pow (.var 3) 5) (.pow (.var 4) 3))))) (.add (.mul (.int (-8)) (.mul (.var 11) (.mul (.var 2) (.mul (.pow (.var 3) 2) (.pow (.var 4) 3))))) (.add (.mul (.int (-8)) (.mul (.var 12) (.mul (.var 0) (.mul (.pow (.var 3) 4) (.pow (.var 4) 2))))) (.add (.mul (.int (-8)) (.mul (.var 12) (.mul (.pow (.var 0) 2) (.mul (.pow (.var 3) 6) (.pow (.var 4) 3))))) (.add (.mul (.int (-8)) (.mul (.var 12) (.mul (.pow (.var 1) 2) (.mul (.pow (.var 3) 4) (.pow (.var 4) 3))))) (.add (.mul (.int (-8)) (.mul (.var 15) (.mul (.var 2) (.mul (.pow (.var 3) 3) (.pow (.var 4) 3))))) (.add (.mul (.int (-4)) (.mul (.var 11) (.mul (.pow (.var 1) 2) (.mul (.pow (.var 3) 3) (.pow (.var 4) 2))))) (.add (.mul (.int (-2)) (.mul (.var 11) (.mul (.var 1) (.mul (.var 2) (.var 3))))) (.add (.mul (.int (-2)) (.mul (.var 12) (.mul (.var 4) (.mul (.pow (.var 1) 2) (.pow (.var 3) 3))))) (.add (.mul (.int 2) (.mul (.var 15) (.mul (.var 1) (.mul (.var 4) (.pow (.var 3) 3))))) (.add (.mul (.int 2) (.mul (.var 15) (.mul (.var 2) (.mul (.var 4) (.pow (.var 3) 2))))) (.add (.mul (.int 4) (.mul (.var 11) (.mul (.var 1) (.mul (.var 4) (.pow (.var 3) 2))))) (.add (.mul (.int 4) (.mul (.var 11) (.mul (.var 2) (.mul (.var 3) (.var 4))))) (.add (.mul (.int 4) (.mul (.var 11) (.mul (.pow (.var 0) 2) (.mul (.pow (.var 3) 5) (.pow (.var 4) 2))))) (.add (.mul (.int 4) (.mul (.var 12) (.mul (.var 1) (.mul (.pow (.var 3) 3) (.pow (.var 4) 2))))) (.add (.mul (.int 8) (.mul (.var 11) (.mul (.var 1) (.mul (.pow (.var 3) 3) (.pow (.var 4) 3))))) (.add (.mul (.int 8) (.mul (.var 15) (.mul (.var 1) (.mul (.pow (.var 3) 4) (.pow (.var 4) 3))))) (.add (.mul (.int 8) (.mul (.var 15) (.mul (.pow (.var 2) 2) (.mul (.pow (.var 3) 2) (.pow (.var 4) 2))))) (.add (.mul (.int 8) (.mul (.var 15) (.mul (.pow (.var 2) 3) (.mul (.pow (.var 3) 2) (.pow (.var 4) 3))))) (.add (.mul (.int 16) (.mul (.var 11) (.mul (.var 3) (.mul (.pow (.var 2) 2) (.pow (.var 4) 2))))) (.add (.mul (.int 16) (.mul (.var 11) (.mul (.var 3) (.mul (.pow (.var 2) 3) (.pow (.var 4) 3))))) (.add (.mul (.int (-16)) (.mul (.var 11) (.mul (.var 1) (.mul (.var 3) (.mul (.pow (.var 2) 3) (.pow (.var 4) 2)))))) (.add (.mul (.int (-16)) (.mul (.var 12) (.mul (.var 0) (.mul (.var 2) (.mul (.pow (.var 3) 4) (.pow (.var 4) 3)))))) (.add (.mul (.int (-10)) (.mul (.var 11) (.mul (.var 1) (.mul (.var 3) (.mul (.var 4) (.pow (.var 2) 2)))))) (.add (.mul (.int (-8)) (.mul (.var 11) (.mul (.var 1) (.mul (.var 3) (.mul (.pow (.var 2) 4) (.pow (.var 4) 3)))))) (.add (.mul (.int (-8)) (.mul (.var 11) (.mul (.var 2) (.mul (.pow (.var 0) 2) (.mul (.pow (.var 3) 5) (.pow (.var 4) 3)))))) (.add (.mul (.int (-8)) (.mul (.var 11) (.mul (.var 2) (.mul (.pow (.var 1) 2) (.mul (.pow (.var 3) 3) (.pow (.var 4) 3)))))) (.add (.mul (.int (-8)) (.mul (.var 12) (.mul (.var 1) (.mul (.pow (.var 2) 2) (.mul (.pow (.var 3) 2) (.pow (.var 4) 2)))))) (.add (.mul (.int (-8)) (.mul (.var 12) (.mul (.var 1) (.mul (.pow (.var 2) 3) (.mul (.pow (.var 3) 2) (.pow (.var 4) 3)))))) (.add (.mul (.int (-4)) (.mul (.var 11) (.mul (.var 2) (.mul (.var 4) (.mul (.pow (.var 1) 2) (.pow (.var 3) 2)))))) (.add (.mul (.int (-4)) (.mul (.var 11) (.mul (.pow (.var 1) 2) (.mul (.pow (.var 2) 2) (.mul (.pow (.var 3) 2) (.pow (.var 4) 2)))))) (.add (.mul (.int (-4)) (.mul (.var 12) (.mul (.var 2) (.mul (.pow (.var 1) 2) (.mul (.pow (.var 3) 3) (.pow (.var 4) 2)))))) (.add (.mul (.int (-2)) (.mul (.var 12) (.mul (.var 1) (.mul (.var 2) (.mul (.var 4) (.pow (.var 3) 2)))))) (.add (.mul (.int 2) (.mul (.var 11) (.mul (.var 0) (.mul (.var 4) (.mul (.pow (.var 2) 2) (.pow (.var 3) 2)))))) (.add (.mul (.int 4) (.mul (.var 11) (.mul (.var 0) (.mul (.var 1) (.mul (.pow (.var 3) 4) (.pow (.var 4) 2)))))) (.add (.mul (.int 4) (.mul (.var 11) (.mul (.var 0) (.mul (.var 2) (.mul (.pow (.var 3) 3) (.pow (.var 4) 2)))))) (.add (.mul (.int 4) (.mul (.var 12) (.mul (.var 0) (.mul (.var 1) (.mul (.var 4) (.pow (.var 3) 4)))))) (.add (.mul (.int 4) (.mul (.var 12) (.mul (.var 0) (.mul (.var 2) (.mul (.var 4) (.pow (.var 3) 3)))))) (.add (.mul (.int 4) (.mul (.var 15) (.mul (.var 0) (.mul (.var 1) (.mul (.pow (.var 3) 5) (.pow (.var 4) 2)))))) (.add (.mul (.int 4) (.mul (.var 15) (.mul (.var 0) (.mul (.var 2) (.mul (.pow (.var 3) 4) (.pow (.var 4) 2)))))) (.add (.mul (.int 4) (.mul (.var 15) (.mul (.var 1) (.mul (.var 2) (.mul (.pow (.var 3) 3) (.pow (.var 4) 2)))))) (.add (.mul (.int 8) (.mul (.var 11) (.mul (.var 0) (.mul (.pow (.var 2) 2) (.mul (.pow (.var 3) 3) (.pow (.var 4) 3)))))) (.add (.mul (.int 8) (.mul (.var 11) (.mul (.var 0) (.mul (.pow (.var 2) 3) (.mul (.pow (.var 3) 2) (.pow (.var 4) 2)))))) (.add (.mul (.int 8) (.mul (.var 11) (.mul (.var 0) (.mul (.pow (.var 2) 4) (.mul (.pow (.var 3) 2) (.pow (.var 4) 3)))))) (.add (.mul (.int 8) (.mul (.var 11) (.mul (.var 1) (.mul (.var 2) (.mul (.pow (.var 3) 2) (.pow (.var 4) 2)))))) (.add (.mul (.int 8) (.mul (.var 12) (.mul (.var 1) (.mul (.var 2) (.mul (.pow (.var 3) 3) (.pow (.var 4) 3)))))) (.add (.mul (.int 8) (.mul (.var 15) (.mul (.var 0) (.mul (.pow (.var 2) 2) (.mul (.pow (.var 3) 4) (.pow (.var 4) 3)))))) (.add (.mul (.int 16) (.mul (.var 12) (.mul (.var 0) (.mul (.var 1) (.mul (.pow (.var 3) 5) (.pow (.var 4) 3)))))) (.add (.mul (.int 16) (.mul (.var 12) (.mul (.var 0) (.mul (.pow (.var 2) 2) (.mul (.pow (.var 3) 3) (.pow (.var 4) 2)))))) (.add (.mul (.int 16) (.mul (.var 12) (.mul (.var 0) (.mul (.pow (.var 2) 3) (.mul (.pow (.var 3) 3) (.pow (.var 4) 3)))))) (.add (.mul (.int 2) (.mul (.var 11) (.mul (.var 0) (.mul (.var 1) (.mul (.var 2) (.mul (.var 4) (.pow (.var 3) 3))))))) (.add (.mul (.int 4) (.mul (.var 11) (.mul (.var 0) (.mul (.var 1) (.mul (.pow (.var 2) 2) (.mul (.pow (.var 3) 3) (.pow (.var 4) 2))))))) (.add (.mul (.int 8) (.mul (.var 12) (.mul (.var 0) (.mul (.var 1) (.mul (.var 2) (.mul (.pow (.var 3) 4) (.pow (.var 4) 2))))))) (.mul (.int 16) (.mul (.var 11) (.mul (.var 0) (.mul (.var 1) (.mul (.var 2) (.mul (.pow (.var 3) 4) (.pow (.var 4) 3))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
theorem dataN9t_5_8_binding : litN9tExpr 5 8=dataN9t_5_8 := rfl

def dataN9t_6_6 : RingExpr := (.mul (.var 10) (.mul (.var 8) (.add (.var 2) (.add (.mul (.var 1) (.var 3)) (.add (.mul (.int 2) (.mul (.var 4) (.pow (.var 2) 2))) (.add (.mul (.int (-2)) (.mul (.var 0) (.mul (.var 2) (.mul (.var 4) (.pow (.var 3) 2))))) (.mul (.int 2) (.mul (.var 1) (.mul (.var 2) (.mul (.var 3) (.var 4)))))))))))
theorem dataN9t_6_6_binding : litN9tExpr 6 6=dataN9t_6_6 := rfl

def dataN9t_6_7 : RingExpr := (.add (.mul (.int (1)) (.pow (.var 10) 1)) (.add (.mul (.var 2) (.var 4)) (.add (.mul (.var 1) (.mul (.var 3) (.var 4))) (.mul (.int (-1)) (.mul (.var 0) (.mul (.var 4) (.pow (.var 3) 2)))))))
theorem dataN9t_6_7_binding : litN9tExpr 6 7=dataN9t_6_7 := rfl

def dataN9t_7_6 : RingExpr := (.mul (.var 10) (.mul (.pow (.var 8) 2) (.add (.mul (.int (-1)) (.var 3)) (.add (.mul (.int (-1)) (.pow (.var 2) 2)) (.add (.mul (.int (-2)) (.mul (.var 4) (.pow (.var 2) 3))) (.add (.mul (.int (-1)) (.mul (.var 1) (.mul (.var 2) (.var 3)))) (.add (.mul (.int (-2)) (.mul (.var 1) (.mul (.var 3) (.mul (.var 4) (.pow (.var 2) 2))))) (.mul (.int 2) (.mul (.var 0) (.mul (.var 4) (.mul (.pow (.var 2) 2) (.pow (.var 3) 2))))))))))))
theorem dataN9t_7_6_binding : litN9tExpr 7 6=dataN9t_7_6 := rfl

def dataN9t_7_7 : RingExpr := (.mul (.var 10) (.mul (.var 8) (.add (.mul (.int (-1)) (.var 2)) (.add (.mul (.int (-2)) (.mul (.var 4) (.pow (.var 2) 2))) (.add (.mul (.int (-2)) (.mul (.var 1) (.mul (.var 2) (.mul (.var 3) (.var 4))))) (.mul (.int 2) (.mul (.var 0) (.mul (.var 2) (.mul (.var 4) (.pow (.var 3) 2))))))))))
theorem dataN9t_7_7_binding : litN9tExpr 7 7=dataN9t_7_7 := rfl

def dataCSz_0_0 : RingExpr := (.int 1)
theorem dataCSz_0_0_binding : litCSzExpr 0 0=dataCSz_0_0 := rfl

def dataCSz_1_1 : RingExpr := (.int 1)
theorem dataCSz_1_1_binding : litCSzExpr 1 1=dataCSz_1_1 := rfl

def dataCSz_2_0 : RingExpr := (.mul (.var 7) (.mul (.var 9) (.mul (.pow (.var 10) 2) (.mul (.pow (.var 8) 3) (.add (.mul (.int 3) (.var 2)) (.add (.mul (.int (-12)) (.mul (.pow (.var 2) 3) (.pow (.var 4) 2))) (.add (.mul (.int (-6)) (.mul (.var 3) (.var 4))) (.add (.mul (.int (-2)) (.mul (.var 5) (.var 2))) (.add (.mul (.int 3) (.mul (.var 1) (.var 3))) (.add (.mul (.int (-12)) (.mul (.var 0) (.mul (.pow (.var 3) 3) (.pow (.var 4) 2)))) (.add (.mul (.int (-6)) (.mul (.var 4) (.mul (.pow (.var 1) 2) (.pow (.var 3) 2)))) (.add (.mul (.int (-4)) (.mul (.var 5) (.mul (.var 4) (.pow (.var 2) 2)))) (.add (.mul (.int (-2)) (.mul (.var 5) (.mul (.var 1) (.var 3)))) (.add (.mul (.int 4) (.mul (.var 5) (.mul (.var 3) (.var 4)))) (.add (.mul (.int 12) (.mul (.var 1) (.mul (.pow (.var 3) 2) (.pow (.var 4) 2)))) (.add (.mul (.int 12) (.mul (.var 2) (.mul (.var 3) (.pow (.var 4) 2)))) (.add (.mul (.int (-24)) (.mul (.var 1) (.mul (.var 3) (.mul (.pow (.var 2) 2) (.pow (.var 4) 2))))) (.add (.mul (.int (-12)) (.mul (.var 2) (.mul (.pow (.var 1) 2) (.mul (.pow (.var 3) 2) (.pow (.var 4) 2))))) (.add (.mul (.int (-6)) (.mul (.var 0) (.mul (.var 2) (.mul (.var 4) (.pow (.var 3) 2))))) (.add (.mul (.int (-6)) (.mul (.var 1) (.mul (.var 2) (.mul (.var 3) (.var 4))))) (.add (.mul (.int 12) (.mul (.var 0) (.mul (.pow (.var 2) 2) (.mul (.pow (.var 3) 2) (.pow (.var 4) 2))))) (.add (.mul (.int (-4)) (.mul (.var 5) (.mul (.var 1) (.mul (.var 2) (.mul (.var 3) (.var 4)))))) (.add (.mul (.int 4) (.mul (.var 5) (.mul (.var 0) (.mul (.var 2) (.mul (.var 4) (.pow (.var 3) 2)))))) (.mul (.int 12) (.mul (.var 0) (.mul (.var 1) (.mul (.var 2) (.mul (.pow (.var 3) 3) (.pow (.var 4) 2)))))))))))))))))))))))))))))
theorem dataCSz_2_0_binding : litCSzExpr 2 0=dataCSz_2_0 := rfl

def dataCSz_2_1 : RingExpr := (.mul (.var 7) (.mul (.var 10) (.mul (.var 8) (.add (.mul (.int 3) (.var 1)) (.add (.mul (.int (-2)) (.mul (.var 5) (.var 1))) (.add (.mul (.int (-6)) (.mul (.var 1) (.mul (.var 2) (.var 4)))) (.add (.mul (.int (-6)) (.mul (.var 3) (.mul (.var 4) (.pow (.var 1) 2)))) (.add (.mul (.int 2) (.mul (.var 5) (.mul (.var 0) (.var 3)))) (.mul (.int 6) (.mul (.var 0) (.mul (.var 1) (.mul (.var 4) (.pow (.var 3) 2)))))))))))))
theorem dataCSz_2_1_binding : litCSzExpr 2 1=dataCSz_2_1 := rfl

def dataCSz_2_2 : RingExpr := (.mul (.var 7) (.mul (.var 10) (.mul (.var 8) (.add (.int (-3)) (.add (.mul (.int 2) (.var 5)) (.add (.mul (.int 6) (.mul (.var 2) (.var 4))) (.add (.mul (.int (-6)) (.mul (.var 0) (.mul (.var 4) (.pow (.var 3) 2)))) (.mul (.int 6) (.mul (.var 1) (.mul (.var 3) (.var 4)))))))))))
theorem dataCSz_2_2_binding : litCSzExpr 2 2=dataCSz_2_2 := rfl

def dataCSz_2_8 : RingExpr := (.mul (.var 7) (.mul (.var 9) (.mul (.pow (.var 10) 2) (.mul (.pow (.var 8) 3) (.add (.mul (.int (-3)) (.mul (.var 11) (.var 2))) (.add (.mul (.int (-3)) (.mul (.var 11) (.mul (.var 1) (.var 3)))) (.add (.mul (.int 2) (.mul (.var 11) (.mul (.var 5) (.var 2)))) (.add (.mul (.int 6) (.mul (.var 11) (.mul (.var 3) (.var 4)))) (.add (.mul (.int 6) (.mul (.var 15) (.mul (.var 4) (.pow (.var 3) 2)))) (.add (.mul (.int 12) (.mul (.var 11) (.mul (.pow (.var 2) 3) (.pow (.var 4) 2)))) (.add (.mul (.int (-12)) (.mul (.var 11) (.mul (.var 1) (.mul (.pow (.var 3) 2) (.pow (.var 4) 2))))) (.add (.mul (.int (-12)) (.mul (.var 11) (.mul (.var 2) (.mul (.var 3) (.pow (.var 4) 2))))) (.add (.mul (.int (-12)) (.mul (.var 15) (.mul (.var 1) (.mul (.pow (.var 3) 3) (.pow (.var 4) 2))))) (.add (.mul (.int (-12)) (.mul (.var 15) (.mul (.var 2) (.mul (.pow (.var 3) 2) (.pow (.var 4) 2))))) (.add (.mul (.int (-6)) (.mul (.var 12) (.mul (.var 1) (.mul (.var 4) (.pow (.var 3) 2))))) (.add (.mul (.int (-4)) (.mul (.var 11) (.mul (.var 5) (.mul (.var 3) (.var 4))))) (.add (.mul (.int (-4)) (.mul (.var 15) (.mul (.var 5) (.mul (.var 4) (.pow (.var 3) 2))))) (.add (.mul (.int 2) (.mul (.var 11) (.mul (.var 5) (.mul (.var 1) (.var 3))))) (.add (.mul (.int 4) (.mul (.var 11) (.mul (.var 5) (.mul (.var 4) (.pow (.var 2) 2))))) (.add (.mul (.int 4) (.mul (.var 13) (.mul (.var 0) (.mul (.var 4) (.pow (.var 3) 3))))) (.add (.mul (.int 6) (.mul (.var 11) (.mul (.var 4) (.mul (.pow (.var 1) 2) (.pow (.var 3) 2))))) (.add (.mul (.int 12) (.mul (.var 11) (.mul (.var 0) (.mul (.pow (.var 3) 3) (.pow (.var 4) 2))))) (.add (.mul (.int 12) (.mul (.var 12) (.mul (.pow (.var 1) 2) (.mul (.pow (.var 3) 3) (.pow (.var 4) 2))))) (.add (.mul (.int 12) (.mul (.var 15) (.mul (.var 0) (.mul (.pow (.var 3) 4) (.pow (.var 4) 2))))) (.add (.mul (.int (-12)) (.mul (.var 11) (.mul (.var 0) (.mul (.pow (.var 2) 2) (.mul (.pow (.var 3) 2) (.pow (.var 4) 2)))))) (.add (.mul (.int (-12)) (.mul (.var 12) (.mul (.var 0) (.mul (.var 1) (.mul (.pow (.var 3) 4) (.pow (.var 4) 2)))))) (.add (.mul (.int (-4)) (.mul (.var 12) (.mul (.var 5) (.mul (.var 0) (.mul (.var 4) (.pow (.var 3) 3)))))) (.add (.mul (.int 4) (.mul (.var 12) (.mul (.var 5) (.mul (.var 1) (.mul (.var 4) (.pow (.var 3) 2)))))) (.add (.mul (.int 6) (.mul (.var 11) (.mul (.var 0) (.mul (.var 2) (.mul (.var 4) (.pow (.var 3) 2)))))) (.add (.mul (.int 6) (.mul (.var 11) (.mul (.var 1) (.mul (.var 2) (.mul (.var 3) (.var 4)))))) (.add (.mul (.int 12) (.mul (.var 11) (.mul (.var 2) (.mul (.pow (.var 1) 2) (.mul (.pow (.var 3) 2) (.pow (.var 4) 2)))))) (.add (.mul (.int 12) (.mul (.var 12) (.mul (.var 1) (.mul (.var 2) (.mul (.pow (.var 3) 2) (.pow (.var 4) 2)))))) (.add (.mul (.int 24) (.mul (.var 11) (.mul (.var 1) (.mul (.var 3) (.mul (.pow (.var 2) 2) (.pow (.var 4) 2)))))) (.add (.mul (.int (-12)) (.mul (.var 11) (.mul (.var 0) (.mul (.var 1) (.mul (.var 2) (.mul (.pow (.var 3) 3) (.pow (.var 4) 2))))))) (.add (.mul (.int (-4)) (.mul (.var 11) (.mul (.var 5) (.mul (.var 0) (.mul (.var 2) (.mul (.var 4) (.pow (.var 3) 2))))))) (.mul (.int 4) (.mul (.var 11) (.mul (.var 5) (.mul (.var 1) (.mul (.var 2) (.mul (.var 3) (.var 4))))))))))))))))))))))))))))))))))))))))))
theorem dataCSz_2_8_binding : litCSzExpr 2 8=dataCSz_2_8 := rfl

def dataCSz_3_0 : RingExpr := (.mul (.var 7) (.mul (.var 9) (.mul (.pow (.var 10) 2) (.mul (.pow (.var 8) 3) (.add (.var 2) (.add (.mul (.var 1) (.var 3)) (.add (.mul (.int (-2)) (.mul (.var 3) (.var 4))) (.add (.mul (.int 4) (.mul (.var 4) (.pow (.var 2) 2))) (.add (.mul (.int 4) (.mul (.pow (.var 2) 3) (.pow (.var 4) 2))) (.add (.mul (.int (-4)) (.mul (.var 0) (.mul (.pow (.var 3) 3) (.pow (.var 4) 2)))) (.add (.mul (.int (-4)) (.mul (.var 2) (.mul (.var 3) (.pow (.var 4) 2)))) (.add (.mul (.int (-4)) (.mul (.var 0) (.mul (.pow (.var 2) 2) (.mul (.pow (.var 3) 2) (.pow (.var 4) 2))))) (.add (.mul (.int (-2)) (.mul (.var 0) (.mul (.var 2) (.mul (.var 4) (.pow (.var 3) 2))))) (.add (.mul (.int 4) (.mul (.var 1) (.mul (.var 2) (.mul (.var 3) (.var 4))))) (.mul (.int 4) (.mul (.var 1) (.mul (.var 3) (.mul (.pow (.var 2) 2) (.pow (.var 4) 2)))))))))))))))))))
theorem dataCSz_3_0_binding : litCSzExpr 3 0=dataCSz_3_0 := rfl

def dataCSz_3_1 : RingExpr := (.mul (.var 7) (.mul (.var 10) (.mul (.var 8) (.add (.var 1) (.add (.mul (.int 2) (.mul (.var 1) (.mul (.var 2) (.var 4)))) (.mul (.int (-4)) (.mul (.var 0) (.mul (.var 2) (.mul (.var 3) (.var 4))))))))))
theorem dataCSz_3_1_binding : litCSzExpr 3 1=dataCSz_3_1 := rfl

def dataCSz_3_2 : RingExpr := (.mul (.var 7) (.mul (.var 10) (.mul (.var 8) (.add (.int (-1)) (.add (.mul (.int (-2)) (.mul (.var 2) (.var 4))) (.mul (.int (-2)) (.mul (.var 0) (.mul (.var 4) (.pow (.var 3) 2)))))))))
theorem dataCSz_3_2_binding : litCSzExpr 3 2=dataCSz_3_2 := rfl

def dataCSz_3_8 : RingExpr := (.mul (.var 7) (.mul (.var 9) (.mul (.pow (.var 10) 2) (.mul (.pow (.var 8) 3) (.add (.mul (.int (-1)) (.mul (.var 11) (.var 2))) (.add (.mul (.int (-1)) (.mul (.var 11) (.mul (.var 1) (.var 3)))) (.add (.mul (.int (-4)) (.mul (.var 11) (.mul (.var 4) (.pow (.var 2) 2)))) (.add (.mul (.int (-4)) (.mul (.var 11) (.mul (.pow (.var 2) 3) (.pow (.var 4) 2)))) (.add (.mul (.int 2) (.mul (.var 11) (.mul (.var 3) (.var 4)))) (.add (.mul (.int 2) (.mul (.var 15) (.mul (.var 4) (.pow (.var 3) 2)))) (.add (.mul (.int (-2)) (.mul (.var 12) (.mul (.var 1) (.mul (.var 4) (.pow (.var 3) 2))))) (.add (.mul (.int 4) (.mul (.var 11) (.mul (.var 0) (.mul (.pow (.var 3) 3) (.pow (.var 4) 2))))) (.add (.mul (.int 4) (.mul (.var 11) (.mul (.var 2) (.mul (.var 3) (.pow (.var 4) 2))))) (.add (.mul (.int 4) (.mul (.var 14) (.mul (.var 0) (.mul (.var 4) (.pow (.var 3) 3))))) (.add (.mul (.int 4) (.mul (.var 15) (.mul (.var 0) (.mul (.pow (.var 3) 4) (.pow (.var 4) 2))))) (.add (.mul (.int 4) (.mul (.var 15) (.mul (.var 2) (.mul (.pow (.var 3) 2) (.pow (.var 4) 2))))) (.add (.mul (.int (-4)) (.mul (.var 11) (.mul (.var 1) (.mul (.var 2) (.mul (.var 3) (.var 4)))))) (.add (.mul (.int (-4)) (.mul (.var 11) (.mul (.var 1) (.mul (.var 3) (.mul (.pow (.var 2) 2) (.pow (.var 4) 2)))))) (.add (.mul (.int (-4)) (.mul (.var 12) (.mul (.var 1) (.mul (.var 2) (.mul (.pow (.var 3) 2) (.pow (.var 4) 2)))))) (.add (.mul (.int 2) (.mul (.var 11) (.mul (.var 0) (.mul (.var 2) (.mul (.var 4) (.pow (.var 3) 2)))))) (.add (.mul (.int 4) (.mul (.var 11) (.mul (.var 0) (.mul (.pow (.var 2) 2) (.mul (.pow (.var 3) 2) (.pow (.var 4) 2)))))) (.mul (.int 8) (.mul (.var 12) (.mul (.var 0) (.mul (.var 2) (.mul (.pow (.var 3) 3) (.pow (.var 4) 2)))))))))))))))))))))))))))
theorem dataCSz_3_8_binding : litCSzExpr 3 8=dataCSz_3_8 := rfl

def dataCSz_4_2 : RingExpr := (.int 1)
theorem dataCSz_4_2_binding : litCSzExpr 4 2=dataCSz_4_2 := rfl

def dataCSz_5_0 : RingExpr := (.mul (.var 7) (.mul (.var 9) (.mul (.pow (.var 10) 2) (.mul (.pow (.var 8) 4) (.add (.mul (.int (-1)) (.pow (.var 2) 2)) (.add (.mul (.int (-4)) (.mul (.var 4) (.pow (.var 2) 3))) (.add (.mul (.int (-4)) (.mul (.pow (.var 2) 4) (.pow (.var 4) 2))) (.add (.mul (.int (-4)) (.mul (.pow (.var 3) 2) (.pow (.var 4) 2))) (.add (.mul (.int (-1)) (.mul (.var 1) (.mul (.var 2) (.var 3)))) (.add (.mul (.int 2) (.mul (.var 0) (.mul (.var 4) (.pow (.var 3) 3)))) (.add (.mul (.int 2) (.mul (.var 1) (.mul (.var 4) (.pow (.var 3) 2)))) (.add (.mul (.int 4) (.mul (.var 2) (.mul (.var 3) (.var 4)))) (.add (.mul (.int 8) (.mul (.var 3) (.mul (.pow (.var 2) 2) (.pow (.var 4) 2)))) (.add (.mul (.int (-4)) (.mul (.var 1) (.mul (.var 3) (.mul (.var 4) (.pow (.var 2) 2))))) (.add (.mul (.int (-4)) (.mul (.var 1) (.mul (.var 3) (.mul (.pow (.var 2) 3) (.pow (.var 4) 2))))) (.add (.mul (.int 2) (.mul (.var 0) (.mul (.var 4) (.mul (.pow (.var 2) 2) (.pow (.var 3) 2))))) (.add (.mul (.int 4) (.mul (.var 0) (.mul (.pow (.var 2) 3) (.mul (.pow (.var 3) 2) (.pow (.var 4) 2))))) (.mul (.int 4) (.mul (.var 1) (.mul (.var 2) (.mul (.pow (.var 3) 2) (.pow (.var 4) 2))))))))))))))))))))))
theorem dataCSz_5_0_binding : litCSzExpr 5 0=dataCSz_5_0 := rfl

def dataCSz_5_1 : RingExpr := (.mul (.var 7) (.mul (.var 10) (.mul (.pow (.var 8) 2) (.add (.mul (.int (-1)) (.mul (.var 1) (.var 2))) (.add (.mul (.int (-2)) (.mul (.var 0) (.mul (.var 4) (.pow (.var 3) 2)))) (.add (.mul (.int (-2)) (.mul (.var 1) (.mul (.var 4) (.pow (.var 2) 2)))) (.add (.mul (.int 2) (.mul (.var 0) (.mul (.var 2) (.var 3)))) (.add (.mul (.int 2) (.mul (.var 1) (.mul (.var 3) (.var 4)))) (.mul (.int 4) (.mul (.var 0) (.mul (.var 3) (.mul (.var 4) (.pow (.var 2) 2)))))))))))))
theorem dataCSz_5_1_binding : litCSzExpr 5 1=dataCSz_5_1 := rfl

def dataCSz_5_2 : RingExpr := (.mul (.var 7) (.mul (.var 10) (.mul (.pow (.var 8) 2) (.add (.var 2) (.add (.mul (.int (-2)) (.mul (.var 3) (.var 4))) (.add (.mul (.int 2) (.mul (.var 0) (.pow (.var 3) 2))) (.add (.mul (.int 2) (.mul (.var 4) (.pow (.var 2) 2))) (.mul (.int 2) (.mul (.var 0) (.mul (.var 2) (.mul (.var 4) (.pow (.var 3) 2))))))))))))
theorem dataCSz_5_2_binding : litCSzExpr 5 2=dataCSz_5_2 := rfl

def dataCSz_5_8 : RingExpr := (.mul (.var 7) (.mul (.var 9) (.mul (.pow (.var 10) 2) (.mul (.pow (.var 8) 4) (.add (.mul (.var 11) (.pow (.var 2) 2)) (.add (.mul (.int 4) (.mul (.var 11) (.mul (.var 4) (.pow (.var 2) 3)))) (.add (.mul (.int 4) (.mul (.var 11) (.mul (.pow (.var 2) 4) (.pow (.var 4) 2)))) (.add (.mul (.int 4) (.mul (.var 11) (.mul (.pow (.var 3) 2) (.pow (.var 4) 2)))) (.add (.mul (.int 4) (.mul (.var 15) (.mul (.pow (.var 3) 3) (.pow (.var 4) 2)))) (.add (.mul (.var 11) (.mul (.var 1) (.mul (.var 2) (.var 3)))) (.add (.mul (.int (-8)) (.mul (.var 11) (.mul (.var 3) (.mul (.pow (.var 2) 2) (.pow (.var 4) 2))))) (.add (.mul (.int (-4)) (.mul (.var 11) (.mul (.var 2) (.mul (.var 3) (.var 4))))) (.add (.mul (.int (-4)) (.mul (.var 12) (.mul (.var 1) (.mul (.pow (.var 3) 3) (.pow (.var 4) 2))))) (.add (.mul (.int (-4)) (.mul (.var 15) (.mul (.var 0) (.mul (.var 4) (.pow (.var 3) 4))))) (.add (.mul (.int (-4)) (.mul (.var 15) (.mul (.pow (.var 2) 2) (.mul (.pow (.var 3) 2) (.pow (.var 4) 2))))) (.add (.mul (.int (-2)) (.mul (.var 11) (.mul (.var 0) (.mul (.var 4) (.pow (.var 3) 3))))) (.add (.mul (.int (-2)) (.mul (.var 11) (.mul (.var 1) (.mul (.var 4) (.pow (.var 3) 2))))) (.add (.mul (.int (-2)) (.mul (.var 15) (.mul (.var 2) (.mul (.var 4) (.pow (.var 3) 2))))) (.add (.mul (.int 4) (.mul (.var 12) (.mul (.var 0) (.mul (.pow (.var 3) 4) (.pow (.var 4) 2))))) (.add (.mul (.int 4) (.mul (.var 16) (.mul (.var 0) (.mul (.var 4) (.pow (.var 3) 4))))) (.add (.mul (.int (-8)) (.mul (.var 12) (.mul (.var 0) (.mul (.pow (.var 2) 2) (.mul (.pow (.var 3) 3) (.pow (.var 4) 2)))))) (.add (.mul (.int (-4)) (.mul (.var 11) (.mul (.var 0) (.mul (.pow (.var 2) 3) (.mul (.pow (.var 3) 2) (.pow (.var 4) 2)))))) (.add (.mul (.int (-4)) (.mul (.var 11) (.mul (.var 1) (.mul (.var 2) (.mul (.pow (.var 3) 2) (.pow (.var 4) 2)))))) (.add (.mul (.int (-4)) (.mul (.var 12) (.mul (.var 0) (.mul (.var 2) (.mul (.var 4) (.pow (.var 3) 3)))))) (.add (.mul (.int (-4)) (.mul (.var 15) (.mul (.var 0) (.mul (.var 2) (.mul (.pow (.var 3) 4) (.pow (.var 4) 2)))))) (.add (.mul (.int (-2)) (.mul (.var 11) (.mul (.var 0) (.mul (.var 4) (.mul (.pow (.var 2) 2) (.pow (.var 3) 2)))))) (.add (.mul (.int 2) (.mul (.var 12) (.mul (.var 1) (.mul (.var 2) (.mul (.var 4) (.pow (.var 3) 2)))))) (.add (.mul (.int 4) (.mul (.var 11) (.mul (.var 1) (.mul (.var 3) (.mul (.var 4) (.pow (.var 2) 2)))))) (.add (.mul (.int 4) (.mul (.var 11) (.mul (.var 1) (.mul (.var 3) (.mul (.pow (.var 2) 3) (.pow (.var 4) 2)))))) (.mul (.int 4) (.mul (.var 12) (.mul (.var 1) (.mul (.pow (.var 2) 2) (.mul (.pow (.var 3) 2) (.pow (.var 4) 2)))))))))))))))))))))))))))))))))))
theorem dataCSz_5_8_binding : litCSzExpr 5 8=dataCSz_5_8 := rfl

def dataCSb_0_0 : RingExpr := (.int 1)
theorem dataCSb_0_0_binding : litCSbExpr 0 0=dataCSb_0_0 := rfl

def dataCSb_0_6 : RingExpr := (.int 1)
theorem dataCSb_0_6_binding : litCSbExpr 0 6=dataCSb_0_6 := rfl

def dataCSb_1_1 : RingExpr := (.int 1)
theorem dataCSb_1_1_binding : litCSbExpr 1 1=dataCSb_1_1 := rfl

def dataCSb_1_7 : RingExpr := (.int 1)
theorem dataCSb_1_7_binding : litCSbExpr 1 7=dataCSb_1_7 := rfl

def dataCSb_2_0 : RingExpr := (.mul (.var 7) (.mul (.var 9) (.mul (.pow (.var 10) 2) (.mul (.pow (.var 8) 3) (.add (.mul (.int 3) (.var 2)) (.add (.mul (.int (-12)) (.mul (.pow (.var 2) 3) (.pow (.var 4) 2))) (.add (.mul (.int (-6)) (.mul (.var 3) (.var 4))) (.add (.mul (.int (-2)) (.mul (.var 5) (.var 2))) (.add (.mul (.int 3) (.mul (.var 1) (.var 3))) (.add (.mul (.int (-12)) (.mul (.var 0) (.mul (.pow (.var 3) 3) (.pow (.var 4) 2)))) (.add (.mul (.int (-6)) (.mul (.var 4) (.mul (.pow (.var 1) 2) (.pow (.var 3) 2)))) (.add (.mul (.int (-4)) (.mul (.var 5) (.mul (.var 4) (.pow (.var 2) 2)))) (.add (.mul (.int (-2)) (.mul (.var 5) (.mul (.var 1) (.var 3)))) (.add (.mul (.int 4) (.mul (.var 5) (.mul (.var 3) (.var 4)))) (.add (.mul (.int 12) (.mul (.var 1) (.mul (.pow (.var 3) 2) (.pow (.var 4) 2)))) (.add (.mul (.int 12) (.mul (.var 2) (.mul (.var 3) (.pow (.var 4) 2)))) (.add (.mul (.int (-24)) (.mul (.var 1) (.mul (.var 3) (.mul (.pow (.var 2) 2) (.pow (.var 4) 2))))) (.add (.mul (.int (-12)) (.mul (.var 2) (.mul (.pow (.var 1) 2) (.mul (.pow (.var 3) 2) (.pow (.var 4) 2))))) (.add (.mul (.int (-6)) (.mul (.var 0) (.mul (.var 2) (.mul (.var 4) (.pow (.var 3) 2))))) (.add (.mul (.int (-6)) (.mul (.var 1) (.mul (.var 2) (.mul (.var 3) (.var 4))))) (.add (.mul (.int 12) (.mul (.var 0) (.mul (.pow (.var 2) 2) (.mul (.pow (.var 3) 2) (.pow (.var 4) 2))))) (.add (.mul (.int (-4)) (.mul (.var 5) (.mul (.var 1) (.mul (.var 2) (.mul (.var 3) (.var 4)))))) (.add (.mul (.int 4) (.mul (.var 5) (.mul (.var 0) (.mul (.var 2) (.mul (.var 4) (.pow (.var 3) 2)))))) (.mul (.int 12) (.mul (.var 0) (.mul (.var 1) (.mul (.var 2) (.mul (.pow (.var 3) 3) (.pow (.var 4) 2)))))))))))))))))))))))))))))
theorem dataCSb_2_0_binding : litCSbExpr 2 0=dataCSb_2_0 := rfl

def dataCSb_2_1 : RingExpr := (.mul (.var 7) (.mul (.var 10) (.mul (.var 8) (.add (.mul (.int 3) (.var 1)) (.add (.mul (.int (-2)) (.mul (.var 5) (.var 1))) (.add (.mul (.int (-6)) (.mul (.var 1) (.mul (.var 2) (.var 4)))) (.add (.mul (.int (-6)) (.mul (.var 3) (.mul (.var 4) (.pow (.var 1) 2)))) (.add (.mul (.int 2) (.mul (.var 5) (.mul (.var 0) (.var 3)))) (.mul (.int 6) (.mul (.var 0) (.mul (.var 1) (.mul (.var 4) (.pow (.var 3) 2)))))))))))))
theorem dataCSb_2_1_binding : litCSbExpr 2 1=dataCSb_2_1 := rfl

def dataCSb_2_2 : RingExpr := (.mul (.var 7) (.mul (.var 10) (.mul (.var 8) (.add (.int (-3)) (.add (.mul (.int 2) (.var 5)) (.add (.mul (.int 6) (.mul (.var 2) (.var 4))) (.add (.mul (.int (-6)) (.mul (.var 0) (.mul (.var 4) (.pow (.var 3) 2)))) (.mul (.int 6) (.mul (.var 1) (.mul (.var 3) (.var 4)))))))))))
theorem dataCSb_2_2_binding : litCSbExpr 2 2=dataCSb_2_2 := rfl

def dataCSb_2_6 : RingExpr := (.mul (.var 10) (.mul (.var 8) (.add (.mul (.int (-3)) (.var 2)) (.add (.mul (.int (-6)) (.mul (.var 4) (.pow (.var 2) 2))) (.add (.mul (.int (-3)) (.mul (.var 1) (.var 3))) (.add (.mul (.int (-6)) (.mul (.var 1) (.mul (.var 2) (.mul (.var 3) (.var 4))))) (.mul (.int 6) (.mul (.var 0) (.mul (.var 2) (.mul (.var 4) (.pow (.var 3) 2)))))))))))
theorem dataCSb_2_6_binding : litCSbExpr 2 6=dataCSb_2_6 := rfl

def dataCSb_2_7 : RingExpr := (.add (.mul (.int (3)) (.pow (.var 10) 1)) (.add (.mul (.int (-3)) (.mul (.var 2) (.var 4))) (.add (.mul (.int (-3)) (.mul (.var 1) (.mul (.var 3) (.var 4)))) (.mul (.int 3) (.mul (.var 0) (.mul (.var 4) (.pow (.var 3) 2)))))))
theorem dataCSb_2_7_binding : litCSbExpr 2 7=dataCSb_2_7 := rfl

def dataCSb_2_8 : RingExpr := (.mul (.var 7) (.mul (.var 9) (.mul (.pow (.var 10) 2) (.mul (.pow (.var 8) 3) (.add (.mul (.int (-3)) (.mul (.var 11) (.var 2))) (.add (.mul (.int (-3)) (.mul (.var 11) (.mul (.var 1) (.var 3)))) (.add (.mul (.int 2) (.mul (.var 11) (.mul (.var 5) (.var 2)))) (.add (.mul (.int 6) (.mul (.var 11) (.mul (.var 3) (.var 4)))) (.add (.mul (.int 6) (.mul (.var 15) (.mul (.var 4) (.pow (.var 3) 2)))) (.add (.mul (.int 12) (.mul (.var 11) (.mul (.pow (.var 2) 3) (.pow (.var 4) 2)))) (.add (.mul (.int (-12)) (.mul (.var 11) (.mul (.var 1) (.mul (.pow (.var 3) 2) (.pow (.var 4) 2))))) (.add (.mul (.int (-12)) (.mul (.var 11) (.mul (.var 2) (.mul (.var 3) (.pow (.var 4) 2))))) (.add (.mul (.int (-12)) (.mul (.var 15) (.mul (.var 1) (.mul (.pow (.var 3) 3) (.pow (.var 4) 2))))) (.add (.mul (.int (-12)) (.mul (.var 15) (.mul (.var 2) (.mul (.pow (.var 3) 2) (.pow (.var 4) 2))))) (.add (.mul (.int (-6)) (.mul (.var 12) (.mul (.var 1) (.mul (.var 4) (.pow (.var 3) 2))))) (.add (.mul (.int (-4)) (.mul (.var 11) (.mul (.var 5) (.mul (.var 3) (.var 4))))) (.add (.mul (.int (-4)) (.mul (.var 15) (.mul (.var 5) (.mul (.var 4) (.pow (.var 3) 2))))) (.add (.mul (.int 2) (.mul (.var 11) (.mul (.var 5) (.mul (.var 1) (.var 3))))) (.add (.mul (.int 4) (.mul (.var 11) (.mul (.var 5) (.mul (.var 4) (.pow (.var 2) 2))))) (.add (.mul (.int 4) (.mul (.var 13) (.mul (.var 0) (.mul (.var 4) (.pow (.var 3) 3))))) (.add (.mul (.int 6) (.mul (.var 11) (.mul (.var 4) (.mul (.pow (.var 1) 2) (.pow (.var 3) 2))))) (.add (.mul (.int 12) (.mul (.var 11) (.mul (.var 0) (.mul (.pow (.var 3) 3) (.pow (.var 4) 2))))) (.add (.mul (.int 12) (.mul (.var 12) (.mul (.pow (.var 1) 2) (.mul (.pow (.var 3) 3) (.pow (.var 4) 2))))) (.add (.mul (.int 12) (.mul (.var 15) (.mul (.var 0) (.mul (.pow (.var 3) 4) (.pow (.var 4) 2))))) (.add (.mul (.int (-12)) (.mul (.var 11) (.mul (.var 0) (.mul (.pow (.var 2) 2) (.mul (.pow (.var 3) 2) (.pow (.var 4) 2)))))) (.add (.mul (.int (-12)) (.mul (.var 12) (.mul (.var 0) (.mul (.var 1) (.mul (.pow (.var 3) 4) (.pow (.var 4) 2)))))) (.add (.mul (.int (-4)) (.mul (.var 12) (.mul (.var 5) (.mul (.var 0) (.mul (.var 4) (.pow (.var 3) 3)))))) (.add (.mul (.int 4) (.mul (.var 12) (.mul (.var 5) (.mul (.var 1) (.mul (.var 4) (.pow (.var 3) 2)))))) (.add (.mul (.int 6) (.mul (.var 11) (.mul (.var 0) (.mul (.var 2) (.mul (.var 4) (.pow (.var 3) 2)))))) (.add (.mul (.int 6) (.mul (.var 11) (.mul (.var 1) (.mul (.var 2) (.mul (.var 3) (.var 4)))))) (.add (.mul (.int 12) (.mul (.var 11) (.mul (.var 2) (.mul (.pow (.var 1) 2) (.mul (.pow (.var 3) 2) (.pow (.var 4) 2)))))) (.add (.mul (.int 12) (.mul (.var 12) (.mul (.var 1) (.mul (.var 2) (.mul (.pow (.var 3) 2) (.pow (.var 4) 2)))))) (.add (.mul (.int 24) (.mul (.var 11) (.mul (.var 1) (.mul (.var 3) (.mul (.pow (.var 2) 2) (.pow (.var 4) 2)))))) (.add (.mul (.int (-12)) (.mul (.var 11) (.mul (.var 0) (.mul (.var 1) (.mul (.var 2) (.mul (.pow (.var 3) 3) (.pow (.var 4) 2))))))) (.add (.mul (.int (-4)) (.mul (.var 11) (.mul (.var 5) (.mul (.var 0) (.mul (.var 2) (.mul (.var 4) (.pow (.var 3) 2))))))) (.mul (.int 4) (.mul (.var 11) (.mul (.var 5) (.mul (.var 1) (.mul (.var 2) (.mul (.var 3) (.var 4))))))))))))))))))))))))))))))))))))))))))
theorem dataCSb_2_8_binding : litCSbExpr 2 8=dataCSb_2_8 := rfl

def dataCSb_3_0 : RingExpr := (.mul (.var 7) (.mul (.var 9) (.mul (.pow (.var 10) 2) (.mul (.pow (.var 8) 3) (.add (.var 2) (.add (.mul (.var 1) (.var 3)) (.add (.mul (.int (-2)) (.mul (.var 3) (.var 4))) (.add (.mul (.int 4) (.mul (.var 4) (.pow (.var 2) 2))) (.add (.mul (.int 4) (.mul (.pow (.var 2) 3) (.pow (.var 4) 2))) (.add (.mul (.int (-4)) (.mul (.var 0) (.mul (.pow (.var 3) 3) (.pow (.var 4) 2)))) (.add (.mul (.int (-4)) (.mul (.var 2) (.mul (.var 3) (.pow (.var 4) 2)))) (.add (.mul (.int (-4)) (.mul (.var 0) (.mul (.pow (.var 2) 2) (.mul (.pow (.var 3) 2) (.pow (.var 4) 2))))) (.add (.mul (.int (-2)) (.mul (.var 0) (.mul (.var 2) (.mul (.var 4) (.pow (.var 3) 2))))) (.add (.mul (.int 4) (.mul (.var 1) (.mul (.var 2) (.mul (.var 3) (.var 4))))) (.mul (.int 4) (.mul (.var 1) (.mul (.var 3) (.mul (.pow (.var 2) 2) (.pow (.var 4) 2)))))))))))))))))))
theorem dataCSb_3_0_binding : litCSbExpr 3 0=dataCSb_3_0 := rfl

def dataCSb_3_1 : RingExpr := (.mul (.var 7) (.mul (.var 10) (.mul (.var 8) (.add (.var 1) (.add (.mul (.int 2) (.mul (.var 1) (.mul (.var 2) (.var 4)))) (.mul (.int (-4)) (.mul (.var 0) (.mul (.var 2) (.mul (.var 3) (.var 4))))))))))
theorem dataCSb_3_1_binding : litCSbExpr 3 1=dataCSb_3_1 := rfl

def dataCSb_3_2 : RingExpr := (.mul (.var 7) (.mul (.var 10) (.mul (.var 8) (.add (.int (-1)) (.add (.mul (.int (-2)) (.mul (.var 2) (.var 4))) (.mul (.int (-2)) (.mul (.var 0) (.mul (.var 4) (.pow (.var 3) 2)))))))))
theorem dataCSb_3_2_binding : litCSbExpr 3 2=dataCSb_3_2 := rfl

def dataCSb_3_6 : RingExpr := (.mul (.var 10) (.mul (.var 8) (.add (.mul (.int (-1)) (.var 2)) (.add (.mul (.int (-1)) (.mul (.var 1) (.var 3))) (.add (.mul (.int (-2)) (.mul (.var 4) (.pow (.var 2) 2))) (.add (.mul (.int (-2)) (.mul (.var 1) (.mul (.var 2) (.mul (.var 3) (.var 4))))) (.mul (.int 2) (.mul (.var 0) (.mul (.var 2) (.mul (.var 4) (.pow (.var 3) 2)))))))))))
theorem dataCSb_3_6_binding : litCSbExpr 3 6=dataCSb_3_6 := rfl

def dataCSb_3_7 : RingExpr := (.add (.mul (.int (1)) (.pow (.var 10) 1)) (.add (.mul (.int (-1)) (.mul (.var 2) (.var 4))) (.add (.mul (.var 0) (.mul (.var 4) (.pow (.var 3) 2))) (.mul (.int (-1)) (.mul (.var 1) (.mul (.var 3) (.var 4)))))))
theorem dataCSb_3_7_binding : litCSbExpr 3 7=dataCSb_3_7 := rfl

def dataCSb_3_8 : RingExpr := (.mul (.var 7) (.mul (.var 9) (.mul (.pow (.var 10) 2) (.mul (.pow (.var 8) 3) (.add (.mul (.int (-1)) (.mul (.var 11) (.var 2))) (.add (.mul (.int (-1)) (.mul (.var 11) (.mul (.var 1) (.var 3)))) (.add (.mul (.int (-4)) (.mul (.var 11) (.mul (.var 4) (.pow (.var 2) 2)))) (.add (.mul (.int (-4)) (.mul (.var 11) (.mul (.pow (.var 2) 3) (.pow (.var 4) 2)))) (.add (.mul (.int 2) (.mul (.var 11) (.mul (.var 3) (.var 4)))) (.add (.mul (.int 2) (.mul (.var 15) (.mul (.var 4) (.pow (.var 3) 2)))) (.add (.mul (.int (-2)) (.mul (.var 12) (.mul (.var 1) (.mul (.var 4) (.pow (.var 3) 2))))) (.add (.mul (.int 4) (.mul (.var 11) (.mul (.var 0) (.mul (.pow (.var 3) 3) (.pow (.var 4) 2))))) (.add (.mul (.int 4) (.mul (.var 11) (.mul (.var 2) (.mul (.var 3) (.pow (.var 4) 2))))) (.add (.mul (.int 4) (.mul (.var 14) (.mul (.var 0) (.mul (.var 4) (.pow (.var 3) 3))))) (.add (.mul (.int 4) (.mul (.var 15) (.mul (.var 0) (.mul (.pow (.var 3) 4) (.pow (.var 4) 2))))) (.add (.mul (.int 4) (.mul (.var 15) (.mul (.var 2) (.mul (.pow (.var 3) 2) (.pow (.var 4) 2))))) (.add (.mul (.int (-4)) (.mul (.var 11) (.mul (.var 1) (.mul (.var 2) (.mul (.var 3) (.var 4)))))) (.add (.mul (.int (-4)) (.mul (.var 11) (.mul (.var 1) (.mul (.var 3) (.mul (.pow (.var 2) 2) (.pow (.var 4) 2)))))) (.add (.mul (.int (-4)) (.mul (.var 12) (.mul (.var 1) (.mul (.var 2) (.mul (.pow (.var 3) 2) (.pow (.var 4) 2)))))) (.add (.mul (.int 2) (.mul (.var 11) (.mul (.var 0) (.mul (.var 2) (.mul (.var 4) (.pow (.var 3) 2)))))) (.add (.mul (.int 4) (.mul (.var 11) (.mul (.var 0) (.mul (.pow (.var 2) 2) (.mul (.pow (.var 3) 2) (.pow (.var 4) 2)))))) (.mul (.int 8) (.mul (.var 12) (.mul (.var 0) (.mul (.var 2) (.mul (.pow (.var 3) 3) (.pow (.var 4) 2)))))))))))))))))))))))))))
theorem dataCSb_3_8_binding : litCSbExpr 3 8=dataCSb_3_8 := rfl

def dataCSb_4_2 : RingExpr := (.int 1)
theorem dataCSb_4_2_binding : litCSbExpr 4 2=dataCSb_4_2 := rfl

def dataCSb_4_6 : RingExpr := (.mul (.var 10) (.mul (.var 9) (.mul (.pow (.var 8) 2) (.add (.var 2) (.add (.mul (.var 1) (.var 3)) (.add (.mul (.int (-2)) (.mul (.var 3) (.var 4))) (.add (.mul (.int 2) (.mul (.var 4) (.pow (.var 2) 2))) (.add (.mul (.int (-2)) (.mul (.var 0) (.mul (.var 2) (.mul (.var 4) (.pow (.var 3) 2))))) (.mul (.int 2) (.mul (.var 1) (.mul (.var 2) (.mul (.var 3) (.var 4)))))))))))))
theorem dataCSb_4_6_binding : litCSbExpr 4 6=dataCSb_4_6 := rfl

def dataCSb_4_7 : RingExpr := (.add (.var 1) (.mul (.int (-1)) (.mul (.var 0) (.var 3))))
theorem dataCSb_4_7_binding : litCSbExpr 4 7=dataCSb_4_7 := rfl

def dataCSb_5_0 : RingExpr := (.mul (.var 7) (.mul (.var 9) (.mul (.pow (.var 10) 2) (.mul (.pow (.var 8) 4) (.add (.mul (.int (-1)) (.pow (.var 2) 2)) (.add (.mul (.int (-4)) (.mul (.var 4) (.pow (.var 2) 3))) (.add (.mul (.int (-4)) (.mul (.pow (.var 2) 4) (.pow (.var 4) 2))) (.add (.mul (.int (-4)) (.mul (.pow (.var 3) 2) (.pow (.var 4) 2))) (.add (.mul (.int (-1)) (.mul (.var 1) (.mul (.var 2) (.var 3)))) (.add (.mul (.int 2) (.mul (.var 0) (.mul (.var 4) (.pow (.var 3) 3)))) (.add (.mul (.int 2) (.mul (.var 1) (.mul (.var 4) (.pow (.var 3) 2)))) (.add (.mul (.int 4) (.mul (.var 2) (.mul (.var 3) (.var 4)))) (.add (.mul (.int 8) (.mul (.var 3) (.mul (.pow (.var 2) 2) (.pow (.var 4) 2)))) (.add (.mul (.int (-4)) (.mul (.var 1) (.mul (.var 3) (.mul (.var 4) (.pow (.var 2) 2))))) (.add (.mul (.int (-4)) (.mul (.var 1) (.mul (.var 3) (.mul (.pow (.var 2) 3) (.pow (.var 4) 2))))) (.add (.mul (.int 2) (.mul (.var 0) (.mul (.var 4) (.mul (.pow (.var 2) 2) (.pow (.var 3) 2))))) (.add (.mul (.int 4) (.mul (.var 0) (.mul (.pow (.var 2) 3) (.mul (.pow (.var 3) 2) (.pow (.var 4) 2))))) (.mul (.int 4) (.mul (.var 1) (.mul (.var 2) (.mul (.pow (.var 3) 2) (.pow (.var 4) 2))))))))))))))))))))))
theorem dataCSb_5_0_binding : litCSbExpr 5 0=dataCSb_5_0 := rfl

def dataCSb_5_1 : RingExpr := (.mul (.var 7) (.mul (.var 10) (.mul (.pow (.var 8) 2) (.add (.mul (.int (-1)) (.mul (.var 1) (.var 2))) (.add (.mul (.int (-2)) (.mul (.var 0) (.mul (.var 4) (.pow (.var 3) 2)))) (.add (.mul (.int (-2)) (.mul (.var 1) (.mul (.var 4) (.pow (.var 2) 2)))) (.add (.mul (.int 2) (.mul (.var 0) (.mul (.var 2) (.var 3)))) (.add (.mul (.int 2) (.mul (.var 1) (.mul (.var 3) (.var 4)))) (.mul (.int 4) (.mul (.var 0) (.mul (.var 3) (.mul (.var 4) (.pow (.var 2) 2)))))))))))))
theorem dataCSb_5_1_binding : litCSbExpr 5 1=dataCSb_5_1 := rfl

def dataCSb_5_2 : RingExpr := (.mul (.var 7) (.mul (.var 10) (.mul (.pow (.var 8) 2) (.add (.var 2) (.add (.mul (.int (-2)) (.mul (.var 3) (.var 4))) (.add (.mul (.int 2) (.mul (.var 0) (.pow (.var 3) 2))) (.add (.mul (.int 2) (.mul (.var 4) (.pow (.var 2) 2))) (.mul (.int 2) (.mul (.var 0) (.mul (.var 2) (.mul (.var 4) (.pow (.var 3) 2))))))))))))
theorem dataCSb_5_2_binding : litCSbExpr 5 2=dataCSb_5_2 := rfl

def dataCSb_5_6 : RingExpr := (.mul (.var 10) (.mul (.var 9) (.mul (.pow (.var 8) 2) (.add (.var 2) (.add (.mul (.var 1) (.var 3)) (.add (.mul (.int (-1)) (.mul (.var 3) (.var 4))) (.add (.mul (.int 2) (.mul (.pow (.var 2) 3) (.pow (.var 4) 2))) (.add (.mul (.int 3) (.mul (.var 4) (.pow (.var 2) 2))) (.add (.mul (.int (-2)) (.mul (.var 0) (.mul (.var 2) (.mul (.var 4) (.pow (.var 3) 2))))) (.add (.mul (.int (-2)) (.mul (.var 0) (.mul (.pow (.var 2) 2) (.mul (.pow (.var 3) 2) (.pow (.var 4) 2))))) (.add (.mul (.int 2) (.mul (.var 1) (.mul (.var 3) (.mul (.pow (.var 2) 2) (.pow (.var 4) 2))))) (.mul (.int 3) (.mul (.var 1) (.mul (.var 2) (.mul (.var 3) (.var 4))))))))))))))))
theorem dataCSb_5_6_binding : litCSbExpr 5 6=dataCSb_5_6 := rfl

def dataCSb_5_7 : RingExpr := (.mul (.var 10) (.mul (.var 8) (.add (.var 2) (.add (.mul (.int (-2)) (.mul (.var 0) (.pow (.var 3) 2))) (.add (.mul (.int 2) (.mul (.var 1) (.var 3))) (.add (.mul (.int 2) (.mul (.var 4) (.pow (.var 2) 2))) (.add (.mul (.int (-2)) (.mul (.var 0) (.mul (.var 2) (.mul (.var 4) (.pow (.var 3) 2))))) (.mul (.int 2) (.mul (.var 1) (.mul (.var 2) (.mul (.var 3) (.var 4))))))))))))
theorem dataCSb_5_7_binding : litCSbExpr 5 7=dataCSb_5_7 := rfl

def dataCSb_5_8 : RingExpr := (.mul (.var 7) (.mul (.var 9) (.mul (.pow (.var 10) 2) (.mul (.pow (.var 8) 4) (.add (.mul (.var 11) (.pow (.var 2) 2)) (.add (.mul (.int 4) (.mul (.var 11) (.mul (.var 4) (.pow (.var 2) 3)))) (.add (.mul (.int 4) (.mul (.var 11) (.mul (.pow (.var 2) 4) (.pow (.var 4) 2)))) (.add (.mul (.int 4) (.mul (.var 11) (.mul (.pow (.var 3) 2) (.pow (.var 4) 2)))) (.add (.mul (.int 4) (.mul (.var 15) (.mul (.pow (.var 3) 3) (.pow (.var 4) 2)))) (.add (.mul (.var 11) (.mul (.var 1) (.mul (.var 2) (.var 3)))) (.add (.mul (.int (-8)) (.mul (.var 11) (.mul (.var 3) (.mul (.pow (.var 2) 2) (.pow (.var 4) 2))))) (.add (.mul (.int (-4)) (.mul (.var 11) (.mul (.var 2) (.mul (.var 3) (.var 4))))) (.add (.mul (.int (-4)) (.mul (.var 12) (.mul (.var 1) (.mul (.pow (.var 3) 3) (.pow (.var 4) 2))))) (.add (.mul (.int (-4)) (.mul (.var 15) (.mul (.var 0) (.mul (.var 4) (.pow (.var 3) 4))))) (.add (.mul (.int (-4)) (.mul (.var 15) (.mul (.pow (.var 2) 2) (.mul (.pow (.var 3) 2) (.pow (.var 4) 2))))) (.add (.mul (.int (-2)) (.mul (.var 11) (.mul (.var 0) (.mul (.var 4) (.pow (.var 3) 3))))) (.add (.mul (.int (-2)) (.mul (.var 11) (.mul (.var 1) (.mul (.var 4) (.pow (.var 3) 2))))) (.add (.mul (.int (-2)) (.mul (.var 15) (.mul (.var 2) (.mul (.var 4) (.pow (.var 3) 2))))) (.add (.mul (.int 4) (.mul (.var 12) (.mul (.var 0) (.mul (.pow (.var 3) 4) (.pow (.var 4) 2))))) (.add (.mul (.int 4) (.mul (.var 16) (.mul (.var 0) (.mul (.var 4) (.pow (.var 3) 4))))) (.add (.mul (.int (-8)) (.mul (.var 12) (.mul (.var 0) (.mul (.pow (.var 2) 2) (.mul (.pow (.var 3) 3) (.pow (.var 4) 2)))))) (.add (.mul (.int (-4)) (.mul (.var 11) (.mul (.var 0) (.mul (.pow (.var 2) 3) (.mul (.pow (.var 3) 2) (.pow (.var 4) 2)))))) (.add (.mul (.int (-4)) (.mul (.var 11) (.mul (.var 1) (.mul (.var 2) (.mul (.pow (.var 3) 2) (.pow (.var 4) 2)))))) (.add (.mul (.int (-4)) (.mul (.var 12) (.mul (.var 0) (.mul (.var 2) (.mul (.var 4) (.pow (.var 3) 3)))))) (.add (.mul (.int (-4)) (.mul (.var 15) (.mul (.var 0) (.mul (.var 2) (.mul (.pow (.var 3) 4) (.pow (.var 4) 2)))))) (.add (.mul (.int (-2)) (.mul (.var 11) (.mul (.var 0) (.mul (.var 4) (.mul (.pow (.var 2) 2) (.pow (.var 3) 2)))))) (.add (.mul (.int 2) (.mul (.var 12) (.mul (.var 1) (.mul (.var 2) (.mul (.var 4) (.pow (.var 3) 2)))))) (.add (.mul (.int 4) (.mul (.var 11) (.mul (.var 1) (.mul (.var 3) (.mul (.var 4) (.pow (.var 2) 2)))))) (.add (.mul (.int 4) (.mul (.var 11) (.mul (.var 1) (.mul (.var 3) (.mul (.pow (.var 2) 3) (.pow (.var 4) 2)))))) (.mul (.int 4) (.mul (.var 12) (.mul (.var 1) (.mul (.pow (.var 2) 2) (.mul (.pow (.var 3) 2) (.pow (.var 4) 2)))))))))))))))))))))))))))))))))))
theorem dataCSb_5_8_binding : litCSbExpr 5 8=dataCSb_5_8 := rfl

def dataCSt_0_0 : RingExpr := (.int 1)
theorem dataCSt_0_0_binding : litCStExpr 0 0=dataCSt_0_0 := rfl

def dataCSt_0_6 : RingExpr := (.int 1)
theorem dataCSt_0_6_binding : litCStExpr 0 6=dataCSt_0_6 := rfl

def dataCSt_1_1 : RingExpr := (.int 1)
theorem dataCSt_1_1_binding : litCStExpr 1 1=dataCSt_1_1 := rfl

def dataCSt_1_7 : RingExpr := (.int 1)
theorem dataCSt_1_7_binding : litCStExpr 1 7=dataCSt_1_7 := rfl

def dataCSt_2_0 : RingExpr := (.mul (.var 7) (.mul (.var 9) (.mul (.pow (.var 10) 2) (.mul (.pow (.var 8) 3) (.add (.mul (.int 3) (.var 2)) (.add (.mul (.int (-12)) (.mul (.pow (.var 2) 3) (.pow (.var 4) 2))) (.add (.mul (.int (-6)) (.mul (.var 3) (.var 4))) (.add (.mul (.int (-2)) (.mul (.var 5) (.var 2))) (.add (.mul (.int 3) (.mul (.var 1) (.var 3))) (.add (.mul (.int (-12)) (.mul (.var 0) (.mul (.pow (.var 3) 3) (.pow (.var 4) 2)))) (.add (.mul (.int (-6)) (.mul (.var 4) (.mul (.pow (.var 1) 2) (.pow (.var 3) 2)))) (.add (.mul (.int (-4)) (.mul (.var 5) (.mul (.var 4) (.pow (.var 2) 2)))) (.add (.mul (.int (-2)) (.mul (.var 5) (.mul (.var 1) (.var 3)))) (.add (.mul (.int 4) (.mul (.var 5) (.mul (.var 3) (.var 4)))) (.add (.mul (.int 12) (.mul (.var 1) (.mul (.pow (.var 3) 2) (.pow (.var 4) 2)))) (.add (.mul (.int 12) (.mul (.var 2) (.mul (.var 3) (.pow (.var 4) 2)))) (.add (.mul (.int (-24)) (.mul (.var 1) (.mul (.var 3) (.mul (.pow (.var 2) 2) (.pow (.var 4) 2))))) (.add (.mul (.int (-12)) (.mul (.var 2) (.mul (.pow (.var 1) 2) (.mul (.pow (.var 3) 2) (.pow (.var 4) 2))))) (.add (.mul (.int (-6)) (.mul (.var 0) (.mul (.var 2) (.mul (.var 4) (.pow (.var 3) 2))))) (.add (.mul (.int (-6)) (.mul (.var 1) (.mul (.var 2) (.mul (.var 3) (.var 4))))) (.add (.mul (.int 12) (.mul (.var 0) (.mul (.pow (.var 2) 2) (.mul (.pow (.var 3) 2) (.pow (.var 4) 2))))) (.add (.mul (.int (-4)) (.mul (.var 5) (.mul (.var 1) (.mul (.var 2) (.mul (.var 3) (.var 4)))))) (.add (.mul (.int 4) (.mul (.var 5) (.mul (.var 0) (.mul (.var 2) (.mul (.var 4) (.pow (.var 3) 2)))))) (.mul (.int 12) (.mul (.var 0) (.mul (.var 1) (.mul (.var 2) (.mul (.pow (.var 3) 3) (.pow (.var 4) 2)))))))))))))))))))))))))))))
theorem dataCSt_2_0_binding : litCStExpr 2 0=dataCSt_2_0 := rfl

def dataCSt_2_1 : RingExpr := (.mul (.var 7) (.mul (.var 10) (.mul (.var 8) (.add (.mul (.int 3) (.var 1)) (.add (.mul (.int (-2)) (.mul (.var 5) (.var 1))) (.add (.mul (.int (-6)) (.mul (.var 1) (.mul (.var 2) (.var 4)))) (.add (.mul (.int (-6)) (.mul (.var 3) (.mul (.var 4) (.pow (.var 1) 2)))) (.add (.mul (.int 2) (.mul (.var 5) (.mul (.var 0) (.var 3)))) (.mul (.int 6) (.mul (.var 0) (.mul (.var 1) (.mul (.var 4) (.pow (.var 3) 2)))))))))))))
theorem dataCSt_2_1_binding : litCStExpr 2 1=dataCSt_2_1 := rfl

def dataCSt_2_2 : RingExpr := (.mul (.var 7) (.mul (.var 10) (.mul (.var 8) (.add (.int (-3)) (.add (.mul (.int 2) (.var 5)) (.add (.mul (.int 6) (.mul (.var 2) (.var 4))) (.add (.mul (.int (-6)) (.mul (.var 0) (.mul (.var 4) (.pow (.var 3) 2)))) (.mul (.int 6) (.mul (.var 1) (.mul (.var 3) (.var 4)))))))))))
theorem dataCSt_2_2_binding : litCStExpr 2 2=dataCSt_2_2 := rfl

def dataCSt_2_6 : RingExpr := (.mul (.var 10) (.mul (.var 8) (.add (.mul (.int (-3)) (.var 2)) (.add (.mul (.int (-6)) (.mul (.var 4) (.pow (.var 2) 2))) (.add (.mul (.int (-3)) (.mul (.var 1) (.var 3))) (.add (.mul (.int (-6)) (.mul (.var 1) (.mul (.var 2) (.mul (.var 3) (.var 4))))) (.mul (.int 6) (.mul (.var 0) (.mul (.var 2) (.mul (.var 4) (.pow (.var 3) 2)))))))))))
theorem dataCSt_2_6_binding : litCStExpr 2 6=dataCSt_2_6 := rfl

def dataCSt_2_7 : RingExpr := (.add (.mul (.int (3)) (.pow (.var 10) 1)) (.add (.mul (.int (-3)) (.mul (.var 2) (.var 4))) (.add (.mul (.int (-3)) (.mul (.var 1) (.mul (.var 3) (.var 4)))) (.mul (.int 3) (.mul (.var 0) (.mul (.var 4) (.pow (.var 3) 2)))))))
theorem dataCSt_2_7_binding : litCStExpr 2 7=dataCSt_2_7 := rfl

def dataCSt_2_8 : RingExpr := (.mul (.var 7) (.mul (.var 9) (.mul (.pow (.var 10) 2) (.mul (.pow (.var 8) 3) (.add (.mul (.int (-3)) (.mul (.var 11) (.var 2))) (.add (.mul (.int (-3)) (.mul (.var 11) (.mul (.var 1) (.var 3)))) (.add (.mul (.int 2) (.mul (.var 11) (.mul (.var 5) (.var 2)))) (.add (.mul (.int 6) (.mul (.var 11) (.mul (.var 3) (.var 4)))) (.add (.mul (.int 6) (.mul (.var 15) (.mul (.var 4) (.pow (.var 3) 2)))) (.add (.mul (.int 12) (.mul (.var 11) (.mul (.pow (.var 2) 3) (.pow (.var 4) 2)))) (.add (.mul (.int (-12)) (.mul (.var 11) (.mul (.var 1) (.mul (.pow (.var 3) 2) (.pow (.var 4) 2))))) (.add (.mul (.int (-12)) (.mul (.var 11) (.mul (.var 2) (.mul (.var 3) (.pow (.var 4) 2))))) (.add (.mul (.int (-12)) (.mul (.var 15) (.mul (.var 1) (.mul (.pow (.var 3) 3) (.pow (.var 4) 2))))) (.add (.mul (.int (-12)) (.mul (.var 15) (.mul (.var 2) (.mul (.pow (.var 3) 2) (.pow (.var 4) 2))))) (.add (.mul (.int (-6)) (.mul (.var 12) (.mul (.var 1) (.mul (.var 4) (.pow (.var 3) 2))))) (.add (.mul (.int (-4)) (.mul (.var 11) (.mul (.var 5) (.mul (.var 3) (.var 4))))) (.add (.mul (.int (-4)) (.mul (.var 15) (.mul (.var 5) (.mul (.var 4) (.pow (.var 3) 2))))) (.add (.mul (.int 2) (.mul (.var 11) (.mul (.var 5) (.mul (.var 1) (.var 3))))) (.add (.mul (.int 4) (.mul (.var 11) (.mul (.var 5) (.mul (.var 4) (.pow (.var 2) 2))))) (.add (.mul (.int 4) (.mul (.var 13) (.mul (.var 0) (.mul (.var 4) (.pow (.var 3) 3))))) (.add (.mul (.int 6) (.mul (.var 11) (.mul (.var 4) (.mul (.pow (.var 1) 2) (.pow (.var 3) 2))))) (.add (.mul (.int 12) (.mul (.var 11) (.mul (.var 0) (.mul (.pow (.var 3) 3) (.pow (.var 4) 2))))) (.add (.mul (.int 12) (.mul (.var 12) (.mul (.pow (.var 1) 2) (.mul (.pow (.var 3) 3) (.pow (.var 4) 2))))) (.add (.mul (.int 12) (.mul (.var 15) (.mul (.var 0) (.mul (.pow (.var 3) 4) (.pow (.var 4) 2))))) (.add (.mul (.int (-12)) (.mul (.var 11) (.mul (.var 0) (.mul (.pow (.var 2) 2) (.mul (.pow (.var 3) 2) (.pow (.var 4) 2)))))) (.add (.mul (.int (-12)) (.mul (.var 12) (.mul (.var 0) (.mul (.var 1) (.mul (.pow (.var 3) 4) (.pow (.var 4) 2)))))) (.add (.mul (.int (-4)) (.mul (.var 12) (.mul (.var 5) (.mul (.var 0) (.mul (.var 4) (.pow (.var 3) 3)))))) (.add (.mul (.int 4) (.mul (.var 12) (.mul (.var 5) (.mul (.var 1) (.mul (.var 4) (.pow (.var 3) 2)))))) (.add (.mul (.int 6) (.mul (.var 11) (.mul (.var 0) (.mul (.var 2) (.mul (.var 4) (.pow (.var 3) 2)))))) (.add (.mul (.int 6) (.mul (.var 11) (.mul (.var 1) (.mul (.var 2) (.mul (.var 3) (.var 4)))))) (.add (.mul (.int 12) (.mul (.var 11) (.mul (.var 2) (.mul (.pow (.var 1) 2) (.mul (.pow (.var 3) 2) (.pow (.var 4) 2)))))) (.add (.mul (.int 12) (.mul (.var 12) (.mul (.var 1) (.mul (.var 2) (.mul (.pow (.var 3) 2) (.pow (.var 4) 2)))))) (.add (.mul (.int 24) (.mul (.var 11) (.mul (.var 1) (.mul (.var 3) (.mul (.pow (.var 2) 2) (.pow (.var 4) 2)))))) (.add (.mul (.int (-12)) (.mul (.var 11) (.mul (.var 0) (.mul (.var 1) (.mul (.var 2) (.mul (.pow (.var 3) 3) (.pow (.var 4) 2))))))) (.add (.mul (.int (-4)) (.mul (.var 11) (.mul (.var 5) (.mul (.var 0) (.mul (.var 2) (.mul (.var 4) (.pow (.var 3) 2))))))) (.mul (.int 4) (.mul (.var 11) (.mul (.var 5) (.mul (.var 1) (.mul (.var 2) (.mul (.var 3) (.var 4))))))))))))))))))))))))))))))))))))))))))
theorem dataCSt_2_8_binding : litCStExpr 2 8=dataCSt_2_8 := rfl

def dataCSt_3_0 : RingExpr := (.mul (.var 7) (.mul (.var 9) (.mul (.pow (.var 10) 2) (.mul (.pow (.var 8) 3) (.add (.var 2) (.add (.mul (.var 1) (.var 3)) (.add (.mul (.int (-2)) (.mul (.var 3) (.var 4))) (.add (.mul (.int 4) (.mul (.var 4) (.pow (.var 2) 2))) (.add (.mul (.int 4) (.mul (.pow (.var 2) 3) (.pow (.var 4) 2))) (.add (.mul (.int (-4)) (.mul (.var 0) (.mul (.pow (.var 3) 3) (.pow (.var 4) 2)))) (.add (.mul (.int (-4)) (.mul (.var 2) (.mul (.var 3) (.pow (.var 4) 2)))) (.add (.mul (.int (-4)) (.mul (.var 0) (.mul (.pow (.var 2) 2) (.mul (.pow (.var 3) 2) (.pow (.var 4) 2))))) (.add (.mul (.int (-2)) (.mul (.var 0) (.mul (.var 2) (.mul (.var 4) (.pow (.var 3) 2))))) (.add (.mul (.int 4) (.mul (.var 1) (.mul (.var 2) (.mul (.var 3) (.var 4))))) (.mul (.int 4) (.mul (.var 1) (.mul (.var 3) (.mul (.pow (.var 2) 2) (.pow (.var 4) 2)))))))))))))))))))
theorem dataCSt_3_0_binding : litCStExpr 3 0=dataCSt_3_0 := rfl

def dataCSt_3_1 : RingExpr := (.mul (.var 7) (.mul (.var 10) (.mul (.var 8) (.add (.var 1) (.add (.mul (.int 2) (.mul (.var 1) (.mul (.var 2) (.var 4)))) (.mul (.int (-4)) (.mul (.var 0) (.mul (.var 2) (.mul (.var 3) (.var 4))))))))))
theorem dataCSt_3_1_binding : litCStExpr 3 1=dataCSt_3_1 := rfl

def dataCSt_3_2 : RingExpr := (.mul (.var 7) (.mul (.var 10) (.mul (.var 8) (.add (.int (-1)) (.add (.mul (.int (-2)) (.mul (.var 2) (.var 4))) (.mul (.int (-2)) (.mul (.var 0) (.mul (.var 4) (.pow (.var 3) 2)))))))))
theorem dataCSt_3_2_binding : litCStExpr 3 2=dataCSt_3_2 := rfl

def dataCSt_3_6 : RingExpr := (.mul (.var 10) (.mul (.var 8) (.add (.mul (.int (-1)) (.var 2)) (.add (.mul (.int (-1)) (.mul (.var 1) (.var 3))) (.add (.mul (.int (-2)) (.mul (.var 4) (.pow (.var 2) 2))) (.add (.mul (.int (-2)) (.mul (.var 1) (.mul (.var 2) (.mul (.var 3) (.var 4))))) (.mul (.int 2) (.mul (.var 0) (.mul (.var 2) (.mul (.var 4) (.pow (.var 3) 2)))))))))))
theorem dataCSt_3_6_binding : litCStExpr 3 6=dataCSt_3_6 := rfl

def dataCSt_3_7 : RingExpr := (.add (.mul (.int (1)) (.pow (.var 10) 1)) (.add (.mul (.int (-1)) (.mul (.var 2) (.var 4))) (.add (.mul (.var 0) (.mul (.var 4) (.pow (.var 3) 2))) (.mul (.int (-1)) (.mul (.var 1) (.mul (.var 3) (.var 4)))))))
theorem dataCSt_3_7_binding : litCStExpr 3 7=dataCSt_3_7 := rfl

def dataCSt_3_8 : RingExpr := (.mul (.var 7) (.mul (.var 9) (.mul (.pow (.var 10) 2) (.mul (.pow (.var 8) 3) (.add (.mul (.int (-1)) (.mul (.var 11) (.var 2))) (.add (.mul (.int (-1)) (.mul (.var 11) (.mul (.var 1) (.var 3)))) (.add (.mul (.int (-4)) (.mul (.var 11) (.mul (.var 4) (.pow (.var 2) 2)))) (.add (.mul (.int (-4)) (.mul (.var 11) (.mul (.pow (.var 2) 3) (.pow (.var 4) 2)))) (.add (.mul (.int 2) (.mul (.var 11) (.mul (.var 3) (.var 4)))) (.add (.mul (.int 2) (.mul (.var 15) (.mul (.var 4) (.pow (.var 3) 2)))) (.add (.mul (.int (-2)) (.mul (.var 12) (.mul (.var 1) (.mul (.var 4) (.pow (.var 3) 2))))) (.add (.mul (.int 4) (.mul (.var 11) (.mul (.var 0) (.mul (.pow (.var 3) 3) (.pow (.var 4) 2))))) (.add (.mul (.int 4) (.mul (.var 11) (.mul (.var 2) (.mul (.var 3) (.pow (.var 4) 2))))) (.add (.mul (.int 4) (.mul (.var 14) (.mul (.var 0) (.mul (.var 4) (.pow (.var 3) 3))))) (.add (.mul (.int 4) (.mul (.var 15) (.mul (.var 0) (.mul (.pow (.var 3) 4) (.pow (.var 4) 2))))) (.add (.mul (.int 4) (.mul (.var 15) (.mul (.var 2) (.mul (.pow (.var 3) 2) (.pow (.var 4) 2))))) (.add (.mul (.int (-4)) (.mul (.var 11) (.mul (.var 1) (.mul (.var 2) (.mul (.var 3) (.var 4)))))) (.add (.mul (.int (-4)) (.mul (.var 11) (.mul (.var 1) (.mul (.var 3) (.mul (.pow (.var 2) 2) (.pow (.var 4) 2)))))) (.add (.mul (.int (-4)) (.mul (.var 12) (.mul (.var 1) (.mul (.var 2) (.mul (.pow (.var 3) 2) (.pow (.var 4) 2)))))) (.add (.mul (.int 2) (.mul (.var 11) (.mul (.var 0) (.mul (.var 2) (.mul (.var 4) (.pow (.var 3) 2)))))) (.add (.mul (.int 4) (.mul (.var 11) (.mul (.var 0) (.mul (.pow (.var 2) 2) (.mul (.pow (.var 3) 2) (.pow (.var 4) 2)))))) (.mul (.int 8) (.mul (.var 12) (.mul (.var 0) (.mul (.var 2) (.mul (.pow (.var 3) 3) (.pow (.var 4) 2)))))))))))))))))))))))))))
theorem dataCSt_3_8_binding : litCStExpr 3 8=dataCSt_3_8 := rfl

def dataCSt_4_2 : RingExpr := (.int 1)
theorem dataCSt_4_2_binding : litCStExpr 4 2=dataCSt_4_2 := rfl

def dataCSt_4_6 : RingExpr := (.mul (.var 10) (.mul (.var 9) (.mul (.pow (.var 8) 2) (.add (.var 2) (.add (.mul (.var 1) (.var 3)) (.add (.mul (.int (-2)) (.mul (.var 3) (.var 4))) (.add (.mul (.int 2) (.mul (.var 4) (.pow (.var 2) 2))) (.add (.mul (.int (-2)) (.mul (.var 0) (.mul (.var 2) (.mul (.var 4) (.pow (.var 3) 2))))) (.mul (.int 2) (.mul (.var 1) (.mul (.var 2) (.mul (.var 3) (.var 4)))))))))))))
theorem dataCSt_4_6_binding : litCStExpr 4 6=dataCSt_4_6 := rfl

def dataCSt_4_7 : RingExpr := (.add (.var 1) (.mul (.int (-1)) (.mul (.var 0) (.var 3))))
theorem dataCSt_4_7_binding : litCStExpr 4 7=dataCSt_4_7 := rfl

def dataCSt_5_0 : RingExpr := (.mul (.var 7) (.mul (.var 9) (.mul (.pow (.var 10) 2) (.mul (.pow (.var 8) 4) (.add (.mul (.int (-1)) (.pow (.var 2) 2)) (.add (.mul (.int (-4)) (.mul (.var 4) (.pow (.var 2) 3))) (.add (.mul (.int (-4)) (.mul (.pow (.var 2) 4) (.pow (.var 4) 2))) (.add (.mul (.int (-4)) (.mul (.pow (.var 3) 2) (.pow (.var 4) 2))) (.add (.mul (.int (-1)) (.mul (.var 1) (.mul (.var 2) (.var 3)))) (.add (.mul (.int 2) (.mul (.var 0) (.mul (.var 4) (.pow (.var 3) 3)))) (.add (.mul (.int 2) (.mul (.var 1) (.mul (.var 4) (.pow (.var 3) 2)))) (.add (.mul (.int 4) (.mul (.var 2) (.mul (.var 3) (.var 4)))) (.add (.mul (.int 8) (.mul (.var 3) (.mul (.pow (.var 2) 2) (.pow (.var 4) 2)))) (.add (.mul (.int (-4)) (.mul (.var 1) (.mul (.var 3) (.mul (.var 4) (.pow (.var 2) 2))))) (.add (.mul (.int (-4)) (.mul (.var 1) (.mul (.var 3) (.mul (.pow (.var 2) 3) (.pow (.var 4) 2))))) (.add (.mul (.int 2) (.mul (.var 0) (.mul (.var 4) (.mul (.pow (.var 2) 2) (.pow (.var 3) 2))))) (.add (.mul (.int 4) (.mul (.var 0) (.mul (.pow (.var 2) 3) (.mul (.pow (.var 3) 2) (.pow (.var 4) 2))))) (.mul (.int 4) (.mul (.var 1) (.mul (.var 2) (.mul (.pow (.var 3) 2) (.pow (.var 4) 2))))))))))))))))))))))
theorem dataCSt_5_0_binding : litCStExpr 5 0=dataCSt_5_0 := rfl

def dataCSt_5_1 : RingExpr := (.mul (.var 7) (.mul (.var 10) (.mul (.pow (.var 8) 2) (.add (.mul (.int (-1)) (.mul (.var 1) (.var 2))) (.add (.mul (.int (-2)) (.mul (.var 0) (.mul (.var 4) (.pow (.var 3) 2)))) (.add (.mul (.int (-2)) (.mul (.var 1) (.mul (.var 4) (.pow (.var 2) 2)))) (.add (.mul (.int 2) (.mul (.var 0) (.mul (.var 2) (.var 3)))) (.add (.mul (.int 2) (.mul (.var 1) (.mul (.var 3) (.var 4)))) (.mul (.int 4) (.mul (.var 0) (.mul (.var 3) (.mul (.var 4) (.pow (.var 2) 2)))))))))))))
theorem dataCSt_5_1_binding : litCStExpr 5 1=dataCSt_5_1 := rfl

def dataCSt_5_2 : RingExpr := (.mul (.var 7) (.mul (.var 10) (.mul (.pow (.var 8) 2) (.add (.var 2) (.add (.mul (.int (-2)) (.mul (.var 3) (.var 4))) (.add (.mul (.int 2) (.mul (.var 0) (.pow (.var 3) 2))) (.add (.mul (.int 2) (.mul (.var 4) (.pow (.var 2) 2))) (.mul (.int 2) (.mul (.var 0) (.mul (.var 2) (.mul (.var 4) (.pow (.var 3) 2))))))))))))
theorem dataCSt_5_2_binding : litCStExpr 5 2=dataCSt_5_2 := rfl

def dataCSt_5_6 : RingExpr := (.mul (.var 10) (.mul (.var 9) (.mul (.pow (.var 8) 2) (.add (.var 2) (.add (.mul (.var 1) (.var 3)) (.add (.mul (.int (-1)) (.mul (.var 3) (.var 4))) (.add (.mul (.int 2) (.mul (.pow (.var 2) 3) (.pow (.var 4) 2))) (.add (.mul (.int 3) (.mul (.var 4) (.pow (.var 2) 2))) (.add (.mul (.int (-2)) (.mul (.var 0) (.mul (.var 2) (.mul (.var 4) (.pow (.var 3) 2))))) (.add (.mul (.int (-2)) (.mul (.var 0) (.mul (.pow (.var 2) 2) (.mul (.pow (.var 3) 2) (.pow (.var 4) 2))))) (.add (.mul (.int 2) (.mul (.var 1) (.mul (.var 3) (.mul (.pow (.var 2) 2) (.pow (.var 4) 2))))) (.mul (.int 3) (.mul (.var 1) (.mul (.var 2) (.mul (.var 3) (.var 4))))))))))))))))
theorem dataCSt_5_6_binding : litCStExpr 5 6=dataCSt_5_6 := rfl

def dataCSt_5_7 : RingExpr := (.mul (.var 10) (.mul (.var 8) (.add (.var 2) (.add (.mul (.int (-2)) (.mul (.var 0) (.pow (.var 3) 2))) (.add (.mul (.int 2) (.mul (.var 1) (.var 3))) (.add (.mul (.int 2) (.mul (.var 4) (.pow (.var 2) 2))) (.add (.mul (.int (-2)) (.mul (.var 0) (.mul (.var 2) (.mul (.var 4) (.pow (.var 3) 2))))) (.mul (.int 2) (.mul (.var 1) (.mul (.var 2) (.mul (.var 3) (.var 4))))))))))))
theorem dataCSt_5_7_binding : litCStExpr 5 7=dataCSt_5_7 := rfl

def dataCSt_5_8 : RingExpr := (.mul (.var 7) (.mul (.var 9) (.mul (.pow (.var 10) 2) (.mul (.pow (.var 8) 4) (.add (.mul (.var 11) (.pow (.var 2) 2)) (.add (.mul (.int 4) (.mul (.var 11) (.mul (.var 4) (.pow (.var 2) 3)))) (.add (.mul (.int 4) (.mul (.var 11) (.mul (.pow (.var 2) 4) (.pow (.var 4) 2)))) (.add (.mul (.int 4) (.mul (.var 11) (.mul (.pow (.var 3) 2) (.pow (.var 4) 2)))) (.add (.mul (.int 4) (.mul (.var 15) (.mul (.pow (.var 3) 3) (.pow (.var 4) 2)))) (.add (.mul (.var 11) (.mul (.var 1) (.mul (.var 2) (.var 3)))) (.add (.mul (.int (-8)) (.mul (.var 11) (.mul (.var 3) (.mul (.pow (.var 2) 2) (.pow (.var 4) 2))))) (.add (.mul (.int (-4)) (.mul (.var 11) (.mul (.var 2) (.mul (.var 3) (.var 4))))) (.add (.mul (.int (-4)) (.mul (.var 12) (.mul (.var 1) (.mul (.pow (.var 3) 3) (.pow (.var 4) 2))))) (.add (.mul (.int (-4)) (.mul (.var 15) (.mul (.var 0) (.mul (.var 4) (.pow (.var 3) 4))))) (.add (.mul (.int (-4)) (.mul (.var 15) (.mul (.pow (.var 2) 2) (.mul (.pow (.var 3) 2) (.pow (.var 4) 2))))) (.add (.mul (.int (-2)) (.mul (.var 11) (.mul (.var 0) (.mul (.var 4) (.pow (.var 3) 3))))) (.add (.mul (.int (-2)) (.mul (.var 11) (.mul (.var 1) (.mul (.var 4) (.pow (.var 3) 2))))) (.add (.mul (.int (-2)) (.mul (.var 15) (.mul (.var 2) (.mul (.var 4) (.pow (.var 3) 2))))) (.add (.mul (.int 4) (.mul (.var 12) (.mul (.var 0) (.mul (.pow (.var 3) 4) (.pow (.var 4) 2))))) (.add (.mul (.int 4) (.mul (.var 16) (.mul (.var 0) (.mul (.var 4) (.pow (.var 3) 4))))) (.add (.mul (.int (-8)) (.mul (.var 12) (.mul (.var 0) (.mul (.pow (.var 2) 2) (.mul (.pow (.var 3) 3) (.pow (.var 4) 2)))))) (.add (.mul (.int (-4)) (.mul (.var 11) (.mul (.var 0) (.mul (.pow (.var 2) 3) (.mul (.pow (.var 3) 2) (.pow (.var 4) 2)))))) (.add (.mul (.int (-4)) (.mul (.var 11) (.mul (.var 1) (.mul (.var 2) (.mul (.pow (.var 3) 2) (.pow (.var 4) 2)))))) (.add (.mul (.int (-4)) (.mul (.var 12) (.mul (.var 0) (.mul (.var 2) (.mul (.var 4) (.pow (.var 3) 3)))))) (.add (.mul (.int (-4)) (.mul (.var 15) (.mul (.var 0) (.mul (.var 2) (.mul (.pow (.var 3) 4) (.pow (.var 4) 2)))))) (.add (.mul (.int (-2)) (.mul (.var 11) (.mul (.var 0) (.mul (.var 4) (.mul (.pow (.var 2) 2) (.pow (.var 3) 2)))))) (.add (.mul (.int 2) (.mul (.var 12) (.mul (.var 1) (.mul (.var 2) (.mul (.var 4) (.pow (.var 3) 2)))))) (.add (.mul (.int 4) (.mul (.var 11) (.mul (.var 1) (.mul (.var 3) (.mul (.var 4) (.pow (.var 2) 2)))))) (.add (.mul (.int 4) (.mul (.var 11) (.mul (.var 1) (.mul (.var 3) (.mul (.pow (.var 2) 3) (.pow (.var 4) 2)))))) (.mul (.int 4) (.mul (.var 12) (.mul (.var 1) (.mul (.pow (.var 2) 2) (.mul (.pow (.var 3) 2) (.pow (.var 4) 2)))))))))))))))))))))))))))))))))))
theorem dataCSt_5_8_binding : litCStExpr 5 8=dataCSt_5_8 := rfl

def datainitialBz_0_0 : RingExpr := (.int (-1))
theorem datainitialBz_0_0_binding : litinitialBzExpr 0 0=datainitialBz_0_0 := rfl

def datainitialBz_0_3 : RingExpr := (.mul (.var 7) (.mul (.pow (.var 8) 2) (.add (.var 2) (.add (.mul (.var 1) (.var 3)) (.add (.mul (.int (-1)) (.mul (.var 0) (.pow (.var 3) 2))) (.add (.mul (.int (-2)) (.mul (.var 3) (.var 4))) (.add (.mul (.int 2) (.mul (.var 4) (.pow (.var 2) 2))) (.add (.mul (.int (-2)) (.mul (.var 0) (.mul (.var 2) (.mul (.var 4) (.pow (.var 3) 2))))) (.mul (.int 2) (.mul (.var 1) (.mul (.var 2) (.mul (.var 3) (.var 4)))))))))))))
theorem datainitialBz_0_3_binding : litinitialBzExpr 0 3=datainitialBz_0_3 := rfl

def datainitialBz_0_4 : RingExpr := (.mul (.var 7) (.add (.mul (.int 2) (.mul (.var 1) (.var 4))) (.mul (.int (-2)) (.mul (.var 0) (.mul (.var 3) (.var 4))))))
theorem datainitialBz_0_4_binding : litinitialBzExpr 0 4=datainitialBz_0_4 := rfl

def datainitialBz_0_5 : RingExpr := (.mul (.int (-2)) (.mul (.var 7) (.var 4)))
theorem datainitialBz_0_5_binding : litinitialBzExpr 0 5=datainitialBz_0_5 := rfl

def datainitialBz_0_8 : RingExpr := (.mul (.var 7) (.mul (.pow (.var 8) 2) (.add (.mul (.int (-1)) (.mul (.var 11) (.var 2))) (.add (.mul (.int (-1)) (.mul (.var 11) (.mul (.var 0) (.pow (.var 3) 2)))) (.add (.mul (.int (-1)) (.mul (.var 11) (.mul (.var 1) (.var 3)))) (.add (.mul (.int (-2)) (.mul (.var 11) (.mul (.var 4) (.pow (.var 2) 2)))) (.add (.mul (.int (-2)) (.mul (.var 15) (.mul (.var 0) (.pow (.var 3) 3)))) (.add (.mul (.int 2) (.mul (.var 11) (.mul (.var 3) (.var 4)))) (.add (.mul (.int 2) (.mul (.var 15) (.mul (.var 4) (.pow (.var 3) 2)))) (.add (.mul (.int 2) (.mul (.var 16) (.mul (.var 0) (.pow (.var 3) 3)))) (.add (.mul (.int (-2)) (.mul (.var 12) (.mul (.var 0) (.mul (.var 2) (.pow (.var 3) 2))))) (.add (.mul (.int (-2)) (.mul (.var 12) (.mul (.var 1) (.mul (.var 4) (.pow (.var 3) 2))))) (.add (.mul (.int 2) (.mul (.var 12) (.mul (.var 0) (.mul (.var 4) (.pow (.var 3) 3))))) (.add (.mul (.int 2) (.mul (.var 14) (.mul (.var 0) (.mul (.var 2) (.pow (.var 3) 2))))) (.add (.mul (.int (-2)) (.mul (.var 11) (.mul (.var 1) (.mul (.var 2) (.mul (.var 3) (.var 4)))))) (.mul (.int 2) (.mul (.var 11) (.mul (.var 0) (.mul (.var 2) (.mul (.var 4) (.pow (.var 3) 2)))))))))))))))))))))
theorem datainitialBz_0_8_binding : litinitialBzExpr 0 8=datainitialBz_0_8 := rfl

def datainitialBb_0_0 : RingExpr := (.mul (.var 7) (.mul (.pow (.var 8) 2) (.add (.var 2) (.add (.mul (.var 1) (.var 3)) (.add (.mul (.int (-2)) (.mul (.var 0) (.pow (.var 3) 2))) (.add (.mul (.int (-2)) (.mul (.var 3) (.var 4))) (.add (.mul (.int 2) (.mul (.var 4) (.pow (.var 2) 2))) (.add (.mul (.int (-2)) (.mul (.var 0) (.mul (.var 2) (.mul (.var 4) (.pow (.var 3) 2))))) (.mul (.int 2) (.mul (.var 1) (.mul (.var 2) (.mul (.var 3) (.var 4)))))))))))))
theorem datainitialBb_0_0_binding : litinitialBbExpr 0 0=datainitialBb_0_0 := rfl

def datainitialBb_0_1 : RingExpr := (.mul (.var 7) (.add (.mul (.int 2) (.mul (.var 1) (.var 4))) (.mul (.int (-2)) (.mul (.var 0) (.mul (.var 3) (.var 4))))))
theorem datainitialBb_0_1_binding : litinitialBbExpr 0 1=datainitialBb_0_1 := rfl

def datainitialBb_0_2 : RingExpr := (.mul (.int (-2)) (.mul (.var 7) (.var 4)))
theorem datainitialBb_0_2_binding : litinitialBbExpr 0 2=datainitialBb_0_2 := rfl

def datainitialBb_0_6 : RingExpr := (.int (-2))
theorem datainitialBb_0_6_binding : litinitialBbExpr 0 6=datainitialBb_0_6 := rfl

def datainitialBb_0_8 : RingExpr := (.mul (.var 7) (.mul (.pow (.var 8) 2) (.add (.mul (.int (-1)) (.mul (.var 11) (.var 2))) (.add (.mul (.int (-1)) (.mul (.var 11) (.mul (.var 0) (.pow (.var 3) 2)))) (.add (.mul (.int (-1)) (.mul (.var 11) (.mul (.var 1) (.var 3)))) (.add (.mul (.int (-2)) (.mul (.var 11) (.mul (.var 4) (.pow (.var 2) 2)))) (.add (.mul (.int 2) (.mul (.var 11) (.mul (.var 3) (.var 4)))) (.add (.mul (.int 2) (.mul (.var 15) (.mul (.var 4) (.pow (.var 3) 2)))) (.add (.mul (.int (-2)) (.mul (.var 12) (.mul (.var 1) (.mul (.var 4) (.pow (.var 3) 2))))) (.add (.mul (.int 2) (.mul (.var 12) (.mul (.var 0) (.mul (.var 4) (.pow (.var 3) 3))))) (.add (.mul (.int (-2)) (.mul (.var 11) (.mul (.var 1) (.mul (.var 2) (.mul (.var 3) (.var 4)))))) (.mul (.int 2) (.mul (.var 11) (.mul (.var 0) (.mul (.var 2) (.mul (.var 4) (.pow (.var 3) 2)))))))))))))))))
theorem datainitialBb_0_8_binding : litinitialBbExpr 0 8=datainitialBb_0_8 := rfl

def datainitialBt_0_0 : RingExpr := (.int (-3))
theorem datainitialBt_0_0_binding : litinitialBtExpr 0 0=datainitialBt_0_0 := rfl

def datainitialBt_0_6 : RingExpr := (.int (-3))
theorem datainitialBt_0_6_binding : litinitialBtExpr 0 6=datainitialBt_0_6 := rfl

def datainitialZz_0_0 : RingExpr := (.mul (.var 7) (.mul (.var 10) (.mul (.pow (.var 8) 2) (.add (.var 2) (.add (.mul (.var 1) (.var 3)) (.add (.mul (.int (-1)) (.mul (.var 0) (.pow (.var 3) 2))) (.add (.mul (.int (-2)) (.mul (.var 3) (.var 4))) (.add (.mul (.int 2) (.mul (.var 4) (.pow (.var 2) 2))) (.add (.mul (.int (-2)) (.mul (.var 0) (.mul (.var 2) (.mul (.var 4) (.pow (.var 3) 2))))) (.mul (.int 2) (.mul (.var 1) (.mul (.var 2) (.mul (.var 3) (.var 4))))))))))))))
theorem datainitialZz_0_0_binding : litinitialZzExpr 0 0=datainitialZz_0_0 := rfl

def datainitialZz_0_1 : RingExpr := (.mul (.var 7) (.add (.mul (.var 1) (.var 4)) (.mul (.int (-1)) (.mul (.var 0) (.mul (.var 3) (.var 4))))))
theorem datainitialZz_0_1_binding : litinitialZzExpr 0 1=datainitialZz_0_1 := rfl

def datainitialZz_0_2 : RingExpr := (.mul (.int (-1)) (.mul (.var 7) (.var 4)))
theorem datainitialZz_0_2_binding : litinitialZzExpr 0 2=datainitialZz_0_2 := rfl

def datainitialZz_0_3 : RingExpr := (.mul (.var 7) (.mul (.var 10) (.mul (.pow (.var 8) 2) (.add (.var 2) (.add (.mul (.var 1) (.var 3)) (.add (.mul (.int (-1)) (.mul (.var 0) (.pow (.var 3) 2))) (.add (.mul (.int (-2)) (.mul (.var 3) (.var 4))) (.add (.mul (.int 2) (.mul (.var 4) (.pow (.var 2) 2))) (.add (.mul (.int (-2)) (.mul (.var 0) (.mul (.var 2) (.mul (.var 4) (.pow (.var 3) 2))))) (.mul (.int 2) (.mul (.var 1) (.mul (.var 2) (.mul (.var 3) (.var 4))))))))))))))
theorem datainitialZz_0_3_binding : litinitialZzExpr 0 3=datainitialZz_0_3 := rfl

def datainitialZz_0_4 : RingExpr := (.mul (.var 7) (.add (.mul (.var 1) (.var 4)) (.mul (.int (-1)) (.mul (.var 0) (.mul (.var 3) (.var 4))))))
theorem datainitialZz_0_4_binding : litinitialZzExpr 0 4=datainitialZz_0_4 := rfl

def datainitialZz_0_5 : RingExpr := (.mul (.int (-1)) (.mul (.var 7) (.var 4)))
theorem datainitialZz_0_5_binding : litinitialZzExpr 0 5=datainitialZz_0_5 := rfl

def datainitialZz_0_8 : RingExpr := (.mul (.var 7) (.mul (.pow (.var 8) 2) (.add (.mul (.int (-1)) (.mul (.var 11) (.var 2))) (.add (.mul (.int (-1)) (.mul (.var 11) (.mul (.var 1) (.var 3)))) (.add (.mul (.int (-3)) (.mul (.var 15) (.mul (.var 0) (.pow (.var 3) 3)))) (.add (.mul (.int (-2)) (.mul (.var 11) (.mul (.var 0) (.pow (.var 3) 2)))) (.add (.mul (.int (-2)) (.mul (.var 11) (.mul (.var 4) (.pow (.var 2) 2)))) (.add (.mul (.int 2) (.mul (.var 11) (.mul (.var 3) (.var 4)))) (.add (.mul (.int 2) (.mul (.var 15) (.mul (.var 4) (.pow (.var 3) 2)))) (.add (.mul (.int 3) (.mul (.var 16) (.mul (.var 0) (.pow (.var 3) 3)))) (.add (.mul (.int (-3)) (.mul (.var 12) (.mul (.var 0) (.mul (.var 2) (.pow (.var 3) 2))))) (.add (.mul (.int (-2)) (.mul (.var 12) (.mul (.var 1) (.mul (.var 4) (.pow (.var 3) 2))))) (.add (.mul (.int 2) (.mul (.var 12) (.mul (.var 0) (.mul (.var 4) (.pow (.var 3) 3))))) (.add (.mul (.int 3) (.mul (.var 14) (.mul (.var 0) (.mul (.var 2) (.pow (.var 3) 2))))) (.add (.mul (.int (-2)) (.mul (.var 11) (.mul (.var 1) (.mul (.var 2) (.mul (.var 3) (.var 4)))))) (.mul (.int 2) (.mul (.var 11) (.mul (.var 0) (.mul (.var 2) (.mul (.var 4) (.pow (.var 3) 2)))))))))))))))))))))
theorem datainitialZz_0_8_binding : litinitialZzExpr 0 8=datainitialZz_0_8 := rfl

def datainitialZb_0_0 : RingExpr := (.mul (.var 7) (.mul (.pow (.var 8) 2) (.add (.var 2) (.add (.mul (.var 1) (.var 3)) (.add (.mul (.int (-1)) (.mul (.var 0) (.pow (.var 3) 2))) (.add (.mul (.int (-2)) (.mul (.var 3) (.var 4))) (.add (.mul (.int 2) (.mul (.var 4) (.pow (.var 2) 2))) (.add (.mul (.int (-2)) (.mul (.var 0) (.mul (.var 2) (.mul (.var 4) (.pow (.var 3) 2))))) (.mul (.int 2) (.mul (.var 1) (.mul (.var 2) (.mul (.var 3) (.var 4)))))))))))))
theorem datainitialZb_0_0_binding : litinitialZbExpr 0 0=datainitialZb_0_0 := rfl

def datainitialZb_0_1 : RingExpr := (.mul (.var 7) (.add (.mul (.int 2) (.mul (.var 1) (.var 4))) (.mul (.int (-2)) (.mul (.var 0) (.mul (.var 3) (.var 4))))))
theorem datainitialZb_0_1_binding : litinitialZbExpr 0 1=datainitialZb_0_1 := rfl

def datainitialZb_0_2 : RingExpr := (.mul (.int (-2)) (.mul (.var 7) (.var 4)))
theorem datainitialZb_0_2_binding : litinitialZbExpr 0 2=datainitialZb_0_2 := rfl

def datainitialZb_0_6 : RingExpr := (.int (-1))
theorem datainitialZb_0_6_binding : litinitialZbExpr 0 6=datainitialZb_0_6 := rfl

def datainitialZb_0_8 : RingExpr := (.mul (.var 7) (.mul (.pow (.var 8) 2) (.add (.mul (.int (-1)) (.mul (.var 11) (.var 2))) (.add (.mul (.int (-1)) (.mul (.var 11) (.mul (.var 1) (.var 3)))) (.add (.mul (.int (-2)) (.mul (.var 11) (.mul (.var 0) (.pow (.var 3) 2)))) (.add (.mul (.int (-2)) (.mul (.var 11) (.mul (.var 4) (.pow (.var 2) 2)))) (.add (.mul (.int (-2)) (.mul (.var 15) (.mul (.var 0) (.pow (.var 3) 3)))) (.add (.mul (.int 2) (.mul (.var 11) (.mul (.var 3) (.var 4)))) (.add (.mul (.int 2) (.mul (.var 15) (.mul (.var 4) (.pow (.var 3) 2)))) (.add (.mul (.int 2) (.mul (.var 16) (.mul (.var 0) (.pow (.var 3) 3)))) (.add (.mul (.int (-2)) (.mul (.var 12) (.mul (.var 0) (.mul (.var 2) (.pow (.var 3) 2))))) (.add (.mul (.int (-2)) (.mul (.var 12) (.mul (.var 1) (.mul (.var 4) (.pow (.var 3) 2))))) (.add (.mul (.int 2) (.mul (.var 12) (.mul (.var 0) (.mul (.var 4) (.pow (.var 3) 3))))) (.add (.mul (.int 2) (.mul (.var 14) (.mul (.var 0) (.mul (.var 2) (.pow (.var 3) 2))))) (.add (.mul (.int (-2)) (.mul (.var 11) (.mul (.var 1) (.mul (.var 2) (.mul (.var 3) (.var 4)))))) (.mul (.int 2) (.mul (.var 11) (.mul (.var 0) (.mul (.var 2) (.mul (.var 4) (.pow (.var 3) 2)))))))))))))))))))))
theorem datainitialZb_0_8_binding : litinitialZbExpr 0 8=datainitialZb_0_8 := rfl

def datainitialZt_0_0 : RingExpr := (.mul (.var 7) (.mul (.var 10) (.mul (.pow (.var 8) 2) (.add (.var 2) (.add (.mul (.var 1) (.var 3)) (.add (.mul (.int (-3)) (.mul (.var 0) (.pow (.var 3) 2))) (.add (.mul (.int (-2)) (.mul (.var 3) (.var 4))) (.add (.mul (.int 2) (.mul (.var 4) (.pow (.var 2) 2))) (.add (.mul (.int (-2)) (.mul (.var 0) (.mul (.var 2) (.mul (.var 4) (.pow (.var 3) 2))))) (.mul (.int 2) (.mul (.var 1) (.mul (.var 2) (.mul (.var 3) (.var 4))))))))))))))
theorem datainitialZt_0_0_binding : litinitialZtExpr 0 0=datainitialZt_0_0 := rfl

def datainitialZt_0_1 : RingExpr := (.mul (.var 7) (.add (.mul (.var 1) (.var 4)) (.mul (.int (-1)) (.mul (.var 0) (.mul (.var 3) (.var 4))))))
theorem datainitialZt_0_1_binding : litinitialZtExpr 0 1=datainitialZt_0_1 := rfl

def datainitialZt_0_2 : RingExpr := (.mul (.int (-1)) (.mul (.var 7) (.var 4)))
theorem datainitialZt_0_2_binding : litinitialZtExpr 0 2=datainitialZt_0_2 := rfl

def datainitialZt_0_3 : RingExpr := (.mul (.var 7) (.mul (.var 10) (.mul (.pow (.var 8) 2) (.add (.var 2) (.add (.mul (.var 1) (.var 3)) (.add (.mul (.int (-1)) (.mul (.var 0) (.pow (.var 3) 2))) (.add (.mul (.int (-2)) (.mul (.var 3) (.var 4))) (.add (.mul (.int 2) (.mul (.var 4) (.pow (.var 2) 2))) (.add (.mul (.int (-2)) (.mul (.var 0) (.mul (.var 2) (.mul (.var 4) (.pow (.var 3) 2))))) (.mul (.int 2) (.mul (.var 1) (.mul (.var 2) (.mul (.var 3) (.var 4))))))))))))))
theorem datainitialZt_0_3_binding : litinitialZtExpr 0 3=datainitialZt_0_3 := rfl

def datainitialZt_0_4 : RingExpr := (.mul (.var 7) (.add (.mul (.var 1) (.var 4)) (.mul (.int (-1)) (.mul (.var 0) (.mul (.var 3) (.var 4))))))
theorem datainitialZt_0_4_binding : litinitialZtExpr 0 4=datainitialZt_0_4 := rfl

def datainitialZt_0_5 : RingExpr := (.mul (.int (-1)) (.mul (.var 7) (.var 4)))
theorem datainitialZt_0_5_binding : litinitialZtExpr 0 5=datainitialZt_0_5 := rfl

def datainitialZt_0_6 : RingExpr := (.int (-1))
theorem datainitialZt_0_6_binding : litinitialZtExpr 0 6=datainitialZt_0_6 := rfl

def datainitialZt_0_8 : RingExpr := (.mul (.var 7) (.mul (.pow (.var 8) 2) (.add (.mul (.int (-1)) (.mul (.var 11) (.var 2))) (.add (.mul (.var 16) (.mul (.var 0) (.pow (.var 3) 3))) (.add (.mul (.int (-1)) (.mul (.var 11) (.mul (.var 0) (.pow (.var 3) 2)))) (.add (.mul (.int (-1)) (.mul (.var 11) (.mul (.var 1) (.var 3)))) (.add (.mul (.int (-1)) (.mul (.var 15) (.mul (.var 0) (.pow (.var 3) 3)))) (.add (.mul (.int (-2)) (.mul (.var 11) (.mul (.var 4) (.pow (.var 2) 2)))) (.add (.mul (.int 2) (.mul (.var 11) (.mul (.var 3) (.var 4)))) (.add (.mul (.int 2) (.mul (.var 15) (.mul (.var 4) (.pow (.var 3) 2)))) (.add (.mul (.var 14) (.mul (.var 0) (.mul (.var 2) (.pow (.var 3) 2)))) (.add (.mul (.int (-1)) (.mul (.var 12) (.mul (.var 0) (.mul (.var 2) (.pow (.var 3) 2))))) (.add (.mul (.int (-2)) (.mul (.var 12) (.mul (.var 1) (.mul (.var 4) (.pow (.var 3) 2))))) (.add (.mul (.int 2) (.mul (.var 12) (.mul (.var 0) (.mul (.var 4) (.pow (.var 3) 3))))) (.add (.mul (.int (-2)) (.mul (.var 11) (.mul (.var 1) (.mul (.var 2) (.mul (.var 3) (.var 4)))))) (.mul (.int 2) (.mul (.var 11) (.mul (.var 0) (.mul (.var 2) (.mul (.var 4) (.pow (.var 3) 2)))))))))))))))))))))
theorem datainitialZt_0_8_binding : litinitialZtExpr 0 8=datainitialZt_0_8 := rfl

end StackSorting.FiniteGraph
