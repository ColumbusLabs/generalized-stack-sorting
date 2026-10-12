import StagedDirectionProbe
noncomputable section
namespace StackSorting.FiniteGraph
set_option maxRecDepth 65536
set_option maxHeartbeats 32000000
variable {R : Type} [Lean.Grind.CommRing R]

def dirn0E : RingExpr := dz2n0E
def dirn0P : Lean.Grind.CommRing.Poly := dz2n0P
theorem dirn0_norm : (reflectRing dirn0E).toPoly=dirn0P := dz2n0_norm

def dirn1E : RingExpr := dz2n1E
def dirn1P : Lean.Grind.CommRing.Poly := dz2n1P
theorem dirn1_norm : (reflectRing dirn1E).toPoly=dirn1P := dz2n1_norm

def dirn2E : RingExpr := dz2n2E
def dirn2P : Lean.Grind.CommRing.Poly := dz2n2P
theorem dirn2_norm : (reflectRing dirn2E).toPoly=dirn2P := dz2n2_norm

def dirn3E : RingExpr := dz2n3E
def dirn3P : Lean.Grind.CommRing.Poly := dz2n3P
theorem dirn3_norm : (reflectRing dirn3E).toPoly=dirn3P := dz2n3_norm

def dirn4E : RingExpr := dz2n4E
def dirn4P : Lean.Grind.CommRing.Poly := dz2n4P
theorem dirn4_norm : (reflectRing dirn4E).toPoly=dirn4P := dz2n4_norm

def dirn5E : RingExpr := dz2n5E
def dirn5P : Lean.Grind.CommRing.Poly := dz2n5P
theorem dirn5_norm : (reflectRing dirn5E).toPoly=dirn5P := dz2n5_norm

def dirn6E : RingExpr := dz2n6E
def dirn6P : Lean.Grind.CommRing.Poly := dz2n6P
theorem dirn6_norm : (reflectRing dirn6E).toPoly=dirn6P := dz2n6_norm

def dirn7E : RingExpr := dz2n7E
def dirn7P : Lean.Grind.CommRing.Poly := dz2n7P
theorem dirn7_norm : (reflectRing dirn7E).toPoly=dirn7P := dz2n7_norm

def dirn8E : RingExpr := dz2n8E
def dirn8P : Lean.Grind.CommRing.Poly := dz2n8P
theorem dirn8_norm : (reflectRing dirn8E).toPoly=dirn8P := dz2n8_norm

def dirn9E : RingExpr := dz2n9E
def dirn9P : Lean.Grind.CommRing.Poly := dz2n9P
theorem dirn9_norm : (reflectRing dirn9E).toPoly=dirn9P := dz2n9_norm

def dirn10E : RingExpr := dz2n10E
def dirn10P : Lean.Grind.CommRing.Poly := dz2n10P
theorem dirn10_norm : (reflectRing dirn10E).toPoly=dirn10P := dz2n10_norm

def dirn11E : RingExpr := dz2n11E
def dirn11P : Lean.Grind.CommRing.Poly := dz2n11P
theorem dirn11_norm : (reflectRing dirn11E).toPoly=dirn11P := dz2n11_norm

def dirn12E : RingExpr := dz2n12E
def dirn12P : Lean.Grind.CommRing.Poly := dz2n12P
theorem dirn12_norm : (reflectRing dirn12E).toPoly=dirn12P := dz2n12_norm

def dirn13E : RingExpr := dz2n13E
def dirn13P : Lean.Grind.CommRing.Poly := dz2n13P
theorem dirn13_norm : (reflectRing dirn13E).toPoly=dirn13P := dz2n13_norm

def dirn14E : RingExpr := dz2n14E
def dirn14P : Lean.Grind.CommRing.Poly := dz2n14P
theorem dirn14_norm : (reflectRing dirn14E).toPoly=dirn14P := dz2n14_norm

def dirn15E : RingExpr := dz2n15E
def dirn15P : Lean.Grind.CommRing.Poly := dz2n15P
theorem dirn15_norm : (reflectRing dirn15E).toPoly=dirn15P := dz2n15_norm

def dirn16E : RingExpr := dz2n16E
def dirn16P : Lean.Grind.CommRing.Poly := dz2n16P
theorem dirn16_norm : (reflectRing dirn16E).toPoly=dirn16P := dz2n16_norm

def dirn17E : RingExpr := dz2n17E
def dirn17P : Lean.Grind.CommRing.Poly := dz2n17P
theorem dirn17_norm : (reflectRing dirn17E).toPoly=dirn17P := dz2n17_norm

def dirn18E : RingExpr := dz2n18E
def dirn18P : Lean.Grind.CommRing.Poly := dz2n18P
theorem dirn18_norm : (reflectRing dirn18E).toPoly=dirn18P := dz2n18_norm

def dirn19E : RingExpr := dz2n19E
def dirn19P : Lean.Grind.CommRing.Poly := dz2n19P
theorem dirn19_norm : (reflectRing dirn19E).toPoly=dirn19P := dz2n19_norm

def dirn20E : RingExpr := dz2n20E
def dirn20P : Lean.Grind.CommRing.Poly := dz2n20P
theorem dirn20_norm : (reflectRing dirn20E).toPoly=dirn20P := dz2n20_norm

def dirn21E : RingExpr := dz2n21E
def dirn21P : Lean.Grind.CommRing.Poly := dz2n21P
theorem dirn21_norm : (reflectRing dirn21E).toPoly=dirn21P := dz2n21_norm

def dirn22E : RingExpr := dz2n22E
def dirn22P : Lean.Grind.CommRing.Poly := dz2n22P
theorem dirn22_norm : (reflectRing dirn22E).toPoly=dirn22P := dz2n22_norm

def dirn23E : RingExpr := dz2n23E
def dirn23P : Lean.Grind.CommRing.Poly := dz2n23P
theorem dirn23_norm : (reflectRing dirn23E).toPoly=dirn23P := dz2n23_norm

def dirn24E : RingExpr := dz2n24E
def dirn24P : Lean.Grind.CommRing.Poly := dz2n24P
theorem dirn24_norm : (reflectRing dirn24E).toPoly=dirn24P := dz2n24_norm

def dirn25E : RingExpr := dz2n25E
def dirn25P : Lean.Grind.CommRing.Poly := dz2n25P
theorem dirn25_norm : (reflectRing dirn25E).toPoly=dirn25P := dz2n25_norm

def dirn26E : RingExpr := dz2n26E
def dirn26P : Lean.Grind.CommRing.Poly := dz2n26P
theorem dirn26_norm : (reflectRing dirn26E).toPoly=dirn26P := dz2n26_norm

def dirn27E : RingExpr := dz2n27E
def dirn27P : Lean.Grind.CommRing.Poly := dz2n27P
theorem dirn27_norm : (reflectRing dirn27E).toPoly=dirn27P := dz2n27_norm

def dirn28E : RingExpr := dz2n28E
def dirn28P : Lean.Grind.CommRing.Poly := dz2n28P
theorem dirn28_norm : (reflectRing dirn28E).toPoly=dirn28P := dz2n28_norm

def dirn29E : RingExpr := dz2n29E
def dirn29P : Lean.Grind.CommRing.Poly := dz2n29P
theorem dirn29_norm : (reflectRing dirn29E).toPoly=dirn29P := dz2n29_norm

def dirn30E : RingExpr := dz2n30E
def dirn30P : Lean.Grind.CommRing.Poly := dz2n30P
theorem dirn30_norm : (reflectRing dirn30E).toPoly=dirn30P := dz2n30_norm

def dirn31E : RingExpr := dz2n31E
def dirn31P : Lean.Grind.CommRing.Poly := dz2n31P
theorem dirn31_norm : (reflectRing dirn31E).toPoly=dirn31P := dz2n31_norm

def dirn32E : RingExpr := dz2n32E
def dirn32P : Lean.Grind.CommRing.Poly := dz2n32P
theorem dirn32_norm : (reflectRing dirn32E).toPoly=dirn32P := dz2n32_norm

def dirn33E : RingExpr := dz2n33E
def dirn33P : Lean.Grind.CommRing.Poly := dz2n33P
theorem dirn33_norm : (reflectRing dirn33E).toPoly=dirn33P := dz2n33_norm

def dirn34E : RingExpr := dz2n34E
def dirn34P : Lean.Grind.CommRing.Poly := dz2n34P
theorem dirn34_norm : (reflectRing dirn34E).toPoly=dirn34P := dz2n34_norm

def dirn35E : RingExpr := dz2n35E
def dirn35P : Lean.Grind.CommRing.Poly := dz2n35P
theorem dirn35_norm : (reflectRing dirn35E).toPoly=dirn35P := dz2n35_norm

def dirn36E : RingExpr := dz2n36E
def dirn36P : Lean.Grind.CommRing.Poly := dz2n36P
theorem dirn36_norm : (reflectRing dirn36E).toPoly=dirn36P := dz2n36_norm

def dirn37E : RingExpr := dz2n37E
def dirn37P : Lean.Grind.CommRing.Poly := dz2n37P
theorem dirn37_norm : (reflectRing dirn37E).toPoly=dirn37P := dz2n37_norm

def dirn38E : RingExpr := dz2n38E
def dirn38P : Lean.Grind.CommRing.Poly := dz2n38P
theorem dirn38_norm : (reflectRing dirn38E).toPoly=dirn38P := dz2n38_norm

def dirn39E : RingExpr := dz2n39E
def dirn39P : Lean.Grind.CommRing.Poly := dz2n39P
theorem dirn39_norm : (reflectRing dirn39E).toPoly=dirn39P := dz2n39_norm

def dirn40E : RingExpr := dz2n40E
def dirn40P : Lean.Grind.CommRing.Poly := dz2n40P
theorem dirn40_norm : (reflectRing dirn40E).toPoly=dirn40P := dz2n40_norm

def dirn41E : RingExpr := dz2n41E
def dirn41P : Lean.Grind.CommRing.Poly := dz2n41P
theorem dirn41_norm : (reflectRing dirn41E).toPoly=dirn41P := dz2n41_norm

def dirn42E : RingExpr := dz2n42E
def dirn42P : Lean.Grind.CommRing.Poly := dz2n42P
theorem dirn42_norm : (reflectRing dirn42E).toPoly=dirn42P := dz2n42_norm

def dirn43E : RingExpr := dz2n43E
def dirn43P : Lean.Grind.CommRing.Poly := dz2n43P
theorem dirn43_norm : (reflectRing dirn43E).toPoly=dirn43P := dz2n43_norm

def dirn44E : RingExpr := dz2n44E
def dirn44P : Lean.Grind.CommRing.Poly := dz2n44P
theorem dirn44_norm : (reflectRing dirn44E).toPoly=dirn44P := dz2n44_norm

def dirn45E : RingExpr := dz2n45E
def dirn45P : Lean.Grind.CommRing.Poly := dz2n45P
theorem dirn45_norm : (reflectRing dirn45E).toPoly=dirn45P := dz2n45_norm

def dirn46E : RingExpr := dz2n46E
def dirn46P : Lean.Grind.CommRing.Poly := dz2n46P
theorem dirn46_norm : (reflectRing dirn46E).toPoly=dirn46P := dz2n46_norm

def dirn47E : RingExpr := dz2n47E
def dirn47P : Lean.Grind.CommRing.Poly := dz2n47P
theorem dirn47_norm : (reflectRing dirn47E).toPoly=dirn47P := dz2n47_norm

def dirn48E : RingExpr := dz2n48E
def dirn48P : Lean.Grind.CommRing.Poly := dz2n48P
theorem dirn48_norm : (reflectRing dirn48E).toPoly=dirn48P := dz2n48_norm

def dirn49E : RingExpr := dz2n49E
def dirn49P : Lean.Grind.CommRing.Poly := dz2n49P
theorem dirn49_norm : (reflectRing dirn49E).toPoly=dirn49P := dz2n49_norm

def dirn50E : RingExpr := dz2n50E
def dirn50P : Lean.Grind.CommRing.Poly := dz2n50P
theorem dirn50_norm : (reflectRing dirn50E).toPoly=dirn50P := dz2n50_norm

def dirn51E : RingExpr := dz2n51E
def dirn51P : Lean.Grind.CommRing.Poly := dz2n51P
theorem dirn51_norm : (reflectRing dirn51E).toPoly=dirn51P := dz2n51_norm

def dirn52E : RingExpr := dz2n52E
def dirn52P : Lean.Grind.CommRing.Poly := dz2n52P
theorem dirn52_norm : (reflectRing dirn52E).toPoly=dirn52P := dz2n52_norm

def dirn53E : RingExpr := dz2n53E
def dirn53P : Lean.Grind.CommRing.Poly := dz2n53P
theorem dirn53_norm : (reflectRing dirn53E).toPoly=dirn53P := dz2n53_norm

def dirn54E : RingExpr := dz2n54E
def dirn54P : Lean.Grind.CommRing.Poly := dz2n54P
theorem dirn54_norm : (reflectRing dirn54E).toPoly=dirn54P := dz2n54_norm

def dirn55E : RingExpr := dz2n55E
def dirn55P : Lean.Grind.CommRing.Poly := dz2n55P
theorem dirn55_norm : (reflectRing dirn55E).toPoly=dirn55P := dz2n55_norm

def dirn56E : RingExpr := dz2n56E
def dirn56P : Lean.Grind.CommRing.Poly := dz2n56P
theorem dirn56_norm : (reflectRing dirn56E).toPoly=dirn56P := dz2n56_norm

def dirn57E : RingExpr := dz2n57E
def dirn57P : Lean.Grind.CommRing.Poly := dz2n57P
theorem dirn57_norm : (reflectRing dirn57E).toPoly=dirn57P := dz2n57_norm

def dirn58E : RingExpr := dz2n58E
def dirn58P : Lean.Grind.CommRing.Poly := dz2n58P
theorem dirn58_norm : (reflectRing dirn58E).toPoly=dirn58P := dz2n58_norm

def dirn59E : RingExpr := dz2n59E
def dirn59P : Lean.Grind.CommRing.Poly := dz2n59P
theorem dirn59_norm : (reflectRing dirn59E).toPoly=dirn59P := dz2n59_norm

def dirn60E : RingExpr := dz2n60E
def dirn60P : Lean.Grind.CommRing.Poly := dz2n60P
theorem dirn60_norm : (reflectRing dirn60E).toPoly=dirn60P := dz2n60_norm

def dirn61E : RingExpr := dz2n61E
def dirn61P : Lean.Grind.CommRing.Poly := dz2n61P
theorem dirn61_norm : (reflectRing dirn61E).toPoly=dirn61P := dz2n61_norm

def dirn62E : RingExpr := dz2n62E
def dirn62P : Lean.Grind.CommRing.Poly := dz2n62P
theorem dirn62_norm : (reflectRing dirn62E).toPoly=dirn62P := dz2n62_norm

def dirn63E : RingExpr := dz2n63E
def dirn63P : Lean.Grind.CommRing.Poly := dz2n63P
theorem dirn63_norm : (reflectRing dirn63E).toPoly=dirn63P := dz2n63_norm

def dirn64E : RingExpr := dz2n64E
def dirn64P : Lean.Grind.CommRing.Poly := dz2n64P
theorem dirn64_norm : (reflectRing dirn64E).toPoly=dirn64P := dz2n64_norm

def dirn65E : RingExpr := dz2n65E
def dirn65P : Lean.Grind.CommRing.Poly := dz2n65P
theorem dirn65_norm : (reflectRing dirn65E).toPoly=dirn65P := dz2n65_norm

def dirn66E : RingExpr := dz2n66E
def dirn66P : Lean.Grind.CommRing.Poly := dz2n66P
theorem dirn66_norm : (reflectRing dirn66E).toPoly=dirn66P := dz2n66_norm

def dirn67E : RingExpr := dz2n67E
def dirn67P : Lean.Grind.CommRing.Poly := dz2n67P
theorem dirn67_norm : (reflectRing dirn67E).toPoly=dirn67P := dz2n67_norm

def dirn68E : RingExpr := dz2n68E
def dirn68P : Lean.Grind.CommRing.Poly := dz2n68P
theorem dirn68_norm : (reflectRing dirn68E).toPoly=dirn68P := dz2n68_norm

def dirn69E : RingExpr := dz2n69E
def dirn69P : Lean.Grind.CommRing.Poly := dz2n69P
theorem dirn69_norm : (reflectRing dirn69E).toPoly=dirn69P := dz2n69_norm

def dirn70E : RingExpr := dz2n70E
def dirn70P : Lean.Grind.CommRing.Poly := dz2n70P
theorem dirn70_norm : (reflectRing dirn70E).toPoly=dirn70P := dz2n70_norm

def dirn71E : RingExpr := dz2n71E
def dirn71P : Lean.Grind.CommRing.Poly := dz2n71P
theorem dirn71_norm : (reflectRing dirn71E).toPoly=dirn71P := dz2n71_norm

def dirn72E : RingExpr := dz2n72E
def dirn72P : Lean.Grind.CommRing.Poly := dz2n72P
theorem dirn72_norm : (reflectRing dirn72E).toPoly=dirn72P := dz2n72_norm

def dirn73E : RingExpr := dz2n73E
def dirn73P : Lean.Grind.CommRing.Poly := dz2n73P
theorem dirn73_norm : (reflectRing dirn73E).toPoly=dirn73P := dz2n73_norm

def dirn74E : RingExpr := dz2n74E
def dirn74P : Lean.Grind.CommRing.Poly := dz2n74P
theorem dirn74_norm : (reflectRing dirn74E).toPoly=dirn74P := dz2n74_norm

def dirn75E : RingExpr := dz2n75E
def dirn75P : Lean.Grind.CommRing.Poly := dz2n75P
theorem dirn75_norm : (reflectRing dirn75E).toPoly=dirn75P := dz2n75_norm

def dirn76E : RingExpr := dz2n76E
def dirn76P : Lean.Grind.CommRing.Poly := dz2n76P
theorem dirn76_norm : (reflectRing dirn76E).toPoly=dirn76P := dz2n76_norm

def dirn77E : RingExpr := dz2n77E
def dirn77P : Lean.Grind.CommRing.Poly := dz2n77P
theorem dirn77_norm : (reflectRing dirn77E).toPoly=dirn77P := dz2n77_norm

def dirn78E : RingExpr := dz2n78E
def dirn78P : Lean.Grind.CommRing.Poly := dz2n78P
theorem dirn78_norm : (reflectRing dirn78E).toPoly=dirn78P := dz2n78_norm

def dirn79E : RingExpr := dz2n79E
def dirn79P : Lean.Grind.CommRing.Poly := dz2n79P
theorem dirn79_norm : (reflectRing dirn79E).toPoly=dirn79P := dz2n79_norm

def dirn80E : RingExpr := dz2n80E
def dirn80P : Lean.Grind.CommRing.Poly := dz2n80P
theorem dirn80_norm : (reflectRing dirn80E).toPoly=dirn80P := dz2n80_norm

def dirn81E : RingExpr := dz2n81E
def dirn81P : Lean.Grind.CommRing.Poly := dz2n81P
theorem dirn81_norm : (reflectRing dirn81E).toPoly=dirn81P := dz2n81_norm

def dirn82E : RingExpr := dz2n82E
def dirn82P : Lean.Grind.CommRing.Poly := dz2n82P
theorem dirn82_norm : (reflectRing dirn82E).toPoly=dirn82P := dz2n82_norm

def dirn83E : RingExpr := dz2n83E
def dirn83P : Lean.Grind.CommRing.Poly := dz2n83P
theorem dirn83_norm : (reflectRing dirn83E).toPoly=dirn83P := dz2n83_norm

def dirn84E : RingExpr := dz2n84E
def dirn84P : Lean.Grind.CommRing.Poly := dz2n84P
theorem dirn84_norm : (reflectRing dirn84E).toPoly=dirn84P := dz2n84_norm

def dirn85E : RingExpr := dz2n85E
def dirn85P : Lean.Grind.CommRing.Poly := dz2n85P
theorem dirn85_norm : (reflectRing dirn85E).toPoly=dirn85P := dz2n85_norm

def dirn86E : RingExpr := dz2n86E
def dirn86P : Lean.Grind.CommRing.Poly := dz2n86P
theorem dirn86_norm : (reflectRing dirn86E).toPoly=dirn86P := dz2n86_norm

def dirn87E : RingExpr := dz2n87E
def dirn87P : Lean.Grind.CommRing.Poly := dz2n87P
theorem dirn87_norm : (reflectRing dirn87E).toPoly=dirn87P := dz2n87_norm

def dirn88E : RingExpr := dz2n88E
def dirn88P : Lean.Grind.CommRing.Poly := dz2n88P
theorem dirn88_norm : (reflectRing dirn88E).toPoly=dirn88P := dz2n88_norm

def dirn89E : RingExpr := dz2n89E
def dirn89P : Lean.Grind.CommRing.Poly := dz2n89P
theorem dirn89_norm : (reflectRing dirn89E).toPoly=dirn89P := dz2n89_norm

def dirn90E : RingExpr := dz2n90E
def dirn90P : Lean.Grind.CommRing.Poly := dz2n90P
theorem dirn90_norm : (reflectRing dirn90E).toPoly=dirn90P := dz2n90_norm

def dirn91E : RingExpr := dz2n91E
def dirn91P : Lean.Grind.CommRing.Poly := dz2n91P
theorem dirn91_norm : (reflectRing dirn91E).toPoly=dirn91P := dz2n91_norm

def dirn92E : RingExpr := dz2n92E
def dirn92P : Lean.Grind.CommRing.Poly := dz2n92P
theorem dirn92_norm : (reflectRing dirn92E).toPoly=dirn92P := dz2n92_norm

def dirn93E : RingExpr := dz2n93E
def dirn93P : Lean.Grind.CommRing.Poly := dz2n93P
theorem dirn93_norm : (reflectRing dirn93E).toPoly=dirn93P := dz2n93_norm

def dirn94E : RingExpr := dz2n94E
def dirn94P : Lean.Grind.CommRing.Poly := dz2n94P
theorem dirn94_norm : (reflectRing dirn94E).toPoly=dirn94P := dz2n94_norm

def dirn95E : RingExpr := dz2n95E
def dirn95P : Lean.Grind.CommRing.Poly := dz2n95P
theorem dirn95_norm : (reflectRing dirn95E).toPoly=dirn95P := dz2n95_norm

def dirn96E : RingExpr := dz2n96E
def dirn96P : Lean.Grind.CommRing.Poly := dz2n96P
theorem dirn96_norm : (reflectRing dirn96E).toPoly=dirn96P := dz2n96_norm

def dirn97E : RingExpr := dz2n97E
def dirn97P : Lean.Grind.CommRing.Poly := dz2n97P
theorem dirn97_norm : (reflectRing dirn97E).toPoly=dirn97P := dz2n97_norm

def dirn98E : RingExpr := dz2n98E
def dirn98P : Lean.Grind.CommRing.Poly := dz2n98P
theorem dirn98_norm : (reflectRing dirn98E).toPoly=dirn98P := dz2n98_norm

def dirn99E : RingExpr := dz2n99E
def dirn99P : Lean.Grind.CommRing.Poly := dz2n99P
theorem dirn99_norm : (reflectRing dirn99E).toPoly=dirn99P := dz2n99_norm

def dirn100E : RingExpr := dz2n100E
def dirn100P : Lean.Grind.CommRing.Poly := dz2n100P
theorem dirn100_norm : (reflectRing dirn100E).toPoly=dirn100P := dz2n100_norm

def dirn101E : RingExpr := dz2n101E
def dirn101P : Lean.Grind.CommRing.Poly := dz2n101P
theorem dirn101_norm : (reflectRing dirn101E).toPoly=dirn101P := dz2n101_norm

def dirn102E : RingExpr := dz2n102E
def dirn102P : Lean.Grind.CommRing.Poly := dz2n102P
theorem dirn102_norm : (reflectRing dirn102E).toPoly=dirn102P := dz2n102_norm

def dirn103E : RingExpr := dz2n103E
def dirn103P : Lean.Grind.CommRing.Poly := dz2n103P
theorem dirn103_norm : (reflectRing dirn103E).toPoly=dirn103P := dz2n103_norm

def dirn104E : RingExpr := dz2n104E
def dirn104P : Lean.Grind.CommRing.Poly := dz2n104P
theorem dirn104_norm : (reflectRing dirn104E).toPoly=dirn104P := dz2n104_norm

def dirn105E : RingExpr := dz2n105E
def dirn105P : Lean.Grind.CommRing.Poly := dz2n105P
theorem dirn105_norm : (reflectRing dirn105E).toPoly=dirn105P := dz2n105_norm

def dirn106E : RingExpr := dz2n106E
def dirn106P : Lean.Grind.CommRing.Poly := dz2n106P
theorem dirn106_norm : (reflectRing dirn106E).toPoly=dirn106P := dz2n106_norm

def dirn107E : RingExpr := dz2n107E
def dirn107P : Lean.Grind.CommRing.Poly := dz2n107P
theorem dirn107_norm : (reflectRing dirn107E).toPoly=dirn107P := dz2n107_norm

def dirn108E : RingExpr := dz2n108E
def dirn108P : Lean.Grind.CommRing.Poly := dz2n108P
theorem dirn108_norm : (reflectRing dirn108E).toPoly=dirn108P := dz2n108_norm

def dirn109E : RingExpr := dz2n109E
def dirn109P : Lean.Grind.CommRing.Poly := dz2n109P
theorem dirn109_norm : (reflectRing dirn109E).toPoly=dirn109P := dz2n109_norm

def dirn110E : RingExpr := dz2n110E
def dirn110P : Lean.Grind.CommRing.Poly := dz2n110P
theorem dirn110_norm : (reflectRing dirn110E).toPoly=dirn110P := dz2n110_norm

def dirn111E : RingExpr := dz2n111E
def dirn111P : Lean.Grind.CommRing.Poly := dz2n111P
theorem dirn111_norm : (reflectRing dirn111E).toPoly=dirn111P := dz2n111_norm

def dirn112E : RingExpr := dz2n112E
def dirn112P : Lean.Grind.CommRing.Poly := dz2n112P
theorem dirn112_norm : (reflectRing dirn112E).toPoly=dirn112P := dz2n112_norm

def dirn113E : RingExpr := dz2n113E
def dirn113P : Lean.Grind.CommRing.Poly := dz2n113P
theorem dirn113_norm : (reflectRing dirn113E).toPoly=dirn113P := dz2n113_norm

def dirn114E : RingExpr := dz2n114E
def dirn114P : Lean.Grind.CommRing.Poly := dz2n114P
theorem dirn114_norm : (reflectRing dirn114E).toPoly=dirn114P := dz2n114_norm

def dirn115E : RingExpr := dz2n115E
def dirn115P : Lean.Grind.CommRing.Poly := dz2n115P
theorem dirn115_norm : (reflectRing dirn115E).toPoly=dirn115P := dz2n115_norm

def dirn116E : RingExpr := dz2n116E
def dirn116P : Lean.Grind.CommRing.Poly := dz2n116P
theorem dirn116_norm : (reflectRing dirn116E).toPoly=dirn116P := dz2n116_norm

def dirn117E : RingExpr := dz2n117E
def dirn117P : Lean.Grind.CommRing.Poly := dz2n117P
theorem dirn117_norm : (reflectRing dirn117E).toPoly=dirn117P := dz2n117_norm

def dirn118E : RingExpr := dz2n118E
def dirn118P : Lean.Grind.CommRing.Poly := dz2n118P
theorem dirn118_norm : (reflectRing dirn118E).toPoly=dirn118P := dz2n118_norm

def dirn119E : RingExpr := dz2n119E
def dirn119P : Lean.Grind.CommRing.Poly := dz2n119P
theorem dirn119_norm : (reflectRing dirn119E).toPoly=dirn119P := dz2n119_norm

def dirn120E : RingExpr := dz2n120E
def dirn120P : Lean.Grind.CommRing.Poly := dz2n120P
theorem dirn120_norm : (reflectRing dirn120E).toPoly=dirn120P := dz2n120_norm

def dirn121E : RingExpr := dz2n121E
def dirn121P : Lean.Grind.CommRing.Poly := dz2n121P
theorem dirn121_norm : (reflectRing dirn121E).toPoly=dirn121P := dz2n121_norm

def dirn122E : RingExpr := dz2n122E
def dirn122P : Lean.Grind.CommRing.Poly := dz2n122P
theorem dirn122_norm : (reflectRing dirn122E).toPoly=dirn122P := dz2n122_norm

def dirn123E : RingExpr := dz2n123E
def dirn123P : Lean.Grind.CommRing.Poly := dz2n123P
theorem dirn123_norm : (reflectRing dirn123E).toPoly=dirn123P := dz2n123_norm

def dirn124E : RingExpr := dz2n124E
def dirn124P : Lean.Grind.CommRing.Poly := dz2n124P
theorem dirn124_norm : (reflectRing dirn124E).toPoly=dirn124P := dz2n124_norm

def dirn125E : RingExpr := dz2n125E
def dirn125P : Lean.Grind.CommRing.Poly := dz2n125P
theorem dirn125_norm : (reflectRing dirn125E).toPoly=dirn125P := dz2n125_norm

def dirn126E : RingExpr := dz2n126E
def dirn126P : Lean.Grind.CommRing.Poly := dz2n126P
theorem dirn126_norm : (reflectRing dirn126E).toPoly=dirn126P := dz2n126_norm

def dirn127E : RingExpr := dz2n127E
def dirn127P : Lean.Grind.CommRing.Poly := dz2n127P
theorem dirn127_norm : (reflectRing dirn127E).toPoly=dirn127P := dz2n127_norm

def dirn128E : RingExpr := dz2n128E
def dirn128P : Lean.Grind.CommRing.Poly := dz2n128P
theorem dirn128_norm : (reflectRing dirn128E).toPoly=dirn128P := dz2n128_norm

def dirn129E : RingExpr := dz2n129E
def dirn129P : Lean.Grind.CommRing.Poly := dz2n129P
theorem dirn129_norm : (reflectRing dirn129E).toPoly=dirn129P := dz2n129_norm

def dirn130E : RingExpr := dz2n130E
def dirn130P : Lean.Grind.CommRing.Poly := dz2n130P
theorem dirn130_norm : (reflectRing dirn130E).toPoly=dirn130P := dz2n130_norm

def dirn131E : RingExpr := dz2n131E
def dirn131P : Lean.Grind.CommRing.Poly := dz2n131P
theorem dirn131_norm : (reflectRing dirn131E).toPoly=dirn131P := dz2n131_norm

def dirn132E : RingExpr := dz2n132E
def dirn132P : Lean.Grind.CommRing.Poly := dz2n132P
theorem dirn132_norm : (reflectRing dirn132E).toPoly=dirn132P := dz2n132_norm

def dirn133E : RingExpr := dz2n133E
def dirn133P : Lean.Grind.CommRing.Poly := dz2n133P
theorem dirn133_norm : (reflectRing dirn133E).toPoly=dirn133P := dz2n133_norm

def dirn134E : RingExpr := dz2n134E
def dirn134P : Lean.Grind.CommRing.Poly := dz2n134P
theorem dirn134_norm : (reflectRing dirn134E).toPoly=dirn134P := dz2n134_norm

def dirn135E : RingExpr := dz2n135E
def dirn135P : Lean.Grind.CommRing.Poly := dz2n135P
theorem dirn135_norm : (reflectRing dirn135E).toPoly=dirn135P := dz2n135_norm

def dirn136E : RingExpr := dz2n136E
def dirn136P : Lean.Grind.CommRing.Poly := dz2n136P
theorem dirn136_norm : (reflectRing dirn136E).toPoly=dirn136P := dz2n136_norm

def dirn137E : RingExpr := dz2n137E
def dirn137P : Lean.Grind.CommRing.Poly := dz2n137P
theorem dirn137_norm : (reflectRing dirn137E).toPoly=dirn137P := dz2n137_norm

def dirn138E : RingExpr := dz2n138E
def dirn138P : Lean.Grind.CommRing.Poly := dz2n138P
theorem dirn138_norm : (reflectRing dirn138E).toPoly=dirn138P := dz2n138_norm

def dirn139E : RingExpr := dz2n139E
def dirn139P : Lean.Grind.CommRing.Poly := dz2n139P
theorem dirn139_norm : (reflectRing dirn139E).toPoly=dirn139P := dz2n139_norm

def dirn140E : RingExpr := dz2n140E
def dirn140P : Lean.Grind.CommRing.Poly := dz2n140P
theorem dirn140_norm : (reflectRing dirn140E).toPoly=dirn140P := dz2n140_norm

def dirn141E : RingExpr := dz2n141E
def dirn141P : Lean.Grind.CommRing.Poly := dz2n141P
theorem dirn141_norm : (reflectRing dirn141E).toPoly=dirn141P := dz2n141_norm

def dirn142E : RingExpr := dz2n142E
def dirn142P : Lean.Grind.CommRing.Poly := dz2n142P
theorem dirn142_norm : (reflectRing dirn142E).toPoly=dirn142P := dz2n142_norm

def dirn143E : RingExpr := dz2n143E
def dirn143P : Lean.Grind.CommRing.Poly := dz2n143P
theorem dirn143_norm : (reflectRing dirn143E).toPoly=dirn143P := dz2n143_norm

def dirn144E : RingExpr := dz2n144E
def dirn144P : Lean.Grind.CommRing.Poly := dz2n144P
theorem dirn144_norm : (reflectRing dirn144E).toPoly=dirn144P := dz2n144_norm

def dirn145E : RingExpr := dz2n145E
def dirn145P : Lean.Grind.CommRing.Poly := dz2n145P
theorem dirn145_norm : (reflectRing dirn145E).toPoly=dirn145P := dz2n145_norm

def dirn146E : RingExpr := dz2n146E
def dirn146P : Lean.Grind.CommRing.Poly := dz2n146P
theorem dirn146_norm : (reflectRing dirn146E).toPoly=dirn146P := dz2n146_norm

def dirn147E : RingExpr := dz2n147E
def dirn147P : Lean.Grind.CommRing.Poly := dz2n147P
theorem dirn147_norm : (reflectRing dirn147E).toPoly=dirn147P := dz2n147_norm

def dirn148E : RingExpr := dz2n148E
def dirn148P : Lean.Grind.CommRing.Poly := dz2n148P
theorem dirn148_norm : (reflectRing dirn148E).toPoly=dirn148P := dz2n148_norm

def dirn149E : RingExpr := dz2n149E
def dirn149P : Lean.Grind.CommRing.Poly := dz2n149P
theorem dirn149_norm : (reflectRing dirn149E).toPoly=dirn149P := dz2n149_norm

def dirn150E : RingExpr := dz2n150E
def dirn150P : Lean.Grind.CommRing.Poly := dz2n150P
theorem dirn150_norm : (reflectRing dirn150E).toPoly=dirn150P := dz2n150_norm

def dirn151E : RingExpr := dz2n151E
def dirn151P : Lean.Grind.CommRing.Poly := dz2n151P
theorem dirn151_norm : (reflectRing dirn151E).toPoly=dirn151P := dz2n151_norm

def dirn152E : RingExpr := dz2n152E
def dirn152P : Lean.Grind.CommRing.Poly := dz2n152P
theorem dirn152_norm : (reflectRing dirn152E).toPoly=dirn152P := dz2n152_norm

def dirn153E : RingExpr := dz2n153E
def dirn153P : Lean.Grind.CommRing.Poly := dz2n153P
theorem dirn153_norm : (reflectRing dirn153E).toPoly=dirn153P := dz2n153_norm

def dirn154E : RingExpr := dz2n154E
def dirn154P : Lean.Grind.CommRing.Poly := dz2n154P
theorem dirn154_norm : (reflectRing dirn154E).toPoly=dirn154P := dz2n154_norm

def dirn155E : RingExpr := dz2n155E
def dirn155P : Lean.Grind.CommRing.Poly := dz2n155P
theorem dirn155_norm : (reflectRing dirn155E).toPoly=dirn155P := dz2n155_norm

def dirn156E : RingExpr := dz2n156E
def dirn156P : Lean.Grind.CommRing.Poly := dz2n156P
theorem dirn156_norm : (reflectRing dirn156E).toPoly=dirn156P := dz2n156_norm

def dirn157E : RingExpr := dz2n157E
def dirn157P : Lean.Grind.CommRing.Poly := dz2n157P
theorem dirn157_norm : (reflectRing dirn157E).toPoly=dirn157P := dz2n157_norm

def dirn158E : RingExpr := dz2n158E
def dirn158P : Lean.Grind.CommRing.Poly := dz2n158P
theorem dirn158_norm : (reflectRing dirn158E).toPoly=dirn158P := dz2n158_norm

def dirn159E : RingExpr := dz2n159E
def dirn159P : Lean.Grind.CommRing.Poly := dz2n159P
theorem dirn159_norm : (reflectRing dirn159E).toPoly=dirn159P := dz2n159_norm

def dirn160E : RingExpr := dz2n160E
def dirn160P : Lean.Grind.CommRing.Poly := dz2n160P
theorem dirn160_norm : (reflectRing dirn160E).toPoly=dirn160P := dz2n160_norm

def dirn161E : RingExpr := dz2n161E
def dirn161P : Lean.Grind.CommRing.Poly := dz2n161P
theorem dirn161_norm : (reflectRing dirn161E).toPoly=dirn161P := dz2n161_norm

def dirn162E : RingExpr := dz2n162E
def dirn162P : Lean.Grind.CommRing.Poly := dz2n162P
theorem dirn162_norm : (reflectRing dirn162E).toPoly=dirn162P := dz2n162_norm

def dirn163E : RingExpr := dz2n163E
def dirn163P : Lean.Grind.CommRing.Poly := dz2n163P
theorem dirn163_norm : (reflectRing dirn163E).toPoly=dirn163P := dz2n163_norm

def dirn164E : RingExpr := dz2n164E
def dirn164P : Lean.Grind.CommRing.Poly := dz2n164P
theorem dirn164_norm : (reflectRing dirn164E).toPoly=dirn164P := dz2n164_norm

def dirn165E : RingExpr := dz2n165E
def dirn165P : Lean.Grind.CommRing.Poly := dz2n165P
theorem dirn165_norm : (reflectRing dirn165E).toPoly=dirn165P := dz2n165_norm

def dirn166E : RingExpr := dz2n166E
def dirn166P : Lean.Grind.CommRing.Poly := dz2n166P
theorem dirn166_norm : (reflectRing dirn166E).toPoly=dirn166P := dz2n166_norm

def dirn167E : RingExpr := dz2n167E
def dirn167P : Lean.Grind.CommRing.Poly := dz2n167P
theorem dirn167_norm : (reflectRing dirn167E).toPoly=dirn167P := dz2n167_norm

def dirn168E : RingExpr := dz2n168E
def dirn168P : Lean.Grind.CommRing.Poly := dz2n168P
theorem dirn168_norm : (reflectRing dirn168E).toPoly=dirn168P := dz2n168_norm

def dirn169E : RingExpr := dz2n169E
def dirn169P : Lean.Grind.CommRing.Poly := dz2n169P
theorem dirn169_norm : (reflectRing dirn169E).toPoly=dirn169P := dz2n169_norm

def dirn170E : RingExpr := dz2n170E
def dirn170P : Lean.Grind.CommRing.Poly := dz2n170P
theorem dirn170_norm : (reflectRing dirn170E).toPoly=dirn170P := dz2n170_norm

def dirn171E : RingExpr := dz2n171E
def dirn171P : Lean.Grind.CommRing.Poly := dz2n171P
theorem dirn171_norm : (reflectRing dirn171E).toPoly=dirn171P := dz2n171_norm

def dirn172E : RingExpr := dz2n172E
def dirn172P : Lean.Grind.CommRing.Poly := dz2n172P
theorem dirn172_norm : (reflectRing dirn172E).toPoly=dirn172P := dz2n172_norm

def dirn173E : RingExpr := dz2n173E
def dirn173P : Lean.Grind.CommRing.Poly := dz2n173P
theorem dirn173_norm : (reflectRing dirn173E).toPoly=dirn173P := dz2n173_norm

def dirn174E : RingExpr := dz2n174E
def dirn174P : Lean.Grind.CommRing.Poly := dz2n174P
theorem dirn174_norm : (reflectRing dirn174E).toPoly=dirn174P := dz2n174_norm

def dirn175E : RingExpr := dz2n175E
def dirn175P : Lean.Grind.CommRing.Poly := dz2n175P
theorem dirn175_norm : (reflectRing dirn175E).toPoly=dirn175P := dz2n175_norm

def dirn176E : RingExpr := dz2n176E
def dirn176P : Lean.Grind.CommRing.Poly := dz2n176P
theorem dirn176_norm : (reflectRing dirn176E).toPoly=dirn176P := dz2n176_norm

def dirn177E : RingExpr := dz2n177E
def dirn177P : Lean.Grind.CommRing.Poly := dz2n177P
theorem dirn177_norm : (reflectRing dirn177E).toPoly=dirn177P := dz2n177_norm

def dirn178E : RingExpr := dz2n178E
def dirn178P : Lean.Grind.CommRing.Poly := dz2n178P
theorem dirn178_norm : (reflectRing dirn178E).toPoly=dirn178P := dz2n178_norm

def dirn179E : RingExpr := dz2n179E
def dirn179P : Lean.Grind.CommRing.Poly := dz2n179P
theorem dirn179_norm : (reflectRing dirn179E).toPoly=dirn179P := dz2n179_norm

def dirn180E : RingExpr := dz2n180E
def dirn180P : Lean.Grind.CommRing.Poly := dz2n180P
theorem dirn180_norm : (reflectRing dirn180E).toPoly=dirn180P := dz2n180_norm

def dirn181E : RingExpr := dz2n181E
def dirn181P : Lean.Grind.CommRing.Poly := dz2n181P
theorem dirn181_norm : (reflectRing dirn181E).toPoly=dirn181P := dz2n181_norm

def dirn182E : RingExpr := dz2n182E
def dirn182P : Lean.Grind.CommRing.Poly := dz2n182P
theorem dirn182_norm : (reflectRing dirn182E).toPoly=dirn182P := dz2n182_norm

def dirn183E : RingExpr := dz2n183E
def dirn183P : Lean.Grind.CommRing.Poly := dz2n183P
theorem dirn183_norm : (reflectRing dirn183E).toPoly=dirn183P := dz2n183_norm

def dirn184E : RingExpr := dz2n184E
def dirn184P : Lean.Grind.CommRing.Poly := dz2n184P
theorem dirn184_norm : (reflectRing dirn184E).toPoly=dirn184P := dz2n184_norm

def dirn185E : RingExpr := dz2n185E
def dirn185P : Lean.Grind.CommRing.Poly := dz2n185P
theorem dirn185_norm : (reflectRing dirn185E).toPoly=dirn185P := dz2n185_norm

def dirn186E : RingExpr := dz2n186E
def dirn186P : Lean.Grind.CommRing.Poly := dz2n186P
theorem dirn186_norm : (reflectRing dirn186E).toPoly=dirn186P := dz2n186_norm

def dirn187E : RingExpr := dz2n187E
def dirn187P : Lean.Grind.CommRing.Poly := dz2n187P
theorem dirn187_norm : (reflectRing dirn187E).toPoly=dirn187P := dz2n187_norm

def dirn188E : RingExpr := dz2n188E
def dirn188P : Lean.Grind.CommRing.Poly := dz2n188P
theorem dirn188_norm : (reflectRing dirn188E).toPoly=dirn188P := dz2n188_norm

def dirn189E : RingExpr := dz2n189E
def dirn189P : Lean.Grind.CommRing.Poly := dz2n189P
theorem dirn189_norm : (reflectRing dirn189E).toPoly=dirn189P := dz2n189_norm

def dirn190E : RingExpr := dz2n190E
def dirn190P : Lean.Grind.CommRing.Poly := dz2n190P
theorem dirn190_norm : (reflectRing dirn190E).toPoly=dirn190P := dz2n190_norm

def dirn191E : RingExpr := dz2n191E
def dirn191P : Lean.Grind.CommRing.Poly := dz2n191P
theorem dirn191_norm : (reflectRing dirn191E).toPoly=dirn191P := dz2n191_norm

def dirn192E : RingExpr := dz2n192E
def dirn192P : Lean.Grind.CommRing.Poly := dz2n192P
theorem dirn192_norm : (reflectRing dirn192E).toPoly=dirn192P := dz2n192_norm

def dirn193E : RingExpr := dz2n193E
def dirn193P : Lean.Grind.CommRing.Poly := dz2n193P
theorem dirn193_norm : (reflectRing dirn193E).toPoly=dirn193P := dz2n193_norm

def dirn194E : RingExpr := dz2n194E
def dirn194P : Lean.Grind.CommRing.Poly := dz2n194P
theorem dirn194_norm : (reflectRing dirn194E).toPoly=dirn194P := dz2n194_norm

def dirn195E : RingExpr := dz2n195E
def dirn195P : Lean.Grind.CommRing.Poly := dz2n195P
theorem dirn195_norm : (reflectRing dirn195E).toPoly=dirn195P := dz2n195_norm

def dirn196E : RingExpr := dz2n196E
def dirn196P : Lean.Grind.CommRing.Poly := dz2n196P
theorem dirn196_norm : (reflectRing dirn196E).toPoly=dirn196P := dz2n196_norm

def dirn197E : RingExpr := dz2n197E
def dirn197P : Lean.Grind.CommRing.Poly := dz2n197P
theorem dirn197_norm : (reflectRing dirn197E).toPoly=dirn197P := dz2n197_norm

def dirn198E : RingExpr := dz2n198E
def dirn198P : Lean.Grind.CommRing.Poly := dz2n198P
theorem dirn198_norm : (reflectRing dirn198E).toPoly=dirn198P := dz2n198_norm

def dirn199E : RingExpr := dz2n199E
def dirn199P : Lean.Grind.CommRing.Poly := dz2n199P
theorem dirn199_norm : (reflectRing dirn199E).toPoly=dirn199P := dz2n199_norm

def dirn200E : RingExpr := dz2n200E
def dirn200P : Lean.Grind.CommRing.Poly := dz2n200P
theorem dirn200_norm : (reflectRing dirn200E).toPoly=dirn200P := dz2n200_norm

def dirn201E : RingExpr := dz2n201E
def dirn201P : Lean.Grind.CommRing.Poly := dz2n201P
theorem dirn201_norm : (reflectRing dirn201E).toPoly=dirn201P := dz2n201_norm

def dirn202E : RingExpr := dz2n202E
def dirn202P : Lean.Grind.CommRing.Poly := dz2n202P
theorem dirn202_norm : (reflectRing dirn202E).toPoly=dirn202P := dz2n202_norm

def dirn203E : RingExpr := dz2n203E
def dirn203P : Lean.Grind.CommRing.Poly := dz2n203P
theorem dirn203_norm : (reflectRing dirn203E).toPoly=dirn203P := dz2n203_norm

def dirn204E : RingExpr := dz2n204E
def dirn204P : Lean.Grind.CommRing.Poly := dz2n204P
theorem dirn204_norm : (reflectRing dirn204E).toPoly=dirn204P := dz2n204_norm

def dirn205E : RingExpr := dz2n205E
def dirn205P : Lean.Grind.CommRing.Poly := dz2n205P
theorem dirn205_norm : (reflectRing dirn205E).toPoly=dirn205P := dz2n205_norm

def dirn206E : RingExpr := dz2n206E
def dirn206P : Lean.Grind.CommRing.Poly := dz2n206P
theorem dirn206_norm : (reflectRing dirn206E).toPoly=dirn206P := dz2n206_norm

def dirn207E : RingExpr := dz2n207E
def dirn207P : Lean.Grind.CommRing.Poly := dz2n207P
theorem dirn207_norm : (reflectRing dirn207E).toPoly=dirn207P := dz2n207_norm

def dirn208E : RingExpr := dz2n208E
def dirn208P : Lean.Grind.CommRing.Poly := dz2n208P
theorem dirn208_norm : (reflectRing dirn208E).toPoly=dirn208P := dz2n208_norm

def dirn209E : RingExpr := dz2n209E
def dirn209P : Lean.Grind.CommRing.Poly := dz2n209P
theorem dirn209_norm : (reflectRing dirn209E).toPoly=dirn209P := dz2n209_norm

def dirn210E : RingExpr := dz2n210E
def dirn210P : Lean.Grind.CommRing.Poly := dz2n210P
theorem dirn210_norm : (reflectRing dirn210E).toPoly=dirn210P := dz2n210_norm

def dirn211E : RingExpr := dz2n211E
def dirn211P : Lean.Grind.CommRing.Poly := dz2n211P
theorem dirn211_norm : (reflectRing dirn211E).toPoly=dirn211P := dz2n211_norm

def dirn212E : RingExpr := dz2n212E
def dirn212P : Lean.Grind.CommRing.Poly := dz2n212P
theorem dirn212_norm : (reflectRing dirn212E).toPoly=dirn212P := dz2n212_norm

def dirn213E : RingExpr := dz2n213E
def dirn213P : Lean.Grind.CommRing.Poly := dz2n213P
theorem dirn213_norm : (reflectRing dirn213E).toPoly=dirn213P := dz2n213_norm

def dirn214E : RingExpr := dz2n214E
def dirn214P : Lean.Grind.CommRing.Poly := dz2n214P
theorem dirn214_norm : (reflectRing dirn214E).toPoly=dirn214P := dz2n214_norm

def dirn215E : RingExpr := dz2n215E
def dirn215P : Lean.Grind.CommRing.Poly := dz2n215P
theorem dirn215_norm : (reflectRing dirn215E).toPoly=dirn215P := dz2n215_norm

def dirn216E : RingExpr := dz2n216E
def dirn216P : Lean.Grind.CommRing.Poly := dz2n216P
theorem dirn216_norm : (reflectRing dirn216E).toPoly=dirn216P := dz2n216_norm

def dirn217E : RingExpr := dz2n217E
def dirn217P : Lean.Grind.CommRing.Poly := dz2n217P
theorem dirn217_norm : (reflectRing dirn217E).toPoly=dirn217P := dz2n217_norm

def dirn218E : RingExpr := dz2n218E
def dirn218P : Lean.Grind.CommRing.Poly := dz2n218P
theorem dirn218_norm : (reflectRing dirn218E).toPoly=dirn218P := dz2n218_norm

def dirn219E : RingExpr := dz2n219E
def dirn219P : Lean.Grind.CommRing.Poly := dz2n219P
theorem dirn219_norm : (reflectRing dirn219E).toPoly=dirn219P := dz2n219_norm

def dirn220E : RingExpr := dz2n220E
def dirn220P : Lean.Grind.CommRing.Poly := dz2n220P
theorem dirn220_norm : (reflectRing dirn220E).toPoly=dirn220P := dz2n220_norm

def dirn221E : RingExpr := dz2n221E
def dirn221P : Lean.Grind.CommRing.Poly := dz2n221P
theorem dirn221_norm : (reflectRing dirn221E).toPoly=dirn221P := dz2n221_norm

def dirn222E : RingExpr := dz2n222E
def dirn222P : Lean.Grind.CommRing.Poly := dz2n222P
theorem dirn222_norm : (reflectRing dirn222E).toPoly=dirn222P := dz2n222_norm

def dirn223E : RingExpr := dz2n223E
def dirn223P : Lean.Grind.CommRing.Poly := dz2n223P
theorem dirn223_norm : (reflectRing dirn223E).toPoly=dirn223P := dz2n223_norm

def dirn224E : RingExpr := dz2n224E
def dirn224P : Lean.Grind.CommRing.Poly := dz2n224P
theorem dirn224_norm : (reflectRing dirn224E).toPoly=dirn224P := dz2n224_norm

def dirn225E : RingExpr := dz2n225E
def dirn225P : Lean.Grind.CommRing.Poly := dz2n225P
theorem dirn225_norm : (reflectRing dirn225E).toPoly=dirn225P := dz2n225_norm

def dirn226E : RingExpr := dz2n226E
def dirn226P : Lean.Grind.CommRing.Poly := dz2n226P
theorem dirn226_norm : (reflectRing dirn226E).toPoly=dirn226P := dz2n226_norm

def dirn227E : RingExpr := dz2n227E
def dirn227P : Lean.Grind.CommRing.Poly := dz2n227P
theorem dirn227_norm : (reflectRing dirn227E).toPoly=dirn227P := dz2n227_norm

def dirn228E : RingExpr := dz2n228E
def dirn228P : Lean.Grind.CommRing.Poly := dz2n228P
theorem dirn228_norm : (reflectRing dirn228E).toPoly=dirn228P := dz2n228_norm

def dirn229E : RingExpr := dz2n229E
def dirn229P : Lean.Grind.CommRing.Poly := dz2n229P
theorem dirn229_norm : (reflectRing dirn229E).toPoly=dirn229P := dz2n229_norm

def dirn230E : RingExpr := dz2n230E
def dirn230P : Lean.Grind.CommRing.Poly := dz2n230P
theorem dirn230_norm : (reflectRing dirn230E).toPoly=dirn230P := dz2n230_norm

def dirn231E : RingExpr := dz2n231E
def dirn231P : Lean.Grind.CommRing.Poly := dz2n231P
theorem dirn231_norm : (reflectRing dirn231E).toPoly=dirn231P := dz2n231_norm

def dirn232E : RingExpr := dz2n232E
def dirn232P : Lean.Grind.CommRing.Poly := dz2n232P
theorem dirn232_norm : (reflectRing dirn232E).toPoly=dirn232P := dz2n232_norm

def dirn233E : RingExpr := dz2n233E
def dirn233P : Lean.Grind.CommRing.Poly := dz2n233P
theorem dirn233_norm : (reflectRing dirn233E).toPoly=dirn233P := dz2n233_norm

def dirn234E : RingExpr := dz2n234E
def dirn234P : Lean.Grind.CommRing.Poly := dz2n234P
theorem dirn234_norm : (reflectRing dirn234E).toPoly=dirn234P := dz2n234_norm

def dirn235E : RingExpr := dz2n235E
def dirn235P : Lean.Grind.CommRing.Poly := dz2n235P
theorem dirn235_norm : (reflectRing dirn235E).toPoly=dirn235P := dz2n235_norm

def dirn236E : RingExpr := dz2n236E
def dirn236P : Lean.Grind.CommRing.Poly := dz2n236P
theorem dirn236_norm : (reflectRing dirn236E).toPoly=dirn236P := dz2n236_norm

def dirn237E : RingExpr := dz2n237E
def dirn237P : Lean.Grind.CommRing.Poly := dz2n237P
theorem dirn237_norm : (reflectRing dirn237E).toPoly=dirn237P := dz2n237_norm

def dirn238E : RingExpr := dz2n238E
def dirn238P : Lean.Grind.CommRing.Poly := dz2n238P
theorem dirn238_norm : (reflectRing dirn238E).toPoly=dirn238P := dz2n238_norm

def dirn239E : RingExpr := dz2n239E
def dirn239P : Lean.Grind.CommRing.Poly := dz2n239P
theorem dirn239_norm : (reflectRing dirn239E).toPoly=dirn239P := dz2n239_norm

def dirn240E : RingExpr := dz2n240E
def dirn240P : Lean.Grind.CommRing.Poly := dz2n240P
theorem dirn240_norm : (reflectRing dirn240E).toPoly=dirn240P := dz2n240_norm

def dirn241E : RingExpr := dz2n241E
def dirn241P : Lean.Grind.CommRing.Poly := dz2n241P
theorem dirn241_norm : (reflectRing dirn241E).toPoly=dirn241P := dz2n241_norm

def dirn242E : RingExpr := dz2n242E
def dirn242P : Lean.Grind.CommRing.Poly := dz2n242P
theorem dirn242_norm : (reflectRing dirn242E).toPoly=dirn242P := dz2n242_norm

def dirn243E : RingExpr := dz2n243E
def dirn243P : Lean.Grind.CommRing.Poly := dz2n243P
theorem dirn243_norm : (reflectRing dirn243E).toPoly=dirn243P := dz2n243_norm

def dirn244E : RingExpr := dz2n244E
def dirn244P : Lean.Grind.CommRing.Poly := dz2n244P
theorem dirn244_norm : (reflectRing dirn244E).toPoly=dirn244P := dz2n244_norm

def dirn245E : RingExpr := dz2n245E
def dirn245P : Lean.Grind.CommRing.Poly := dz2n245P
theorem dirn245_norm : (reflectRing dirn245E).toPoly=dirn245P := dz2n245_norm

def dirn246E : RingExpr := dz2n246E
def dirn246P : Lean.Grind.CommRing.Poly := dz2n246P
theorem dirn246_norm : (reflectRing dirn246E).toPoly=dirn246P := dz2n246_norm

def dirn247E : RingExpr := dz2n247E
def dirn247P : Lean.Grind.CommRing.Poly := dz2n247P
theorem dirn247_norm : (reflectRing dirn247E).toPoly=dirn247P := dz2n247_norm

def dirn248E : RingExpr := dz2n248E
def dirn248P : Lean.Grind.CommRing.Poly := dz2n248P
theorem dirn248_norm : (reflectRing dirn248E).toPoly=dirn248P := dz2n248_norm

def dirn249E : RingExpr := dz2n249E
def dirn249P : Lean.Grind.CommRing.Poly := dz2n249P
theorem dirn249_norm : (reflectRing dirn249E).toPoly=dirn249P := dz2n249_norm

def dirn250E : RingExpr := dz2n250E
def dirn250P : Lean.Grind.CommRing.Poly := dz2n250P
theorem dirn250_norm : (reflectRing dirn250E).toPoly=dirn250P := dz2n250_norm

def dirn251E : RingExpr := dz2n251E
def dirn251P : Lean.Grind.CommRing.Poly := dz2n251P
theorem dirn251_norm : (reflectRing dirn251E).toPoly=dirn251P := dz2n251_norm

def dirn252E : RingExpr := dz2n252E
def dirn252P : Lean.Grind.CommRing.Poly := dz2n252P
theorem dirn252_norm : (reflectRing dirn252E).toPoly=dirn252P := dz2n252_norm

def dirn253E : RingExpr := dz2n253E
def dirn253P : Lean.Grind.CommRing.Poly := dz2n253P
theorem dirn253_norm : (reflectRing dirn253E).toPoly=dirn253P := dz2n253_norm

def dirn254E : RingExpr := dz2n254E
def dirn254P : Lean.Grind.CommRing.Poly := dz2n254P
theorem dirn254_norm : (reflectRing dirn254E).toPoly=dirn254P := dz2n254_norm

def dirn255E : RingExpr := dz2n255E
def dirn255P : Lean.Grind.CommRing.Poly := dz2n255P
theorem dirn255_norm : (reflectRing dirn255E).toPoly=dirn255P := dz2n255_norm

def dirn256E : RingExpr := dz2n256E
def dirn256P : Lean.Grind.CommRing.Poly := dz2n256P
theorem dirn256_norm : (reflectRing dirn256E).toPoly=dirn256P := dz2n256_norm

def dirn257E : RingExpr := dz2n257E
def dirn257P : Lean.Grind.CommRing.Poly := dz2n257P
theorem dirn257_norm : (reflectRing dirn257E).toPoly=dirn257P := dz2n257_norm

def dirn258E : RingExpr := dz2n258E
def dirn258P : Lean.Grind.CommRing.Poly := dz2n258P
theorem dirn258_norm : (reflectRing dirn258E).toPoly=dirn258P := dz2n258_norm

def dirn259E : RingExpr := dz2n259E
def dirn259P : Lean.Grind.CommRing.Poly := dz2n259P
theorem dirn259_norm : (reflectRing dirn259E).toPoly=dirn259P := dz2n259_norm

def dirn260E : RingExpr := dz2n260E
def dirn260P : Lean.Grind.CommRing.Poly := dz2n260P
theorem dirn260_norm : (reflectRing dirn260E).toPoly=dirn260P := dz2n260_norm

def dirn261E : RingExpr := dz2n261E
def dirn261P : Lean.Grind.CommRing.Poly := dz2n261P
theorem dirn261_norm : (reflectRing dirn261E).toPoly=dirn261P := dz2n261_norm

def dirn262E : RingExpr := dz2n262E
def dirn262P : Lean.Grind.CommRing.Poly := dz2n262P
theorem dirn262_norm : (reflectRing dirn262E).toPoly=dirn262P := dz2n262_norm

def dirn263E : RingExpr := dz2n263E
def dirn263P : Lean.Grind.CommRing.Poly := dz2n263P
theorem dirn263_norm : (reflectRing dirn263E).toPoly=dirn263P := dz2n263_norm

def dirn264E : RingExpr := dz2n264E
def dirn264P : Lean.Grind.CommRing.Poly := dz2n264P
theorem dirn264_norm : (reflectRing dirn264E).toPoly=dirn264P := dz2n264_norm

def dirn265E : RingExpr := dz2n265E
def dirn265P : Lean.Grind.CommRing.Poly := dz2n265P
theorem dirn265_norm : (reflectRing dirn265E).toPoly=dirn265P := dz2n265_norm

def dirn266E : RingExpr := dz2n266E
def dirn266P : Lean.Grind.CommRing.Poly := dz2n266P
theorem dirn266_norm : (reflectRing dirn266E).toPoly=dirn266P := dz2n266_norm

def dirn267E : RingExpr := dz2n267E
def dirn267P : Lean.Grind.CommRing.Poly := dz2n267P
theorem dirn267_norm : (reflectRing dirn267E).toPoly=dirn267P := dz2n267_norm

def dirn268E : RingExpr := dz2n268E
def dirn268P : Lean.Grind.CommRing.Poly := dz2n268P
theorem dirn268_norm : (reflectRing dirn268E).toPoly=dirn268P := dz2n268_norm

def dirn269E : RingExpr := dz2n269E
def dirn269P : Lean.Grind.CommRing.Poly := dz2n269P
theorem dirn269_norm : (reflectRing dirn269E).toPoly=dirn269P := dz2n269_norm

def dirn270E : RingExpr := dz2n270E
def dirn270P : Lean.Grind.CommRing.Poly := dz2n270P
theorem dirn270_norm : (reflectRing dirn270E).toPoly=dirn270P := dz2n270_norm

def dirn271E : RingExpr := dz2n271E
def dirn271P : Lean.Grind.CommRing.Poly := dz2n271P
theorem dirn271_norm : (reflectRing dirn271E).toPoly=dirn271P := dz2n271_norm

def dirn272E : RingExpr := dz2n272E
def dirn272P : Lean.Grind.CommRing.Poly := dz2n272P
theorem dirn272_norm : (reflectRing dirn272E).toPoly=dirn272P := dz2n272_norm

def dirn273E : RingExpr := dz2n273E
def dirn273P : Lean.Grind.CommRing.Poly := dz2n273P
theorem dirn273_norm : (reflectRing dirn273E).toPoly=dirn273P := dz2n273_norm

def dirn274E : RingExpr := dz2n274E
def dirn274P : Lean.Grind.CommRing.Poly := dz2n274P
theorem dirn274_norm : (reflectRing dirn274E).toPoly=dirn274P := dz2n274_norm

def dirn275E : RingExpr := dz2n275E
def dirn275P : Lean.Grind.CommRing.Poly := dz2n275P
theorem dirn275_norm : (reflectRing dirn275E).toPoly=dirn275P := dz2n275_norm

def dirn276E : RingExpr := dz2n276E
def dirn276P : Lean.Grind.CommRing.Poly := dz2n276P
theorem dirn276_norm : (reflectRing dirn276E).toPoly=dirn276P := dz2n276_norm

def dirn277E : RingExpr := dz2n277E
def dirn277P : Lean.Grind.CommRing.Poly := dz2n277P
theorem dirn277_norm : (reflectRing dirn277E).toPoly=dirn277P := dz2n277_norm

def dirn278E : RingExpr := dz2n278E
def dirn278P : Lean.Grind.CommRing.Poly := dz2n278P
theorem dirn278_norm : (reflectRing dirn278E).toPoly=dirn278P := dz2n278_norm

def dirn279E : RingExpr := dz2n279E
def dirn279P : Lean.Grind.CommRing.Poly := dz2n279P
theorem dirn279_norm : (reflectRing dirn279E).toPoly=dirn279P := dz2n279_norm

def dirn280E : RingExpr := dz2n280E
def dirn280P : Lean.Grind.CommRing.Poly := dz2n280P
theorem dirn280_norm : (reflectRing dirn280E).toPoly=dirn280P := dz2n280_norm

def dirn281E : RingExpr := dz2n281E
def dirn281P : Lean.Grind.CommRing.Poly := dz2n281P
theorem dirn281_norm : (reflectRing dirn281E).toPoly=dirn281P := dz2n281_norm

def dirn282E : RingExpr := dz2n282E
def dirn282P : Lean.Grind.CommRing.Poly := dz2n282P
theorem dirn282_norm : (reflectRing dirn282E).toPoly=dirn282P := dz2n282_norm

def dirn283E : RingExpr := dz2n283E
def dirn283P : Lean.Grind.CommRing.Poly := dz2n283P
theorem dirn283_norm : (reflectRing dirn283E).toPoly=dirn283P := dz2n283_norm

def dirn284E : RingExpr := dz2n284E
def dirn284P : Lean.Grind.CommRing.Poly := dz2n284P
theorem dirn284_norm : (reflectRing dirn284E).toPoly=dirn284P := dz2n284_norm

def dirn285E : RingExpr := dz2n285E
def dirn285P : Lean.Grind.CommRing.Poly := dz2n285P
theorem dirn285_norm : (reflectRing dirn285E).toPoly=dirn285P := dz2n285_norm

def dirn286E : RingExpr := dz2n286E
def dirn286P : Lean.Grind.CommRing.Poly := dz2n286P
theorem dirn286_norm : (reflectRing dirn286E).toPoly=dirn286P := dz2n286_norm

def dirn287E : RingExpr := dz2n287E
def dirn287P : Lean.Grind.CommRing.Poly := dz2n287P
theorem dirn287_norm : (reflectRing dirn287E).toPoly=dirn287P := dz2n287_norm

def dirn288E : RingExpr := dz2n288E
def dirn288P : Lean.Grind.CommRing.Poly := dz2n288P
theorem dirn288_norm : (reflectRing dirn288E).toPoly=dirn288P := dz2n288_norm

def dirn289E : RingExpr := dz2n289E
def dirn289P : Lean.Grind.CommRing.Poly := dz2n289P
theorem dirn289_norm : (reflectRing dirn289E).toPoly=dirn289P := dz2n289_norm

def dirn290E : RingExpr := dz2n290E
def dirn290P : Lean.Grind.CommRing.Poly := dz2n290P
theorem dirn290_norm : (reflectRing dirn290E).toPoly=dirn290P := dz2n290_norm

def dirn291E : RingExpr := dz2n291E
def dirn291P : Lean.Grind.CommRing.Poly := dz2n291P
theorem dirn291_norm : (reflectRing dirn291E).toPoly=dirn291P := dz2n291_norm

def dirn292E : RingExpr := dz2n292E
def dirn292P : Lean.Grind.CommRing.Poly := dz2n292P
theorem dirn292_norm : (reflectRing dirn292E).toPoly=dirn292P := dz2n292_norm

def dirn293E : RingExpr := dz2n293E
def dirn293P : Lean.Grind.CommRing.Poly := dz2n293P
theorem dirn293_norm : (reflectRing dirn293E).toPoly=dirn293P := dz2n293_norm

def dirn294E : RingExpr := dz2n294E
def dirn294P : Lean.Grind.CommRing.Poly := dz2n294P
theorem dirn294_norm : (reflectRing dirn294E).toPoly=dirn294P := dz2n294_norm

def dirn295E : RingExpr := dz2n295E
def dirn295P : Lean.Grind.CommRing.Poly := dz2n295P
theorem dirn295_norm : (reflectRing dirn295E).toPoly=dirn295P := dz2n295_norm

def dirn296E : RingExpr := dz2n296E
def dirn296P : Lean.Grind.CommRing.Poly := dz2n296P
theorem dirn296_norm : (reflectRing dirn296E).toPoly=dirn296P := dz2n296_norm

def dirn297E : RingExpr := dz2n297E
def dirn297P : Lean.Grind.CommRing.Poly := dz2n297P
theorem dirn297_norm : (reflectRing dirn297E).toPoly=dirn297P := dz2n297_norm

def dirn298E : RingExpr := dz2n298E
def dirn298P : Lean.Grind.CommRing.Poly := dz2n298P
theorem dirn298_norm : (reflectRing dirn298E).toPoly=dirn298P := dz2n298_norm

def dirn299E : RingExpr := dz2n299E
def dirn299P : Lean.Grind.CommRing.Poly := dz2n299P
theorem dirn299_norm : (reflectRing dirn299E).toPoly=dirn299P := dz2n299_norm

def dirn300E : RingExpr := dz2n300E
def dirn300P : Lean.Grind.CommRing.Poly := dz2n300P
theorem dirn300_norm : (reflectRing dirn300E).toPoly=dirn300P := dz2n300_norm

def dirn301E : RingExpr := dz2n301E
def dirn301P : Lean.Grind.CommRing.Poly := dz2n301P
theorem dirn301_norm : (reflectRing dirn301E).toPoly=dirn301P := dz2n301_norm

def dirn302E : RingExpr := dz2n302E
def dirn302P : Lean.Grind.CommRing.Poly := dz2n302P
theorem dirn302_norm : (reflectRing dirn302E).toPoly=dirn302P := dz2n302_norm

def dirn303E : RingExpr := dz2n303E
def dirn303P : Lean.Grind.CommRing.Poly := dz2n303P
theorem dirn303_norm : (reflectRing dirn303E).toPoly=dirn303P := dz2n303_norm

def dirn304E : RingExpr := dz2n304E
def dirn304P : Lean.Grind.CommRing.Poly := dz2n304P
theorem dirn304_norm : (reflectRing dirn304E).toPoly=dirn304P := dz2n304_norm

def dirn305E : RingExpr := dz2n305E
def dirn305P : Lean.Grind.CommRing.Poly := dz2n305P
theorem dirn305_norm : (reflectRing dirn305E).toPoly=dirn305P := dz2n305_norm

def dirn306E : RingExpr := dz2n306E
def dirn306P : Lean.Grind.CommRing.Poly := dz2n306P
theorem dirn306_norm : (reflectRing dirn306E).toPoly=dirn306P := dz2n306_norm

def dirn307E : RingExpr := dz2n307E
def dirn307P : Lean.Grind.CommRing.Poly := dz2n307P
theorem dirn307_norm : (reflectRing dirn307E).toPoly=dirn307P := dz2n307_norm

def dirn308E : RingExpr := dz2n308E
def dirn308P : Lean.Grind.CommRing.Poly := dz2n308P
theorem dirn308_norm : (reflectRing dirn308E).toPoly=dirn308P := dz2n308_norm

def dirn309E : RingExpr := dz2n309E
def dirn309P : Lean.Grind.CommRing.Poly := dz2n309P
theorem dirn309_norm : (reflectRing dirn309E).toPoly=dirn309P := dz2n309_norm

def dirn310E : RingExpr := dz2n310E
def dirn310P : Lean.Grind.CommRing.Poly := dz2n310P
theorem dirn310_norm : (reflectRing dirn310E).toPoly=dirn310P := dz2n310_norm

def dirn311E : RingExpr := dz2n311E
def dirn311P : Lean.Grind.CommRing.Poly := dz2n311P
theorem dirn311_norm : (reflectRing dirn311E).toPoly=dirn311P := dz2n311_norm

def dirn312E : RingExpr := dz2n312E
def dirn312P : Lean.Grind.CommRing.Poly := dz2n312P
theorem dirn312_norm : (reflectRing dirn312E).toPoly=dirn312P := dz2n312_norm

def dirn313E : RingExpr := dz2n313E
def dirn313P : Lean.Grind.CommRing.Poly := dz2n313P
theorem dirn313_norm : (reflectRing dirn313E).toPoly=dirn313P := dz2n313_norm

def dirn314E : RingExpr := dz2n314E
def dirn314P : Lean.Grind.CommRing.Poly := dz2n314P
theorem dirn314_norm : (reflectRing dirn314E).toPoly=dirn314P := dz2n314_norm

def dirn315E : RingExpr := dz2n315E
def dirn315P : Lean.Grind.CommRing.Poly := dz2n315P
theorem dirn315_norm : (reflectRing dirn315E).toPoly=dirn315P := dz2n315_norm

def dirn316E : RingExpr := dz2n316E
def dirn316P : Lean.Grind.CommRing.Poly := dz2n316P
theorem dirn316_norm : (reflectRing dirn316E).toPoly=dirn316P := dz2n316_norm

def dirn317E : RingExpr := dz2n317E
def dirn317P : Lean.Grind.CommRing.Poly := dz2n317P
theorem dirn317_norm : (reflectRing dirn317E).toPoly=dirn317P := dz2n317_norm

def dirn318E : RingExpr := dz2n318E
def dirn318P : Lean.Grind.CommRing.Poly := dz2n318P
theorem dirn318_norm : (reflectRing dirn318E).toPoly=dirn318P := dz2n318_norm

def dirn319E : RingExpr := dz2n319E
def dirn319P : Lean.Grind.CommRing.Poly := dz2n319P
theorem dirn319_norm : (reflectRing dirn319E).toPoly=dirn319P := dz2n319_norm

def dirn320E : RingExpr := dz2n320E
def dirn320P : Lean.Grind.CommRing.Poly := dz2n320P
theorem dirn320_norm : (reflectRing dirn320E).toPoly=dirn320P := dz2n320_norm

def dirn321E : RingExpr := dz2n321E
def dirn321P : Lean.Grind.CommRing.Poly := dz2n321P
theorem dirn321_norm : (reflectRing dirn321E).toPoly=dirn321P := dz2n321_norm

def dirn322E : RingExpr := dz2n322E
def dirn322P : Lean.Grind.CommRing.Poly := dz2n322P
theorem dirn322_norm : (reflectRing dirn322E).toPoly=dirn322P := dz2n322_norm

def dirn323E : RingExpr := dz2n323E
def dirn323P : Lean.Grind.CommRing.Poly := dz2n323P
theorem dirn323_norm : (reflectRing dirn323E).toPoly=dirn323P := dz2n323_norm

def dirn324E : RingExpr := dz2n324E
def dirn324P : Lean.Grind.CommRing.Poly := dz2n324P
theorem dirn324_norm : (reflectRing dirn324E).toPoly=dirn324P := dz2n324_norm

def dirn325E : RingExpr := dz2n325E
def dirn325P : Lean.Grind.CommRing.Poly := dz2n325P
theorem dirn325_norm : (reflectRing dirn325E).toPoly=dirn325P := dz2n325_norm

def dirn326E : RingExpr := dz2n326E
def dirn326P : Lean.Grind.CommRing.Poly := dz2n326P
theorem dirn326_norm : (reflectRing dirn326E).toPoly=dirn326P := dz2n326_norm

def dirn327E : RingExpr := dz2n327E
def dirn327P : Lean.Grind.CommRing.Poly := dz2n327P
theorem dirn327_norm : (reflectRing dirn327E).toPoly=dirn327P := dz2n327_norm

def dirn328E : RingExpr := dz2n328E
def dirn328P : Lean.Grind.CommRing.Poly := dz2n328P
theorem dirn328_norm : (reflectRing dirn328E).toPoly=dirn328P := dz2n328_norm

def dirn329E : RingExpr := dz2n329E
def dirn329P : Lean.Grind.CommRing.Poly := dz2n329P
theorem dirn329_norm : (reflectRing dirn329E).toPoly=dirn329P := dz2n329_norm

def dirn330E : RingExpr := dz2n330E
def dirn330P : Lean.Grind.CommRing.Poly := dz2n330P
theorem dirn330_norm : (reflectRing dirn330E).toPoly=dirn330P := dz2n330_norm

def dirn331E : RingExpr := dz2n331E
def dirn331P : Lean.Grind.CommRing.Poly := dz2n331P
theorem dirn331_norm : (reflectRing dirn331E).toPoly=dirn331P := dz2n331_norm

def dirn332E : RingExpr := dz2n332E
def dirn332P : Lean.Grind.CommRing.Poly := dz2n332P
theorem dirn332_norm : (reflectRing dirn332E).toPoly=dirn332P := dz2n332_norm

def dirn333E : RingExpr := dz2n333E
def dirn333P : Lean.Grind.CommRing.Poly := dz2n333P
theorem dirn333_norm : (reflectRing dirn333E).toPoly=dirn333P := dz2n333_norm

def dirn334E : RingExpr := dz2n334E
def dirn334P : Lean.Grind.CommRing.Poly := dz2n334P
theorem dirn334_norm : (reflectRing dirn334E).toPoly=dirn334P := dz2n334_norm

def dirn335E : RingExpr := dz2n335E
def dirn335P : Lean.Grind.CommRing.Poly := dz2n335P
theorem dirn335_norm : (reflectRing dirn335E).toPoly=dirn335P := dz2n335_norm

def dirn336E : RingExpr := dz2n336E
def dirn336P : Lean.Grind.CommRing.Poly := dz2n336P
theorem dirn336_norm : (reflectRing dirn336E).toPoly=dirn336P := dz2n336_norm

def dirn337E : RingExpr := dz2n337E
def dirn337P : Lean.Grind.CommRing.Poly := dz2n337P
theorem dirn337_norm : (reflectRing dirn337E).toPoly=dirn337P := dz2n337_norm

def dirn338E : RingExpr := dz2n338E
def dirn338P : Lean.Grind.CommRing.Poly := dz2n338P
theorem dirn338_norm : (reflectRing dirn338E).toPoly=dirn338P := dz2n338_norm

def dirn339E : RingExpr := dz2n339E
def dirn339P : Lean.Grind.CommRing.Poly := dz2n339P
theorem dirn339_norm : (reflectRing dirn339E).toPoly=dirn339P := dz2n339_norm

def dirn340E : RingExpr := dz2n340E
def dirn340P : Lean.Grind.CommRing.Poly := dz2n340P
theorem dirn340_norm : (reflectRing dirn340E).toPoly=dirn340P := dz2n340_norm

def dirn341E : RingExpr := dz2n341E
def dirn341P : Lean.Grind.CommRing.Poly := dz2n341P
theorem dirn341_norm : (reflectRing dirn341E).toPoly=dirn341P := dz2n341_norm

def dirn342E : RingExpr := dz2n342E
def dirn342P : Lean.Grind.CommRing.Poly := dz2n342P
theorem dirn342_norm : (reflectRing dirn342E).toPoly=dirn342P := dz2n342_norm

def dirn343E : RingExpr := dz2n343E
def dirn343P : Lean.Grind.CommRing.Poly := dz2n343P
theorem dirn343_norm : (reflectRing dirn343E).toPoly=dirn343P := dz2n343_norm

def dirn344E : RingExpr := dz2n344E
def dirn344P : Lean.Grind.CommRing.Poly := dz2n344P
theorem dirn344_norm : (reflectRing dirn344E).toPoly=dirn344P := dz2n344_norm

def dirn345E : RingExpr := dz2n345E
def dirn345P : Lean.Grind.CommRing.Poly := dz2n345P
theorem dirn345_norm : (reflectRing dirn345E).toPoly=dirn345P := dz2n345_norm

def dirn346E : RingExpr := dz2n346E
def dirn346P : Lean.Grind.CommRing.Poly := dz2n346P
theorem dirn346_norm : (reflectRing dirn346E).toPoly=dirn346P := dz2n346_norm

def dirn347E : RingExpr := dz2n347E
def dirn347P : Lean.Grind.CommRing.Poly := dz2n347P
theorem dirn347_norm : (reflectRing dirn347E).toPoly=dirn347P := dz2n347_norm

def dirn348E : RingExpr := dz2n348E
def dirn348P : Lean.Grind.CommRing.Poly := dz2n348P
theorem dirn348_norm : (reflectRing dirn348E).toPoly=dirn348P := dz2n348_norm

def dirn349E : RingExpr := dz2n349E
def dirn349P : Lean.Grind.CommRing.Poly := dz2n349P
theorem dirn349_norm : (reflectRing dirn349E).toPoly=dirn349P := dz2n349_norm

def dirn350E : RingExpr := dz2n350E
def dirn350P : Lean.Grind.CommRing.Poly := dz2n350P
theorem dirn350_norm : (reflectRing dirn350E).toPoly=dirn350P := dz2n350_norm

def dirn351E : RingExpr := dz2n351E
def dirn351P : Lean.Grind.CommRing.Poly := dz2n351P
theorem dirn351_norm : (reflectRing dirn351E).toPoly=dirn351P := dz2n351_norm

def dirn352E : RingExpr := dz2n352E
def dirn352P : Lean.Grind.CommRing.Poly := dz2n352P
theorem dirn352_norm : (reflectRing dirn352E).toPoly=dirn352P := dz2n352_norm

def dirn353E : RingExpr := dz2n353E
def dirn353P : Lean.Grind.CommRing.Poly := dz2n353P
theorem dirn353_norm : (reflectRing dirn353E).toPoly=dirn353P := dz2n353_norm

def dirn354E : RingExpr := dz2n354E
def dirn354P : Lean.Grind.CommRing.Poly := dz2n354P
theorem dirn354_norm : (reflectRing dirn354E).toPoly=dirn354P := dz2n354_norm

def dirn355E : RingExpr := dz2n355E
def dirn355P : Lean.Grind.CommRing.Poly := dz2n355P
theorem dirn355_norm : (reflectRing dirn355E).toPoly=dirn355P := dz2n355_norm

def dirn356E : RingExpr := dz2n356E
def dirn356P : Lean.Grind.CommRing.Poly := dz2n356P
theorem dirn356_norm : (reflectRing dirn356E).toPoly=dirn356P := dz2n356_norm

def dirn357E : RingExpr := dz2n357E
def dirn357P : Lean.Grind.CommRing.Poly := dz2n357P
theorem dirn357_norm : (reflectRing dirn357E).toPoly=dirn357P := dz2n357_norm

def dirn358E : RingExpr := dz2n358E
def dirn358P : Lean.Grind.CommRing.Poly := dz2n358P
theorem dirn358_norm : (reflectRing dirn358E).toPoly=dirn358P := dz2n358_norm

def dirn359E : RingExpr := dz2n359E
def dirn359P : Lean.Grind.CommRing.Poly := dz2n359P
theorem dirn359_norm : (reflectRing dirn359E).toPoly=dirn359P := dz2n359_norm

def dirn360E : RingExpr := dz2n360E
def dirn360P : Lean.Grind.CommRing.Poly := dz2n360P
theorem dirn360_norm : (reflectRing dirn360E).toPoly=dirn360P := dz2n360_norm

def dirn361E : RingExpr := dz2n361E
def dirn361P : Lean.Grind.CommRing.Poly := dz2n361P
theorem dirn361_norm : (reflectRing dirn361E).toPoly=dirn361P := dz2n361_norm

def dirn362E : RingExpr := dz2n362E
def dirn362P : Lean.Grind.CommRing.Poly := dz2n362P
theorem dirn362_norm : (reflectRing dirn362E).toPoly=dirn362P := dz2n362_norm

def dirn363E : RingExpr := dz2n363E
def dirn363P : Lean.Grind.CommRing.Poly := dz2n363P
theorem dirn363_norm : (reflectRing dirn363E).toPoly=dirn363P := dz2n363_norm

def dirn364E : RingExpr := dz2n364E
def dirn364P : Lean.Grind.CommRing.Poly := dz2n364P
theorem dirn364_norm : (reflectRing dirn364E).toPoly=dirn364P := dz2n364_norm

def dirn365E : RingExpr := dz2n365E
def dirn365P : Lean.Grind.CommRing.Poly := dz2n365P
theorem dirn365_norm : (reflectRing dirn365E).toPoly=dirn365P := dz2n365_norm

def dirn366E : RingExpr := dz2n366E
def dirn366P : Lean.Grind.CommRing.Poly := dz2n366P
theorem dirn366_norm : (reflectRing dirn366E).toPoly=dirn366P := dz2n366_norm

def dirn367E : RingExpr := dz2n367E
def dirn367P : Lean.Grind.CommRing.Poly := dz2n367P
theorem dirn367_norm : (reflectRing dirn367E).toPoly=dirn367P := dz2n367_norm

def dirn368E : RingExpr := dz2n368E
def dirn368P : Lean.Grind.CommRing.Poly := dz2n368P
theorem dirn368_norm : (reflectRing dirn368E).toPoly=dirn368P := dz2n368_norm

def dirn369E : RingExpr := dz2n369E
def dirn369P : Lean.Grind.CommRing.Poly := dz2n369P
theorem dirn369_norm : (reflectRing dirn369E).toPoly=dirn369P := dz2n369_norm

def dirn370E : RingExpr := dz2n370E
def dirn370P : Lean.Grind.CommRing.Poly := dz2n370P
theorem dirn370_norm : (reflectRing dirn370E).toPoly=dirn370P := dz2n370_norm

def dirn371E : RingExpr := dz2n371E
def dirn371P : Lean.Grind.CommRing.Poly := dz2n371P
theorem dirn371_norm : (reflectRing dirn371E).toPoly=dirn371P := dz2n371_norm

def dirn372E : RingExpr := dz2n372E
def dirn372P : Lean.Grind.CommRing.Poly := dz2n372P
theorem dirn372_norm : (reflectRing dirn372E).toPoly=dirn372P := dz2n372_norm

def dirn373E : RingExpr := dz2n373E
def dirn373P : Lean.Grind.CommRing.Poly := dz2n373P
theorem dirn373_norm : (reflectRing dirn373E).toPoly=dirn373P := dz2n373_norm

def dirn374E : RingExpr := dz2n374E
def dirn374P : Lean.Grind.CommRing.Poly := dz2n374P
theorem dirn374_norm : (reflectRing dirn374E).toPoly=dirn374P := dz2n374_norm

def dirn375E : RingExpr := dz2n375E
def dirn375P : Lean.Grind.CommRing.Poly := dz2n375P
theorem dirn375_norm : (reflectRing dirn375E).toPoly=dirn375P := dz2n375_norm

def dirn376E : RingExpr := dz2n376E
def dirn376P : Lean.Grind.CommRing.Poly := dz2n376P
theorem dirn376_norm : (reflectRing dirn376E).toPoly=dirn376P := dz2n376_norm

def dirn377E : RingExpr := dz2n377E
def dirn377P : Lean.Grind.CommRing.Poly := dz2n377P
theorem dirn377_norm : (reflectRing dirn377E).toPoly=dirn377P := dz2n377_norm

def dirn378E : RingExpr := dz2n378E
def dirn378P : Lean.Grind.CommRing.Poly := dz2n378P
theorem dirn378_norm : (reflectRing dirn378E).toPoly=dirn378P := dz2n378_norm

def dirn379E : RingExpr := dz2n379E
def dirn379P : Lean.Grind.CommRing.Poly := dz2n379P
theorem dirn379_norm : (reflectRing dirn379E).toPoly=dirn379P := dz2n379_norm

def dirn380E : RingExpr := dz2n380E
def dirn380P : Lean.Grind.CommRing.Poly := dz2n380P
theorem dirn380_norm : (reflectRing dirn380E).toPoly=dirn380P := dz2n380_norm

def dirn381E : RingExpr := dz2n381E
def dirn381P : Lean.Grind.CommRing.Poly := dz2n381P
theorem dirn381_norm : (reflectRing dirn381E).toPoly=dirn381P := dz2n381_norm

def dirn382E : RingExpr := dz2n382E
def dirn382P : Lean.Grind.CommRing.Poly := dz2n382P
theorem dirn382_norm : (reflectRing dirn382E).toPoly=dirn382P := dz2n382_norm

def dirn383E : RingExpr := dz2n383E
def dirn383P : Lean.Grind.CommRing.Poly := dz2n383P
theorem dirn383_norm : (reflectRing dirn383E).toPoly=dirn383P := dz2n383_norm

def dirn384E : RingExpr := dz2n384E
def dirn384P : Lean.Grind.CommRing.Poly := dz2n384P
theorem dirn384_norm : (reflectRing dirn384E).toPoly=dirn384P := dz2n384_norm

def dirn385E : RingExpr := dz2n385E
def dirn385P : Lean.Grind.CommRing.Poly := dz2n385P
theorem dirn385_norm : (reflectRing dirn385E).toPoly=dirn385P := dz2n385_norm

def dirn386E : RingExpr := dz2n386E
def dirn386P : Lean.Grind.CommRing.Poly := dz2n386P
theorem dirn386_norm : (reflectRing dirn386E).toPoly=dirn386P := dz2n386_norm

def dirn387E : RingExpr := dz2n387E
def dirn387P : Lean.Grind.CommRing.Poly := dz2n387P
theorem dirn387_norm : (reflectRing dirn387E).toPoly=dirn387P := dz2n387_norm

def dirn388E : RingExpr := dz2n388E
def dirn388P : Lean.Grind.CommRing.Poly := dz2n388P
theorem dirn388_norm : (reflectRing dirn388E).toPoly=dirn388P := dz2n388_norm

def dirn389E : RingExpr := dz2n389E
def dirn389P : Lean.Grind.CommRing.Poly := dz2n389P
theorem dirn389_norm : (reflectRing dirn389E).toPoly=dirn389P := dz2n389_norm

def dirn390E : RingExpr := dz2n390E
def dirn390P : Lean.Grind.CommRing.Poly := dz2n390P
theorem dirn390_norm : (reflectRing dirn390E).toPoly=dirn390P := dz2n390_norm

def dirn391E : RingExpr := dz2n391E
def dirn391P : Lean.Grind.CommRing.Poly := dz2n391P
theorem dirn391_norm : (reflectRing dirn391E).toPoly=dirn391P := dz2n391_norm

def dirn392E : RingExpr := dz2n392E
def dirn392P : Lean.Grind.CommRing.Poly := dz2n392P
theorem dirn392_norm : (reflectRing dirn392E).toPoly=dirn392P := dz2n392_norm

def dirn393E : RingExpr := dz2n393E
def dirn393P : Lean.Grind.CommRing.Poly := dz2n393P
theorem dirn393_norm : (reflectRing dirn393E).toPoly=dirn393P := dz2n393_norm

def dirn394E : RingExpr := dz2n394E
def dirn394P : Lean.Grind.CommRing.Poly := dz2n394P
theorem dirn394_norm : (reflectRing dirn394E).toPoly=dirn394P := dz2n394_norm

def dirn395E : RingExpr := dz2n395E
def dirn395P : Lean.Grind.CommRing.Poly := dz2n395P
theorem dirn395_norm : (reflectRing dirn395E).toPoly=dirn395P := dz2n395_norm

def dirn396E : RingExpr := dz2n396E
def dirn396P : Lean.Grind.CommRing.Poly := dz2n396P
theorem dirn396_norm : (reflectRing dirn396E).toPoly=dirn396P := dz2n396_norm

def dirn397E : RingExpr := dz2n397E
def dirn397P : Lean.Grind.CommRing.Poly := dz2n397P
theorem dirn397_norm : (reflectRing dirn397E).toPoly=dirn397P := dz2n397_norm

def dirn398E : RingExpr := dz2n398E
def dirn398P : Lean.Grind.CommRing.Poly := dz2n398P
theorem dirn398_norm : (reflectRing dirn398E).toPoly=dirn398P := dz2n398_norm

def dirn399E : RingExpr := dz2n399E
def dirn399P : Lean.Grind.CommRing.Poly := dz2n399P
theorem dirn399_norm : (reflectRing dirn399E).toPoly=dirn399P := dz2n399_norm

def dirn400E : RingExpr := dz2n400E
def dirn400P : Lean.Grind.CommRing.Poly := dz2n400P
theorem dirn400_norm : (reflectRing dirn400E).toPoly=dirn400P := dz2n400_norm

def dirn401E : RingExpr := dz2n401E
def dirn401P : Lean.Grind.CommRing.Poly := dz2n401P
theorem dirn401_norm : (reflectRing dirn401E).toPoly=dirn401P := dz2n401_norm

def dirn402E : RingExpr := dz2n402E
def dirn402P : Lean.Grind.CommRing.Poly := dz2n402P
theorem dirn402_norm : (reflectRing dirn402E).toPoly=dirn402P := dz2n402_norm

def dirn403E : RingExpr := dz2n403E
def dirn403P : Lean.Grind.CommRing.Poly := dz2n403P
theorem dirn403_norm : (reflectRing dirn403E).toPoly=dirn403P := dz2n403_norm

def dirn404E : RingExpr := dz2n404E
def dirn404P : Lean.Grind.CommRing.Poly := dz2n404P
theorem dirn404_norm : (reflectRing dirn404E).toPoly=dirn404P := dz2n404_norm

def dirn405E : RingExpr := dz2n405E
def dirn405P : Lean.Grind.CommRing.Poly := dz2n405P
theorem dirn405_norm : (reflectRing dirn405E).toPoly=dirn405P := dz2n405_norm

def dirn406E : RingExpr := dz2n406E
def dirn406P : Lean.Grind.CommRing.Poly := dz2n406P
theorem dirn406_norm : (reflectRing dirn406E).toPoly=dirn406P := dz2n406_norm

def dirn407E : RingExpr := dz2n407E
def dirn407P : Lean.Grind.CommRing.Poly := dz2n407P
theorem dirn407_norm : (reflectRing dirn407E).toPoly=dirn407P := dz2n407_norm

def dirn408E : RingExpr := dz2n408E
def dirn408P : Lean.Grind.CommRing.Poly := dz2n408P
theorem dirn408_norm : (reflectRing dirn408E).toPoly=dirn408P := dz2n408_norm

def dirn409E : RingExpr := dz2n409E
def dirn409P : Lean.Grind.CommRing.Poly := dz2n409P
theorem dirn409_norm : (reflectRing dirn409E).toPoly=dirn409P := dz2n409_norm

def dirn410E : RingExpr := dz2n410E
def dirn410P : Lean.Grind.CommRing.Poly := dz2n410P
theorem dirn410_norm : (reflectRing dirn410E).toPoly=dirn410P := dz2n410_norm

def dirn411E : RingExpr := dz2n411E
def dirn411P : Lean.Grind.CommRing.Poly := dz2n411P
theorem dirn411_norm : (reflectRing dirn411E).toPoly=dirn411P := dz2n411_norm

def dirn412E : RingExpr := dz2n412E
def dirn412P : Lean.Grind.CommRing.Poly := dz2n412P
theorem dirn412_norm : (reflectRing dirn412E).toPoly=dirn412P := dz2n412_norm

def dirn413E : RingExpr := dz2n413E
def dirn413P : Lean.Grind.CommRing.Poly := dz2n413P
theorem dirn413_norm : (reflectRing dirn413E).toPoly=dirn413P := dz2n413_norm

def dirn414E : RingExpr := dz2n414E
def dirn414P : Lean.Grind.CommRing.Poly := dz2n414P
theorem dirn414_norm : (reflectRing dirn414E).toPoly=dirn414P := dz2n414_norm

def dirn415E : RingExpr := dz2n415E
def dirn415P : Lean.Grind.CommRing.Poly := dz2n415P
theorem dirn415_norm : (reflectRing dirn415E).toPoly=dirn415P := dz2n415_norm

def dirn416E : RingExpr := dz2n416E
def dirn416P : Lean.Grind.CommRing.Poly := dz2n416P
theorem dirn416_norm : (reflectRing dirn416E).toPoly=dirn416P := dz2n416_norm

def dirn417E : RingExpr := dz2n417E
def dirn417P : Lean.Grind.CommRing.Poly := dz2n417P
theorem dirn417_norm : (reflectRing dirn417E).toPoly=dirn417P := dz2n417_norm

def dirn418E : RingExpr := dz2n418E
def dirn418P : Lean.Grind.CommRing.Poly := dz2n418P
theorem dirn418_norm : (reflectRing dirn418E).toPoly=dirn418P := dz2n418_norm

def dirn419E : RingExpr := dz2n419E
def dirn419P : Lean.Grind.CommRing.Poly := dz2n419P
theorem dirn419_norm : (reflectRing dirn419E).toPoly=dirn419P := dz2n419_norm

def dirn420E : RingExpr := dz2n420E
def dirn420P : Lean.Grind.CommRing.Poly := dz2n420P
theorem dirn420_norm : (reflectRing dirn420E).toPoly=dirn420P := dz2n420_norm

def dirn421E : RingExpr := dz2n421E
def dirn421P : Lean.Grind.CommRing.Poly := dz2n421P
theorem dirn421_norm : (reflectRing dirn421E).toPoly=dirn421P := dz2n421_norm

def dirn422E : RingExpr := dz2n422E
def dirn422P : Lean.Grind.CommRing.Poly := dz2n422P
theorem dirn422_norm : (reflectRing dirn422E).toPoly=dirn422P := dz2n422_norm

def dirn423E : RingExpr := dz2n423E
def dirn423P : Lean.Grind.CommRing.Poly := dz2n423P
theorem dirn423_norm : (reflectRing dirn423E).toPoly=dirn423P := dz2n423_norm

def dirn424E : RingExpr := dz2n424E
def dirn424P : Lean.Grind.CommRing.Poly := dz2n424P
theorem dirn424_norm : (reflectRing dirn424E).toPoly=dirn424P := dz2n424_norm

def dirn425E : RingExpr := dz2n425E
def dirn425P : Lean.Grind.CommRing.Poly := dz2n425P
theorem dirn425_norm : (reflectRing dirn425E).toPoly=dirn425P := dz2n425_norm

def dirn426E : RingExpr := dz2n426E
def dirn426P : Lean.Grind.CommRing.Poly := dz2n426P
theorem dirn426_norm : (reflectRing dirn426E).toPoly=dirn426P := dz2n426_norm

def dirn427E : RingExpr := dz2n427E
def dirn427P : Lean.Grind.CommRing.Poly := dz2n427P
theorem dirn427_norm : (reflectRing dirn427E).toPoly=dirn427P := dz2n427_norm

def dirn428E : RingExpr := dz2n428E
def dirn428P : Lean.Grind.CommRing.Poly := dz2n428P
theorem dirn428_norm : (reflectRing dirn428E).toPoly=dirn428P := dz2n428_norm

def dirn429E : RingExpr := dz2n429E
def dirn429P : Lean.Grind.CommRing.Poly := dz2n429P
theorem dirn429_norm : (reflectRing dirn429E).toPoly=dirn429P := dz2n429_norm

def dirn430E : RingExpr := dz2n430E
def dirn430P : Lean.Grind.CommRing.Poly := dz2n430P
theorem dirn430_norm : (reflectRing dirn430E).toPoly=dirn430P := dz2n430_norm

def dirn431E : RingExpr := dz2n431E
def dirn431P : Lean.Grind.CommRing.Poly := dz2n431P
theorem dirn431_norm : (reflectRing dirn431E).toPoly=dirn431P := dz2n431_norm

def dirn432E : RingExpr := dz2n432E
def dirn432P : Lean.Grind.CommRing.Poly := dz2n432P
theorem dirn432_norm : (reflectRing dirn432E).toPoly=dirn432P := dz2n432_norm

def dirn433E : RingExpr := dz2n433E
def dirn433P : Lean.Grind.CommRing.Poly := dz2n433P
theorem dirn433_norm : (reflectRing dirn433E).toPoly=dirn433P := dz2n433_norm

def dirn434E : RingExpr := dz2n434E
def dirn434P : Lean.Grind.CommRing.Poly := dz2n434P
theorem dirn434_norm : (reflectRing dirn434E).toPoly=dirn434P := dz2n434_norm

def dirn435E : RingExpr := dz2n435E
def dirn435P : Lean.Grind.CommRing.Poly := dz2n435P
theorem dirn435_norm : (reflectRing dirn435E).toPoly=dirn435P := dz2n435_norm

def dirn436E : RingExpr := dz2n436E
def dirn436P : Lean.Grind.CommRing.Poly := dz2n436P
theorem dirn436_norm : (reflectRing dirn436E).toPoly=dirn436P := dz2n436_norm

def dirn437E : RingExpr := dz2n437E
def dirn437P : Lean.Grind.CommRing.Poly := dz2n437P
theorem dirn437_norm : (reflectRing dirn437E).toPoly=dirn437P := dz2n437_norm

def dirn438E : RingExpr := dz2n438E
def dirn438P : Lean.Grind.CommRing.Poly := dz2n438P
theorem dirn438_norm : (reflectRing dirn438E).toPoly=dirn438P := dz2n438_norm

def dirn439E : RingExpr := dz2n439E
def dirn439P : Lean.Grind.CommRing.Poly := dz2n439P
theorem dirn439_norm : (reflectRing dirn439E).toPoly=dirn439P := dz2n439_norm

def dirn440E : RingExpr := dz2n440E
def dirn440P : Lean.Grind.CommRing.Poly := dz2n440P
theorem dirn440_norm : (reflectRing dirn440E).toPoly=dirn440P := dz2n440_norm

def dirn441E : RingExpr := dz2n441E
def dirn441P : Lean.Grind.CommRing.Poly := dz2n441P
theorem dirn441_norm : (reflectRing dirn441E).toPoly=dirn441P := dz2n441_norm

def dirn442E : RingExpr := dz2n442E
def dirn442P : Lean.Grind.CommRing.Poly := dz2n442P
theorem dirn442_norm : (reflectRing dirn442E).toPoly=dirn442P := dz2n442_norm

def dirn443E : RingExpr := dz2n443E
def dirn443P : Lean.Grind.CommRing.Poly := dz2n443P
theorem dirn443_norm : (reflectRing dirn443E).toPoly=dirn443P := dz2n443_norm

def dirn444E : RingExpr := dz2n444E
def dirn444P : Lean.Grind.CommRing.Poly := dz2n444P
theorem dirn444_norm : (reflectRing dirn444E).toPoly=dirn444P := dz2n444_norm

def dirn445E : RingExpr := dz2n445E
def dirn445P : Lean.Grind.CommRing.Poly := dz2n445P
theorem dirn445_norm : (reflectRing dirn445E).toPoly=dirn445P := dz2n445_norm

def dirn446E : RingExpr := dz2n446E
def dirn446P : Lean.Grind.CommRing.Poly := dz2n446P
theorem dirn446_norm : (reflectRing dirn446E).toPoly=dirn446P := dz2n446_norm

def dirn447E : RingExpr := dz2n447E
def dirn447P : Lean.Grind.CommRing.Poly := dz2n447P
theorem dirn447_norm : (reflectRing dirn447E).toPoly=dirn447P := dz2n447_norm

def dirn448E : RingExpr := dz2n448E
def dirn448P : Lean.Grind.CommRing.Poly := dz2n448P
theorem dirn448_norm : (reflectRing dirn448E).toPoly=dirn448P := dz2n448_norm

def dirn449E : RingExpr := dz2n449E
def dirn449P : Lean.Grind.CommRing.Poly := dz2n449P
theorem dirn449_norm : (reflectRing dirn449E).toPoly=dirn449P := dz2n449_norm

def dirn450E : RingExpr := dz2n450E
def dirn450P : Lean.Grind.CommRing.Poly := dz2n450P
theorem dirn450_norm : (reflectRing dirn450E).toPoly=dirn450P := dz2n450_norm

def dirn451E : RingExpr := dz2n451E
def dirn451P : Lean.Grind.CommRing.Poly := dz2n451P
theorem dirn451_norm : (reflectRing dirn451E).toPoly=dirn451P := dz2n451_norm

def dirn452E : RingExpr := dz2n452E
def dirn452P : Lean.Grind.CommRing.Poly := dz2n452P
theorem dirn452_norm : (reflectRing dirn452E).toPoly=dirn452P := dz2n452_norm

def dirn453E : RingExpr := dz2n453E
def dirn453P : Lean.Grind.CommRing.Poly := dz2n453P
theorem dirn453_norm : (reflectRing dirn453E).toPoly=dirn453P := dz2n453_norm

def dirn454E : RingExpr := dz2n454E
def dirn454P : Lean.Grind.CommRing.Poly := dz2n454P
theorem dirn454_norm : (reflectRing dirn454E).toPoly=dirn454P := dz2n454_norm

def dirn455E : RingExpr := dz2n455E
def dirn455P : Lean.Grind.CommRing.Poly := dz2n455P
theorem dirn455_norm : (reflectRing dirn455E).toPoly=dirn455P := dz2n455_norm

def dirn456E : RingExpr := dz2n456E
def dirn456P : Lean.Grind.CommRing.Poly := dz2n456P
theorem dirn456_norm : (reflectRing dirn456E).toPoly=dirn456P := dz2n456_norm

def dirn457E : RingExpr := dz2n457E
def dirn457P : Lean.Grind.CommRing.Poly := dz2n457P
theorem dirn457_norm : (reflectRing dirn457E).toPoly=dirn457P := dz2n457_norm

def dirn458E : RingExpr := dz2n458E
def dirn458P : Lean.Grind.CommRing.Poly := dz2n458P
theorem dirn458_norm : (reflectRing dirn458E).toPoly=dirn458P := dz2n458_norm

def dirn459E : RingExpr := dz2n459E
def dirn459P : Lean.Grind.CommRing.Poly := dz2n459P
theorem dirn459_norm : (reflectRing dirn459E).toPoly=dirn459P := dz2n459_norm

def dirn460E : RingExpr := dz2n460E
def dirn460P : Lean.Grind.CommRing.Poly := dz2n460P
theorem dirn460_norm : (reflectRing dirn460E).toPoly=dirn460P := dz2n460_norm

def dirn461E : RingExpr := dz2n461E
def dirn461P : Lean.Grind.CommRing.Poly := dz2n461P
theorem dirn461_norm : (reflectRing dirn461E).toPoly=dirn461P := dz2n461_norm

def dirn462E : RingExpr := dz2n462E
def dirn462P : Lean.Grind.CommRing.Poly := dz2n462P
theorem dirn462_norm : (reflectRing dirn462E).toPoly=dirn462P := dz2n462_norm

def dirn463E : RingExpr := dz2n463E
def dirn463P : Lean.Grind.CommRing.Poly := dz2n463P
theorem dirn463_norm : (reflectRing dirn463E).toPoly=dirn463P := dz2n463_norm

def dirn464E : RingExpr := dz2n464E
def dirn464P : Lean.Grind.CommRing.Poly := dz2n464P
theorem dirn464_norm : (reflectRing dirn464E).toPoly=dirn464P := dz2n464_norm

def dirn465E : RingExpr := dz2n465E
def dirn465P : Lean.Grind.CommRing.Poly := dz2n465P
theorem dirn465_norm : (reflectRing dirn465E).toPoly=dirn465P := dz2n465_norm

def dirn466E : RingExpr := dz2n466E
def dirn466P : Lean.Grind.CommRing.Poly := dz2n466P
theorem dirn466_norm : (reflectRing dirn466E).toPoly=dirn466P := dz2n466_norm

def dirn467E : RingExpr := dz2n467E
def dirn467P : Lean.Grind.CommRing.Poly := dz2n467P
theorem dirn467_norm : (reflectRing dirn467E).toPoly=dirn467P := dz2n467_norm

def dirn468E : RingExpr := dz2n468E
def dirn468P : Lean.Grind.CommRing.Poly := dz2n468P
theorem dirn468_norm : (reflectRing dirn468E).toPoly=dirn468P := dz2n468_norm

def dirn469E : RingExpr := dz2n469E
def dirn469P : Lean.Grind.CommRing.Poly := dz2n469P
theorem dirn469_norm : (reflectRing dirn469E).toPoly=dirn469P := dz2n469_norm

def dirn470E : RingExpr := dz2n470E
def dirn470P : Lean.Grind.CommRing.Poly := dz2n470P
theorem dirn470_norm : (reflectRing dirn470E).toPoly=dirn470P := dz2n470_norm

def dirn471E : RingExpr := dz2n471E
def dirn471P : Lean.Grind.CommRing.Poly := dz2n471P
theorem dirn471_norm : (reflectRing dirn471E).toPoly=dirn471P := dz2n471_norm

def dirn472E : RingExpr := dz2n472E
def dirn472P : Lean.Grind.CommRing.Poly := dz2n472P
theorem dirn472_norm : (reflectRing dirn472E).toPoly=dirn472P := dz2n472_norm

def dirn473E : RingExpr := dz2n473E
def dirn473P : Lean.Grind.CommRing.Poly := dz2n473P
theorem dirn473_norm : (reflectRing dirn473E).toPoly=dirn473P := dz2n473_norm

def dirn474E : RingExpr := dz2n474E
def dirn474P : Lean.Grind.CommRing.Poly := dz2n474P
theorem dirn474_norm : (reflectRing dirn474E).toPoly=dirn474P := dz2n474_norm

def dirn475E : RingExpr := dz2n475E
def dirn475P : Lean.Grind.CommRing.Poly := dz2n475P
theorem dirn475_norm : (reflectRing dirn475E).toPoly=dirn475P := dz2n475_norm

def dirn476E : RingExpr := dz2n476E
def dirn476P : Lean.Grind.CommRing.Poly := dz2n476P
theorem dirn476_norm : (reflectRing dirn476E).toPoly=dirn476P := dz2n476_norm

def dirn477E : RingExpr := dz2n477E
def dirn477P : Lean.Grind.CommRing.Poly := dz2n477P
theorem dirn477_norm : (reflectRing dirn477E).toPoly=dirn477P := dz2n477_norm

def dirn478E : RingExpr := dz2n478E
def dirn478P : Lean.Grind.CommRing.Poly := dz2n478P
theorem dirn478_norm : (reflectRing dirn478E).toPoly=dirn478P := dz2n478_norm

def dirn479E : RingExpr := dz2n479E
def dirn479P : Lean.Grind.CommRing.Poly := dz2n479P
theorem dirn479_norm : (reflectRing dirn479E).toPoly=dirn479P := dz2n479_norm

def dirn480E : RingExpr := dz2n480E
def dirn480P : Lean.Grind.CommRing.Poly := dz2n480P
theorem dirn480_norm : (reflectRing dirn480E).toPoly=dirn480P := dz2n480_norm

def dirn481E : RingExpr := dz2n481E
def dirn481P : Lean.Grind.CommRing.Poly := dz2n481P
theorem dirn481_norm : (reflectRing dirn481E).toPoly=dirn481P := dz2n481_norm

def dirn482E : RingExpr := dz2n482E
def dirn482P : Lean.Grind.CommRing.Poly := dz2n482P
theorem dirn482_norm : (reflectRing dirn482E).toPoly=dirn482P := dz2n482_norm

def dirn483E : RingExpr := dz2n483E
def dirn483P : Lean.Grind.CommRing.Poly := dz2n483P
theorem dirn483_norm : (reflectRing dirn483E).toPoly=dirn483P := dz2n483_norm

def dirn484E : RingExpr := dz2n484E
def dirn484P : Lean.Grind.CommRing.Poly := dz2n484P
theorem dirn484_norm : (reflectRing dirn484E).toPoly=dirn484P := dz2n484_norm

def dirn485E : RingExpr := dz2n485E
def dirn485P : Lean.Grind.CommRing.Poly := dz2n485P
theorem dirn485_norm : (reflectRing dirn485E).toPoly=dirn485P := dz2n485_norm

def dirn486E : RingExpr := dz2n486E
def dirn486P : Lean.Grind.CommRing.Poly := dz2n486P
theorem dirn486_norm : (reflectRing dirn486E).toPoly=dirn486P := dz2n486_norm

def dirn487E : RingExpr := dz2n487E
def dirn487P : Lean.Grind.CommRing.Poly := dz2n487P
theorem dirn487_norm : (reflectRing dirn487E).toPoly=dirn487P := dz2n487_norm

def dirn488E : RingExpr := dz2n488E
def dirn488P : Lean.Grind.CommRing.Poly := dz2n488P
theorem dirn488_norm : (reflectRing dirn488E).toPoly=dirn488P := dz2n488_norm

def dirn489E : RingExpr := dz2n489E
def dirn489P : Lean.Grind.CommRing.Poly := dz2n489P
theorem dirn489_norm : (reflectRing dirn489E).toPoly=dirn489P := dz2n489_norm

def dirn490E : RingExpr := dz2n490E
def dirn490P : Lean.Grind.CommRing.Poly := dz2n490P
theorem dirn490_norm : (reflectRing dirn490E).toPoly=dirn490P := dz2n490_norm

def dirn491E : RingExpr := dz2n491E
def dirn491P : Lean.Grind.CommRing.Poly := dz2n491P
theorem dirn491_norm : (reflectRing dirn491E).toPoly=dirn491P := dz2n491_norm

def dirn492E : RingExpr := dz2n492E
def dirn492P : Lean.Grind.CommRing.Poly := dz2n492P
theorem dirn492_norm : (reflectRing dirn492E).toPoly=dirn492P := dz2n492_norm

def dirn493E : RingExpr := dz2n493E
def dirn493P : Lean.Grind.CommRing.Poly := dz2n493P
theorem dirn493_norm : (reflectRing dirn493E).toPoly=dirn493P := dz2n493_norm

def dirn494E : RingExpr := dz2n494E
def dirn494P : Lean.Grind.CommRing.Poly := dz2n494P
theorem dirn494_norm : (reflectRing dirn494E).toPoly=dirn494P := dz2n494_norm

def dirn495E : RingExpr := dz2n495E
def dirn495P : Lean.Grind.CommRing.Poly := dz2n495P
theorem dirn495_norm : (reflectRing dirn495E).toPoly=dirn495P := dz2n495_norm

def dirn496E : RingExpr := dz2n496E
def dirn496P : Lean.Grind.CommRing.Poly := dz2n496P
theorem dirn496_norm : (reflectRing dirn496E).toPoly=dirn496P := dz2n496_norm

def dirn497E : RingExpr := dz2n497E
def dirn497P : Lean.Grind.CommRing.Poly := dz2n497P
theorem dirn497_norm : (reflectRing dirn497E).toPoly=dirn497P := dz2n497_norm

def dirn498E : RingExpr := dz2n498E
def dirn498P : Lean.Grind.CommRing.Poly := dz2n498P
theorem dirn498_norm : (reflectRing dirn498E).toPoly=dirn498P := dz2n498_norm

def dirn499E : RingExpr := dz2n499E
def dirn499P : Lean.Grind.CommRing.Poly := dz2n499P
theorem dirn499_norm : (reflectRing dirn499E).toPoly=dirn499P := dz2n499_norm

def dirn500E : RingExpr := dz2n500E
def dirn500P : Lean.Grind.CommRing.Poly := dz2n500P
theorem dirn500_norm : (reflectRing dirn500E).toPoly=dirn500P := dz2n500_norm

def dirn501E : RingExpr := dz2n501E
def dirn501P : Lean.Grind.CommRing.Poly := dz2n501P
theorem dirn501_norm : (reflectRing dirn501E).toPoly=dirn501P := dz2n501_norm

def dirn502E : RingExpr := dz2n502E
def dirn502P : Lean.Grind.CommRing.Poly := dz2n502P
theorem dirn502_norm : (reflectRing dirn502E).toPoly=dirn502P := dz2n502_norm

def dirn503E : RingExpr := dz2n503E
def dirn503P : Lean.Grind.CommRing.Poly := dz2n503P
theorem dirn503_norm : (reflectRing dirn503E).toPoly=dirn503P := dz2n503_norm

def dirn504E : RingExpr := dz2n504E
def dirn504P : Lean.Grind.CommRing.Poly := dz2n504P
theorem dirn504_norm : (reflectRing dirn504E).toPoly=dirn504P := dz2n504_norm

def dirn505E : RingExpr := dz2n505E
def dirn505P : Lean.Grind.CommRing.Poly := dz2n505P
theorem dirn505_norm : (reflectRing dirn505E).toPoly=dirn505P := dz2n505_norm

def dirn506E : RingExpr := dz2n506E
def dirn506P : Lean.Grind.CommRing.Poly := dz2n506P
theorem dirn506_norm : (reflectRing dirn506E).toPoly=dirn506P := dz2n506_norm

def dirn507E : RingExpr := dz2n507E
def dirn507P : Lean.Grind.CommRing.Poly := dz2n507P
theorem dirn507_norm : (reflectRing dirn507E).toPoly=dirn507P := dz2n507_norm

def dirn508E : RingExpr := dz2n508E
def dirn508P : Lean.Grind.CommRing.Poly := dz2n508P
theorem dirn508_norm : (reflectRing dirn508E).toPoly=dirn508P := dz2n508_norm

def dirn509E : RingExpr := dz2n509E
def dirn509P : Lean.Grind.CommRing.Poly := dz2n509P
theorem dirn509_norm : (reflectRing dirn509E).toPoly=dirn509P := dz2n509_norm

def dirn510E : RingExpr := dz2n510E
def dirn510P : Lean.Grind.CommRing.Poly := dz2n510P
theorem dirn510_norm : (reflectRing dirn510E).toPoly=dirn510P := dz2n510_norm

def dirn511E : RingExpr := dz2n511E
def dirn511P : Lean.Grind.CommRing.Poly := dz2n511P
theorem dirn511_norm : (reflectRing dirn511E).toPoly=dirn511P := dz2n511_norm

def dirn512E : RingExpr := dz2n512E
def dirn512P : Lean.Grind.CommRing.Poly := dz2n512P
theorem dirn512_norm : (reflectRing dirn512E).toPoly=dirn512P := dz2n512_norm

def dirn513E : RingExpr := dz2n513E
def dirn513P : Lean.Grind.CommRing.Poly := dz2n513P
theorem dirn513_norm : (reflectRing dirn513E).toPoly=dirn513P := dz2n513_norm

def dirn514E : RingExpr := dz2n514E
def dirn514P : Lean.Grind.CommRing.Poly := dz2n514P
theorem dirn514_norm : (reflectRing dirn514E).toPoly=dirn514P := dz2n514_norm

def dirn515E : RingExpr := dz2n515E
def dirn515P : Lean.Grind.CommRing.Poly := dz2n515P
theorem dirn515_norm : (reflectRing dirn515E).toPoly=dirn515P := dz2n515_norm

def dirn516E : RingExpr := dz2n516E
def dirn516P : Lean.Grind.CommRing.Poly := dz2n516P
theorem dirn516_norm : (reflectRing dirn516E).toPoly=dirn516P := dz2n516_norm

def dirn517E : RingExpr := dz2n517E
def dirn517P : Lean.Grind.CommRing.Poly := dz2n517P
theorem dirn517_norm : (reflectRing dirn517E).toPoly=dirn517P := dz2n517_norm

def dirn518E : RingExpr := dz2n518E
def dirn518P : Lean.Grind.CommRing.Poly := dz2n518P
theorem dirn518_norm : (reflectRing dirn518E).toPoly=dirn518P := dz2n518_norm

def dirn519E : RingExpr := dz2n519E
def dirn519P : Lean.Grind.CommRing.Poly := dz2n519P
theorem dirn519_norm : (reflectRing dirn519E).toPoly=dirn519P := dz2n519_norm

def dirn520E : RingExpr := dz2n520E
def dirn520P : Lean.Grind.CommRing.Poly := dz2n520P
theorem dirn520_norm : (reflectRing dirn520E).toPoly=dirn520P := dz2n520_norm

def dirn521E : RingExpr := dz2n521E
def dirn521P : Lean.Grind.CommRing.Poly := dz2n521P
theorem dirn521_norm : (reflectRing dirn521E).toPoly=dirn521P := dz2n521_norm

def dirn522E : RingExpr := dz2n522E
def dirn522P : Lean.Grind.CommRing.Poly := dz2n522P
theorem dirn522_norm : (reflectRing dirn522E).toPoly=dirn522P := dz2n522_norm

def dirn523E : RingExpr := dz2n523E
def dirn523P : Lean.Grind.CommRing.Poly := dz2n523P
theorem dirn523_norm : (reflectRing dirn523E).toPoly=dirn523P := dz2n523_norm

def dirn524E : RingExpr := dz2n524E
def dirn524P : Lean.Grind.CommRing.Poly := dz2n524P
theorem dirn524_norm : (reflectRing dirn524E).toPoly=dirn524P := dz2n524_norm

def dirn525E : RingExpr := dz2n525E
def dirn525P : Lean.Grind.CommRing.Poly := dz2n525P
theorem dirn525_norm : (reflectRing dirn525E).toPoly=dirn525P := dz2n525_norm

def dirn526E : RingExpr := dz2n526E
def dirn526P : Lean.Grind.CommRing.Poly := dz2n526P
theorem dirn526_norm : (reflectRing dirn526E).toPoly=dirn526P := dz2n526_norm

def dirn527E : RingExpr := dz2n527E
def dirn527P : Lean.Grind.CommRing.Poly := dz2n527P
theorem dirn527_norm : (reflectRing dirn527E).toPoly=dirn527P := dz2n527_norm

def dirn528E : RingExpr := dz2n528E
def dirn528P : Lean.Grind.CommRing.Poly := dz2n528P
theorem dirn528_norm : (reflectRing dirn528E).toPoly=dirn528P := dz2n528_norm

def dirn529E : RingExpr := dz2n529E
def dirn529P : Lean.Grind.CommRing.Poly := dz2n529P
theorem dirn529_norm : (reflectRing dirn529E).toPoly=dirn529P := dz2n529_norm

def dirn530E : RingExpr := dz2n530E
def dirn530P : Lean.Grind.CommRing.Poly := dz2n530P
theorem dirn530_norm : (reflectRing dirn530E).toPoly=dirn530P := dz2n530_norm

def dirn531E : RingExpr := dz2n531E
def dirn531P : Lean.Grind.CommRing.Poly := dz2n531P
theorem dirn531_norm : (reflectRing dirn531E).toPoly=dirn531P := dz2n531_norm

def dirn532E : RingExpr := dz2n532E
def dirn532P : Lean.Grind.CommRing.Poly := dz2n532P
theorem dirn532_norm : (reflectRing dirn532E).toPoly=dirn532P := dz2n532_norm

def dirn533E : RingExpr := dz2n533E
def dirn533P : Lean.Grind.CommRing.Poly := dz2n533P
theorem dirn533_norm : (reflectRing dirn533E).toPoly=dirn533P := dz2n533_norm

def dirn534E : RingExpr := dz2n534E
def dirn534P : Lean.Grind.CommRing.Poly := dz2n534P
theorem dirn534_norm : (reflectRing dirn534E).toPoly=dirn534P := dz2n534_norm

def dirn535E : RingExpr := dz2n535E
def dirn535P : Lean.Grind.CommRing.Poly := dz2n535P
theorem dirn535_norm : (reflectRing dirn535E).toPoly=dirn535P := dz2n535_norm

def dirn536E : RingExpr := dz2n536E
def dirn536P : Lean.Grind.CommRing.Poly := dz2n536P
theorem dirn536_norm : (reflectRing dirn536E).toPoly=dirn536P := dz2n536_norm

def dirn537E : RingExpr := dz2n537E
def dirn537P : Lean.Grind.CommRing.Poly := dz2n537P
theorem dirn537_norm : (reflectRing dirn537E).toPoly=dirn537P := dz2n537_norm

def dirn538E : RingExpr := dz2n538E
def dirn538P : Lean.Grind.CommRing.Poly := dz2n538P
theorem dirn538_norm : (reflectRing dirn538E).toPoly=dirn538P := dz2n538_norm

def dirn539E : RingExpr := dz2n539E
def dirn539P : Lean.Grind.CommRing.Poly := dz2n539P
theorem dirn539_norm : (reflectRing dirn539E).toPoly=dirn539P := dz2n539_norm

def dirn540E : RingExpr := dz2n540E
def dirn540P : Lean.Grind.CommRing.Poly := dz2n540P
theorem dirn540_norm : (reflectRing dirn540E).toPoly=dirn540P := dz2n540_norm

def dirn541E : RingExpr := dz2n541E
def dirn541P : Lean.Grind.CommRing.Poly := dz2n541P
theorem dirn541_norm : (reflectRing dirn541E).toPoly=dirn541P := dz2n541_norm

def dirn542E : RingExpr := dz2n542E
def dirn542P : Lean.Grind.CommRing.Poly := dz2n542P
theorem dirn542_norm : (reflectRing dirn542E).toPoly=dirn542P := dz2n542_norm

def dirn543E : RingExpr := dz2n543E
def dirn543P : Lean.Grind.CommRing.Poly := dz2n543P
theorem dirn543_norm : (reflectRing dirn543E).toPoly=dirn543P := dz2n543_norm

def dirn544E : RingExpr := dz2n544E
def dirn544P : Lean.Grind.CommRing.Poly := dz2n544P
theorem dirn544_norm : (reflectRing dirn544E).toPoly=dirn544P := dz2n544_norm

def dirn545E : RingExpr := dz2n545E
def dirn545P : Lean.Grind.CommRing.Poly := dz2n545P
theorem dirn545_norm : (reflectRing dirn545E).toPoly=dirn545P := dz2n545_norm

def dirn546E : RingExpr := dz2n546E
def dirn546P : Lean.Grind.CommRing.Poly := dz2n546P
theorem dirn546_norm : (reflectRing dirn546E).toPoly=dirn546P := dz2n546_norm

def dirn547E : RingExpr := dz2n547E
def dirn547P : Lean.Grind.CommRing.Poly := dz2n547P
theorem dirn547_norm : (reflectRing dirn547E).toPoly=dirn547P := dz2n547_norm

def dirn548E : RingExpr := dz2n548E
def dirn548P : Lean.Grind.CommRing.Poly := dz2n548P
theorem dirn548_norm : (reflectRing dirn548E).toPoly=dirn548P := dz2n548_norm

def dirn549E : RingExpr := dz2n549E
def dirn549P : Lean.Grind.CommRing.Poly := dz2n549P
theorem dirn549_norm : (reflectRing dirn549E).toPoly=dirn549P := dz2n549_norm

def dirn550E : RingExpr := dz2n550E
def dirn550P : Lean.Grind.CommRing.Poly := dz2n550P
theorem dirn550_norm : (reflectRing dirn550E).toPoly=dirn550P := dz2n550_norm

def dirn551E : RingExpr := dz2n551E
def dirn551P : Lean.Grind.CommRing.Poly := dz2n551P
theorem dirn551_norm : (reflectRing dirn551E).toPoly=dirn551P := dz2n551_norm

def dirn552E : RingExpr := dz2n552E
def dirn552P : Lean.Grind.CommRing.Poly := dz2n552P
theorem dirn552_norm : (reflectRing dirn552E).toPoly=dirn552P := dz2n552_norm

def dirn553E : RingExpr := dz2n553E
def dirn553P : Lean.Grind.CommRing.Poly := dz2n553P
theorem dirn553_norm : (reflectRing dirn553E).toPoly=dirn553P := dz2n553_norm

def dirn554E : RingExpr := dz2n554E
def dirn554P : Lean.Grind.CommRing.Poly := dz2n554P
theorem dirn554_norm : (reflectRing dirn554E).toPoly=dirn554P := dz2n554_norm

def dirn555E : RingExpr := dz2n555E
def dirn555P : Lean.Grind.CommRing.Poly := dz2n555P
theorem dirn555_norm : (reflectRing dirn555E).toPoly=dirn555P := dz2n555_norm

def dirn556E : RingExpr := dz2n556E
def dirn556P : Lean.Grind.CommRing.Poly := dz2n556P
theorem dirn556_norm : (reflectRing dirn556E).toPoly=dirn556P := dz2n556_norm

def dirn557E : RingExpr := dz2n557E
def dirn557P : Lean.Grind.CommRing.Poly := dz2n557P
theorem dirn557_norm : (reflectRing dirn557E).toPoly=dirn557P := dz2n557_norm

def dirn558E : RingExpr := dz2n558E
def dirn558P : Lean.Grind.CommRing.Poly := dz2n558P
theorem dirn558_norm : (reflectRing dirn558E).toPoly=dirn558P := dz2n558_norm

def dirn559E : RingExpr := dz2n559E
def dirn559P : Lean.Grind.CommRing.Poly := dz2n559P
theorem dirn559_norm : (reflectRing dirn559E).toPoly=dirn559P := dz2n559_norm

def dirn560E : RingExpr := dz2n560E
def dirn560P : Lean.Grind.CommRing.Poly := dz2n560P
theorem dirn560_norm : (reflectRing dirn560E).toPoly=dirn560P := dz2n560_norm

def dirn561E : RingExpr := dz2n561E
def dirn561P : Lean.Grind.CommRing.Poly := dz2n561P
theorem dirn561_norm : (reflectRing dirn561E).toPoly=dirn561P := dz2n561_norm

def dirn562E : RingExpr := dz2n562E
def dirn562P : Lean.Grind.CommRing.Poly := dz2n562P
theorem dirn562_norm : (reflectRing dirn562E).toPoly=dirn562P := dz2n562_norm

def dirn563E : RingExpr := dz2n563E
def dirn563P : Lean.Grind.CommRing.Poly := dz2n563P
theorem dirn563_norm : (reflectRing dirn563E).toPoly=dirn563P := dz2n563_norm

def dirn564E : RingExpr := dz2n564E
def dirn564P : Lean.Grind.CommRing.Poly := dz2n564P
theorem dirn564_norm : (reflectRing dirn564E).toPoly=dirn564P := dz2n564_norm

def dirn565E : RingExpr := dz2n565E
def dirn565P : Lean.Grind.CommRing.Poly := dz2n565P
theorem dirn565_norm : (reflectRing dirn565E).toPoly=dirn565P := dz2n565_norm

def dirn566E : RingExpr := dz2n566E
def dirn566P : Lean.Grind.CommRing.Poly := dz2n566P
theorem dirn566_norm : (reflectRing dirn566E).toPoly=dirn566P := dz2n566_norm

def dirn567E : RingExpr := dz2n567E
def dirn567P : Lean.Grind.CommRing.Poly := dz2n567P
theorem dirn567_norm : (reflectRing dirn567E).toPoly=dirn567P := dz2n567_norm

def dirn568E : RingExpr := dz2n568E
def dirn568P : Lean.Grind.CommRing.Poly := dz2n568P
theorem dirn568_norm : (reflectRing dirn568E).toPoly=dirn568P := dz2n568_norm

def dirn569E : RingExpr := dz2n569E
def dirn569P : Lean.Grind.CommRing.Poly := dz2n569P
theorem dirn569_norm : (reflectRing dirn569E).toPoly=dirn569P := dz2n569_norm

def dirn570E : RingExpr := dz2n570E
def dirn570P : Lean.Grind.CommRing.Poly := dz2n570P
theorem dirn570_norm : (reflectRing dirn570E).toPoly=dirn570P := dz2n570_norm

def dirn571E : RingExpr := dz2n571E
def dirn571P : Lean.Grind.CommRing.Poly := dz2n571P
theorem dirn571_norm : (reflectRing dirn571E).toPoly=dirn571P := dz2n571_norm

def dirn572E : RingExpr := dz2n572E
def dirn572P : Lean.Grind.CommRing.Poly := dz2n572P
theorem dirn572_norm : (reflectRing dirn572E).toPoly=dirn572P := dz2n572_norm

def dirn573E : RingExpr := dz2n573E
def dirn573P : Lean.Grind.CommRing.Poly := dz2n573P
theorem dirn573_norm : (reflectRing dirn573E).toPoly=dirn573P := dz2n573_norm

def dirn574E : RingExpr := dz2n574E
def dirn574P : Lean.Grind.CommRing.Poly := dz2n574P
theorem dirn574_norm : (reflectRing dirn574E).toPoly=dirn574P := dz2n574_norm

def dirn575E : RingExpr := dz2n575E
def dirn575P : Lean.Grind.CommRing.Poly := dz2n575P
theorem dirn575_norm : (reflectRing dirn575E).toPoly=dirn575P := dz2n575_norm

def dirn576E : RingExpr := dz2n576E
def dirn576P : Lean.Grind.CommRing.Poly := dz2n576P
theorem dirn576_norm : (reflectRing dirn576E).toPoly=dirn576P := dz2n576_norm

def dirn577E : RingExpr := dz2n577E
def dirn577P : Lean.Grind.CommRing.Poly := dz2n577P
theorem dirn577_norm : (reflectRing dirn577E).toPoly=dirn577P := dz2n577_norm

def dirn578E : RingExpr := dz2n578E
def dirn578P : Lean.Grind.CommRing.Poly := dz2n578P
theorem dirn578_norm : (reflectRing dirn578E).toPoly=dirn578P := dz2n578_norm

def dirn579E : RingExpr := dz2n579E
def dirn579P : Lean.Grind.CommRing.Poly := dz2n579P
theorem dirn579_norm : (reflectRing dirn579E).toPoly=dirn579P := dz2n579_norm

def dirn580E : RingExpr := dz2n580E
def dirn580P : Lean.Grind.CommRing.Poly := dz2n580P
theorem dirn580_norm : (reflectRing dirn580E).toPoly=dirn580P := dz2n580_norm

def dirn581E : RingExpr := dz2n581E
def dirn581P : Lean.Grind.CommRing.Poly := dz2n581P
theorem dirn581_norm : (reflectRing dirn581E).toPoly=dirn581P := dz2n581_norm

def dirn582E : RingExpr := dz2n582E
def dirn582P : Lean.Grind.CommRing.Poly := dz2n582P
theorem dirn582_norm : (reflectRing dirn582E).toPoly=dirn582P := dz2n582_norm

def dirn583E : RingExpr := dz2n583E
def dirn583P : Lean.Grind.CommRing.Poly := dz2n583P
theorem dirn583_norm : (reflectRing dirn583E).toPoly=dirn583P := dz2n583_norm

def dirn584E : RingExpr := dz2n584E
def dirn584P : Lean.Grind.CommRing.Poly := dz2n584P
theorem dirn584_norm : (reflectRing dirn584E).toPoly=dirn584P := dz2n584_norm

def dirn585E : RingExpr := dz2n585E
def dirn585P : Lean.Grind.CommRing.Poly := dz2n585P
theorem dirn585_norm : (reflectRing dirn585E).toPoly=dirn585P := dz2n585_norm

def dirn586E : RingExpr := dz2n586E
def dirn586P : Lean.Grind.CommRing.Poly := dz2n586P
theorem dirn586_norm : (reflectRing dirn586E).toPoly=dirn586P := dz2n586_norm

def dirn587E : RingExpr := dz2n587E
def dirn587P : Lean.Grind.CommRing.Poly := dz2n587P
theorem dirn587_norm : (reflectRing dirn587E).toPoly=dirn587P := dz2n587_norm

def dirn588E : RingExpr := dz2n588E
def dirn588P : Lean.Grind.CommRing.Poly := dz2n588P
theorem dirn588_norm : (reflectRing dirn588E).toPoly=dirn588P := dz2n588_norm

def dirn589E : RingExpr := dz2n589E
def dirn589P : Lean.Grind.CommRing.Poly := dz2n589P
theorem dirn589_norm : (reflectRing dirn589E).toPoly=dirn589P := dz2n589_norm

def dirn590E : RingExpr := dz2n590E
def dirn590P : Lean.Grind.CommRing.Poly := dz2n590P
theorem dirn590_norm : (reflectRing dirn590E).toPoly=dirn590P := dz2n590_norm

def dirn591E : RingExpr := dz2n591E
def dirn591P : Lean.Grind.CommRing.Poly := dz2n591P
theorem dirn591_norm : (reflectRing dirn591E).toPoly=dirn591P := dz2n591_norm

def dirn592E : RingExpr := dz2n592E
def dirn592P : Lean.Grind.CommRing.Poly := dz2n592P
theorem dirn592_norm : (reflectRing dirn592E).toPoly=dirn592P := dz2n592_norm

def dirn593E : RingExpr := dz2n593E
def dirn593P : Lean.Grind.CommRing.Poly := dz2n593P
theorem dirn593_norm : (reflectRing dirn593E).toPoly=dirn593P := dz2n593_norm

def dirn594E : RingExpr := dz2n594E
def dirn594P : Lean.Grind.CommRing.Poly := dz2n594P
theorem dirn594_norm : (reflectRing dirn594E).toPoly=dirn594P := dz2n594_norm

def dirn595E : RingExpr := dz2n595E
def dirn595P : Lean.Grind.CommRing.Poly := dz2n595P
theorem dirn595_norm : (reflectRing dirn595E).toPoly=dirn595P := dz2n595_norm

def dirn596E : RingExpr := dz2n596E
def dirn596P : Lean.Grind.CommRing.Poly := dz2n596P
theorem dirn596_norm : (reflectRing dirn596E).toPoly=dirn596P := dz2n596_norm

def dirn597E : RingExpr := dz2n597E
def dirn597P : Lean.Grind.CommRing.Poly := dz2n597P
theorem dirn597_norm : (reflectRing dirn597E).toPoly=dirn597P := dz2n597_norm

def dirn598E : RingExpr := dz2n598E
def dirn598P : Lean.Grind.CommRing.Poly := dz2n598P
theorem dirn598_norm : (reflectRing dirn598E).toPoly=dirn598P := dz2n598_norm

def dirn599E : RingExpr := dz2n599E
def dirn599P : Lean.Grind.CommRing.Poly := dz2n599P
theorem dirn599_norm : (reflectRing dirn599E).toPoly=dirn599P := dz2n599_norm

def dirn600E : RingExpr := dz2n600E
def dirn600P : Lean.Grind.CommRing.Poly := dz2n600P
theorem dirn600_norm : (reflectRing dirn600E).toPoly=dirn600P := dz2n600_norm

def dirn601E : RingExpr := dz2n601E
def dirn601P : Lean.Grind.CommRing.Poly := dz2n601P
theorem dirn601_norm : (reflectRing dirn601E).toPoly=dirn601P := dz2n601_norm

def dirn602E : RingExpr := dz2n602E
def dirn602P : Lean.Grind.CommRing.Poly := dz2n602P
theorem dirn602_norm : (reflectRing dirn602E).toPoly=dirn602P := dz2n602_norm

def dirn603E : RingExpr := dz2n603E
def dirn603P : Lean.Grind.CommRing.Poly := dz2n603P
theorem dirn603_norm : (reflectRing dirn603E).toPoly=dirn603P := dz2n603_norm

def dirn604E : RingExpr := dz2n604E
def dirn604P : Lean.Grind.CommRing.Poly := dz2n604P
theorem dirn604_norm : (reflectRing dirn604E).toPoly=dirn604P := dz2n604_norm

def dirn605E : RingExpr := dz2n605E
def dirn605P : Lean.Grind.CommRing.Poly := dz2n605P
theorem dirn605_norm : (reflectRing dirn605E).toPoly=dirn605P := dz2n605_norm

def dirn606E : RingExpr := dz2n606E
def dirn606P : Lean.Grind.CommRing.Poly := dz2n606P
theorem dirn606_norm : (reflectRing dirn606E).toPoly=dirn606P := dz2n606_norm

def dirn607E : RingExpr := dz2n607E
def dirn607P : Lean.Grind.CommRing.Poly := dz2n607P
theorem dirn607_norm : (reflectRing dirn607E).toPoly=dirn607P := dz2n607_norm

def dirn608E : RingExpr := dz2n608E
def dirn608P : Lean.Grind.CommRing.Poly := dz2n608P
theorem dirn608_norm : (reflectRing dirn608E).toPoly=dirn608P := dz2n608_norm

def dirn609E : RingExpr := dz2n609E
def dirn609P : Lean.Grind.CommRing.Poly := dz2n609P
theorem dirn609_norm : (reflectRing dirn609E).toPoly=dirn609P := dz2n609_norm

def dirn610E : RingExpr := dz2n610E
def dirn610P : Lean.Grind.CommRing.Poly := dz2n610P
theorem dirn610_norm : (reflectRing dirn610E).toPoly=dirn610P := dz2n610_norm

def dirn611E : RingExpr := dz2n611E
def dirn611P : Lean.Grind.CommRing.Poly := dz2n611P
theorem dirn611_norm : (reflectRing dirn611E).toPoly=dirn611P := dz2n611_norm

def dirn612E : RingExpr := dz2n612E
def dirn612P : Lean.Grind.CommRing.Poly := dz2n612P
theorem dirn612_norm : (reflectRing dirn612E).toPoly=dirn612P := dz2n612_norm

def dirn613E : RingExpr := dz2n613E
def dirn613P : Lean.Grind.CommRing.Poly := dz2n613P
theorem dirn613_norm : (reflectRing dirn613E).toPoly=dirn613P := dz2n613_norm

def dirn614E : RingExpr := dz2n614E
def dirn614P : Lean.Grind.CommRing.Poly := dz2n614P
theorem dirn614_norm : (reflectRing dirn614E).toPoly=dirn614P := dz2n614_norm

def dirn615E : RingExpr := dz2n615E
def dirn615P : Lean.Grind.CommRing.Poly := dz2n615P
theorem dirn615_norm : (reflectRing dirn615E).toPoly=dirn615P := dz2n615_norm

def dirn616E : RingExpr := dz2n616E
def dirn616P : Lean.Grind.CommRing.Poly := dz2n616P
theorem dirn616_norm : (reflectRing dirn616E).toPoly=dirn616P := dz2n616_norm

def dirn617E : RingExpr := dz2n617E
def dirn617P : Lean.Grind.CommRing.Poly := dz2n617P
theorem dirn617_norm : (reflectRing dirn617E).toPoly=dirn617P := dz2n617_norm

def dirn618E : RingExpr := dz2n618E
def dirn618P : Lean.Grind.CommRing.Poly := dz2n618P
theorem dirn618_norm : (reflectRing dirn618E).toPoly=dirn618P := dz2n618_norm

def dirn619E : RingExpr := dz2n619E
def dirn619P : Lean.Grind.CommRing.Poly := dz2n619P
theorem dirn619_norm : (reflectRing dirn619E).toPoly=dirn619P := dz2n619_norm

def dirn620E : RingExpr := dz2n620E
def dirn620P : Lean.Grind.CommRing.Poly := dz2n620P
theorem dirn620_norm : (reflectRing dirn620E).toPoly=dirn620P := dz2n620_norm

def dirn621E : RingExpr := dz2n621E
def dirn621P : Lean.Grind.CommRing.Poly := dz2n621P
theorem dirn621_norm : (reflectRing dirn621E).toPoly=dirn621P := dz2n621_norm

def dirn622E : RingExpr := dz2n622E
def dirn622P : Lean.Grind.CommRing.Poly := dz2n622P
theorem dirn622_norm : (reflectRing dirn622E).toPoly=dirn622P := dz2n622_norm

def dirn623E : RingExpr := dz2n623E
def dirn623P : Lean.Grind.CommRing.Poly := dz2n623P
theorem dirn623_norm : (reflectRing dirn623E).toPoly=dirn623P := dz2n623_norm

def dirn624E : RingExpr := dz2n624E
def dirn624P : Lean.Grind.CommRing.Poly := dz2n624P
theorem dirn624_norm : (reflectRing dirn624E).toPoly=dirn624P := dz2n624_norm

def dirn625E : RingExpr := dz2n625E
def dirn625P : Lean.Grind.CommRing.Poly := dz2n625P
theorem dirn625_norm : (reflectRing dirn625E).toPoly=dirn625P := dz2n625_norm

def dirn626E : RingExpr := dz2n626E
def dirn626P : Lean.Grind.CommRing.Poly := dz2n626P
theorem dirn626_norm : (reflectRing dirn626E).toPoly=dirn626P := dz2n626_norm

def dirn627E : RingExpr := dz2n627E
def dirn627P : Lean.Grind.CommRing.Poly := dz2n627P
theorem dirn627_norm : (reflectRing dirn627E).toPoly=dirn627P := dz2n627_norm

def dirn628E : RingExpr := dz2n628E
def dirn628P : Lean.Grind.CommRing.Poly := dz2n628P
theorem dirn628_norm : (reflectRing dirn628E).toPoly=dirn628P := dz2n628_norm

def dirn629E : RingExpr := dz2n629E
def dirn629P : Lean.Grind.CommRing.Poly := dz2n629P
theorem dirn629_norm : (reflectRing dirn629E).toPoly=dirn629P := dz2n629_norm

def dirn630E : RingExpr := dz2n630E
def dirn630P : Lean.Grind.CommRing.Poly := dz2n630P
theorem dirn630_norm : (reflectRing dirn630E).toPoly=dirn630P := dz2n630_norm

def dirn631E : RingExpr := dz2n631E
def dirn631P : Lean.Grind.CommRing.Poly := dz2n631P
theorem dirn631_norm : (reflectRing dirn631E).toPoly=dirn631P := dz2n631_norm

def dirn632E : RingExpr := dz2n632E
def dirn632P : Lean.Grind.CommRing.Poly := dz2n632P
theorem dirn632_norm : (reflectRing dirn632E).toPoly=dirn632P := dz2n632_norm

def dirn633E : RingExpr := dz2n633E
def dirn633P : Lean.Grind.CommRing.Poly := dz2n633P
theorem dirn633_norm : (reflectRing dirn633E).toPoly=dirn633P := dz2n633_norm

def dirn634E : RingExpr := dz2n634E
def dirn634P : Lean.Grind.CommRing.Poly := dz2n634P
theorem dirn634_norm : (reflectRing dirn634E).toPoly=dirn634P := dz2n634_norm

def dirn635E : RingExpr := dz2n635E
def dirn635P : Lean.Grind.CommRing.Poly := dz2n635P
theorem dirn635_norm : (reflectRing dirn635E).toPoly=dirn635P := dz2n635_norm

def dirn636E : RingExpr := dz2n636E
def dirn636P : Lean.Grind.CommRing.Poly := dz2n636P
theorem dirn636_norm : (reflectRing dirn636E).toPoly=dirn636P := dz2n636_norm

def dirn637E : RingExpr := dz2n637E
def dirn637P : Lean.Grind.CommRing.Poly := dz2n637P
theorem dirn637_norm : (reflectRing dirn637E).toPoly=dirn637P := dz2n637_norm

def dirn638E : RingExpr := dz2n638E
def dirn638P : Lean.Grind.CommRing.Poly := dz2n638P
theorem dirn638_norm : (reflectRing dirn638E).toPoly=dirn638P := dz2n638_norm

def dirn639E : RingExpr := dz2n639E
def dirn639P : Lean.Grind.CommRing.Poly := dz2n639P
theorem dirn639_norm : (reflectRing dirn639E).toPoly=dirn639P := dz2n639_norm

def dirn640E : RingExpr := dz2n640E
def dirn640P : Lean.Grind.CommRing.Poly := dz2n640P
theorem dirn640_norm : (reflectRing dirn640E).toPoly=dirn640P := dz2n640_norm

def dirn641E : RingExpr := dz2n641E
def dirn641P : Lean.Grind.CommRing.Poly := dz2n641P
theorem dirn641_norm : (reflectRing dirn641E).toPoly=dirn641P := dz2n641_norm

def dirn642E : RingExpr := dz2n642E
def dirn642P : Lean.Grind.CommRing.Poly := dz2n642P
theorem dirn642_norm : (reflectRing dirn642E).toPoly=dirn642P := dz2n642_norm

def dirn643E : RingExpr := dz2n643E
def dirn643P : Lean.Grind.CommRing.Poly := dz2n643P
theorem dirn643_norm : (reflectRing dirn643E).toPoly=dirn643P := dz2n643_norm

def dirn644E : RingExpr := dz2n644E
def dirn644P : Lean.Grind.CommRing.Poly := dz2n644P
theorem dirn644_norm : (reflectRing dirn644E).toPoly=dirn644P := dz2n644_norm

def dirn645E : RingExpr := dz2n645E
def dirn645P : Lean.Grind.CommRing.Poly := dz2n645P
theorem dirn645_norm : (reflectRing dirn645E).toPoly=dirn645P := dz2n645_norm

def dirn646E : RingExpr := dz2n646E
def dirn646P : Lean.Grind.CommRing.Poly := dz2n646P
theorem dirn646_norm : (reflectRing dirn646E).toPoly=dirn646P := dz2n646_norm

def dirn647E : RingExpr := dz2n647E
def dirn647P : Lean.Grind.CommRing.Poly := dz2n647P
theorem dirn647_norm : (reflectRing dirn647E).toPoly=dirn647P := dz2n647_norm

def dirn648E : RingExpr := dz2n648E
def dirn648P : Lean.Grind.CommRing.Poly := dz2n648P
theorem dirn648_norm : (reflectRing dirn648E).toPoly=dirn648P := dz2n648_norm

def dirn649E : RingExpr := dz2n649E
def dirn649P : Lean.Grind.CommRing.Poly := dz2n649P
theorem dirn649_norm : (reflectRing dirn649E).toPoly=dirn649P := dz2n649_norm

def dirn650E : RingExpr := dz2n650E
def dirn650P : Lean.Grind.CommRing.Poly := dz2n650P
theorem dirn650_norm : (reflectRing dirn650E).toPoly=dirn650P := dz2n650_norm

def dirn651E : RingExpr := dz2n651E
def dirn651P : Lean.Grind.CommRing.Poly := dz2n651P
theorem dirn651_norm : (reflectRing dirn651E).toPoly=dirn651P := dz2n651_norm

def dirn652E : RingExpr := dz2n652E
def dirn652P : Lean.Grind.CommRing.Poly := dz2n652P
theorem dirn652_norm : (reflectRing dirn652E).toPoly=dirn652P := dz2n652_norm

def dirn653E : RingExpr := dz2n653E
def dirn653P : Lean.Grind.CommRing.Poly := dz2n653P
theorem dirn653_norm : (reflectRing dirn653E).toPoly=dirn653P := dz2n653_norm

def dirn654E : RingExpr := dz2n654E
def dirn654P : Lean.Grind.CommRing.Poly := dz2n654P
theorem dirn654_norm : (reflectRing dirn654E).toPoly=dirn654P := dz2n654_norm

def dirn655E : RingExpr := dz2n655E
def dirn655P : Lean.Grind.CommRing.Poly := dz2n655P
theorem dirn655_norm : (reflectRing dirn655E).toPoly=dirn655P := dz2n655_norm

def dirn656E : RingExpr := dz2n656E
def dirn656P : Lean.Grind.CommRing.Poly := dz2n656P
theorem dirn656_norm : (reflectRing dirn656E).toPoly=dirn656P := dz2n656_norm

def dirn657E : RingExpr := dz2n657E
def dirn657P : Lean.Grind.CommRing.Poly := dz2n657P
theorem dirn657_norm : (reflectRing dirn657E).toPoly=dirn657P := dz2n657_norm

def dirn658E : RingExpr := dz2n658E
def dirn658P : Lean.Grind.CommRing.Poly := dz2n658P
theorem dirn658_norm : (reflectRing dirn658E).toPoly=dirn658P := dz2n658_norm

def dirn659E : RingExpr := dz2n659E
def dirn659P : Lean.Grind.CommRing.Poly := dz2n659P
theorem dirn659_norm : (reflectRing dirn659E).toPoly=dirn659P := dz2n659_norm

def dirn660E : RingExpr := dz2n660E
def dirn660P : Lean.Grind.CommRing.Poly := dz2n660P
theorem dirn660_norm : (reflectRing dirn660E).toPoly=dirn660P := dz2n660_norm

def dirn661E : RingExpr := dz2n661E
def dirn661P : Lean.Grind.CommRing.Poly := dz2n661P
theorem dirn661_norm : (reflectRing dirn661E).toPoly=dirn661P := dz2n661_norm

def dirn662E : RingExpr := dz2n662E
def dirn662P : Lean.Grind.CommRing.Poly := dz2n662P
theorem dirn662_norm : (reflectRing dirn662E).toPoly=dirn662P := dz2n662_norm

def dirn663E : RingExpr := dz2n663E
def dirn663P : Lean.Grind.CommRing.Poly := dz2n663P
theorem dirn663_norm : (reflectRing dirn663E).toPoly=dirn663P := dz2n663_norm

def dirn664E : RingExpr := dz2n664E
def dirn664P : Lean.Grind.CommRing.Poly := dz2n664P
theorem dirn664_norm : (reflectRing dirn664E).toPoly=dirn664P := dz2n664_norm

def dirn665E : RingExpr := dz2n665E
def dirn665P : Lean.Grind.CommRing.Poly := dz2n665P
theorem dirn665_norm : (reflectRing dirn665E).toPoly=dirn665P := dz2n665_norm

def dirn666E : RingExpr := dz2n666E
def dirn666P : Lean.Grind.CommRing.Poly := dz2n666P
theorem dirn666_norm : (reflectRing dirn666E).toPoly=dirn666P := dz2n666_norm

def dirn667E : RingExpr := dz2n667E
def dirn667P : Lean.Grind.CommRing.Poly := dz2n667P
theorem dirn667_norm : (reflectRing dirn667E).toPoly=dirn667P := dz2n667_norm

def dirn668E : RingExpr := dz2n668E
def dirn668P : Lean.Grind.CommRing.Poly := dz2n668P
theorem dirn668_norm : (reflectRing dirn668E).toPoly=dirn668P := dz2n668_norm

def dirn669E : RingExpr := dz2n669E
def dirn669P : Lean.Grind.CommRing.Poly := dz2n669P
theorem dirn669_norm : (reflectRing dirn669E).toPoly=dirn669P := dz2n669_norm

def dirn670E : RingExpr := dz2n670E
def dirn670P : Lean.Grind.CommRing.Poly := dz2n670P
theorem dirn670_norm : (reflectRing dirn670E).toPoly=dirn670P := dz2n670_norm

def dirn671E : RingExpr := dz2n671E
def dirn671P : Lean.Grind.CommRing.Poly := dz2n671P
theorem dirn671_norm : (reflectRing dirn671E).toPoly=dirn671P := dz2n671_norm

def dirn672E : RingExpr := dz2n672E
def dirn672P : Lean.Grind.CommRing.Poly := dz2n672P
theorem dirn672_norm : (reflectRing dirn672E).toPoly=dirn672P := dz2n672_norm

def dirn673E : RingExpr := dz2n673E
def dirn673P : Lean.Grind.CommRing.Poly := dz2n673P
theorem dirn673_norm : (reflectRing dirn673E).toPoly=dirn673P := dz2n673_norm

def dirn674E : RingExpr := dz2n674E
def dirn674P : Lean.Grind.CommRing.Poly := dz2n674P
theorem dirn674_norm : (reflectRing dirn674E).toPoly=dirn674P := dz2n674_norm

def dirn675E : RingExpr := dz2n675E
def dirn675P : Lean.Grind.CommRing.Poly := dz2n675P
theorem dirn675_norm : (reflectRing dirn675E).toPoly=dirn675P := dz2n675_norm

def dirn676E : RingExpr := dz2n676E
def dirn676P : Lean.Grind.CommRing.Poly := dz2n676P
theorem dirn676_norm : (reflectRing dirn676E).toPoly=dirn676P := dz2n676_norm

def dirn677E : RingExpr := dz2n677E
def dirn677P : Lean.Grind.CommRing.Poly := dz2n677P
theorem dirn677_norm : (reflectRing dirn677E).toPoly=dirn677P := dz2n677_norm

def dirn678E : RingExpr := dz2n678E
def dirn678P : Lean.Grind.CommRing.Poly := dz2n678P
theorem dirn678_norm : (reflectRing dirn678E).toPoly=dirn678P := dz2n678_norm

def dirn679E : RingExpr := dz2n679E
def dirn679P : Lean.Grind.CommRing.Poly := dz2n679P
theorem dirn679_norm : (reflectRing dirn679E).toPoly=dirn679P := dz2n679_norm

def dirn680E : RingExpr := dz2n680E
def dirn680P : Lean.Grind.CommRing.Poly := dz2n680P
theorem dirn680_norm : (reflectRing dirn680E).toPoly=dirn680P := dz2n680_norm

def dirn681E : RingExpr := dz2n681E
def dirn681P : Lean.Grind.CommRing.Poly := dz2n681P
theorem dirn681_norm : (reflectRing dirn681E).toPoly=dirn681P := dz2n681_norm

def dirn682E : RingExpr := dz2n682E
def dirn682P : Lean.Grind.CommRing.Poly := dz2n682P
theorem dirn682_norm : (reflectRing dirn682E).toPoly=dirn682P := dz2n682_norm

def dirn683E : RingExpr := dz2n683E
def dirn683P : Lean.Grind.CommRing.Poly := dz2n683P
theorem dirn683_norm : (reflectRing dirn683E).toPoly=dirn683P := dz2n683_norm

def dirn684E : RingExpr := dz2n684E
def dirn684P : Lean.Grind.CommRing.Poly := dz2n684P
theorem dirn684_norm : (reflectRing dirn684E).toPoly=dirn684P := dz2n684_norm

def dirn685E : RingExpr := dz2n685E
def dirn685P : Lean.Grind.CommRing.Poly := dz2n685P
theorem dirn685_norm : (reflectRing dirn685E).toPoly=dirn685P := dz2n685_norm

def dirn686E : RingExpr := dz2n686E
def dirn686P : Lean.Grind.CommRing.Poly := dz2n686P
theorem dirn686_norm : (reflectRing dirn686E).toPoly=dirn686P := dz2n686_norm

def dirn687E : RingExpr := dz2n687E
def dirn687P : Lean.Grind.CommRing.Poly := dz2n687P
theorem dirn687_norm : (reflectRing dirn687E).toPoly=dirn687P := dz2n687_norm

def dirn688E : RingExpr := dz2n688E
def dirn688P : Lean.Grind.CommRing.Poly := dz2n688P
theorem dirn688_norm : (reflectRing dirn688E).toPoly=dirn688P := dz2n688_norm

def dirn689E : RingExpr := dz2n689E
def dirn689P : Lean.Grind.CommRing.Poly := dz2n689P
theorem dirn689_norm : (reflectRing dirn689E).toPoly=dirn689P := dz2n689_norm

def dirn690E : RingExpr := dz2n690E
def dirn690P : Lean.Grind.CommRing.Poly := dz2n690P
theorem dirn690_norm : (reflectRing dirn690E).toPoly=dirn690P := dz2n690_norm

def dirn691E : RingExpr := dz2n691E
def dirn691P : Lean.Grind.CommRing.Poly := dz2n691P
theorem dirn691_norm : (reflectRing dirn691E).toPoly=dirn691P := dz2n691_norm

def dirn692E : RingExpr := dz2n692E
def dirn692P : Lean.Grind.CommRing.Poly := dz2n692P
theorem dirn692_norm : (reflectRing dirn692E).toPoly=dirn692P := dz2n692_norm

def dirn693E : RingExpr := dz2n693E
def dirn693P : Lean.Grind.CommRing.Poly := dz2n693P
theorem dirn693_norm : (reflectRing dirn693E).toPoly=dirn693P := dz2n693_norm

def dirn694E : RingExpr := dz2n694E
def dirn694P : Lean.Grind.CommRing.Poly := dz2n694P
theorem dirn694_norm : (reflectRing dirn694E).toPoly=dirn694P := dz2n694_norm

def dirn695E : RingExpr := dz2n695E
def dirn695P : Lean.Grind.CommRing.Poly := dz2n695P
theorem dirn695_norm : (reflectRing dirn695E).toPoly=dirn695P := dz2n695_norm

def dirn696E : RingExpr := dz2n696E
def dirn696P : Lean.Grind.CommRing.Poly := dz2n696P
theorem dirn696_norm : (reflectRing dirn696E).toPoly=dirn696P := dz2n696_norm

def dirn697E : RingExpr := dz2n697E
def dirn697P : Lean.Grind.CommRing.Poly := dz2n697P
theorem dirn697_norm : (reflectRing dirn697E).toPoly=dirn697P := dz2n697_norm

def dirn698E : RingExpr := dz2n698E
def dirn698P : Lean.Grind.CommRing.Poly := dz2n698P
theorem dirn698_norm : (reflectRing dirn698E).toPoly=dirn698P := dz2n698_norm

def dirn699E : RingExpr := dz2n699E
def dirn699P : Lean.Grind.CommRing.Poly := dz2n699P
theorem dirn699_norm : (reflectRing dirn699E).toPoly=dirn699P := dz2n699_norm

def dirn700E : RingExpr := dz2n700E
def dirn700P : Lean.Grind.CommRing.Poly := dz2n700P
theorem dirn700_norm : (reflectRing dirn700E).toPoly=dirn700P := dz2n700_norm

def dirn701E : RingExpr := dz2n701E
def dirn701P : Lean.Grind.CommRing.Poly := dz2n701P
theorem dirn701_norm : (reflectRing dirn701E).toPoly=dirn701P := dz2n701_norm

def dirn702E : RingExpr := dz2n702E
def dirn702P : Lean.Grind.CommRing.Poly := dz2n702P
theorem dirn702_norm : (reflectRing dirn702E).toPoly=dirn702P := dz2n702_norm

def dirn703E : RingExpr := dz2n703E
def dirn703P : Lean.Grind.CommRing.Poly := dz2n703P
theorem dirn703_norm : (reflectRing dirn703E).toPoly=dirn703P := dz2n703_norm

def dirn704E : RingExpr := dz2n704E
def dirn704P : Lean.Grind.CommRing.Poly := dz2n704P
theorem dirn704_norm : (reflectRing dirn704E).toPoly=dirn704P := dz2n704_norm

def dirn705E : RingExpr := dz2n705E
def dirn705P : Lean.Grind.CommRing.Poly := dz2n705P
theorem dirn705_norm : (reflectRing dirn705E).toPoly=dirn705P := dz2n705_norm

def dirn706E : RingExpr := dz2n706E
def dirn706P : Lean.Grind.CommRing.Poly := dz2n706P
theorem dirn706_norm : (reflectRing dirn706E).toPoly=dirn706P := dz2n706_norm

def dirn707E : RingExpr := dz2n707E
def dirn707P : Lean.Grind.CommRing.Poly := dz2n707P
theorem dirn707_norm : (reflectRing dirn707E).toPoly=dirn707P := dz2n707_norm

def dirn708E : RingExpr := dz2n708E
def dirn708P : Lean.Grind.CommRing.Poly := dz2n708P
theorem dirn708_norm : (reflectRing dirn708E).toPoly=dirn708P := dz2n708_norm

def dirn709E : RingExpr := dz2n709E
def dirn709P : Lean.Grind.CommRing.Poly := dz2n709P
theorem dirn709_norm : (reflectRing dirn709E).toPoly=dirn709P := dz2n709_norm

def dirn710E : RingExpr := dz2n710E
def dirn710P : Lean.Grind.CommRing.Poly := dz2n710P
theorem dirn710_norm : (reflectRing dirn710E).toPoly=dirn710P := dz2n710_norm

def dirn711E : RingExpr := dz2n711E
def dirn711P : Lean.Grind.CommRing.Poly := dz2n711P
theorem dirn711_norm : (reflectRing dirn711E).toPoly=dirn711P := dz2n711_norm

def dirn712E : RingExpr := dz2n712E
def dirn712P : Lean.Grind.CommRing.Poly := dz2n712P
theorem dirn712_norm : (reflectRing dirn712E).toPoly=dirn712P := dz2n712_norm

def dirn713E : RingExpr := dz2n713E
def dirn713P : Lean.Grind.CommRing.Poly := dz2n713P
theorem dirn713_norm : (reflectRing dirn713E).toPoly=dirn713P := dz2n713_norm

def dirn714E : RingExpr := dz2n714E
def dirn714P : Lean.Grind.CommRing.Poly := dz2n714P
theorem dirn714_norm : (reflectRing dirn714E).toPoly=dirn714P := dz2n714_norm

def dirn715E : RingExpr := dz2n715E
def dirn715P : Lean.Grind.CommRing.Poly := dz2n715P
theorem dirn715_norm : (reflectRing dirn715E).toPoly=dirn715P := dz2n715_norm

def dirn716E : RingExpr := dz2n716E
def dirn716P : Lean.Grind.CommRing.Poly := dz2n716P
theorem dirn716_norm : (reflectRing dirn716E).toPoly=dirn716P := dz2n716_norm

def dirn717E : RingExpr := dz2n717E
def dirn717P : Lean.Grind.CommRing.Poly := dz2n717P
theorem dirn717_norm : (reflectRing dirn717E).toPoly=dirn717P := dz2n717_norm

def dirn718E : RingExpr := dz2n718E
def dirn718P : Lean.Grind.CommRing.Poly := dz2n718P
theorem dirn718_norm : (reflectRing dirn718E).toPoly=dirn718P := dz2n718_norm

def dirn719E : RingExpr := dz2n719E
def dirn719P : Lean.Grind.CommRing.Poly := dz2n719P
theorem dirn719_norm : (reflectRing dirn719E).toPoly=dirn719P := dz2n719_norm

def dirn720E : RingExpr := dz2n720E
def dirn720P : Lean.Grind.CommRing.Poly := dz2n720P
theorem dirn720_norm : (reflectRing dirn720E).toPoly=dirn720P := dz2n720_norm

def dirn721E : RingExpr := dz2n721E
def dirn721P : Lean.Grind.CommRing.Poly := dz2n721P
theorem dirn721_norm : (reflectRing dirn721E).toPoly=dirn721P := dz2n721_norm

def dirn722E : RingExpr := dz2n722E
def dirn722P : Lean.Grind.CommRing.Poly := dz2n722P
theorem dirn722_norm : (reflectRing dirn722E).toPoly=dirn722P := dz2n722_norm

def dirn723E : RingExpr := dz2n723E
def dirn723P : Lean.Grind.CommRing.Poly := dz2n723P
theorem dirn723_norm : (reflectRing dirn723E).toPoly=dirn723P := dz2n723_norm

def dirn724E : RingExpr := dz2n724E
def dirn724P : Lean.Grind.CommRing.Poly := dz2n724P
theorem dirn724_norm : (reflectRing dirn724E).toPoly=dirn724P := dz2n724_norm

def dirn725E : RingExpr := dz2n725E
def dirn725P : Lean.Grind.CommRing.Poly := dz2n725P
theorem dirn725_norm : (reflectRing dirn725E).toPoly=dirn725P := dz2n725_norm

def dirn726E : RingExpr := dz2n726E
def dirn726P : Lean.Grind.CommRing.Poly := dz2n726P
theorem dirn726_norm : (reflectRing dirn726E).toPoly=dirn726P := dz2n726_norm

def dirn727E : RingExpr := dz2n727E
def dirn727P : Lean.Grind.CommRing.Poly := dz2n727P
theorem dirn727_norm : (reflectRing dirn727E).toPoly=dirn727P := dz2n727_norm

def dirn728E : RingExpr := dz2n728E
def dirn728P : Lean.Grind.CommRing.Poly := dz2n728P
theorem dirn728_norm : (reflectRing dirn728E).toPoly=dirn728P := dz2n728_norm

def dirn729E : RingExpr := dz2n729E
def dirn729P : Lean.Grind.CommRing.Poly := dz2n729P
theorem dirn729_norm : (reflectRing dirn729E).toPoly=dirn729P := dz2n729_norm

def dirn730E : RingExpr := dz2n730E
def dirn730P : Lean.Grind.CommRing.Poly := dz2n730P
theorem dirn730_norm : (reflectRing dirn730E).toPoly=dirn730P := dz2n730_norm

def dirn731E : RingExpr := dz2n731E
def dirn731P : Lean.Grind.CommRing.Poly := dz2n731P
theorem dirn731_norm : (reflectRing dirn731E).toPoly=dirn731P := dz2n731_norm

def dirn732E : RingExpr := dz2n732E
def dirn732P : Lean.Grind.CommRing.Poly := dz2n732P
theorem dirn732_norm : (reflectRing dirn732E).toPoly=dirn732P := dz2n732_norm

def dirn733E : RingExpr := dz2n733E
def dirn733P : Lean.Grind.CommRing.Poly := dz2n733P
theorem dirn733_norm : (reflectRing dirn733E).toPoly=dirn733P := dz2n733_norm

def dirn734E : RingExpr := dz2n734E
def dirn734P : Lean.Grind.CommRing.Poly := dz2n734P
theorem dirn734_norm : (reflectRing dirn734E).toPoly=dirn734P := dz2n734_norm

def dirn735E : RingExpr := dz2n735E
def dirn735P : Lean.Grind.CommRing.Poly := dz2n735P
theorem dirn735_norm : (reflectRing dirn735E).toPoly=dirn735P := dz2n735_norm

def dirn736E : RingExpr := dz2n736E
def dirn736P : Lean.Grind.CommRing.Poly := dz2n736P
theorem dirn736_norm : (reflectRing dirn736E).toPoly=dirn736P := dz2n736_norm

def dirn737E : RingExpr := dz2n737E
def dirn737P : Lean.Grind.CommRing.Poly := dz2n737P
theorem dirn737_norm : (reflectRing dirn737E).toPoly=dirn737P := dz2n737_norm

def dirn738E : RingExpr := dz2n738E
def dirn738P : Lean.Grind.CommRing.Poly := dz2n738P
theorem dirn738_norm : (reflectRing dirn738E).toPoly=dirn738P := dz2n738_norm

def dirn739E : RingExpr := dz2n739E
def dirn739P : Lean.Grind.CommRing.Poly := dz2n739P
theorem dirn739_norm : (reflectRing dirn739E).toPoly=dirn739P := dz2n739_norm

def dirn740E : RingExpr := dz2n740E
def dirn740P : Lean.Grind.CommRing.Poly := dz2n740P
theorem dirn740_norm : (reflectRing dirn740E).toPoly=dirn740P := dz2n740_norm

def dirn741E : RingExpr := dz2n741E
def dirn741P : Lean.Grind.CommRing.Poly := dz2n741P
theorem dirn741_norm : (reflectRing dirn741E).toPoly=dirn741P := dz2n741_norm

def dirn742E : RingExpr := dz2n742E
def dirn742P : Lean.Grind.CommRing.Poly := dz2n742P
theorem dirn742_norm : (reflectRing dirn742E).toPoly=dirn742P := dz2n742_norm

def dirn743E : RingExpr := dz2n743E
def dirn743P : Lean.Grind.CommRing.Poly := dz2n743P
theorem dirn743_norm : (reflectRing dirn743E).toPoly=dirn743P := dz2n743_norm

def dirn744E : RingExpr := dz2n744E
def dirn744P : Lean.Grind.CommRing.Poly := dz2n744P
theorem dirn744_norm : (reflectRing dirn744E).toPoly=dirn744P := dz2n744_norm

def dirn745E : RingExpr := dz2n745E
def dirn745P : Lean.Grind.CommRing.Poly := dz2n745P
theorem dirn745_norm : (reflectRing dirn745E).toPoly=dirn745P := dz2n745_norm

def dirn746E : RingExpr := dz2n746E
def dirn746P : Lean.Grind.CommRing.Poly := dz2n746P
theorem dirn746_norm : (reflectRing dirn746E).toPoly=dirn746P := dz2n746_norm

def dirn747E : RingExpr := dz2n747E
def dirn747P : Lean.Grind.CommRing.Poly := dz2n747P
theorem dirn747_norm : (reflectRing dirn747E).toPoly=dirn747P := dz2n747_norm

def dirn748E : RingExpr := dz2n748E
def dirn748P : Lean.Grind.CommRing.Poly := dz2n748P
theorem dirn748_norm : (reflectRing dirn748E).toPoly=dirn748P := dz2n748_norm

def dirn749E : RingExpr := dz2n749E
def dirn749P : Lean.Grind.CommRing.Poly := dz2n749P
theorem dirn749_norm : (reflectRing dirn749E).toPoly=dirn749P := dz2n749_norm

def dirn750E : RingExpr := dz2n750E
def dirn750P : Lean.Grind.CommRing.Poly := dz2n750P
theorem dirn750_norm : (reflectRing dirn750E).toPoly=dirn750P := dz2n750_norm

def dirn751E : RingExpr := dz2n751E
def dirn751P : Lean.Grind.CommRing.Poly := dz2n751P
theorem dirn751_norm : (reflectRing dirn751E).toPoly=dirn751P := dz2n751_norm

def dirn752E : RingExpr := dz2n752E
def dirn752P : Lean.Grind.CommRing.Poly := dz2n752P
theorem dirn752_norm : (reflectRing dirn752E).toPoly=dirn752P := dz2n752_norm

def dirn753E : RingExpr := dz2n753E
def dirn753P : Lean.Grind.CommRing.Poly := dz2n753P
theorem dirn753_norm : (reflectRing dirn753E).toPoly=dirn753P := dz2n753_norm

def dirn754E : RingExpr := dz2n754E
def dirn754P : Lean.Grind.CommRing.Poly := dz2n754P
theorem dirn754_norm : (reflectRing dirn754E).toPoly=dirn754P := dz2n754_norm

def dirn755E : RingExpr := dz2n755E
def dirn755P : Lean.Grind.CommRing.Poly := dz2n755P
theorem dirn755_norm : (reflectRing dirn755E).toPoly=dirn755P := dz2n755_norm

def dirn756E : RingExpr := dz2n756E
def dirn756P : Lean.Grind.CommRing.Poly := dz2n756P
theorem dirn756_norm : (reflectRing dirn756E).toPoly=dirn756P := dz2n756_norm

def dirn757E : RingExpr := dz2n757E
def dirn757P : Lean.Grind.CommRing.Poly := dz2n757P
theorem dirn757_norm : (reflectRing dirn757E).toPoly=dirn757P := dz2n757_norm

def dirn758E : RingExpr := dz2n758E
def dirn758P : Lean.Grind.CommRing.Poly := dz2n758P
theorem dirn758_norm : (reflectRing dirn758E).toPoly=dirn758P := dz2n758_norm

def dirn759E : RingExpr := dz2n759E
def dirn759P : Lean.Grind.CommRing.Poly := dz2n759P
theorem dirn759_norm : (reflectRing dirn759E).toPoly=dirn759P := dz2n759_norm

def dirn760E : RingExpr := dz2n760E
def dirn760P : Lean.Grind.CommRing.Poly := dz2n760P
theorem dirn760_norm : (reflectRing dirn760E).toPoly=dirn760P := dz2n760_norm

def dirn761E : RingExpr := dz2n761E
def dirn761P : Lean.Grind.CommRing.Poly := dz2n761P
theorem dirn761_norm : (reflectRing dirn761E).toPoly=dirn761P := dz2n761_norm

def dirn762E : RingExpr := dz2n762E
def dirn762P : Lean.Grind.CommRing.Poly := dz2n762P
theorem dirn762_norm : (reflectRing dirn762E).toPoly=dirn762P := dz2n762_norm

def dirn763E : RingExpr := dz2n763E
def dirn763P : Lean.Grind.CommRing.Poly := dz2n763P
theorem dirn763_norm : (reflectRing dirn763E).toPoly=dirn763P := dz2n763_norm

def dirn764E : RingExpr := dz2n764E
def dirn764P : Lean.Grind.CommRing.Poly := dz2n764P
theorem dirn764_norm : (reflectRing dirn764E).toPoly=dirn764P := dz2n764_norm

def dirn765E : RingExpr := dz2n765E
def dirn765P : Lean.Grind.CommRing.Poly := dz2n765P
theorem dirn765_norm : (reflectRing dirn765E).toPoly=dirn765P := dz2n765_norm

def dirn766E : RingExpr := dz2n766E
def dirn766P : Lean.Grind.CommRing.Poly := dz2n766P
theorem dirn766_norm : (reflectRing dirn766E).toPoly=dirn766P := dz2n766_norm

def dirn767E : RingExpr := dz2n767E
def dirn767P : Lean.Grind.CommRing.Poly := dz2n767P
theorem dirn767_norm : (reflectRing dirn767E).toPoly=dirn767P := dz2n767_norm

def dirn768E : RingExpr := dz2n768E
def dirn768P : Lean.Grind.CommRing.Poly := dz2n768P
theorem dirn768_norm : (reflectRing dirn768E).toPoly=dirn768P := dz2n768_norm

def dirn769E : RingExpr := dz2n769E
def dirn769P : Lean.Grind.CommRing.Poly := dz2n769P
theorem dirn769_norm : (reflectRing dirn769E).toPoly=dirn769P := dz2n769_norm

def dirn770E : RingExpr := dz2n770E
def dirn770P : Lean.Grind.CommRing.Poly := dz2n770P
theorem dirn770_norm : (reflectRing dirn770E).toPoly=dirn770P := dz2n770_norm

def dirn771E : RingExpr := dz2n771E
def dirn771P : Lean.Grind.CommRing.Poly := dz2n771P
theorem dirn771_norm : (reflectRing dirn771E).toPoly=dirn771P := dz2n771_norm

def dirn772E : RingExpr := dz2n772E
def dirn772P : Lean.Grind.CommRing.Poly := dz2n772P
theorem dirn772_norm : (reflectRing dirn772E).toPoly=dirn772P := dz2n772_norm

def dirn773E : RingExpr := dz2n773E
def dirn773P : Lean.Grind.CommRing.Poly := dz2n773P
theorem dirn773_norm : (reflectRing dirn773E).toPoly=dirn773P := dz2n773_norm

def dirn774E : RingExpr := dz2n774E
def dirn774P : Lean.Grind.CommRing.Poly := dz2n774P
theorem dirn774_norm : (reflectRing dirn774E).toPoly=dirn774P := dz2n774_norm

def dirn775E : RingExpr := dz2n775E
def dirn775P : Lean.Grind.CommRing.Poly := dz2n775P
theorem dirn775_norm : (reflectRing dirn775E).toPoly=dirn775P := dz2n775_norm

def dirn776E : RingExpr := dz2n776E
def dirn776P : Lean.Grind.CommRing.Poly := dz2n776P
theorem dirn776_norm : (reflectRing dirn776E).toPoly=dirn776P := dz2n776_norm

def dirn777E : RingExpr := dz2n777E
def dirn777P : Lean.Grind.CommRing.Poly := dz2n777P
theorem dirn777_norm : (reflectRing dirn777E).toPoly=dirn777P := dz2n777_norm

def dirn778E : RingExpr := dz2n778E
def dirn778P : Lean.Grind.CommRing.Poly := dz2n778P
theorem dirn778_norm : (reflectRing dirn778E).toPoly=dirn778P := dz2n778_norm

def dirn779E : RingExpr := dz2n779E
def dirn779P : Lean.Grind.CommRing.Poly := dz2n779P
theorem dirn779_norm : (reflectRing dirn779E).toPoly=dirn779P := dz2n779_norm

def dirn780E : RingExpr := dz2n780E
def dirn780P : Lean.Grind.CommRing.Poly := dz2n780P
theorem dirn780_norm : (reflectRing dirn780E).toPoly=dirn780P := dz2n780_norm

def dirn781E : RingExpr := dz2n781E
def dirn781P : Lean.Grind.CommRing.Poly := dz2n781P
theorem dirn781_norm : (reflectRing dirn781E).toPoly=dirn781P := dz2n781_norm

def dirn782E : RingExpr := dz2n782E
def dirn782P : Lean.Grind.CommRing.Poly := dz2n782P
theorem dirn782_norm : (reflectRing dirn782E).toPoly=dirn782P := dz2n782_norm

def dirn783E : RingExpr := dz2n783E
def dirn783P : Lean.Grind.CommRing.Poly := dz2n783P
theorem dirn783_norm : (reflectRing dirn783E).toPoly=dirn783P := dz2n783_norm

def dirn784E : RingExpr := dz2n784E
def dirn784P : Lean.Grind.CommRing.Poly := dz2n784P
theorem dirn784_norm : (reflectRing dirn784E).toPoly=dirn784P := dz2n784_norm

def dirn785E : RingExpr := dz2n785E
def dirn785P : Lean.Grind.CommRing.Poly := dz2n785P
theorem dirn785_norm : (reflectRing dirn785E).toPoly=dirn785P := dz2n785_norm

def dirn786E : RingExpr := dz2n786E
def dirn786P : Lean.Grind.CommRing.Poly := dz2n786P
theorem dirn786_norm : (reflectRing dirn786E).toPoly=dirn786P := dz2n786_norm

def dirn787E : RingExpr := dz2n787E
def dirn787P : Lean.Grind.CommRing.Poly := dz2n787P
theorem dirn787_norm : (reflectRing dirn787E).toPoly=dirn787P := dz2n787_norm

def dirn788E : RingExpr := dz2n788E
def dirn788P : Lean.Grind.CommRing.Poly := dz2n788P
theorem dirn788_norm : (reflectRing dirn788E).toPoly=dirn788P := dz2n788_norm

def dirn789E : RingExpr := dz2n789E
def dirn789P : Lean.Grind.CommRing.Poly := dz2n789P
theorem dirn789_norm : (reflectRing dirn789E).toPoly=dirn789P := dz2n789_norm

def dirn790E : RingExpr := dz2n790E
def dirn790P : Lean.Grind.CommRing.Poly := dz2n790P
theorem dirn790_norm : (reflectRing dirn790E).toPoly=dirn790P := dz2n790_norm

def dirn791E : RingExpr := dz2n791E
def dirn791P : Lean.Grind.CommRing.Poly := dz2n791P
theorem dirn791_norm : (reflectRing dirn791E).toPoly=dirn791P := dz2n791_norm

def dirn792E : RingExpr := dz2n792E
def dirn792P : Lean.Grind.CommRing.Poly := dz2n792P
theorem dirn792_norm : (reflectRing dirn792E).toPoly=dirn792P := dz2n792_norm

def dirn793E : RingExpr := dz2n793E
def dirn793P : Lean.Grind.CommRing.Poly := dz2n793P
theorem dirn793_norm : (reflectRing dirn793E).toPoly=dirn793P := dz2n793_norm

def dirn794E : RingExpr := dz2n794E
def dirn794P : Lean.Grind.CommRing.Poly := dz2n794P
theorem dirn794_norm : (reflectRing dirn794E).toPoly=dirn794P := dz2n794_norm

def dirn795E : RingExpr := dz2n795E
def dirn795P : Lean.Grind.CommRing.Poly := dz2n795P
theorem dirn795_norm : (reflectRing dirn795E).toPoly=dirn795P := dz2n795_norm

def dirn796E : RingExpr := dz2n796E
def dirn796P : Lean.Grind.CommRing.Poly := dz2n796P
theorem dirn796_norm : (reflectRing dirn796E).toPoly=dirn796P := dz2n796_norm

def dirn797E : RingExpr := dz2n797E
def dirn797P : Lean.Grind.CommRing.Poly := dz2n797P
theorem dirn797_norm : (reflectRing dirn797E).toPoly=dirn797P := dz2n797_norm

def dirn798E : RingExpr := dz2n798E
def dirn798P : Lean.Grind.CommRing.Poly := dz2n798P
theorem dirn798_norm : (reflectRing dirn798E).toPoly=dirn798P := dz2n798_norm

def dirn799E : RingExpr := dz2n799E
def dirn799P : Lean.Grind.CommRing.Poly := dz2n799P
theorem dirn799_norm : (reflectRing dirn799E).toPoly=dirn799P := dz2n799_norm

def dirn800E : RingExpr := dz2n800E
def dirn800P : Lean.Grind.CommRing.Poly := dz2n800P
theorem dirn800_norm : (reflectRing dirn800E).toPoly=dirn800P := dz2n800_norm

def dirn801E : RingExpr := dz2n801E
def dirn801P : Lean.Grind.CommRing.Poly := dz2n801P
theorem dirn801_norm : (reflectRing dirn801E).toPoly=dirn801P := dz2n801_norm

def dirn802E : RingExpr := dz2n802E
def dirn802P : Lean.Grind.CommRing.Poly := dz2n802P
theorem dirn802_norm : (reflectRing dirn802E).toPoly=dirn802P := dz2n802_norm

def dirn803E : RingExpr := dz2n803E
def dirn803P : Lean.Grind.CommRing.Poly := dz2n803P
theorem dirn803_norm : (reflectRing dirn803E).toPoly=dirn803P := dz2n803_norm

def dirn804E : RingExpr := dz2n804E
def dirn804P : Lean.Grind.CommRing.Poly := dz2n804P
theorem dirn804_norm : (reflectRing dirn804E).toPoly=dirn804P := dz2n804_norm

def dirn805E : RingExpr := dz2n805E
def dirn805P : Lean.Grind.CommRing.Poly := dz2n805P
theorem dirn805_norm : (reflectRing dirn805E).toPoly=dirn805P := dz2n805_norm

def dirn806E : RingExpr := dz2n806E
def dirn806P : Lean.Grind.CommRing.Poly := dz2n806P
theorem dirn806_norm : (reflectRing dirn806E).toPoly=dirn806P := dz2n806_norm

def dirn807E : RingExpr := dz2n807E
def dirn807P : Lean.Grind.CommRing.Poly := dz2n807P
theorem dirn807_norm : (reflectRing dirn807E).toPoly=dirn807P := dz2n807_norm

def dirn808E : RingExpr := dz2n808E
def dirn808P : Lean.Grind.CommRing.Poly := dz2n808P
theorem dirn808_norm : (reflectRing dirn808E).toPoly=dirn808P := dz2n808_norm

def dirn809E : RingExpr := dz2n809E
def dirn809P : Lean.Grind.CommRing.Poly := dz2n809P
theorem dirn809_norm : (reflectRing dirn809E).toPoly=dirn809P := dz2n809_norm

def dirn810E : RingExpr := dz2n810E
def dirn810P : Lean.Grind.CommRing.Poly := dz2n810P
theorem dirn810_norm : (reflectRing dirn810E).toPoly=dirn810P := dz2n810_norm

def dirn811E : RingExpr := dz2n811E
def dirn811P : Lean.Grind.CommRing.Poly := dz2n811P
theorem dirn811_norm : (reflectRing dirn811E).toPoly=dirn811P := dz2n811_norm

def dirn812E : RingExpr := dz2n812E
def dirn812P : Lean.Grind.CommRing.Poly := dz2n812P
theorem dirn812_norm : (reflectRing dirn812E).toPoly=dirn812P := dz2n812_norm

def dirn813E : RingExpr := dz2n813E
def dirn813P : Lean.Grind.CommRing.Poly := dz2n813P
theorem dirn813_norm : (reflectRing dirn813E).toPoly=dirn813P := dz2n813_norm

end StackSorting.FiniteGraph
