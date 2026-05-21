import OneThird.MainTheorem
import OneThird.Step8.MainAssembly
import OneThird.Step8.TheoremE
import OneThird.Step8.TheoremEWiring
import OneThird.Step8.Cascade

/-! Headline theorems — full audit (mg-49a4) -/

#print axioms OneThird.width3_one_third_two_thirds
#print axioms OneThird.Step8.width3_one_third_two_thirds_assembled
#print axioms OneThird.width3_one_third_two_thirds_via_step8
#print axioms OneThird.Step8.mainAssembly
#print axioms OneThird.Step8.mainAssembly_smallN
#print axioms OneThird.Step8.cexImpliesLowBKExpansion
#print axioms OneThird.counterexample_implies_low_BK_expansion

/-! Piece 4 — Theorem E wiring (`mg-MA-ThmE`, mg-3638) -/

#print axioms OneThird.Step8.theoremE_lowConductanceWitness
#print axioms OneThird.Step8.theoremE_lowConductanceWitness_nonempty

/-! Piece 4 — Steps 1-7 cascade wiring (`mg-MA-Cascade`, mg-52e0).
`chainLiftData_of_cascade` and the supporting lemmas are axiom-free;
`stepsOneToSevenCascade` carries the one disclosed Steps-1-7 axiom. -/

#print axioms OneThird.Step8.chainLiftData_of_cascade
#print axioms OneThird.Step8.stepsOneToSevenCascade
#print axioms OneThird.Step8.GridChainLift.grid_Step5C_fires_bridge
