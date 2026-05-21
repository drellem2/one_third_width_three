import OneThird.Step8.LayeredFromStep7

/-! Axiom audit for the finalised S7-F bridge `lem_layered_from_step7`
(mg-02cd, FULL REFACTOR Phase-2 Piece-3 sub-arc Z).

`lem_layered_from_step7` and the `compactifySelf` machinery depend only
on the standard `propext` / `Classical.choice` / `Quot.sound`.

`excPerturbLift_of_bridge_output` and the grid pipeline certificate
additionally carry `OneThird.LinearExt.brightwell_sharp_centred` —
**inherited** from the S7-F-D `exc_perturb` lift (F6b already carries
it; see `AXIOMS.md`). No `sorryAx`, no new project axiom. -/

#print axioms OneThird.Step8.lem_layered_from_step7
#print axioms OneThird.Step8.LayeredDecomposition.compactifySelf
#print axioms OneThird.Step8.LayeredDecomposition.compactifySelf_bandSet_nonempty
#print axioms OneThird.Step8.LayeredDecomposition.compactifySelf_K_le
#print axioms OneThird.Step8.excPerturbLift_of_bridge_output
#print axioms OneThird.Step8.GridChainLift.grid_lem_layered_from_step7
#print axioms OneThird.Step8.GridChainLift.gridLayeredFromStep7_w
#print axioms OneThird.Step8.GridChainLift.gridLayeredFromStep7_band_nonconstant
#print axioms OneThird.Step8.GridChainLift.gridLayeredFromStep7_K_ge_two
#print axioms OneThird.Step8.GridChainLift.grid_excPerturbLift_of_bridge
