/-
Copyright (c) 2026 The OneThird Authors. All rights reserved.
Released under the MIT License.
-/

import OneThird.Basic
import OneThird.Poset
import OneThird.Mathlib.RelationPoset
import OneThird.Mathlib.RelationPoset.LinearExt
import OneThird.Mathlib.RelationPoset.Birkhoff
import OneThird.Mathlib.RelationPoset.FKG
import OneThird.Mathlib.LinearExtension.Fintype
import OneThird.Mathlib.LinearExtension.Subtype
import OneThird.Mathlib.LinearExtension.FiberSize
import OneThird.Mathlib.LinearExtension.Birkhoff
import OneThird.Mathlib.LinearExtension.FKG
import OneThird.Mathlib.LinearExtension.BrightwellAxiom
import OneThird.Mathlib.BKGraph
import OneThird.LinearExtension
import OneThird.Mathlib.SimpleGraph.EdgeBoundary
import OneThird.Step1.LocalCoords
import OneThird.RichPair
import OneThird.MainTheorem
import OneThird.Mathlib.Poset.Width
import OneThird.Mathlib.Poset.Indecomposable
import OneThird.Mathlib.Poset.Dilworth
import OneThird.Mathlib.Grid2D
import OneThird.Mathlib.DirichletForm
import OneThird.Step1.CommonChain
import OneThird.Step1.Corollaries
import OneThird.Step2.OneD
import OneThird.Step2.RowDecomp
import OneThird.Step2.FiberAvg
import OneThird.Step2.WeakGrid
import OneThird.Step2.PerFiber
import OneThird.Step2.Conclusion
import OneThird.Step3.LocalSign
import OneThird.Step3.CommonAxes
import OneThird.Step3.Step3Theorem
import OneThird.Step4.RectangleModel
import OneThird.Step4.DensityRegularization
import OneThird.Step4.Step4Theorem
import OneThird.Step5.EndpointMono
import OneThird.Step5.ConvexOverlap
import OneThird.Step5.FiberMass
import OneThird.Step5.Layering
import OneThird.Step5.SecondMoment
import OneThird.Step5.Dichotomy
import OneThird.Step6.ErrorControl
import OneThird.Step6.CommutingSquare
import OneThird.Step6.RichnessBound
import OneThird.Step6.Incoherence
import OneThird.Step6.OverlapCounting
import OneThird.Step6.Assembly
import OneThird.Step7.SignedThreshold
import OneThird.Step7.SignConsistency
import OneThird.Step7.Cocycle
import OneThird.Step7.Potential
import OneThird.Step7.SingleThreshold
import OneThird.Step7.Bandwidth
import OneThird.Step8.FrozenPair
import OneThird.Step8.OneElemPerturb
import OneThird.Step8.ExcPerturb
import OneThird.Step8.TheoremE
import OneThird.Step8.G2Constants
import OneThird.Step8.BipartiteEnum
import OneThird.Step8.Case3Struct
import OneThird.Step8.Case3Dispatch
import OneThird.Step8.Case2FKG
import OneThird.Step8.Case2BipartiteBound
import OneThird.Step8.Case2Rotation
import OneThird.Step8.Case3Residual
import OneThird.Step8.Case3Enum
import OneThird.Step8.Case3Enum.Certificate
import OneThird.Step8.Case3Enum.Correctness
import OneThird.Step8.Case3Enum.BalancedLift
import OneThird.Step8.Case3Enum.IrreducibleBridge
import OneThird.Step8.LayeredReduction
import OneThird.Step8.LayerOrdinal
import OneThird.Step8.LayeredBalanced
import OneThird.Step8.BoundedIrreducibleBalanced
import OneThird.Step8.Case3Enum.AdjIncompBridge
import OneThird.Step8.Case3Enum.EnumPosetsForBridge
import OneThird.Step8.Case3Enum.PredMaskBridge
import OneThird.Step8.Case3Enum.SymmetricLift
import OneThird.Step8.Window
import OneThird.Step8.SmallN
import OneThird.Step8.ChainPotentials
import OneThird.Step8.LayeredBridges
import OneThird.Step7.Assembly
import OneThird.Step8.MainAssembly
import OneThird.Bridge

/-!
# OneThird: the width-3 1/3–2/3 theorem

Root library for the Lean formalization of the width-3 case of the
1/3–2/3 conjecture. The main theorem is
`OneThird.width3_one_third_two_thirds` in
`OneThird/MainTheorem.lean` (discharged via the Step 8 assembly
in `OneThird/Step8/MainAssembly.lean`).
-/
