import PLAStochastic.Index.CEPS.Normal.FunctionalFirstSlopeLiftLocal
import PLAStochastic.ForMathlib.Analysis.Complex.CompactAnalyticGermLift

/-! # Actual moving divided differences from a local analytic germ -/

noncomputable section
open Complex Filter Topology
namespace PGM

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem analyticAt_moving_dslope_local_zero {f : E × ℂ → ℂ} {a b : E → ℂ} {p₀ : E}
    (hf : AnalyticAt ℂ f (p₀, 0)) (ha : AnalyticAt ℂ a p₀) (hb : AnalyticAt ℂ b p₀)
    (ha₀ : a p₀ = 0) (hb₀ : b p₀ = 0) :
    AnalyticAt ℂ (fun p => dslope (fun z => f (p, z)) (a p) (b p)) p₀ := by
  let A : E → C(PUnit.{1}, ℂ) := fun p => ContinuousMap.const _ (a p)
  let B : E → C(PUnit.{1}, ℂ) := fun p => ContinuousMap.const _ (b p)
  have hA : AnalyticAt ℂ A p₀ := ha.continuousMap_const
  have hB : AnalyticAt ℂ B p₀ := hb.continuousMap_const
  have hA₀ : A p₀ = 0 := by simp only [A, ha₀, ContinuousMap.const_zero]
  have hB₀ : B p₀ = 0 := by simp only [B, hb₀, ContinuousMap.const_zero]
  obtain ⟨H, hH, _, he⟩ :=
    exists_analytic_parametric_compact_germ_lift (K := CompactSlopeLine PUnit.{1}) hf
  have hS : functionalFirstSlopeSegment A B p₀ = 0 := by
    simp only [functionalFirstSlopeSegment, hA₀, hB₀, map_zero, sub_self, mul_zero, add_zero]
  have hH' : AnalyticAt ℂ H (p₀, functionalFirstSlopeSegment A B p₀) := by
    simpa only [hS] using hH
  have h := ((ContinuousMap.evalCLM ℂ PUnit.unit).analyticAt _).comp
    (functionalFirstSlopeLift_analyticAt hH' hA hB)
  apply h.congr
  filter_upwards [functionalFirstSlopeLift_eventually_apply_local (f := fun p z => f (p, z)) hf hH he hA hB
      hA₀ hB₀]
    with p hp
  exact hp PUnit.unit

theorem analyticAt_moving_second_dslope_local_zero {f : E × ℂ → ℂ}
    {a b c : E → ℂ} {p₀ : E} (hf : AnalyticAt ℂ f (p₀, 0))
    (ha : AnalyticAt ℂ a p₀) (hb : AnalyticAt ℂ b p₀) (hc : AnalyticAt ℂ c p₀)
    (ha₀ : a p₀ = 0) (hb₀ : b p₀ = 0) (hc₀ : c p₀ = 0) :
    AnalyticAt ℂ (fun p => dslope (dslope (fun z => f (p, z)) (a p)) (b p) (c p)) p₀ := by
  let A : E → C(PUnit.{1}, ℂ) := fun p => ContinuousMap.const _ (a p)
  let B : E → C(PUnit.{1}, ℂ) := fun p => ContinuousMap.const _ (b p)
  let C₀ : E → C(PUnit.{1}, ℂ) := fun p => ContinuousMap.const _ (c p)
  have hA : AnalyticAt ℂ A p₀ := ha.continuousMap_const
  have hB : AnalyticAt ℂ B p₀ := hb.continuousMap_const
  have hC : AnalyticAt ℂ C₀ p₀ := hc.continuousMap_const
  have hA₀ : A p₀ = 0 := by simp only [A, ha₀, ContinuousMap.const_zero]
  have hB₀ : B p₀ = 0 := by simp only [B, hb₀, ContinuousMap.const_zero]
  have hC₀ : C₀ p₀ = 0 := by simp only [C₀, hc₀, ContinuousMap.const_zero]
  obtain ⟨H, hH, _, he⟩ :=
    exists_analytic_parametric_compact_germ_lift (K := CompactSlopeSquare PUnit.{1}) hf
  exact analyticAt_functional_second_dslope_of_local_lift (f := fun p z => f (p, z)) hf hH he
    hA hB hC hA₀ hB₀ hC₀ PUnit.unit

end PGM
