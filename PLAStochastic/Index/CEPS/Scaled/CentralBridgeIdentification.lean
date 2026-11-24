import PLAStochastic.Index.CEPS.Scaled.CentralBridgeFrequency
import PLAStochastic.Index.CEPS.Scaled.MorseChartIdentification
import PLAStochastic.Index.CEPS.Scaled.SurrogateBridge

/-! # Exact identification of the central continuation on actual frequencies -/

noncomputable section
open Complex Set Metric MeasureTheory Filter Topology
open PGM.WienerHopf
namespace PGM

variable {D θ v : ℝ} {ρW : Measure ℝ} {fW : ℝ → ℝ}
variable (dom : CepsCanonDomain D θ v) (hW : IsStepLaw ρW fW D θ v)
  (hθ : 0 < θ) (hD : 0 < D)

include hW hθ hD in
theorem cepsScaledSignedDiscount_eq_scaled (lam : ℝ) (z b : ℂ)
    (hmu : ‖b * (lam : ℂ)‖ < cepsChartMu D θ) :
    cepsScaledSignedDiscount D θ ρW lam (cepsScaledRootCoordinate D θ ρW lam z b) b =
      cepsComplexScaledDiscount lam z b := by
  have h := cepsScaledMorseRadicand_actual hW hθ hD (z := z) hmu
  rw [cepsScaledSignedDiscount, mul_pow, cepsScaledRootCoordinate, sqrt_sq_eq]
  unfold cepsComplexScaledDiscount
  linear_combination -h

include hW hθ hD in
theorem cepsScaledCentralSurrogateBridge_eq_of_fixed_roots (N : ℕ) (lam : ℝ) (z b : ℂ)
    (hmu : ‖b * (lam : ℂ)‖ < cepsChartMu D θ)
    (hp : cepsScaledSignedRoot D θ ρW lam z 1 b =
      cepsScaledMorseChart D θ ρW lam (cepsScaledRootCoordinate D θ ρW lam z b) b)
    (hm : cepsScaledSignedRoot D θ ρW lam z (-1) b =
      cepsScaledMorseChart D θ ρW lam (-cepsScaledRootCoordinate D θ ρW lam z b) b) :
    cepsScaledCentralSurrogateBridge dom ρW N lam z b = cepsScaledSurrogateBridge dom ρW N lam z b := by
  have hg : cepsScaledSignedSurrogateG dom ρW N lam (cepsScaledRootCoordinate D θ ρW lam z b) b =
      cepsScaledSurrogateG dom ρW N lam z b := by
    funext ξ
    unfold cepsScaledSignedSurrogateG cepsScaledBoundedSpatialG cepsScaledSurrogateG
    rw [cepsScaledSignedDiscount_eq_scaled hW hθ hD lam z b hmu]
  change cepsScaledSignedSurrogateBridge dom ρW N lam (cepsScaledRootCoordinate D θ ρW lam z b) b = _
  unfold cepsScaledSignedSurrogateBridge cepsScaledSurrogateBridge
    cepsScaledSignedSurrogateDenominator cepsScaledSurrogateDenominator
  rw [hg, hp, hm]

include hW hθ hD in
theorem cepsScaledCentralSurrogateBridge_eq (N : ℕ) (lam : ℝ) {z b : ℂ} (hz : 0 ≤ z.re)
    (hmu : ‖b * (lam : ℂ)‖ < cepsChartMu D θ) :
    cepsScaledCentralSurrogateBridge dom ρW N lam z b = cepsScaledSurrogateBridge dom ρW N lam z b := by
  apply cepsScaledCentralSurrogateBridge_eq_of_fixed_roots dom hW hθ hD N lam z b hmu
  · simpa only [one_mul] using cepsScaledSignedRoot_eq_fixed_chart dom hW hθ hD lam hz
      (by norm_num : ‖(1 : ℂ)‖ ≤ 1) b
  · simpa only [neg_one_mul] using cepsScaledSignedRoot_eq_fixed_chart dom hW hθ hD lam hz
      (by norm_num : ‖(-1 : ℂ)‖ ≤ 1) b

include hW hθ hD in
theorem cepsScaledCentralSurrogateBridge_eq_of_ne_scale (N : ℕ) (lam : ℝ) (z : ℂ) {b : ℂ}
    (hb : b ≠ 0) (hmu : ‖b * (lam : ℂ)‖ < cepsChartMu D θ) :
    cepsScaledCentralSurrogateBridge dom ρW N lam z b = cepsScaledSurrogateBridge dom ρW N lam z b := by
  apply cepsScaledCentralSurrogateBridge_eq_of_fixed_roots dom hW hθ hD N lam z b hmu
  · rw [cepsScaledSignedRoot_eq_div hW hθ hD lam z 1 hb,
      cepsScaledMorseChart_eq_div hW hθ hD _ _ hb, mul_one]
  · rw [cepsScaledSignedRoot_eq_div hW hθ hD lam z (-1) hb,
      cepsScaledMorseChart_eq_div hW hθ hD _ _ hb, mul_neg_one, neg_mul, mul_neg]

include hW hθ hD in
theorem cepsScaledCentralSurrogateBridge_eq_of_slit_zero (N : ℕ) (lam : ℝ) (z b : ℂ)
    (hmu : ‖b * (lam : ℂ)‖ < cepsChartMu D θ)
    (hbranch : cepsScaledMorseRadicand D θ ρW lam z 0 ∈ slitPlane) :
    cepsScaledCentralSurrogateBridge dom ρW N lam z b = cepsScaledSurrogateBridge dom ρW N lam z b := by
  have hd := (cepsScaledMorseRadicand_budget dom hW hθ hD (lam : ℂ) z).1
  have hc : DifferentiableAt ℂ (cepsScaledRootCoordinate D θ ρW lam z) 0 :=
    (differentiableAt_sqrt hbranch).comp 0
      ((hd 0 (mem_ball_self (dom.minimumScaleRadius_pos lam))).differentiableAt
        (ball_mem_nhds _ (dom.minimumScaleRadius_pos lam)))
  apply cepsScaledCentralSurrogateBridge_eq_of_fixed_roots dom hW hθ hD N lam z b hmu
  · simpa only [one_mul] using cepsScaledSignedRoot_eq_fixed_chart_of_differentiable hW hθ hD lam z 1 hc b
  · simpa only [neg_one_mul] using cepsScaledSignedRoot_eq_fixed_chart_of_differentiable hW hθ hD lam z (-1) hc b

include hW hθ hD in
theorem cepsScaledCentralSurrogateBridge_eventuallyEq (N : ℕ) (lam : ℝ) {z b : ℂ}
    (hz : 0 ≤ z.re) (hmu : ‖b * (lam : ℂ)‖ < cepsChartMu D θ) :
    (fun z => cepsScaledSurrogateBridge dom ρW N lam z b) =ᶠ[𝓝 z]
      (fun z => cepsScaledCentralSurrogateBridge dom ρW N lam z b) := by
  by_cases hb : b ≠ 0
  · exact Filter.Eventually.of_forall (fun u =>
      (cepsScaledCentralSurrogateBridge_eq_of_ne_scale dom hW hθ hD N lam u hb hmu).symm)
  by_cases hl : lam = 0
  · subst lam
    apply Filter.Eventually.of_forall
    intro u
    apply (cepsScaledCentralSurrogateBridge_eq_of_fixed_roots dom hW hθ hD N 0 u b hmu ?_ ?_).symm
    · simpa only [cepsScaledRootCoordinate, cepsScaledMorseRadicand, ofReal_zero, mul_zero, zero_pow (by norm_num : 2 ≠ 0),
        zero_mul, add_zero, mul_one, sub_zero, one_mul] using cepsScaledSignedRoot_zeroDrift_eq_chart (ρW := ρW) (D := D) (θ := θ) u 1 b
    · simpa only [cepsScaledRootCoordinate, cepsScaledMorseRadicand, ofReal_zero, mul_zero, zero_pow (by norm_num : 2 ≠ 0),
        zero_mul, add_zero, mul_one, sub_zero, neg_one_mul] using cepsScaledSignedRoot_zeroDrift_eq_chart (ρW := ρW) (D := D) (θ := θ) u (-1) b
  have hbranch := cepsScaledMorseRadicand_mem_slitPlane dom hW hθ hD lam hz (Or.inl hl)
    (mem_ball_self (radicandScaleRadius_budget dom hW hθ hD lam).1)
  have hc : Continuous (fun u : ℂ => cepsScaledMorseRadicand D θ ρW lam u 0) := by
    unfold cepsScaledMorseRadicand
    fun_prop
  have he := hc.tendsto z (isOpen_slitPlane.mem_nhds hbranch)
  filter_upwards [he] with u hu
  exact (cepsScaledCentralSurrogateBridge_eq_of_slit_zero dom hW hθ hD N lam u b hmu hu).symm

include hW hθ hD in
theorem cepsScaledCentralSurrogateBridge_deriv_eq (N : ℕ) (lam : ℝ) {z b : ℂ}
    (hz : 0 ≤ z.re) (hmu : ‖b * (lam : ℂ)‖ < cepsChartMu D θ) :
    deriv (fun z => cepsScaledSurrogateBridge dom ρW N lam z b) z =
      deriv (fun z => cepsScaledCentralSurrogateBridge dom ρW N lam z b) z :=
  (cepsScaledCentralSurrogateBridge_eventuallyEq dom hW hθ hD N lam hz hmu).deriv_eq

end PGM
