import PLAStochastic.Index.CEPS.Scaled.RadicandRelative
import PLAStochastic.ForMathlib.Analysis.Complex.SqrtScale

/-! # The genuine scaled square-root coordinate and its scale jets -/

noncomputable section
open Complex MeasureTheory Set Metric
open PGM.WienerHopf
namespace PGM

def cepsScaledRootCoordinate (D θ : ℝ) (ρW : Measure ℝ) (lam : ℝ) (z b : ℂ) : ℂ :=
  Complex.sqrt (cepsScaledMorseRadicand D θ ρW lam z b)

def CepsCanonDomain.scaledRootCoordinateBound {D θ v : ℝ} (_dom : CepsCanonDomain D θ v)
    (lam : ℝ) (z : ℂ) : ℝ := Real.sqrt (2 * (‖z‖ + lam ^ 2 / (2 * cepsVarLo D)))

variable {ρW : Measure ℝ} {fW : ℝ → ℝ} {D θ v : ℝ}
variable (dom : CepsCanonDomain D θ v) (hW : IsStepLaw ρW fW D θ v)
  (hθ : 0 < θ) (hD : 0 < D)

include hW hθ hD in
theorem cepsScaledRootCoordinate_budget (lam : ℝ) {z : ℂ} (hz : 0 ≤ z.re) :
    DifferentiableOn ℂ (cepsScaledRootCoordinate D θ ρW lam z)
      (ball 0 (dom.radicandScaleRadius lam)) ∧
    ∀ b ∈ ball (0 : ℂ) (dom.radicandScaleRadius lam),
      ‖cepsScaledRootCoordinate D θ ρW lam z b‖ ≤ dom.scaledRootCoordinateBound lam z := by
  have hsub : ball (0 : ℂ) (dom.radicandScaleRadius lam) ⊆ ball 0 (dom.minimumScaleRadius lam) :=
    ball_subset_ball ((radicandScaleRadius_budget dom hW hθ hD lam).2.trans
      (half_le_self (dom.minimumScaleRadius_pos (lam : ℂ)).le))
  obtain ⟨hd, _⟩ := cepsScaledMorseRadicand_budget dom hW hθ hD (lam : ℂ) z
  refine ⟨?_, ?_⟩
  · by_cases hne : lam ≠ 0 ∨ z ≠ 0
    · exact Complex.differentiableOn_sqrt.comp (hd.mono hsub)
        (fun b hb => cepsScaledMorseRadicand_mem_slitPlane dom hW hθ hD lam hz hne hb)
    · have hl : lam = 0 := not_ne_iff.mp (fun h => hne (Or.inl h))
      have hz0 : z = 0 := not_ne_iff.mp (fun h => hne (Or.inr h))
      subst lam
      subst z
      have he : cepsScaledRootCoordinate D θ ρW 0 0 = fun _ : ℂ => 0 := by
        funext b
        simp [cepsScaledRootCoordinate, cepsScaledMorseRadicand]
      rw [he]
      exact differentiableOn_const (0 : ℂ)
  · intro b hb
    have hrel := cepsScaledMorseRadicand_relative dom hW hθ hD lam hz hb
    let a : ℝ := lam ^ 2 / (2 * cepsStepVar ρW)
    have hV := cepsStepVar_pos hW hθ hD
    have ha : 0 ≤ a := by dsimp [a]; positivity
    have he : cepsScaledMorseRadicand D θ ρW lam z 0 = z + (a : ℂ) := by
      rw [cepsScaledMorseRadicand_zero hW hθ hD]
      dsimp [a]
      push_cast
      ring
    have haB : a ≤ lam ^ 2 / (2 * cepsVarLo D) :=
      div_le_div_of_nonneg_left (sq_nonneg _) (by have := cepsVarLo_pos hD; positivity)
        (by linarith [cepsVarLo_le hW hθ hD])
    have hbase : ‖cepsScaledMorseRadicand D θ ρW lam z 0‖ ≤
        ‖z‖ + lam ^ 2 / (2 * cepsVarLo D) := by
      rw [he]
      exact (norm_add_le z (a : ℂ)).trans (by
        rw [norm_real, Real.norm_eq_abs, abs_of_nonneg ha]
        exact add_le_add le_rfl haB)
    have hrad : ‖cepsScaledMorseRadicand D θ ρW lam z b‖ ≤
        2 * (‖z‖ + lam ^ 2 / (2 * cepsVarLo D)) := by
      have hnorm := norm_sub_norm_le (cepsScaledMorseRadicand D θ ρW lam z b)
        (cepsScaledMorseRadicand D θ ρW lam z 0)
      nlinarith [norm_nonneg (cepsScaledMorseRadicand D θ ρW lam z 0)]
    have hs : (dom.scaledRootCoordinateBound lam z) ^ 2 =
        2 * (‖z‖ + lam ^ 2 / (2 * cepsVarLo D)) := by
      unfold CepsCanonDomain.scaledRootCoordinateBound
      rw [Real.sq_sqrt (by have := cepsVarLo_pos hD; positivity)]
    have hroot := norm_complex_sqrt_sq (cepsScaledMorseRadicand D θ ρW lam z b)
    have hsq : ‖cepsScaledRootCoordinate D θ ρW lam z b‖ ^ 2 ≤
        (dom.scaledRootCoordinateBound lam z) ^ 2 := by
      rw [hs]
      exact hroot.le.trans hrad
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (Real.sqrt_nonneg _) (by norm_num : 2 ≠ 0)).mp hsq

include hW hθ hD in
theorem cepsScaledRootCoordinate_scale_jet_le (lam : ℝ) {z : ℂ} (hz : 0 ≤ z.re) (n : ℕ) :
    ‖iteratedDeriv n (cepsScaledRootCoordinate D θ ρW lam z) 0‖ ≤
      (n.factorial : ℝ) * dom.scaledRootCoordinateBound lam z / (dom.radicandScaleRadius lam / 2) ^ n := by
  obtain ⟨hd, hb⟩ := cepsScaledRootCoordinate_budget dom hW hθ hD lam hz
  exact norm_iteratedDeriv_le_of_ball n (radicandScaleRadius_budget dom hW hθ hD lam).1 hd hb

include hW hθ hD in
theorem cepsScaledRootCoordinate_actual {b lam : ℝ} (hb : 0 < b) {z : ℂ}
    (hμ : ‖((b * lam : ℝ) : ℂ)‖ < cepsChartMu D θ) :
    cepsRootR D θ ρW (b * lam) (cepsScaledDiscount b lam z) =
      (b : ℂ) * cepsScaledRootCoordinate D θ ρW lam z b := by
  have hm : ‖(b : ℂ) * (lam : ℂ)‖ < cepsChartMu D θ := by simpa only [ofReal_mul] using hμ
  unfold cepsScaledDiscount
  push_cast
  rw [cepsRootR, cepsScaledMorseRadicand_actual hW hθ hD hm,
    complex_sqrt_sq_real_mul hb, cepsScaledRootCoordinate]

end PGM
