import PLAStochastic.Index.CEPS.Scaled.RootCoordinate
import Mathlib.Analysis.Complex.Schwarz

/-! # Genuine scale-zero extensions of the actual discounted roots -/

noncomputable section
open Complex MeasureTheory Set Metric
open PGM.WienerHopf
namespace PGM

def cepsScaledSignedRoot (D θ : ℝ) (ρW : Measure ℝ) (lam : ℝ) (z sign b : ℂ) : ℂ :=
  dslope (fun a : ℂ => cepsMorseRoot D θ ρW (a * lam)
    (a * sign * cepsScaledRootCoordinate D θ ρW lam z a)) 0 b

def CepsCanonDomain.actualRootScaleRadius {D θ v : ℝ} (dom : CepsCanonDomain D θ v)
    (lam : ℝ) (z : ℂ) : ℝ :=
  min (dom.radicandScaleRadius lam) (dom.rmax / (4 * (1 + dom.scaledRootCoordinateBound lam z)))

def CepsCanonDomain.actualScaledRootBound {D θ v : ℝ} (dom : CepsCanonDomain D θ v)
    (lam : ℝ) (z : ℂ) : ℝ := 2 / cepsVarLo D * |lam| + cepsChartK D * dom.scaledRootCoordinateBound lam z

variable {ρW : Measure ℝ} {fW : ℝ → ℝ} {D θ v : ℝ}
variable (dom : CepsCanonDomain D θ v) (hW : IsStepLaw ρW fW D θ v)
  (hθ : 0 < θ) (hD : 0 < D)

include hW hθ hD in
theorem actualRootScaleRadius_pos (lam : ℝ) (z : ℂ) : 0 < dom.actualRootScaleRadius lam z := by
  have hS : 0 ≤ dom.scaledRootCoordinateBound lam z := Real.sqrt_nonneg _
  exact lt_min (radicandScaleRadius_budget dom hW hθ hD lam).1 (div_pos dom.rmax_pos (by positivity))

include hW hθ hD in
theorem cepsScaledSignedRoot_budget (lam : ℝ) {z : ℂ} (hz : 0 ≤ z.re)
    {sign : ℂ} (hsign : ‖sign‖ ≤ 1) :
    DifferentiableOn ℂ (cepsScaledSignedRoot D θ ρW lam z sign)
      (ball 0 (dom.actualRootScaleRadius lam z)) ∧
    ∀ b ∈ ball (0 : ℂ) (dom.actualRootScaleRadius lam z),
      ‖cepsScaledSignedRoot D θ ρW lam z sign b‖ ≤ dom.actualScaledRootBound lam z := by
  let F : ℂ → ℂ := fun a => cepsMorseRoot D θ ρW (a * lam)
    (a * sign * cepsScaledRootCoordinate D θ ρW lam z a)
  let R := dom.actualRootScaleRadius lam z
  let C := dom.actualScaledRootBound lam z
  have hR : 0 < R := actualRootScaleRadius_pos dom hW hθ hD lam z
  have hS : 0 ≤ dom.scaledRootCoordinateBound lam z := Real.sqrt_nonneg _
  have hC : 0 ≤ C := by
    have := cepsVarLo_pos hD
    have := cepsChartK_pos hD
    unfold C CepsCanonDomain.actualScaledRootBound
    positivity
  have hsub : ball (0 : ℂ) R ⊆ ball 0 (dom.radicandScaleRadius lam) :=
    ball_subset_ball (min_le_left _ _)
  obtain ⟨hdS, hbS⟩ := cepsScaledRootCoordinate_budget dom hW hθ hD lam hz
  have hm : ∀ b ∈ ball (0 : ℂ) R, ‖b * (lam : ℂ)‖ ≤ dom.μ₀ := by
    intro b hb
    have hb' := (radicandScaleRadius_budget dom hW hθ hD lam).2
    have hs := ball_subset_ball hb' (hsub hb)
    have hs' := ball_subset_ball (half_le_self (dom.minimumScaleRadius_pos (lam : ℂ)).le) hs
    exact (mem_ball_zero_iff.mp (dom.minimumScale_mapsTo (lam : ℂ) hs')).le.trans
      (half_le_self dom.μ₀_pos.le)
  have hr : ∀ b ∈ ball (0 : ℂ) R,
      ‖b * sign * cepsScaledRootCoordinate D θ ρW lam z b‖ < dom.rmax := by
    intro b hb
    have hn : ‖b‖ < dom.rmax / (4 * (1 + dom.scaledRootCoordinateBound lam z)) :=
      (mem_ball_zero_iff.mp hb).trans_le (min_le_right _ _)
    have hp := (lt_div_iff₀ (by positivity : 0 < 4 * (1 + dom.scaledRootCoordinateBound lam z))).mp hn
    rw [norm_mul, norm_mul]
    have ht : ‖b‖ * ‖sign‖ * ‖cepsScaledRootCoordinate D θ ρW lam z b‖ ≤
        ‖b‖ * dom.scaledRootCoordinateBound lam z := by
      calc
        _ ≤ ‖b‖ * 1 * dom.scaledRootCoordinateBound lam z := by gcongr; exact hbS b (hsub hb)
        _ = _ := by ring
    have hv : ‖b‖ * dom.scaledRootCoordinateBound lam z < dom.rmax := by
      nlinarith [norm_nonneg b]
    exact ht.trans_lt hv
  have hF : DifferentiableOn ℂ F (ball 0 R) := by
    refine (differentiableOn_cepsMorseRoot hW hθ hD).comp
      ((differentiableOn_id.mul_const (lam : ℂ)).prodMk
        ((differentiableOn_id.mul_const sign).mul (hdS.mono hsub))) ?_
    intro b hb
    exact ⟨mem_ball_zero_iff.mpr (dom.μ_lt_chart (hm b hb)),
      mem_ball_zero_iff.mpr ((hr b hb).trans_le (by have := dom.rmax_r1; have := dom.rmax_pos; linarith))⟩
  have hF0 : F 0 = 0 := by
    dsimp [F]
    rw [zero_mul, zero_mul, zero_mul, cepsMorseRoot_zero hW hθ hD
      (by simpa using cepsChartMu_pos hD hθ), cepsMorseCenter_at_zero hW hθ hD]
  have hnorm : ∀ b ∈ ball (0 : ℂ) R, ‖F b‖ ≤ C * ‖b‖ := by
    intro b hb
    have hc := cepsMorseCenter_norm_le_drift dom hW hθ hD (hm b hb)
    have ht := norm_cepsMorseRoot_sub_center_le hW hθ hD (dom.μ_lt_chart (hm b hb))
      ((hr b hb).trans_le (by have := dom.rmax_r1; have := dom.rmax_pos; linarith))
    have hrt : ‖b * sign * cepsScaledRootCoordinate D θ ρW lam z b‖ ≤
        ‖b‖ * dom.scaledRootCoordinateBound lam z := by
      rw [norm_mul, norm_mul]
      calc
        _ ≤ ‖b‖ * 1 * dom.scaledRootCoordinateBound lam z := by gcongr; exact hbS b (hsub hb)
        _ = _ := by ring
    calc
      ‖F b‖ = ‖cepsMorseCenter D θ ρW (b * lam) + (F b - cepsMorseCenter D θ ρW (b * lam))‖ := by ring_nf
      _ ≤ _ := norm_add_le _ _
      _ ≤ 2 / cepsVarLo D * ‖b * (lam : ℂ)‖ + cepsChartK D *
          (‖b‖ * dom.scaledRootCoordinateBound lam z) := add_le_add hc
            (ht.trans (mul_le_mul_of_nonneg_left hrt (cepsChartK_pos hD).le))
      _ = C * ‖b‖ := by
        rw [norm_mul, norm_real, Real.norm_eq_abs]
        unfold C CepsCanonDomain.actualScaledRootBound
        ring
  have hmap : MapsTo F (ball 0 R) (closedBall (F 0) (R * C)) := by
    intro b hb
    rw [mem_closedBall, hF0, dist_zero_right]
    exact (hnorm b hb).trans (by nlinarith [mem_ball_zero_iff.mp hb])
  refine ⟨(differentiableOn_dslope (ball_mem_nhds 0 hR)).mpr hF, ?_⟩
  intro b hb
  change ‖dslope F 0 b‖ ≤ C
  simpa only [mul_div_cancel_left₀ C hR.ne'] using norm_dslope_le_div_of_mapsTo_ball hF hmap hb

include hW hθ hD in
theorem cepsScaledSignedRoot_scale_jet_le (lam : ℝ) {z : ℂ} (hz : 0 ≤ z.re)
    {sign : ℂ} (hsign : ‖sign‖ ≤ 1) (n : ℕ) :
    ‖iteratedDeriv n (cepsScaledSignedRoot D θ ρW lam z sign) 0‖ ≤
      (n.factorial : ℝ) * dom.actualScaledRootBound lam z / (dom.actualRootScaleRadius lam z / 2) ^ n := by
  obtain ⟨hd, hb⟩ := cepsScaledSignedRoot_budget dom hW hθ hD lam hz hsign
  exact norm_iteratedDeriv_le_of_ball n (actualRootScaleRadius_pos dom hW hθ hD lam z) hd hb

include hW hθ hD in
theorem cepsScaledSignedRoot_taylor_le (lam : ℝ) {z : ℂ} (hz : 0 ≤ z.re)
    {sign : ℂ} (hsign : ‖sign‖ ≤ 1) (n : ℕ) {b : ℂ}
    (hb : b ∈ ball (0 : ℂ) (dom.actualRootScaleRadius lam z / 2)) :
    ‖cepsScaledSignedRoot D θ ρW lam z sign b -
        complexTaylorSum (cepsScaledSignedRoot D θ ρW lam z sign) n 0 b‖ ≤
      ((n.factorial : ℝ) * dom.actualScaledRootBound lam z / (dom.actualRootScaleRadius lam z / 4) ^ n) *
        ‖b‖ ^ n := by
  obtain ⟨hd, hm⟩ := cepsScaledSignedRoot_budget dom hW hθ hD lam hz hsign
  simpa only [sub_zero] using norm_sub_complexTaylorSum_le_of_ball n
    (actualRootScaleRadius_pos dom hW hθ hD lam z) hd hm hb

include hW hθ hD in
theorem cepsScaledSignedRoot_eq_div (lam : ℝ) (z sign : ℂ) {b : ℂ} (hb : b ≠ 0) :
    cepsScaledSignedRoot D θ ρW lam z sign b =
      cepsMorseRoot D θ ρW (b * lam)
        (b * sign * cepsScaledRootCoordinate D θ ρW lam z b) / b := by
  rw [cepsScaledSignedRoot, dslope_of_ne _ hb, slope_def_field, zero_mul, zero_mul, zero_mul,
    cepsMorseRoot_zero hW hθ hD (by simpa using cepsChartMu_pos hD hθ),
    cepsMorseCenter_at_zero hW hθ hD, sub_zero, sub_zero]

include hW hθ hD in
theorem cepsScaledSignedRoot_plus_actual {b lam : ℝ} (hb : 0 < b) {z : ℂ}
    (hμ : ‖((b * lam : ℝ) : ℂ)‖ < cepsChartMu D θ) :
    cepsScaledSignedRoot D θ ρW lam z 1 b =
      cepsRootPlus D θ ρW ((b * lam : ℝ) : ℂ) (cepsScaledDiscount b lam z) / b := by
  have hb' : (b : ℂ) ≠ 0 := by exact_mod_cast hb.ne'
  rw [cepsScaledSignedRoot_eq_div hW hθ hD lam z 1 hb', cepsRootPlus,
    ofReal_mul, cepsScaledRootCoordinate_actual hW hθ hD hb hμ, mul_one]

include hW hθ hD in
theorem cepsScaledSignedRoot_minus_actual {b lam : ℝ} (hb : 0 < b) {z : ℂ}
    (hμ : ‖((b * lam : ℝ) : ℂ)‖ < cepsChartMu D θ) :
    cepsScaledSignedRoot D θ ρW lam z (-1) b =
      cepsRootMinus D θ ρW ((b * lam : ℝ) : ℂ) (cepsScaledDiscount b lam z) / b := by
  have hb' : (b : ℂ) ≠ 0 := by exact_mod_cast hb.ne'
  rw [cepsScaledSignedRoot_eq_div hW hθ hD lam z (-1) hb', cepsRootMinus,
    ofReal_mul, cepsScaledRootCoordinate_actual hW hθ hD hb hμ, mul_neg_one, neg_mul]

end PGM
