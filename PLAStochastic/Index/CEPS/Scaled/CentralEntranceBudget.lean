import PLAStochastic.Index.CEPS.Scaled.CentralBridgeTaylor
import PLAStochastic.Index.CEPS.Scaled.SurrogateEntranceBudget
import PLAStochastic.Index.CEPS.Scaled.PairPolynomialRadius

/-! # A uniform complete-entrance bound in the central frequency region -/

noncomputable section
open Complex Set Metric MeasureTheory
open PGM.WienerHopf
namespace PGM

def CepsCanonDomain.centralEntranceBound {D θ v : ℝ}
    (dom : CepsCanonDomain D θ v) (N : ℕ) (M : ℝ) : ℝ :=
  3 * dom.surrogateEntrancePolynomialConstant N M * (2 + Real.exp 2)

def CepsCanonDomain.centralPairScaleRadius {D θ v : ℝ}
    (dom : CepsCanonDomain D θ v) (N : ℕ) (M : ℝ) : ℝ :=
  min (dom.centralScaleRadius N M) (dom.pairPolynomialScaleBase N M / 3)

variable {D θ v : ℝ} {ρW : Measure ℝ} {fW : ℝ → ℝ}
variable (dom : CepsCanonDomain D θ v) (hW : IsStepLaw ρW fW D θ v)
  (hθ : 0 < θ) (hD : 0 < D)

include hW hθ hD in
theorem centralPairScaleRadius_pos (N : ℕ) (M : ℝ) : 0 < dom.centralPairScaleRadius N M :=
  lt_min (centralScaleRadius_pos dom hW hθ hD N M)
    (div_pos (pairPolynomialScaleBase_pos dom hW hθ hD N M) (by norm_num))

include hW hθ hD in
theorem centralFrequencyRadius_le_one (N : ℕ) (M : ℝ) : dom.centralFrequencyRadius N M ≤ 1 := by
  have hr1 : dom.centralCoordinateRadius N M ≤ 1 := min_le_left _ _
  have hr0 := (centralCoordinateRadius_pos dom hW hθ hD N M).le
  unfold CepsCanonDomain.centralFrequencyRadius
  nlinarith

include hW hθ hD in
theorem cepsScaledCentral_frequency_envelope (N : ℕ) (M : ℝ) {lam : ℝ} {z : ℂ}
    (hlam : |lam| ≤ dom.centralFrequencyDriftRadius N M)
    (hz : ‖z‖ ≤ dom.centralFrequencyRadius N M) :
    |lam| ≤ 1 ∧ ‖z‖ ≤ 1 ∧ 1 + |lam| + Real.sqrt ‖z‖ ≤ 3 := by
  have hl : |lam| ≤ 1 := hlam.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hz1 : ‖z‖ ≤ 1 := hz.trans (centralFrequencyRadius_le_one dom hW hθ hD N M)
  have hs : Real.sqrt ‖z‖ ≤ 1 := by
    exact (Real.sqrt_le_sqrt hz1).trans_eq (by norm_num)
  exact ⟨hl, hz1, by linarith⟩

include hW hθ hD in
theorem cepsScaledCentral_pairScale_mem (N : ℕ) (M : ℝ) {lam : ℝ} {z b : ℂ}
    (hlam : |lam| ≤ dom.centralFrequencyDriftRadius N M)
    (hz : ‖z‖ ≤ dom.centralFrequencyRadius N M)
    (hb : b ∈ ball (0 : ℂ) (dom.centralPairScaleRadius N M)) :
    b ∈ ball (0 : ℂ) (dom.centralScaleRadius N M) ∧
      b ∈ ball (0 : ℂ) (dom.entranceScaleRadius N M lam z) := by
  have hX := (cepsScaledCentral_frequency_envelope dom hW hθ hD N M hlam hz).2.2
  have hXP : 0 < 1 + |lam| + Real.sqrt ‖z‖ := by positivity
  have hrad : dom.pairPolynomialScaleBase N M / 3 ≤ dom.pairPolynomialScaleBase N M /
      (1 + |lam| + Real.sqrt ‖z‖) :=
    div_le_div_of_nonneg_left (pairPolynomialScaleBase_pos dom hW hθ hD N M).le hXP hX
  exact ⟨ball_subset_ball (min_le_left _ _) hb,
    ball_subset_ball ((min_le_right _ _).trans (hrad.trans
      (pairPolynomialScaleRadius_le dom hW hθ hD N M lam z).2)) hb⟩

include hW hθ hD in
theorem cepsScaledSurrogateEntrance_central_bound {m : ℕ} {η M : ℝ}
    (hf : CepsSobolevClass m η fW) (hη : 2 * dom.c₀ ≤ η)
    (hM : cepsSobolev m η fW ≤ M) (N : ℕ) (hN : N + 1 ≤ m) (lam : ℝ)
    (hlam : |lam| ≤ dom.centralFrequencyDriftRadius N M) {z b : ℂ} (hz : 0 ≤ z.re)
    (hznorm : ‖z‖ ≤ dom.centralFrequencyRadius N M)
    (hb : b ∈ ball (0 : ℂ) (dom.centralPairScaleRadius N M)) :
    ‖cepsScaledSurrogateEntrance dom ρW N lam z b‖ ≤ dom.centralEntranceBound N M := by
  obtain ⟨hbC, hbE⟩ := cepsScaledCentral_pairScale_mem dom hW hθ hD N M hlam hznorm hb
  have hL : ‖(lam : ℂ)‖ ≤ dom.centralFrequencyDriftRadius N M := by simpa only [norm_real, Real.norm_eq_abs] using hlam
  have hσ := cepsScaledCentral_radicand_bounds dom hW hθ hD N M hL hznorm hbC
  have hR := centralCoordinateRadius_pos dom hW hθ hD N M
  have hr : ‖cepsScaledRootCoordinate D θ ρW lam z b‖ ≤ dom.centralCoordinateRadius N M :=
    (norm_sqrt_lt hR (hσ.trans (half_lt_self (sq_pos_of_pos hR)))).le
  have hm := (cepsScaledCentral_chart_bounds dom hW hθ hD N M (hL.trans (min_le_left _ _))
    (show ‖-cepsScaledRootCoordinate D θ ρW lam z b‖ ≤ dom.centralCoordinateRadius N M by simpa using hr) hbC).2.2.2
  have hid := cepsScaledSignedRoot_eq_fixed_chart dom hW hθ hD lam hz (by norm_num : ‖(-1 : ℂ)‖ ≤ 1) b
  simp only [neg_one_mul] at hid
  have ha : ‖cepsScaledSignedRoot D θ ρW lam z (-1) b‖ ≤ 1 / 4 := by
    rw [hid]
    have hroot : dom.boundedSpatialRootRadius N M ≤ 1 / 4 := min_le_left _ _
    linarith
  obtain ⟨_, hz1, hX⟩ := cepsScaledCentral_frequency_envelope dom hW hθ hD N M hlam hznorm
  obtain ⟨_, hbhalf, _, _, hw⟩ := cepsScaledCentral_scale_bounds dom hW hθ hD N M
    (hL.trans (min_le_left _ _)) hr hbC
  have ht : ‖b * z‖ ≤ 1 / 2 := by
    rw [norm_mul]
    exact (mul_le_mul_of_nonneg_left hz1 (norm_nonneg b)).trans (by simpa only [mul_one] using hbhalf)
  have hw2 : ‖1 + b * lam‖ ≤ 2 := by
    have hh := norm_add_le ((1 + b * lam) - 1) (1 : ℂ)
    rw [sub_add_cancel, norm_one] at hh
    linarith
  have hexp : Real.exp (((cepsScaledSignedRoot D θ ρW lam z (-1) b - b * z) * (1 + b * lam)).re) ≤ Real.exp 2 := by
    apply Real.exp_le_exp.mpr
    apply (re_le_norm _).trans
    rw [norm_mul]
    have hh := norm_sub_le (cepsScaledSignedRoot D θ ρW lam z (-1) b) (b * z)
    nlinarith [norm_nonneg (1 + b * lam)]
  have hH := cepsScaledSurrogateEntrance_polynomial_budget dom hW hθ hD hf hη hM N hN lam hz hbE
  have hcoef := surrogateEntrancePolynomialConstant_pos dom hW hθ hD N M
  have he : 2 + Real.exp (((cepsScaledSignedRoot D θ ρW lam z (-1) b - b * z) * (1 + b * lam)).re) ≤
      2 + Real.exp 2 := by linarith
  have h := mul_le_mul (mul_le_mul_of_nonneg_left hX hcoef.le)
    he (by positivity) (by positivity)
  apply hH.trans
  apply h.trans_eq
  unfold CepsCanonDomain.centralEntranceBound
  ring

end PGM
