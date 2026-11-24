import PLAStochastic.Index.CEPS.Scaled.SurrogateHolomorphy

/-! # Inverse surrogate-denominator budgets away from the joint origin -/

noncomputable section
open Complex Set Metric MeasureTheory
open PGM.WienerHopf
namespace PGM

def CepsCanonDomain.scaledCoordinateLower {D θ v : ℝ} (_dom : CepsCanonDomain D θ v)
    (lam : ℝ) (z : ℂ) : ℝ := Real.sqrt ((lam ^ 2 + ‖z‖) / (4 * v + 4))

def CepsCanonDomain.surrogateDeltaInverseBound {D θ v : ℝ} (dom : CepsCanonDomain D θ v)
    (lam : ℝ) (z : ℂ) : ℝ := 4 / dom.scaledComplexSector / min 1 (dom.scaledCoordinateLower lam z)

variable {D θ v : ℝ} {ρW : Measure ℝ} {fW : ℝ → ℝ}
variable (dom : CepsCanonDomain D θ v) (hW : IsStepLaw ρW fW D θ v)
  (hθ : 0 < θ) (hD : 0 < D)

include hW hθ hD in
theorem cepsScaledRootCoordinate_lower (N : ℕ) (M lam : ℝ) {z : ℂ} (hz : 0 ≤ z.re) {b : ℂ}
    (hb : b ∈ ball (0 : ℂ) (dom.surrogateScaleRadius N M lam z)) :
    dom.scaledCoordinateLower lam z ≤ ‖cepsScaledRootCoordinate D θ ρW lam z b‖ := by
  have hsub : dom.surrogateScaleRadius N M lam z ≤ dom.radicandScaleRadius lam / 2 := by
    have h1 : dom.surrogateScaleRadius N M lam z ≤ dom.canonScaleRadius lam z / 2 := min_le_left _ _
    have h2 : dom.canonScaleRadius lam z ≤ dom.actualRootScaleRadius lam z := min_le_left _ _
    have h3 : dom.actualRootScaleRadius lam z ≤ dom.radicandScaleRadius lam := min_le_left _ _
    exact h1.trans (div_le_div_of_nonneg_right (h2.trans h3) (by norm_num))
  have hco := cepsScaledRootCoordinate_complex_coercive dom hW hθ hD lam hz (ball_subset_ball hsub hb)
  have hv : 0 < 4 * v + 4 := by linarith [CepsCanonDomain.v_pos hW hθ hD]
  have hsq : (lam ^ 2 + ‖z‖) / (4 * v + 4) ≤ ‖cepsScaledRootCoordinate D θ ρW lam z b‖ ^ 2 :=
    (div_le_iff₀ hv).mpr (by nlinarith [hco])
  simpa only [CepsCanonDomain.scaledCoordinateLower, Real.sqrt_sq (norm_nonneg _)] using Real.sqrt_le_sqrt hsq

include hW hθ hD in
theorem scaledCoordinateLower_pos (lam : ℝ) {z : ℂ} (hne : 0 < lam ^ 2 + ‖z‖) :
    0 < dom.scaledCoordinateLower lam z := Real.sqrt_pos.mpr
      (div_pos hne (by linarith [CepsCanonDomain.v_pos hW hθ hD]))

include hW hθ hD in
theorem cepsScaledSurrogateDelta_inverse_budget {m : ℕ} {η M : ℝ}
    (hf : CepsSobolevClass m η fW) (hη : 2 * dom.c₀ ≤ η)
    (hM : cepsSobolev m η fW ≤ M) (N : ℕ) (hN : N + 1 ≤ m)
    (lam : ℝ) {z : ℂ} (hz : 0 ≤ z.re) (hne : 0 < lam ^ 2 + ‖z‖) :
    DifferentiableOn ℂ (fun b => (cepsScaledSurrogateDelta dom ρW N lam z b)⁻¹)
      (ball 0 (dom.surrogateScaleRadius N M lam z)) ∧
    ∀ b ∈ ball (0 : ℂ) (dom.surrogateScaleRadius N M lam z),
      ‖(cepsScaledSurrogateDelta dom ρW N lam z b)⁻¹‖ ≤ dom.surrogateDeltaInverseBound lam z := by
  have hc := (cepsScaledSurrogate_constants dom hW hθ hD N M).2.1
  have hT := scaledCoordinateLower_pos dom hW hθ hD lam hne
  have hlo : 0 < dom.scaledComplexSector / 4 * min 1 (dom.scaledCoordinateLower lam z) :=
    mul_pos (div_pos hc (by norm_num)) (lt_min (by norm_num) hT)
  have hbnd : ∀ b ∈ ball (0 : ℂ) (dom.surrogateScaleRadius N M lam z),
      dom.scaledComplexSector / 4 * min 1 (dom.scaledCoordinateLower lam z) ≤
        ‖cepsScaledSurrogateDelta dom ρW N lam z b‖ := by
    intro b hb
    exact (mul_le_mul_of_nonneg_left
      (min_le_min le_rfl (cepsScaledRootCoordinate_lower dom hW hθ hD N M lam hz hb))
      (div_nonneg hc.le (by norm_num))).trans
        (cepsScaledSurrogateDelta_lower_bound dom hW hθ hD hf hη hM N hN lam hz hb)
  have hnz : ∀ b ∈ ball (0 : ℂ) (dom.surrogateScaleRadius N M lam z),
      cepsScaledSurrogateDelta dom ρW N lam z b ≠ 0 :=
    fun b hb => norm_pos_iff.mp (hlo.trans_le (hbnd b hb))
  refine ⟨(cepsScaledSurrogateDelta_budget dom hW hθ hD hf hη hM N hN lam hz).1.inv hnz,
    fun b hb => ?_⟩
  rw [norm_inv]
  calc
    _ ≤ (dom.scaledComplexSector / 4 * min 1 (dom.scaledCoordinateLower lam z))⁻¹ :=
      (inv_le_inv₀ (hlo.trans_le (hbnd b hb)) hlo).mpr (hbnd b hb)
    _ = _ := by unfold CepsCanonDomain.surrogateDeltaInverseBound; ring

include hW hθ hD in
theorem cepsScaledSurrogateDelta_inverse_taylor_le {m : ℕ} {η M : ℝ}
    (hf : CepsSobolevClass m η fW) (hη : 2 * dom.c₀ ≤ η)
    (hM : cepsSobolev m η fW ≤ M) (N : ℕ) (hN : N + 1 ≤ m)
    (lam : ℝ) {z : ℂ} (hz : 0 ≤ z.re) (hne : 0 < lam ^ 2 + ‖z‖) (n : ℕ) {b : ℂ}
    (hb : b ∈ ball (0 : ℂ) (dom.surrogateScaleRadius N M lam z / 2)) :
    ‖(cepsScaledSurrogateDelta dom ρW N lam z b)⁻¹ -
      complexTaylorSum (fun b => (cepsScaledSurrogateDelta dom ρW N lam z b)⁻¹) n 0 b‖ ≤
      ((n.factorial : ℝ) * dom.surrogateDeltaInverseBound lam z /
        (dom.surrogateScaleRadius N M lam z / 4) ^ n) * ‖b‖ ^ n := by
  obtain ⟨hd, hm⟩ := cepsScaledSurrogateDelta_inverse_budget dom hW hθ hD hf hη hM N hN lam hz hne
  simpa only [sub_zero] using norm_sub_complexTaylorSum_le_of_ball n
    (surrogateScaleRadius_pos dom hW hθ hD N M lam z) hd hm hb

end PGM
