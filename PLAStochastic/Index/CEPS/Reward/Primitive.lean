import PLAStochastic.Index.CEPS.Reward.Moment

/-! # A finite-interval primitive formula for exponential rewards -/

noncomputable section
open MeasureTheory Set Complex Filter
namespace PGM.WienerHopf

variable {g : ℝ → ℂ} {D θ : ℝ}

theorem rewardSource_add_exp_conv (hg : IsExpDensity g D θ) (hθ : 0 ≤ θ)
    {a : ℂ} (ha : ‖a‖ < θ) (x : ℝ) :
    rewardSource g a x + convC g (halfLine (fun y : ℝ => cexp (a * y))) x =
      cexp (a * x) * laplaceC g (-a) := by
  have hi : Integrable (fun h : ℝ => if x < h then cexp (-a * (h - x : ℝ)) * g h else 0) := by
    have hIo := integrableOn_rewardSource_integrand hg (a₀ := ‖a‖) le_rfl ha x
    exact hIo.integrable_indicator measurableSet_Ioi
  have hE : HalfBdd (halfLine (fun y : ℝ => cexp (a * y))) := by
    simpa only [neg_neg] using halfBdd_exponential (-a)
  have hc := (hg.halfBdd hθ).integrable_convC_integrand hE x
  rw [rewardSource, convC, ← integral_add hi hc, laplaceC, ← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun h => ?_)
  dsimp only
  have he : cexp (-a * (h - x : ℝ)) = cexp (a * x) * cexp (-a * h) := by
    rw [← exp_add]
    congr 1
    push_cast
    ring
  by_cases hh : x < h
  · rw [if_pos hh, halfLine_of_neg _ (by linarith), mul_zero, add_zero, he]
    ring
  · rw [if_neg hh, zero_add, halfLine_of_nonneg _ (by linarith)]
    have he' : cexp (a * (x - h : ℝ)) = cexp (-a * (h - x : ℝ)) := by
      congr 1
      push_cast
      ring
    rw [he', he]
    ring

theorem halfLine_rewardSource_eq (hg : IsExpDensity g D θ) (hθ : 0 ≤ θ)
    {a : ℂ} (ha : ‖a‖ < θ) :
    halfLine (rewardSource g a) =
      (fun y : ℝ => laplaceC g (-a) * halfLine (fun z : ℝ => cexp (a * z)) y) -
        convC g (halfLine (fun z : ℝ => cexp (a * z))) := by
  have hE : HalfBdd (halfLine (fun y : ℝ => cexp (a * y))) := by
    simpa only [neg_neg] using halfBdd_exponential (-a)
  funext x
  simp only [Pi.sub_apply]
  by_cases hx : 0 ≤ x
  · rw [halfLine_of_nonneg _ hx, halfLine_of_nonneg _ hx]
    have he := rewardSource_add_exp_conv hg hθ ha x
    linear_combination he
  · rw [halfLine_of_neg _ (not_le.mp hx), halfLine_of_neg _ (not_le.mp hx), mul_zero,
      ((hg.halfBdd hθ).convC hE).eq_zero x (not_le.mp hx), sub_self]

theorem convC_const_mul_right (f h : ℝ → ℂ) (A : ℂ) (x : ℝ) :
    convC f (fun y => A * h y) x = A * convC f h x := by
  rw [convC, convC, ← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  dsimp only
  ring

theorem rewardSolution_primitive_conv (hg : IsExpDensity g D θ) (hθ : 0 ≤ θ)
    {a : ℂ} (ha : ‖a‖ < θ) {x : ℝ} (hx : 0 ≤ x) :
    rewardSolution g (rewardSource g a) x =
      laplaceC g (-a) * cexp (a * x) + (laplaceC g (-a) - 1) *
        convC (renewalDensity g) (halfLine (fun z : ℝ => cexp (a * z))) x := by
  let E := halfLine (fun y : ℝ => cexp (a * y))
  have hE : HalfBdd E := by simpa only [neg_neg] using halfBdd_exponential (-a)
  have hg' := hg.halfBdd hθ
  have hu := halfBdd_renewalDensity hg hθ
  have he : renewalDensity g = g + convC g (renewalDensity g) :=
    funext (renewalDensity_eq_add_convC hg hθ)
  have hr := congrArg (fun u => convC u E x) he
  rw [convC_add_left hg' (hg'.convC hu) hE] at hr
  have hd : convC (renewalDensity g) (convC g E) x =
      convC (renewalDensity g) E x - convC g E x := by
    have hcomm : convC (renewalDensity g) g = convC g (renewalDensity g) :=
      funext fun y => convC_comm (renewalDensity g) g y
    rw [convC_assoc hu hg' hE, hcomm]
    linear_combination -hr
  rw [rewardSolution, halfLine_rewardSource_eq hg hθ ha]
  change laplaceC g (-a) * E x - convC g E x +
    convC (renewalDensity g) ((fun y => laplaceC g (-a) * E y) - convC g E) x = _
  rw [convC_sub_right hu (hE.const_mul _) (hg'.convC hE)]
  rw [convC_const_mul_right, hd]
  have hEx : E x = cexp (a * x) := halfLine_of_nonneg _ hx
  rw [hEx]
  dsimp only [E]
  ring

theorem convC_exponential_primitive {u : ℝ → ℂ} (hu : HalfBdd u) (a : ℂ)
    {x : ℝ} (_hx : 0 ≤ x) :
    convC u (halfLine (fun z : ℝ => cexp (a * z))) x =
      cexp (a * x) * ∫ z in Ioo (0 : ℝ) x, cexp (-a * z) * u z := by
  rw [convC, ← integral_const_mul, ← integral_Icc_eq_integral_Ioo,
    ← integral_indicator measurableSet_Icc]
  refine integral_congr_ae (Eventually.of_forall fun z => ?_)
  dsimp only
  by_cases hz : z ∈ Icc (0 : ℝ) x
  · rw [indicator_of_mem hz, halfLine_of_nonneg _ (by linarith [hz.2])]
    have he : cexp (a * (x - z : ℝ)) = cexp (a * x) * cexp (-a * z) := by
      rw [← exp_add]
      congr 1
      push_cast
      ring
    rw [he]
    ring
  · rw [indicator_of_notMem hz]
    simp only [mem_Icc, not_and_or, not_le] at hz
    rcases hz with hz | hz
    · rw [hu.eq_zero z hz, zero_mul]
    · rw [halfLine_of_neg _ (by linarith), mul_zero]

theorem rewardSolution_primitive (hg : IsExpDensity g D θ) (hθ : 0 ≤ θ)
    {a : ℂ} (ha : ‖a‖ < θ) {x : ℝ} (hx : 0 ≤ x) :
    rewardSolution g (rewardSource g a) x = cexp (a * x) *
      (laplaceC g (-a) + (laplaceC g (-a) - 1) *
        ∫ z in (0 : ℝ)..x, cexp (-a * z) * renewalDensity g z) := by
  rw [rewardSolution_primitive_conv hg hθ ha hx,
    convC_exponential_primitive (halfBdd_renewalDensity hg hθ) a hx,
    ← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hx]
  ring

end PGM.WienerHopf
