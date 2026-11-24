import PLAStochastic.Index.CEPS.Reward.Source

/-! # General overshoot test sources and an exponential test envelope -/

noncomputable section
open MeasureTheory Set Complex Filter
namespace PGM.WienerHopf

def rewardTestSource (g : ℝ → ℂ) (φ : ℝ → ℂ) (x : ℝ) : ℂ :=
  ∫ h : ℝ, if x < h then φ (h - x) * g h else 0

theorem rewardTestSource_eq_setIntegral (g φ : ℝ → ℂ) (x : ℝ) :
    rewardTestSource g φ x = ∫ h in Ioi x, φ (h - x) * g h := by
  change (∫ h, (Ioi x).indicator (fun h => φ (h - x) * g h) h) = _
  exact integral_indicator measurableSet_Ioi

variable {g φ : ℝ → ℂ} {D θ B κ : ℝ}

theorem measurable_rewardTestSource (hg : IsExpDensity g D θ) (hφ : Measurable φ) :
    Measurable (rewardTestSource g φ) := by
  have hm : Measurable (fun p : ℝ × ℝ =>
      if p.1 < p.2 then φ (p.2 - p.1) * g p.2 else 0) :=
    Measurable.ite (measurableSet_lt measurable_fst measurable_snd)
      ((hφ.comp (measurable_snd.sub measurable_fst)).mul
        (hg.measurable.comp measurable_snd)) measurable_const
  exact hm.stronglyMeasurable.integral_prod_right.measurable

theorem rewardTestSource_integrand_le (hg : IsExpDensity g D θ)
    (hφB : ∀ y, 0 ≤ y → ‖φ y‖ ≤ B * Real.exp (κ * y)) {x h : ℝ} (hh : x < h) :
    ‖φ (h - x) * g h‖ ≤ B * D * Real.exp (-κ * x) * Real.exp ((κ - θ) * h) := by
  rw [norm_mul]
  calc
    _ ≤ (B * Real.exp (κ * (h - x))) * (D * Real.exp (-θ * h)) :=
      mul_le_mul (hφB _ (by linarith)) (hg.norm_le h) (norm_nonneg _) (by
        have hb := hφB 0 le_rfl
        simp only [mul_zero, Real.exp_zero, mul_one] at hb
        exact mul_nonneg ((norm_nonneg _).trans hb) (Real.exp_pos _).le)
    _ = _ := by
      have he : Real.exp (κ * (h - x)) * Real.exp (-θ * h) =
          Real.exp (-κ * x) * Real.exp ((κ - θ) * h) := by
        rw [← Real.exp_add, ← Real.exp_add]
        congr 1
        ring
      calc
        _ = (B * D) * (Real.exp (κ * (h - x)) * Real.exp (-θ * h)) := by ring
        _ = _ := by rw [he]; ring

theorem integrableOn_rewardTestSource_integrand (hg : IsExpDensity g D θ)
    (hφ : Measurable φ) (hφB : ∀ y, 0 ≤ y → ‖φ y‖ ≤ B * Real.exp (κ * y))
    (hκ : κ < θ) (x : ℝ) :
    IntegrableOn (fun h => φ (h - x) * g h) (Ioi x) := by
  have hi : IntegrableOn (fun h : ℝ =>
      B * D * Real.exp (-κ * x) * Real.exp ((κ - θ) * h)) (Ioi x) :=
    (integrableOn_exp_mul_Ioi (by linarith) x).const_mul _
  exact hi.mono' ((hφ.comp (measurable_id.sub measurable_const)).mul
    hg.measurable).aestronglyMeasurable
    ((ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun h hh =>
      rewardTestSource_integrand_le hg hφB hh))

theorem norm_rewardTestSource_le (hg : IsExpDensity g D θ) (hφ : Measurable φ)
    (hφB : ∀ y, 0 ≤ y → ‖φ y‖ ≤ B * Real.exp (κ * y)) (hκ : κ < θ) (x : ℝ) :
    ‖rewardTestSource g φ x‖ ≤ B * D / (θ - κ) * Real.exp (-θ * x) := by
  have hi : IntegrableOn (fun h : ℝ =>
      B * D * Real.exp (-κ * x) * Real.exp ((κ - θ) * h)) (Ioi x) :=
    (integrableOn_exp_mul_Ioi (by linarith) x).const_mul _
  rw [rewardTestSource_eq_setIntegral]
  calc
    _ ≤ ∫ h in Ioi x, ‖φ (h - x) * g h‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ h in Ioi x, B * D * Real.exp (-κ * x) * Real.exp ((κ - θ) * h) :=
      integral_mono_ae (integrableOn_rewardTestSource_integrand hg hφ hφB hκ x).norm hi
        ((ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun h hh =>
          rewardTestSource_integrand_le hg hφB hh))
    _ = _ := by
      rw [integral_const_mul, integral_exp_mul_Ioi (by linarith) x]
      have he : Real.exp (-κ * x) * Real.exp ((κ - θ) * x) = Real.exp (-θ * x) := by
        rw [← Real.exp_add]
        congr 1
        ring
      calc
        _ = -(B * D * (Real.exp (-κ * x) * Real.exp ((κ - θ) * x))) / (κ - θ) := by ring
        _ = -(B * D * Real.exp (-θ * x)) / (κ - θ) := by rw [he]
        _ = _ := by rw [show κ - θ = -(θ - κ) by ring, div_neg]; ring

theorem halfBdd_rewardTestSource (hg : IsExpDensity g D θ) (hθ : 0 ≤ θ)
    (hφ : Measurable φ) (hφB : ∀ y, 0 ≤ y → ‖φ y‖ ≤ B * Real.exp (κ * y))
    (hκ : κ < θ) : HalfBdd (halfLine (rewardTestSource g φ)) := by
  have hB : 0 ≤ B := by
    have := hφB 0 le_rfl
    simpa using (norm_nonneg (φ 0)).trans this
  refine halfBdd_halfLine (measurable_rewardTestSource hg hφ) (fun _X => ?_)
  refine ⟨B * D / (θ - κ), by have := hg.nonneg_D; positivity, fun x hx _ => ?_⟩
  exact (norm_rewardTestSource_le hg hφ hφB hκ x).trans
    (mul_le_of_le_one_right (by have := hg.nonneg_D; positivity)
      (Real.exp_le_one_iff.mpr (by nlinarith)))

end PGM.WienerHopf
