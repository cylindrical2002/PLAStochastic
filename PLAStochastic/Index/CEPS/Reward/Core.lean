import PLAStochastic.Index.CEPS.Reward.Moment

/-! # The linear exponential-remainder estimate for renewal rewards -/

noncomputable section
open MeasureTheory Set Complex Filter
namespace PGM.WienerHopf

def rewardRenewalBound (D θ c K : ℝ) : ℝ :=
  D + 2 * renewalFactorBound c K * D ^ 2 / (c * (θ - c / 2)) + 7 * renewalFactorBound c K

def rewardLinearBound (D θ c K : ℝ) : ℝ :=
  1 + rewardRenewalBound D θ c K / (θ - c / 2) + renewalFactorBound c K / (θ - c / 4)

theorem reward_pole_shift (R β : ℂ) (x z : ℝ) :
    R * cexp (-β * (x - z : ℝ)) = R * cexp (-β * x) * cexp (β * z) := by
  rw [mul_assoc, ← exp_add]
  congr 2
  push_cast
  ring

variable {g b : ℝ → ℂ} {D θ c K B : ℝ} {β : ℂ} {L : ℂ → ℂ}

theorem halfBdd_source_of_exp (hb : Measurable b) (hB0 : 0 ≤ B) (hθ : 0 ≤ θ)
    (hB : ∀ z, 0 ≤ z → ‖b z‖ ≤ B * Real.exp (-θ * z)) : HalfBdd (halfLine b) := by
  refine halfBdd_halfLine hb (fun _ => ⟨B, hB0, fun z hz _ => ?_⟩)
  exact (hB z hz).trans (mul_le_of_le_one_right hB0
    (Real.exp_le_one_iff.mpr (by nlinarith)))

theorem reward_remainder_decomposition (hu : HalfBdd (renewalDensity g))
    (hb : Measurable b) (hbs : HalfBdd (halfLine b))
    (hB : ∀ z, 0 ≤ z → ‖b z‖ ≤ B * Real.exp (-θ * z))
    (hβ : ‖β‖ < θ) {x : ℝ} (hx : 0 ≤ x) :
    rewardSolution g b x - renewalRes g β * cexp (-β * x) * rewardMoment β b =
      b x + (∫ z in Ioo 0 x,
        (renewalDensity g (x - z) - renewalRes g β * cexp (-β * (x - z : ℝ))) * b z) -
      renewalRes g β * cexp (-β * x) * (∫ z in Ioi x, cexp (β * z) * b z) := by
  have hm := integrableOn_rewardMoment_tail hb hB le_rfl hβ (x := 0) le_rfl
  have hs : Ioo (0 : ℝ) x ⊆ Ioi 0 := fun _ hz => hz.1
  have hp : IntegrableOn (fun z : ℝ => renewalRes g β * cexp (-β * (x - z : ℝ)) * b z)
      (Ioo 0 x) := by
    have hp₀ : IntegrableOn (fun z : ℝ =>
        (renewalRes g β * cexp (-β * x)) * (cexp (β * z) * b z)) (Ioo 0 x) :=
      (hm.mono_set hs).const_mul _
    refine hp₀.congr_fun ?_ measurableSet_Ioo
    intro z _
    dsimp only
    rw [reward_pole_shift]
    ring
  have hi : IntegrableOn (fun z : ℝ => renewalDensity g (x - z) * b z) (Ioo 0 x) := by
    refine ((hbs.integrable_convC_integrand hu x).integrableOn).congr_fun ?_ measurableSet_Ioo
    intro z hz
    dsimp only
    rw [halfLine_of_nonneg _ hz.1.le]
    ring
  have hd : (∫ z in Ioo 0 x,
      (renewalDensity g (x - z) - renewalRes g β * cexp (-β * (x - z : ℝ))) * b z) =
      (∫ z in Ioo 0 x, renewalDensity g (x - z) * b z) -
        renewalRes g β * cexp (-β * x) * (∫ z in Ioo 0 x, cexp (β * z) * b z) := by
    rw [← integral_const_mul, ← integral_sub hi
      ((hm.mono_set hs).const_mul (renewalRes g β * cexp (-β * x)))]
    apply setIntegral_congr_fun measurableSet_Ioo
    intro z _
    dsimp only
    rw [reward_pole_shift]
    ring
  rw [rewardSolution, Pi.add_apply, halfLine_of_nonneg _ hx,
    convC_halfLine_eq_interval hu, rewardMoment_split hb hB le_rfl hβ hx, hd]
  ring

/-- The linear core estimate (L) for any exponentially decaying source. -/
theorem norm_rewardSolution_sub_pole_le (h : ExpRenewalData g D θ c β L K)
    (hb : Measurable b) (hB0 : 0 ≤ B)
    (hB : ∀ z, 0 ≤ z → ‖b z‖ ≤ B * Real.exp (-θ * z)) {x : ℝ} (hx : 0 ≤ x) :
    ‖rewardSolution g b x - renewalRes g β * cexp (-β * x) * rewardMoment β b‖ ≤
      rewardLinearBound D θ c K * B * Real.exp (-(c / 2) * x) := by
  let u := renewalDensity g
  let R := renewalRes g β
  let C := rewardRenewalBound D θ c K
  have hc := h.c₀_pos
  have ht := h.c₀_lt
  have hD := h.density.nonneg_D
  have hfac := h.factorBound_pos
  have hden : 0 < θ - c / 2 := by linarith
  have hden' : 0 < θ - c / 4 := by linarith
  have hC : 0 ≤ C := by unfold C rewardRenewalBound; positivity
  have hu := halfBdd_renewalDensity h.density h.θ_pos.le
  have hbs := halfBdd_source_of_exp hb hB0 h.θ_pos.le hB
  have hβ : ‖β‖ < θ := h.root_le.trans_lt (by linarith)
  have hm := integrableOn_rewardMoment_tail hb hB h.root_le (by linarith : c / 4 < θ)
    (x := 0) le_rfl
  have hs : Ioo (0 : ℝ) x ⊆ Ioi 0 := fun _ hz => hz.1
  have hiu : IntegrableOn (fun z : ℝ => u (x - z) * b z) (Ioo 0 x) := by
    refine ((hbs.integrable_convC_integrand hu x).integrableOn).congr_fun ?_ measurableSet_Ioo
    intro z hz
    dsimp only
    rw [halfLine_of_nonneg _ hz.1.le]
    ring
  have hip : IntegrableOn (fun z : ℝ => R * cexp (-β * (x - z : ℝ)) * b z) (Ioo 0 x) := by
    have hp₀ : IntegrableOn (fun z : ℝ => (R * cexp (-β * x)) * (cexp (β * z) * b z))
        (Ioo 0 x) := (hm.mono_set hs).const_mul _
    refine hp₀.congr_fun ?_ measurableSet_Ioo
    intro z _
    dsimp only
    rw [reward_pole_shift]
    ring
  have hir : IntegrableOn (fun z : ℝ => (u (x - z) - R * cexp (-β * (x - z : ℝ))) * b z)
      (Ioo 0 x) := (hiu.sub hip).congr_fun (fun z _ => by simp only [Pi.sub_apply]; ring)
        measurableSet_Ioo
  have hdom : IntegrableOn (fun z : ℝ => C * B * Real.exp (-(c / 2) * x) *
      Real.exp ((c / 2 - θ) * z)) (Ioi 0) :=
    (integrableOn_exp_mul_Ioi (by linarith) 0).const_mul _
  have her : ‖∫ z in Ioo 0 x, (u (x - z) - R * cexp (-β * (x - z : ℝ))) * b z‖ ≤
      C * B / (θ - c / 2) * Real.exp (-(c / 2) * x) := by
    calc
      _ ≤ ∫ z in Ioo 0 x, ‖(u (x - z) - R * cexp (-β * (x - z : ℝ))) * b z‖ :=
        norm_integral_le_integral_norm _
      _ ≤ ∫ z in Ioo 0 x, C * B * Real.exp (-(c / 2) * x) * Real.exp ((c / 2 - θ) * z) := by
        apply integral_mono_ae hir.norm (hdom.mono_set hs)
        refine (ae_restrict_iff' measurableSet_Ioo).mpr (Eventually.of_forall fun z hz => ?_)
        dsimp only
        rw [norm_mul]
        calc
          _ ≤ (C * Real.exp (-(c / 2) * (x - z))) * (B * Real.exp (-θ * z)) :=
            mul_le_mul (h.norm_renewalDensity_sub_le (by linarith [hz.2])) (hB z hz.1.le)
              (norm_nonneg _) (by positivity)
          _ = _ := by
            have he : Real.exp (-(c / 2) * (x - z)) * Real.exp (-θ * z) =
                Real.exp (-(c / 2) * x) * Real.exp ((c / 2 - θ) * z) := by
              rw [← Real.exp_add, ← Real.exp_add]
              congr 1
              ring
            calc
              _ = C * B * (Real.exp (-(c / 2) * (x - z)) * Real.exp (-θ * z)) := by ring
              _ = _ := by rw [he]; ring
      _ ≤ ∫ z in Ioi 0, C * B * Real.exp (-(c / 2) * x) * Real.exp ((c / 2 - θ) * z) :=
        setIntegral_mono_set hdom (Eventually.of_forall fun _ => by positivity)
          (Eventually.of_forall hs)
      _ = _ := by
        rw [integral_const_mul, integral_exp_mul_Ioi (by linarith) 0]
        simp only [mul_zero, Real.exp_zero]
        rw [show c / 2 - θ = -(θ - c / 2) by ring, div_neg]
        ring
  have htail : ‖R * cexp (-β * x) * (∫ z in Ioi x, cexp (β * z) * b z)‖ ≤
      renewalFactorBound c K * B / (θ - c / 4) * Real.exp (-(c / 2) * x) := by
    rw [norm_mul, norm_mul]
    have he : ‖cexp (-β * x)‖ ≤ Real.exp ((c / 4) * x) := by
      rw [norm_cexp_mul_ofReal', neg_re, neg_neg]
      apply Real.exp_le_exp.mpr
      exact mul_le_mul_of_nonneg_right
        ((neg_le_abs _).trans ((abs_re_le_norm _).trans h.root_le)) hx
    calc
      _ ≤ renewalFactorBound c K * Real.exp ((c / 4) * x) *
          (B / (θ - c / 4) * Real.exp (-(θ - c / 4) * x)) :=
        mul_le_mul (mul_le_mul h.norm_renewalRes_le he (norm_nonneg _) hfac.le)
          (norm_rewardMoment_tail_le hb hB h.root_le (by linarith) hx)
          (norm_nonneg _) (by positivity)
      _ = renewalFactorBound c K * B / (θ - c / 4) * Real.exp (-(θ - c / 2) * x) := by
        calc
          _ = renewalFactorBound c K * B / (θ - c / 4) *
              (Real.exp ((c / 4) * x) * Real.exp (-(θ - c / 4) * x)) := by ring
          _ = _ := by rw [← Real.exp_add]; congr 2; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by nlinarith)) (by positivity)
  rw [reward_remainder_decomposition hu hb hbs hB hβ hx]
  calc
    _ ≤ ‖b x‖ + ‖∫ z in Ioo 0 x, (u (x - z) - R * cexp (-β * (x - z : ℝ))) * b z‖ +
        ‖R * cexp (-β * x) * (∫ z in Ioi x, cexp (β * z) * b z)‖ :=
      (norm_sub_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ B * Real.exp (-(c / 2) * x) + C * B / (θ - c / 2) * Real.exp (-(c / 2) * x) +
        renewalFactorBound c K * B / (θ - c / 4) * Real.exp (-(c / 2) * x) := by
      apply add_le_add (add_le_add ?_ her) htail
      exact (hB x hx).trans (mul_le_mul_of_nonneg_left
        (Real.exp_le_exp.mpr (by nlinarith)) hB0)
    _ = _ := by unfold rewardLinearBound; dsimp [C]; ring

end PGM.WienerHopf
