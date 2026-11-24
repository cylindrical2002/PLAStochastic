import PLAStochastic.Index.CEPS.Reference.Basic

/-! # Smooth exponentially bounded density of the actual CEPS reference law -/

namespace PGM

noncomputable section
open MeasureTheory ProbabilityTheory BrownianAffine Filter Set
open scoped Topology ContDiff

def cepsLambdaDensity (x : ℝ) : ℝ :=
  optimalMeanConstant * (-deriv optimalImageSeries (optimalMeanConstant * x))

theorem cepsLambda_survival (x : ℝ) :
    (cepsLambda : Measure ℝ).real (Ioi x) = optimalImageSeries (optimalMeanConstant * x) := by
  change (canonicalPreBrownianMeasure.map
    (fun w => optimalUnitLifetime canonicalBrownian w / optimalMeanConstant)).real (Ioi x) = _
  rw [Measure.real, Measure.map_apply_of_aemeasurable
    ((aemeasurable_optimalUnitLifetime isBrownianReal_canonicalBrownian).div_const _) measurableSet_Ioi,
    optimalImageSeries_eq_measureReal isBrownianReal_canonicalBrownian]
  apply congrArg ENNReal.toReal
  congr 1
  ext w
  simp only [mem_preimage, mem_Ioi, mem_ofPred_eq, lt_div_iff₀ optimalMeanConstant_pos]
  rw [mul_comm x optimalMeanConstant]

theorem cdf_cepsLambda (x : ℝ) :
    cdf (cepsLambda : Measure ℝ) x = 1 - optimalImageSeries (optimalMeanConstant * x) := by
  rw [cdf_eq_real, ← compl_Ioi, probReal_compl_eq_one_sub measurableSet_Ioi, cepsLambda_survival]

theorem hasDerivAt_cepsLambdaCDF (x : ℝ) :
    HasDerivAt (fun t => 1 - optimalImageSeries (optimalMeanConstant * t)) (cepsLambdaDensity x) x := by
  have hd := (contDiff_infty_iff_deriv.mp contDiff_optimalImageSeries).1
  have h := ((hd (optimalMeanConstant * x)).hasDerivAt.comp x
    ((hasDerivAt_id x).const_mul optimalMeanConstant)).const_sub 1
  convert! h using 1
  unfold cepsLambdaDensity
  ring

theorem contDiff_cepsLambdaDensity : ContDiff ℝ ∞ cepsLambdaDensity := by
  have hd := (contDiff_infty_iff_deriv.mp contDiff_optimalImageSeries).2
  exact contDiff_const.mul ((hd.comp (contDiff_const.mul contDiff_id)).neg)

theorem cepsLambdaDensity_nonneg (x : ℝ) : 0 ≤ cepsLambdaDensity x := by
  exact mul_nonneg optimalMeanConstant_pos.le (neg_nonneg.mpr antitone_optimalImageSeries.deriv_nonpos)

theorem cepsLambdaDensity_of_nonpos {x : ℝ} (hx : x ≤ 0) : cepsLambdaDensity x = 0 := by
  have h := iteratedDeriv_optimalImageSeries_succ_of_nonpos 0
    (mul_nonpos_of_nonneg_of_nonpos optimalMeanConstant_pos.le hx)
  have hd : deriv optimalImageSeries (optimalMeanConstant * x) = 0 := by
    simpa only [Nat.zero_add, iteratedDeriv_one] using h
  simp only [cepsLambdaDensity, hd, neg_zero, mul_zero]

theorem iteratedDeriv_cepsLambdaDensity (r : ℕ) (x : ℝ) :
    iteratedDeriv r cepsLambdaDensity x =
      -(optimalMeanConstant ^ (r + 1) *
        iteratedDeriv (r + 1) optimalImageSeries (optimalMeanConstant * x)) := by
  change iteratedDeriv r (fun t => optimalMeanConstant *
    (-deriv optimalImageSeries (optimalMeanConstant * t))) x = _
  rw [iteratedDeriv_const_mul_field, iteratedDeriv_fun_neg]
  have hd : ContDiff ℝ r (deriv optimalImageSeries) :=
    ((contDiff_infty_iff_deriv.mp contDiff_optimalImageSeries).2).of_le
      (by exact_mod_cast (le_top : (r : ℕ∞) ≤ ⊤))
  rw [iteratedDeriv_comp_const_mul hd, ← iteratedDeriv_succ', pow_succ]
  ring

theorem iteratedDeriv_cepsLambdaDensity_of_nonpos (r : ℕ) {x : ℝ} (hx : x ≤ 0) :
    iteratedDeriv r cepsLambdaDensity x = 0 := by
  rw [iteratedDeriv_cepsLambdaDensity, iteratedDeriv_optimalImageSeries_succ_of_nonpos r
    (mul_nonpos_of_nonneg_of_nonpos optimalMeanConstant_pos.le hx), mul_zero, neg_zero]

theorem iteratedDeriv_cepsLambdaDensity_exponential_bound (r : ℕ) :
    ∃ A θ : ℝ, 0 ≤ A ∧ 0 < θ ∧ ∀ x : ℝ,
      ‖iteratedDeriv r cepsLambdaDensity x‖ ≤ A * Real.exp (-θ * x) := by
  obtain ⟨A, ρ, hA, hρ, hb⟩ := iteratedDeriv_optimalImageSeries_exponential_bound_nonneg (r + 1)
  have hκ := optimalMeanConstant_pos
  refine ⟨optimalMeanConstant ^ (r + 1) * A, ρ * optimalMeanConstant,
    by positivity, mul_pos hρ hκ, fun x => ?_⟩
  by_cases hx : x ≤ 0
  · rw [iteratedDeriv_cepsLambdaDensity_of_nonpos r hx, norm_zero]
    positivity
  · rw [iteratedDeriv_cepsLambdaDensity, norm_neg, norm_mul, Real.norm_eq_abs,
      abs_of_nonneg (pow_nonneg hκ.le _), Real.norm_eq_abs]
    calc
      _ ≤ optimalMeanConstant ^ (r + 1) * (A * Real.exp (-ρ * (optimalMeanConstant * x))) :=
        mul_le_mul_of_nonneg_left (hb _ (mul_nonneg hκ.le (le_of_not_ge hx))) (pow_nonneg hκ.le _)
      _ = _ := by ring_nf

theorem exists_integrable_expWeighted_iteratedDeriv_cepsLambdaDensity (r : ℕ) :
    ∃ η : ℝ, 0 < η ∧
      Integrable (fun x : ℝ => Real.exp (η * |x|) * iteratedDeriv r cepsLambdaDensity x) := by
  obtain ⟨A, θ, hA, hθ, hb⟩ := iteratedDeriv_cepsLambdaDensity_exponential_bound r
  refine ⟨θ / 2, by positivity, ?_⟩
  have hi : IntegrableOn (fun x : ℝ => A * Real.exp (-(θ / 2) * x)) (Ioi (0 : ℝ)) :=
    (integrableOn_exp_mul_Ioi (by linarith : -(θ / 2) < 0) 0).const_mul A
  have hgi : Integrable ((Ioi (0 : ℝ)).indicator (fun x => A * Real.exp (-(θ / 2) * x))) :=
    (integrable_indicator_iff measurableSet_Ioi).mpr hi
  have hc : Continuous (iteratedDeriv r cepsLambdaDensity) :=
    contDiff_cepsLambdaDensity.continuous_iteratedDeriv r (by
      exact_mod_cast (le_top : (r : ℕ∞) ≤ ⊤))
  apply hgi.mono' ((Real.continuous_exp.comp (continuous_const.mul continuous_abs)).mul hc).aestronglyMeasurable
  apply Eventually.of_forall
  intro x
  change ‖Real.exp (θ / 2 * |x|) * iteratedDeriv r cepsLambdaDensity x‖ ≤
    (Ioi (0 : ℝ)).indicator (fun x => A * Real.exp (-(θ / 2) * x)) x
  by_cases hx : 0 < x
  · rw [indicator_of_mem (show x ∈ Ioi (0 : ℝ) from hx), Real.norm_eq_abs,
      abs_mul, abs_of_pos (Real.exp_pos _), abs_of_pos hx]
    calc
      _ ≤ Real.exp (θ / 2 * x) * (A * Real.exp (-θ * x)) :=
        mul_le_mul_of_nonneg_left (by simpa only [Real.norm_eq_abs] using hb x) (Real.exp_nonneg _)
      _ = A * Real.exp (-(θ / 2) * x) := by
        rw [mul_left_comm, ← Real.exp_add]
        congr 1
        congr 1
        ring
  · rw [indicator_of_notMem (show x ∉ Ioi (0 : ℝ) from hx),
      iteratedDeriv_cepsLambdaDensity_of_nonpos r (le_of_not_gt hx), mul_zero, norm_zero]

theorem integrable_expWeighted_iteratedDeriv_cepsLambdaDensity_mono (r : ℕ) {η ζ : ℝ}
    (hηζ : η ≤ ζ)
    (hi : Integrable (fun x : ℝ => Real.exp (ζ * |x|) * iteratedDeriv r cepsLambdaDensity x)) :
    Integrable (fun x : ℝ => Real.exp (η * |x|) * iteratedDeriv r cepsLambdaDensity x) := by
  have hc : Continuous (iteratedDeriv r cepsLambdaDensity) :=
    contDiff_cepsLambdaDensity.continuous_iteratedDeriv r (by
      exact_mod_cast (le_top : (r : ℕ∞) ≤ ⊤))
  apply hi.norm.mono' ((Real.continuous_exp.comp (continuous_const.mul continuous_abs)).mul hc).aestronglyMeasurable
  apply Eventually.of_forall
  intro x
  change ‖Real.exp (η * |x|) * iteratedDeriv r cepsLambdaDensity x‖ ≤
    ‖Real.exp (ζ * |x|) * iteratedDeriv r cepsLambdaDensity x‖
  simp only [norm_mul, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos (η * |x|)), abs_of_pos (Real.exp_pos (ζ * |x|))]
  exact mul_le_mul_of_nonneg_right
    (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hηζ (abs_nonneg _))) (abs_nonneg _)

/-- Any finite derivative budget admits one common positive exponential weight. -/
theorem cepsLambdaDensity_finite_jet_integrability (m : ℕ) :
    ∃ η : ℝ, 0 < η ∧ ∀ r : ℕ, r ≤ m →
      Integrable (fun x : ℝ => Real.exp (η * |x|) * iteratedDeriv r cepsLambdaDensity x) := by
  induction m with
  | zero =>
    obtain ⟨η, hη, hi⟩ := exists_integrable_expWeighted_iteratedDeriv_cepsLambdaDensity 0
    exact ⟨η, hη, fun r hr => by simpa only [Nat.le_zero.mp hr] using hi⟩
  | succ m ih =>
    obtain ⟨η, hη, hi⟩ := ih
    obtain ⟨ζ, hζ, hj⟩ := exists_integrable_expWeighted_iteratedDeriv_cepsLambdaDensity (m + 1)
    refine ⟨min η ζ, lt_min hη hζ, fun r hr => ?_⟩
    by_cases h : r ≤ m
    · exact integrable_expWeighted_iteratedDeriv_cepsLambdaDensity_mono r (min_le_left _ _) (hi r h)
    · have he : r = m + 1 := by omega
      subst r
      exact integrable_expWeighted_iteratedDeriv_cepsLambdaDensity_mono _ (min_le_right _ _) hj

theorem cepsLambda_eq_withDensity :
    (cepsLambda : Measure ℝ) = volume.withDensity (fun x => ENNReal.ofReal (cepsLambdaDensity x)) := by
  have hF : ContDiff ℝ 1 (fun t => 1 - optimalImageSeries (optimalMeanConstant * t)) := by
    apply contDiff_const.sub
    apply (contDiff_optimalImageSeries.of_le (by simp)).comp
    fun_prop
  have he : deriv (fun t => 1 - optimalImageSeries (optimalMeanConstant * t)) = cepsLambdaDensity := by
    funext x
    exact (hasDerivAt_cepsLambdaCDF x).deriv
  simpa only [he] using Measure.eq_withDensity_of_contDiff_cdf (cepsLambda : Measure ℝ) hF cdf_cepsLambda

theorem cepsLambdaDensity_exponential_bound :
    ∃ D θ : ℝ, 0 < D ∧ 0 < θ ∧ ∀ x : ℝ, cepsLambdaDensity x ≤ D * Real.exp (-θ * x) := by
  obtain ⟨A, ρ, hA, hρ, hb⟩ := iteratedDeriv_optimalImageSeries_exponential_bound_nonneg 1
  have hκ := optimalMeanConstant_pos
  refine ⟨optimalMeanConstant * A + 1, ρ * optimalMeanConstant, by positivity,
    mul_pos hρ optimalMeanConstant_pos, fun x => ?_⟩
  by_cases hx : x ≤ 0
  · rw [cepsLambdaDensity_of_nonpos hx]
    positivity
  · have hx0 : 0 ≤ x := (lt_of_not_ge hx).le
    have hbound := hb (optimalMeanConstant * x) (mul_nonneg optimalMeanConstant_pos.le hx0)
    have hd : -deriv optimalImageSeries (optimalMeanConstant * x) ≤
        A * Real.exp (-ρ * (optimalMeanConstant * x)) := by
      exact (neg_le_abs _).trans (by simpa only [iteratedDeriv_one] using hbound)
    unfold cepsLambdaDensity
    calc
      _ ≤ optimalMeanConstant * (A * Real.exp (-ρ * (optimalMeanConstant * x))) :=
        mul_le_mul_of_nonneg_left hd optimalMeanConstant_pos.le
      _ = (optimalMeanConstant * A) * Real.exp (-(ρ * optimalMeanConstant) * x) := by ring_nf
      _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith) (Real.exp_nonneg _)

/-- The reference law satisfies the existing regular-law definition with no analytic inputs. -/
theorem exists_regLaw_cepsLambda :
    ∃ D θ : ℝ, 0 < D ∧ 0 < θ ∧
      RegLaw D θ optimalDispersionConstant optimalDispersionConstant cepsLambda := by
  obtain ⟨D, θ, hD, hθ, hb⟩ := cepsLambdaDensity_exponential_bound
  refine ⟨D, θ, hD, hθ, ?_⟩
  exact ⟨⟨cepsLambdaDensity, contDiff_cepsLambdaDensity.continuous.measurable,
    cepsLambdaDensity_nonneg, fun _ hx => cepsLambdaDensity_of_nonpos hx, hb,
    cepsLambda_eq_withDensity⟩, lawMean_cepsLambda, lawVar_cepsLambda.ge, lawVar_cepsLambda.le⟩

end

end PGM
