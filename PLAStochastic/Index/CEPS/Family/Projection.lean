import PLAStochastic.Index.CEPS.Family.Defs
import PLAStochastic.Index.CEPS.DensityResidual

/-!
# Scalar and residual projections of a family expansion

The mean-one variance and the coupled orbit residual are read from the weighted
density expansion. A fixed polynomial weight costs only a constant against any
positive exponential weight, so the order-zero term of the weighted size suffices.
-/

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set

theorem sum_Icc_one_eq_sum_range (P : ℕ) (F : ℕ → ℝ) :
    ∑ n ∈ Finset.Icc 1 P, F n = ∑ i ∈ Finset.range P, F (i + 1) := by
  induction P with
  | zero => simp
  | succ P ih => rw [Finset.sum_Icc_succ_top (by omega), ih, Finset.sum_range_succ]

/-- Expectations of a law with a nonnegative measurable density. -/
theorem integral_eq_integral_density_mul {ν : Measure ℝ} {f : ℝ → ℝ} (hf : Measurable f)
    (hν : ν = volume.withDensity (fun x => ENNReal.ofReal (f x))) (hnn : ∀ x, 0 ≤ f x)
    (φ : ℝ → ℝ) : ∫ x, φ x ∂ν = ∫ x, f x * φ x := by
  rw [hν, integral_withDensity_eq_integral_toReal_smul hf.ennreal_ofReal
    (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  simp only [ENNReal.toReal_ofReal (hnn _), smul_eq_mul]

theorem exists_hellingerDensity_of_withDensity {f : ℝ → ℝ} (hf : Measurable f)
    (hnn : ∀ x, 0 ≤ f x) {ν : ProbabilityMeasure ℝ}
    (hν : (ν : Measure ℝ) = volume.withDensity (fun x => ENNReal.ofReal (f x))) :
    ∃ p : HellingerDensity (volume : Measure ℝ), p.density = f ∧ (ν : Measure ℝ) = p.toMeasure := by
  have hl : ∫⁻ x, ENNReal.ofReal (f x) = 1 := by
    have h := measure_univ (μ := (ν : Measure ℝ))
    rwa [hν, withDensity_apply _ MeasurableSet.univ, setLIntegral_univ] at h
  have hi : Integrable f := by
    refine ⟨hf.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ hnn), hl]
    exact ENNReal.one_lt_top
  have h1 : ∫ x, f x = 1 := by
    rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ hnn) hf.aestronglyMeasurable, hl,
      ENNReal.toReal_one]
  exact ⟨⟨f, hf, hnn, hi, h1⟩, rfl, hν⟩

theorem integrable_mul_of_abs_le_expWeight {η C : ℝ} {φ F : ℝ → ℝ}
    (hφ : AEStronglyMeasurable φ) (hF : AEStronglyMeasurable F)
    (hb : ∀ x, |φ x| ≤ C * Real.exp (η * |x|))
    (hi : Integrable (fun x => Real.exp (η * |x|) * F x)) :
    Integrable (fun x => φ x * F x) := by
  refine (hi.norm.const_mul C).mono' (hφ.mul hF) (ae_of_all _ fun x => ?_)
  rw [Real.norm_eq_abs, abs_mul, Real.norm_eq_abs, abs_mul, Real.abs_exp]
  calc
    |φ x| * |F x| ≤ C * Real.exp (η * |x|) * |F x| :=
      mul_le_mul_of_nonneg_right (hb x) (abs_nonneg _)
    _ = C * (Real.exp (η * |x|) * |F x|) := by ring

theorem abs_integral_mul_le_expWeighted {η C : ℝ} {φ F : ℝ → ℝ}
    (hb : ∀ x, |φ x| ≤ C * Real.exp (η * |x|))
    (hi : Integrable (fun x => Real.exp (η * |x|) * F x)) :
    |∫ x, φ x * F x| ≤ C * ∫ x, Real.exp (η * |x|) * |F x| := by
  have habs : Integrable (fun x => Real.exp (η * |x|) * |F x|) := by
    simpa only [Real.norm_eq_abs, abs_mul, Real.abs_exp] using hi.norm
  rw [← integral_const_mul, ← Real.norm_eq_abs]
  apply norm_integral_le_of_norm_le (habs.const_mul C)
  refine ae_of_all _ fun x => ?_
  rw [Real.norm_eq_abs, abs_mul]
  calc
    |φ x| * |F x| ≤ C * Real.exp (η * |x|) * |F x| :=
      mul_le_mul_of_nonneg_right (hb x) (abs_nonneg _)
    _ = C * (Real.exp (η * |x|) * |F x|) := by ring

theorem exists_sq_sub_one_le_exp {η : ℝ} (hη : 0 < η) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, |(x - 1) ^ 2| ≤ C * Real.exp (η * |x|) := by
  obtain ⟨C, hC, hb⟩ := cepsDensityWeight_le_exp (η := 0) hη
  exact ⟨C, hC, fun x => (variance_test_le_cepsDensityWeight le_rfl x).trans (hb x)⟩

/-- The polynomial factor of the distance weight is absorbed by a larger exponential weight. -/
theorem integrable_cepsDensityWeight_mul {η θ : ℝ} (hηθ : η < θ) {F : ℝ → ℝ}
    (hF : Continuous F) (hi : Integrable (fun x => Real.exp (θ * |x|) * F x)) :
    Integrable (fun x => cepsDensityWeight η x * F x) := by
  obtain ⟨C, -, hb⟩ := cepsDensityWeight_le_exp hηθ
  refine integrable_mul_of_abs_le_expWeight (C := C) (by unfold cepsDensityWeight; fun_prop)
    hF.aestronglyMeasurable (fun x => ?_) hi
  rw [abs_of_nonneg (cepsDensityWeight_nonneg η x)]
  exact hb x

theorem continuous_cepsRemainder {m : ℕ} {η : ℝ} {P : ℕ} {f : ℝ → ℝ} {g : ℕ → ℝ → ℝ}
    (hf : CepsSobolevClass m η f) (hg : ∀ n ∈ Finset.Icc 1 P, CepsSobolevClass m η (g n))
    (eps : ℝ) :
    Continuous (fun x => f x - cepsLambdaDensity x - ∑ n ∈ Finset.Icc 1 P, (eps⁻¹) ^ n * g n x) :=
  (hf.continuous.sub contDiff_cepsLambdaDensity.continuous).sub
    (continuous_finsetSum _ fun n hn => continuous_const.mul (hg n hn).continuous)

theorem integrable_expWeighted_cepsRemainder {m : ℕ} {η : ℝ} {P : ℕ} {f : ℝ → ℝ}
    {g : ℕ → ℝ → ℝ} (hf : CepsSobolevClass m η f) (hΛ : CepsSobolevClass m η cepsLambdaDensity)
    (hg : ∀ n ∈ Finset.Icc 1 P, CepsSobolevClass m η (g n)) (eps : ℝ) :
    Integrable (fun x => Real.exp (η * |x|) *
      (f x - cepsLambdaDensity x - ∑ n ∈ Finset.Icc 1 P, (eps⁻¹) ^ n * g n x)) := by
  have hs : Integrable (fun x => ∑ n ∈ Finset.Icc 1 P,
      (eps⁻¹) ^ n * (Real.exp (η * |x|) * g n x)) :=
    integrable_finsetSum _ fun n hn => ((hg n hn).integrable_zero).const_mul _
  have he : (fun x => Real.exp (η * |x|) *
      (f x - cepsLambdaDensity x - ∑ n ∈ Finset.Icc 1 P, (eps⁻¹) ^ n * g n x)) =
      fun x => (Real.exp (η * |x|) * f x - Real.exp (η * |x|) * cepsLambdaDensity x) -
        ∑ n ∈ Finset.Icc 1 P, (eps⁻¹) ^ n * (Real.exp (η * |x|) * g n x) := by
    funext x
    rw [mul_sub, mul_sub, Finset.mul_sum]
    congr 1
    exact Finset.sum_congr rfl fun n _ => by ring
  rw [he]
  exact (hf.integrable_zero.sub hΛ.integrable_zero).sub hs

/-- Coefficients of the variance expansion: the reference variance, then the second
centred moments of the density coefficients. -/
def cepsVarianceCoeff (g : ℕ → ℝ → ℝ) : ℕ → ℝ
  | 0 => ∫ x, (x - 1) ^ 2 * cepsLambdaDensity x
  | n + 1 => ∫ x, (x - 1) ^ 2 * g (n + 1) x

theorem cepsVarianceCoeff_zero (g : ℕ → ℝ → ℝ) : cepsVarianceCoeff g 0 = lawVar cepsLambda := by
  rw [lawVar, lawMean_cepsLambda, integral_eq_integral_density_mul
    contDiff_cepsLambdaDensity.continuous.measurable cepsLambda_eq_withDensity
    cepsLambdaDensity_nonneg]
  exact integral_congr_ae (ae_of_all _ fun x => mul_comm _ _)

/-- A mean-one family expansion gives the variance expansion at the same order. -/
theorem CepsFamilyExpansion.lawVar_hasInverseExpansionAtOrder {ν : ℝ → ProbabilityMeasure ℝ}
    {m : ℕ} {η : ℝ} {P : ℕ} {g : ℕ → ℝ → ℝ} (h : CepsFamilyExpansion ν m η P g) (hη : 0 < η)
    (hmean : ∀ᶠ eps in atTop, lawMean (ν eps) = 1) :
    HasInverseExpansionAtOrder (fun eps => lawVar (ν eps)) (cepsVarianceCoeff g) P := by
  obtain ⟨f, hfev, hrem⟩ := h.density
  obtain ⟨C, hC, hb⟩ := exists_sq_sub_one_le_exp hη
  obtain ⟨K, e1, hK⟩ := hrem
  obtain ⟨e0, he0⟩ := eventually_atTop.mp (hfev.and hmean)
  refine ⟨C * K, max e0 e1, fun eps heps => ?_⟩
  obtain ⟨⟨hnn, hcl, hν⟩, hm⟩ := he0 eps ((le_max_left _ _).trans heps)
  have hKe := hK eps ((le_max_right _ _).trans heps)
  set R : ℝ → ℝ := fun x =>
    f eps x - cepsLambdaDensity x - ∑ n ∈ Finset.Icc 1 P, (eps⁻¹) ^ n * g n x with hR
  have hRi : Integrable (fun x => Real.exp (η * |x|) * R x) :=
    integrable_expWeighted_cepsRemainder hcl h.reference h.coeff eps
  have htest {F : ℝ → ℝ} (hF : CepsSobolevClass m η F) :
      Integrable (fun x => (x - 1) ^ 2 * F x) :=
    integrable_mul_of_abs_le_expWeight (by fun_prop) hF.continuous.aestronglyMeasurable hb
      hF.integrable_zero
  have hvar : lawVar (ν eps) = ∫ x, (x - 1) ^ 2 * f eps x := by
    rw [lawVar, hm, integral_eq_integral_density_mul hcl.continuous.measurable hν hnn]
    exact integral_congr_ae (ae_of_all _ fun x => mul_comm _ _)
  have hpoly : inversePolynomial (cepsVarianceCoeff g) P eps =
      (∫ x, (x - 1) ^ 2 * cepsLambdaDensity x) +
        ∑ n ∈ Finset.Icc 1 P, (eps⁻¹) ^ n * ∫ x, (x - 1) ^ 2 * g n x := by
    rw [inversePolynomial, Finset.sum_range_succ', sum_Icc_one_eq_sum_range, add_comm]
    simp only [cepsVarianceCoeff, pow_zero, mul_one]
    congr 1
    exact Finset.sum_congr rfl fun i _ => by ring
  have hsplit : ∫ x, (x - 1) ^ 2 * R x =
      (∫ x, (x - 1) ^ 2 * f eps x) - (∫ x, (x - 1) ^ 2 * cepsLambdaDensity x) -
        ∑ n ∈ Finset.Icc 1 P, (eps⁻¹) ^ n * ∫ x, (x - 1) ^ 2 * g n x := by
    have hs : ∀ n ∈ Finset.Icc 1 P,
        Integrable (fun x => (eps⁻¹) ^ n * ((x - 1) ^ 2 * g n x)) :=
      fun n hn => (htest (h.coeff n hn)).const_mul _
    have he : (fun x => (x - 1) ^ 2 * R x) = fun x =>
        ((x - 1) ^ 2 * f eps x - (x - 1) ^ 2 * cepsLambdaDensity x) -
          ∑ n ∈ Finset.Icc 1 P, (eps⁻¹) ^ n * ((x - 1) ^ 2 * g n x) := by
      funext x
      rw [hR, mul_sub, mul_sub, Finset.mul_sum]
      congr 1
      exact Finset.sum_congr rfl fun n _ => by ring
    have h12 : Integrable (fun x => (x - 1) ^ 2 * f eps x - (x - 1) ^ 2 * cepsLambdaDensity x) :=
      (htest hcl).sub (htest h.reference)
    rw [he, integral_sub h12 (integrable_finsetSum _ hs),
      integral_sub (htest hcl) (htest h.reference), integral_finsetSum _ hs]
    simp only [integral_const_mul]
  have hbound := abs_integral_mul_le_expWeighted (φ := fun x => (x - 1) ^ 2) (F := R) hb hRi
  have hsob := integral_expWeighted_abs_le_cepsSobolev m η R
  rw [abs_of_nonneg (cepsSobolev_nonneg _ _ _)] at hKe
  have heq : lawVar (ν eps) - inversePolynomial (cepsVarianceCoeff g) P eps =
      ∫ x, (x - 1) ^ 2 * R x := by
    rw [hvar, hpoly, hsplit]
    ring
  rw [heq]
  calc
    |∫ x, (x - 1) ^ 2 * R x| ≤ C * ∫ x, Real.exp (η * |x|) * |R x| := hbound
    _ ≤ C * cepsSobolev m η R := mul_le_mul_of_nonneg_left hsob hC
    _ ≤ C * (K * (eps⁻¹) ^ (P + 1)) := mul_le_mul_of_nonneg_left hKe hC
    _ = C * K * (eps⁻¹) ^ (P + 1) := by ring

/-- The remainder of a family expansion has exponentially weighted `L¹` size of the next order. -/
theorem CepsFamilyExpansion.expWeighted_remainder {ν : ℝ → ProbabilityMeasure ℝ}
    {m : ℕ} {η : ℝ} {P : ℕ} {g : ℕ → ℝ → ℝ} (h : CepsFamilyExpansion ν m η P g) :
    ∃ f : ℝ → ℝ → ℝ,
      (∀ᶠ eps in atTop, (∀ x, 0 ≤ f eps x) ∧ CepsSobolevClass m η (f eps) ∧
        (ν eps : Measure ℝ) = volume.withDensity (fun x => ENNReal.ofReal (f eps x))) ∧
      IsInverseOrder (fun eps => ∫ x, Real.exp (η * |x|) * |f eps x - (cepsLambdaDensity x +
        ∑ n ∈ Finset.Icc 1 P, (eps⁻¹) ^ n * g n x)|) (P + 1) := by
  obtain ⟨f, hfev, K, e1, hK⟩ := h.density
  refine ⟨f, hfev, K, e1, fun eps heps => ?_⟩
  have hs := integral_expWeighted_abs_le_cepsSobolev m η (fun x =>
    f eps x - cepsLambdaDensity x - ∑ n ∈ Finset.Icc 1 P, (eps⁻¹) ^ n * g n x)
  have hKe := hK eps heps
  rw [abs_of_nonneg (cepsSobolev_nonneg _ _ _)] at hKe
  rw [abs_of_nonneg (integral_nonneg fun _ => mul_nonneg (Real.exp_nonneg _) (abs_nonneg _))]
  simp only [sub_add_eq_sub_sub]
  exact hs.trans hKe

/-- Two mean-one family expansions sharing their polynomial through order `j` pay the
coupled residual at order `j + 1`, at every weight below both expansion weights. -/
theorem ceps_residual_inverseOrder_of_familyExpansion {ν ρ : ℝ → ProbabilityMeasure ℝ}
    {m m' j : ℕ} {ηa ηb η : ℝ} {g g' : ℕ → ℝ → ℝ}
    (hν : CepsFamilyExpansion ν m ηa j g) (hρ : CepsFamilyExpansion ρ m' ηb j g')
    (hgg : ∀ n ∈ Finset.Icc 1 j, g' n = g n)
    (hmeanν : ∀ᶠ eps in atTop, lawMean (ν eps) = 1)
    (hmeanρ : ∀ᶠ eps in atTop, lawMean (ρ eps) = 1)
    (hη : 0 < η) (hηa : η < ηa) (hηb : η < ηb) :
    IsInverseOrder (fun eps => dEta η (ν eps) (ρ eps) + |lawVar (ρ eps) - lawVar (ν eps)|)
      (j + 1) := by
  obtain ⟨fa, hfa, hoa⟩ := hν.expWeighted_remainder
  obtain ⟨fb, hfb, hob⟩ := hρ.expWeighted_remainder
  let S : ℝ → ℝ → ℝ := fun eps x =>
    cepsLambdaDensity x + ∑ n ∈ Finset.Icc 1 j, (eps⁻¹) ^ n * g n x
  have hSb (eps : ℝ) (x : ℝ) : cepsLambdaDensity x +
      ∑ n ∈ Finset.Icc 1 j, (eps⁻¹) ^ n * g' n x = S eps x := by
    simp only [S]
    congr 1
    exact Finset.sum_congr rfl fun n hn => by rw [hgg n hn]
  simp only [hSb] at hob
  obtain ⟨e0, he0⟩ := eventually_atTop.mp (((hfa.and hfb).and hmeanν).and hmeanρ)
  have hrem (eps : ℝ) {θ : ℝ} {f : ℝ → ℝ} {m₀ P₀ : ℕ} {g₀ : ℕ → ℝ → ℝ}
      (hf : CepsSobolevClass m₀ θ f) (hΛ : CepsSobolevClass m₀ θ cepsLambdaDensity)
      (hg : ∀ n ∈ Finset.Icc 1 P₀, CepsSobolevClass m₀ θ (g₀ n)) :
      Continuous (fun x => f x - (cepsLambdaDensity x +
          ∑ n ∈ Finset.Icc 1 P₀, (eps⁻¹) ^ n * g₀ n x)) ∧
        Integrable (fun x => Real.exp (θ * |x|) * (f x - (cepsLambdaDensity x +
          ∑ n ∈ Finset.Icc 1 P₀, (eps⁻¹) ^ n * g₀ n x))) := by
    simp only [← sub_sub]
    exact ⟨continuous_cepsRemainder hf hg eps, integrable_expWeighted_cepsRemainder hf hΛ hg eps⟩
  have hga : ∀ eps, e0 ≤ eps → Continuous (fun x => fa eps x - S eps x) ∧
      Integrable (fun x => Real.exp (ηa * |x|) * (fa eps x - S eps x)) := fun eps he =>
    hrem eps (he0 eps he).1.1.1.2.1 hν.reference hν.coeff
  have hgb : ∀ eps, e0 ≤ eps → Continuous (fun x => fb eps x - S eps x) ∧
      Integrable (fun x => Real.exp (ηb * |x|) * (fb eps x - S eps x)) := by
    intro eps he
    have h := hrem eps (he0 eps he).1.1.2.2.1 hρ.reference hρ.coeff
    simpa only [hSb] using h
  have hwa := cepsWeightedL1_inverseOrder_of_expWeightedL1 hηa (fun eps x => fa eps x - S eps x)
    (fun eps he => (hga eps he).1.measurable) (fun eps he => (hga eps he).2) hoa
  have hwb := cepsWeightedL1_inverseOrder_of_expWeightedL1 hηb (fun eps x => fb eps x - S eps x)
    (fun eps he => (hgb eps he).1.measurable) (fun eps he => (hgb eps he).2) hob
  have hw := cepsWeightedL1_inverseOrder_of_common_expansion (η := η) (e0 := e0) fa fb S
    (fun eps he => integrable_cepsDensityWeight_mul hηa (hga eps he).1 (hga eps he).2)
    (fun eps he => integrable_cepsDensityWeight_mul hηb (hgb eps he).1 (hgb eps he).2) hwa hwb
  obtain ⟨K, e2, hK⟩ := hw
  refine ⟨2 * K, max e0 e2, fun eps heps => ?_⟩
  obtain ⟨⟨⟨⟨hna, hca, hνe⟩, hnb, hcb, hρe⟩, hmν⟩, hmρ⟩ := he0 eps ((le_max_left _ _).trans heps)
  have hKe := hK eps ((le_max_right _ _).trans heps)
  rw [abs_of_nonneg (cepsWeightedL1_nonneg _ _)] at hKe
  obtain ⟨pa, hpa, hνp⟩ := exists_hellingerDensity_of_withDensity hca.continuous.measurable hna hνe
  obtain ⟨pb, hpb, hρp⟩ := exists_hellingerDensity_of_withDensity hcb.continuous.measurable hnb hρe
  have hia : Integrable (fun x => cepsDensityWeight η x * pa.density x) := by
    rw [hpa]
    exact integrable_cepsDensityWeight_mul hηa hca.continuous hca.integrable_zero
  have hib : Integrable (fun x => cepsDensityWeight η x * pb.density x) := by
    rw [hpb]
    exact integrable_cepsDensityWeight_mul hηb hcb.continuous hcb.integrable_zero
  have hD := dEta_le_cepsWeightedL1 pa pb (ν eps) (ρ eps) hνp hρp hη.le hia hib
  have hV := abs_lawVar_sub_le_cepsWeightedL1 pa pb (ν eps) (ρ eps) hνp hρp hmν hmρ hη.le hia hib
  rw [hpa, hpb] at hD hV
  rw [abs_of_nonneg (add_nonneg (dEta_nonneg _ _ _) (abs_nonneg _))]
  linarith

end

end PGM
