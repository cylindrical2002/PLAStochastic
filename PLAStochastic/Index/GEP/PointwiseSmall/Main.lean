import PLAStochastic.Index.GEP.PointwiseSmall.RowPhi
import PLAStochastic.Index.GEP.PointwiseSmall.CoarseInfluenceBounds
import PLAStochastic.Index.GEP.PointwiseSmall.AEQuadratic

/-!
# WP4 leaf `PointwiseSmall` from (U) and `SurvivalBound`

`pointwiseSmall_of_univ`: with the rate exponent `βU > 1/2` of (U) we take
`β = (βU + 1/2)/2`, `P₁ = 4`, `ηP = min ηφ ηJ` (the output weights of row φ and of the coarse
kernel bound), `αP = 1`.  For an input weight `α`:

* rows A and V use the two-bump directions with `θσ = α/4` (`pw_affine_of_dir`), the row bounds
  `pw_rowA` (identified with `∫ J_A d(σ - ν)` by `pw_integral_lawJA_sub`) and `pw_rowV`, and the
  coarse bounds `pw_lawJA_bound`, `pw_outJ_bound` (slope `O(ε⁴)`);
* row φ uses the three-bump directions of equal variance with `θσ = α/8`
  (`pw_quadratic_of_pair`) and the pair bound `pw_rowPhi`.

The errors `K ε^{-βU} (1 + log ε)² / c(x)` are converted by `pw_two_bump_error`,
`pw_three_bump_error` (`1/c(x) ≤ K e^{αx}`) and `pw_rate_convert`
(`ε^{-βU} (1 + log ε)² ≤ K ε^{-β}`).
-/

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set

variable {D θ vlo vhi : ℝ}

/-! ## The exponential form of the errors -/

theorem pw_two_bump_error {α δ x : ℝ} (hα : 0 < α) (hx : 0 < x) (hδ : 0 ≤ δ) :
    2 * δ / dirC (α / 4) x ≤ 4 * Real.exp (α / 4) * (1 + 4 / α) * δ * Real.exp (α * x) := by
  have h := pw_one_div_dirC_le (θσ := α / 4) (by positivity) hx
  have h2 : Real.exp (2 * (α / 4) * x) ≤ Real.exp (α * x) := Real.exp_le_exp.2 (by nlinarith)
  rw [div_eq_mul_one_div]
  calc 2 * δ * (1 / dirC (α / 4) x)
      ≤ 2 * δ * (2 * Real.exp (α / 4) * (1 + 1 / (α / 4)) * Real.exp (2 * (α / 4) * x)) := by
        gcongr
    _ ≤ 2 * δ * (2 * Real.exp (α / 4) * (1 + 1 / (α / 4)) * Real.exp (α * x)) := by gcongr
    _ = 4 * Real.exp (α / 4) * (1 + 4 / α) * δ * Real.exp (α * x) := by rw [one_div_div]; ring

theorem pw_three_bump_error {α δ x : ℝ} (hα : 0 < α) (hx : 0 < x) (hδ : 0 ≤ δ) :
    δ / pwC3 (α / 8) x ≤ 30 * Real.exp (α / 8) * (1 + 8 / α) ^ 2 * δ * Real.exp (α * x) := by
  rw [div_eq_mul_one_div, one_div_pwC3]
  have h := pw_sq_mul_exp_le (θσ := α / 8) (by positivity) hx.le
  have h2 : Real.exp (4 * (α / 8) * x) ≤ Real.exp (α * x) := Real.exp_le_exp.2 (by nlinarith)
  rw [show α / 8 * (x + 1) = α / 8 * x + α / 8 by ring, Real.exp_add]
  calc δ * (30 * (1 + x) ^ 2 * (Real.exp (α / 8 * x) * Real.exp (α / 8)))
      = 30 * Real.exp (α / 8) * δ * ((1 + x) ^ 2 * Real.exp (α / 8 * x)) := by ring
    _ ≤ 30 * Real.exp (α / 8) * δ * ((1 + 1 / (α / 8)) ^ 2 * Real.exp (4 * (α / 8) * x)) := by
        gcongr
    _ ≤ 30 * Real.exp (α / 8) * δ * ((1 + 1 / (α / 8)) ^ 2 * Real.exp (α * x)) := by gcongr
    _ = 30 * Real.exp (α / 8) * (1 + 8 / α) ^ 2 * δ * Real.exp (α * x) := by
        rw [one_div_div]; ring

/-! ## The three rows -/

/-- **Row A, a.e. form.** -/
theorem pw_rowA_ae (hS : SurvivalBound) {βU : ℝ} (hβU : 1 / 2 < βU) (hUM : PwUnivMix βU)
    (hD : 0 < D) (hθ : 0 < θ) (hvlo : 0 < vlo) (hv : vlo ≤ vhi) {α : ℝ} (hα : 0 < α) :
    ∃ K e0 : ℝ, 0 ≤ K ∧ 1 ≤ e0 ∧ ∀ eps, e0 ≤ eps → ∀ ν : ProbabilityMeasure ℝ,
      RegLaw D θ vlo vhi ν → ∃ l₀ l₁ : ℝ, |l₁| ≤ K * eps ^ 4 ∧
        ∀ᵐ x ∂(volume.restrict (Ioi (0 : ℝ))),
          |lawJA eps ν x - (l₀ + l₁ * x)| ≤
            K * eps ^ (-((βU + 1 / 2) / 2)) * Real.exp (α * x) := by
  have hβU0 : 0 ≤ βU := by linarith
  have hθσ : 0 < α / 4 := by positivity
  obtain ⟨Kr, hKr, hrate⟩ := pw_rate_convert hβU
  obtain ⟨KA, eA, hKA, heA, hrowA⟩ := pw_rowA hS hβU0 hUM hD hθ hvlo hv
    (1 + Real.exp (α / 4 * (5 / 2))) (α / 4) hθσ
  obtain ⟨KA', eA', hKA', -, hAb⟩ := pw_lawJA_bound hD hθ hvlo hv
  obtain ⟨KJ, eJ, -, -, hJC⟩ := pw_lawJC_integrable hD hθ hvlo hv
  set cA : ℝ := 4 * Real.exp (α / 4) * (1 + 4 / α) with hcA
  have hcA0 : 0 ≤ cA := by positivity
  set K : ℝ := 2 * (KA' * Real.exp (2 * (5 / 2))) + cA * KA * Kr with hK
  have hK1 : 2 * (KA' * Real.exp (2 * (5 / 2))) ≤ K := by
    have : 0 ≤ cA * KA * Kr := by positivity
    rw [hK]; linarith
  have hK2 : cA * KA * Kr ≤ K := by
    have : 0 ≤ 2 * (KA' * Real.exp (2 * (5 / 2))) := by positivity
    rw [hK]; linarith
  refine ⟨K, max (max eA eA') eJ, by positivity,
    heA.trans ((le_max_left _ _).trans (le_max_left _ _)), ?_⟩
  intro eps heps ν hν
  have heA1 : eA ≤ eps := ((le_max_left _ _).trans (le_max_left _ _)).trans heps
  have heA2 : eA' ≤ eps := ((le_max_right _ _).trans (le_max_left _ _)).trans heps
  have heJ1 : eJ ≤ eps := (le_max_right _ _).trans heps
  have heps1 : 1 ≤ eps := heA.trans heA1
  have heps0 : 0 < eps := by linarith
  obtain ⟨hJAm, hJAb⟩ := hAb eps heA2 ν hν
  obtain ⟨-, -, hJi⟩ := hJC eps heJ1 ν hν
  have hδ0 : 0 ≤ KA * eps ^ (-βU) * (1 + Real.log eps) ^ 2 := by positivity
  have hdir : ∀ σ : ProbabilityMeasure ℝ, SigmaLaw (1 + Real.exp (α / 4 * (5 / 2))) (α / 4) σ →
      |∫ y, lawJA eps ν y ∂(σ : Measure ℝ) - ∫ y, lawJA eps ν y ∂(ν : Measure ℝ)| ≤
        KA * eps ^ (-βU) * (1 + Real.log eps) ^ 2 := by
    intro σ hσ
    obtain ⟨hσ3, -⟩ := hσ.cube hθσ
    obtain ⟨-, iσ2, -⟩ := moments_of_cube hσ.pos hσ3
    rw [pw_integral_lawJA_sub (hJi σ) (hJi ν) iσ2 (hν.integrable_sq_sub_one hθ) hσ.mean hν.mean]
    exact hrowA eps heA1 ν σ hν hσ
  obtain ⟨a', b', hb', hae⟩ := pw_affine_of_dir hθσ hJAm (by norm_num : (0 : ℝ) ≤ 2) hJAb hdir
  refine ⟨a', b', ?_, ?_⟩
  · refine hb'.trans ?_
    rw [abs_of_nonneg (by positivity)]
    calc 2 * (KA' * eps ^ 4 * Real.exp (2 * (5 / 2)))
        = 2 * (KA' * Real.exp (2 * (5 / 2))) * eps ^ 4 := by ring
      _ ≤ K * eps ^ 4 := by gcongr
  · filter_upwards [hae, ae_restrict_mem measurableSet_Ioi] with x hx hx0
    have hx0' : 0 < x := hx0
    refine hx.trans ((pw_two_bump_error hα hx0' hδ0).trans ?_)
    have hr := hrate eps heps1
    calc cA * (KA * eps ^ (-βU) * (1 + Real.log eps) ^ 2) * Real.exp (α * x)
        = cA * KA * (eps ^ (-βU) * (1 + Real.log eps) ^ 2) * Real.exp (α * x) := by ring
      _ ≤ cA * KA * (Kr * eps ^ (-((βU + 1 / 2) / 2))) * Real.exp (α * x) := by gcongr
      _ = cA * KA * Kr * eps ^ (-((βU + 1 / 2) / 2)) * Real.exp (α * x) := by ring
      _ ≤ K * eps ^ (-((βU + 1 / 2) / 2)) * Real.exp (α * x) := by gcongr

/-- **Row V, a.e. form.** -/
theorem pw_rowV_ae (hS : SurvivalBound) {βU : ℝ} (hβU : 1 / 2 < βU) (hUM : PwUnivMix βU)
    (hD : 0 < D) (hθ : 0 < θ) (hvlo : 0 < vlo) (hv : vlo ≤ vhi) {α : ℝ} (hα : 0 < α) :
    ∃ K e0 : ℝ, 0 ≤ K ∧ 1 ≤ e0 ∧ ∀ eps, e0 ≤ eps → ∀ ν : ProbabilityMeasure ℝ,
      RegLaw D θ vlo vhi ν → ∃ l₀ l₁ : ℝ, |l₁| ≤ K * eps ^ 4 ∧
        ∀ᵐ x ∂(volume.restrict (Ioi (0 : ℝ))),
          |lawJV eps ν x - (l₀ + l₁ * x)| ≤
            K * eps ^ (-((βU + 1 / 2) / 2)) * Real.exp (α * x) := by
  have hβU0 : 0 ≤ βU := by linarith
  have hθσ : 0 < α / 4 := by positivity
  obtain ⟨Kr, hKr, hrate⟩ := pw_rate_convert hβU
  obtain ⟨KV, eV, hKV, heV, hrowV⟩ := pw_rowV hS hβU0 hUM hD hθ hvlo hv
    (1 + Real.exp (α / 4 * (5 / 2))) (α / 4) hθσ
  obtain ⟨ηJ, κ₀, KJ', eJ', hηJ, hκ₀, hKJ', -, hJb⟩ := pw_outJ_bound hD hθ hvlo hv
  set MV : ℝ := 2 / ηJ + 2 with hMV
  have hMV0 : 0 ≤ MV := by positivity
  set cA : ℝ := 4 * Real.exp (α / 4) * (1 + 4 / α) with hcA
  have hcA0 : 0 ≤ cA := by positivity
  set K : ℝ := 2 * (MV * KJ' * Real.exp (κ₀ * (5 / 2))) + cA * KV * Kr with hK
  have hK1 : 2 * (MV * KJ' * Real.exp (κ₀ * (5 / 2))) ≤ K := by
    have : 0 ≤ cA * KV * Kr := by positivity
    rw [hK]; linarith
  have hK2 : cA * KV * Kr ≤ K := by
    have : 0 ≤ 2 * (MV * KJ' * Real.exp (κ₀ * (5 / 2))) := by positivity
    rw [hK]; linarith
  refine ⟨K, max eV eJ', by positivity, heV.trans (le_max_left _ _), ?_⟩
  intro eps heps ν hν
  have heV1 : eV ≤ eps := (le_max_left _ _).trans heps
  have heJ1 : eJ' ≤ eps := (le_max_right _ _).trans heps
  have heps1 : 1 ≤ eps := heV.trans heV1
  have heps0 : 0 < eps := by linarith
  obtain ⟨hJm, hJbd⟩ := hJb eps heJ1 ν hν MV psiVar (outTest_psiVar hηJ)
  have hδ0 : 0 ≤ KV * eps ^ (-βU) * (1 + Real.log eps) ^ 2 := by positivity
  have hdir : ∀ σ : ProbabilityMeasure ℝ, SigmaLaw (1 + Real.exp (α / 4 * (5 / 2))) (α / 4) σ →
      |∫ y, outJ eps ν psiVar y ∂(σ : Measure ℝ) - ∫ y, outJ eps ν psiVar y ∂(ν : Measure ℝ)| ≤
        KV * eps ^ (-βU) * (1 + Real.log eps) ^ 2 := fun σ hσ => hrowV eps heV1 ν σ hν hσ
  obtain ⟨a', b', hb', hae⟩ := pw_affine_of_dir hθσ hJm hκ₀ hJbd hdir
  refine ⟨a', b', ?_, ?_⟩
  · refine hb'.trans ?_
    rw [abs_of_nonneg (by positivity)]
    calc 2 * (MV * KJ' * eps ^ 4 * Real.exp (κ₀ * (5 / 2)))
        = 2 * (MV * KJ' * Real.exp (κ₀ * (5 / 2))) * eps ^ 4 := by ring
      _ ≤ K * eps ^ 4 := by gcongr
  · filter_upwards [hae, ae_restrict_mem measurableSet_Ioi] with x hx hx0
    have hx0' : 0 < x := hx0
    refine hx.trans ((pw_two_bump_error hα hx0' hδ0).trans ?_)
    have hr := hrate eps heps1
    calc cA * (KV * eps ^ (-βU) * (1 + Real.log eps) ^ 2) * Real.exp (α * x)
        = cA * KV * (eps ^ (-βU) * (1 + Real.log eps) ^ 2) * Real.exp (α * x) := by ring
      _ ≤ cA * KV * (Kr * eps ^ (-((βU + 1 / 2) / 2))) * Real.exp (α * x) := by gcongr
      _ = cA * KV * Kr * eps ^ (-((βU + 1 / 2) / 2)) * Real.exp (α * x) := by ring
      _ ≤ K * eps ^ (-((βU + 1 / 2) / 2)) * Real.exp (α * x) := by gcongr

/-- **Row φ, a.e. form**: the output weight `ηP` is fixed before `α`. -/
theorem pw_rowPhi_ae (hS : SurvivalBound) {βU : ℝ} (hβU : 1 / 2 < βU) (hUM : PwUnivMix βU)
    (hD : 0 < D) (hθ : 0 < θ) (hvlo : 0 < vlo) (hv : vlo ≤ vhi) :
    ∃ ηP : ℝ, 0 < ηP ∧ ∀ α : ℝ, 0 < α →
      ∃ K e0 : ℝ, 0 ≤ K ∧ 1 ≤ e0 ∧ ∀ eps, e0 ≤ eps → ∀ ν : ProbabilityMeasure ℝ,
        RegLaw D θ vlo vhi ν → ∀ M ψ, OutTest ηP M ψ → ∃ l₀ l₁ l₂ : ℝ,
          |l₁| + |l₂| ≤ M * (K * eps ^ 4) ∧
          ∀ᵐ x ∂(volume.restrict (Ioi (0 : ℝ))),
            |outJ eps ν ψ x - (l₀ + l₁ * x + l₂ * x ^ 2)| ≤
              M * (K * eps ^ (-((βU + 1 / 2) / 2))) * Real.exp (α * x) := by
  have hβU0 : 0 ≤ βU := by linarith
  obtain ⟨Kr, hKr, hrate⟩ := pw_rate_convert hβU
  obtain ⟨ηφ, hηφ, hrowPhi⟩ := pw_rowPhi hS hβU0 hUM hD hθ hvlo hv
  obtain ⟨ηJ, κ₀, KJ', eJ', hηJ, hκ₀, hKJ', heJ', hJb⟩ := pw_outJ_bound hD hθ hvlo hv
  refine ⟨min ηφ ηJ, lt_min hηφ hηJ, fun α hα => ?_⟩
  have hθσ : 0 < α / 8 := by positivity
  obtain ⟨Kφ, eφ, hKφ, heφ, hrowφ⟩ := hrowPhi (1 + Real.exp (α / 8 * (7 / 2))) (α / 8) hθσ
  set cφ : ℝ := 30 * Real.exp (α / 8) * (1 + 8 / α) ^ 2 with hcφ
  have hcφ0 : 0 ≤ cφ := by positivity
  set K : ℝ := 7 * (KJ' * Real.exp (κ₀ * (7 / 2))) + cφ * Kφ * Kr with hK
  have hK1 : 7 * (KJ' * Real.exp (κ₀ * (7 / 2))) ≤ K := by
    have : 0 ≤ cφ * Kφ * Kr := by positivity
    rw [hK]; linarith
  have hK2 : cφ * Kφ * Kr ≤ K := by
    have : 0 ≤ 7 * (KJ' * Real.exp (κ₀ * (7 / 2))) := by positivity
    rw [hK]; linarith
  refine ⟨K, max eφ eJ', by positivity, heφ.trans (le_max_left _ _), ?_⟩
  intro eps heps ν hν M ψ hψ
  have heφ1 : eφ ≤ eps := (le_max_left _ _).trans heps
  have heJ1 : eJ' ≤ eps := (le_max_right _ _).trans heps
  have heps1 : 1 ≤ eps := heφ.trans heφ1
  have heps0 : 0 < eps := by linarith
  have hM := hψ.nonneg'
  obtain ⟨hJm, hJbd⟩ := hJb eps heJ1 ν hν M ψ (hψ.mono_eta (min_le_right _ _))
  have hδ0 : 0 ≤ M * (Kφ * eps ^ (-βU) * (1 + Real.log eps) ^ 2) := by positivity
  have hdir : ∀ σp σm : ProbabilityMeasure ℝ,
      SigmaLaw (1 + Real.exp (α / 8 * (7 / 2))) (α / 8) σp →
      SigmaLaw (1 + Real.exp (α / 8 * (7 / 2))) (α / 8) σm → lawVar σp = lawVar σm →
      |∫ y, outJ eps ν ψ y ∂(σp : Measure ℝ) - ∫ y, outJ eps ν ψ y ∂(σm : Measure ℝ)| ≤
        M * (Kφ * eps ^ (-βU) * (1 + Real.log eps) ^ 2) := fun σp σm hσp hσm hvar =>
    hrowφ eps heφ1 ν σp σm hν hσp hσm hvar M ψ (hψ.mono_eta (min_le_left _ _))
  obtain ⟨l₀, l₁, l₂, hl, hae⟩ := pw_quadratic_of_pair hθσ hJm hκ₀ hJbd hdir
  refine ⟨l₀, l₁, l₂, ?_, ?_⟩
  · refine hl.trans ?_
    rw [abs_of_nonneg (by positivity)]
    calc 7 * (M * KJ' * eps ^ 4 * Real.exp (κ₀ * (7 / 2)))
        = M * (7 * (KJ' * Real.exp (κ₀ * (7 / 2))) * eps ^ 4) := by ring
      _ ≤ M * (K * eps ^ 4) := by gcongr
  · filter_upwards [hae, ae_restrict_mem measurableSet_Ioi] with x hx hx0
    have hx0' : 0 < x := hx0
    refine hx.trans ((pw_three_bump_error hα hx0' hδ0).trans ?_)
    have hr := hrate eps heps1
    calc cφ * (M * (Kφ * eps ^ (-βU) * (1 + Real.log eps) ^ 2)) * Real.exp (α * x)
        = M * (cφ * Kφ * (eps ^ (-βU) * (1 + Real.log eps) ^ 2)) * Real.exp (α * x) := by ring
      _ ≤ M * (cφ * Kφ * (Kr * eps ^ (-((βU + 1 / 2) / 2)))) * Real.exp (α * x) := by gcongr
      _ = M * (cφ * Kφ * Kr * eps ^ (-((βU + 1 / 2) / 2))) * Real.exp (α * x) := by ring
      _ ≤ M * (K * eps ^ (-((βU + 1 / 2) / 2))) * Real.exp (α * x) := by gcongr

/-! ## The leaf -/

/-- **Leaf 4A-P from (U) and the survival bound**: `β = (βU + 1/2)/2`, `P₁ = 4`, `αP = 1`. -/
theorem pointwiseSmall_of_univ (hU : GEPUniversality) (hS : SurvivalBound) : PointwiseSmall := by
  obtain ⟨βU, hβU, hUM⟩ := pwUnivMix_of_univ hU
  intro D θ vlo vhi hD hθ hvlo hv
  obtain ⟨ηP, hηP, hrowφ⟩ := pw_rowPhi_ae hS hβU hUM hD hθ hvlo hv
  refine ⟨(βU + 1 / 2) / 2, by linarith, 4, ηP, hηP, 1, one_pos, fun α hα _ => ?_⟩
  obtain ⟨KA, eA, hKA, heA, hA⟩ := pw_rowA_ae hS hβU hUM hD hθ hvlo hv hα
  obtain ⟨KV, eV, hKV, heV, hV⟩ := pw_rowV_ae hS hβU hUM hD hθ hvlo hv hα
  obtain ⟨Kφ, eφ, hKφ, heφ, hφ⟩ := hrowφ α hα
  set K : ℝ := KA + KV + Kφ with hK
  have hKA' : KA ≤ K := by rw [hK]; linarith
  have hKV' : KV ≤ K := by rw [hK]; linarith
  have hKφ' : Kφ ≤ K := by rw [hK]; linarith
  refine ⟨K, max (max eA eV) eφ, fun eps heps ν hν => ?_⟩
  have heA1 : eA ≤ eps := ((le_max_left _ _).trans (le_max_left _ _)).trans heps
  have heV1 : eV ≤ eps := ((le_max_right _ _).trans (le_max_left _ _)).trans heps
  have heφ1 : eφ ≤ eps := (le_max_right _ _).trans heps
  have heps0 : 0 < eps := by linarith
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨l₀, l₁, hl, hae⟩ := hA eps heA1 ν hν
    refine ⟨l₀, l₁, hl.trans (by gcongr), ?_⟩
    filter_upwards [hae] with x hx
    exact hx.trans (by gcongr)
  · obtain ⟨l₀, l₁, hl, hae⟩ := hV eps heV1 ν hν
    refine ⟨l₀, l₁, hl.trans (by gcongr), ?_⟩
    filter_upwards [hae] with x hx
    exact hx.trans (by gcongr)
  · intro M ψ hψ
    obtain ⟨l₀, l₁, l₂, hl, hae⟩ := hφ eps heφ1 ν hν M ψ hψ
    have hM := hψ.nonneg'
    refine ⟨l₀, l₁, l₂, hl.trans (by gcongr), ?_⟩
    filter_upwards [hae] with x hx
    exact hx.trans (by gcongr)

end

end PGM
