import PLAStochastic.Index.CEPS.Jets.Transform
import PLAStochastic.Index.CEPS.Assembly.Output

/-!
# X8: densities and coefficients of expanding families

For a regular family `ν` expanding as `CepsFamilyExpansion ν m η P g`:

* the continuous densities `f_ε` of `ν ε` vanish on `(-∞, 0)`
  (`CepsEventuallyRegular.eventually_eq_zero_of_neg`): the regular class gives a density
  vanishing on `(-∞, 0]`, and two densities of one law agree almost everywhere;
* `CepsFamilyExpansion.remainder_data` collects, for all `ε ≥ ε₀`, the density, its vanishing on
  `(-∞, 0)`, its Sobolev class, the Sobolev class of the remainder
  `R_ε = f_ε - f_Λ - ∑_{n ≤ P} ε^{-n} g_n` and the bound `‖R_ε‖_{m,η} ≤ K ε^{-(P+1)}`;
* the coefficients vanish on `(-∞, 0)` (`CepsFamilyExpansion.coeff_eq_zero_of_neg`). With
  `h = ε⁻¹`, on `(-∞, 0)` the remainder is `-∑_{n ≤ P} h^n g_n`, so
  `∫_{x<0} e^{η|x|} |∑_{n ≤ P} h^n g_n| ≤ K h^{P+1}`. If `g_1, …, g_{n-1}` vanish there, then
  `h^n ∫_{x<0} e^{η|x|}|g_n| ≤ h^{n+1} (K + ∑_j ∫_{x<0} e^{η|x|}|g_j|)`, so the integral is zero
  (let `h → 0`), and `g_n` vanishes on `(-∞, 0)` by continuity.
-/

noncomputable section

open MeasureTheory Filter Topology Set Finset

namespace PGM

/-- A continuous function vanishing almost everywhere on `(-∞, 0)` vanishes there. -/
theorem eq_zero_of_ae_of_neg {g : ℝ → ℝ} (hg : Continuous g) (h : ∀ᵐ x, x < 0 → g x = 0) :
    ∀ x, x < 0 → g x = 0 := by
  have h' : g =ᵐ[volume.restrict (Iio 0)] fun _ => 0 := by
    rw [EventuallyEq, ae_restrict_iff' measurableSet_Iio]
    exact h.mono fun x hx hx0 => hx hx0
  exact fun x hx =>
    Measure.eqOn_open_of_ae_eq h' isOpen_Iio hg.continuousOn continuousOn_const hx

/-- Continuous densities of an eventually regular family eventually vanish on `(-∞, 0)`. -/
theorem CepsEventuallyRegular.eventually_eq_zero_of_neg {ν : ℝ → ProbabilityMeasure ℝ}
    (hreg : CepsEventuallyRegular ν) {f : ℝ → ℝ → ℝ}
    (hf : ∀ᶠ eps in atTop, (∀ x, 0 ≤ f eps x) ∧ Continuous (f eps) ∧
      (ν eps : Measure ℝ) = volume.withDensity (fun x => ENNReal.ofReal (f eps x))) :
    ∀ᶠ eps in atTop, ∀ x, x < 0 → f eps x = 0 := by
  obtain ⟨D, θ, vlo, vhi, -, -, -, -, hR⟩ := hreg
  filter_upwards [hR, hf] with eps hr hfe
  obtain ⟨f', hf'm, -, hf'0, -, hν⟩ := hr.density
  have hae : (fun x => ENNReal.ofReal (f eps x)) =ᵐ[volume] fun x => ENNReal.ofReal (f' x) :=
    (withDensity_eq_iff_of_sigmaFinite hfe.2.1.measurable.ennreal_ofReal.aemeasurable
      hf'm.ennreal_ofReal.aemeasurable).mp (hfe.2.2.symm.trans hν)
  refine eq_zero_of_ae_of_neg hfe.2.1 (hae.mono fun x hx hx0 => ?_)
  have hx' : ENNReal.ofReal (f eps x) = ENNReal.ofReal (f' x) := hx
  rw [hf'0 x hx0.le, ENNReal.ofReal_zero, ENNReal.ofReal_eq_zero] at hx'
  exact le_antisymm hx' (hfe.1 x)

/-- **Remainder data.** Beyond some `ε₀ > 0` the family has a nonnegative Sobolev density
vanishing on `(-∞, 0)`, and the remainder of the expansion is in the Sobolev class with
`‖R_ε‖_{m,η} ≤ K ε^{-(P+1)}`. -/
theorem CepsFamilyExpansion.remainder_data {ν : ℝ → ProbabilityMeasure ℝ} {m : ℕ} {η : ℝ}
    {P : ℕ} {g : ℕ → ℝ → ℝ} (hreg : CepsEventuallyRegular ν)
    (h : CepsFamilyExpansion ν m η P g) :
    ∃ f : ℝ → ℝ → ℝ, ∃ K eps₀ : ℝ, 0 < eps₀ ∧ 0 ≤ K ∧ ∀ eps, eps₀ ≤ eps →
      (∀ x, 0 ≤ f eps x) ∧ (∀ x, x < 0 → f eps x = 0) ∧ CepsSobolevClass m η (f eps) ∧
      (ν eps : Measure ℝ) = volume.withDensity (fun x => ENNReal.ofReal (f eps x)) ∧
      CepsSobolevClass m η (fun x => f eps x - cepsLambdaDensity x -
        ∑ n ∈ Finset.Icc 1 P, (eps⁻¹) ^ n * g n x) ∧
      cepsSobolev m η (fun x => f eps x - cepsLambdaDensity x -
        ∑ n ∈ Finset.Icc 1 P, (eps⁻¹) ^ n * g n x) ≤ K * (eps⁻¹) ^ (P + 1) := by
  obtain ⟨f, hfev, hord⟩ := h.density
  obtain ⟨K, e0, hK, he0, hKb⟩ := hord.nonneg_witness
  have hneg := hreg.eventually_eq_zero_of_neg
    (hfev.mono fun eps he => ⟨he.1, he.2.1.continuous, he.2.2⟩)
  obtain ⟨e1, he1⟩ := eventually_atTop.mp (hfev.and hneg)
  refine ⟨f, K, max e0 e1, lt_of_lt_of_le one_pos (he0.trans (le_max_left _ _)), hK,
    fun eps heps => ?_⟩
  obtain ⟨⟨hf0, hfc, hν⟩, hfn⟩ := he1 eps ((le_max_right _ _).trans heps)
  refine ⟨hf0, hfn, hfc, hν,
    (hfc.sub h.reference).sub (CepsSobolevClass.sum _ fun n hn => (h.coeff n hn).const_mul _),
    ?_⟩
  exact (le_abs_self _).trans (hKb eps ((le_max_left _ _).trans heps))

/-- **The coefficients vanish on the negative half-line.** -/
theorem CepsFamilyExpansion.coeff_eq_zero_of_neg {ν : ℝ → ProbabilityMeasure ℝ} {m : ℕ}
    {η : ℝ} {P : ℕ} {g : ℕ → ℝ → ℝ} (hreg : CepsEventuallyRegular ν)
    (h : CepsFamilyExpansion ν m η P g) : ∀ n ∈ Finset.Icc 1 P, ∀ x, x < 0 → g n x = 0 := by
  obtain ⟨f, K, e0, -, hK, hf⟩ := h.remainder_data hreg
  have hgi : ∀ j ∈ Finset.Icc 1 P, Integrable fun x => Real.exp (η * |x|) * |g j x| :=
    fun j hj => by
      simpa only [iteratedDeriv_zero] using (h.coeff j hj).integrable_abs (Nat.zero_le m)
  have hBi : Integrable fun x => Real.exp (η * |x|) * ∑ j ∈ Finset.Icc 1 P, |g j x| :=
    (integrable_finsetSum (Finset.Icc 1 P)
      (f := fun j x => Real.exp (η * |x|) * |g j x|) hgi).congr
      (ae_of_all _ fun x => by simp only [Finset.mul_sum])
  set B : ℝ := ∫ x in Iio 0, Real.exp (η * |x|) * ∑ j ∈ Finset.Icc 1 P, |g j x| with hB
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro hn
  set A : ℝ := ∫ x in Iio 0, Real.exp (η * |x|) * |g n x| with hA
  have hkey : ∀ eps, max e0 1 ≤ eps → A ≤ eps⁻¹ * (K + B) := by
    intro eps heps
    have he1 : 1 ≤ eps := (le_max_right _ _).trans heps
    have ht0 : 0 < eps⁻¹ := inv_pos.mpr (by linarith)
    have ht1 : eps⁻¹ ≤ 1 := inv_le_one_of_one_le₀ he1
    obtain ⟨-, hfn, -, -, hRc, hRle⟩ := hf eps ((le_max_left _ _).trans heps)
    set t : ℝ := eps⁻¹ with ht
    set R : ℝ → ℝ := fun x => f eps x - cepsLambdaDensity x -
      ∑ j ∈ Finset.Icc 1 P, t ^ j * g j x with hR
    have hRi : Integrable fun x => Real.exp (η * |x|) * |R x| := by
      simpa only [iteratedDeriv_zero] using hRc.integrable_abs (Nat.zero_le m)
    have hpt : ∀ x ∈ Iio (0 : ℝ), t ^ n * (Real.exp (η * |x|) * |g n x|) ≤
        Real.exp (η * |x|) * |R x| +
          t ^ (n + 1) * (Real.exp (η * |x|) * ∑ j ∈ Finset.Icc 1 P, |g j x|) := by
      intro x hx
      have hx : x < 0 := hx
      have hRx : R x = -∑ j ∈ Finset.Icc 1 P, t ^ j * g j x := by
        simp only [hR, hfn x hx, cepsLambdaDensity_of_nonpos hx.le]
        ring
      have herase : |∑ j ∈ (Finset.Icc 1 P).erase n, t ^ j * g j x| ≤
          t ^ (n + 1) * ∑ j ∈ Finset.Icc 1 P, |g j x| := by
        refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
        rw [Finset.mul_sum]
        refine (Finset.sum_le_sum fun j hj => ?_).trans
          (Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset n _)
            fun j _ _ => by positivity)
        rw [abs_mul, abs_of_pos (pow_pos ht0 j)]
        rcases lt_or_gt_of_ne (Finset.ne_of_mem_erase hj) with hjn | hjn
        · rw [ih j hjn (Finset.mem_of_mem_erase hj) x hx, abs_zero, mul_zero, mul_zero]
        · exact mul_le_mul_of_nonneg_right (pow_le_pow_of_le_one ht0.le ht1 hjn) (abs_nonneg _)
      have habs : t ^ n * |g n x| ≤ |R x| + t ^ (n + 1) * ∑ j ∈ Finset.Icc 1 P, |g j x| := by
        rw [hRx, abs_neg, ← Finset.add_sum_erase _ _ hn]
        have h1 := abs_add_le (t ^ n * g n x + ∑ j ∈ (Finset.Icc 1 P).erase n, t ^ j * g j x)
          (-∑ j ∈ (Finset.Icc 1 P).erase n, t ^ j * g j x)
        rw [add_neg_cancel_right, abs_neg, abs_mul, abs_of_pos (pow_pos ht0 n)] at h1
        linarith
      have hw := (Real.exp_pos (η * |x|)).le
      calc t ^ n * (Real.exp (η * |x|) * |g n x|) = Real.exp (η * |x|) * (t ^ n * |g n x|) := by
            ring
        _ ≤ Real.exp (η * |x|) * (|R x| + t ^ (n + 1) * ∑ j ∈ Finset.Icc 1 P, |g j x|) :=
            mul_le_mul_of_nonneg_left habs hw
        _ = _ := by ring
    have hint : t ^ n * A ≤ (∫ x in Iio 0, Real.exp (η * |x|) * |R x|) + t ^ (n + 1) * B := by
      rw [hA, hB, ← integral_const_mul, ← integral_const_mul,
        ← integral_add hRi.integrableOn (hBi.const_mul _).integrableOn]
      exact setIntegral_mono_on ((hgi n hn).const_mul _).integrableOn
        (hRi.add (hBi.const_mul _)).integrableOn measurableSet_Iio hpt
    have hRint : (∫ x in Iio 0, Real.exp (η * |x|) * |R x|) ≤ K * t ^ (n + 1) := by
      refine (setIntegral_le_integral hRi (ae_of_all _ fun x => by positivity)).trans ?_
      refine (integral_expWeighted_abs_le_cepsSobolev m η R).trans (hRle.trans ?_)
      exact mul_le_mul_of_nonneg_left
        (pow_le_pow_of_le_one ht0.le ht1 (by have := (Finset.mem_Icc.mp hn).2; omega)) hK
    have hB0 : 0 ≤ B := setIntegral_nonneg measurableSet_Iio fun x _ => by positivity
    have hfin : t ^ n * A ≤ t ^ n * (t * (K + B)) := by
      calc t ^ n * A ≤ K * t ^ (n + 1) + t ^ (n + 1) * B := by linarith
        _ = t ^ n * (t * (K + B)) := by ring
    exact le_of_mul_le_mul_left hfin (pow_pos ht0 n)
  have hlim : Tendsto (fun eps : ℝ => eps⁻¹ * (K + B)) atTop (𝓝 0) := by
    simpa only [zero_mul] using tendsto_inv_atTop_zero.mul_const (K + B)
  have hA0 : A ≤ 0 := ge_of_tendsto hlim (eventually_atTop.mpr ⟨max e0 1, hkey⟩)
  have hAeq : A = 0 :=
    le_antisymm hA0 (setIntegral_nonneg measurableSet_Iio fun x _ => by positivity)
  have hae := (integral_eq_zero_iff_of_nonneg (fun x => by positivity)
    (hgi n hn).integrableOn).mp hAeq
  rw [EventuallyEq, ae_restrict_iff' measurableSet_Iio] at hae
  refine eq_zero_of_ae_of_neg ((h.coeff n hn).continuous) (hae.mono fun x hx hx0 => ?_)
  have hx' : Real.exp (η * |x|) * |g n x| = 0 := hx hx0
  rcases mul_eq_zero.mp hx' with h0 | h0
  · exact absurd h0 (Real.exp_pos _).ne'
  · exact abs_eq_zero.mp h0

end PGM
