import PLAStochastic.Index.CEPS.Glue.T5

/-! # Flat normal-slope error before finite mean-jet identification

The actual normalized mean is close to the genuine normal slope to every
inverse-epsilon order. No finite jet coefficient premise is used.
-/

namespace PGM
noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology Set

/-- S-10 derivative transfer without a mean-expansion premise. -/
theorem ceps_normal_mean_close_of_normal
    {Gn : ℝ → ProbabilityMeasure ℝ → ℂ → ℂ}
    {Dn : ℝ → ProbabilityMeasure ℝ → ℂ}
    (hclose : CepsNormalClose Gn) (htaylor : CepsNormalTaylor Gn Dn) :
    ∀ P : ℕ, ∃ m : ℕ, ∀ D θ vlo vhi η : ℝ,
      0 < D → 0 < θ → 0 < vlo → vlo ≤ vhi → 0 < η →
      ∃ r : ℝ, 0 < r ∧ ∃ K eps₀ : ℝ, ∀ eps : ℝ, eps₀ ≤ eps →
        ∀ ν : ProbabilityMeasure ℝ, CepsInputClass D θ vlo vhi m η r ν →
          ‖((lawC eps ν / eps ^ 2 : ℝ) : ℂ) + 4 * Dn eps ν‖ ≤
            K * (eps⁻¹) ^ P := by
  intro P
  obtain ⟨m₀, hcl⟩ := hclose
  obtain ⟨m₁, hty⟩ := htaylor
  refine ⟨max m₀ m₁, fun D θ vlo vhi η hD hθ hvlo hv hη => ?_⟩
  obtain ⟨r₀, hr₀, K₀, c₀, t₀, e₀, hc₀, ht₀, p₀, H0⟩ := hcl D θ vlo vhi η hD hθ hvlo hv hη
  obtain ⟨r₁, hr₁, M, y₀, e₁, hy₀, q, H1⟩ := hty D θ vlo vhi η hD hθ hvlo hv hη
  obtain ⟨e₃, s_lo, s_hi, B₂, he₃, hslo, hB₂, Hm⟩ := ceps_class_moments hD hθ hvlo hv
  obtain ⟨Ka, hKa0, hKa⟩ := exists_pow_mul_exp_neg_le (max p₀ q) P (half_pos hc₀)
  set σ : ℝ := min t₀ (y₀ / 4) with hσ
  have hσpos : 0 < σ := lt_min ht₀ (by positivity)
  refine ⟨min r₀ r₁, lt_min hr₀ hr₁,
    (|K₀| / σ + σ * (B₂ + 16 * |M|)) * Ka, max (max e₀ e₁) e₃,
    fun eps heps ν hν => ?_⟩
  have he₀ : e₀ ≤ eps := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) heps
  have he₁ : e₁ ≤ eps := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) heps
  have he₃' : e₃ ≤ eps := le_trans (le_max_right _ _) heps
  have heps1 : 1 ≤ eps := he₃.trans he₃'
  have hepspos : 0 < eps := lt_of_lt_of_le one_pos heps1
  have hν₀ := hν.mono (le_max_left m₀ _) (min_le_left _ _)
  have hν₁ := hν.mono (le_max_right m₀ m₁) (min_le_right _ _)
  obtain ⟨-, -, hS1, hW, hS2, hS2b⟩ := Hm eps he₃' ν hν.reg
  -- the evaluation point `s = σ e^{-c₀ε/2} / ε²`
  set E : ℝ := Real.exp (-(c₀ / 2) * eps) with hE
  have hEpos : 0 < E := Real.exp_pos _
  have hE1 : E ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
  have he2 : 1 ≤ eps ^ 2 := one_le_pow₀ heps1
  set s : ℝ := σ * E / eps ^ 2 with hs
  have hspos : 0 < s := by positivity
  have h4s : 4 * eps ^ 2 * s = 4 * σ * E := by rw [hs]; field_simp
  have hsle : s ≤ σ := by
    rw [hs, div_le_iff₀ (by positivity)]
    calc σ * E ≤ σ * 1 := mul_le_mul_of_nonneg_left hE1 hσpos.le
      _ ≤ σ * eps ^ 2 := mul_le_mul_of_nonneg_left he2 hσpos.le
  have hst : |s| ≤ t₀ := by rw [abs_of_pos hspos]; exact hsle.trans (min_le_left _ _)
  have hsy : |4 * eps ^ 2 * s| ≤ y₀ := by
    rw [h4s, abs_of_pos (by positivity)]
    calc 4 * σ * E ≤ 4 * σ * 1 := mul_le_mul_of_nonneg_left hE1 (by positivity)
      _ ≤ 4 * (y₀ / 4) := by linarith [min_le_right t₀ (y₀ / 4)]
      _ = y₀ := by ring
  have hcl' := H0 eps he₀ ν hν₀ s hst
  have hty' := H1 eps he₁ ν hν₁ (4 * eps ^ 2 * s) hsy
  have htr := norm_lawC_add_le_of_close (Dn := Dn eps ν) hspos hS1 hW hS2 hS2b hcl' hty'
  -- the exponentially small part, divided by `ε²`
  have hexp : Real.exp (-c₀ * eps) = E * E := by rw [hE, ← Real.exp_add]; ring_nf
  have hmain : ‖(lawC eps ν : ℂ) + 4 * (eps : ℂ) ^ 2 * Dn eps ν‖ / eps ^ 2 ≤
      (|K₀| / σ + σ * (B₂ + 16 * |M|)) * (eps ^ max p₀ q * E) := by
    rw [div_le_iff₀ (by positivity)]
    refine htr.trans ?_
    have hp : eps ^ p₀ ≤ eps ^ max p₀ q := pow_le_pow_right₀ heps1 (le_max_left _ _)
    have hq : eps ^ q ≤ eps ^ max p₀ q := pow_le_pow_right₀ heps1 (le_max_right _ _)
    have t1 : K₀ * eps ^ p₀ * Real.exp (-c₀ * eps) / s ≤
        |K₀| / σ * (eps ^ max p₀ q * E) * eps ^ 2 := by
      rw [hexp, hs, div_div_eq_mul_div, div_le_iff₀ (by positivity)]
      have : K₀ * eps ^ p₀ ≤ |K₀| * eps ^ max p₀ q :=
        mul_le_mul (le_abs_self K₀) hp (by positivity) (abs_nonneg _)
      calc K₀ * eps ^ p₀ * (E * E) * eps ^ 2 ≤ |K₀| * eps ^ max p₀ q * (E * E) * eps ^ 2 := by
            gcongr
        _ = |K₀| / σ * (eps ^ max p₀ q * E) * eps ^ 2 * (σ * E) := by
            field_simp
    have t2 : (B₂ * eps ^ 4 + 16 * (M * eps ^ q) * eps ^ 4) * s ≤
        σ * (B₂ + 16 * |M|) * (eps ^ max p₀ q * E) * eps ^ 2 := by
      have hM : M * eps ^ q ≤ |M| * eps ^ max p₀ q :=
        mul_le_mul (le_abs_self M) hq (by positivity) (abs_nonneg _)
      have he4 : eps ^ 2 ≤ eps ^ 4 := pow_le_pow_right₀ heps1 (by norm_num)
      have hmax1 : 1 ≤ eps ^ max p₀ q := one_le_pow₀ heps1
      rw [hs]
      have e1 : (B₂ * eps ^ 4 + 16 * (M * eps ^ q) * eps ^ 4) * (σ * E / eps ^ 2) =
          σ * E * (B₂ * eps ^ 2 + 16 * (M * eps ^ q) * eps ^ 2) := by
        field_simp
      rw [e1]
      have e2 : σ * (B₂ + 16 * |M|) * (eps ^ max p₀ q * E) * eps ^ 2 =
          σ * E * (B₂ * eps ^ max p₀ q * eps ^ 2 + 16 * (|M| * eps ^ max p₀ q) * eps ^ 2) := by
        ring
      rw [e2]
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      have : B₂ * eps ^ 2 ≤ B₂ * eps ^ max p₀ q * eps ^ 2 := by
        have := mul_le_mul_of_nonneg_left hmax1 hB₂
        nlinarith [this, he2]
      have h16 : 16 * (M * eps ^ q) * eps ^ 2 ≤ 16 * (|M| * eps ^ max p₀ q) * eps ^ 2 := by
        gcongr
      linarith
    calc K₀ * eps ^ p₀ * Real.exp (-c₀ * eps) / s + (B₂ * eps ^ 4 + 16 * (M * eps ^ q) * eps ^ 4) * s
        ≤ |K₀| / σ * (eps ^ max p₀ q * E) * eps ^ 2 +
            σ * (B₂ + 16 * |M|) * (eps ^ max p₀ q * E) * eps ^ 2 := add_le_add t1 t2
      _ = (|K₀| / σ + σ * (B₂ + 16 * |M|)) * (eps ^ max p₀ q * E) * eps ^ 2 := by ring
  have hKa' : eps ^ max p₀ q * E ≤ Ka * (eps⁻¹) ^ P := by
    exact hKa eps heps1
  have hcoef : 0 ≤ |K₀| / σ + σ * (B₂ + 16 * |M|) := by positivity
  have hfirst : ‖(lawC eps ν : ℂ) + 4 * (eps : ℂ) ^ 2 * Dn eps ν‖ / eps ^ 2 ≤
      (|K₀| / σ + σ * (B₂ + 16 * |M|)) * Ka * (eps⁻¹) ^ P := by
    refine hmain.trans ?_
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left hKa' hcoef
  have hid : ((lawC eps ν / eps ^ 2 : ℝ) : ℂ) + 4 * Dn eps ν =
      ((lawC eps ν : ℂ) + 4 * (eps : ℂ) ^ 2 * Dn eps ν) / ((eps : ℂ) ^ 2) := by
    have hne : (eps : ℂ) ≠ 0 := by exact_mod_cast hepspos.ne'
    push_cast
    field_simp
  rw [hid, norm_div, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hepspos]
  exact hfirst

end
end PGM
