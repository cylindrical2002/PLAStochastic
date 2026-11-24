import PLAStochastic.Index.CEPS.Glue.Moments
import PLAStochastic.ForMathlib.Analysis.Calculus.DerivativeTransfer

/-!
# WP11a: S-10 (T5) from the normal transform

* `norm_lawC_add_le_of_close` (S-10, first step, one point): Wald's `E S_T = C` and the Taylor
  bound `‖E e^{-isS_T} - 1 + is E S_T‖ ≤ s² E S_T²` transfer the closeness of the actual and
  normal transforms at `t = is` into `‖C + 4ε² ∂_z Ĝ(b,0)‖ ≤ δ/s + (E S_T² + 16 M ε⁴) s`, i.e.
  `|b² E T + ∂_z Ĝ(b,0)|` is at most `b²` times this;
* `cepsT5_of_normal`: with `s = σ e^{-cε/2}/ε²` the right side is `O(ε^p e^{-cε/2})`, and the
  `b`-expansion of `-∂_z Ĝ(b,0)` gives `CepsT5 J` for `c_k = 4 · 2^{-k} C_k`.
-/

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set

/-- **S-10, first step, at one point.** -/
theorem norm_lawC_add_le_of_close {Gn : ℝ → ProbabilityMeasure ℝ → ℂ → ℂ} {Dn : ℂ} {eps : ℝ}
    {ν : ProbabilityMeasure ℝ} {s δ M B₂ : ℝ} (hs : 0 < s)
    (hS1 : Integrable (stopSum eps) (iidLaw ν)) (hW : ∫ g, stopSum eps g ∂(iidLaw ν) = lawC eps ν)
    (hS2 : Integrable (fun g => stopSum eps g ^ 2) (iidLaw ν))
    (hB₂ : ∫ g, stopSum eps g ^ 2 ∂(iidLaw ν) ≤ B₂)
    (hclose : ‖cepsActualTransform eps ν (Complex.I * s) -
      Gn eps ν (Complex.I * ((4 * eps ^ 2 * s : ℝ) : ℂ))‖ ≤ δ)
    (htay : ‖Gn eps ν (Complex.I * ((4 * eps ^ 2 * s : ℝ) : ℂ)) - 1 -
      Complex.I * ((4 * eps ^ 2 * s : ℝ) : ℂ) * Dn‖ ≤ M * (4 * eps ^ 2 * s) ^ 2) :
    ‖(lawC eps ν : ℂ) + 4 * (eps : ℂ) ^ 2 * Dn‖ ≤ δ / s + (B₂ + 16 * M * eps ^ 4) * s := by
  have hτ : Complex.I * (s : ℂ) ≠ 0 := mul_ne_zero Complex.I_ne_zero (by exact_mod_cast hs.ne')
  have hτn : ‖Complex.I * (s : ℂ)‖ = s := by
    rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs]
  have hact := norm_integral_cexp_sub_le (P := iidLaw ν) hS1 hS2 s
  rw [hW] at hact
  have hG : ‖cepsActualTransform eps ν (Complex.I * s) - 1 -
      Complex.I * s * (-(lawC eps ν : ℂ))‖ ≤ B₂ * ‖Complex.I * (s : ℂ)‖ ^ 2 := by
    refine hact.trans ?_
    rw [mul_comm]
    exact mul_le_mul_of_nonneg_right hB₂ (by positivity)
  have hĜ : ‖Gn eps ν (Complex.I * ((4 * eps ^ 2 * s : ℝ) : ℂ)) - 1 -
      Complex.I * s * (4 * (eps : ℂ) ^ 2 * Dn)‖ ≤ (16 * M * eps ^ 4) * ‖Complex.I * (s : ℂ)‖ ^ 2 := by
    have e : Complex.I * s * (4 * (eps : ℂ) ^ 2 * Dn) =
        Complex.I * ((4 * eps ^ 2 * s : ℝ) : ℂ) * Dn := by push_cast; ring
    rw [e, hτn]
    refine htay.trans (le_of_eq ?_)
    ring
  have h := norm_sub_le_of_taylor_close hτ hclose hG hĜ
  rw [hτn] at h
  have e : (lawC eps ν : ℂ) + 4 * (eps : ℂ) ^ 2 * Dn =
      -(-(lawC eps ν : ℂ) - 4 * (eps : ℂ) ^ 2 * Dn) := by ring
  rw [e, norm_neg]
  exact h

/-- The scalar coefficients `c_k = 4 · 2^{-k} C_k` turn the `b`-sum into the `h`-sum. -/
theorem sum_inv_pow_scal {J : CepsJetData} {Cs : ℕ → (ℕ → ℝ) → ℝ}
    (hscal : ∀ k p, J.scal k p = 4 * (2⁻¹) ^ k * Cs k p) (P : ℕ) (eps : ℝ) (p : ℕ → ℝ) :
    ∑ k ∈ Finset.range (P + 1), (eps⁻¹) ^ k * J.scal k p =
      4 * ∑ k ∈ Finset.range (P + 1), ((2 * eps)⁻¹) ^ k * Cs k p := by
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [hscal, mul_inv, mul_pow]
  ring

/-- **T5 from the normal transform.** -/
theorem cepsT5_of_normal {J : CepsJetData} {Gn : ℝ → ProbabilityMeasure ℝ → ℂ → ℂ}
    {Dn : ℝ → ProbabilityMeasure ℝ → ℂ} {Cs : ℕ → (ℕ → ℝ) → ℝ}
    (hclose : CepsNormalClose Gn) (htaylor : CepsNormalTaylor Gn Dn)
    (hmean : CepsNormalMeanExpansion J Dn Cs)
    (hscal : ∀ k p, J.scal k p = 4 * (2⁻¹) ^ k * Cs k p) : CepsT5 J := by
  intro P
  obtain ⟨m₀, hcl⟩ := hclose
  obtain ⟨m₁, hty⟩ := htaylor
  obtain ⟨m₂, hmn⟩ := hmean P
  refine ⟨max m₀ (max m₁ m₂), fun D θ vlo vhi η hD hθ hvlo hv hη => ?_⟩
  obtain ⟨r₀, hr₀, K₀, c₀, t₀, e₀, hc₀, ht₀, p₀, H0⟩ := hcl D θ vlo vhi η hD hθ hvlo hv hη
  obtain ⟨r₁, hr₁, M, y₀, e₁, hy₀, q, H1⟩ := hty D θ vlo vhi η hD hθ hvlo hv hη
  obtain ⟨r₂, hr₂, K₂, e₂, H2⟩ := hmn D θ vlo vhi η hD hθ hvlo hv hη
  obtain ⟨e₃, s_lo, s_hi, B₂, he₃, hslo, hB₂, Hm⟩ := ceps_class_moments hD hθ hvlo hv
  obtain ⟨Ka, hKa0, hKa⟩ := exists_pow_mul_exp_neg_le (max p₀ q) (P + 1) (half_pos hc₀)
  set σ : ℝ := min t₀ (y₀ / 4) with hσ
  have hσpos : 0 < σ := lt_min ht₀ (by positivity)
  refine ⟨min r₀ (min r₁ r₂), lt_min hr₀ (lt_min hr₁ hr₂),
    (|K₀| / σ + σ * (B₂ + 16 * |M|)) * Ka + 4 * |K₂|, max (max e₀ e₁) (max e₂ e₃),
    fun eps heps ν hν => ?_⟩
  have he₀ : e₀ ≤ eps := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) heps
  have he₁ : e₁ ≤ eps := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) heps
  have he₂ : e₂ ≤ eps := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) heps
  have he₃' : e₃ ≤ eps := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) heps
  have heps1 : 1 ≤ eps := he₃.trans he₃'
  have hepspos : 0 < eps := lt_of_lt_of_le one_pos heps1
  have hν₀ := hν.mono (le_max_left m₀ _) (min_le_left _ _)
  have hν₁ := hν.mono ((le_max_left m₁ m₂).trans (le_max_right m₀ _))
    ((min_le_right _ _).trans (min_le_left _ _))
  have hν₂ := hν.mono ((le_max_right m₁ m₂).trans (le_max_right m₀ _))
    ((min_le_right _ _).trans (min_le_right _ _))
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
  have hKa' : eps ^ max p₀ q * E ≤ Ka * (eps⁻¹) ^ (P + 1) := by
    exact hKa eps heps1
  have hcoef : 0 ≤ |K₀| / σ + σ * (B₂ + 16 * |M|) := by positivity
  have hfirst : ‖(lawC eps ν : ℂ) + 4 * (eps : ℂ) ^ 2 * Dn eps ν‖ / eps ^ 2 ≤
      (|K₀| / σ + σ * (B₂ + 16 * |M|)) * Ka * (eps⁻¹) ^ (P + 1) := by
    refine hmain.trans ?_
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left hKa' hcoef
  have hsecond := H2 eps he₂ ν hν₂
  -- assemble
  have hid : ((lawC eps ν / eps ^ 2 -
      ∑ k ∈ Finset.range (P + 1), (eps⁻¹) ^ k * J.scal k (J.jet ν) : ℝ) : ℂ) =
      ((lawC eps ν : ℂ) + 4 * (eps : ℂ) ^ 2 * Dn eps ν) / ((eps : ℂ) ^ 2) -
        4 * (Dn eps ν + ∑ k ∈ Finset.range (P + 1),
          ((((2 * eps)⁻¹) ^ k * Cs k (J.jet ν) : ℝ) : ℂ)) := by
    rw [sum_inv_pow_scal hscal]
    have hne : (eps : ℂ) ≠ 0 := by exact_mod_cast hepspos.ne'
    push_cast
    field_simp
    ring
  have hnorm : |lawC eps ν / eps ^ 2 -
      ∑ k ∈ Finset.range (P + 1), (eps⁻¹) ^ k * J.scal k (J.jet ν)| =
      ‖((lawC eps ν : ℂ) + 4 * (eps : ℂ) ^ 2 * Dn eps ν) / ((eps : ℂ) ^ 2) -
        4 * (Dn eps ν + ∑ k ∈ Finset.range (P + 1),
          ((((2 * eps)⁻¹) ^ k * Cs k (J.jet ν) : ℝ) : ℂ))‖ := by
    rw [← hid, Complex.norm_real, Real.norm_eq_abs]
  rw [hnorm]
  refine (norm_sub_le _ _).trans ?_
  rw [norm_div, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hepspos, norm_mul,
    show ‖(4 : ℂ)‖ = 4 by norm_num]
  have h2 : 4 * ‖Dn eps ν + ∑ k ∈ Finset.range (P + 1),
      ((((2 * eps)⁻¹) ^ k * Cs k (J.jet ν) : ℝ) : ℂ)‖ ≤ 4 * |K₂| * (eps⁻¹) ^ (P + 1) := by
    have : K₂ * (eps⁻¹) ^ (P + 1) ≤ |K₂| * (eps⁻¹) ^ (P + 1) :=
      mul_le_mul_of_nonneg_right (le_abs_self K₂) (by positivity)
    linarith
  calc ‖(lawC eps ν : ℂ) + 4 * (eps : ℂ) ^ 2 * Dn eps ν‖ / eps ^ 2 +
        4 * ‖Dn eps ν + ∑ k ∈ Finset.range (P + 1),
          ((((2 * eps)⁻¹) ^ k * Cs k (J.jet ν) : ℝ) : ℂ)‖
      ≤ (|K₀| / σ + σ * (B₂ + 16 * |M|)) * Ka * (eps⁻¹) ^ (P + 1) +
          4 * |K₂| * (eps⁻¹) ^ (P + 1) := add_le_add hfirst h2
    _ = ((|K₀| / σ + σ * (B₂ + 16 * |M|)) * Ka + 4 * |K₂|) * (eps⁻¹) ^ (P + 1) := by ring

end

end PGM
