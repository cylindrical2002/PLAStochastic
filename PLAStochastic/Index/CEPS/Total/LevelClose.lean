import PLAStochastic.Index.CEPS.Total.Level
import PLAStochastic.Index.CEPS.Total.Instance
import PLAStochastic.Index.CEPS.Total.DrawupClass

/-!
# WP10: S-9 uniformly on one level

On level `n` (`CepsLevel n`, fixed domain `cepsLevelDomain n` and cutoff `cepsLevelCutoff n`) the
outer tails (X6), the drawup (S-8, `drawup_close`) and the pair error (S-6, premise
`CepsPairCloseLevel n` until WP9 lands) give, uniformly over the level,

  `‖E e^{-i y S_T} - cepsScaledTrueNormalExpression dom_n ρW (2ε)⁻¹ δ_n (4 ε² i y)‖ ≤ K εᵖ e^{-c ε}`

for `|y| ≤ t₀`, `ε ≥ ε₀` (`ceps_close_level`).
-/

noncomputable section
open Complex Set Metric MeasureTheory
open PGM.WienerHopf

namespace PGM

theorem cepsLevelDomain_two_c₀_le (n : ℕ) : 2 * (cepsLevelDomain n).c₀ ≤ cepsLevelRate n := by
  set dom := cepsLevelDomain n
  have h1 := dom.c₀_le
  have h2 := dom.ρA_R
  have h3 : cepsChartRadius (cepsLevelStepD n) (cepsLevelRate n) ≤
      cepsCgfRadius (cepsLevelStepD n) (cepsLevelRate n) / 8 := by
    unfold cepsChartRadius; exact min_le_left _ _
  have h4 : cepsCgfRadius (cepsLevelStepD n) (cepsLevelRate n) ≤ cepsLevelRate n / 4 := by
    unfold cepsCgfRadius; exact min_le_left _ _
  have h5 := dom.c₀_pos
  linarith

theorem cepsScaledTrueNormalExpression_zero {D θ v : ℝ} (dom : CepsCanonDomain D θ v)
    (ρW : Measure ℝ) (b δ : ℝ) : cepsScaledTrueNormalExpression dom ρW b δ 0 = 1 := by
  unfold cepsScaledTrueNormalExpression cepsScaledMarkedEndpoint cepsScaledMarkedDiscount
  simp

/-- **S-6 on level `n`** (premise until WP9 lands): the actual pair is exponentially close to the
physical normal pair on `[-δ_n, δ_n]`, uniformly over the level, for small imaginary marks. -/
def CepsPairCloseLevel (n : ℕ) : Prop :=
  ∃ K c t₀ eps₀ : ℝ, ∃ p : ℕ, 0 < c ∧ 0 < t₀ ∧
    ∀ eps : ℝ, eps₀ ≤ eps → ∀ ν : ProbabilityMeasure ℝ, ∀ f : ℝ → ℝ, CepsLevelDensity n ν f →
    ∀ y : ℝ, y ≠ 0 → |y| ≤ t₀ → ∀ μ ∈ Icc (-cepsLevelCutoff n) (cepsLevelCutoff n),
      ‖cepsActualPair ν f eps (Complex.I * y) μ -
        cepsPhysicalPair (cepsLevelDomain n) ((ν : Measure ℝ).map fun x => 1 - x) (2 * eps)⁻¹
          (Complex.I * ((4 * eps ^ 2 * y : ℝ) : ℂ)) μ‖ ≤ K * eps ^ p * Real.exp (-c * eps)

/-- The scaled mark of `t = i y` at `b = (2ε)⁻¹`. -/
theorem scaled_mark_eq {eps : ℝ} (heps : 0 < eps) (y : ℝ) :
    (((2 * eps)⁻¹ : ℝ) : ℂ) ^ 2 * (Complex.I * ((4 * eps ^ 2 * y : ℝ) : ℂ)) = Complex.I * y := by
  have he : (eps : ℂ) ≠ 0 := ofReal_ne_zero.mpr heps.ne'
  push_cast
  field_simp
  ring

theorem aux_disc_lt {a q δ : ℝ} (ha : a ≤ q / 8) (hq : 0 < q) (hδ0 : 0 ≤ δ) (hδ : δ < 1)
    (_ha0 : 0 ≤ a) : a * (1 + δ) < q / 4 := by nlinarith

theorem aux_disc_le {a r δ : ℝ} (ha : a ≤ r / 2) (hr : 0 < r) (hδ0 : 0 ≤ δ) (hδ : δ < 1)
    (_ha0 : 0 ≤ a) : a * (1 + δ) ≤ r := by nlinarith

theorem aux_inv_le {eps δ : ℝ} (hδ : 0 < δ) (h : 1 / (2 * δ) ≤ eps) : (2 * eps)⁻¹ ≤ δ := by
  have heps : 0 < eps := lt_of_lt_of_le (by positivity) h
  rw [inv_eq_one_div, div_le_iff₀ (by positivity)]
  have := (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * δ)).mp h
  linarith

theorem aux_inv_le' {eps B : ℝ} (hB : 0 < B) (h : 8 / B ≤ eps) : (2 * eps)⁻¹ ≤ B / 16 := by
  have heps : 0 < eps := lt_of_lt_of_le (by positivity) h
  rw [inv_eq_one_div, div_le_iff₀ (by positivity)]
  have := (div_le_iff₀ hB).mp h
  linarith

theorem aux_width {l eps δ : ℝ} (h : l / 2 ≤ eps) (heps : 0 ≤ eps) (hδ : 0 ≤ δ) :
    l ≤ 2 * eps * (1 + δ) := by nlinarith

theorem aux_exp_le {a c eps : ℝ} (hc : c ≤ a) (heps : 0 ≤ eps) :
    Real.exp (-a * eps) ≤ Real.exp (-c * eps) :=
  Real.exp_le_exp.mpr (by nlinarith)

theorem pow_le_pow_of_one_le {x : ℝ} (hx : 1 ≤ x) {a b : ℕ} (h : a ≤ b) : x ^ a ≤ x ^ b :=
  pow_le_pow_right₀ hx h

/-- **S-9, uniform over a family of laws** given by a predicate `P` with fixed class data. -/
theorem ceps_close_uniform {D θ v : ℝ} (dom : CepsCanonDomain D θ v) (hθ : 0 < θ) (hD : 0 < D)
    (hv : 0 < v) {D₀ θ₀ vlo vhi : ℝ} (hD₀ : 0 < D₀) (hθ₀ : 0 < θ₀) (hvlo : 0 < vlo)
    {m : ℕ} {η M δ : ℝ} (hm : 2 ≤ m) (hη : 2 * dom.c₀ ≤ η)
    (hbase : 0 < dom.trueDecayScaleBase M)
    (hδ : 0 < δ) (hδR : δ ≤ dom.renewalMu) (hδμ8 : δ ≤ dom.μ₀ / 8)
    (hδB : δ ≤ dom.trueDecayScaleBase M / 4) (hδ12 : δ ≤ 1 / 2)
    (P : ProbabilityMeasure ℝ → Prop) (Pf : ProbabilityMeasure ℝ → (ℝ → ℝ) → Prop)
    (hdata : ∀ ν, P ν → ∃ f : ℝ → ℝ, Pf ν f ∧ RegLaw D₀ θ₀ vlo vhi ν ∧ CepsGapDensity ν f D₀ ∧
      IsStepLaw ((ν : Measure ℝ).map fun x => 1 - x) (fun x => f (1 - x)) D θ v ∧
      CepsSobolevClass m η (fun x => f (1 - x)) ∧ cepsSobolev m η (fun x => f (1 - x)) ≤ M)
    (hS6 : ∃ K c t₀ eps₀ : ℝ, ∃ p : ℕ, 0 < c ∧ 0 < t₀ ∧
      ∀ eps : ℝ, eps₀ ≤ eps → ∀ ν : ProbabilityMeasure ℝ, ∀ f : ℝ → ℝ, Pf ν f →
      ∀ y : ℝ, y ≠ 0 → |y| ≤ t₀ → ∀ μ ∈ Icc (-δ) δ,
        ‖cepsActualPair ν f eps (Complex.I * y) μ -
          cepsPhysicalPair dom ((ν : Measure ℝ).map fun x => 1 - x) (2 * eps)⁻¹
            (Complex.I * ((4 * eps ^ 2 * y : ℝ) : ℂ)) μ‖ ≤ K * eps ^ p * Real.exp (-c * eps)) :
    ∃ K c t₀ eps₀ : ℝ, ∃ p : ℕ, 0 ≤ K ∧ 0 < c ∧ 0 < t₀ ∧ 1 ≤ eps₀ ∧
      ∀ eps : ℝ, eps₀ ≤ eps → ∀ ν : ProbabilityMeasure ℝ, P ν → ∀ y : ℝ, |y| ≤ t₀ →
        ‖cepsActualTransform eps ν (Complex.I * y) -
          cepsScaledTrueNormalExpression dom ((ν : Measure ℝ).map fun x => 1 - x)
            (2 * eps)⁻¹ δ (Complex.I * ((4 * eps ^ 2 * y : ℝ) : ℂ))‖ ≤
          K * eps ^ p * Real.exp (-c * eps) := by
  set base := dom.trueDecayScaleBase M
  have hμ₀ := dom.μ₀_pos
  have hδ1 : δ < 1 := by linarith
  have hδμ : δ < dom.μ₀ / 4 := by linarith
  -- X6, S-8, S-6
  obtain ⟨K₆, C₆, w₀, hK₆, hC₆, hw₀, hX6⟩ :=
    ceps_outer_tails_of_regLaw (vlo := vlo) (vhi := vhi) hD₀ hθ₀ hvlo hδ hδ1
  obtain ⟨C₈, c₈, l₈, hc₈, hC₈, hS8⟩ := drawup_close dom hθ hD hv hδ hδR
  obtain ⟨K₉, c₉, t₉, e₉, p₉, hc₉, ht₉, hS6'⟩ := hS6
  -- constants
  have hq₀ := dom.q₀_pos
  have hc0 := dom.c₀_pos
  have hrd := dom.renewalDiscount_pos hD
  have hur := cepsMarkedUnitRadius_pos hD hθ
  set t₀ := min (min t₉ ((base / 8) ^ 2 / 2))
    (min (min (dom.q₀ / 8) (dom.renewalDiscount / 2)) (min (dom.c₀ / 4)
      (cepsMarkedUnitRadius D θ / 2))) with ht₀_def
  have ht₀ : 0 < t₀ := lt_min (lt_min ht₉ (by positivity))
    (lt_min (lt_min (by positivity) (by positivity)) (lt_min (by positivity) (by positivity)))
  have ht₀9 : t₀ ≤ t₉ := (min_le_left _ _).trans (min_le_left _ _)
  have ht₀b : t₀ ≤ (base / 8) ^ 2 / 2 := (min_le_left _ _).trans (min_le_right _ _)
  have ht₀q : t₀ ≤ dom.q₀ / 8 :=
    (min_le_right _ _).trans ((min_le_left _ _).trans (min_le_left _ _))
  have ht₀r : t₀ ≤ dom.renewalDiscount / 2 :=
    (min_le_right _ _).trans ((min_le_left _ _).trans (min_le_right _ _))
  have ht₀c : t₀ ≤ dom.c₀ / 4 :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have ht₀u : t₀ ≤ cepsMarkedUnitRadius D θ / 2 :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  set eps₀ := max (max 1 (1 / (2 * δ))) (max (8 / base) (max (w₀ / 2) (max (l₈ / 2) e₉)))
  have he1 : 1 ≤ eps₀ := (le_max_left _ _).trans (le_max_left _ _)
  have heδ : 1 / (2 * δ) ≤ eps₀ := (le_max_right _ _).trans (le_max_left _ _)
  have heb : 8 / base ≤ eps₀ := (le_max_left _ _).trans (le_max_right _ _)
  have hew : w₀ / 2 ≤ eps₀ :=
    (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have hel : l₈ / 2 ≤ eps₀ := (le_max_left _ _).trans
    ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _)))
  have he9 : e₉ ≤ eps₀ := (le_max_right _ _).trans
    ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _)))
  set c := min (2 * C₆) (min c₉ (2 * c₈))
  have hc : 0 < c := lt_min (by positivity) (lt_min hc₉ (by positivity))
  set p := max 9 p₉
  set K := 4 * 2 ^ 9 * K₆ + 2 * max K₉ 0 + C₈
  have hK : 0 ≤ K := by positivity
  refine ⟨K, c, t₀, eps₀, p, hK, hc, ht₀, he1, ?_⟩
  intro eps heps ν hν y hy
  have heps1 : 1 ≤ eps := he1.trans heps
  have heps0 : 0 < eps := by linarith
  have hEpos : 0 ≤ K * eps ^ p * Real.exp (-c * eps) := by positivity
  by_cases hy0 : y = 0
  · subst hy0
    simp only [ofReal_zero, mul_zero, cepsActualTransform_zero,
      cepsScaledTrueNormalExpression_zero, sub_self, norm_zero]
    exact hEpos
  obtain ⟨f, hPf, hreg, hgap, hW, hS, hSM⟩ := hdata ν hν
  set w := 2 * eps with hw_def
  have hw : 0 < w := by positivity
  set z := Complex.I * ((4 * eps ^ 2 * y : ℝ) : ℂ) with hz_def
  have htz : ((w⁻¹ : ℝ) : ℂ) ^ 2 * z = Complex.I * y := by
    rw [hw_def, hz_def]; exact scaled_mark_eq heps0 y
  have hw2 : w / 2 = eps := by rw [hw_def]; ring
  have hyn : ‖Complex.I * (y : ℂ)‖ = |y| := by
    rw [norm_mul, Complex.norm_I, one_mul, norm_real, Real.norm_eq_abs]
  have hyre : (Complex.I * (y : ℂ)).re = 0 := by simp
  -- the identification data
  have hbinv : w⁻¹ ≤ δ := by rw [hw_def]; exact aux_inv_le hδ (heδ.trans heps)
  have hbb : w⁻¹ ≤ base / 16 := by rw [hw_def]; exact aux_inv_le' hbase (heb.trans heps)
  have hsq : Real.sqrt |y| < base / 8 := by
    have h1 : |y| < (base / 8) ^ 2 := by
      have := hy.trans (ht₀b)
      have : 0 < (base / 8) ^ 2 := by positivity
      linarith
    calc Real.sqrt |y| < Real.sqrt ((base / 8) ^ 2) := Real.sqrt_lt_sqrt (abs_nonneg _) h1
      _ = base / 8 := Real.sqrt_sq (by positivity)
  have hzn : ‖z‖ = 4 * eps ^ 2 * |y| := by
    rw [hz_def, norm_mul, Complex.norm_I, one_mul, norm_real, Real.norm_eq_abs, abs_mul,
      abs_of_pos (by positivity : (0 : ℝ) < 4 * eps ^ 2)]
  have hfreq : w⁻¹ * (1 + Real.sqrt ‖z‖) < base / 4 := by
    have hs : Real.sqrt ‖z‖ = 2 * eps * Real.sqrt |y| := by
      rw [hzn, Real.sqrt_mul (by positivity), Real.sqrt_mul (by norm_num) ,
        Real.sqrt_sq heps0.le, show Real.sqrt 4 = 2 by
          rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    rw [hs, mul_add, mul_one, show w⁻¹ * (2 * eps * Real.sqrt |y|) = Real.sqrt |y| by
      rw [hw_def]; field_simp]
    linarith
  have hdisc : ‖((w⁻¹ : ℝ) : ℂ) ^ 2 * z‖ * (1 + δ) < dom.q₀ / 4 := by
    rw [htz, hyn]
    exact aux_disc_lt (hy.trans ht₀q) hq₀ hδ.le hδ1 (abs_nonneg y)
  have hI : CepsIdentData dom ((ν : Measure ℝ).map fun x => 1 - x) (fun x => f (1 - x))
      m η M w⁻¹ δ z :=
    { sobolev := hS
      order := hm
      weight := hη
      bound := hSM
      pos := inv_pos.mpr hw
      le := hbinv
      cut := hδB
      drift := by linarith
      imag := by
        show (Complex.I * ((4 * eps ^ 2 * y : ℝ) : ℂ)).re = 0
        simp only [mul_re, Complex.I_re, Complex.I_im, ofReal_re, ofReal_im]; ring
      ne := by
        rw [hz_def]
        refine mul_ne_zero Complex.I_ne_zero (ofReal_ne_zero.mpr ?_)
        exact mul_ne_zero (by positivity) hy0
      freq := hfreq
      disc := hdisc.le.trans (by linarith)
      unit := by
        rw [htz, mem_ball_zero_iff, hyn]
        linarith [hy.trans ht₀u] }
  -- the four bounds
  have hX := hX6 ν hreg f hgap w (by linarith [hew.trans heps]) (Complex.I * y) hyre.symm.le
  have hlw : l₈ ≤ w * (1 + δ) := by rw [hw_def]; exact aux_width (hel.trans heps) heps0.le hδ.le
  have hS8' := hS8 ν (fun x => f (1 - x)) hW (Complex.I * y) hyre (by rw [hyn]; linarith [hy.trans ht₀c])
    (by
      rw [norm_mul, hyn]
      calc |y| * ‖1 + (δ : ℂ)‖ ≤ |y| * (1 + δ) := by
            gcongr
            calc ‖1 + (δ : ℂ)‖ ≤ ‖(1 : ℂ)‖ + ‖(δ : ℂ)‖ := norm_add_le _ _
              _ = 1 + δ := by rw [norm_one, norm_real, Real.norm_eq_abs, abs_of_pos hδ]
        _ ≤ dom.renewalDiscount := aux_disc_le (hy.trans ht₀r) hrd hδ.le hδ1 (abs_nonneg y))
    (w * (1 + δ)) hlw
  set e₄ := max K₉ 0 * eps ^ p₉ * Real.exp (-c₉ * eps)
  have hpair : ∀ μ ∈ Icc (-δ) δ, ‖cepsActualPair ν f (w / 2) (((w⁻¹ : ℝ) : ℂ) ^ 2 * z) μ -
      cepsPhysicalPair dom ((ν : Measure ℝ).map fun x => 1 - x) w⁻¹ z μ‖ ≤ e₄ := by
    intro μ hμ
    rw [htz, hw2, hw_def]
    refine (hS6' eps (he9.trans heps) ν f hPf y hy0 (hy.trans ht₀9) μ hμ).trans ?_
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _)
      (by positivity)) (Real.exp_pos _).le
  have hmain := ceps_close_at_point dom hθ hD hW hreg hvlo hθ₀ hD₀ hgap hI hw hδ1 hδμ hdisc
    (e₁ := K₆ * w ^ 9 * Real.exp (-C₆ * w)) (e₂ := K₆ * w ^ 9 * Real.exp (-C₆ * w))
    (e₃ := C₈ * Real.exp (-c₈ * (w * (1 + δ)))) (e₄ := e₄)
    (by rw [htz]; exact hX.1) (by rw [htz]; exact hX.2) (by rw [htz]; exact hS8') hpair
  rw [htz, hw2] at hmain
  refine hmain.trans ?_
  -- numeric bound
  have hd2 : ‖1 - cepsLaplace ν (Complex.I * y)‖ ≤ 2 := by
    have := hgap.norm_cepsLaplace_le (t := Complex.I * y) hyre.symm.le
    calc ‖1 - cepsLaplace ν (Complex.I * y)‖ ≤ ‖(1 : ℂ)‖ + ‖cepsLaplace ν (Complex.I * y)‖ :=
          norm_sub_le _ _
      _ ≤ 2 := by rw [norm_one]; linarith
  have hp9 : eps ^ 9 ≤ eps ^ p := pow_le_pow_of_one_le heps1 (le_max_left _ _)
  have hpp : eps ^ p₉ ≤ eps ^ p := pow_le_pow_of_one_le heps1 (le_max_right _ _)
  have hp0 : 1 ≤ eps ^ p := one_le_pow₀ heps1
  have hc6 : c ≤ 2 * C₆ := min_le_left _ _
  have hc9 : c ≤ c₉ := (min_le_right _ _).trans (min_le_left _ _)
  have hc8 : c ≤ 2 * c₈ := (min_le_right _ _).trans (min_le_right _ _)
  have hx1 : Real.exp (-C₆ * w) ≤ Real.exp (-c * eps) := by
    rw [show -C₆ * w = -(2 * C₆) * eps by rw [hw_def]; ring]
    exact aux_exp_le hc6 heps0.le
  have hx2 : Real.exp (-c₉ * eps) ≤ Real.exp (-c * eps) := aux_exp_le hc9 heps0.le
  have hx3 : Real.exp (-c₈ * (w * (1 + δ))) ≤ Real.exp (-c * eps) := by
    refine (Real.exp_le_exp.mpr ?_).trans (aux_exp_le hc8 heps0.le)
    have h0 : 0 ≤ c₈ * eps * δ := by positivity
    rw [hw_def, show -c₈ * (2 * eps * (1 + δ)) = -(2 * c₈) * eps - 2 * (c₈ * eps * δ) by ring]
    linarith
  have hE := Real.exp_pos (-c * eps)
  have hK9 : 0 ≤ max K₉ 0 := le_max_right _ _
  have hw9 : w ^ 9 = 2 ^ 9 * eps ^ 9 := by rw [hw_def]; ring
  have he1b : K₆ * w ^ 9 * Real.exp (-C₆ * w) ≤ 2 ^ 9 * K₆ * eps ^ p * Real.exp (-c * eps) := by
    rw [hw9]
    calc K₆ * (2 ^ 9 * eps ^ 9) * Real.exp (-C₆ * w) ≤
        K₆ * (2 ^ 9 * eps ^ p) * Real.exp (-c * eps) := by gcongr
      _ = _ := by ring
  have he4b : 2 * δ * e₄ ≤ max K₉ 0 * eps ^ p * Real.exp (-c * eps) := by
    have h2δ : 2 * δ ≤ 1 := by linarith
    calc 2 * δ * e₄ ≤ 1 * e₄ := by gcongr
      _ = max K₉ 0 * eps ^ p₉ * Real.exp (-c₉ * eps) := one_mul _
      _ ≤ max K₉ 0 * eps ^ p * Real.exp (-c * eps) := by gcongr
  have he3b : C₈ * Real.exp (-c₈ * (w * (1 + δ))) ≤ C₈ * eps ^ p * Real.exp (-c * eps) := by
    calc C₈ * Real.exp (-c₈ * (w * (1 + δ))) ≤ C₈ * 1 * Real.exp (-c * eps) := by
          rw [mul_one]; gcongr
      _ ≤ C₈ * eps ^ p * Real.exp (-c * eps) := by gcongr
  have hsum : 0 ≤ K₆ * w ^ 9 * Real.exp (-C₆ * w) + K₆ * w ^ 9 * Real.exp (-C₆ * w) +
      2 * δ * e₄ := by positivity
  calc ‖1 - cepsLaplace ν (Complex.I * y)‖ * (K₆ * w ^ 9 * Real.exp (-C₆ * w) +
        K₆ * w ^ 9 * Real.exp (-C₆ * w) + 2 * δ * e₄) + C₈ * Real.exp (-c₈ * (w * (1 + δ)))
      ≤ 2 * (K₆ * w ^ 9 * Real.exp (-C₆ * w) + K₆ * w ^ 9 * Real.exp (-C₆ * w) +
        2 * δ * e₄) + C₈ * Real.exp (-c₈ * (w * (1 + δ))) := by gcongr
    _ ≤ 2 * (2 ^ 9 * K₆ * eps ^ p * Real.exp (-c * eps) +
        2 ^ 9 * K₆ * eps ^ p * Real.exp (-c * eps) +
        max K₉ 0 * eps ^ p * Real.exp (-c * eps)) + C₈ * eps ^ p * Real.exp (-c * eps) := by
        gcongr
    _ = K * eps ^ p * Real.exp (-c * eps) := by ring

/-- **S-9 on level `n`.** -/
theorem ceps_close_level (n : ℕ) (hS6 : CepsPairCloseLevel n) :
    ∃ K c t₀ eps₀ : ℝ, ∃ p : ℕ, 0 ≤ K ∧ 0 < c ∧ 0 < t₀ ∧ 1 ≤ eps₀ ∧
      ∀ eps : ℝ, eps₀ ≤ eps → ∀ ν : ProbabilityMeasure ℝ, CepsLevel n ν → ∀ y : ℝ, |y| ≤ t₀ →
        ‖cepsActualTransform eps ν (Complex.I * y) -
          cepsScaledTrueNormalExpression (cepsLevelDomain n) ((ν : Measure ℝ).map fun x => 1 - x)
            (2 * eps)⁻¹ (cepsLevelCutoff n) (Complex.I * ((4 * eps ^ 2 * y : ℝ) : ℂ))‖ ≤
          K * eps ^ p * Real.exp (-c * eps) := by
  by_cases hex : ∃ ν, CepsLevel n ν
  swap
  · exact ⟨0, 1, 1, 1, 0, le_rfl, one_pos, one_pos, le_rfl,
      fun eps _ ν hν => absurd ⟨ν, hν⟩ hex⟩
  obtain ⟨ν₀, hν₀⟩ := hex
  obtain ⟨f₀, -, -, -, hW₀, -, -⟩ := hν₀.stepLaw
  have hθ := cepsLevelRate_pos n
  have hD := cepsLevelStepD_pos n
  have hM := cepsLevelScale_pos n
  have hbase := trueDecayScaleBase_pos (cepsLevelDomain n) hW₀ hθ hD hM.le
  obtain ⟨hδR, hδμ8, hδB, hδ12⟩ := cepsLevelCutoff_le n
  have hδ : 0 < cepsLevelCutoff n := lt_min (lt_min ((cepsLevelDomain n).renewalMu_pos hD)
    (by have := (cepsLevelDomain n).μ₀_pos; positivity)) (lt_min (by positivity) (by norm_num))
  obtain ⟨K, c, t₀, eps₀, p, hK, hc, ht₀, he, h⟩ := ceps_close_uniform (cepsLevelDomain n) hθ hD hM
    hM hθ hθ (m := cepsLevelOrder) (η := cepsLevelRate n) (M := cepsLevelScale n)
    (by norm_num [cepsLevelOrder]) (cepsLevelDomain_two_c₀_le n) hbase hδ hδR hδμ8 hδB hδ12
    (CepsLevel n) (CepsLevelDensity n) (fun ν hν => hν.stepLaw) hS6
  exact ⟨K, c, t₀, eps₀, p, hK, hc, ht₀, he, h⟩

end PGM
