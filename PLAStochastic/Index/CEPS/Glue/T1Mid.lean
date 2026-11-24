import PLAStochastic.Index.CEPS.Glue.Moments

/-!
# WP11a: S-11, mid band (T1-mid) from the normal transform

On `U ≤ |u| ≤ ε^{3/2}` the frequency `t = -iu/C` satisfies `|t| ≤ 1/(s_lo √ε) ≤ t₀`, so S-9 gives
`φ_ν(u) = Ĝ(b, iy) + O(εᵖ e^{-cε})` with `y = -4u/(C/ε²)`, `|y| ∈ [4|u|/s_hi, 4|u|/s_lo]`.
C-11 then gives `CepsT1Mid` with `δ = 1/2` (`cepsT1Mid_of_normal`).
-/

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set

/-- **T1-mid from the normal transform.** -/
theorem cepsT1Mid_of_normal {Gn : ℝ → ProbabilityMeasure ℝ → ℂ → ℂ}
    (hclose : CepsNormalClose Gn) (hmid : CepsNormalMid Gn) : CepsT1Mid := by
  obtain ⟨m0, h0⟩ := hclose
  obtain ⟨m1, h1⟩ := hmid
  refine ⟨1 / 2, by norm_num, by norm_num, max m0 m1,
    fun D θ vlo vhi η hD hθ hvlo hv hη => ?_⟩
  obtain ⟨r0, hr0, K0, c0, t0, e0, hc0, ht0, p0, H0⟩ := h0 D θ vlo vhi η hD hθ hvlo hv hη
  obtain ⟨r1, hr1, K1, c1, U1, R, e1, hc1, hR, d1, H1⟩ := h1 D θ vlo vhi η hD hθ hvlo hv hη
  obtain ⟨em, s_lo, s_hi, B₂, hem, hslo, -, Hm⟩ := ceps_class_moments hD hθ hvlo hv
  set S : ℝ := max s_hi 1 with hS
  have hSpos : 0 < S := lt_of_lt_of_le one_pos (le_max_right _ _)
  set c' : ℝ := min c0 (c1 * Real.sqrt (4 / S)) with hc'
  have hc'pos : 0 < c' := lt_min hc0 (mul_pos hc1 (Real.sqrt_pos.2 (by positivity)))
  set κ : ℝ := 1 + 4 / s_lo with hκ
  refine ⟨min r0 r1, lt_min hr0 hr1, c', U1 * S / 4, |K1| * κ ^ d1 + |K0|,
    max (max e0 e1) (max em (max ((4 / (s_lo * R)) ^ 2) ((1 / (s_lo * t0)) ^ 2))), hc'pos,
    max d1 p0, fun eps heps ν hν u hU hu => ?_⟩
  have he0 : e0 ≤ eps := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) heps
  have he1 : e1 ≤ eps := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) heps
  have hemm : em ≤ eps := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) heps
  have hRR : (4 / (s_lo * R)) ^ 2 ≤ eps := le_trans (le_trans (le_trans (le_max_left _ _)
    (le_max_right _ _)) (le_max_right _ _)) heps
  have htt : (1 / (s_lo * t0)) ^ 2 ≤ eps := le_trans (le_trans (le_trans (le_max_right _ _)
    (le_max_right _ _)) (le_max_right _ _)) heps
  have heps1 : 1 ≤ eps := hem.trans hemm
  have hepspos : 0 < eps := lt_of_lt_of_le one_pos heps1
  have hν0 := hν.mono (le_max_left _ _) (min_le_left _ _)
  have hν1 := hν.mono (le_max_right _ _) (min_le_right _ _)
  obtain ⟨hlo, hhi, -⟩ := Hm eps hemm ν hν.reg
  set C := lawC eps ν with hC
  have he2 : 0 < eps ^ 2 := by positivity
  set s : ℝ := C / eps ^ 2 with hs
  have hspos : 0 < s := lt_of_lt_of_le hslo hlo
  have hsS : s ≤ S := hhi.trans (le_max_left _ _)
  have hCpos : 0 < C := by
    have := mul_pos hspos he2
    rwa [hs, div_mul_cancel₀ _ he2.ne'] at this
  have hC' : s_lo * eps ^ 2 ≤ C := by rwa [hs, le_div_iff₀ he2] at hlo
  -- the band in terms of `q = √ε`
  set q : ℝ := Real.sqrt eps with hq
  have hqpos : 0 < q := Real.sqrt_pos.2 hepspos
  have hq2 : q ^ 2 = eps := Real.sq_sqrt hepspos.le
  have hu' : |u| ≤ eps * q := by
    have e : eps ^ ((1 : ℝ) + 1 / 2) = eps * q := by
      rw [Real.rpow_add hepspos, Real.rpow_one, hq, Real.sqrt_eq_rpow]
    rw [← e]
    exact hu
  have hqR : 4 / (s_lo * R) ≤ q := Real.le_sqrt_of_sq_le hRR
  have hqt : 1 / (s_lo * t0) ≤ q := Real.le_sqrt_of_sq_le htt
  -- the actual/normal step
  set y' : ℝ := -(u / C) with hy'
  have hy't : |y'| ≤ t0 := by
    rw [hy', abs_neg, abs_div, abs_of_pos hCpos, div_le_iff₀ hCpos]
    have h1 : 1 ≤ q * (s_lo * t0) := by rwa [div_le_iff₀ (mul_pos hslo ht0)] at hqt
    calc |u| ≤ eps * q := hu'
      _ ≤ eps * q * (q * (s_lo * t0)) := le_mul_of_one_le_right (by positivity) h1
      _ = t0 * (s_lo * eps * q ^ 2) := by ring
      _ = t0 * (s_lo * eps ^ 2) := by rw [hq2]; ring
      _ ≤ t0 * C := mul_le_mul_of_nonneg_left hC' ht0.le
  set y : ℝ := -4 * u / s with hy
  have hyy : 4 * eps ^ 2 * y' = y := by
    rw [hy', hy, hs]
    field_simp
  have hyabs : |y| = 4 * |u| / s := by
    rw [hy, abs_div, abs_of_pos hspos, abs_mul, abs_neg, abs_of_pos (by norm_num : (0 : ℝ) < 4)]
  have hyU : U1 ≤ |y| := by
    rw [hyabs]
    have h1 : 4 * |u| / S ≤ 4 * |u| / s :=
      div_le_div_of_nonneg_left (by positivity) hspos hsS
    have h2 : U1 ≤ 4 * |u| / S := by
      rw [le_div_iff₀ hSpos]
      linarith
    linarith
  have hyR : |y| ≤ R * eps ^ 2 := by
    rw [hyabs, div_le_iff₀ hspos]
    have h4 : 4 ≤ q * (s_lo * R) := by rwa [div_le_iff₀ (mul_pos hslo hR)] at hqR
    calc 4 * |u| ≤ 4 * (eps * q) := by linarith
      _ ≤ q * (s_lo * R) * (eps * q) := mul_le_mul_of_nonneg_right h4 (by positivity)
      _ = R * eps * (s_lo * q ^ 2) := by ring
      _ = R * eps * (s_lo * eps) := by rw [hq2]
      _ ≤ R * eps * (s * eps) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hlo hepspos.le) (by positivity)
      _ = R * eps ^ 2 * s := by ring
  have hact : ‖cepsOutChar eps ν u - Gn eps ν (Complex.I * y)‖ ≤
      |K0| * eps ^ max d1 p0 * Real.exp (-c' * eps) := by
    rw [cepsOutChar_eq_actual, ← hyy]
    refine (H0 eps he0 ν hν0 y' hy't).trans ?_
    have hp : eps ^ p0 ≤ eps ^ max d1 p0 := pow_le_pow_right₀ heps1 (le_max_right _ _)
    have hexp : Real.exp (-c0 * eps) ≤ Real.exp (-c' * eps) :=
      Real.exp_le_exp.mpr (by
        have := mul_le_mul_of_nonneg_right (min_le_left c0 (c1 * Real.sqrt (4 / S))) hepspos.le
        linarith)
    calc K0 * eps ^ p0 * Real.exp (-c0 * eps) ≤ |K0| * eps ^ p0 * Real.exp (-c0 * eps) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self K0)
            (by positivity)) (by positivity)
      _ ≤ |K0| * eps ^ max d1 p0 * Real.exp (-c' * eps) := by gcongr
  -- the mid-band step
  have hmid' : ‖Gn eps ν (Complex.I * y)‖ ≤
      |K1| * κ ^ d1 * (1 + |u|) ^ max d1 p0 * Real.exp (-c' * Real.sqrt |u|) := by
    refine (H1 eps he1 ν hν1 y hyU hyR).trans ?_
    have hb1 : 1 + |y| ≤ κ * (1 + |u|) := by
      rw [hyabs, hκ]
      have h1 : 4 * |u| / s ≤ 4 / s_lo * |u| := by
        rw [div_mul_eq_mul_div, div_le_div_iff₀ hspos hslo]
        have : 4 * |u| * s_lo ≤ 4 * |u| * s :=
          mul_le_mul_of_nonneg_left hlo (by positivity)
        linarith
      have h2 : 0 ≤ 4 / s_lo := by positivity
      have e : (1 + 4 / s_lo) * (1 + |u|) = 1 + |u| + 4 / s_lo + 4 / s_lo * |u| := by ring
      linarith [abs_nonneg u]
    have hsq : Real.sqrt (4 / S) * Real.sqrt |u| ≤ Real.sqrt |y| := by
      rw [← Real.sqrt_mul (by positivity)]
      refine Real.sqrt_le_sqrt ?_
      rw [hyabs, div_mul_eq_mul_div, div_le_div_iff₀ hSpos hspos]
      have : 4 * |u| * s ≤ 4 * |u| * S := mul_le_mul_of_nonneg_left hsS (by positivity)
      linarith
    have hexp : Real.exp (-c1 * Real.sqrt |y|) ≤ Real.exp (-c' * Real.sqrt |u|) := by
      rw [Real.exp_le_exp]
      have hcc : c' * Real.sqrt |u| ≤ c1 * Real.sqrt (4 / S) * Real.sqrt |u| :=
        mul_le_mul_of_nonneg_right (min_le_right _ _) (Real.sqrt_nonneg _)
      have : c1 * (Real.sqrt (4 / S) * Real.sqrt |u|) ≤ c1 * Real.sqrt |y| :=
        mul_le_mul_of_nonneg_left hsq hc1.le
      linarith
    have hpow : (1 + |y|) ^ d1 ≤ κ ^ d1 * (1 + |u|) ^ max d1 p0 := by
      calc (1 + |y|) ^ d1 ≤ (κ * (1 + |u|)) ^ d1 :=
            pow_le_pow_left₀ (by positivity) hb1 d1
        _ = κ ^ d1 * (1 + |u|) ^ d1 := mul_pow _ _ _
        _ ≤ κ ^ d1 * (1 + |u|) ^ max d1 p0 :=
            mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (by linarith [abs_nonneg u])
              (le_max_left _ _)) (by positivity)
    calc K1 * (1 + |y|) ^ d1 * Real.exp (-c1 * Real.sqrt |y|)
        ≤ |K1| * (κ ^ d1 * (1 + |u|) ^ max d1 p0) * Real.exp (-c' * Real.sqrt |u|) := by
          refine mul_le_mul (mul_le_mul (le_abs_self K1) hpow (by positivity) (abs_nonneg _))
            hexp (by positivity) (by positivity)
      _ = |K1| * κ ^ d1 * (1 + |u|) ^ max d1 p0 * Real.exp (-c' * Real.sqrt |u|) := by ring
  calc ‖cepsOutChar eps ν u‖
      ≤ ‖Gn eps ν (Complex.I * y)‖ + ‖cepsOutChar eps ν u - Gn eps ν (Complex.I * y)‖ := by
        have := norm_add_le (Gn eps ν (Complex.I * y))
          (cepsOutChar eps ν u - Gn eps ν (Complex.I * y))
        rwa [add_sub_cancel] at this
    _ ≤ |K1| * κ ^ d1 * (1 + |u|) ^ max d1 p0 * Real.exp (-c' * Real.sqrt |u|) +
          |K0| * eps ^ max d1 p0 * Real.exp (-c' * eps) := add_le_add hmid' hact
    _ ≤ (|K1| * κ ^ d1 + |K0|) * (1 + |u|) ^ max d1 p0 * Real.exp (-c' * Real.sqrt |u|) +
          (|K1| * κ ^ d1 + |K0|) * eps ^ max d1 p0 * Real.exp (-c' * eps) := by
        have hA : 0 ≤ (1 + |u|) ^ max d1 p0 * Real.exp (-c' * Real.sqrt |u|) := by positivity
        have hB : 0 ≤ eps ^ max d1 p0 * Real.exp (-c' * eps) := by positivity
        have h1 : 0 ≤ |K0| := abs_nonneg _
        have h2 : 0 ≤ |K1| * κ ^ d1 := by positivity
        have h3 := mul_nonneg h1 hA
        have h4 := mul_nonneg h2 hB
        linarith

end

end PGM
