import PLAStochastic.Affine.Process.Hitting.SupremumExponentialLaw

/-!
# Brownian oscillation against every linear slope near zero

The one-sided exponential law and Brownian scaling first give unbounded
excursions over all time. Compactness moves the excursions past every finite
time. Time inversion then gives both signs in every neighborhood of zero,
on one common full-measure set for all real slopes.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace BrownianAffine

set_option backward.isDefEq.respectTransparency false

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

theorem measure_brownian_bounded_above_eq_zero (hB : IsBrownianReal B μ)
    {K : ℝ} (hK : 0 ≤ K) : μ {ω | ∀ t : ℝ≥0, B t ω ≤ K} = 0 := by
  have : IsProbabilityMeasure μ := hB.isGaussianProcess.isProbabilityMeasure
  let s := {ω | ∀ t : ℝ≥0, B t ω ≤ K}
  have hbound (n : ℕ) : μ.real s ≤ 1 - Real.exp (-2 * ((reciprocalMesh n : ℝ≥0) : ℝ) * K) := by
    let e := reciprocalMesh n
    have he : 0 < e := reciprocalMesh_pos n
    have hC := isBrownianReal_driftScaled hB he.ne'
    let A := {ω | ∃ t : ℝ≥0, (e : ℝ) * K < actualBrownianDrift (driftScaledBrownian B e) t ω}
    have hs : s ⊆ Aᶜ := by
      intro ω hω hA
      obtain ⟨u, hu⟩ := hA
      have hraw := hω (u / (e * e))
      have hmul := mul_le_mul_of_nonneg_left hraw e.property
      dsimp only [actualBrownianDrift, driftScaledBrownian] at hu
      have hu0 := u.property
      exact (not_lt_of_ge ((sub_le_self _ hu0).trans hmul)) hu
    calc
      μ.real s ≤ μ.real Aᶜ := measureReal_mono hs
      _ = 1 - Real.exp (-2 * ((reciprocalMesh n : ℝ≥0) : ℝ) * K) := by
        have hnull : NullMeasurableSet A μ := by
          simpa only [A] using! nullMeasurableSet_brownian_drift_crossing hC (mul_nonneg e.property hK)
        have htail : μ.real A = Real.exp (-2 * ((e : ℝ) * K)) := by
          simpa only [A] using! measureReal_brownian_drift_crossing hC (mul_nonneg e.property hK)
        rw [measureReal_compl₀ hnull, probReal_univ, htail]
        congr 2
        ring
  have he : Tendsto (fun n : ℕ => ((reciprocalMesh n : ℝ≥0) : ℝ)) atTop (𝓝 0) :=
    (NNReal.continuous_coe.tendsto 0).comp reciprocalMesh_tendsto_zero
  have hlim : Tendsto (fun n : ℕ => 1 - Real.exp (-2 * ((reciprocalMesh n : ℝ≥0) : ℝ) * K))
      atTop (𝓝 0) := by
    have hexp : Tendsto (fun n : ℕ => Real.exp (-2 * ((reciprocalMesh n : ℝ≥0) : ℝ) * K))
        atTop (𝓝 1) := by
      have ht : Tendsto (fun n : ℕ => -2 * ((reciprocalMesh n : ℝ≥0) : ℝ) * K) atTop (𝓝 0) := by
        simpa only [mul_zero, zero_mul] using ((he.const_mul (-2)).mul_const K)
      simpa only [Real.exp_zero, Function.comp_def] using! (Real.continuous_exp.tendsto 0).comp ht
    simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub hexp
  have hs : μ.real s ≤ 0 := ge_of_tendsto hlim (Eventually.of_forall hbound)
  exact (measureReal_eq_zero_iff (measure_ne_top μ s)).mp (le_antisymm hs measureReal_nonneg)

/-- Brownian paths exceed every real level on one common full-measure set. -/
theorem brownian_unbounded_above_ae (hB : IsBrownianReal B μ) :
    ∀ᵐ ω ∂μ, ∀ M : ℝ, ∃ t : ℝ≥0, M < B t ω := by
  have hn (n : ℕ) : ∀ᵐ ω ∂μ, ∃ t : ℝ≥0, (n : ℝ) < B t ω := by
    apply ae_iff.mpr
    simpa only [not_exists, not_lt] using
      measure_brownian_bounded_above_eq_zero hB (Nat.cast_nonneg n)
  filter_upwards [ae_all_iff.mpr hn] with ω hω
  intro M
  obtain ⟨n, hn⟩ := exists_nat_ge M
  obtain ⟨t, ht⟩ := hω n
  exact ⟨t, hn.trans_lt ht⟩

theorem brownian_unbounded_below_ae (hB : IsBrownianReal B μ) :
    ∀ᵐ ω ∂μ, ∀ M : ℝ, ∃ t : ℝ≥0, B t ω < M := by
  filter_upwards [brownian_unbounded_above_ae hB.neg] with ω hω
  intro M
  obtain ⟨t, ht⟩ := hω (-M)
  simp only [Pi.neg_apply] at ht
  exact ⟨t, by linarith⟩

omit [MeasurableSpace Ω] in
theorem unbounded_above_after_every_time {X : ℝ≥0 → ℝ} (hc : Continuous X)
    (hX : ∀ M : ℝ, ∃ t : ℝ≥0, M < X t) :
    ∀ M : ℝ, ∀ T : ℝ≥0, ∃ t : ℝ≥0, T < t ∧ M < X t := by
  intro M T
  obtain ⟨L, hL⟩ := isCompact_Icc.bddAbove_image (K := Icc (0 : ℝ≥0) T) hc.continuousOn
  obtain ⟨t, ht⟩ := hX (max M L)
  refine ⟨t, ?_, (le_max_left _ _).trans_lt ht⟩
  by_contra h
  have hb := hL (mem_image_of_mem X ⟨bot_le, le_of_not_gt h⟩)
  exact (not_le_of_gt ((le_max_right _ _).trans_lt ht)) hb

theorem brownian_unbounded_after_every_time_ae (hB : IsBrownianReal B μ) :
    ∀ᵐ ω ∂μ, ∀ M : ℝ, ∀ T : ℝ≥0,
      (∃ t : ℝ≥0, T < t ∧ M < B t ω) ∧ (∃ t : ℝ≥0, T < t ∧ B t ω < M) := by
  filter_upwards [hB.cont, brownian_unbounded_above_ae hB, brownian_unbounded_above_ae hB.neg]
    with ω hc hp hn
  intro M T
  refine ⟨unbounded_above_after_every_time hc hp M T, ?_⟩
  obtain ⟨t, ht, hv⟩ := unbounded_above_after_every_time hc.neg hn (-M) T
  simp only [Pi.neg_apply] at hv
  exact ⟨t, ht, by linarith⟩

/-- Every neighborhood of zero contains excursions on both sides of every
line through zero, simultaneously for all real slopes. -/
theorem brownian_linear_oscillation_zero_ae (hB : IsBrownianReal B μ) :
    ∀ᵐ ω ∂μ, ∀ a : ℝ, ∀ δ : ℝ≥0, 0 < δ →
      (∃ t : ℝ≥0, 0 < t ∧ t < δ ∧ 0 < B t ω - a * (t : ℝ)) ∧
      (∃ t : ℝ≥0, 0 < t ∧ t < δ ∧ B t ω - a * (t : ℝ) < 0) := by
  filter_upwards [brownian_unbounded_after_every_time_ae (isBrownianReal_timeInversion hB)]
    with ω hω
  intro a δ hδ
  obtain ⟨⟨s, hs, hup⟩, ⟨r, hr, hlo⟩⟩ := hω a (1 / δ)
  have hs0 : 0 < s := (by positivity : (0 : ℝ≥0) < 1 / δ).trans hs
  have hr0 : 0 < r := (by positivity : (0 : ℝ≥0) < 1 / δ).trans hr
  have hsR : 0 < (s : ℝ) := by exact_mod_cast hs0
  have hrR : 0 < (r : ℝ) := by exact_mod_cast hr0
  constructor
  · refine ⟨1 / s, by positivity, (one_div_lt hs0 hδ).mpr hs, ?_⟩
    have hh : a / (s : ℝ) < B (1 / s) ω :=
      (div_lt_iff₀ hsR).mpr (by simpa only [timeInvertedProcess, mul_comm] using hup)
    apply sub_pos.mpr
    simpa only [NNReal.coe_div, NNReal.coe_one, div_eq_mul_inv, one_mul, NNReal.coe_inv] using hh
  · refine ⟨1 / r, by positivity, (one_div_lt hr0 hδ).mpr hr, ?_⟩
    have hh : B (1 / r) ω < a / (r : ℝ) :=
      (lt_div_iff₀ hrR).mpr (by simpa only [timeInvertedProcess, mul_comm] using hlo)
    apply sub_neg.mpr
    simpa only [NNReal.coe_div, NNReal.coe_one, div_eq_mul_inv, one_mul, NNReal.coe_inv] using hh

end BrownianAffine
