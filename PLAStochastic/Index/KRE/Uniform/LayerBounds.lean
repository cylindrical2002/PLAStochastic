import PLAStochastic.Index.GRE.PreciseHeightDefs
import PLAStochastic.Index.KRE.Uniform.LandauChaining
import PLAStochastic.Index.KRE.Uniform.CurvatureLowerCount

/-!
# The per-layer bounds of `thm:uniform` off the Model K bad event

`uniformLayerFacts_of_good`: for fixed class parameters `c` there are constants such that,
along every sequence `N → ∞`, `ε → ∞`, eventually and for every `ω ∉ kreBad` (the existing
bad event of `PLAStochastic.Index.KRE.GoodEvent` at the levels `tRE N`, `jK N`), every `δ` and every `f ∈ 𝔉_δ`,
the Rényi keys `renyiKeys f N ω` satisfy `UniformLayerFacts`.  The constants are

* `cN = 1 / 2056`, `CN = 8 / aRE` (`unif_noise`);
* `Cu = 1638400 + 16 √κ`, `C0 = 32 κ + 1` with `κ = 40 f₊ L / f₋³` (`unif_curvUp`);
* `c₁ = V / √(3456 L)`, `c₂ = (V⁴ / (152882380800 L²))^{1/3}`, `c₃ = f₋ V / (5760 L)` and
  `K_L = 307200 L / f₋² + 164 / (f₋ a) + 164 / (f₋ (1 - b))` (`unif_curvLow`).

The eventual threshold is that of the side conditions `UnifCond` (`eventually_unifCond`); it
depends only on `c` and the sequence.  The hypothesis `log ε / log N → 0` is not needed.
-/

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory Finset Filter Topology

/-- The side conditions `UnifCond` hold eventually along `N → ∞`, `ε → ∞`. -/
theorem eventually_unifCond (c : DensityClassParams) {N : ℕ → ℕ} {ε : ℕ → ℝ}
    (hN : Tendsto (fun k => (N k : ℝ)) atTop atTop) (hε : Tendsto ε atTop atTop) :
    ∀ᶠ k in atTop, UnifCond c (N k) (ε k) := by
  have hL : Tendsto (fun k => Real.log (N k)) atTop atTop := Real.tendsto_log_atTop.comp hN
  have hq : (0 : ℝ) < 1 / 4 := by norm_num
  filter_upwards [hN.eventually_ge_atTop 160000, hε.eventually_ge_atTop 46,
    hL.eventually_ge_atTop (max 1 (16 * unifKappa c)),
    hL.eventually_ge_atTop (9 * 10 ^ 8 * unifKappa c * CjK ^ 2),
    hL.eventually_ge_atTop (64 / (cRE * aRE) + 32 / aRE),
    hN.eventually (eventually_mul_log_pow_le_rpow (8 * unifKappa c) 1 one_pos),
    hN.eventually (eventually_mul_log_pow_le_rpow (2 * 640 ^ 3) 7 one_pos),
    hN.eventually (eventually_mul_log_pow_le_rpow (3276800 ^ 3) 7 hq),
    hN.eventually (eventually_mul_log_pow_le_rpow (1024 ^ 3 * unifKappa c ^ 3) 4 hq),
    hN.eventually (eventually_mul_log_pow_le_rpow (64 ^ 3 * unifKappa c ^ 3) 4 hq),
    hN.eventually (eventually_mul_log_pow_le_rpow 82 1 one_pos)]
    with k h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11
  rw [Real.rpow_one, pow_one] at h6 h11
  rw [Real.rpow_one] at h7
  have hY1 : 1 ≤ Real.log (N k) := le_trans (le_max_left _ _) h3
  have hYκ : 16 * unifKappa c ≤ Real.log (N k) := le_trans (le_max_right _ _) h3
  have hY3 : Real.log (N k) ≤ Real.log (N k) ^ 3 := le_self_pow₀ hY1 (by norm_num)
  exact
    { n_ge := by exact_mod_cast h1
      eps_ge := h2
      noise1 := hYκ.trans hY3
      noise2 := h4
      noise3 := h5
      lam := h6
      band0 := h7
      band1 := h8
      band2 := h9
      band3 := h10
      low := by linarith }

/-- **The per-layer bounds of `thm:uniform`** hold off the bad event, uniformly over the
density classes `𝔉_δ`. -/
theorem uniformLayerFacts_of_good (c : DensityClassParams) :
    ∃ cN CN Cu C0 c1 c2 c3 KL : ℝ, 0 < cN ∧ 0 < CN ∧ 0 < Cu ∧ 0 ≤ C0 ∧ 0 < c1 ∧ 0 < c2 ∧
      0 < c3 ∧ 0 < KL ∧
      ∀ {N : ℕ → ℕ} {ε : ℕ → ℝ},
        Tendsto (fun k => (N k : ℝ)) atTop atTop → Tendsto ε atTop atTop →
        Tendsto (fun k => Real.log (ε k) / Real.log (N k)) atTop (𝓝 0) →
        ∀ᶠ k in atTop, ∀ ω : ℕ → ℝ,
          ω ∉ kreBad expCoord (N k) (ε k) (tRE (N k)) (jK (N k)) →
          ∀ δ f, c.Mem δ f →
            UniformLayerFacts (renyiKeys f (N k) ω) (N k) (ε k) δ cN CN Cu C0 c1 c2 c3 KL := by
  have hκ := unifKappa_pos c
  have haRE := aRE_pos
  refine ⟨1 / 2056, 8 / aRE, 1638400 + 16 * Real.sqrt (unifKappa c), 32 * unifKappa c + 1,
    unifC1 c, unifC2 c, unifC3 c, unifKL c, by norm_num, by positivity, by positivity,
    by positivity, unifC1_pos c, unifC2_pos c, unifC3_pos c, unifKL_pos c, ?_⟩
  intro N ε hN hε _
  filter_upwards [eventually_unifCond c hN hε] with k hk
  intro ω hω δ f hf
  exact
    { noise := fun ℓ _ hN1 hN2 => unif_noise hk hω hf ℓ hN1 hN2
      band := fun ℓ _ hB hB2 => unif_band hk hω hf ℓ hB hB2
      curvUp := fun ℓ h2 hC => unif_curvUp hk hω hf ℓ h2 hC
      curvLow := fun hδ ℓ h2 hΔ hKL => unif_curvLow hk hω hf hδ ℓ h2 hΔ hKL }

end

end PGM
