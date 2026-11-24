import PLAStochastic.Swing.Transient.Brackets.ZeroRow

/-! # The boundary order `T(a, ·) ≤ T(0, ·)`

**Step 1 (CDF formula).**  For every drift `b` and level `r`,
`𝖡(b)(-∞, r] = 𝔼(H_b - (b - r)₊)₊ / 𝔼H_b` (layer cake applied to the equilibrium density
`P(H_b > o)/𝔼H_b`).

**Step 2 (boundary CDF comparison).**  For `a > 0` and `0 < a_k ≤ a`, the existing
monotonicity gives `𝖡(a)(-∞, r] ≤ 𝖡(a_k)(-∞, r]`.  Along `a_k ↓ 0` with `a_k ≤ 1/2`,
`𝔼H_0 ≤ 𝔼H_{a_k}` (Fatou), the shift `(a_k - r)₊ ≥ (-r)₊`, and `𝔼|H_{a_k} - H_0| → 0`, so
`𝖡(a_k)(-∞, r] ≤ (𝔼(H_0 - (-r)₊)₊ + 𝔼|H_{a_k} - H_0|)/𝔼H_0 → 𝖡(0)(-∞, r]`.
Hence `𝖡(a)(-∞, r] ≤ 𝖡(0)(-∞, r]`: `𝖡(0) ≤_st 𝖡(a)`.

**Step 3.**  The slope stage `𝖠` maps a test function monotone on `(0, ∞)` to a globally
Lipschitz antitone function of the margin, so `∫ g dT(a) ≤ ∫ g dT(0)` for every
`a > 0` and every Lipschitz test function `g` monotone on `(0, ∞)`.
-/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
namespace SwingRepair
open SlopeEvaluation Fluctuation
set_option backward.isDefEq.respectTransparency false

variable {Ω : Type*} [MeasurableSpace Ω] {X : ℕ → Ω → ℝ} {μ : Measure Ω}

/-! ### The CDF formula -/

/-- Layer cake with a shift: `∫_{[s,∞)} P(Y > o) do = 𝔼(Y - s)₊`. -/
theorem lintegral_Ici_measure_lt_eq_posPart {Y : Ω → ℝ} (hY : Measurable Y) (s : ℝ) :
    ∫⁻ o in Ici s, μ {ω | o < Y ω} = ∫⁻ ω, ENNReal.ofReal (Y ω - s) ∂μ := by
  have hlc := lintegral_eq_lintegral_meas_lt μ (f := fun ω => max (Y ω - s) 0)
    (ae_of_all _ fun ω => le_max_right _ _) ((hY.sub_const s).max measurable_const).aemeasurable
  simp_rw [ofReal_max_zero] at hlc
  rw [hlc]
  set F : ℝ → ℝ≥0∞ := fun o => μ {ω | o < Y ω} with hF
  set G : ℝ → ℝ≥0∞ := fun t => μ {ω | t < max (Y ω - s) 0} with hG
  have hIci : ∫⁻ o in Ici s, F o = ∫⁻ o in Ioi s, F o :=
    (setLIntegral_congr (Ioi_ae_eq_Ici' (measure_singleton s))).symm
  rw [hIci, ← lintegral_indicator measurableSet_Ioi, ← lintegral_indicator measurableSet_Ioi]
  calc ∫⁻ o, (Ioi s).indicator F o
      = ∫⁻ u, (Ioi s).indicator F (u + s) :=
        (lintegral_add_right_eq_self (fun o => (Ioi s).indicator F o) s).symm
    _ = ∫⁻ u, (Ioi 0).indicator G u := by
        refine lintegral_congr fun u => ?_
        by_cases hu : 0 < u
        · rw [indicator_of_mem (show u + s ∈ Ioi s by simp only [mem_Ioi]; linarith),
            indicator_of_mem (show u ∈ Ioi 0 from hu)]
          simp only [hF, hG]
          congr 1
          ext ω
          simp only [mem_ofPred_eq, lt_max_iff]
          constructor
          · intro h; left; linarith
          · rintro (h | h)
            · linarith
            · exact absurd (hu.trans h) (lt_irrefl _)
        · rw [indicator_of_notMem (show u ∉ Ioi 0 from hu),
            indicator_of_notMem (show u + s ∉ Ioi s by
              simp only [mem_Ioi]; intro h; exact hu (by linarith))]

/-- **The CDF of `𝖡(b)` for every drift**: `𝖡(b)(-∞, r] = 𝔼(H_b - (b - r)₊)₊ / 𝔼H_b`. -/
theorem swingOvershootMeasure_Iic_eq (hX : ∀ n, Measurable (X n)) (b r : ℝ) :
    swingOvershootMeasure X μ b (Iic r) =
      (∫⁻ ω, ENNReal.ofReal (gaussianAscendingLadderHeight X b ω - max (b - r) 0) ∂μ) /
        ladderMeanLIntegral X μ b := by
  have hH := gaussianAscendingLadderHeight_measurable hX b
  rw [swingOvershootMeasure_apply _ _ _ measurableSet_Iic]
  have hpre : ((fun o : ℝ => b - o) ⁻¹' Iic r) ∩ Ici 0 = Ici (max (b - r) 0) := by
    ext o
    simp only [mem_inter_iff, mem_preimage, mem_Iic, mem_Ici, max_le_iff]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨by linarith, h2⟩
    · rintro ⟨h1, h2⟩; exact ⟨by linarith, h2⟩
  rw [hpre]
  have hdens : ∀ o, swingEquilibriumDensity X μ b o =
      (ladderMeanLIntegral X μ b)⁻¹ * μ {ω | o < gaussianAscendingLadderHeight X b ω} := by
    intro o
    rw [swingEquilibriumDensity, ladderMeanENN_gaussianAscendingLadderLaw hX,
      ENNReal.div_eq_inv_mul,
      gaussianAscendingLadderLaw, Measure.map_apply hH measurableSet_Ioi]
    rfl
  simp_rw [hdens]
  have hmeas : Measurable fun o : ℝ => μ {ω | o < gaussianAscendingLadderHeight X b ω} :=
    Antitone.measurable fun o o' h => measure_mono fun ω hω => lt_of_le_of_lt h hω
  rw [lintegral_const_mul _ hmeas, lintegral_Ici_measure_lt_eq_posPart hH, ENNReal.div_eq_inv_mul]

/-! ### The boundary CDF comparison -/

/-- `𝔼(H_x - c')₊ ≤ 𝔼(H_y - c)₊ + 𝔼|H_x - H_y|` for `c ≤ c'`. -/
theorem ladderHeight_lintegral_ofReal_sub_le_add (hX : ∀ n, Measurable (X n)) (x y : ℝ) {c c' : ℝ}
    (hcc : c ≤ c') :
    (∫⁻ ω, ENNReal.ofReal (gaussianAscendingLadderHeight X x ω - c') ∂μ) ≤
      (∫⁻ ω, ENNReal.ofReal (gaussianAscendingLadderHeight X y ω - c) ∂μ) +
        ∫⁻ ω, ENNReal.ofReal
          |gaussianAscendingLadderHeight X x ω - gaussianAscendingLadderHeight X y ω| ∂μ := by
  have hmy : Measurable fun ω => ENNReal.ofReal (gaussianAscendingLadderHeight X y ω - c) :=
    ENNReal.measurable_ofReal.comp ((gaussianAscendingLadderHeight_measurable hX y).sub_const c)
  rw [← lintegral_add_left hmy]
  refine lintegral_mono fun ω => ?_
  refine le_trans ?_ ENNReal.ofReal_add_le
  refine ENNReal.ofReal_le_ofReal ?_
  have := le_abs_self (gaussianAscendingLadderHeight X x ω - gaussianAscendingLadderHeight X y ω)
  linarith

/-- **Boundary CDF comparison**: `𝖡(a)(-∞, r] ≤ 𝖡(0)(-∞, r]` for every `a > 0`. -/
theorem swingOvershootMeasure_Iic_le_zero (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) {a : ℝ} (ha : 0 < a) (r : ℝ) :
    swingOvershootMeasure X μ a (Iic r) ≤ swingOvershootMeasure X μ 0 (Iic r) := by
  set s : ℕ → ℝ := fun k => (1 / 2) * (1 / ((k : ℝ) + 1)) with hs
  have hspos : ∀ k, 0 < s k := fun k => by simp only [hs]; positivity
  have hshalf : ∀ k, s k ≤ 1 / 2 := by
    intro k
    simp only [hs]
    have h1 : 1 / ((k : ℝ) + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]
      have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
      linarith
    linarith
  have hslim : Tendsto s atTop (𝓝 0) := by
    have := tendsto_one_div_add_atTop_nhds_zero_nat.const_mul (1 / 2 : ℝ)
    simpa [hs] using this
  set c : ℝ := max (0 - r) 0 with hc
  set N₀ : ℝ≥0∞ := ∫⁻ ω, ENNReal.ofReal (gaussianAscendingLadderHeight X 0 ω - c) ∂μ with hN₀
  set m₀ : ℝ≥0∞ := ladderMeanLIntegral X μ 0 with hm₀
  set E : ℕ → ℝ≥0∞ := fun k => ∫⁻ ω, ENNReal.ofReal
    |gaussianAscendingLadderHeight X (s k) ω - gaussianAscendingLadderHeight X 0 ω| ∂μ with hE
  have hE0 : Tendsto E atTop (𝓝 0) :=
    tendsto_lintegral_abs_ladderHeight_sub_zero hX hi hG hshalf hslim
  have hm₀0 : m₀ ≠ 0 := ladderMeanLIntegral_zero_ne_zero hX hi hG
  have hlim : Tendsto (fun k => (N₀ + E k) / m₀) atTop (𝓝 ((N₀ + 0) / m₀)) :=
    ENNReal.Tendsto.div_const (tendsto_const_nhds.add hE0) (Or.inr hm₀0)
  have hbound : ∀ᶠ k in atTop, swingOvershootMeasure X μ a (Iic r) ≤ (N₀ + E k) / m₀ := by
    filter_upwards [hslim.eventually (gt_mem_nhds ha)] with k hk
    calc swingOvershootMeasure X μ a (Iic r)
        ≤ swingOvershootMeasure X μ (s k) (Iic r) :=
          swingOvershootMeasure_Iic_antitone hX hi hG (hspos k) hk.le r
      _ = (∫⁻ ω, ENNReal.ofReal (gaussianAscendingLadderHeight X (s k) ω - max (s k - r) 0) ∂μ) /
            ladderMeanLIntegral X μ (s k) := swingOvershootMeasure_Iic_eq hX (s k) r
      _ ≤ (∫⁻ ω, ENNReal.ofReal (gaussianAscendingLadderHeight X (s k) ω - max (s k - r) 0) ∂μ) /
            m₀ := ENNReal.div_le_div_left (ladderMeanLIntegral_zero_le hX hi hG (hspos k)) _
      _ ≤ (N₀ + E k) / m₀ := by
          refine ENNReal.div_le_div_right ?_ _
          exact ladderHeight_lintegral_ofReal_sub_le_add hX (s k) 0
            (max_le_max (by linarith [hspos k]) le_rfl)
  have h := ge_of_tendsto hlim hbound
  rwa [add_zero, hN₀, hm₀, hc, ← swingOvershootMeasure_Iic_eq hX 0 r] at h

/-- **`𝖡(0) ≤_st 𝖡(a)`** for every `a > 0`. -/
theorem swingOvershootMeasure_zero_stochasticallyLE (hX : ∀ n, Measurable (X n))
    (hi : iIndepFun X μ) (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) {a : ℝ} (ha : 0 < a) :
    StochasticallyLE (swingOvershootMeasure X μ 0) (swingOvershootMeasure X μ a) := by
  have hB0 := swingOvershootMeasure_zero_isProbability hX hi hG
  have hBa := swingOvershootMeasure_isProbability hX hi hG ha
  have hIoi : ∀ r, swingOvershootMeasure X μ 0 (Ioi r) ≤ swingOvershootMeasure X μ a (Ioi r) := by
    intro r
    rw [← compl_Iic, prob_compl_eq_one_sub measurableSet_Iic,
      prob_compl_eq_one_sub measurableSet_Iic]
    exact tsub_le_tsub_left (swingOvershootMeasure_Iic_le_zero hX hi hG ha r) 1
  have hIci : ∀ r, swingOvershootMeasure X μ 0 (Ici r) ≤ swingOvershootMeasure X μ a (Ici r) := by
    intro r
    rw [swingOvershootMeasure_Ici_eq_Ioi, swingOvershootMeasure_Ici_eq_Ioi]
    exact hIoi r
  exact stochasticallyLE_of_tails hIoi hIci

/-! ### The boundary order of the slope chain -/

/-- **Boundary order**: for every `a > 0` and every Lipschitz test function `g` monotone on
`(0, ∞)`, `∫ g dT(a) ≤ ∫ g dT(0)`; i.e. `T(a, ·) ≤_st T(0, ·)` on such tests. -/
theorem swingSlopeChainKernel_integral_le_zero [SFinite μ] (hX : ∀ n, Measurable (X n))
    (hi : iIndepFun X μ) (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) {a : ℝ} (ha : 0 < a)
    {L : ℝ≥0} {g : ℝ → ℝ} (hg : IsTest (Ioi 0) L g) (hmono : MonotoneOn g (Ioi 0)) :
    ∫ x, g x ∂(swingSlopeChainKernel X μ a) ≤ ∫ x, g x ∂(swingSlopeChainKernel X μ 0) := by
  have hprob : IsProbabilityMeasure μ := hi.isProbabilityMeasure
  have hA := swingSlopeKernel_isMarkov (μ := μ) hX
  have hB0 := swingOvershootMeasure_zero_isProbability hX hi hG
  have hBa := swingOvershootMeasure_isProbability hX hi hG ha
  rw [swingSlopeChainKernel_integral_eq hX hi
      (swingSlopeChainKernel_integrable_test hX hi hG ha hg),
    swingSlopeChainKernel_integral_eq hX hi
      (swingSlopeChainKernel_zero_integrable_test hX hi hG hg)]
  set G : ℝ → ℝ := fun r => ∫ b, g b ∂swingSlopeKernel X μ r with hGdef
  have hGl : LipschitzWith L G := swingSlopeKernel_integral_lipschitz_test hX hi hG hg
  have hGm : Measurable G := act_measurable (T := swingSlopeKernel X μ) hg.meas
  have hGanti : Antitone G := swingSlopeKernel_integral_antitone_test hX hi hG hg hmono
  have hm0 := swingOvershootMeasure_zero_integrable_id hX hi hG
  have hma := swingOvershootMeasure_integrable_id hX hi hG ha
  have hG0 := integrable_of_lipschitzWith_of_moment hm0 hGl hGm
  have hGa := integrable_of_lipschitzWith_of_moment hma hGl hGm
  have h := swingOvershootMeasure_zero_stochasticallyLE hX hi hG ha (fun r => -G r) hGm.neg
    (fun x y hxy => by simp only [neg_le_neg_iff]; exact hGanti hxy) hG0.neg hGa.neg
  rw [integral_neg, integral_neg] at h
  linarith

end SwingRepair
