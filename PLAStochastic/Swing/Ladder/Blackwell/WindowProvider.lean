import PLAStochastic.Swing.Ladder.Renewal.PositionUniformWindow
import PLAStochastic.Swing.Ladder.Renewal.ResidualLifeUniform
import PLAStochastic.Swing.Ladder.Blackwell.OvershootProvider

/-!
# Replacing the Blanchet--Glynn expansion by bare uniform Blackwell

The existing residual-life comparison consumes the full Blanchet--Glynn
expansion: its constant term `E H²/(2μ²)` and its exponential rate both enter,
because the far-tail branch is bounded by `(b + (h-t))/μ + |K| + C`, which
grows with the passage level `b`.

`LadderWindowUniform` removes that growth: the renewal mass of a window is
bounded by a constant depending only on the window length.  Consequently the
far branch no longer needs the expansion at all, and the near branch needs only

  `U_a((b-x, b]) → x/μ_a` uniformly for `x` in a compact range,

which is the bare uniform Blackwell renewal theorem: no constant term, no rate.
This file introduces that predicate, proves it suffices for
`UniformOvershootTailLimit`, and proves it is implied by the expansion, so no
route is lost.
-/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology Classical MeasureTheory
namespace SwingRepair
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {X : ℕ → Ω → ℝ}

/-- The position-uniform window constant of `LadderWindowUniform`, written as
an affine function of the window length. -/
noncomputable def gaussianWindowConstant (M : ℝ) : ℝ :=
  2 * Real.exp 1 / gaussianAscendingLadderCommonDensity M

theorem gaussianWindowConstant_pos (M : ℝ) : 0 < gaussianWindowConstant M := by
  unfold gaussianWindowConstant
  have := gaussianAscendingLadderCommonDensity_pos M
  positivity

/-- The residual-life window is the renewal mass of an explicit interval. -/
theorem renewalWindowReal_eq_Ioc (ν : Measure ℝ) {b t h : ℝ}
    (_hb : 0 ≤ b) (hbound : max (h - t) 0 ≤ b) :
    renewalWindowReal ν b t h =
      (ladderRenewalMeasure ν (Ioc (b - max (h - t) 0) b)).toReal := by
  unfold renewalWindowReal
  rcases le_or_gt h t with hht | hht
  · rw [max_eq_right (by linarith), sub_zero,
      window_of_ge (show b ≤ b + t - h by linarith)]
    simp
  · have hmax : max (h - t) 0 = h - t := max_eq_left (by linarith)
    rw [hmax] at hbound ⊢
    rw [show b + t - h = b - (h - t) by ring,
      window_of_mid (b := b) (show (0 : ℝ) ≤ b - (h - t) by linarith)]

/-- **The `b`-free bound on the residual-life window.**  Unlike the expansion
route, the right-hand side does not grow with the passage level. -/
theorem renewalWindowReal_le_windowConstant [IsProbabilityMeasure μ]
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1)
    {M a : ℝ} (ha : 0 < a) (haM : a ≤ M) (b t h : ℝ) :
    renewalWindowReal (gaussianAscendingLadderLaw X μ a) b t h ≤
      gaussianWindowConstant M * (1 + max (h - t) 0) := by
  set ν := gaussianAscendingLadderLaw X μ a with hνdef
  set x := max (h - t) 0 with hxdef
  have hx : 0 ≤ x := le_max_right _ _
  have hsub : Ioi (b + t - h) ∩ Icc (0 : ℝ) b ⊆ Ioc (b - x) ((b - x) + x) := by
    intro y hy
    obtain ⟨hy1, hy2, hy3⟩ := hy
    have hy1' : b + t - h < y := hy1
    have hxge : h - t ≤ x := le_max_left _ _
    refine ⟨?_, by linarith⟩
    have hle : b - x ≤ b + t - h := by linarith
    exact lt_of_le_of_lt hle hy1'
  have hbnd := ladderRenewalMeasure_Ioc_le_const (X := X) (μ := μ) hX hi hG ha haM (b - x) hx
  have hmono : ladderRenewalMeasure ν (Ioi (b + t - h) ∩ Icc (0 : ℝ) b) ≤
      ENNReal.ofReal (2 * Real.exp 1 * (1 + x) /
        gaussianAscendingLadderCommonDensity M) :=
    le_trans (measure_mono hsub) hbnd
  have hfin : ENNReal.ofReal (2 * Real.exp 1 * (1 + x) /
      gaussianAscendingLadderCommonDensity M) ≠ ⊤ := ENNReal.ofReal_ne_top
  have htoReal := ENNReal.toReal_mono hfin hmono
  have hval : (ENNReal.ofReal (2 * Real.exp 1 * (1 + x) /
      gaussianAscendingLadderCommonDensity M)).toReal =
      gaussianWindowConstant M * (1 + x) := by
    have hc := gaussianAscendingLadderCommonDensity_pos M
    rw [ENNReal.toReal_ofReal (by positivity)]
    unfold gaussianWindowConstant
    field_simp
  unfold renewalWindowReal
  rw [← hval]
  exact htoReal

/-! ### The bare Blackwell predicate -/

/--
`UniformRenewalWindowLimit X μ`: for every positive compact drift strip and
every compact range of window lengths, the renewal mass of the window
`(b-x, b]` converges to `x/μ_a` as the position `b` tends to infinity,
uniformly in the drift and in the window length.

This is the classical Blackwell renewal theorem made uniform over the strip.
Compared with `UniformLadderRenewalExpansion` it carries **no** constant term
and **no** rate.  It is a hypothesis, not a theorem.
-/
def UniformRenewalWindowLimit (X : ℕ → Ω → ℝ) (μ : Measure Ω) : Prop :=
  ∀ δ M K ε : ℝ, 0 < δ → 0 ≤ M → 0 ≤ K → 0 < ε →
    ∃ b₀ : ℝ, 0 < b₀ ∧
      ∀ a ∈ Icc δ M, ∀ b : ℝ, b₀ ≤ b → ∀ x : ℝ, 0 ≤ x → x ≤ K →
        |(ladderRenewalMeasure (gaussianAscendingLadderLaw X μ a)
            (Ioc (b - x) b)).toReal -
          x / ladderMean (gaussianAscendingLadderLaw X μ a)| ≤ ε


/-! ### The pointwise comparison -/

theorem renewalWindowReal_sub_le_of_window [IsProbabilityMeasure μ]
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1)
    {M a : ℝ} (ha : 0 < a) (haM : a ≤ M)
    {b t h K ε : ℝ} (_ht : 0 ≤ t) (hK : 0 ≤ K) (hKb : K ≤ b)
    (hnear : ∀ x : ℝ, 0 ≤ x → x ≤ K →
      |(ladderRenewalMeasure (gaussianAscendingLadderLaw X μ a)
          (Ioc (b - x) b)).toReal -
        x / ladderMean (gaussianAscendingLadderLaw X μ a)| ≤ ε) :
    |renewalWindowReal (gaussianAscendingLadderLaw X μ a) b t h -
        max (h - t) 0 / ladderMean (gaussianAscendingLadderLaw X μ a)| ≤
      ε + (Ioi (t + K)).indicator
        (fun y => gaussianWindowConstant M * (1 + (y - t)) +
          (y - t) / ladderMean (gaussianAscendingLadderLaw X μ a)) h := by
  set ν := gaussianAscendingLadderLaw X μ a with hνdef
  set μ0 : ℝ := ladderMean ν with hμ0
  have hb : 0 ≤ b := le_trans hK hKb
  have hμ0nn : 0 ≤ μ0 := ENNReal.toReal_nonneg
  have hε : 0 ≤ ε := by
    have h0 := hnear 0 le_rfl hK
    simp only [sub_zero, zero_div, Set.Ioc_self, measure_empty,
      ENNReal.toReal_zero, abs_zero] at h0
    exact h0
  by_cases hcase : t + K < h
  · rw [Set.indicator_of_mem (show h ∈ Ioi (t + K) from hcase)]
    have hht : t < h := by linarith
    have hmax : max (h - t) 0 = h - t := max_eq_left (by linarith)
    have hW0 : 0 ≤ renewalWindowReal ν b t h := renewalWindowReal_nonneg ν b t h
    have hWle : renewalWindowReal ν b t h ≤
        gaussianWindowConstant M * (1 + (h - t)) := by
      have hbase := renewalWindowReal_le_windowConstant hX hi hG ha haM b t h
      rwa [hmax] at hbase
    rw [hmax]
    have hm0 : 0 ≤ (h - t) / μ0 := div_nonneg (by linarith) hμ0nn
    have habs : |renewalWindowReal ν b t h - (h - t) / μ0| ≤
        renewalWindowReal ν b t h + (h - t) / μ0 := by
      rw [abs_sub_le_iff]
      constructor <;> linarith
    linarith
  · rw [Set.indicator_of_notMem (by simpa using hcase), add_zero]
    have hmaxle : max (h - t) 0 ≤ K := by
      refine max_le ?_ hK
      linarith [not_lt.mp hcase]
    have hmaxb : max (h - t) 0 ≤ b := le_trans hmaxle hKb
    rw [renewalWindowReal_eq_Ioc ν hb hmaxb]
    exact hnear (max (h - t) 0) (le_max_right _ _) hmaxle

/-! ### The integrated comparison -/

/-- The explicit far-tail cost of the window route.  It tends to zero as the
window range `K` grows, and does not depend on the passage level. -/
noncomputable def gaussianWindowResidualBound (δ M K : ℝ) : ℝ :=
  gaussianWindowConstant M * (gaussianAscendingLadderMomentBound δ M 2 / K ^ 2) +
    (gaussianWindowConstant M + 1 / gaussianAscendingLadderCommonDensity M) *
      (gaussianAscendingLadderMomentBound δ M 2 / K)

theorem renewalOvershootTail_sub_equilibrium_le_of_window [IsProbabilityMeasure μ]
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1)
    {δ M : ℝ} (hδ : 0 < δ) {a : ℝ} (hδa : δ ≤ a) (haM : a ≤ M)
    {b t K ε : ℝ} (ht : 0 ≤ t) (hK : 0 < K) (hKb : K ≤ b)
    (hnear : ∀ x : ℝ, 0 ≤ x → x ≤ K →
      |(ladderRenewalMeasure (gaussianAscendingLadderLaw X μ a)
          (Ioc (b - x) b)).toReal -
        x / ladderMean (gaussianAscendingLadderLaw X μ a)| ≤ ε) :
    |(renewalOvershootTail (gaussianAscendingLadderLaw X μ a) b t).toReal -
        (equilibriumOvershootTail (gaussianAscendingLadderLaw X μ a) t).toReal| ≤
      ε + gaussianWindowResidualBound δ M K := by
  have ha : 0 < a := lt_of_lt_of_le hδ hδa
  have hprob := gaussianAscendingLadderLaw_isProbabilityMeasure hX hi a
  set ν := gaussianAscendingLadderLaw X μ a with hνdef
  set μ0 : ℝ := ladderMean ν with hμ0def
  set C2 : ℝ := gaussianWindowConstant M with hC2def
  set B : ℝ := gaussianAscendingLadderMomentBound δ M 2 with hBdef
  set cM : ℝ := gaussianAscendingLadderCommonDensity M with hcMdef
  have hC2 : 0 < C2 := gaussianWindowConstant_pos M
  have hcM : 0 < cM := gaussianAscendingLadderCommonDensity_pos M
  have hB0 : 0 ≤ B := gaussianAscendingLadderMomentBound_two_nonneg hX hi hG hδ hδa haM
  have hb : 0 ≤ b := le_trans hK.le hKb
  have hfin := gaussianAscendingLadderRenewal_Icc_ne_top hX hi hG ha haM
  have hid := gaussianAscendingLadderLaw_id_integrable hX hi hG hδ hδa haM
  have hsq := gaussianAscendingLadderLaw_sq_integrable hX hi hG hδ hδa haM
  have hsqle : (∫ x, x ^ 2 ∂ν) ≤ B :=
    gaussianAscendingLadderLaw_sq_integral_le hX hi hG hδ hδa haM
  have hmean := ladderMean_gaussianAscendingLadderLaw_ge hX hi hG hδ hδa haM
  have hmean0 : 0 < μ0 := lt_of_lt_of_le hcM hmean
  have hint := gaussianAscendingLadderLaw_max_integrable hX hi hG hδ hδa haM t
  have hs : 0 < t + K := by linarith
  set W : ℝ → ℝ := renewalWindowReal ν b t with hWdef
  set g : ℝ → ℝ := fun h => max (h - t) 0 / μ0 with hgdef
  set far : ℝ → ℝ := (Ioi (t + K)).indicator
    (fun y => C2 * (1 + (y - t)) + (y - t) / μ0) with hfardef
  -- integrability, exactly as in the expansion route
  have hWmeas : Measurable W := renewalWindowReal_measurable ν hfin b t
  have hWint : Integrable W ν := by
    refine Integrable.mono' (integrable_const (ladderRenewalFunction ν b))
      hWmeas.aestronglyMeasurable ?_
    filter_upwards with h
    rw [Real.norm_eq_abs, abs_of_nonneg (renewalWindowReal_nonneg ν b t h)]
    exact renewalWindowReal_le ν hfin
  have hgint : Integrable g ν := hint.div_const μ0
  have hmaxOn : IntegrableOn (fun h => max (h - t) 0) (Ioi (t + K)) ν := hint.integrableOn
  have hsubOn : IntegrableOn (fun h => h - t) (Ioi (t + K)) ν := by
    refine IntegrableOn.congr_fun hmaxOn (fun h hh => ?_) measurableSet_Ioi
    have hh' : t + K < h := hh
    exact max_eq_left (by linarith)
  have hfarOn : IntegrableOn
      (fun y => C2 * (1 + (y - t)) + (y - t) / μ0) (Ioi (t + K)) ν := by
    have h1 : IntegrableOn (fun y : ℝ => C2 * (1 + (y - t))) (Ioi (t + K)) ν := by
      refine IntegrableOn.congr_fun
        (((integrable_const (1 : ℝ)).integrableOn.add hsubOn).const_mul C2)
        (fun y _ => ?_) measurableSet_Ioi
      simp only [Pi.add_apply]
    have h2 : IntegrableOn (fun y : ℝ => (y - t) / μ0) (Ioi (t + K)) ν :=
      hsubOn.div_const μ0
    exact h1.add h2
  have hfarint : Integrable far ν := hfarOn.integrable_indicator measurableSet_Ioi
  have hdomint : Integrable (fun h => ε + far h) ν := (integrable_const _).add hfarint
  -- pointwise
  have hpoint : ∀ h, |W h - g h| ≤ ε + far h := fun h =>
    renewalWindowReal_sub_le_of_window hX hi hG ha haM ht hK.le hKb hnear
  -- the two far-tail estimates
  have htail : ν.real (Ioi (t + K)) ≤ B / K ^ 2 := by
    refine (measureReal_Ioi_le_sq_moment hsq hs).trans ?_
    refine div_le_div₀ hB0 hsqle (by positivity) ?_
    nlinarith
  have hfar : (∫ h in Ioi (t + K), (h - t) ∂ν) ≤ B / K := by
    refine (setIntegral_sub_le_sq_moment hid hsq ht hs).trans ?_
    exact div_le_div₀ hB0 hsqle hK (by linarith)
  have hfar0 : 0 ≤ ∫ h in Ioi (t + K), (h - t) ∂ν := by
    refine setIntegral_nonneg measurableSet_Ioi (fun h hh => ?_)
    have hh' : t + K < h := hh
    linarith
  -- integrate
  have hsub : (renewalOvershootTail ν b t).toReal -
      (equilibriumOvershootTail ν t).toReal = ∫ h, (W h - g h) ∂ν := by
    rw [renewalOvershootTail_toReal ν hfin b t, equilibriumOvershootTail_toReal ν t,
      integral_sub hWint hgint, hgdef, integral_div]
  have hfarval : (∫ h, far h ∂ν) =
      C2 * ν.real (Ioi (t + K)) +
        (C2 + 1 / μ0) * ∫ h in Ioi (t + K), (h - t) ∂ν := by
    rw [hfardef, integral_indicator measurableSet_Ioi]
    have hsplit : (∫ y in Ioi (t + K), (C2 * (1 + (y - t)) + (y - t) / μ0) ∂ν) =
        (∫ y in Ioi (t + K), C2 ∂ν) +
          (∫ y in Ioi (t + K), (C2 + 1 / μ0) * (y - t) ∂ν) := by
      rw [← integral_add ((integrable_const C2).integrableOn)
        (hsubOn.const_mul (C2 + 1 / μ0))]
      refine setIntegral_congr_fun measurableSet_Ioi (fun y _ => ?_)
      field_simp
      ring
    rw [hsplit, setIntegral_const, integral_const_mul, smul_eq_mul]
    ring
  have hcoef : (C2 + 1 / μ0) ≤ C2 + 1 / cM := by
    have : 1 / μ0 ≤ 1 / cM := by
      rw [div_le_div_iff₀ hmean0 hcM]
      linarith
    linarith
  rw [hsub]
  calc |∫ h, (W h - g h) ∂ν| ≤ ∫ h, |W h - g h| ∂ν := abs_integral_le_integral_abs
    _ ≤ ∫ h, (ε + far h) ∂ν := integral_mono ((hWint.sub hgint).abs) hdomint hpoint
    _ = ε + ∫ h, far h ∂ν := by
        rw [integral_add (integrable_const _) hfarint, integral_const]
        simp
    _ = ε + (C2 * ν.real (Ioi (t + K)) +
          (C2 + 1 / μ0) * ∫ h in Ioi (t + K), (h - t) ∂ν) := by rw [hfarval]
    _ ≤ ε + gaussianWindowResidualBound δ M K := by
        have h1 : C2 * ν.real (Ioi (t + K)) ≤ C2 * (B / K ^ 2) :=
          mul_le_mul_of_nonneg_left htail hC2.le
        have h2 : (C2 + 1 / μ0) * ∫ h in Ioi (t + K), (h - t) ∂ν ≤
            (C2 + 1 / cM) * (B / K) := by
          have hnn : 0 ≤ C2 + 1 / μ0 := by positivity
          calc (C2 + 1 / μ0) * ∫ h in Ioi (t + K), (h - t) ∂ν
              ≤ (C2 + 1 / μ0) * (B / K) := mul_le_mul_of_nonneg_left hfar hnn
            _ ≤ (C2 + 1 / cM) * (B / K) := by
                refine mul_le_mul_of_nonneg_right hcoef (by positivity)
        unfold gaussianWindowResidualBound
        rw [← hC2def, ← hBdef, ← hcMdef]
        linarith


/-! ### The far cost vanishes -/

theorem gaussianWindowResidualBound_tendsto (δ M : ℝ) :
    Tendsto (fun K : ℝ => gaussianWindowResidualBound δ M K) atTop (𝓝 0) := by
  have hsq : Tendsto (fun K : ℝ => K ^ 2) atTop atTop :=
    tendsto_pow_atTop (n := 2) (by norm_num)
  have h1 : Tendsto
      (fun K : ℝ => gaussianAscendingLadderMomentBound δ M 2 / K ^ 2) atTop (𝓝 0) :=
    Filter.Tendsto.div_atTop tendsto_const_nhds hsq
  have h2 : Tendsto
      (fun K : ℝ => gaussianAscendingLadderMomentBound δ M 2 / K) atTop (𝓝 0) :=
    Filter.Tendsto.div_atTop tendsto_const_nhds tendsto_id
  have hsum := ((h1.const_mul (gaussianWindowConstant M)).add
    (h2.const_mul (gaussianWindowConstant M +
      1 / gaussianAscendingLadderCommonDensity M)))
  simpa [gaussianWindowResidualBound] using hsum

/-! ### Bare Blackwell suffices -/

/--
**The uniform overshoot tail limit follows from bare uniform Blackwell.**
Consequently the whole Theorem 4.3 chain no longer needs the Blanchet--Glynn
constant term or its exponential rate: the classical uniform renewal theorem
for windows is enough.
-/
theorem uniformOvershootTailLimit_of_windowLimit
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1)
    (hwin : UniformRenewalWindowLimit X μ) :
    UniformOvershootTailLimit X μ := by
  have _ : IsProbabilityMeasure μ := hi.isProbabilityMeasure
  intro δ M ε hδ hM hε
  -- choose the window range so that the far cost is at most `ε/2`
  have hsmall : ∀ᶠ K : ℝ in atTop,
      gaussianWindowResidualBound δ M K < ε / 2 :=
    (gaussianWindowResidualBound_tendsto δ M).eventually_lt_const (by linarith)
  obtain ⟨K₀, hK₀⟩ := eventually_atTop.mp hsmall
  set K : ℝ := max K₀ 1 with hKdef
  have hK1 : (1 : ℝ) ≤ K := le_max_right _ _
  have hKpos : 0 < K := lt_of_lt_of_le one_pos hK1
  have hKcost : gaussianWindowResidualBound δ M K ≤ ε / 2 :=
    (hK₀ K (le_max_left _ _)).le
  obtain ⟨b₀, hb₀pos, hnear⟩ := hwin δ M K (ε / 2) hδ hM hKpos.le (by linarith)
  refine ⟨max b₀ K, lt_of_lt_of_le hb₀pos (le_max_left _ _), ?_⟩
  intro a ha b hb t ht
  have hb0 : b₀ ≤ b := le_trans (le_max_left _ _) hb
  have hKb : K ≤ b := le_trans (le_max_right _ _) hb
  have hbpos : 0 < b := lt_of_lt_of_le hKpos hKb
  have hδa : δ ≤ a := ha.1
  have haM : a ≤ M := ha.2
  have hapos : 0 < a := lt_of_lt_of_le hδ hδa
  have hP : (gaussianWalkOvershootLaw X μ a b).real (Ioi t) =
      (renewalOvershootTail (gaussianAscendingLadderLaw X μ a) b t).toReal := by
    rw [Measure.real, gaussianWalkOvershootLaw_Ioi hX hi hG hapos haM hbpos.le ht]
  have hQ : (equilibriumOvershootLaw
      (gaussianAscendingLadderLaw X μ a)).real (Ioi t) =
      (equilibriumOvershootTail (gaussianAscendingLadderLaw X μ a) t).toReal := by
    rw [Measure.real, equilibriumOvershootLaw_Ioi _
      (gaussianAscendingLadderLaw_mean_ne_zero hX hG hapos haM) ht]
  rw [hP, hQ]
  have hmain := renewalOvershootTail_sub_equilibrium_le_of_window
    (X := X) (μ := μ) hX hi hG hδ hδa haM ht hKpos hKb
    (hnear a ha b hb0)
  refine hmain.trans ?_
  linarith

/-- The Blanchet--Glynn expansion implies the bare window limit, so nothing is
lost by weakening the standing hypothesis. -/
theorem uniformRenewalWindowLimit_of_uniform_renewal
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1)
    (hrenew : ∀ {δ M : ℝ}, 0 < δ → 0 ≤ M →
      ∃ Cexp c : ℝ,
        UniformLadderRenewalExpansion
          (gaussianAscendingLadderLaw X μ) (Icc δ M) Cexp c) :
    UniformRenewalWindowLimit X μ := by
  have _ : IsProbabilityMeasure μ := hi.isProbabilityMeasure
  intro δ M K ε hδ hM hK hε
  obtain ⟨C, c, hexp⟩ := hrenew hδ hM
  have hc : 0 < c := hexp.1
  have hC : 0 ≤ C := hexp.2.1
  -- the expansion remainder at the two endpoints of the window
  have hdecay : Tendsto (fun b : ℝ => 2 * C * Real.exp (-c * (b - K))) atTop (𝓝 0) := by
    have hmul : Tendsto (fun b : ℝ => -c * (b - K)) atTop atBot := by
      have h1 : Tendsto (fun b : ℝ => b - K) atTop atTop := tendsto_atTop_add_const_right _ _ tendsto_id
      have h2 : Tendsto (fun b : ℝ => c * (b - K)) atTop atTop := h1.const_mul_atTop hc
      refine Filter.Tendsto.congr (fun b => ?_) (tendsto_neg_atTop_atBot.comp h2)
      simp only [Function.comp_def]
      ring
    have he : Tendsto (fun b : ℝ => Real.exp (-c * (b - K))) atTop (𝓝 0) := by
      simpa only [Function.comp_def] using Real.tendsto_exp_atBot.comp hmul
    have hcm := he.const_mul (2 * C)
    rw [mul_zero] at hcm
    exact hcm
  have hev : ∀ᶠ b : ℝ in atTop, 2 * C * Real.exp (-c * (b - K)) < ε :=
    hdecay.eventually_lt_const hε
  obtain ⟨b₁, hb₁⟩ := eventually_atTop.mp hev
  refine ⟨max (max b₁ K) 1, lt_of_lt_of_le one_pos (le_max_right _ _), ?_⟩
  intro a ha b hb x hx hxK
  have hb1 : b₁ ≤ b := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hb
  have hKb : K ≤ b := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hb
  have hbpos : (0 : ℝ) < b := lt_of_lt_of_le one_pos (le_trans (le_max_right _ _) hb)
  have hδa : δ ≤ a := ha.1
  have haM : a ≤ M := ha.2
  have hapos : 0 < a := lt_of_lt_of_le hδ hδa
  have hprob := gaussianAscendingLadderLaw_isProbabilityMeasure hX hi a
  set ν := gaussianAscendingLadderLaw X μ a with hνdef
  have hfin := gaussianAscendingLadderRenewal_Icc_ne_top hX hi hG hapos haM
  have hxb : x ≤ b := le_trans hxK hKb
  -- the window written through the renewal function
  have hwin : (ladderRenewalMeasure ν (Ioc (b - x) b)).toReal =
      ladderRenewalFunction ν b - ladderRenewalFunction ν (b - x) :=
    ladderRenewalMeasure_Ioc_toReal ν hfin (by linarith) (by linarith)
  have hD := hexp.2.2
  have hDb := hD a ha b (by linarith)
  have hDbx := hD a ha (b - x) (by linarith)
  rw [hwin]
  have hsplit : ladderRenewalFunction ν b - ladderRenewalFunction ν (b - x) -
      x / ladderMean ν =
      (ladderRenewalFunction ν b -
        (b / ladderMean ν + ladderRenewalConstant ν)) -
      (ladderRenewalFunction ν (b - x) -
        ((b - x) / ladderMean ν + ladderRenewalConstant ν)) := by
    field_simp
    ring
  rw [hsplit]
  have hstep : |ladderRenewalFunction ν b -
        (b / ladderMean ν + ladderRenewalConstant ν)| +
      |ladderRenewalFunction ν (b - x) -
        ((b - x) / ladderMean ν + ladderRenewalConstant ν)| ≤
      C * Real.exp (-c * b) + C * Real.exp (-c * (b - x)) :=
    add_le_add hDb hDbx
  have hmono1 : Real.exp (-c * b) ≤ Real.exp (-c * (b - K)) := by
    apply Real.exp_le_exp.mpr
    nlinarith
  have hmono2 : Real.exp (-c * (b - x)) ≤ Real.exp (-c * (b - K)) := by
    apply Real.exp_le_exp.mpr
    nlinarith
  have hfinal : C * Real.exp (-c * b) + C * Real.exp (-c * (b - x)) ≤
      2 * C * Real.exp (-c * (b - K)) := by nlinarith
  calc |_| ≤ |ladderRenewalFunction ν b -
        (b / ladderMean ν + ladderRenewalConstant ν)| +
      |ladderRenewalFunction ν (b - x) -
        ((b - x) / ladderMean ν + ladderRenewalConstant ν)| := abs_sub _ _
    _ ≤ 2 * C * Real.exp (-c * (b - K)) := le_trans hstep hfinal
    _ ≤ ε := (hb₁ b hb1).le

end SwingRepair
