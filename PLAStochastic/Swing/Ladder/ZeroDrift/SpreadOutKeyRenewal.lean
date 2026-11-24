import PLAStochastic.Swing.Ladder.ZeroDrift.SpreadOutBlackwell

/-!
# The key renewal theorem for the residual life of a spread-out law

For a `SpreadOutLaw ν κ` the residual-life integral

`∫_{[0,b]} ν((b+t-s, ∞)) U(ds)`

converges, as `b → ∞`, to the equilibrium overshoot tail `(∫_t^∞ ν((o,∞)) do) / E H`.  This
is the key renewal theorem for the directly Riemann integrable function `y ↦ ν((y+t,∞))`.
The proof follows the window route of `Swing.Ladder.Blackwell.WindowProvider`: after the
exchange of variables the residual-life integral is an integral over the ladder height of
the renewal mass of a window ending at the level; windows of length at most `K` are
handled by Blackwell's theorem, longer ones by the position-uniform window bound and a
Chebyshev estimate whose cost vanishes as `K → ∞`.
-/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology Classical MeasureTheory
namespace SwingRepair
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

/-- The window constant `2e/κ` of `SpreadOutLaw.renewal_Ioc_le_const`. -/
def spreadOutWindowConstant (κ : ℝ) : ℝ := 2 * Real.exp 1 / κ

theorem spreadOutWindowConstant_pos {κ : ℝ} (hκ : 0 < κ) : 0 < spreadOutWindowConstant κ := by
  unfold spreadOutWindowConstant
  have := Real.exp_pos 1
  positivity

/-- The far-tail cost of the window route at window range `K`. -/
def spreadOutResidualBound (ν : Measure ℝ) (κ K : ℝ) : ℝ :=
  spreadOutWindowConstant κ * ((∫ x, x ^ 2 ∂ν) / K ^ 2) +
    (spreadOutWindowConstant κ + 1 / κ) * ((∫ x, x ^ 2 ∂ν) / K)

namespace SpreadOutLaw

variable {ν : Measure ℝ} {κ : ℝ}

theorem max_integrable (hν : SpreadOutLaw ν κ) (t : ℝ) :
    Integrable (fun h : ℝ => max (h - t) 0) ν := by
  have hprob := hν.isProbabilityMeasure
  have hdom : Integrable (fun h : ℝ => |h| + |t|) ν := hν.id_integrable.abs.add (integrable_const |t|)
  refine Integrable.mono' hdom ?_ ?_
  · exact ((measurable_id.sub measurable_const).max measurable_const).aestronglyMeasurable
  · filter_upwards with h
    rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
    have h1 : max (h - t) 0 ≤ |h - t| := max_le (le_abs_self _) (abs_nonneg _)
    have h2 : |h - t| ≤ |h| + |t| := abs_sub _ _
    linarith

/-- The `b`-free bound on the residual-life window. -/
theorem renewalWindowReal_le_const (hν : SpreadOutLaw ν κ) (b t h : ℝ) :
    renewalWindowReal ν b t h ≤ spreadOutWindowConstant κ * (1 + max (h - t) 0) := by
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
  have hbnd := hν.renewal_Ioc_le_const (b - x) hx
  have hmono : ladderRenewalMeasure ν (Ioi (b + t - h) ∩ Icc (0 : ℝ) b) ≤
      ENNReal.ofReal (2 * Real.exp 1 * (1 + x) /
        κ) :=
    le_trans (measure_mono hsub) hbnd
  have hfin : ENNReal.ofReal (2 * Real.exp 1 * (1 + x) /
      κ) ≠ ⊤ := ENNReal.ofReal_ne_top
  have htoReal := ENNReal.toReal_mono hfin hmono
  have hval : (ENNReal.ofReal (2 * Real.exp 1 * (1 + x) /
      κ)).toReal =
      spreadOutWindowConstant κ * (1 + x) := by
    have hc := hν.pos
    rw [ENNReal.toReal_ofReal (by positivity)]
    unfold spreadOutWindowConstant
    field_simp
  unfold renewalWindowReal
  rw [← hval]
  exact htoReal

/-- The pointwise comparison of the residual-life window with its linear value. -/
theorem renewalWindowReal_sub_le_of_window (hν : SpreadOutLaw ν κ)
    {b t h K ε : ℝ} (_ht : 0 ≤ t) (hK : 0 ≤ K) (hKb : K ≤ b)
    (hnear : ∀ x : ℝ, 0 ≤ x → x ≤ K →
      |(ladderRenewalMeasure ν (Ioc (b - x) b)).toReal - x / ladderMean ν| ≤ ε) :
    |renewalWindowReal ν b t h - max (h - t) 0 / ladderMean ν| ≤
      ε + (Ioi (t + K)).indicator
        (fun y => spreadOutWindowConstant κ * (1 + (y - t)) + (y - t) / ladderMean ν) h := by
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
        spreadOutWindowConstant κ * (1 + (h - t)) := by
      have hbase := hν.renewalWindowReal_le_const b t h
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

/-- The residual-life tail is within `ε + spreadOutResidualBound ν κ K` of the equilibrium
overshoot tail as soon as every window of length at most `K` ending at `b` is within `ε`
of its Blackwell value. -/
theorem renewalOvershootTail_sub_equilibrium_le (hν : SpreadOutLaw ν κ)
    {b t K ε : ℝ} (ht : 0 ≤ t) (hK : 0 < K) (hKb : K ≤ b)
    (hnear : ∀ x : ℝ, 0 ≤ x → x ≤ K →
      |(ladderRenewalMeasure ν (Ioc (b - x) b)).toReal - x / ladderMean ν| ≤ ε) :
    |(renewalOvershootTail ν b t).toReal - (equilibriumOvershootTail ν t).toReal| ≤
      ε + spreadOutResidualBound ν κ K := by
  have hprob := hν.isProbabilityMeasure
  set μ0 : ℝ := ladderMean ν with hμ0def
  set C2 : ℝ := spreadOutWindowConstant κ with hC2def
  set B : ℝ := (∫ x, x ^ 2 ∂ν) with hBdef
  set cM : ℝ := κ with hcMdef
  have hC2 : 0 < C2 := spreadOutWindowConstant_pos hν.pos
  have hcM : 0 < cM := hν.pos
  have hB0 : 0 ≤ B := hν.sqMoment_nonneg
  have hb : 0 ≤ b := le_trans hK.le hKb
  have hfin := hν.renewal_Icc_ne_top
  have hid := hν.id_integrable
  have hsq := hν.sq_integrable
  have hsqle : (∫ x, x ^ 2 ∂ν) ≤ B :=
    le_rfl
  have hmean := hν.mean_ge
  have hmean0 : 0 < μ0 := lt_of_lt_of_le hcM hmean
  have hint := hν.max_integrable t
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
    hν.renewalWindowReal_sub_le_of_window ht hK.le hKb hnear
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
    _ ≤ ε + spreadOutResidualBound ν κ K := by
        have h1 : C2 * ν.real (Ioi (t + K)) ≤ C2 * (B / K ^ 2) :=
          mul_le_mul_of_nonneg_left htail hC2.le
        have h2 : (C2 + 1 / μ0) * ∫ h in Ioi (t + K), (h - t) ∂ν ≤
            (C2 + 1 / cM) * (B / K) := by
          have hnn : 0 ≤ C2 + 1 / μ0 := by positivity
          calc (C2 + 1 / μ0) * ∫ h in Ioi (t + K), (h - t) ∂ν
              ≤ (C2 + 1 / μ0) * (B / K) := mul_le_mul_of_nonneg_left hfar hnn
            _ ≤ (C2 + 1 / cM) * (B / K) := by
                refine mul_le_mul_of_nonneg_right hcoef (by positivity)
        unfold spreadOutResidualBound
        rw [← hC2def, ← hBdef, ← hcMdef]
        linarith

theorem spreadOutResidualBound_tendsto (ν : Measure ℝ) (κ : ℝ) :
    Tendsto (fun K : ℝ => spreadOutResidualBound ν κ K) atTop (𝓝 0) := by
  have hsq : Tendsto (fun K : ℝ => K ^ 2) atTop atTop :=
    tendsto_pow_atTop (n := 2) (by norm_num)
  have h1 : Tendsto
      (fun K : ℝ => (∫ x, x ^ 2 ∂ν) / K ^ 2) atTop (𝓝 0) :=
    Filter.Tendsto.div_atTop tendsto_const_nhds hsq
  have h2 : Tendsto
      (fun K : ℝ => (∫ x, x ^ 2 ∂ν) / K) atTop (𝓝 0) :=
    Filter.Tendsto.div_atTop tendsto_const_nhds tendsto_id
  have hsum := ((h1.const_mul (spreadOutWindowConstant κ)).add
    (h2.const_mul (spreadOutWindowConstant κ +
      1 / κ)))
  simpa [spreadOutResidualBound] using hsum

/-- **The key renewal theorem for the residual life.**  For every `t ≥ 0`,
`∫_{[0,b]} ν((b+t-s,∞)) U(ds) → (∫_t^∞ ν((o,∞)) do) / E H` as `b → ∞`. -/
theorem renewalOvershootTail_tendsto (hν : SpreadOutLaw ν κ) {t : ℝ} (ht : 0 ≤ t) :
    Tendsto (fun b : ℝ => (renewalOvershootTail ν b t).toReal) atTop
      (𝓝 (equilibriumOvershootTail ν t).toReal) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hsmall : ∀ᶠ K : ℝ in atTop, spreadOutResidualBound ν κ K < ε / 4 :=
    (spreadOutResidualBound_tendsto ν κ).eventually_lt_const (by linarith)
  obtain ⟨K₀, hK₀⟩ := eventually_atTop.mp hsmall
  set K : ℝ := max K₀ 1 with hKdef
  have hKpos : 0 < K := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hKcost : spreadOutResidualBound ν κ K < ε / 4 := hK₀ K (le_max_left _ _)
  obtain ⟨b₀, -, hnear⟩ := hν.renewalWindow_uniform hKpos.le (show (0 : ℝ) < ε / 4 by linarith)
  refine ⟨max b₀ K, fun b hb => ?_⟩
  have hb0 : b₀ ≤ b := le_trans (le_max_left _ _) hb
  have hKb : K ≤ b := le_trans (le_max_right _ _) hb
  have hmain := hν.renewalOvershootTail_sub_equilibrium_le ht hKpos hKb (hnear b hb0)
  rw [Real.dist_eq]
  linarith

end SpreadOutLaw

end SwingRepair
