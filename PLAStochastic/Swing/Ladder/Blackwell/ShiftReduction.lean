import PLAStochastic.Swing.Ladder.Renewal.StationaryIdentity
import PLAStochastic.Swing.Ladder.Blackwell.WindowProvider
import PLAStochastic.Swing.StationaryLimit.AssemblyFromOvershootProvider

/-!
# Blackwell reduced to asymptotic shift invariance

`LadderStationaryIdentity` proves the exact identity

`∫ U_a((b-x-y, b-y]) dQ_a(y) = x/μ_a`,

so the Blackwell error is a `Q_a`-average of *differences* of window masses at
shifted positions.  Combined with the position-uniform window bound (which
makes every such difference bounded by a constant depending only on the window
length) and the uniform Chebyshev tail of `Q_a`, this shows that
`UniformRenewalWindowLimit` follows from asymptotic shift invariance of the
window mass alone.

Nothing about the *value* of the limit is left open by this reduction: the
constant `1/μ_a` is produced by the exact identity, not assumed.  The residual
hypothesis is stated inline, deliberately not as a new named predicate, so
that the library keeps exactly one named renewal provider.
-/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology Classical MeasureTheory
namespace SwingRepair
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {X : ℕ → Ω → ℝ}

/--
**Asymptotic shift invariance implies uniform Blackwell.**

The hypothesis `hshift` is the statement that the renewal window mass at a
distant position does not change when the window is shifted by a bounded
amount, uniformly over the drift strip, the window length and the shift.  It is
strictly weaker than `UniformRenewalWindowLimit`: it says nothing about the
value of the limit.  It is still a hypothesis and is *not* proved here.
-/
theorem uniformRenewalWindowLimit_of_shift
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1)
    (hshift : ∀ δ M K Y ε : ℝ, 0 < δ → 0 ≤ M → 0 ≤ K → 0 ≤ Y → 0 < ε →
      ∃ b₀ : ℝ, 0 < b₀ ∧
        ∀ a ∈ Icc δ M, ∀ b : ℝ, b₀ ≤ b → ∀ x : ℝ, 0 ≤ x → x ≤ K →
          ∀ y : ℝ, 0 ≤ y → y ≤ Y →
            |(ladderRenewalMeasure (gaussianAscendingLadderLaw X μ a)
                (Ioc (b - x) b)).toReal -
              (ladderRenewalMeasure (gaussianAscendingLadderLaw X μ a)
                (Ioc (b - x - y) (b - y))).toReal| ≤ ε) :
    UniformRenewalWindowLimit X μ := by
  have _ : IsProbabilityMeasure μ := hi.isProbabilityMeasure
  intro δ M K ε hδ hM hK hε
  set cM : ℝ := gaussianAscendingLadderCommonDensity M with hcMdef
  have hcM : 0 < cM := gaussianAscendingLadderCommonDensity_pos M
  set B : ℝ := gaussianAscendingLadderMomentBound δ M 2 with hBdef
  set C : ℝ := 2 * Real.exp 1 * (1 + K) / cM with hCdef
  have hC : 0 < C := by
    rw [hCdef]
    have : (0 : ℝ) < 2 * Real.exp 1 * (1 + K) := by
      have := Real.exp_pos 1
      positivity
    positivity
  -- choose the shift range so that the far part costs at most `ε/2`
  have hlim : Tendsto (fun Y : ℝ => 2 * C * (B / (cM * Y))) atTop (𝓝 0) := by
    have hden : Tendsto (fun Y : ℝ => cM * Y) atTop atTop :=
      tendsto_id.const_mul_atTop hcM
    have h1 : Tendsto (fun Y : ℝ => B / (cM * Y)) atTop (𝓝 0) :=
      Filter.Tendsto.div_atTop tendsto_const_nhds hden
    have h2 := h1.const_mul (2 * C)
    rw [mul_zero] at h2
    exact h2
  obtain ⟨Y₀, hY₀⟩ := eventually_atTop.mp (hlim.eventually_lt_const (by linarith : (0:ℝ) < ε / 2))
  set Y : ℝ := max Y₀ 1 with hYdef
  have hY1 : (1 : ℝ) ≤ Y := le_max_right _ _
  have hYpos : 0 < Y := lt_of_lt_of_le one_pos hY1
  have hYcost : 2 * C * (B / (cM * Y)) ≤ ε / 2 := (hY₀ Y (le_max_left _ _)).le
  obtain ⟨b₀, hb₀pos, hb₀⟩ := hshift δ M K Y (ε / 2) hδ hM hK hYpos.le (by linarith)
  refine ⟨max b₀ (max K 1), lt_of_lt_of_le hb₀pos (le_max_left _ _), ?_⟩
  intro a ha b hb x hx hxK
  have hbb : b₀ ≤ b := le_trans (le_max_left _ _) hb
  have hKb : K ≤ b := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hb
  have hxb : x ≤ b := le_trans hxK hKb
  have hδa : δ ≤ a := ha.1
  have haM : a ≤ M := ha.2
  have hapos : 0 < a := lt_of_lt_of_le hδ hδa
  have hprob := gaussianAscendingLadderLaw_isProbabilityMeasure hX hi a
  set ν := gaussianAscendingLadderLaw X μ a with hνdef
  have hQprob := gaussianAscendingLadderEquilibrium_isProbabilityMeasure
    hX hi hG hδ hδa haM
  set Q := equilibriumOvershootLaw ν with hQdef
  set W₀ : ℝ := (ladderRenewalMeasure ν (Ioc (b - x) b)).toReal with hW₀def
  set W : ℝ → ℝ := fun y =>
    (ladderRenewalMeasure ν (Ioc (b - x - y) (b - y))).toReal with hWdef
  -- the exact error representation
  have hrep : W₀ - x / ladderMean ν = ∫ y, (W₀ - W y) ∂Q :=
    ladderRenewalMeasure_window_sub_eq_integral hX hi hG hδ hδa haM hx hxb
  -- every window mass is bounded by `C`
  have hWbound : ∀ y : ℝ, |W y| ≤ C := by
    intro y
    have hbnd := ladderRenewalMeasure_Ioc_le_const (X := X) (μ := μ)
      hX hi hG hapos haM (b - x - y) hx
    rw [show b - x - y + x = b - y by ring] at hbnd
    have hmono := ENNReal.toReal_mono ENNReal.ofReal_ne_top hbnd
    rw [ENNReal.toReal_ofReal (by positivity)] at hmono
    rw [hWdef]
    simp only []
    rw [abs_of_nonneg ENNReal.toReal_nonneg]
    refine le_trans hmono ?_
    rw [hCdef]
    have hnum : 2 * Real.exp 1 * (1 + x) ≤ 2 * Real.exp 1 * (1 + K) := by
      have := Real.exp_pos 1
      nlinarith
    exact div_le_div_of_nonneg_right hnum hcM.le
  have hW₀bound : |W₀| ≤ C := by
    have hbnd := ladderRenewalMeasure_Ioc_le_const (X := X) (μ := μ)
      hX hi hG hapos haM (b - x) hx
    rw [show b - x + x = b by ring] at hbnd
    have hmono := ENNReal.toReal_mono ENNReal.ofReal_ne_top hbnd
    rw [ENNReal.toReal_ofReal (by positivity)] at hmono
    rw [hW₀def]
    rw [abs_of_nonneg ENNReal.toReal_nonneg]
    refine le_trans hmono ?_
    rw [hCdef]
    have hnum : 2 * Real.exp 1 * (1 + x) ≤ 2 * Real.exp 1 * (1 + K) := by
      have := Real.exp_pos 1
      nlinarith
    exact div_le_div_of_nonneg_right hnum hcM.le
  -- measurability and integrability
  have hWmeas : Measurable W :=
    (measurable_ladderRenewal_window_shift ν b x).ennreal_toReal
  have hDmeas : Measurable (fun y => W₀ - W y) := measurable_const.sub hWmeas
  have hDint : Integrable (fun y => W₀ - W y) Q := by
    refine (integrable_const (2 * C)).mono' hDmeas.aestronglyMeasurable ?_
    filter_upwards with y
    rw [Real.norm_eq_abs]
    calc |W₀ - W y| ≤ |W₀| + |W y| := abs_sub _ _
      _ ≤ 2 * C := by linarith [hWbound y, hW₀bound]
  set dom : ℝ → ℝ := fun y =>
    ε / 2 + Set.indicator (Ioi Y) (fun _ => 2 * C) y with hdomdef
  have hdomint : Integrable dom Q := by
    refine (integrable_const (ε / 2)).add ?_
    exact ((integrable_const (2 * C)).indicator measurableSet_Ioi)
  -- the pointwise domination, using that `Q` lives on `[0,∞)`
  have hQnn : ∀ᵐ y ∂Q, 0 ≤ y := by
    rw [ae_iff]
    have hset : {y : ℝ | ¬ (0 : ℝ) ≤ y} = Iio 0 := by
      ext y
      simp
    rw [hset, hQdef]
    exact equilibriumOvershootLaw_Iio_zero ν
  have hpoint : ∀ᵐ y ∂Q, |W₀ - W y| ≤ dom y := by
    filter_upwards [hQnn] with y hy
    by_cases hcase : Y < y
    · rw [hdomdef]
      simp only []
      rw [Set.indicator_of_mem (show y ∈ Ioi Y from hcase)]
      have h2 : |W₀ - W y| ≤ 2 * C := by
        calc |W₀ - W y| ≤ |W₀| + |W y| := abs_sub _ _
          _ ≤ 2 * C := by linarith [hWbound y, hW₀bound]
      linarith
    · rw [hdomdef]
      simp only []
      rw [Set.indicator_of_notMem (by simpa using hcase), add_zero]
      exact hb₀ a ha b hbb x hx hxK y hy (le_of_not_gt hcase)
  -- integrate
  have hQtail : Q.real (Ioi Y) ≤ B / (cM * Y) :=
    equilibriumOvershoot_tail_le hX hi hG hδ hδa haM hYpos
  have hdomval : (∫ y, dom y ∂Q) = ε / 2 + 2 * C * Q.real (Ioi Y) := by
    rw [hdomdef, integral_add (integrable_const _)
      ((integrable_const (2 * C)).indicator measurableSet_Ioi), integral_const]
    have hQuniv : Q.real univ = 1 := by
      rw [Measure.real, measure_univ, ENNReal.toReal_one]
    rw [hQuniv, one_smul, integral_indicator_const _ measurableSet_Ioi]
    congr 1
    rw [smul_eq_mul, mul_comm]
  rw [hrep]
  calc |∫ y, (W₀ - W y) ∂Q| ≤ ∫ y, |W₀ - W y| ∂Q := abs_integral_le_integral_abs
    _ ≤ ∫ y, dom y ∂Q := integral_mono_ae hDint.abs hdomint hpoint
    _ = ε / 2 + 2 * C * Q.real (Ioi Y) := hdomval
    _ ≤ ε := by
        have hstep : 2 * C * Q.real (Ioi Y) ≤ 2 * C * (B / (cM * Y)) :=
          mul_le_mul_of_nonneg_left hQtail (by linarith)
        linarith

/-- The terminal theorem with the shift-invariance hypothesis.  It is the same
paper-level conclusion as `theorem_4_3_swing_of_renewal_window`, reached from a
strictly weaker input. -/
theorem theorem_4_3_swing_of_renewal_shift [SFinite μ]
    (hX : ∀ j, Measurable (X j)) (hi : iIndepFun X μ)
    (hG : ∀ j, μ.map (X j) = gaussianReal 0 1)
    {ι : Type*} {l : Filter ι} [l.NeBot]
    {budget : ι → ℝ} (hbudget : ∀ i, stationaryScaleThreshold ≤ budget i)
    (hbudget_top : Tendsto budget l atTop)
    (hshift : ∀ δ M K Y ε : ℝ, 0 < δ → 0 ≤ M → 0 ≤ K → 0 ≤ Y → 0 < ε →
      ∃ b₀ : ℝ, 0 < b₀ ∧
        ∀ a ∈ Icc δ M, ∀ b : ℝ, b₀ ≤ b → ∀ x : ℝ, 0 ≤ x → x ≤ K →
          ∀ y : ℝ, 0 ≤ y → y ≤ Y →
            |(ladderRenewalMeasure (gaussianAscendingLadderLaw X μ a)
                (Ioc (b - x) b)).toReal -
              (ladderRenewalMeasure (gaussianAscendingLadderLaw X μ a)
                (Ioc (b - x - y) (b - y))).toReal| ≤ ε) :
    ∃ ν : ProbabilityMeasure ℝ,
      (swingMarginKernel X μ).Invariant (ν : Measure ℝ) ∧
      (∀ ν' : Measure ℝ, IsProbabilityMeasure ν' →
        (swingMarginKernel X μ).Invariant ν' → ν' = (ν : Measure ℝ)) ∧
      (ν : Measure ℝ) ≪ volume ∧ (volume : Measure ℝ) ≪ (ν : Measure ℝ) ∧
      Tendsto (fun i =>
        LeadingCoefficient.nativeStationaryMarginProb X μ (budget i)) l (𝓝 ν) ∧
      Tendsto
        (fun i => LeadingCoefficient.nativeStationarySegmentMean X μ (budget i) /
          (budget i * Real.log (budget i))) l
        (𝓝 (LeadingCoefficient.stationaryLeadingCoefficient X μ (ν : Measure ℝ))) ∧
      LeadingCoefficient.stationaryLeadingCoefficient X μ (ν : Measure ℝ) =
        4 * ∫ r in Ioi (0 : ℝ), gaussianRenewalPotential X μ r ∂(ν : Measure ℝ) ∧
      IntegrableOn (gaussianRenewalPotential X μ) (Ioi (0 : ℝ)) (ν : Measure ℝ) ∧
      LeadingCoefficient.stationaryLeadingCoefficient X μ (ν : Measure ℝ) ≤
        4 * (gaussianExcessExpMomentBound 2 + ∫ r, |r| ∂(ν : Measure ℝ)) ∧
      0 < LeadingCoefficient.stationaryLeadingCoefficient X μ (ν : Measure ℝ) :=
  LeadingCoefficient.theorem_4_3_swing_of_renewal_window hX hi hG hbudget
    hbudget_top (uniformRenewalWindowLimit_of_shift hX hi hG hshift)

end SwingRepair
