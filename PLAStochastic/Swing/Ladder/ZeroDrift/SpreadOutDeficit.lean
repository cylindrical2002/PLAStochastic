import PLAStochastic.Swing.Ladder.ZeroDrift.SpreadOut

/-!
# The deficit estimate of the Blackwell argument for one spread-out law

This file transports the two analytic steps of `Swing.Ladder.Blackwell.UniformWindowLimit`
from the Gaussian ladder family to an arbitrary `SpreadOutLaw ν κ`:

* the exact stationary identity `∫ U((b-x-y, b-y]) Q(dy) = x / E H`, averaged once more
  against `ν^{*m₀}`, so that the smoothing `σ = ν^{*m₀} ∗ Q` reproduces `x / E H` up to the
  remote mass of `ν^{*m₀}`;
* the core deficit estimate: the `σ`-average of a bounded deficit `Ψ` that is nonnegative
  far to the left is controlled by its `ν^{*(m+1)}`-averages, through the explicit Lebesgue
  components of the convolution powers.

All constants are explicit in `κ`, `E H²` and the window bound `2e(1+K)/κ`.
-/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology Classical MeasureTheory
namespace SwingRepair
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

/-- The position-uniform window bound `2e(1+K)/κ` for window lengths at most `K`. -/
def spreadOutWindowBound (κ K : ℝ) : ℝ := 2 * Real.exp 1 * (1 + K) / κ

theorem spreadOutWindowBound_pos {κ K : ℝ} (hκ : 0 < κ) (hK : 0 ≤ K) :
    0 < spreadOutWindowBound κ K := by
  unfold spreadOutWindowBound
  have := Real.exp_pos 1
  positivity

namespace SpreadOutLaw

variable {ν : Measure ℝ} {κ : ℝ}

theorem window_le_ofReal (h : SpreadOutLaw ν κ) {x K : ℝ} (hx : 0 ≤ x) (hxK : x ≤ K) (u : ℝ) :
    ladderRenewalMeasure ν (Ioc (u - x) u) ≤ ENNReal.ofReal (spreadOutWindowBound κ K) := by
  have h1 := h.renewal_Ioc_le_const (u - x) hx
  rw [show u - x + x = u by ring] at h1
  refine h1.trans (ENNReal.ofReal_le_ofReal ?_)
  unfold spreadOutWindowBound
  have := h.pos
  have := Real.exp_pos 1
  gcongr

theorem renewalWindow_le_bound (h : SpreadOutLaw ν κ) {x K : ℝ} (hx : 0 ≤ x) (hxK : x ≤ K)
    (u : ℝ) : renewalWindow ν x u ≤ spreadOutWindowBound κ K :=
  renewalWindow_le _ (spreadOutWindowBound_pos h.pos (hx.trans hxK)).le
    (fun u => h.window_le_ofReal hx hxK u) u

/-! ## The stationary identity transported through the smoothing -/

/-- Transporting `∫ W(b - y) dQ(y) = x/μ` through `σ = ν^{*m₀} ∗ Q`: the only
error comes from the `ν^{*m₀}`-mass beyond `b - x`. -/
theorem integral_window_smoothing_sub_le (h : SpreadOutLaw ν κ)
    {x K : ℝ} (hx : 0 ≤ x) (hxK : x ≤ K) (m₀ : ℕ) (b : ℝ) :
    |(∫ w, renewalWindow ν x (b - w)
        ∂(blackwellSmoothing ν m₀)) -
      x / ladderMean ν| ≤
      (spreadOutWindowBound κ K + K / κ) *
        (measureConvPow ν m₀).real (Ioi (b - K)) := by
  have hprob := h.isProbabilityMeasure
  have hQprob := h.equilibrium_isProbabilityMeasure
  set Q := equilibriumOvershootLaw ν with hQdef
  set ρ := measureConvPow ν m₀ with hρdef
  set P := spreadOutWindowBound κ K with hPdef
  set μ0 := ladderMean ν with hμ0def
  set W : ℝ → ℝ := renewalWindow ν x with hWdef
  have hκ : 0 < κ := h.pos
  have hμ0 : κ ≤ μ0 := h.mean_ge
  have hμ0pos : 0 < μ0 := lt_of_lt_of_le hκ hμ0
  have hP : 0 < P := spreadOutWindowBound_pos h.pos (hx.trans hxK)
  have hW0 : ∀ u, 0 ≤ W u := fun u => renewalWindow_nonneg ν x u
  have hWP : ∀ u, W u ≤ P := fun u =>
    h.renewalWindow_le_bound hx hxK u
  have hxμ : x / μ0 ≤ K / κ := by
    rw [div_le_div_iff₀ hμ0pos hκ]
    nlinarith
  have hxμ0 : 0 ≤ x / μ0 := div_nonneg hx hμ0pos.le
  have hρuniv : ρ.real univ = 1 := by
    rw [Measure.real, measure_univ, ENNReal.toReal_one]
  have hQuniv : Q.real univ = 1 := by
    rw [Measure.real, measure_univ, ENNReal.toReal_one]
  -- the function on the product
  set F : ℝ × ℝ → ℝ := fun p => W (b - (p.1 + p.2)) with hFdef
  have hWmeas : Measurable (fun w => W (b - w)) := measurable_renewalWindow_shift ν x b
  have hFmeas : Measurable F := hWmeas.comp (measurable_fst.add measurable_snd)
  have hFint : Integrable F (ρ.prod Q) := by
    refine (integrable_const P).mono' hFmeas.aestronglyMeasurable ?_
    filter_upwards with p
    rw [Real.norm_eq_abs, abs_of_nonneg (hW0 _)]
    exact hWP _
  -- unfold the convolution
  have hconv : (∫ w, W (b - w) ∂(blackwellSmoothing ν m₀)) =
      ∫ z, ∫ y, W (b - (z + y)) ∂Q ∂ρ := by
    have h1 : (∫ w, W (b - w) ∂(blackwellSmoothing ν m₀)) = ∫ p, F p ∂(ρ.prod Q) := by
      unfold blackwellSmoothing Measure.conv
      rw [integral_map (by fun_prop) hWmeas.aestronglyMeasurable]
    rw [h1, integral_prod F hFint]
  -- the inner integral
  set g : ℝ → ℝ := fun z => ∫ y, W (b - (z + y)) ∂Q with hgdef
  have hg_eq : ∀ z, z ≤ b - x → g z = x / μ0 := by
    intro z hz
    have h := h.integral_equilibrium_window_eq hx
      (show x ≤ b - z by linarith)
    rw [hgdef]
    simp only []
    rw [← h]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    show renewalWindow ν x (b - (z + y)) =
      (ladderRenewalMeasure ν (Ioc (b - z - x - y) (b - z - y))).toReal
    unfold renewalWindow
    rw [show b - (z + y) - x = b - z - x - y by ring, show b - (z + y) = b - z - y by ring]
  have hg0 : ∀ z, 0 ≤ g z := fun z => integral_nonneg fun y => hW0 _
  have hgP : ∀ z, g z ≤ P := by
    intro z
    have hint : Integrable (fun y => W (b - (z + y))) Q := by
      refine (integrable_const P).mono' ?_ ?_
      · exact (hWmeas.comp (measurable_const.add measurable_id)).aestronglyMeasurable
      · filter_upwards with y
        rw [Real.norm_eq_abs, abs_of_nonneg (hW0 _)]
        exact hWP _
    calc g z ≤ ∫ _y, P ∂Q := integral_mono hint (integrable_const P) fun y => hWP _
      _ = P := by rw [integral_const, hQuniv, one_smul]
  have hgint : Integrable g ρ := hFint.integral_prod_left
  -- pointwise deviation
  have hdev : ∀ z, |g z - x / μ0| ≤ (Ioi (b - K)).indicator (fun _ => P + K / κ) z := by
    intro z
    by_cases hz : z ≤ b - x
    · rw [hg_eq z hz, sub_self, abs_zero]
      exact Set.indicator_nonneg (fun _ _ => add_nonneg hP.le (div_nonneg (hx.trans hxK) hκ.le)) z
    · have hz' : z ∈ Ioi (b - K) := by
        show b - K < z
        linarith [not_le.mp hz]
      rw [Set.indicator_of_mem hz', abs_sub_le_iff]
      constructor <;> linarith [hg0 z, hgP z]
  rw [hconv]
  have hsub : (∫ z, g z ∂ρ) - x / μ0 = ∫ z, (g z - x / μ0) ∂ρ := by
    rw [integral_sub hgint (integrable_const _), integral_const, hρuniv, one_smul]
  change |(∫ z, g z ∂ρ) - x / μ0| ≤ _
  rw [hsub]
  calc |∫ z, (g z - x / μ0) ∂ρ| ≤ ∫ z, |g z - x / μ0| ∂ρ := abs_integral_le_integral_abs
    _ ≤ ∫ z, (Ioi (b - K)).indicator (fun _ => P + K / κ) z ∂ρ :=
        integral_mono (hgint.sub (integrable_const _)).abs
          ((integrable_const _).indicator measurableSet_Ioi) hdev
    _ = (P + K / κ) * ρ.real (Ioi (b - K)) := by
        rw [integral_indicator_const _ measurableSet_Ioi, smul_eq_mul, mul_comm]


/--
**The core deficit estimate.**  For a measurable `Ψ` with `-P ≤ Ψ ≤ P`,
nonnegative on `(-∞, S]` with `S ≥ T`, and whose `ν^{*(m+1)}`-averages are at
most `D` for `m ≤ n`, the `σ`-average of `max Ψ 0` is at most `A_n D + R₀`.
-/
theorem deficit_integral_smoothing_le (h : SpreadOutLaw ν κ)
    {K : ℝ} (hK : 0 ≤ K) {η : ℝ} (hη : 0 < η) (hη4 : η ≤ 1 / 4) (n m₀ : ℕ) (hn : 1 ≤ n)
    {T S : ℝ} (hT : 0 < T) (hTS : T ≤ S)
    {Ψ : ℝ → ℝ} (hΨmeas : Measurable Ψ)
    (hΨP : ∀ y, Ψ y ≤ spreadOutWindowBound κ K)
    (hΨlow : ∀ y, -spreadOutWindowBound κ K ≤ Ψ y)
    (hΨnn : ∀ y, y ≤ S → 0 ≤ Ψ y)
    {D : ℝ}
    (hΨint : ∀ m, m < n + 1 →
      ∫ y, Ψ y ∂(measureConvPow ν (m + 1)) ≤ D) :
    ∫ y, max (Ψ y) 0 ∂(blackwellSmoothing ν m₀) ≤
      blackwellAmplification κ η n * D +
        blackwellRemainder κ
          (∫ x, x ^ 2 ∂ν) (spreadOutWindowBound κ K) η T n m₀ := by
  have hprob := h.isProbabilityMeasure
  have hQprob := h.equilibrium_isProbabilityMeasure
  set Q := equilibriumOvershootLaw ν with hQdef
  set B := (∫ x, x ^ 2 ∂ν) with hBdef
  set P := spreadOutWindowBound κ K with hPdef
  have hσprob : IsProbabilityMeasure (blackwellSmoothing ν m₀) :=
    blackwellSmoothing_isProbabilityMeasure ν hQprob m₀
  set σ := blackwellSmoothing ν m₀ with hσdef
  have hκ : 0 < κ := h.pos
  have hκ1 : κ ≤ 1 := h.le_one
  have hB0 : 0 ≤ B := h.sqMoment_nonneg
  have hP : 0 < P := spreadOutWindowBound_pos h.pos hK
  have hν0 : ν (Iio 0) = 0 := h.Iio_zero
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hn2 : (0 : ℝ) < (n : ℝ) / 2 := by positivity
  set Φ : ℝ → ℝ := fun y => max (Ψ y) 0 with hΦdef
  have hΦmeas : Measurable Φ := hΨmeas.max measurable_const
  have hΦ0 : ∀ y, 0 ≤ Φ y := fun y => le_max_right _ _
  have hΦP : ∀ y, Φ y ≤ P := fun y => max_le (hΨP y) hP.le
  have hΦabs : ∀ y, |Φ y| ≤ P := fun y => by
    rw [abs_of_nonneg (hΦ0 y)]
    exact hΦP y
  have hΦint : ∀ (ρ : Measure ℝ) [IsFiniteMeasure ρ], Integrable Φ ρ := by
    intro ρ _
    refine (integrable_const P).mono' hΦmeas.aestronglyMeasurable ?_
    filter_upwards with y
    rw [Real.norm_eq_abs]
    exact hΦabs y
  -- Step B: split `σ` into `(-∞,1)`, `[1,n]`, `(n,∞)`
  have hsplit : ∀ y, Φ y ≤ (Iio (1 : ℝ)).indicator Φ y + (Icc (1 : ℝ) n).indicator Φ y +
      (Ioi (n : ℝ)).indicator Φ y := by
    intro y
    have h1 := Set.indicator_nonneg (fun z _ => hΦ0 z) (s := Iio (1 : ℝ)) y
    have h2 := Set.indicator_nonneg (fun z _ => hΦ0 z) (s := Icc (1 : ℝ) n) y
    have h3 := Set.indicator_nonneg (fun z _ => hΦ0 z) (s := Ioi (n : ℝ)) y
    by_cases hy1 : y < 1
    · rw [Set.indicator_of_mem (show y ∈ Iio 1 from hy1)]
      linarith
    · by_cases hyn : y ≤ n
      · rw [Set.indicator_of_mem (show y ∈ Icc (1 : ℝ) n from ⟨not_lt.mp hy1, hyn⟩)]
        linarith
      · rw [Set.indicator_of_mem (show y ∈ Ioi (n : ℝ) from not_le.mp hyn)]
        linarith
  have hI1 : Integrable ((Iio (1 : ℝ)).indicator Φ) σ :=
    (hΦint σ).indicator measurableSet_Iio
  have hI2 : Integrable ((Icc (1 : ℝ) n).indicator Φ) σ :=
    (hΦint σ).indicator measurableSet_Icc
  have hI3 : Integrable ((Ioi (n : ℝ)).indicator Φ) σ :=
    (hΦint σ).indicator measurableSet_Ioi
  have hB : (∫ y, Φ y ∂σ) ≤ (∫ y, (Iio (1 : ℝ)).indicator Φ y ∂σ) +
      (∫ y, (Icc (1 : ℝ) n).indicator Φ y ∂σ) + ∫ y, (Ioi (n : ℝ)).indicator Φ y ∂σ := by
    have h := integral_mono (hΦint σ) ((hI1.add hI2).add hI3) hsplit
    have e1 := integral_add (μ := σ) (hI1.add hI2) hI3
    have e2 := integral_add (μ := σ) hI1 hI2
    simp only [Pi.add_apply] at e1 e2 h
    linarith
  -- the two mass terms
  have hsetle : ∀ (S : Set ℝ), MeasurableSet S →
      (∫ y, S.indicator Φ y ∂σ) ≤ P * σ.real S := by
    intro S hS
    rw [integral_indicator hS]
    calc (∫ y in S, Φ y ∂σ) ≤ ∫ _y in S, P ∂σ :=
          integral_mono (hΦint _) (integrable_const P) hΦP
      _ = P * σ.real S := by rw [setIntegral_const, smul_eq_mul, mul_comm]
  have hσ1 : σ.real (Iio 1) ≤ (1 - κ) ^ m₀ := by
    have h1 := blackwellSmoothing_Iio_one_le ν hQprob hν0 m₀
    have h2 := h.convPow_Iio_one_le m₀
    exact (ENNReal.toReal_mono (measure_ne_top _ _) h1).trans h2
  have hσn : σ.real (Ioi (n : ℝ)) ≤
      (m₀ : ℝ) ^ 3 * B / ((n : ℝ) / 2) ^ 2 + B / (κ * ((n : ℝ) / 2)) := by
    have h1 := blackwellSmoothing_Ioi_le ν hQprob m₀ ((n : ℝ) / 2)
    rw [show 2 * ((n : ℝ) / 2) = n by ring] at h1
    have h1r : σ.real (Ioi (n : ℝ)) ≤
        (measureConvPow ν m₀).real (Ioi ((n : ℝ) / 2)) + Q.real (Ioi ((n : ℝ) / 2)) := by
      rw [Measure.real, Measure.real, Measure.real, ← ENNReal.toReal_add (measure_ne_top _ _)
        (measure_ne_top _ _)]
      exact ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨measure_ne_top _ _, measure_ne_top _ _⟩) h1
    have h2 := h.convPow_tail_le m₀ hn2
    have h3 := h.equilibrium_tail_le hn2
    linarith
  -- the middle term through the Lebesgue domination
  have hσvol : σ ≤ ENNReal.ofReal (1 / κ) • volume :=
    blackwellSmoothing_le_smul_volume ν (h.equilibrium_le_smul_volume) m₀
  have hIccfin : volume (Icc (1 : ℝ) n) ≠ ⊤ := by
    rw [Real.volume_Icc]
    exact ENNReal.ofReal_ne_top
  have hΦIcc : IntegrableOn Φ (Icc (1 : ℝ) n) volume :=
    integrableOn_of_bounded_of_finite hΦmeas hΦabs hIccfin
  have hmid : (∫ y, (Icc (1 : ℝ) n).indicator Φ y ∂σ) ≤
      (1 / κ) * ∫ y in Icc (1 : ℝ) n, Φ y := by
    rw [integral_indicator measurableSet_Icc]
    have hle : σ.restrict (Icc (1 : ℝ) n) ≤
        ENNReal.ofReal (1 / κ) • volume.restrict (Icc (1 : ℝ) n) := by
      rw [← Measure.restrict_smul]
      exact Measure.restrict_mono subset_rfl hσvol
    have hint : Integrable Φ (ENNReal.ofReal (1 / κ) • volume.restrict (Icc (1 : ℝ) n)) :=
      hΦIcc.smul_measure ENNReal.ofReal_ne_top
    calc (∫ y in Icc (1 : ℝ) n, Φ y ∂σ)
        ≤ ∫ y, Φ y ∂(ENNReal.ofReal (1 / κ) • volume.restrict (Icc (1 : ℝ) n)) :=
          integral_mono_measure hle (Filter.Eventually.of_forall hΦ0) hint
      _ = (1 / κ) * ∫ y in Icc (1 : ℝ) n, Φ y := by
          rw [integral_smul_measure, smul_eq_mul, ENNReal.toReal_ofReal (by positivity)]
  -- Step C: cover `[1,n]` by the gap and the minorizing intervals
  have hgapfin : volume (Ioo (2 : ℝ) (2 + 2 * η)) ≠ ⊤ := by
    rw [Real.volume_Ioo]
    exact ENNReal.ofReal_ne_top
  have hIfin : ∀ m : ℕ, volume (minorIcc η m) ≠ ⊤ := by
    intro m
    unfold minorIcc
    rw [Real.volume_Icc]
    exact ENNReal.ofReal_ne_top
  have hImeas : ∀ m : ℕ, MeasurableSet (minorIcc η m) := fun m => by
    unfold minorIcc
    exact measurableSet_Icc
  have hcover : ∀ y, (Icc (1 : ℝ) n).indicator Φ y ≤
      (Ioo (2 : ℝ) (2 + 2 * η)).indicator Φ y +
        ∑ m ∈ Finset.range (n + 1), (minorIcc η m).indicator Φ y := by
    intro y
    have hgap0 := Set.indicator_nonneg (fun z _ => hΦ0 z) (s := Ioo (2 : ℝ) (2 + 2 * η)) y
    have hsum0 : 0 ≤ ∑ m ∈ Finset.range (n + 1), (minorIcc η m).indicator Φ y :=
      Finset.sum_nonneg fun m _ => Set.indicator_nonneg (fun z _ => hΦ0 z) y
    by_cases hy : y ∈ Icc (1 : ℝ) n
    · rw [Set.indicator_of_mem hy]
      by_cases hgap : y ∈ Ioo (2 : ℝ) (2 + 2 * η)
      · rw [Set.indicator_of_mem hgap]
        linarith
      · have hor : y ≤ 2 ∨ 2 + 2 * η ≤ y := by
          rcases le_or_gt y 2 with h2 | h2
          · exact Or.inl h2
          · right
            by_contra h3
            exact hgap ⟨h2, not_le.mp h3⟩
        obtain ⟨m, hym, hmy⟩ := exists_mem_minorIcc hη hη4 hy.1 hor
        have hmn : m ∈ Finset.range (n + 1) := by
          rw [Finset.mem_range]
          have : (m : ℝ) ≤ n := hmy.trans hy.2
          have : m ≤ n := by exact_mod_cast this
          omega
        have hterm : Φ y = (minorIcc η m).indicator Φ y := (Set.indicator_of_mem hym Φ).symm
        have hle : (minorIcc η m).indicator Φ y ≤
            ∑ k ∈ Finset.range (n + 1), (minorIcc η k).indicator Φ y :=
          Finset.single_le_sum (fun k _ => Set.indicator_nonneg (fun z _ => hΦ0 z) y) hmn
        linarith
    · rw [Set.indicator_of_notMem hy]
      linarith
  have hgapint : Integrable ((Ioo (2 : ℝ) (2 + 2 * η)).indicator Φ) volume :=
    (integrableOn_of_bounded_of_finite hΦmeas hΦabs hgapfin).integrable_indicator
      measurableSet_Ioo
  have hIint : ∀ m : ℕ, Integrable ((minorIcc η m).indicator Φ) volume := fun m =>
    (integrableOn_of_bounded_of_finite hΦmeas hΦabs (hIfin m)).integrable_indicator
      (hImeas m)
  have hC : (∫ y in Icc (1 : ℝ) n, Φ y) ≤
      (∫ y in Ioo (2 : ℝ) (2 + 2 * η), Φ y) +
        ∑ m ∈ Finset.range (n + 1), ∫ y in minorIcc η m, Φ y := by
    rw [← integral_indicator measurableSet_Icc, ← integral_indicator measurableSet_Ioo]
    have hsumint : Integrable
        (fun y => ∑ m ∈ Finset.range (n + 1), (minorIcc η m).indicator Φ y) volume :=
      integrable_finsetSum _ fun m _ => hIint m
    have hsum_eq : (∑ m ∈ Finset.range (n + 1), ∫ y in minorIcc η m, Φ y) =
        ∫ y, ∑ m ∈ Finset.range (n + 1), (minorIcc η m).indicator Φ y := by
      rw [integral_finsetSum _ fun m _ => hIint m]
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [integral_indicator (hImeas m)]
    rw [hsum_eq, ← integral_add hgapint hsumint]
    exact integral_mono (hΦIcc.integrable_indicator measurableSet_Icc) (hgapint.add hsumint)
      hcover
  have hgap : (∫ y in Ioo (2 : ℝ) (2 + 2 * η), Φ y) ≤ P * (2 * η) := by
    have hfin : IsFiniteMeasure (volume.restrict (Ioo (2 : ℝ) (2 + 2 * η))) :=
      ⟨by rw [Measure.restrict_apply_univ]; exact lt_top_iff_ne_top.mpr hgapfin⟩
    calc (∫ y in Ioo (2 : ℝ) (2 + 2 * η), Φ y) ≤ ∫ _y in Ioo (2 : ℝ) (2 + 2 * η), P :=
          integral_mono (integrableOn_of_bounded_of_finite hΦmeas hΦabs hgapfin)
            (integrable_const P) hΦP
      _ = P * (2 * η) := by
          rw [setIntegral_const, smul_eq_mul, Measure.real, Real.volume_Ioo,
            ENNReal.toReal_ofReal (by linarith), mul_comm]
          congr 1
          ring
  -- each minorizing interval is dominated by a convolution power
  have hIm : ∀ m : ℕ, (∫ y in minorIcc η m, Φ y) ≤
      (1 / minorConst κ η m) * ∫ y, Φ y ∂(measureConvPow ν (m + 1)) := by
    intro m
    have hc := minorConst_pos hκ hη m
    have hmin := measureConvPow_ge_minor ν hκ.le hη hη4
      (h.minor) m
    have hint : Integrable Φ (measureConvPow ν (m + 1)) := hΦint _
    have hstep : (∫ y, Φ y ∂(ENNReal.ofReal (minorConst κ η m) • volume.restrict (minorIcc η m))) ≤
        ∫ y, Φ y ∂(measureConvPow ν (m + 1)) :=
      integral_mono_measure hmin (Filter.Eventually.of_forall hΦ0) hint
    rw [integral_smul_measure, smul_eq_mul, ENNReal.toReal_ofReal hc.le] at hstep
    rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ hc, mul_comm]
    exact hstep
  -- Step D: from `Φ` back to `Ψ`
  have hD : ∀ m : ℕ, m < n + 1 → (∫ y, Φ y ∂(measureConvPow ν (m + 1))) ≤
      D + P * (((m + 1 : ℕ) : ℝ) ^ 3 * B / T ^ 2) := by
    intro m hm
    have hpt : ∀ y, Φ y ≤ Ψ y + (Ioi S).indicator (fun _ => P) y := by
      intro y
      by_cases hy : y ≤ S
      · rw [Set.indicator_of_notMem (show y ∉ Ioi S from not_lt.mpr hy), add_zero, hΦdef]
        simp only []
        rw [max_eq_left (hΨnn y hy)]
      · rw [Set.indicator_of_mem (show y ∈ Ioi S from not_le.mp hy)]
        refine max_le (by linarith [hP]) ?_
        linarith [hΨlow y]
    have hΨint' : Integrable Ψ (measureConvPow ν (m + 1)) := by
      refine (integrable_const P).mono' hΨmeas.aestronglyMeasurable ?_
      filter_upwards with y
      rw [Real.norm_eq_abs, abs_le]
      exact ⟨hΨlow y, hΨP y⟩
    have hind : Integrable ((Ioi S).indicator (fun _ : ℝ => P)) (measureConvPow ν (m + 1)) :=
      (integrable_const P).indicator measurableSet_Ioi
    have htail : (measureConvPow ν (m + 1)).real (Ioi S) ≤
        ((m + 1 : ℕ) : ℝ) ^ 3 * B / T ^ 2 := by
      refine (measureReal_mono (Ioi_subset_Ioi hTS) (measure_ne_top _ _)).trans ?_
      exact h.convPow_tail_le (m + 1) hT
    calc (∫ y, Φ y ∂(measureConvPow ν (m + 1)))
        ≤ ∫ y, (Ψ y + (Ioi S).indicator (fun _ => P) y) ∂(measureConvPow ν (m + 1)) :=
          integral_mono (hΦint _) (hΨint'.add hind) hpt
      _ = (∫ y, Ψ y ∂(measureConvPow ν (m + 1))) +
          P * (measureConvPow ν (m + 1)).real (Ioi S) := by
          rw [integral_add hΨint' hind, integral_indicator_const _ measurableSet_Ioi,
            smul_eq_mul, mul_comm]
      _ ≤ D + P * (((m + 1 : ℕ) : ℝ) ^ 3 * B / T ^ 2) := by
          have := hΨint m hm
          have := mul_le_mul_of_nonneg_left htail hP.le
          linarith
  -- assemble
  have hsumle : (∑ m ∈ Finset.range (n + 1), ∫ y in minorIcc η m, Φ y) ≤
      ∑ m ∈ Finset.range (n + 1),
        (1 / minorConst κ η m) * (D + P * (((m + 1 : ℕ) : ℝ) ^ 3 * B / T ^ 2)) := by
    refine Finset.sum_le_sum fun m hm => ?_
    refine (hIm m).trans ?_
    exact mul_le_mul_of_nonneg_left (hD m (Finset.mem_range.mp hm))
      (le_of_lt (one_div_pos.mpr (minorConst_pos hκ hη m)))
  have hsum_split : (∑ m ∈ Finset.range (n + 1),
        (1 / minorConst κ η m) * (D + P * (((m + 1 : ℕ) : ℝ) ^ 3 * B / T ^ 2))) =
      (∑ m ∈ Finset.range (n + 1), 1 / minorConst κ η m) * D +
        ∑ m ∈ Finset.range (n + 1),
          (1 / minorConst κ η m) * (P * (((m + 1 : ℕ) : ℝ) ^ 3 * B / T ^ 2)) := by
    rw [Finset.sum_mul, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun m _ => ?_
    ring
  have hκinv : 0 < 1 / κ := one_div_pos.mpr hκ
  have h1 := hsetle (Iio 1) measurableSet_Iio
  have h3 := hsetle (Ioi (n : ℝ)) measurableSet_Ioi
  have h1' : (∫ y, (Iio (1 : ℝ)).indicator Φ y ∂σ) ≤ P * (1 - κ) ^ m₀ :=
    h1.trans (mul_le_mul_of_nonneg_left hσ1 hP.le)
  have h3' : (∫ y, (Ioi (n : ℝ)).indicator Φ y ∂σ) ≤
      P * ((m₀ : ℝ) ^ 3 * B / ((n : ℝ) / 2) ^ 2 + B / (κ * ((n : ℝ) / 2))) :=
    h3.trans (mul_le_mul_of_nonneg_left hσn hP.le)
  have hmid' : (∫ y, (Icc (1 : ℝ) n).indicator Φ y ∂σ) ≤
      (1 / κ) * (P * (2 * η) +
        ((∑ m ∈ Finset.range (n + 1), 1 / minorConst κ η m) * D +
          ∑ m ∈ Finset.range (n + 1),
            (1 / minorConst κ η m) * (P * (((m + 1 : ℕ) : ℝ) ^ 3 * B / T ^ 2)))) := by
    refine hmid.trans (mul_le_mul_of_nonneg_left ?_ hκinv.le)
    rw [← hsum_split]
    linarith [hC, hgap, hsumle]
  unfold blackwellAmplification blackwellRemainder
  show (∫ y, Φ y ∂σ) ≤ _
  linarith [hB, h1', h3', hmid']

end SpreadOutLaw

end SwingRepair
