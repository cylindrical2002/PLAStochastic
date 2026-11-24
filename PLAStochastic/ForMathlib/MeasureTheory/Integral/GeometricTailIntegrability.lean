import Mathlib.Probability.Moments.IntegrableExpMul
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Tactic

/-!
# Integrability from a geometric tail

These results retain an extended nonnegative random variable until its infinite-value
set has been proved null. A geometric bound on the closed tails at times `16 * n`
implies a positive exponential moment and all finite real moment orders of `X.toReal`.
-/

open MeasureTheory Filter
open scoped ENNReal NNReal Topology

namespace BrownianAffine

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
  {X : Ω → ℝ≥0∞} {q : ℝ}

/-- The closed-tail estimate supplied by the independent Gaussian block argument. -/
def GeometricTail16 (μ : Measure Ω) (X : Ω → ℝ≥0∞) (q : ℝ) : Prop :=
  ∀ n : ℕ, μ {ω | (16 : ℝ≥0∞) * n ≤ X ω} ≤ ENNReal.ofReal (q ^ n)

/-- Convert an extended-real geometric ratio to the real parameter of `GeometricTail16`. -/
theorem geometricTail16_of_ennreal {r : ℝ≥0∞} (hr : r < 1)
    (h : ∀ n : ℕ, μ {ω | (16 : ℝ≥0∞) * n ≤ X ω} ≤ r ^ n) :
    GeometricTail16 μ X r.toReal := by
  intro n
  simpa only [ENNReal.ofReal_pow ENNReal.toReal_nonneg,
    ENNReal.ofReal_toReal (ne_top_of_lt hr)] using h n

/-- A geometric tail bound rules out positive mass at infinity before `toReal` is used. -/
theorem GeometricTail16.ae_ne_top (h : GeometricTail16 μ X q)
    (hq₀ : 0 ≤ q) (hq₁ : q < 1) : ∀ᵐ ω ∂μ, X ω ≠ ∞ := by
  have hlim : Tendsto (fun n : ℕ => ENNReal.ofReal (q ^ n)) atTop (𝓝 0) := by
    simpa using! ENNReal.continuous_ofReal.continuousAt.tendsto.comp
      (tendsto_pow_atTop_nhds_zero_of_lt_one hq₀ hq₁)
  have hm : μ {ω | X ω = ∞} = 0 := by
    apply le_antisymm _ zero_le
    apply ge_of_tendsto hlim
    exact Eventually.of_forall fun n => (measure_mono (by
      intro ω hω
      change X ω = ∞ at hω
      change (16 : ℝ≥0∞) * n ≤ X ω
      rw [hω]
      exact le_top)).trans (h n)
  simpa only [ae_iff, not_not] using hm

/-- A monotone transform is bounded by a sum of tail indicators; no moment is assumed. -/
theorem GeometricTail16.lintegral_toReal_le (h : GeometricTail16 μ X q)
    (hX : AEMeasurable X μ) (w : ℝ → ℝ≥0∞)
    (hw : MonotoneOn w (Set.Ici 0)) :
    ∫⁻ ω, w (X ω).toReal ∂μ ≤
      ∑' n : ℕ, w (16 * ((n : ℝ) + 1)) * ENNReal.ofReal (q ^ n) := by
  classical
  let s : ℕ → Set Ω := fun n => {ω | (16 : ℝ≥0∞) * n ≤ X ω}
  let F : ℕ → Ω → ℝ≥0∞ := fun n =>
    (s n).indicator (fun _ => w (16 * ((n : ℝ) + 1)))
  have hs (n : ℕ) : NullMeasurableSet (s n) μ :=
    hX.nullMeasurableSet_preimage measurableSet_Ici
  have hF (n : ℕ) : AEMeasurable (F n) μ :=
    aemeasurable_const.indicator₀ (hs n)
  calc
    ∫⁻ ω, w (X ω).toReal ∂μ ≤ ∫⁻ ω, ∑' n : ℕ, F n ω ∂μ := by
      apply lintegral_mono
      intro ω
      let y : ℝ := (X ω).toReal
      let n : ℕ := ⌊y / 16⌋₊
      have hy : 0 ≤ y := ENNReal.toReal_nonneg
      have hlo : 16 * (n : ℝ) ≤ y := by
        have := Nat.floor_le (div_nonneg hy (by norm_num : (0 : ℝ) ≤ 16))
        dsimp [n]
        linarith
      have hhi : y ≤ 16 * ((n : ℝ) + 1) := by
        have := Nat.lt_floor_add_one (y / 16)
        dsimp [n]
        linarith
      have hmem : ω ∈ s n := by
        change (16 : ℝ≥0∞) * n ≤ X ω
        have := (ENNReal.ofReal_le_ofReal hlo).trans (ENNReal.ofReal_toReal_le)
        simpa [y, ENNReal.ofReal_mul] using this
      calc
        w y ≤ w (16 * ((n : ℝ) + 1)) := hw hy (show 0 ≤ 16 * ((n : ℝ) + 1) by positivity) hhi
        _ = F n ω := by
          exact (Set.indicator_of_mem hmem (fun _ => w (16 * ((n : ℝ) + 1)))).symm
        _ ≤ ∑' n : ℕ, F n ω := ENNReal.le_tsum n
    _ = ∑' n : ℕ, w (16 * ((n : ℝ) + 1)) * μ (s n) := by
      rw [lintegral_tsum hF]
      apply tsum_congr
      intro n
      exact lintegral_indicator_const₀ (hs n) _
    _ ≤ ∑' n : ℕ, w (16 * ((n : ℝ) + 1)) * ENNReal.ofReal (q ^ n) := by
      exact ENNReal.tsum_le_tsum fun n => mul_le_mul_right (h n) _

/-- Every nonnegative exponential rate whose geometric ratio is below one is integrable. -/
theorem GeometricTail16.integrable_exp (h : GeometricTail16 μ X q)
    (hX : AEMeasurable X μ) (hq₀ : 0 ≤ q) {θ : ℝ} (hθ : 0 ≤ θ)
    (hr : Real.exp (16 * θ) * q < 1) :
    Integrable (fun ω => Real.exp (θ * (X ω).toReal)) μ := by
  have hgeom : Summable (fun n : ℕ =>
      Real.exp (16 * θ) * (Real.exp (16 * θ) * q) ^ n) :=
    (summable_geometric_of_lt_one (mul_nonneg (Real.exp_nonneg _) hq₀) hr).mul_left _
  have hsum : (∑' n : ℕ, ENNReal.ofReal (Real.exp (θ * (16 * ((n : ℝ) + 1)))) *
      ENNReal.ofReal (q ^ n)) < ∞ := by
    have heq (n : ℕ) :
        Real.exp (θ * (16 * ((n : ℝ) + 1))) * q ^ n =
          Real.exp (16 * θ) * (Real.exp (16 * θ) * q) ^ n := by
      rw [show θ * (16 * ((n : ℝ) + 1)) = 16 * θ + n * (16 * θ) by ring,
        Real.exp_add, Real.exp_nat_mul, mul_pow]
      ring
    simpa only [← ENNReal.ofReal_mul (Real.exp_nonneg _), heq] using
      hgeom.tsum_ofReal_lt_top
  have hbound := h.lintegral_toReal_le hX
    (fun y => ENNReal.ofReal (Real.exp (θ * y))) (by
      intro a _ b _ hab
      exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hab hθ)))
  apply (lintegral_ofReal_ne_top_iff_integrable
    (hX.ennreal_toReal.const_mul θ |>.exp |>.aestronglyMeasurable)
    (Eventually.of_forall fun _ => Real.exp_nonneg _)).mp
  exact (hbound.trans_lt hsum).ne

/-- A geometric ratio strictly below one allows a strictly positive exponential rate. -/
theorem exists_pos_exponential_rate {q : ℝ} (hq : q < 1) :
    ∃ θ : ℝ, 0 < θ ∧ Real.exp (16 * θ) * q < 1 := by
  have hc : Continuous (fun θ : ℝ => Real.exp (16 * θ) * q) := by fun_prop
  have he : ∀ᶠ θ : ℝ in 𝓝 0, Real.exp (16 * θ) * q < 1 :=
    hc.continuousAt.tendsto.eventually_lt_const (by simpa using hq)
  obtain ⟨δ, hδ, heδ⟩ := Metric.eventually_nhds_iff.mp he
  refine ⟨δ / 2, by positivity, heδ ?_⟩
  rw [Real.dist_eq, sub_zero, abs_of_pos (half_pos hδ)]
  exact half_lt_self hδ

/-- A genuine exponential moment follows from the tail bound and measurability alone. -/
theorem GeometricTail16.exists_integrable_exp (h : GeometricTail16 μ X q)
    (hX : AEMeasurable X μ) (hq₀ : 0 ≤ q) (hq₁ : q < 1) :
    ∃ θ : ℝ, 0 < θ ∧ Integrable (fun ω => Real.exp (θ * (X ω).toReal)) μ := by
  obtain ⟨θ, hθ, hr⟩ := exists_pos_exponential_rate hq₁
  exact ⟨θ, hθ, h.integrable_exp hX hq₀ hθ.le hr⟩

/-- For a nonnegative random variable, decreasing the exponential rate preserves integrability. -/
theorem integrable_exp_toReal_of_le (hX : AEMeasurable X μ) {a b : ℝ}
    (ha : Integrable (fun ω => Real.exp (a * (X ω).toReal)) μ) (hba : b ≤ a) :
    Integrable (fun ω => Real.exp (b * (X ω).toReal)) μ := by
  apply ha.mono' (hX.ennreal_toReal.const_mul b |>.exp |>.aestronglyMeasurable)
  exact Eventually.of_forall fun ω => by
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hba ENNReal.toReal_nonneg)

/-- The moment-generating function is finite throughout a neighborhood of zero. -/
theorem GeometricTail16.exists_integrable_exp_neighborhood (h : GeometricTail16 μ X q)
    (hX : AEMeasurable X μ) (hq₀ : 0 ≤ q) (hq₁ : q < 1) :
    ∃ θ : ℝ, 0 < θ ∧ ∀ t : ℝ, |t| ≤ θ →
      Integrable (fun ω => Real.exp (t * (X ω).toReal)) μ := by
  obtain ⟨θ, hθ, hpos⟩ := h.exists_integrable_exp hX hq₀ hq₁
  exact ⟨θ, hθ, fun t ht => integrable_exp_toReal_of_le hX hpos
    ((le_abs_self t).trans ht)⟩

/-- All finite `Lᵖ` orders, including the cubic moment needed in the appendix. -/
theorem GeometricTail16.memLp_toReal (h : GeometricTail16 μ X q)
    (hX : AEMeasurable X μ) (hq₀ : 0 ≤ q) (hq₁ : q < 1)
    (p : ℝ≥0∞) (hp : p ≠ ∞) : MemLp (fun ω => (X ω).toReal) p μ := by
  obtain ⟨θ, hθ, hpos⟩ := h.exists_integrable_exp hX hq₀ hq₁
  have hneg := integrable_exp_toReal_of_le hX hpos
    (show -θ ≤ θ by linarith)
  by_cases hp₀ : p = 0
  · subst p
    exact memLp_zero_iff_aestronglyMeasurable.mpr hX.ennreal_toReal.aestronglyMeasurable
  apply (integrable_norm_rpow_iff hX.ennreal_toReal.aestronglyMeasurable hp₀ hp).mp
  simpa only [Real.norm_eq_abs] using
    ProbabilityTheory.integrable_rpow_abs_of_integrable_exp_mul hθ.ne' hpos hneg
      (p := p.toReal) ENNReal.toReal_nonneg

/-- Every nonnegative real raw moment is a genuine integrable function. -/
theorem GeometricTail16.integrable_rpow_toReal (h : GeometricTail16 μ X q)
    (hX : AEMeasurable X μ) (hq₀ : 0 ≤ q) (hq₁ : q < 1)
    {p : ℝ} (hp : 0 ≤ p) : Integrable (fun ω => (X ω).toReal ^ p) μ := by
  obtain ⟨θ, hθ, hpos⟩ := h.exists_integrable_exp hX hq₀ hq₁
  exact ProbabilityTheory.integrable_rpow_of_integrable_exp_mul hθ.ne' hpos
    (integrable_exp_toReal_of_le hX hpos (show -θ ≤ θ by linarith)) hp

/-- In particular every natural power, including the third and fourth, is integrable. -/
theorem GeometricTail16.integrable_pow_toReal (h : GeometricTail16 μ X q)
    (hX : AEMeasurable X μ) (hq₀ : 0 ≤ q) (hq₁ : q < 1)
    (n : ℕ) : Integrable (fun ω => (X ω).toReal ^ n) μ := by
  simpa only [Real.rpow_natCast] using h.integrable_rpow_toReal hX hq₀ hq₁
    (show (0 : ℝ) ≤ n by positivity)

end BrownianAffine
