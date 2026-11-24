import PLAStochastic.Swing.DenseSampling.Empirical.WeakConvergence

/-! # Brownian empirical boundary law and vanishing long-segment proportion -/
noncomputable section
open MeasureTheory ProbabilityTheory BrownianAffine Filter Set
open scoped NNReal ENNReal Topology
namespace SwingRepair
set_option backward.isDefEq.respectTransparency false

def brownianNativeEmpiricalMeasure {Ω : Type*} (B : ℝ≥0 → Ω → ℝ)
    (ε H : ℝ) (h : ℝ≥0) (ω : Ω) : ProbabilityMeasure ℝ :=
  nativeCompletedEmpiricalMeasure (fun j => (j : ℝ) * h)
    (fun j => B ((j : ℝ≥0) * h) ω) ε (brownianNativeMeshStream B ε H h ω)

def brownianNativeLongCompletedProportion {Ω : Type*} (B : ℝ≥0 → Ω → ℝ)
    (ε H a : ℝ) (h : ℝ≥0) (ω : Ω) : ℝ :=
  (nativeLongCompletedCount (fun j => (j : ℝ) * h)
    (brownianNativeMeshStream B ε H h ω) a : ℝ) /
    (((brownianNativeMeshStream B ε H h ω).length - 1 : ℕ) : ℝ)

/-- The empirical part of Theorem 2.3 for the actual native constrained-SSE
algorithm, with no assumed limiting distribution or segment-count divergence.
The same full-measure set works for every horizon past the first pinch and every
positive long-duration threshold. -/
theorem brownian_native_empirical_and_long_proportion_ae {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B μ)
    {ε : ℝ} (hε : 0 < ε) {ι : Type*} {l : Filter ι} {h : ι → ℝ≥0}
    (hh : ∀ i, h i ≠ 0) (hconv : Tendsto (fun i => (h i : ℝ)) l (𝓝 0)) :
    ∀ᵐ ω ∂μ, ∀ H : ℝ, (anchoredProcessLifetime B ε ω).toReal < H →
      Tendsto (fun i => brownianNativeEmpiricalMeasure B ε H (h i) ω)
        l (𝓝 fairBoundaryMeasure) ∧
      ∀ a : ℝ, 0 < a → Tendsto
        (fun i => brownianNativeLongCompletedProportion B ε H a (h i) ω) l (𝓝 0) := by
  filter_upwards [hB.cont, brownian_nativeCompletedCount_atTop_ae hB hε hh hconv]
    with ω hc hR
  intro H hH
  have hT : 0 ≤ H := ENNReal.toReal_nonneg.trans hH.le
  have hh' (i : ι) : 0 < (h i : ℝ) := by exact_mod_cast (pos_iff_ne_zero.mpr (hh i))
  have hN (i : ι) : (⌊H / (h i : ℝ)⌋₊ : ℝ) * h i ≤ H :=
    (le_div_iff₀ (hh' i)).mp (Nat.floor_le (div_nonneg hT (hh' i).le))
  have hy (i : ι) : (fun j : ℕ => B ((j : ℝ≥0) * h i) ω) =
      (fun j : ℕ => processPath B ω ((j : ℝ) * h i)) := by
    funext j
    simpa only [NNReal.coe_mul, NNReal.coe_natCast] using!
      (processPath_apply_of_continuous hc ((j : ℝ≥0) * h i)).symm
  have hcount : Tendsto (fun i => nativeCompletedCount (fun j => (j : ℝ) * h i)
      (fun j => processPath B ω ((j : ℝ) * h i)) ε ⌊H / (h i : ℝ)⌋₊) l atTop := by
    simpa only [hy] using hR H hH
  constructor
  · have ht := native_completed_empiricalMeasure_tendsto (processPath B ω) hT hε hh' hconv hN hcount
    simpa only [brownianNativeEmpiricalMeasure, brownianNativeMeshStream, hy] using ht
  · intro a ha
    have ht := native_long_completed_proportion_tendsto_zero (processPath B ω) hε.le ha hh' hN hcount
    simpa only [brownianNativeLongCompletedProportion, brownianNativeMeshStream,
      nativeCompletedCount, hy] using ht

end SwingRepair
