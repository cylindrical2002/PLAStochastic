import PLAStochastic.Swing.DenseSampling.PostFirst.MaximumLimit
import PLAStochastic.Swing.Algorithm.Equivariance
import PLAStochastic.Affine.Error.BrownianScaling

/-! # Arbitrary positive tolerances by exact Brownian and algorithmic rescaling -/
noncomputable section
open Classical
open MeasureTheory ProbabilityTheory BrownianAffine Filter Set
open scoped NNReal ENNReal Topology
namespace SwingRepair
set_option backward.isDefEq.respectTransparency false

/-- This is a pointwise equality of the actual finite output maxima, not merely
an equality in distribution or a scaling assertion for an idealized cone. -/
theorem brownian_nativePostFirstMaximum_normalized {Ω : Type*} (B : ℝ≥0 → Ω → ℝ)
    {c : ℝ≥0} (hc : 0 < c) (h : ℝ≥0) (n : ℕ) (ω : Ω) :
    nativePostFirstMaximum (fun j => (j : ℝ)*(h : ℝ))
      (nativeStream (fun j => (j : ℝ)*(h : ℝ)) (fun j => B ((j : ℝ≥0)*h) ω) (Real.sqrt (c : ℝ)) n) =
    (c : ℝ)*nativePostFirstMaximum (fun j => (j : ℝ)*((h/c : ℝ≥0) : ℝ))
      (nativeStream (fun j => (j : ℝ)*((h/c : ℝ≥0) : ℝ))
        (fun j => normalizedBrownian B c ((j : ℝ≥0)*(h/c)) ω) 1 n) := by
  let t : ℕ → ℝ := fun j => (j : ℝ)*((h/c : ℝ≥0) : ℝ)
  let y : ℕ → ℝ := fun j => normalizedBrownian B c ((j : ℝ≥0)*(h/c)) ω
  have hcR : (0 : ℝ) < c := by exact_mod_cast hc
  have hd : 0 < Real.sqrt (c : ℝ) := Real.sqrt_pos.mpr hcR
  have ht : (fun j => (c : ℝ)*t j) = (fun j : ℕ => (j : ℝ)*(h : ℝ)) := by
    funext j
    dsimp only [t]
    rw [NNReal.coe_div]
    field_simp
  have hy : (fun j => Real.sqrt (c : ℝ)*y j) = (fun j : ℕ => B ((j : ℝ≥0)*h) ω) := by
    funext j
    dsimp only [y, normalizedBrownian]
    have he : c*((j : ℝ≥0)*(h/c)) = (j : ℝ≥0)*h := by field_simp
    rw [he, mul_inv_cancel_left₀ hd.ne']
  have hs := nativeStream_scaling t y 1 n hcR hd
  rw [ht, hy, mul_one] at hs
  rw [hs, ← ht]
  exact nativePostFirstMaximum_scaling t _ hcR

/-- The actual native maximum tail converges for every positive tolerance. -/
theorem brownian_nativePostFirstMaximum_tail_tendsto_zero_tolerance {Ω ι : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B μ)
    {ε T a : ℝ} (hε : 0 < ε) (hT : 0 ≤ T) (ha : 0 < a)
    {l : Filter ι} [l.IsCountablyGenerated] {h : ι → ℝ≥0}
    (hh : ∀ i, 0 < h i) (hconv : Tendsto (fun i => (h i : ℝ)) l (𝓝 0))
    {n : ι → ℕ} (hnT : ∀ i, (n i : ℝ)*(h i : ℝ) ≤ T) :
    Tendsto (fun i => μ.real {ω | a ≤ nativePostFirstMaximum (fun j => (j : ℝ)*(h i : ℝ))
      (nativeStream (fun j => (j : ℝ)*(h i : ℝ)) (fun j => B ((j : ℝ≥0)*h i) ω) ε (n i))}) l (𝓝 0) := by
  let c : ℝ≥0 := ⟨ε^2, sq_nonneg ε⟩
  have hc : 0 < c := by exact_mod_cast (sq_pos_of_pos hε)
  have hcR : (0 : ℝ) < c := by exact_mod_cast hc
  have hroot : Real.sqrt (c : ℝ) = ε := Real.sqrt_sq hε.le
  have hB' := isBrownianReal_normalized hB hc.ne'
  have hconv' : Tendsto (fun i => ((h i/c : ℝ≥0) : ℝ)) l (𝓝 0) := by
    simpa only [NNReal.coe_div, zero_div] using hconv.div_const (c : ℝ)
  have hnT' (i : ι) : (n i : ℝ)*((h i/c : ℝ≥0) : ℝ) ≤ T/(c : ℝ) := by
    rw [NNReal.coe_div, ← mul_div_assoc]
    exact div_le_div_of_nonneg_right (hnT i) hcR.le
  have ht := brownian_nativePostFirstMaximum_tail_tendsto_zero hB'
    (div_nonneg hT hcR.le) (div_pos ha hcR) (fun i => div_pos (hh i) hc) hconv' hnT'
  convert ht using 1
  funext i
  congr 1
  ext ω
  have he := brownian_nativePostFirstMaximum_normalized B hc (h i) (n i) ω
  rw [hroot] at he
  simp only [Set.mem_ofPred_eq]
  rw [he]
  rw [div_le_iff₀ hcR]
  constructor <;> intro hx <;> nlinarith

/-- The full positive-tolerance maximum convergence result for the actual
constrained-SSE implementation, with its original finite-horizon EOF convention. -/
theorem brownian_nativePostFirstMaximum_tendstoInMeasure {Ω ι : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B μ)
    {ε T : ℝ} (hε : 0 < ε) (hT : 0 ≤ T) {l : Filter ι} [l.IsCountablyGenerated]
    {h : ι → ℝ≥0} (hh : ∀ i, 0 < h i) (hconv : Tendsto (fun i => (h i : ℝ)) l (𝓝 0)) :
    TendstoInMeasure μ (fun i => brownianNativePostFirstMaximum B ε T (h i)) l (fun _ => 0) := by
  let : IsProbabilityMeasure μ := hB.isGaussianProcess.isProbabilityMeasure
  apply tendstoInMeasure_iff_norm.mpr
  intro a ha
  have hnT (i : ι) : (⌊T/(h i : ℝ)⌋₊ : ℝ)*(h i : ℝ) ≤ T :=
    (le_div_iff₀ (show (0 : ℝ) < h i by exact_mod_cast hh i)).mp
      (Nat.floor_le (div_nonneg hT (h i).coe_nonneg))
  have ht := brownian_nativePostFirstMaximum_tail_tendsto_zero_tolerance hB hε hT ha hh hconv hnT
  have hp := ENNReal.continuous_ofReal.continuousAt.tendsto.comp ht
  simpa only [Function.comp_def, sub_zero, Real.norm_eq_abs, ENNReal.ofReal_zero,
    measureReal_def, ENNReal.ofReal_toReal (measure_ne_top μ _),
    brownianNativePostFirstMaximum, brownianNativeMeshStream,
    abs_of_nonneg (nativePostFirstMaximum_nonneg _ _)] using hp

/-- The time-weighted conclusion now follows from the proved maximum theorem,
with no assumed convergence of the maximum remaining. -/
theorem brownian_native_timeweighted_tendsto {Ω ι : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B μ)
    {ε T a : ℝ} (hε : 0 < ε) (hT : 0 ≤ T) (ha : 0 < a)
    {l : Filter ι} [l.IsCountablyGenerated] {h : ι → ℝ≥0}
    (hh : ∀ i, 0 < h i) (hconv : Tendsto (fun i => (h i : ℝ)) l (𝓝 0)) :
    TendstoInMeasure μ (fun i => brownianNativePostFirstLongTime B ε T a (h i)) l (fun _ => 0) ∧
    Tendsto (fun i => eLpNorm (brownianNativePostFirstLongTime B ε T a (h i)) 1 μ) l (𝓝 0) ∧
    Tendsto (fun i => ∫ ω, |brownianNativePostFirstLongTime B ε T a (h i) ω| ∂μ) l (𝓝 0) :=
  brownian_native_timeweighted_of_maximum hB hε hT ha (fun i => (hh i).ne')
    (brownian_nativePostFirstMaximum_tendstoInMeasure hB hε hT hh hconv)

end SwingRepair
