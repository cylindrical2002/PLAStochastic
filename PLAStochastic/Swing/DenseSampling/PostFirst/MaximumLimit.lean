import PLAStochastic.Swing.DenseSampling.PostFirst.MaximumBound
import PLAStochastic.Swing.DenseSampling.PostFirst.MeshChoice
import PLAStochastic.Swing.DenseSampling.PostFirst.ProbabilityConsequences

/-! # Actual post-first maximum convergence from Brownian increments and native recursion -/
noncomputable section
open Classical
open MeasureTheory ProbabilityTheory BrownianAffine Filter Set
open scoped NNReal ENNReal Topology
namespace SwingRepair
set_option backward.isDefEq.respectTransparency false

/-- The longest actual post-first segment vanishes in probability on any fixed
bounded time window. The EOF segment is included. No maximum-limit hypothesis,
independence of restart intervals, or assumed conditional mean appears. -/
theorem brownian_nativePostFirstMaximum_tail_tendsto_zero {Ω ι : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B μ)
    {T a : ℝ} (hT : 0 ≤ T) (ha : 0 < a) {l : Filter ι} [l.IsCountablyGenerated]
    {h : ι → ℝ≥0} (hh : ∀ i, 0 < h i) (hconv : Tendsto (fun i => (h i : ℝ)) l (𝓝 0))
    {n : ι → ℕ} (hnT : ∀ i, (n i : ℝ)*(h i : ℝ) ≤ T) :
    Tendsto (fun i => μ.real {ω | a ≤ nativePostFirstMaximum (fun j => (j : ℝ)*(h i : ℝ))
      (nativeStream (fun j => (j : ℝ)*(h i : ℝ)) (fun j => B ((j : ℝ≥0)*h i) ω) 1 (n i))}) l (𝓝 0) := by
  let : IsProbabilityMeasure μ := hB.isGaussianProcess.isProbabilityMeasure
  apply Metric.tendsto_nhds.mpr
  intro η hη
  obtain ⟨K, hK⟩ := ((integral_brownianNativeHeightFailure_tendsto_zero hB T).eventually
    (gt_mem_nhds (show (0 : ℝ) < η/4 by positivity))).exists
  let M := (2*(K : ℝ)+2)/a
  have hM : 0 ≤ M := by dsimp only [M]; positivity
  let q : ℝ≥0 := ⟨a/2, by positivity⟩
  have hq : 0 < q := by exact_mod_cast (show (0 : ℝ) < a/2 by positivity)
  obtain ⟨H, hH, hHs, hMH⟩ := native_maximum_comparison_cutoff hM
  let β := η/(4*(T+2))
  have hβ : 0 < β := by dsimp only [β]; positivity
  have hβeq : β*(T+2) = η/4 := by dsimp only [β]; field_simp
  obtain ⟨γ, h₀, hγ, hh₀, hsum⟩ := exists_native_rejection_sum_comparison hB hM hq hH hHs hMH hβ
  have hstate := integral_nativeRejectionStateFailure_tendsto_zero hB hT hγ hh hconv hnT
  have hexc : Tendsto (fun i => (2*a*(T+1))*(h i : ℝ)^2) l (𝓝 0) := by
    simpa only [zero_pow (by decide : (2 : ℕ) ≠ 0), mul_zero] using (hconv.pow 2).const_mul (2*a*(T+1))
  have hmesh := hconv.eventually (gt_mem_nhds (show (0 : ℝ) < min h₀ (min (a/4) (1/2)) by positivity))
  filter_upwards [hmesh, hstate.eventually (gt_mem_nhds (show (0 : ℝ) < η/4 by positivity)),
    hexc.eventually (gt_mem_nhds (show (0 : ℝ) < η/4 by positivity))] with i hi hsi hei
  have hhi : (h i : ℝ) ≤ h₀ := hi.le.trans (min_le_left _ _)
  have hhia : (h i : ℝ) ≤ a/4 := hi.le.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hhi1 : (h i : ℝ) ≤ 1/2 := hi.le.trans ((min_le_right _ _).trans (min_le_right _ _))
  let N := ⌈(a/2)/(h i : ℝ)⌉₊
  let last := n i+⌈(H : ℝ)/(h i : ℝ)⌉₊+1
  have hN := native_maximum_future_grid ha (hh i) hhia
  have hl := native_maximum_extended_grid (hh i) (hnT i) hHs hhi1
  have hcost := hsum (h i) (hh i) hhi (n i) last hl.1 ((n i : ℝ)*(h i : ℝ)) le_rfl hl.2.1
    N (by exact_mod_cast hN.1) a hN.2.2
  have hbound := measureReal_nativePostFirstMaximum_le_localizations hB (hh i) ha (hnT i)
    (le_rfl : (2*(K : ℝ)+2)/a ≤ M) hN.2.1 (γ := γ)
  have hb : β*((last : ℝ)*(h i : ℝ)) ≤ η/4 :=
    (mul_le_mul_of_nonneg_left hl.2.2 hβ.le).trans_eq hβeq
  have hex := (native_maximum_mesh_exception ha.le (hnT i) (by linarith : (h i : ℝ) ≤ 1)).trans_lt hei
  rw [Real.dist_eq, sub_zero, abs_of_nonneg measureReal_nonneg]
  linarith

/-- Unit-tolerance dense Brownian native streams satisfy the actual maximum
convergence theorem, directly from the Brownian process assumptions. -/
theorem brownian_nativePostFirstMaximum_tendstoInMeasure_unit {Ω ι : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B μ)
    {T : ℝ} (hT : 0 ≤ T) {l : Filter ι} [l.IsCountablyGenerated]
    {h : ι → ℝ≥0} (hh : ∀ i, 0 < h i) (hconv : Tendsto (fun i => (h i : ℝ)) l (𝓝 0)) :
    TendstoInMeasure μ (fun i => brownianNativePostFirstMaximum B 1 T (h i)) l (fun _ => 0) := by
  let : IsProbabilityMeasure μ := hB.isGaussianProcess.isProbabilityMeasure
  apply tendstoInMeasure_iff_norm.mpr
  intro a ha
  have hnT (i : ι) : (⌊T/(h i : ℝ)⌋₊ : ℝ)*(h i : ℝ) ≤ T :=
    (le_div_iff₀ (show (0 : ℝ) < h i by exact_mod_cast hh i)).mp
      (Nat.floor_le (div_nonneg hT (h i).coe_nonneg))
  have ht := brownian_nativePostFirstMaximum_tail_tendsto_zero hB hT ha hh hconv hnT
  have hp := ENNReal.continuous_ofReal.continuousAt.tendsto.comp ht
  have hn (i : ι) (ω : Ω) : 0 ≤ brownianNativePostFirstMaximum B 1 T (h i) ω :=
    nativePostFirstMaximum_nonneg _ _
  simpa only [Function.comp_def, sub_zero, Real.norm_eq_abs, abs_of_nonneg (hn _ _),
    ENNReal.ofReal_zero, measureReal_def, ENNReal.ofReal_toReal (measure_ne_top μ _),
    brownianNativePostFirstMaximum, brownianNativeMeshStream,
    abs_of_nonneg (nativePostFirstMaximum_nonneg _ _)] using hp

end SwingRepair
