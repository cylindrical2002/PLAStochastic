import PLAStochastic.Swing.DenseSampling.Segments.ShrinkingConeSlope

/-!
# The actual first native endpoint approaches a band boundary

The offset has the manuscript's sign: fitted endpoint minus the true sample,
divided by the tolerance. The result concerns the actual first segment read
from nativeStream, including its constrained-SSE selected coefficient.
-/

noncomputable section
open MeasureTheory ProbabilityTheory BrownianAffine Filter Set
open scoped NNReal ENNReal Topology

namespace SwingRepair
set_option backward.isDefEq.respectTransparency false

def nativeFirstNormalizedOffset (t y : ℕ → ℝ) (ε : ℝ) : ℝ :=
  (nativeSegmentEndpoint t (nativeFirstObservedSegment t y ε) -
    y (nativeFirstObservedSegment t y ε).finish) / ε

theorem nativeFirstNormalizedOffset_mesh_eq (f : C(ℝ, ℝ)) (hf : f 0 = 0)
    (h : ℝ≥0) (hh : h ≠ 0) {ε : ℝ} (hε : 0 ≤ ε)
    (hfinite : finiteMeshAnchoredLifetime f h ε ≠ ∞) :
    nativeFirstNormalizedOffset (fun n => (n : ℝ) * h) (fun n => f ((n : ℝ) * h)) ε =
      (nativeFirstSlope (fun n => (n : ℝ) * h) (fun n => f ((n : ℝ) * h)) ε *
        ((nativeFirstRecording (fun n => (n : ℝ) * h) (fun n => f ((n : ℝ) * h)) ε : ℝ) * h) -
      f ((nativeFirstRecording (fun n => (n : ℝ) * h) (fun n => f ((n : ℝ) * h)) ε : ℝ) * h)) / ε := by
  obtain ⟨K, hK, hcone⟩ := exists_nativeGrid_threshold f hf h hh hε hfinite
  have hc : ∀ j, nativePrefixFeasible (fun n => (n : ℝ) * h)
      (fun n => f ((n : ℝ) * h)) ε 0 j (f ((0 : ℕ) * h)) ↔ j < K := by
    simpa only [Nat.cast_zero, zero_mul] using hcone
  unfold nativeFirstNormalizedOffset nativeFirstSlope
  rw [nativeFirstObservedSegment_eq_threshold _ _ ε hK hc,
    nativeFirstRecording_eq_threshold _ _ ε hK hc]
  simp only [nativeSegmentEndpoint, nativeOutputSegment, Nat.cast_zero, zero_mul, hf, sub_zero, zero_add]

theorem tendsto_nativeFirstNormalizedOffset_mesh (f : C(ℝ, ℝ)) (hf : f 0 = 0)
    {ε : ℝ} (hε : 0 < ε) {σ : ℝ≥0} (hσ : anchoredLifetime f ε = σ)
    {a : ℝ} (ha : ∀ t : Icc (0 : ℝ) (σ : ℝ), |f t - a * (t : ℝ)| ≤ ε)
    {ι : Type*} {l : Filter ι} {h : ι → ℝ≥0} (hh : ∀ i, h i ≠ 0)
    (hconv : Tendsto (fun i => (h i : ℝ)) l (𝓝 0)) :
    Tendsto (fun i => nativeFirstNormalizedOffset (fun n => (n : ℝ) * h i)
      (fun n => f ((n : ℝ) * h i)) ε) l (𝓝 ((a * (σ : ℝ) - f σ) / ε)) := by
  have hfinite : anchoredLifetime f ε ≠ ∞ := by rw [hσ]; exact ENNReal.coe_ne_top
  have htime : Tendsto (fun i =>
      (nativeFirstRecording (fun n => (n : ℝ) * h i) (fun n => f ((n : ℝ) * h i)) ε : ℝ) * h i)
      l (𝓝 (σ : ℝ)) := by
    have ht := tendsto_nativeFirstRecording_mesh f hf hε.le hfinite hh hconv
    convert ht using 1
    · funext i
      exact mul_comm _ _
    · rw [hσ, ENNReal.coe_toReal]
  have hslope := tendsto_nativeFirstSlope_mesh f hf hε hσ ha hh hconv
  have hvalue := (f.continuous.tendsto σ).comp htime
  have hoff := ((hslope.mul htime).sub hvalue).div_const ε
  apply hoff.congr'
  have hp (i : ι) : 0 < (h i : ℝ) := by exact_mod_cast (pos_of_ne_zero (hh i))
  have hlife := tendsto_finiteMeshAnchoredLifetime f ε hp hconv
  filter_upwards [hlife.eventually_lt_const (lt_top_iff_ne_top.mpr hfinite)] with i hi
  exact (nativeFirstNormalizedOffset_mesh_eq f hf (h i) (hh i) hε.le hi.ne).symm

/-- The limit offset has magnitude one, with the actual fitted-minus-sample sign. -/
theorem nativeFirst_limit_offset_sign (f : C(ℝ, ℝ)) (hf : f 0 = 0)
    {ε : ℝ} (hε : 0 < ε) {σ : ℝ≥0} (hσ : anchoredLifetime f ε = σ)
    {a : ℝ} (ha : ∀ t : Icc (0 : ℝ) (σ : ℝ), |f t - a * (t : ℝ)| ≤ ε) :
    (a * (σ : ℝ) - f σ) / ε = 1 ∨ (a * (σ : ℝ) - f σ) / ε = -1 := by
  have hz : |f 0| ≤ ε := by simp only [hf, abs_zero]; exact hε.le
  have heq := anchored_fit_terminal_boundary f hz hσ ha
  rcases eq_or_eq_neg_of_abs_eq heq with h | h
  · right
    apply (div_eq_iff hε.ne').mpr
    linarith
  · left
    apply (div_eq_iff hε.ne').mpr
    linarith

/-- The actual native first duration, selected slope, and fitted offset converge
jointly pathwise. Fairness and independence of the boundary sign are separate
probability statements, not asserted by this deterministic convergence result. -/
theorem native_first_segment_dense_ae {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B μ)
    {ε : ℝ} (hε : 0 < ε) {ι : Type*} {l : Filter ι} {h : ι → ℝ≥0}
    (hh : ∀ i, h i ≠ 0) (hconv : Tendsto (fun i => (h i : ℝ)) l (𝓝 0)) :
    ∀ᵐ ω ∂μ, ∃ a S : ℝ, (S = 1 ∨ S = -1) ∧
      Tendsto (fun i => (h i : ℝ) * (nativeFirstRecording (fun n => (n : ℝ) * h i)
        (fun n => B ((n : ℝ≥0) * h i) ω) ε : ℝ)) l
          (𝓝 (anchoredProcessLifetime B ε ω).toReal) ∧
      Tendsto (fun i => nativeFirstSlope (fun n => (n : ℝ) * h i)
        (fun n => B ((n : ℝ≥0) * h i) ω) ε) l (𝓝 a) ∧
      Tendsto (fun i => nativeFirstNormalizedOffset (fun n => (n : ℝ) * h i)
        (fun n => B ((n : ℝ≥0) * h i) ω) ε) l (𝓝 S) := by
  filter_upwards [hB.cont, hB.eval_zero_ae_eq_zero,
    anchoredProcessLifetime_tolerance_ae_ne_top hB hε,
    nativeFirstRecording_mesh_ae_tendsto hB hε hh hconv] with ω hc hz hf ht
  obtain ⟨σ, hσ⟩ := WithTop.ne_top_iff_exists.mp hf
  have hσ' : anchoredLifetime (processPath B ω) ε = (σ : ℝ≥0∞) := hσ.symm
  have hzero : processPath B ω 0 = 0 := (processPath_apply_of_continuous hc 0).trans hz
  have hzero' : |processPath B ω 0| < ε := by rw [hzero, abs_zero]; exact hε
  obtain ⟨a, ha, _⟩ := existsUnique_anchored_fit_at_lifetime (processPath B ω) hzero' hσ'
  let S := (a * (σ : ℝ) - processPath B ω σ) / ε
  refine ⟨a, S, nativeFirst_limit_offset_sign (processPath B ω) hzero hε hσ' ha, ht, ?_, ?_⟩
  · have hs := tendsto_nativeFirstSlope_mesh (processPath B ω) hzero hε hσ' ha hh hconv
    convert hs using 1
    funext i
    congr 1
    funext n
    simpa only [NNReal.coe_mul, NNReal.coe_natCast] using
      (processPath_apply_of_continuous hc ((n : ℝ≥0) * h i)).symm
  · have hs := tendsto_nativeFirstNormalizedOffset_mesh (processPath B ω) hzero hε hσ' ha hh hconv
    convert hs using 1
    funext i
    congr 1
    funext n
    simpa only [NNReal.coe_mul, NNReal.coe_natCast] using
      (processPath_apply_of_continuous hc ((n : ℝ≥0) * h i)).symm

end SwingRepair
