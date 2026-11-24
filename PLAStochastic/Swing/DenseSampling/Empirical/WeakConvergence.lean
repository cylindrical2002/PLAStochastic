import PLAStochastic.Swing.DenseSampling.Empirical.TestFunctionLimit
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

/-! # Weak convergence of the actual completed-error empirical measures -/
noncomputable section
open MeasureTheory ProbabilityTheory BrownianAffine Filter Set
open scoped NNReal ENNReal Topology
namespace SwingRepair
set_option backward.isDefEq.respectTransparency false

/-- The empirical probability law of a finite real array. At size zero, the
harmless default is a point mass at zero. -/
def finiteArrayEmpiricalMeasure (n : ℕ) (x : ℕ → ℝ) : ProbabilityMeasure ℝ :=
  if hn : n = 0 then ⟨Measure.dirac 0, inferInstance⟩ else
    ⟨(n : ℝ≥0∞)⁻¹ • ∑ k ∈ Finset.range n, Measure.dirac (x k), ⟨by
      simp only [Measure.smul_apply, smul_eq_mul, Measure.finsetSum_apply, Measure.dirac_apply_of_mem,
        Set.mem_univ, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
      exact ENNReal.inv_mul_cancel (by exact_mod_cast hn) (ENNReal.natCast_ne_top n)⟩⟩

theorem finiteArrayEmpiricalMeasure_coe {n : ℕ} (hn : n ≠ 0) (x : ℕ → ℝ) :
    (finiteArrayEmpiricalMeasure n x : Measure ℝ) =
      (n : ℝ≥0∞)⁻¹ • ∑ k ∈ Finset.range n, Measure.dirac (x k) := by
  simp only [finiteArrayEmpiricalMeasure, dif_neg hn]
  rfl

theorem integral_finiteArrayEmpiricalMeasure {n : ℕ} (hn : n ≠ 0)
    (x : ℕ → ℝ) (g : ℝ → ℝ) :
    (∫ z, g z ∂(finiteArrayEmpiricalMeasure n x : Measure ℝ)) =
      (∑ k ∈ Finset.range n, g (x k)) / (n : ℝ) := by
  rw [finiteArrayEmpiricalMeasure_coe hn, integral_smul_measure,
    integral_finsetSum_measure (fun k _ => integrable_dirac (by simp))]
  simp only [integral_dirac, ENNReal.toReal_inv, ENNReal.toReal_natCast, smul_eq_mul]
  ring

/-- The equally weighted law on the two boundary values. -/
def fairBoundaryMeasure : ProbabilityMeasure ℝ :=
  finiteArrayEmpiricalMeasure 2 (fun k => if k = 0 then -1 else 1)

theorem fairBoundaryMeasure_coe : (fairBoundaryMeasure : Measure ℝ) =
    (2 : ℝ≥0∞)⁻¹ • (Measure.dirac (-1) + Measure.dirac 1) := by
  rw [fairBoundaryMeasure, finiteArrayEmpiricalMeasure_coe (by norm_num)]
  simp [Finset.sum_range_succ]

theorem integral_fairBoundaryMeasure (φ : ℝ → ℝ) :
    (∫ z, φ z ∂(fairBoundaryMeasure : Measure ℝ)) = (φ 1 + φ (-1)) / 2 := by
  rw [fairBoundaryMeasure, integral_finiteArrayEmpiricalMeasure (by norm_num)]
  simp [Finset.sum_range_succ, add_comm]

/-- The empirical probability law includes exactly the completed native
segments, excluding the final unfinished EOF segment. -/
def nativeCompletedEmpiricalMeasure (t y : ℕ → ℝ) (ε : ℝ)
    (segs : List NativeSegment) : ProbabilityMeasure ℝ :=
  finiteArrayEmpiricalMeasure (segs.length - 1) (nativeNormalizedRecordingError t y ε segs)

theorem integral_nativeCompletedEmpiricalMeasure (t y : ℕ → ℝ) (ε : ℝ)
    (segs : List NativeSegment) (hn : segs.length - 1 ≠ 0) (φ : ℝ → ℝ) :
    (∫ z, φ z ∂(nativeCompletedEmpiricalMeasure t y ε segs : Measure ℝ)) =
      nativeCompletedTestAverage t y ε segs φ := by
  exact integral_finiteArrayEmpiricalMeasure hn _ φ

/-- Deterministic weak convergence for an arbitrary continuous path once the
actual completed count diverges. All boundary and balance estimates were
proved uniformly over the actual native stream. -/
theorem native_completed_empiricalMeasure_tendsto (f : C(ℝ, ℝ)) {T ε : ℝ}
    (hT : 0 ≤ T) (hε : 0 < ε) {ι : Type*} {l : Filter ι}
    {h : ι → ℝ} {N : ι → ℕ} (hh : ∀ i, 0 < h i) (hconv : Tendsto h l (𝓝 0))
    (hN : ∀ i, (N i : ℝ) * h i ≤ T)
    (hcount : Tendsto (fun i => nativeCompletedCount (fun j => (j : ℝ) * h i)
      (fun j => f ((j : ℝ) * h i)) ε (N i)) l atTop) :
    Tendsto (fun i => nativeCompletedEmpiricalMeasure (fun j => (j : ℝ) * h i)
      (fun j => f ((j : ℝ) * h i)) ε
      (nativeStream (fun j => (j : ℝ) * h i) (fun j => f ((j : ℝ) * h i)) ε (N i)))
      l (𝓝 fairBoundaryMeasure) := by
  apply ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mpr
  intro φ
  rw [integral_fairBoundaryMeasure]
  apply (native_completed_test_average_tendsto f φ.toContinuousMap hT hε hh hconv hN hcount).congr'
  filter_upwards [hcount.eventually (eventually_gt_atTop 0)] with i hi
  exact (integral_nativeCompletedEmpiricalMeasure _ _ ε _ (ne_of_gt hi) φ).symm

end SwingRepair
