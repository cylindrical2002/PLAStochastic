import PLAStochastic.Index.GEP.Response.Defs
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Locally absolutely summable series of response primitives

Only local L¹ summability of the derivatives is required. This is the exchange
needed between the finite-prefix endpoint formula and the full influence series.
-/

namespace PGM
noncomputable section
open MeasureTheory Set Filter Topology
open scoped ENNReal Interval

variable {ι : Type*} [Countable ι]

omit [Countable ι] in
theorem kernel_tsum_lintegral_enorm_ne_top {μ : Measure ℝ} {f : ι → ℝ → ℝ}
    (hi : ∀ i, Integrable (f i) μ)
    (hs : Summable fun i => ∫ x, ‖f i x‖ ∂μ) :
    ∑' i, ∫⁻ x, ‖f i x‖ₑ ∂μ ≠ ∞ := by
  have he (i : ι) : ∫⁻ x, ‖f i x‖ₑ ∂μ = ‖∫ x, ‖f i x‖ ∂μ‖ₑ := by
    dsimp [enorm]
    rw [lintegral_coe_eq_integral _ (hi i).norm, ENNReal.coe_nnreal_eq]
    simp only [coe_nnnorm, Real.norm_eq_abs]
    rw [abs_of_nonneg (integral_nonneg fun x => abs_nonneg (f i x))]
  rw [funext he]
  exact ENNReal.tsum_coe_ne_top_iff_summable.2 (NNReal.summable_coe.1 hs.abs)

theorem kernel_integrable_tsum {μ : Measure ℝ} {f : ι → ℝ → ℝ}
    (hi : ∀ i, Integrable (f i) μ)
    (hs : Summable fun i => ∫ x, ‖f i x‖ ∂μ) :
    Integrable (fun x => ∑' i, f i x) μ := by
  refine ⟨(AEMeasurable.tsum fun i => (hi i).aemeasurable).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_enorm]
  calc
    ∫⁻ x, ‖∑' i, f i x‖ₑ ∂μ ≤ ∫⁻ x, ∑' i, ‖f i x‖ₑ ∂μ :=
      lintegral_mono fun x => enorm_tsum_le_tsum_enorm
    _ = ∑' i, ∫⁻ x, ‖f i x‖ₑ ∂μ :=
      lintegral_tsum fun i => (hi i).aestronglyMeasurable.enorm
    _ < ∞ := (kernel_tsum_lintegral_enorm_ne_top hi hs).lt_top

theorem kernel_hasSum_intervalIntegral {j : ι → ℝ → ℝ} {a b : ℝ}
    (hi : ∀ i, IntervalIntegrable (j i) volume a b)
    (hs : Summable fun i => ∫ x in Ι a b, ‖j i x‖) :
    HasSum (fun i => ∫ x in a..b, j i x) (∫ x in a..b, ∑' i, j i x) := by
  simp only [intervalIntegral.intervalIntegral_eq_integral_uIoc]
  exact (hasSum_integral_of_summable_integral_norm
    (fun i => (hi i).def') hs).const_smul _

/-- Countable sums preserve the original response primitive interface when
their integration constants and local derivative masses are summable. -/
theorem kernel_aePrimitive_tsum {J j : ι → ℝ → ℝ} {c : ι → ℝ}
    (hi : ∀ i R, IntervalIntegrable (j i) volume 0 R)
    (hc : ∀ i, ∀ᵐ x ∂volume.restrict (Ioi (0 : ℝ)),
      J i x = c i + ∫ t in (0 : ℝ)..x, j i t)
    (hcs : Summable c)
    (hs : ∀ R : ℝ, Summable fun i => ∫ t in Ι (0 : ℝ) R, ‖j i t‖) :
    AEPrimitive (fun x => ∑' i, J i x) (fun x => ∑' i, j i x) := by
  refine ⟨fun R => ?_, ∑' i, c i, ?_⟩
  · rw [intervalIntegrable_iff]
    exact kernel_integrable_tsum (fun i => (hi i R).def') (hs R)
  · filter_upwards [ae_all_iff.2 hc] with x hx
    have hsum := kernel_hasSum_intervalIntegral (fun i => hi i x) (hs x)
    calc
      ∑' i, J i x = ∑' i, (c i + ∫ t in (0 : ℝ)..x, j i t) := tsum_congr hx
      _ = (∑' i, c i) + ∫ t in (0 : ℝ)..x, ∑' i, j i t :=
        (hcs.hasSum.add hsum).tsum_eq

omit [Countable ι] in
/-- A bounded primitive admits a controlled integration constant. This converts
the summable finite-prefix probability bounds into summable constants. -/
theorem kernel_aePrimitive_constant_bound {J j : ℝ → ℝ} {B : ℝ}
    (hp : AEPrimitive J j) (hi : Integrable j) (hJ : ∀ x, 0 < x → |J x| ≤ B) :
    ∃ c : ℝ, (∀ᵐ x ∂volume.restrict (Ioi (0 : ℝ)), J x = c + ∫ t in (0 : ℝ)..x, j t) ∧
      |c| ≤ B + ∫ t, |j t| := by
  obtain ⟨_, c, hc⟩ := hp
  have : NeZero (volume (Ioi (0 : ℝ))) := ⟨by simp⟩
  obtain ⟨x, hx, he⟩ := ((ae_restrict_mem measurableSet_Ioi).and hc).exists
  have hx0 : 0 < x := hx
  have hbound : |∫ t in (0 : ℝ)..x, j t| ≤ ∫ t, |j t| := by
    calc
      _ ≤ ∫ t in Ioc 0 x, |j t| := by
        simpa only [Real.norm_eq_abs, uIoc_of_le hx0.le] using
          (intervalIntegral.norm_integral_le_integral_norm_uIoc (μ := volume) (f := j) (a := 0) (b := x))
      _ ≤ ∫ t, |j t| := setIntegral_le_integral hi.abs (Eventually.of_forall fun _ => abs_nonneg _)
  refine ⟨c, hc, ?_⟩
  calc
    |c| = |J x - ∫ t in (0 : ℝ)..x, j t| := by rw [he, add_sub_cancel_right]
    _ ≤ |J x| + |∫ t in (0 : ℝ)..x, j t| := abs_sub _ _
    _ ≤ B + ∫ t, |j t| := add_le_add (hJ x hx) hbound

end
end PGM
