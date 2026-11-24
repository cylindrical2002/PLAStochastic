import PLAStochastic.Affine.Moments.Optimal.Survival.Image.ThetaTransform
import PLAStochastic.Affine.Process.Killed.Boundary.Identities

/-! # The derivative of the alternating theta sum is the actual cross kernel -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology
namespace BrownianAffine
set_option backward.isDefEq.respectTransparency false

def alternatingHeatThetaMode (n : ℕ) (t : ℝ) : ℝ :=
  Real.cos (heatFrequency 1 n) * Real.exp (-(heatFrequency 1 n)^2*t/2)

theorem alternatingHeatThetaMode_bound {δ t : ℝ} (hδ : 0 ≤ δ) (ht : δ ≤ t) (n : ℕ) :
    ‖alternatingHeatThetaMode n t‖ ≤ heatSpatialBound 1 δ 0 0 n := by
  have hexp : Real.exp (-(heatFrequency 1 n ^ 2) * t / 2) ≤
      Real.exp (-((n : ℝ) + 1) * (heatScale 1 * δ)) := by
    apply Real.exp_le_exp.mpr
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have hm : 0 ≤ ((n : ℝ) + 1) ^ 2 - ((n : ℝ) + 1) := by nlinarith
    have hp := mul_nonneg hm (mul_nonneg (heatScale_pos (by norm_num : (0 : ℝ)<1)).le hδ)
    have ht' := mul_le_mul_of_nonneg_left ht (sq_nonneg (heatFrequency 1 n))
    unfold heatFrequency heatScale at *
    nlinarith
  rw [alternatingHeatThetaMode, norm_mul, Real.norm_eq_abs,
    Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  calc
    _ ≤ 1 * Real.exp (-((n : ℝ) + 1) * (heatScale 1 * δ)) :=
      mul_le_mul (Real.abs_cos_le_one _) hexp (Real.exp_nonneg _) zero_le_one
    _ ≤ heatSpatialBound 1 δ 0 0 n := by
      simp only [heatSpatialBound, zero_add, pow_zero, one_mul, div_one]
      nlinarith [Real.exp_pos (-((n : ℝ)+1)*(heatScale 1*δ))]

theorem summable_alternatingHeatThetaMode {t : ℝ} (ht : 0 < t) :
    Summable (fun n => alternatingHeatThetaMode n t) :=
  (summable_heatSpatialBound (by norm_num) ht 0 0).of_norm_bounded
    (fun n => alternatingHeatThetaMode_bound ht.le le_rfl n)

theorem alternatingHeatTheta_eq_nat {t : ℝ} (ht : 0 < t) :
    alternatingHeatTheta t = 1 + 2 * ∑' n : ℕ, alternatingHeatThetaMode n t := by
  let f : ℤ → ℝ := fun n => Real.cos ((n : ℝ)*Real.pi) * Real.exp (-Real.pi^2*(n : ℝ)^2*t/2)
  have hneg (n : ℤ) : f (-n) = f n := by simp [f]
  have hn (n : ℕ) : f ((n : ℤ)+1) = alternatingHeatThetaMode n t := by
    simp only [f, alternatingHeatThetaMode, heatFrequency, div_one, Int.cast_add,
      Int.cast_natCast, Int.cast_one]
    congr 1
    congr 1
    ring
  have hs : Summable (fun n : ℕ => f (n : ℤ)) := by
    apply (summable_nat_add_iff 1).mp
    simpa only [Nat.cast_add, Nat.cast_one, hn] using summable_alternatingHeatThetaMode ht
  have hsn : Summable (fun n : ℕ => f (-(n : ℤ))) := by simpa only [hneg] using hs
  have hz := (hs.of_nat_of_neg hsn).hasSum.nat_add_neg
  rw [← hasSum_nat_add_iff' 1] at hz
  simp only [hneg, Nat.cast_add, Nat.cast_one, hn, Finset.sum_range_one, Nat.cast_zero] at hz
  have hz0 : f 0 = 1 := by simp [f]
  rw [hz0] at hz
  have hsum := hz.tsum_eq
  rw [(summable_alternatingHeatThetaMode ht).tsum_add (summable_alternatingHeatThetaMode ht)] at hsum
  change alternatingHeatTheta t = _
  change (∑' n : ℤ, f n) = _
  linarith

theorem hasDerivAt_alternatingHeatThetaMode (n : ℕ) (t : ℝ) :
    HasDerivAt (alternatingHeatThetaMode n)
      (-1/4 * heatSpatialMode 1 1 1 n t 1 0) t := by
  have hd := (((hasDerivAt_id t).const_mul (-(heatFrequency 1 n)^2)).div_const 2).exp.const_mul
    (Real.cos (heatFrequency 1 n))
  convert! hd using 1
  simp only [heatSpatialMode, Nat.reduceAdd, Nat.cast_one, mul_one, mul_zero,
    zero_add, one_mul, id_eq, Real.sin_add_pi_div_two, Real.sin_pi_div_two, div_one]
  ring

theorem hasDerivAt_alternatingHeatTheta {t : ℝ} (ht : 0 < t) :
    HasDerivAt alternatingHeatTheta (heatCrossBoundary 1 t / 2) t := by
  let δ := t/2
  have hδ : 0 < δ := by dsimp only [δ]; linarith
  have hmem : t ∈ Ioi δ := by change t/2 < t; linarith
  have hb := (summable_heatSpatialBound (by norm_num : (0:ℝ)<1) hδ 1 1).mul_left (1/4)
  have hu (n : ℕ) (s : ℝ) (hs : s ∈ Ioi δ) :
      ‖-1/4 * heatSpatialMode 1 1 1 n s 1 0‖ ≤ (1/4) * heatSpatialBound 1 δ 1 1 n := by
    rw [norm_mul, show ‖(-1/4 : ℝ)‖ = 1/4 by norm_num]
    exact mul_le_mul_of_nonneg_left (heatSpatialMode_bound (by norm_num) hδ.le hs.le 1 1 n 1 0)
      (by norm_num)
  have hd := hasDerivAt_tsum_of_isPreconnected hb isOpen_Ioi isPreconnected_Ioi
    (fun n s _ => hasDerivAt_alternatingHeatThetaMode n s) hu hmem
    (summable_alternatingHeatThetaMode ht) hmem
  have he : alternatingHeatTheta =ᶠ[𝓝 t] (fun s => 1 + 2*∑' n, alternatingHeatThetaMode n s) := by
    filter_upwards [Ioi_mem_nhds ht] with s hs
    exact alternatingHeatTheta_eq_nat hs
  have hh := ((hd.const_mul 2).const_add 1).congr_of_eventuallyEq he
  convert! hh using 1
  simp only [tsum_mul_left, heatCrossBoundary, heatSpatialSeries]
  ring

end BrownianAffine
