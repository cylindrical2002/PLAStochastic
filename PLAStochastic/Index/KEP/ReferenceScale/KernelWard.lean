import PLAStochastic.Index.KEP.ReferenceScale.KernelSlope

/-!
# Slope derivatives of the actual residual step

These are the one-step identities used in the finite-path Ward calculation.
The scalar slope derivative is expressed through actual spatial derivatives.
The long killed-path identity, including its internal boundary fluxes, is a
separate step and is not asserted here.
-/

set_option autoImplicit false

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology

def kepStepSlopeFirst (f f' : ℝ → ℝ) (β a t : ℝ) : ℝ :=
  -(kepStepSpatial f β a t) / a + (β - t) / a * kepStepSpatialFirst f' β a t

def kepStepSlopeSecond (f f' f'' : ℝ → ℝ) (β a t : ℝ) : ℝ :=
  2 / a ^ 2 * kepStepSpatial f β a t -
    4 * (β - t) / a ^ 2 * kepStepSpatialFirst f' β a t +
    (β - t) ^ 2 / a ^ 2 * kepStepSpatialSecond f'' β a t

set_option backward.isDefEq.respectTransparency.types false in
theorem hasDerivAt_kepStepSpatial_slope {f f' : ℝ → ℝ}
    (hd : ∀ x, HasDerivAt f (f' x) x) (β t : ℝ) {a : ℝ} (ha : 0 < a) :
    HasDerivAt (fun c => kepStepSpatial f β c t) (kepStepSlopeFirst f f' β a t) a := by
  have hc : HasDerivAt (fun c : ℝ => (β - t) / c) (-((β - t) / a ^ 2)) a := by
    simpa only [div_eq_mul_inv, mul_neg] using (hasDerivAt_inv ha.ne').const_mul (β - t)
  have h : HasDerivAt (fun c : ℝ => f ((β - t) / c) / c)
      ((f' ((β - t) / a) * (-((β - t) / a ^ 2)) * a - f ((β - t) / a)) / a ^ 2) a := by
    convert ((hd ((β - t) / a)).comp a hc).div (hasDerivAt_id a) ha.ne' using 1 <;>
      first | rfl | (dsimp only [Function.comp_apply, id_eq, Pi.div_apply]; ring)
  have he :
      (f' ((β - t) / a) * (-((β - t) / a ^ 2)) * a - f ((β - t) / a)) / a ^ 2 =
        kepStepSlopeFirst f f' β a t := by
    dsimp [kepStepSlopeFirst, kepStepSpatial, kepStepSpatialFirst]
    rw [abs_of_pos ha]
    field_simp
    ring
  rw [he] at h
  apply h.congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds ha] with c hc
  change 0 < c at hc
  simp only [kepStepSpatial, abs_of_pos hc]

set_option backward.isDefEq.respectTransparency.types false in
theorem hasDerivAt_kepStepSpatialFirst_slope {f' f'' : ℝ → ℝ}
    (hdd : ∀ x, HasDerivAt f' (f'' x) x) (β t : ℝ) {a : ℝ} (ha : 0 < a) :
    HasDerivAt (fun c => kepStepSpatialFirst f' β c t)
      (-2 / a * kepStepSpatialFirst f' β a t +
        (β - t) / a * kepStepSpatialSecond f'' β a t) a := by
  have hc : HasDerivAt (fun c : ℝ => (β - t) / c) (-((β - t) / a ^ 2)) a := by
    simpa only [div_eq_mul_inv, mul_neg] using (hasDerivAt_inv ha.ne').const_mul (β - t)
  have h : HasDerivAt (fun c : ℝ => -(f' ((β - t) / c)) / c ^ 2)
      ((- (f'' ((β - t) / a) * (-((β - t) / a ^ 2))) * a ^ 2 -
        (-f' ((β - t) / a)) * (2 * a)) / (a ^ 2) ^ 2) a := by
    convert (((hdd ((β - t) / a)).comp a hc).neg).div
      ((hasDerivAt_id a).pow 2) (pow_ne_zero _ ha.ne') using 1 <;>
      first | rfl | (simp only [Function.comp_apply, id_eq, Pi.neg_apply, Pi.pow_apply,
        Nat.cast_ofNat, mul_one]; ring)
  have he :
      (- (f'' ((β - t) / a) * (-((β - t) / a ^ 2))) * a ^ 2 -
        (-f' ((β - t) / a)) * (2 * a)) / (a ^ 2) ^ 2 =
      -2 / a * kepStepSpatialFirst f' β a t +
        (β - t) / a * kepStepSpatialSecond f'' β a t := by
    dsimp [kepStepSpatialFirst, kepStepSpatialSecond]
    rw [abs_of_pos ha]
    field_simp
    ring
  rw [he] at h
  apply h.congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds ha] with c hc
  change 0 < c at hc
  simp only [kepStepSpatialFirst, abs_of_pos hc, pow_two]

set_option backward.isDefEq.respectTransparency.types false in
theorem hasDerivAt_kepStepSlopeFirst {f f' f'' : ℝ → ℝ}
    (hd : ∀ x, HasDerivAt f (f' x) x) (hdd : ∀ x, HasDerivAt f' (f'' x) x)
    (β t : ℝ) {a : ℝ} (ha : 0 < a) :
    HasDerivAt (fun c => kepStepSlopeFirst f f' β c t)
      (kepStepSlopeSecond f f' f'' β a t) a := by
  have hp := hasDerivAt_kepStepSpatial_slope hd β t ha
  have hdp := hasDerivAt_kepStepSpatialFirst_slope hdd β t ha
  have hc : HasDerivAt (fun c : ℝ => (β - t) / c) (-((β - t) / a ^ 2)) a := by
    simpa only [div_eq_mul_inv, mul_neg] using (hasDerivAt_inv ha.ne').const_mul (β - t)
  convert ((hp.neg.div (hasDerivAt_id a) ha.ne').add (hc.mul hdp)) using 1 <;>
    first | rfl |
      (dsimp [kepStepSlopeFirst, kepStepSlopeSecond]; field_simp; ring)

theorem kepStepSpatial_reverse (f : ℝ → ℝ) (a t : ℝ) :
    kepStepSpatial f (-1) (-a) t = kepStepSpatial f 1 a (-t) := by
  have he : (-1 - t) / (-a) = (1 - (-t)) / a := by ring
  simp only [kepStepSpatial, he, abs_neg]

/-- The physical positive slope parameter for the reverse residual is also
covered, although its signed parameter in `kepStepSpatial` is negative. -/
theorem hasDerivAt_kepStepSpatial_reverse_slope {f f' : ℝ → ℝ}
    (hd : ∀ x, HasDerivAt f (f' x) x) (t : ℝ) {a : ℝ} (ha : 0 < a) :
    HasDerivAt (fun c => kepStepSpatial f (-1) (-c) t)
      (kepStepSlopeFirst f f' 1 a (-t)) a := by
  simpa only [kepStepSpatial_reverse] using hasDerivAt_kepStepSpatial_slope hd 1 (-t) ha

/-- The true reference density discharges both classical derivative inputs. -/
theorem kepReference_step_slope_derivatives {eps : ℝ}
    (heps : kepReferenceClassicalThreshold ≤ eps) {j : ℕ} (hj : 1 ≤ j)
    (β t : ℝ) {a : ℝ} (ha : 0 < a) :
    let f := (kepReferenceDensity heps hj).density
    let f' := gammaScaledFirst (kepReferenceWeights eps j) (kepReferenceSpan eps j)
    let f'' := gammaScaledSecond (kepReferenceWeights eps j) (kepReferenceSpan eps j)
    HasDerivAt (fun c => kepStepSpatial f β c t) (kepStepSlopeFirst f f' β a t) a ∧
      HasDerivAt (fun c => kepStepSpatialFirst f' β c t)
        (-2 / a * kepStepSpatialFirst f' β a t +
          (β - t) / a * kepStepSpatialSecond f'' β a t) a ∧
      HasDerivAt (fun c => kepStepSlopeFirst f f' β c t)
        (kepStepSlopeSecond f f' f'' β a t) a := by
  have hc := kepReferenceDensity_classical heps hj
  exact ⟨hasDerivAt_kepStepSpatial_slope hc.2.1 β t ha,
    hasDerivAt_kepStepSpatialFirst_slope hc.2.2.1 β t ha,
    hasDerivAt_kepStepSlopeFirst hc.2.1 hc.2.2.1 β t ha⟩

end

end PGM
