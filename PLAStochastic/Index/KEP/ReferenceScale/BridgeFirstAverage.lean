import PLAStochastic.Index.KEP.ReferenceScale.BridgeKernelIdentification
import PLAStochastic.Index.KEP.ReferenceScale.KilledShiftedBounds
import PLAStochastic.Index.KEP.ReferenceScale.LogSlopeIntegral

/-!
# All boundary bridge lengths in the first derivative slope average

The one-step bridge uses the endpoint change of variables, the true two-step
bridge uses one rough convolution, and every longer bridge retains the full
killed exponential rate. There is one input first-derivative norm throughout.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory Set

theorem kepLogBridgeRight_first_exp_bound (ν : ProbabilityMeasure ℝ)
    {f f' : ℝ → ℝ} {D θ vlo vhi K L w a σ : ℝ}
    (H : KrBand D θ vlo vhi K L ν f w w a σ (σ * a))
    (hσ : σ = 1 ∨ σ = -1) (ha : 0 < a) (hpi' : Integrable f' volume)
    (n : ℕ) {x : ℝ} (hx : x ∈ Icc 0 w) (y : ℝ) :
    |kepFixedBridgeRight (kepLogStep f σ) (kepLogStepFirst f' σ)
      w (Real.log a) (n + 1) x y| ≤
      (4 * D * Real.exp (3 / 2) * ∫ t, |f' t|) *
        Real.exp (-kepKilledRate D vlo vhi w * (n + 2 : ℕ)) := by
  have hD := H.hD
  have hJ : 0 ≤ ∫ t, |f' t| := integral_nonneg fun _ => abs_nonneg _
  rw [kepLogBridgeRight_eq_first_convolution ν H.hf H.hf0 H.hfD H.hνf hσ
    (Real.log a) n hx y, Real.exp_log ha]
  cases n with
  | zero =>
    have hr := (kepKilledRate_bounds H.hD H.hvlo H.hvhi H.hw).2
    have he : 1 ≤ Real.exp (3 / 2) *
        Real.exp (-kepKilledRate D vlo vhi w * (0 + 2 : ℕ)) := by
      rw [← Real.exp_add]
      apply Real.one_le_exp_iff.mpr
      norm_num only [Nat.reduceAdd, Nat.cast_ofNat]
      linarith
    exact (krDens_first_rough_bound ν H hpi' 0 x y).trans
      (by nlinarith [mul_le_mul_of_nonneg_left he (by positivity :
        0 ≤ 4 * D * ∫ t, |f' t|)])
  | succ n =>
    have hh := sqrt_krLam_shifted_le_exp H.hD H.hvlo H.hvhi H.hw (n + 3) 3
    simp only [Nat.add_sub_cancel, Nat.cast_ofNat] at hh
    exact (krDens_first_spectral_bound ν H hpi' n x y).trans
      (by simpa only [Nat.add_assoc, Nat.reduceAdd, mul_assoc, mul_left_comm, mul_comm] using
        mul_le_mul_of_nonneg_left hh (by positivity : 0 ≤ 4 * D * ∫ t, |f' t|))

theorem kep_logSlope_interval_volume :
    volume.real (Ioc (Real.log (1 / 2 : ℝ)) (Real.log 2)) ≤ 2 := by
  have hl := Real.log_le_log (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (1 / 2 : ℝ) ≤ 2)
  rw [Real.volume_real_Ioc_of_le hl]
  have hlog := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
  have he : Real.log (1 / 2 : ℝ) = -Real.log 2 := by
    rw [one_div, Real.log_inv]
  rw [he]
  linarith

theorem kepLogBridgeRight_first_boundary_average (ν : ProbabilityMeasure ℝ)
    {f f' : ℝ → ℝ} {D θ vlo vhi K L w σ : ℝ}
    (hD : 0 < D) (hvlo : 0 < vlo) (hvhi : vlo ≤ vhi) (hw : 2 ≤ w)
    (H : ∀ a ∈ Icc (1 / 2 : ℝ) 2, KrBand D θ vlo vhi K L ν f w w a σ (σ * a))
    (hσ : σ = 1 ∨ σ = -1) (hcf' : Continuous f') (hpi' : Integrable f' volume)
    (hz : ∀ t ≤ 0, f' t = 0) (n : ℕ) {x y : ℝ}
    (hx : x = 0 ∨ x = w) (hy : y = 0 ∨ y = w) :
    (∫ s in Ioc (Real.log (1 / 2)) (Real.log 2),
      |kepFixedBridgeRight (kepLogStep f σ) (kepLogStepFirst f' σ) w s n x y|) ≤
      ((2 + 8 * D) * Real.exp 2 * ∫ t, |f' t|) *
        Real.exp (-kepKilledRate D vlo vhi w * (n + 1 : ℕ)) := by
  let J := ∫ t, |f' t|
  let r := kepKilledRate D vlo vhi w
  have hJ : 0 ≤ J := integral_nonneg fun _ => abs_nonneg _
  have hr := (kepKilledRate_bounds hD hvlo hvhi (by linarith : 1 ≤ w)).2
  have hxband : x ∈ Icc 0 w := by
    rcases hx with rfl | rfl <;> constructor <;> linarith
  cases n with
  | zero =>
    have hc : Continuous (fun s => kepLogStepFirst f' σ s (y - x)) :=
      (continuous_kepLogStepFirst hcf' σ).comp (continuous_id.prodMk continuous_const)
    have hs := kep_setIntegral_abs_logSlope_le hc
      (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (1 / 2 : ℝ) ≤ 2)
    have heq : (fun a => |kepLogStepFirst f' σ (Real.log a) (y - x)|) =ᵐ[
        volume.restrict (Icc (1 / 2 : ℝ) 2)]
        (fun a => |kepStepSpatialFirst f' σ (σ * a) (y - x)|) := by
      filter_upwards [ae_restrict_mem measurableSet_Icc] with a ha
      rw [kepLogStepFirst_eq_kepStepSpatialFirst f' hσ,
        Real.exp_log (by linarith [ha.1] : 0 < a)]
    rw [integral_congr_ae heq] at hs
    have havg : (∫ a in Icc (1 / 2 : ℝ) 2,
        |kepStepSpatialFirst f' σ (σ * a) (y - x)|) ≤ J := by
      rcases hσ with rfl | rfl
      · simpa only [one_mul] using
          (kepStepSpatialFirst_endpoint_slope_budget hpi' hz hw hy hx
            (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (1 / 2 : ℝ) ≤ 2)).2
      · simpa only [neg_one_mul] using
          (kepStepSpatialFirst_reverse_endpoint_slope_budget hpi' hz hw hy hx
            (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (1 / 2 : ℝ) ≤ 2)).2
    have he : 1 ≤ Real.exp 2 * Real.exp (-r * (0 + 1 : ℕ)) := by
      rw [← Real.exp_add]
      apply Real.one_le_exp_iff.mpr
      norm_num only [Nat.reduceAdd, Nat.cast_one, mul_one]
      linarith
    change _ ≤ ((2 + 8 * D) * Real.exp 2 * J) * Real.exp (-r * (0 + 1 : ℕ))
    calc
      _ ≤ 2 * J := by
        simpa only [kepFixedBridgeRight, one_div, inv_inv] using hs.trans
          (mul_le_mul_of_nonneg_left havg (by norm_num : 0 ≤ (1 / 2 : ℝ)⁻¹))
      _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_left he hJ]
  | succ n =>
    let C := (4 * D * Real.exp (3 / 2) * J) * Real.exp (-r * (n + 2 : ℕ))
    have hC : 0 ≤ C := by dsimp [C]; positivity
    have hb (s : ℝ) (hs : s ∈ Ioc (Real.log (1 / 2)) (Real.log 2)) :
        |kepFixedBridgeRight (kepLogStep f σ) (kepLogStepFirst f' σ) w s (n + 1) x y| ≤ C := by
      have ha : Real.exp s ∈ Icc (1 / 2 : ℝ) 2 := by
        constructor
        · have hh := Real.exp_le_exp.mpr hs.1.le
          rwa [Real.exp_log (by norm_num : (0 : ℝ) < 1 / 2)] at hh
        · have hh := Real.exp_le_exp.mpr hs.2
          rwa [Real.exp_log (by norm_num : (0 : ℝ) < 2)] at hh
      have hh := kepLogBridgeRight_first_exp_bound ν (H _ ha) hσ (Real.exp_pos s)
        hpi' n hxband y
      simpa only [Real.log_exp] using hh
    have hi := norm_integral_le_of_norm_le_const (μ := volume.restrict
      (Ioc (Real.log (1 / 2 : ℝ)) (Real.log 2))) (C := C)
      (f := fun s => |kepFixedBridgeRight (kepLogStep f σ) (kepLogStepFirst f' σ)
        w s (n + 1) x y|)
      (by filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
          simpa only [Real.norm_eq_abs, abs_abs] using hb s hs)
    rw [Real.norm_eq_abs, abs_of_nonneg (setIntegral_nonneg measurableSet_Ioc
      (fun _ _ => abs_nonneg _)), measureReal_restrict_apply_univ] at hi
    have hm := mul_le_mul_of_nonneg_left kep_logSlope_interval_volume hC
    calc
      _ ≤ C * 2 := hi.trans hm
      _ = (8 * D * Real.exp (3 / 2) * J) * Real.exp (-r * (n + 2 : ℕ)) := by
        dsimp [C]
        ring
      _ ≤ (8 * D * Real.exp 2 * J) * Real.exp (-r * (n + 2 : ℕ)) := by
        gcongr
        norm_num
      _ ≤ _ := by
        gcongr
        linarith

end

end PGM
