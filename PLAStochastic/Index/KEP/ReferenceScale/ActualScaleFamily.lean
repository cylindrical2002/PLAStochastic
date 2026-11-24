import PLAStochastic.Index.KEP.ReferenceScale.WeightedInterpolation
import PLAStochastic.ForMathlib.Analysis.SpecialFunctions.ExponentialWeight
import PLAStochastic.ForMathlib.Probability.Hellinger.ScaleMeasure

/-!
# Actual scale regularity for every sufficiently small fixed weight

The weight can be chosen after the kernel series exponent has been selected.
Only its upper threshold and the epsilon threshold are selected first; the
Hellinger constant may depend on the selected positive weight. No layer-dependent
analytic hypotheses are introduced.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory Set

theorem kepReference_actual_scale_bound_for_small_weights :
    ∃ thetaMax eps0 : ℝ, 0 < thetaMax ∧
      kepReferenceClassicalThreshold ≤ eps0 ∧
      ∀ theta : ℝ, 0 < theta → theta ≤ thetaMax → ∃ K : ℝ, 0 < K ∧
      ∀ eps, eps0 ≤ eps → ∀ j, 1 ≤ j → ∀ s : ℝ,
        let P : Measure ℝ := (kepReferenceLaw eps j : Measure ℝ)
        let : IsProbabilityMeasure (P.map (fun x => Real.exp s * x)) :=
          Measure.isProbabilityMeasure_map (measurable_const.mul measurable_id).aemeasurable
        measureHellinger (P.map (fun x => Real.exp s * x)) P ≤
          K * Real.sqrt (1 + kepReferenceWeightedSecondNorm theta eps j) *
            |s| ^ (2 / 3 : ℝ) := by
  obtain ⟨D, theta0, vlo, vhi, e0, hD, ht0, hvlo, -, hreg⟩ := kepReferenceLaw_regular
  let thetaMax := min (theta0 / 2) (1 / 2)
  have hmax : 0 < thetaMax := lt_min (by positivity) (by norm_num)
  refine ⟨thetaMax, max kepReferenceClassicalThreshold e0, hmax, le_max_left _ _, ?_⟩
  intro theta ht htheta
  have htHalf : theta ≤ theta0 / 2 := htheta.trans (min_le_left _ _)
  have htOne : theta ≤ 1 / 2 := htheta.trans (min_le_right _ _)
  let M := 2 * D / theta0
  let F := 2 * (1 + 4 * theta) * ((2 + theta + theta ^ 2) * M + 1)
  let C1 := 1 + F / theta
  let C2 := 1 + 3 * F / theta + 2 / theta ^ 2
  have hM : 0 < M := by dsimp [M]; positivity
  have hF : 0 < F := by dsimp [F]; positivity
  have hC1 : 0 < C1 := by dsimp [C1]; positivity
  have hC2 : 0 < C2 := by dsimp [C2]; positivity
  refine ⟨2 * Real.sqrt (2 * C2) + Real.sqrt C1 / 2, by positivity, ?_⟩
  intro eps he j hj s
  dsimp only
  have heps : kepReferenceClassicalThreshold ≤ eps := (le_max_left _ _).trans he
  have hr : e0 ≤ eps := (le_max_right _ _).trans he
  let p := kepReferenceDensity heps hj
  let f' := gammaScaledFirst (kepReferenceWeights eps j) (kepReferenceSpan eps j)
  let f'' := gammaScaledSecond (kepReferenceWeights eps j) (kepReferenceSpan eps j)
  let J := kepReferenceWeightedSecondNorm theta eps j
  have hJ : 0 ≤ J := kepReferenceWeightedSecondNorm_nonneg theta eps j
  have hc := kepReferenceDensity_classical heps hj
  have hfm : Measurable f' :=
    (continuous_iff_continuousAt.mpr fun t => (hc.2.2.1 t).continuousAt).measurable
  have hfmm : Measurable f'' := hc.2.2.2.1.measurable
  obtain ⟨hi', hi'', -, -⟩ := kepReferenceDensity_weighted_of_regular heps hj ht0 hvlo
    (hreg eps hr j) ht.le htHalf htOne
  obtain ⟨hip1, hp1⟩ := integrableOn_pow_exp_mul_of_exp_weight hfm
    (show 0 < theta from ht) hi' 1
  obtain ⟨hip2, hp2⟩ := integrableOn_pow_exp_mul_of_exp_weight hfmm
    (show 0 < theta from ht) hi'' 2
  simp only [zero_mul, Real.exp_zero, mul_one, pow_one, sub_zero, Nat.factorial_one,
    Nat.cast_one] at hip1 hp1
  norm_num only [Nat.factorial, Nat.cast_ofNat] at hp2
  simp only [zero_mul, Real.exp_zero, mul_one, sub_zero] at hip2 hp2
  have hfirst := kepReferenceWeightedFirstNorm_le_of_regular heps hj ht0 hvlo
    (hreg eps hr j) ht.le htHalf htOne
  have hsqrt : Real.sqrt (1 + J) ≤ 1 + J := by
    have hs0 := Real.sqrt_nonneg (1 + J)
    have hsq := Real.sq_sqrt (by linarith : 0 ≤ 1 + J)
    nlinarith only [hs0, hsq, hJ]
  have hfirst' : (∫ t, Real.exp (theta * t) * |f' t|) ≤ F * (1 + J) :=
    hfirst.trans (mul_le_mul_of_nonneg_left hsqrt hF.le)
  have hp1' : (∫ t in Ioi (0 : ℝ), |t * f' t|) ≤ (F / theta) * (1 + J) := by
    apply hp1.trans
    convert mul_le_mul_of_nonneg_left hfirst' (by positivity : 0 ≤ 1 / theta) using 1; ring
  have hp2' : (∫ t in Ioi (0 : ℝ), |t ^ 2 * f'' t|) ≤ (2 / theta ^ 2) * J := by
    simpa only [J, kepReferenceWeightedSecondNorm, f''] using hp2
  have hi0 : IntegrableOn p.density (Ioi (0 : ℝ)) volume := p.integrable.integrableOn
  have hmass : (∫ t in Ioi (0 : ℝ), p.density t) ≤ 1 :=
    (setIntegral_le_integral p.integrable (ae_of_all _ p.nonneg)).trans_eq p.integral_eq_one
  have hiLog1 : IntegrableOn (fun t => p.density t + t * f' t) (Ioi (0 : ℝ)) volume := hi0.add hip1
  have hiLog2 : IntegrableOn (fun t => p.density t + 3 * t * f' t + t ^ 2 * f'' t)
      (Ioi (0 : ℝ)) volume := by
    have heq : (fun t => p.density t + 3 * t * f' t + t ^ 2 * f'' t) =
        (p.density + fun t => 3 * (t * f' t)) + fun t => t ^ 2 * f'' t := by
      funext t
      dsimp only [Pi.add_apply]
      ring
    rw [heq]
    exact (hi0.add (hip1.const_mul 3)).add hip2
  have hlog1 : (∫ t in Ioi (0 : ℝ), |p.density t + t * f' t|) ≤ C1 * (1 + J) := by
    calc
      _ ≤ ∫ t in Ioi (0 : ℝ), p.density t + |t * f' t| := by
        apply integral_mono hiLog1.abs (hi0.add hip1.abs)
        intro t
        simpa only [abs_of_nonneg (p.nonneg t), Pi.add_apply] using abs_add_le (p.density t) (t * f' t)
      _ = (∫ t in Ioi (0 : ℝ), p.density t) + ∫ t in Ioi (0 : ℝ), |t * f' t| :=
        integral_add hi0 hip1.abs
      _ ≤ 1 + (F / theta) * (1 + J) := add_le_add hmass hp1'
      _ ≤ _ := by dsimp [C1]; nlinarith only [hJ]
  have hlog2 : (∫ t in Ioi (0 : ℝ), |p.density t + 3 * t * f' t + t ^ 2 * f'' t|) ≤
      C2 * (1 + J) := by
    calc
      _ ≤ ∫ t in Ioi (0 : ℝ), p.density t + 3 * |t * f' t| + |t ^ 2 * f'' t| := by
        apply integral_mono hiLog2.abs ((hi0.add (hip1.abs.const_mul 3)).add hip2.abs)
        intro t
        have hb := (abs_add_le (p.density t + 3 * t * f' t) (t ^ 2 * f'' t)).trans
          (add_le_add (abs_add_le (p.density t) (3 * t * f' t)) le_rfl)
        simpa only [abs_of_nonneg (p.nonneg t), show 3 * t * f' t = 3 * (t * f' t) by ring,
          abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 3), Pi.add_apply] using hb
      _ = (∫ t in Ioi (0 : ℝ), p.density t) +
          3 * (∫ t in Ioi (0 : ℝ), |t * f' t|) + ∫ t in Ioi (0 : ℝ), |t ^ 2 * f'' t| := by
        rw [integral_add (f := fun t => p.density t + 3 * |t * f' t|)
          (g := fun t => |t ^ 2 * f'' t|) (hi0.add (hip1.abs.const_mul 3)) hip2.abs,
          integral_add hi0 (hip1.abs.const_mul 3), integral_const_mul]
      _ ≤ 1 + 3 * ((F / theta) * (1 + J)) + (2 / theta ^ 2) * J := by gcongr
      _ ≤ _ := by
        have hcoef : 0 ≤ 2 / theta ^ 2 := by positivity
        have heq : C2 * (1 + J) =
            1 + 3 * ((F / theta) * (1 + J)) + (2 / theta ^ 2) * J + J + 2 / theta ^ 2 := by
          dsimp [C2]
          ring
        rw [heq]
        linarith only [hJ, hcoef]
  have hh := p.measureHellinger_scale_le_two_thirds hc.1 hc.2.1 hc.2.2.1 hfm hfmm hiLog1 hiLog2 s
  have hs1 : Real.sqrt (∫ t in Ioi (0 : ℝ), |p.density t + t * f' t|) ≤
      Real.sqrt C1 * Real.sqrt (1 + J) := by
    rw [← Real.sqrt_mul hC1.le]
    exact Real.sqrt_le_sqrt hlog1
  have hs2 : Real.sqrt (2 * ∫ t in Ioi (0 : ℝ),
      |p.density t + 3 * t * f' t + t ^ 2 * f'' t|) ≤
      Real.sqrt (2 * C2) * Real.sqrt (1 + J) := by
    rw [← Real.sqrt_mul (by positivity : 0 ≤ 2 * C2)]
    apply Real.sqrt_le_sqrt
    nlinarith only [hlog2]
  have hcoef :
      2 * Real.sqrt (2 * ∫ t in Ioi (0 : ℝ), |p.density t + 3 * t * f' t + t ^ 2 * f'' t|) +
        Real.sqrt (∫ t in Ioi (0 : ℝ), |p.density t + t * f' t|) / 2 ≤
      (2 * Real.sqrt (2 * C2) + Real.sqrt C1 / 2) * Real.sqrt (1 + J) := by
    calc
      _ ≤ 2 * (Real.sqrt (2 * C2) * Real.sqrt (1 + J)) +
          (Real.sqrt C1 * Real.sqrt (1 + J)) / 2 := by gcongr
      _ = _ := by ring
  have hbound := hh.trans (mul_le_mul_of_nonneg_right hcoef (Real.rpow_nonneg (abs_nonneg s) _))
  simpa only [p, kepReferenceDensity_toMeasure] using hbound

end

end PGM
