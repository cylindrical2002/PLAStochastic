import PLAStochastic.Index.KEP.ReferenceScale.WeightedPolynomialBudget
import PLAStochastic.Index.KEP.ReferenceScale.WeightedInterpolation
import PLAStochastic.ForMathlib.Analysis.Calculus.MellinOperator

/-!
# Weighted first and second Mellin insertions on the actual orbit

The first insertion costs one square root of the weighted second norm. The
second costs one linear factor. No pointwise derivative envelope is assumed.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory Set

theorem kep_mellin_second_eq {f f' f'' : ℝ → ℝ}
    (hdf : ∀ x, HasDerivAt f (f' x) x) (hddf : ∀ x, HasDerivAt f' (f'' x) x) :
    mellinOp (mellinOp f) = fun x => f x + 3 * x * f' x + x ^ 2 * f'' x := by
  have hfirst : mellinOp f = fun x => f x + x * f' x := by
    funext x
    rw [mellinOp, (hdf x).deriv]
  have hd (x : ℝ) : HasDerivAt (mellinOp f) (2 * f' x + x * f'' x) x := by
    rw [hfirst]
    convert (hdf x).add ((hasDerivAt_id x).mul (hddf x)) using 1 <;> first
    | rfl
    | (dsimp only [id_eq]; ring)
  funext x
  rw [mellinOp, (hd x).deriv, hfirst]
  ring

theorem kepReferenceSecond_nonpos {eps : ℝ} (heps : kepReferenceClassicalThreshold ≤ eps)
    {j : ℕ} (_hj : 1 ≤ j) {x : ℝ} (hx : x ≤ 0) :
    gammaScaledSecond (kepReferenceWeights eps j) (kepReferenceSpan eps j) x = 0 := by
  have hm := kepReferenceSpan_pos heps j
  have hmx := mul_nonpos_of_nonneg_of_nonpos hm.le hx
  unfold gammaScaledSecond gammaMixtureSecond
  rw [gammaMixtureDensity_succ_of_nonpos _ 0 hmx,
    gammaMixtureDensity_succ_of_nonpos _ 1 hmx,
    gammaMixtureDensity_succ_of_nonpos _ 2 hmx]
  ring

theorem kep_weighted_norm_add {F G : ℝ → ℝ} (alpha : ℝ)
    (hF : Integrable (fun x => Real.exp (alpha * x) * F x) volume)
    (hG : Integrable (fun x => Real.exp (alpha * x) * G x) volume) :
    (∫ x, Real.exp (alpha * x) * |F x + G x|) ≤
      (∫ x, Real.exp (alpha * x) * |F x|) + ∫ x, Real.exp (alpha * x) * |G x| := by
  have hh := integral_mono (hF.add hG).norm (hF.norm.add hG.norm) (fun x => norm_add_le _ _)
  simp only [Pi.add_apply] at hh
  rw [integral_add hF.norm hG.norm] at hh
  simpa only [Pi.add_apply, ← mul_add, Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)] using hh

theorem kep_weighted_norm_const_mul (F : ℝ → ℝ) (alpha b : ℝ) :
    (∫ x, Real.exp (alpha * x) * |b * F x|) = |b| * ∫ x, Real.exp (alpha * x) * |F x| := by
  simp only [abs_mul]
  rw [← integral_const_mul]
  apply integral_congr_ae
  exact ae_of_all _ fun x => by ring

theorem kepReference_mellin_insertion_budgets :
    ∃ thetaMax eps0 : ℝ, 0 < thetaMax ∧ kepReferenceClassicalThreshold ≤ eps0 ∧
      ∀ theta : ℝ, 0 < theta → theta ≤ thetaMax → ∃ K : ℝ, 0 < K ∧
        ∀ eps, eps0 ≤ eps → ∀ heps : kepReferenceClassicalThreshold ≤ eps,
          ∀ j, ∀ hj : 1 ≤ j,
          let f := (kepReferenceDensity heps hj).density
          let J := kepReferenceWeightedSecondNorm theta eps j
          Integrable (fun x => Real.exp ((theta / 4) * x) * f x) volume ∧
          Integrable (fun x => Real.exp ((theta / 4) * x) * mellinOp f x) volume ∧
          Integrable (fun x => Real.exp ((theta / 4) * x) * mellinOp (mellinOp f) x) volume ∧
          (∫ x, Real.exp ((theta / 4) * x) * |f x|) ≤ K ∧
          (∫ x, Real.exp ((theta / 4) * x) * |mellinOp f x|) ≤ K * Real.sqrt (1 + J) ∧
          (∫ x, Real.exp ((theta / 4) * x) * |mellinOp (mellinOp f) x|) ≤ K * (1 + J) := by
  obtain ⟨D, t0, vlo, vhi, e0, hD, ht0, hvlo, _, hreg⟩ := kepReferenceLaw_regular
  let tMax := min (t0 / 2) (1 / 2)
  refine ⟨tMax, max kepReferenceClassicalThreshold e0, lt_min (by positivity) (by norm_num),
    le_max_left _ _, ?_⟩
  intro theta ht htheta
  have htHalf : theta ≤ t0 / 2 := htheta.trans (min_le_left _ _)
  have htOne : theta ≤ 1 / 2 := htheta.trans (min_le_right _ _)
  let M := 2 * D / t0
  let F := 2 * (1 + 4 * theta) * ((2 + theta + theta ^ 2) * M + 1)
  let P1 := 1 / (theta - theta / 4)
  let P2 := 2 / (theta - theta / 4) ^ 2
  let K := M + (M + P1 * F) + (M + 3 * P1 * F + P2)
  have hM : 0 < M := by dsimp [M]; positivity
  have hF : 0 < F := by dsimp [F]; positivity
  have hgap : 0 < theta - theta / 4 := by linarith
  have hP1 : 0 ≤ P1 := by dsimp [P1]; positivity
  have hP2 : 0 ≤ P2 := by dsimp [P2]; positivity
  refine ⟨K, by dsimp [K]; positivity, ?_⟩
  intro eps he heps j hj
  dsimp only
  let f := (kepReferenceDensity heps hj).density
  let f' := gammaScaledFirst (kepReferenceWeights eps j) (kepReferenceSpan eps j)
  let f'' := gammaScaledSecond (kepReferenceWeights eps j) (kepReferenceSpan eps j)
  let alpha := theta / 4
  let J := kepReferenceWeightedSecondNorm theta eps j
  have hc := kepReferenceDensity_classical heps hj
  have hcf : Continuous f := continuous_iff_continuousAt.mpr fun x => (hc.2.1 x).continuousAt
  have hcf' : Continuous f' := continuous_iff_continuousAt.mpr fun x => (hc.2.2.1 x).continuousAt
  have H := hreg eps ((le_max_right _ _).trans he) j
  obtain ⟨hi1, hi2, _, _⟩ := kepReferenceDensity_weighted_of_regular heps hj ht0 hvlo H ht.le htHalf htOne
  have hfirst := kepReferenceWeightedFirstNorm_le_of_regular heps hj ht0 hvlo H ht.le htHalf htOne
  have hI1 : (∫ x, Real.exp (theta * x) * |f' x|) ≤ F * Real.sqrt (1 + J) := hfirst
  have hEM := (H.expMom ht0).mono (H.momClass ht0 hvlo).pos ht.le htHalf le_rfl
  have hiLaw : Integrable (fun x => Real.exp (theta * x)) (kepReferenceDensity heps hj).toMeasure := by
    rw [kepReferenceDensity_toMeasure heps hj]
    exact hEM.integrable
  have hi0 : Integrable (fun x => Real.exp (theta * x) * f x) volume := by
    simpa only [mul_comm] using ((kepReferenceDensity heps hj).integrable_toMeasure_iff _).mp hiLaw
  have hmass : (∫ x, Real.exp (theta * x) * |f x|) ≤ M := by
    have heq := (kepReferenceDensity heps hj).integral_toMeasure (fun x => Real.exp (theta * x))
    rw [kepReferenceDensity_toMeasure heps hj] at heq
    have hh := hEM.le
    rw [heq] at hh
    change (∫ x, f x * Real.exp (theta * x)) ≤ M at hh
    have hfabs (x : ℝ) : |f x| = f x := abs_of_nonneg ((kepReferenceDensity heps hj).nonneg x)
    simpa only [hfabs, mul_comm] using hh
  have hab : alpha < theta := by dsimp [alpha]; linarith
  obtain ⟨ha0, hb0⟩ := kep_weighted_polynomial_budget hcf.measurable hc.1 hab 0 hi0
  obtain ⟨ha1, hb1⟩ := kep_weighted_polynomial_budget hcf'.measurable
    (fun x hx => kepReferenceFirst_nonpos heps hj hx) hab 1 hi1
  obtain ⟨ha2, hb2⟩ := kep_weighted_polynomial_budget hc.2.2.2.1.measurable
    (fun x hx => kepReferenceSecond_nonpos heps hj hx) hab 2 hi2
  simp only [pow_zero, one_mul, mul_one, Nat.factorial_zero, Nat.cast_one, div_one] at ha0 hb0
  simp only [pow_one, Nat.factorial_one, Nat.cast_one] at ha1 hb1
  norm_num only [Nat.factorial, Nat.cast_ofNat] at hb2
  have ha1 : Integrable (fun x => Real.exp (alpha * x) * (x * f' x)) volume := by
    convert ha1 using 1
    funext x
    ring
  have ha2 : Integrable (fun x => Real.exp (alpha * x) * (x ^ 2 * f'' x)) volume := by
    convert ha2 using 1
    funext x
    ring
  have h1norm : (∫ x, Real.exp (alpha * x) * |x * f' x|) ≤ P1 * F * Real.sqrt (1 + J) := by
    have hh := hb1.trans (mul_le_mul_of_nonneg_left hI1 hP1)
    simpa only [alpha, P1, mul_assoc] using hh
  have h2norm : (∫ x, Real.exp (alpha * x) * |x ^ 2 * f'' x|) ≤ P2 * J := hb2
  have h0norm : (∫ x, Real.exp (alpha * x) * |f x|) ≤ M := hb0.trans hmass
  have he1 : mellinOp f = fun x => f x + x * f' x := by
    funext x
    rw [mellinOp, (hc.2.1 x).deriv]
  have he2 := kep_mellin_second_eq hc.2.1 hc.2.2.1
  have haM1 : Integrable (fun x => Real.exp (alpha * x) * mellinOp f x) volume := by
    rw [he1]
    convert ha0.add ha1 using 1 <;> first | rfl | (funext x; dsimp only [Pi.add_apply]; ring)
  have ha3 : Integrable (fun x => Real.exp (alpha * x) * (3 * (x * f' x))) volume := by
    convert ha1.const_mul 3 using 1
    funext x
    ring
  have haSum : Integrable (fun x => Real.exp (alpha * x) * (f x + 3 * (x * f' x))) volume := by
    convert ha0.add ha3 using 1 <;> first | rfl | (funext x; dsimp only [Pi.add_apply]; ring)
  have haM2 : Integrable (fun x => Real.exp (alpha * x) * mellinOp (mellinOp f) x) volume := by
    rw [he2]
    convert haSum.add ha2 using 1 <;> first
    | rfl
    | (funext x; dsimp only [Pi.add_apply]; ring)
  have hJ0 : 0 ≤ J := kepReferenceWeightedSecondNorm_nonneg theta eps j
  have hsq1 : 1 ≤ Real.sqrt (1 + J) := Real.one_le_sqrt.mpr (by linarith)
  have hsqJ : Real.sqrt (1 + J) ≤ 1 + J := by
    have hh := Real.sq_sqrt (by linarith : 0 ≤ 1 + J)
    have hh0 := Real.sqrt_nonneg (1 + J)
    nlinarith
  have hM1 : (∫ x, Real.exp (alpha * x) * |mellinOp f x|) ≤
      (M + P1 * F) * Real.sqrt (1 + J) := by
    rw [he1]
    have hh := kep_weighted_norm_add alpha ha0 ha1
    have hm := mul_le_mul_of_nonneg_left hsq1 hM.le
    nlinarith only [hh, h0norm, h1norm, hm]
  have hM2 : (∫ x, Real.exp (alpha * x) * |mellinOp (mellinOp f) x|) ≤
      (M + 3 * P1 * F + P2) * (1 + J) := by
    rw [he2]
    have heq : (fun x => f x + 3 * x * f' x + x ^ 2 * f'' x) =
        (fun x => f x + 3 * (x * f' x) + x ^ 2 * f'' x) := by funext x; ring
    change (∫ x, Real.exp (alpha * x) * |(fun x => f x + 3 * x * f' x + x ^ 2 * f'' x) x|) ≤ _
    rw [heq]
    have h3norm : (∫ x, Real.exp (alpha * x) * |3 * (x * f' x)|) ≤
        3 * (P1 * F * Real.sqrt (1 + J)) := by
      rw [kep_weighted_norm_const_mul]
      norm_num only [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 3)]
      exact mul_le_mul_of_nonneg_left h1norm (by norm_num)
    have h01 := kep_weighted_norm_add alpha ha0 ha3
    have h012 := kep_weighted_norm_add alpha haSum ha2
    have hm := mul_le_mul_of_nonneg_left (show 1 ≤ 1 + J by linarith) hM.le
    have hq := mul_le_mul_of_nonneg_left hsqJ (by positivity : 0 ≤ 3 * P1 * F)
    nlinarith only [h01, h012, h0norm, h3norm, h2norm, hm, hq, hP2]
  have hK0 : M ≤ K := by dsimp [K]; nlinarith only [hM.le, hP2, mul_nonneg hP1 hF.le]
  have hK1 : M + P1 * F ≤ K := by dsimp [K]; nlinarith only [hM.le, hP2, mul_nonneg hP1 hF.le]
  have hK2 : M + 3 * P1 * F + P2 ≤ K := by dsimp [K]; nlinarith only [hM.le, hP2, mul_nonneg hP1 hF.le]
  refine ⟨ha0, haM1, haM2, h0norm.trans hK0,
    hM1.trans (mul_le_mul_of_nonneg_right hK1 (Real.sqrt_nonneg _)),
    hM2.trans (mul_le_mul_of_nonneg_right hK2 (by linarith))⟩

end

end PGM
