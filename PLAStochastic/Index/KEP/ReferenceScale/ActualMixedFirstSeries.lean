import PLAStochastic.Index.KEP.ReferenceScale.ActualLongKernelFirst
import PLAStochastic.Index.KEP.ReferenceScale.ActualLongKernelQuantitative

/-!
# Two first-derivative factors in the actual reference graph

The long factor uses its derivative-free regular part. The short factor keeps
its killed spectral decay. Their compact-slope product series therefore has a
polynomial epsilon budget with a square-root input norm and an exponentially
small linear input norm. No product of two rough derivative estimates is used.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory Set

def kepReferenceFirstKernel {eps : ℝ} (heps : kepReferenceClassicalThreshold ≤ eps)
    {j : ℕ} (hj : 1 ≤ j) (w σ : ℝ) (n : ℕ) (x y a : ℝ) : ℝ :=
  truncatedConvolution 0 w
    (kepStepSpatialFirst
      (gammaScaledFirst (kepReferenceWeights eps j) (kepReferenceSpan eps j)) σ (σ * a))
    (fun z => krDens (Icc 0 w) (kepReferenceLaw eps j)
      (kepReferenceDensity heps hj).density σ (σ * a) (n + 2) x z) y

theorem measurable_kepReferenceFirstKernel {eps : ℝ}
    (heps : kepReferenceClassicalThreshold ≤ eps) {j : ℕ} (hj : 1 ≤ j)
    (w σ : ℝ) (n : ℕ) (x y : ℝ) :
    Measurable (kepReferenceFirstKernel heps hj w σ n x y) := by
  have hf := (kepReferenceDensity heps hj).measurable
  have hf' := (continuous_iff_continuousAt.mpr fun t =>
    ((kepReferenceDensity_classical heps hj).2.2.1 t).continuousAt).measurable
  have hp : Measurable (fun t : ℝ × ℝ =>
      kepStepSpatialFirst
        (gammaScaledFirst (kepReferenceWeights eps j) (kepReferenceSpan eps j))
        σ (σ * t.1) (y - t.2)) := by
    unfold kepStepSpatialFirst
    fun_prop
  have hk : Measurable (fun t : ℝ × ℝ => krDens (Icc 0 w) (kepReferenceLaw eps j)
      (kepReferenceDensity heps hj).density σ (σ * t.1) (n + 2) x t.2) :=
    measurable_krDens_param (kepReferenceLaw eps j) measurableSet_Icc hf
      (measurable_const : Measurable (fun _ : ℝ × ℝ => σ))
      (measurable_const.mul measurable_fst)
      (measurable_const : Measurable (fun _ : ℝ × ℝ => x)) measurable_snd (n + 2)
  exact (hp.mul hk).stronglyMeasurable.integral_prod_right'.measurable

theorem kepReference_mixed_first_series_polynomial_budget :
    ∃ D vlo vhi theta c eps0 : ℝ,
      0 < D ∧ 0 < vlo ∧ vlo ≤ vhi ∧ 0 < theta ∧ 0 < c ∧
      kepReferenceClassicalThreshold ≤ eps0 ∧
      ∀ p : ℕ, ∃ K : ℝ, 0 < K ∧
        ∀ eps, eps0 ≤ eps → ∀ heps : kepReferenceClassicalThreshold ≤ eps,
          ∀ j, ∀ hj : 1 ≤ j, ∀ σA σB : ℝ,
          (σA = 1 ∨ σA = -1) → (σB = 1 ∨ σB = -1) →
          ∀ n m N : ℕ, 8 ≤ N → eps ≤ (N / 2 : ℕ) →
          ∀ xA yA xB yB : ℝ,
          let C := segMean expSeqMeasure eps (epLayerSeq eps expCoord j)
          let F := fun k : ℕ => (k + N + 1 : ℝ) ^ p *
            Real.exp (2 * theta * (k + N) / C) *
            (∫ a in Icc (1 / 2 : ℝ) 2,
              |kepReferenceFirstKernel heps hj (2 * eps) σA n xA yA a *
                kepReferenceFirstKernel heps hj (2 * eps) σB (m + k + N) xB yB a|)
          Summable F ∧ (∑' k : ℕ, F k) ≤
            K * eps ^ (2 * p + 4) * Real.sqrt (krLam D vlo vhi (2 * eps)) ^ n *
              (1 + Real.sqrt (kepReferenceSecondNorm eps j) +
                Real.exp (-c * eps) * kepReferenceSecondNorm eps j) := by
  obtain ⟨D, vlo, vhi, e0, hD, hvlo, hvhi, he0, hactual⟩ :=
    kepReference_first_short_long_uniform
  obtain ⟨c, hc, hdecay⟩ := kepLong_geometric_cutoff_decay hD hvlo hvhi
  let cb := cBr (bIn 1 1) (vIn 1 1)
  let theta := krKappa D vlo vhi / (256 * cb)
  have hcb1 : 1 ≤ cb := one_le_cBr (bAbs_le_bIn 1 1)
  have hcb : 0 < cb := by linarith
  have hκ := krKappa_pos hD hvlo hvhi
  have htheta : 0 < theta := by dsimp [theta]; positivity
  refine ⟨D, vlo, vhi, theta, c, e0, hD, hvlo, hvhi, htheta, hc, he0, ?_⟩
  intro p
  obtain ⟨K, hK, hsum⟩ := tsum_polynomial_weighted_kepLongFirstBudget_tail_le hD hvlo hvhi p
  refine ⟨72 * D * K * 2 ^ (2 * p + 4), by positivity, ?_⟩
  intro eps he heps j hj σA σB hσA hσB n m N hN hcut xA yA xB yB
  dsimp only
  have heps2 : 2 ≤ eps := (le_max_left _ _).trans heps
  have hepspos : 0 < eps := by linarith
  have hepssq : 0 < eps ^ 2 := by positivity
  let C := segMean expSeqMeasure eps (epLayerSeq eps expCoord j)
  have hC : eps ^ 2 / cb ≤ C :=
    (segMean_bracket gapLaw_expCoord ((le_max_right _ _).trans heps) j).1
  have hC0 : 0 < C := (div_pos hepssq hcb).trans_le hC
  let eta := 2 * theta / C
  have heta : eta ≤ krKappa D vlo vhi / (16 * (2 * eps) ^ 2) := by
    calc
      eta ≤ 2 * theta / (eps ^ 2 / cb) :=
        div_le_div_of_nonneg_left (by positivity) (div_pos hepssq hcb) hC
      _ = krKappa D vlo vhi / (128 * eps ^ 2) := by
        dsimp [theta]
        field_simp
        ring
      _ ≤ krKappa D vlo vhi / (16 * (2 * eps) ^ 2) := by
        apply div_le_div_of_nonneg_left hκ.le (by positivity)
        nlinarith
  let J := kepReferenceSecondNorm eps j
  let S := Real.sqrt (1 + J)
  let r := Real.sqrt (krLam D vlo vhi (2 * eps))
  have hJ : 0 ≤ J := kepReferenceSecondNorm_nonneg eps j
  have hS : 0 ≤ S := Real.sqrt_nonneg _
  have hr : 0 ≤ r := Real.sqrt_nonneg _
  have hnonneg (k : ℕ) : 0 ≤ kepLongFirstBudget D vlo vhi (2 * eps) (k + N) (3 * S) := by
    have hV := kepLongUniformVariation_nonneg (w := 2 * eps) (k + N) hD hvlo hvhi
    have hR := kepLongUniformRemainder_nonneg D vlo vhi (2 * eps) (k + N)
    dsimp [kepLongFirstBudget]
    positivity
  have hprod (k : ℕ) :
      IntegrableOn (fun a =>
        |kepReferenceFirstKernel heps hj (2 * eps) σA n xA yA a *
          kepReferenceFirstKernel heps hj (2 * eps) σB (m + k + N) xB yB a|)
        (Icc (1 / 2 : ℝ) 2) ∧
      (∫ a in Icc (1 / 2 : ℝ) 2,
        |kepReferenceFirstKernel heps hj (2 * eps) σA n xA yA a *
          kepReferenceFirstKernel heps hj (2 * eps) σB (m + k + N) xB yB a|) ≤
        18 * D * S * r ^ n * kepLongFirstBudget D vlo vhi (2 * eps) (k + N) (3 * S) := by
    have hm := ((measurable_kepReferenceFirstKernel heps hj (2 * eps) σA n xA yA).mul
      (measurable_kepReferenceFirstKernel heps hj (2 * eps) σB (m + k + N) xB yB)).abs
    have hb (a : ℝ) (ha : a ∈ Icc (1 / 2 : ℝ) 2) :
        |kepReferenceFirstKernel heps hj (2 * eps) σA n xA yA a *
          kepReferenceFirstKernel heps hj (2 * eps) σB (m + k + N) xB yB a| ≤
        (12 * D * S * r ^ n) * kepLongFirstBudget D vlo vhi (2 * eps) (k + N) (3 * S) := by
      rw [abs_mul]
      have hA := (hactual eps he heps j hj (2 * eps) a σA (by linarith) ha.1 ha.2 hσA).1 n xA yA
      have hB := (hactual eps he heps j hj (2 * eps) a σB (by linarith) ha.1 ha.2 hσB).2
        m (k + N) (by omega) xB yB
      rw [show m + (k + N) + 2 = (m + k + N) + 2 by omega] at hB
      exact mul_le_mul hA hB (abs_nonneg _) (by positivity)
    have hi : IntegrableOn (fun a =>
        |kepReferenceFirstKernel heps hj (2 * eps) σA n xA yA a *
          kepReferenceFirstKernel heps hj (2 * eps) σB (m + k + N) xB yB a|)
        (Icc (1 / 2 : ℝ) 2) := by
      apply (integrableOn_const (by simp : volume (Icc (1 / 2 : ℝ) 2) ≠ ⊤)
        (C := (12 * D * S * r ^ n) * kepLongFirstBudget D vlo vhi (2 * eps) (k + N) (3 * S))).mono'
        hm.aestronglyMeasurable
      filter_upwards [ae_restrict_mem measurableSet_Icc] with a ha
      simpa only [Real.norm_eq_abs, abs_abs, Pi.mul_apply] using hb a ha
    refine ⟨hi, ?_⟩
    calc
      _ ≤ ∫ _a in Icc (1 / 2 : ℝ) 2,
          (12 * D * S * r ^ n) * kepLongFirstBudget D vlo vhi (2 * eps) (k + N) (3 * S) :=
        setIntegral_mono_on hi (integrable_const _)
          measurableSet_Icc hb
      _ = _ := by simp only [integral_const, Measure.real]; norm_num; ring
  obtain ⟨hs, hb⟩ := hsum (2 * eps) eta (by linarith) heta N (3 * S) (by positivity)
  let G := fun k : ℕ => (18 * D * S * r ^ n) *
    ((k + N + 1 : ℝ) ^ p * Real.exp (eta * (k + N)) *
      kepLongFirstBudget D vlo vhi (2 * eps) (k + N) (3 * S))
  have hsG : Summable G := hs.mul_left _
  have hFG (k : ℕ) : (k + N + 1 : ℝ) ^ p *
      Real.exp (2 * theta * (k + N) / C) *
      (∫ a in Icc (1 / 2 : ℝ) 2,
        |kepReferenceFirstKernel heps hj (2 * eps) σA n xA yA a *
          kepReferenceFirstKernel heps hj (2 * eps) σB (m + k + N) xB yB a|) ≤ G k := by
    have heq : 2 * theta * ((k : ℝ) + N) / C = eta * ((k : ℝ) + N) := by dsimp [eta]; ring
    rw [heq]
    exact (mul_le_mul_of_nonneg_left (hprod k).2 (by positivity)).trans_eq (by dsimp [G]; ring)
  have hsF := hsG.of_nonneg_of_le (fun k => mul_nonneg (by positivity)
    (setIntegral_nonneg measurableSet_Icc (fun _ _ => abs_nonneg _))) hFG
  refine ⟨hsF, ?_⟩
  have hsqrt : S ≤ 1 + Real.sqrt J := by
    have hs1 := Real.sq_sqrt (by linarith : 0 ≤ 1 + J)
    have hs0 := Real.sq_sqrt hJ
    have h0 := Real.sqrt_nonneg J
    dsimp [S]
    nlinarith
  have hdec := hdecay eps N hcut
  have hdec1 : Real.exp (-c * eps) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
  have hnorm : S * (1 + Real.sqrt (1 - killCnu D vlo vhi) ^ (N / 2) * (3 * S)) ≤
      4 * (1 + Real.sqrt J + Real.exp (-c * eps) * J) := by
    have hsq : S ^ 2 = 1 + J := Real.sq_sqrt (by linarith)
    calc
      _ = S + 3 * Real.sqrt (1 - killCnu D vlo vhi) ^ (N / 2) * (1 + J) := by
        nlinarith [hsq]
      _ ≤ 1 + Real.sqrt J + 3 * Real.exp (-c * eps) * (1 + J) := by gcongr
      _ ≤ _ := by nlinarith [Real.sqrt_nonneg J, mul_nonneg (Real.exp_pos (-c * eps)).le hJ]
  calc
    _ ≤ ∑' k : ℕ, G k := hsF.tsum_le_tsum hFG hsG
    _ = (18 * D * S * r ^ n) *
        ∑' k : ℕ, (k + N + 1 : ℝ) ^ p * Real.exp (eta * (k + N)) *
          kepLongFirstBudget D vlo vhi (2 * eps) (k + N) (3 * S) := tsum_mul_left
    _ ≤ (18 * D * S * r ^ n) *
        (K * (2 * eps) ^ (2 * p + 4) *
          (1 + Real.sqrt (1 - killCnu D vlo vhi) ^ (N / 2) * (3 * S))) :=
      mul_le_mul_of_nonneg_left hb (by positivity)
    _ = (18 * D * r ^ n * K * (2 * eps) ^ (2 * p + 4)) *
        (S * (1 + Real.sqrt (1 - killCnu D vlo vhi) ^ (N / 2) * (3 * S))) := by ring
    _ ≤ (18 * D * r ^ n * K * (2 * eps) ^ (2 * p + 4)) *
        (4 * (1 + Real.sqrt J + Real.exp (-c * eps) * J)) := by gcongr
    _ = _ := by rw [mul_pow]; ring

end

end PGM
