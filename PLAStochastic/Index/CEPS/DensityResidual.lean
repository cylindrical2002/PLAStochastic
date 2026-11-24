import PLAStochastic.ForMathlib.Analysis.Asymptotics.InverseArithmetic
import PLAStochastic.ForMathlib.Probability.Hellinger.Measure
import PLAStochastic.Index.GEP.Response.OfInterfaces
import PLAStochastic.Index.GEP.Response.Score.UniformBounds

/-!
# Strong density remainders pay for the actual orbit residual

The polynomial factor can be absorbed by a slightly larger exponential weight.
Both the weighted CDF distance and the mean-one variance difference are bounded
by the actual weighted density difference. Truncated sign tests supply the CDF
bound, using the established layer-cake identity.
-/

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set

def cepsDensityWeight (η x : ℝ) : ℝ := (1 + |x|) ^ 2 * Real.exp (η * |x|)

def cepsWeightedL1 (η : ℝ) (f : ℝ → ℝ) : ℝ := ∫ x, cepsDensityWeight η x * |f x|

theorem cepsDensityWeight_nonneg (η x : ℝ) : 0 ≤ cepsDensityWeight η x := by
  unfold cepsDensityWeight
  positivity

theorem cepsWeightedL1_nonneg (η : ℝ) (f : ℝ → ℝ) : 0 ≤ cepsWeightedL1 η f :=
  integral_nonneg fun x => mul_nonneg (cepsDensityWeight_nonneg η x) (abs_nonneg _)

theorem cepsWeightedL1_integrable {η : ℝ} {f : ℝ → ℝ}
    (hf : Integrable (fun x => cepsDensityWeight η x * f x)) :
    Integrable (fun x => cepsDensityWeight η x * |f x|) := by
  simpa only [Real.norm_eq_abs, abs_mul, abs_of_nonneg (cepsDensityWeight_nonneg η _)] using hf.norm

theorem cepsWeightedL1_sub_le {η : ℝ} {f g : ℝ → ℝ}
    (hf : Integrable (fun x => cepsDensityWeight η x * f x))
    (hg : Integrable (fun x => cepsDensityWeight η x * g x)) :
    cepsWeightedL1 η (fun x => f x - g x) ≤ cepsWeightedL1 η f + cepsWeightedL1 η g := by
  have hi : Integrable (fun x => cepsDensityWeight η x * (f x - g x)) := by
    convert! hf.sub hg using 1
    funext x
    simp only [mul_sub, Pi.sub_apply]
  rw [cepsWeightedL1, cepsWeightedL1, cepsWeightedL1,
    ← integral_add (cepsWeightedL1_integrable hf) (cepsWeightedL1_integrable hg)]
  refine integral_mono (cepsWeightedL1_integrable hi)
    ((cepsWeightedL1_integrable hf).add (cepsWeightedL1_integrable hg)) fun x => ?_
  have h := mul_le_mul_of_nonneg_left (abs_sub (f x) (g x)) (cepsDensityWeight_nonneg η x)
  simpa only [mul_add] using h

/-- Expectations of bounded weighted tests depend continuously on the true density. -/
theorem abs_integral_sub_le_cepsWeightedL1 (p q : HellingerDensity (volume : Measure ℝ))
    {η L : ℝ} (_hL : 0 ≤ L)
    (hp : Integrable (fun x => cepsDensityWeight η x * p.density x))
    (hq : Integrable (fun x => cepsDensityWeight η x * q.density x))
    {φ : ℝ → ℝ} (hφ : Measurable φ) (hb : ∀ x, |φ x| ≤ L * cepsDensityWeight η x) :
    |(∫ x, φ x ∂q.toMeasure) - ∫ x, φ x ∂p.toMeasure| ≤
      L * cepsWeightedL1 η (fun x => p.density x - q.density x) := by
  have hint (r : HellingerDensity (volume : Measure ℝ))
      (hr : Integrable (fun x => cepsDensityWeight η x * r.density x)) :
      Integrable (fun x => r.density x * φ x) := by
    refine (hr.const_mul L).mono' (r.measurable.mul hφ).aestronglyMeasurable
      (ae_of_all _ fun x => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (r.nonneg x)]
    have h := mul_le_mul_of_nonneg_left (hb x) (r.nonneg x)
    calc
      _ ≤ r.density x * (L * cepsDensityWeight η x) := h
      _ = L * (cepsDensityWeight η x * r.density x) := by ring
  have hd : Integrable (fun x => cepsDensityWeight η x * (p.density x - q.density x)) := by
    convert! hp.sub hq using 1
    funext x
    simp only [mul_sub, Pi.sub_apply]
  rw [q.integral_toMeasure, p.integral_toMeasure, ← integral_sub (hint q hq) (hint p hp),
    cepsWeightedL1, ← integral_const_mul, ← Real.norm_eq_abs]
  apply norm_integral_le_of_norm_le ((cepsWeightedL1_integrable hd).const_mul L)
  apply ae_of_all
  intro x
  rw [show q.density x * φ x - p.density x * φ x =
    φ x * (q.density x - p.density x) by ring, Real.norm_eq_abs, abs_mul, abs_sub_comm]
  have h := mul_le_mul_of_nonneg_right (hb x) (abs_nonneg (p.density x - q.density x))
  simpa only [mul_assoc] using h

theorem abs_testFn_le_cepsDensityWeight {η : ℝ} (hη : 0 ≤ η)
    {ψ : ℝ → ℝ} (hψ : OutTest η 1 ψ) (x : ℝ) :
    |testFn ψ x| ≤ cepsDensityWeight η x := by
  by_cases hx : 0 ≤ x
  · have h := hψ.abs_testFn_le hη hx
    have hp : x ≤ (1 + |x|) ^ 2 := by rw [abs_of_nonneg hx]; nlinarith
    unfold cepsDensityWeight
    rw [abs_of_nonneg hx]
    calc
      |testFn ψ x| ≤ Real.exp (η * x) * x := by simpa only [one_mul] using h
      _ ≤ (1 + x) ^ 2 * Real.exp (η * x) := by
        have ht := mul_le_mul_of_nonneg_left (by simpa only [abs_of_nonneg hx] using hp)
          (Real.exp_nonneg (η * x))
        simpa only [mul_comm] using ht
  · have he : Ioo (0 : ℝ) x = ∅ := Ioo_eq_empty (by linarith)
    rw [testFn, he, Measure.restrict_empty, integral_zero_measure, abs_zero]
    exact cepsDensityWeight_nonneg η x

/-- No regularity certificate is needed for this density-to-CDF estimate. -/
theorem dEta_le_cepsWeightedL1 (p q : HellingerDensity (volume : Measure ℝ))
    (ν ρ : ProbabilityMeasure ℝ) (hν : (ν : Measure ℝ) = p.toMeasure)
    (hρ : (ρ : Measure ℝ) = q.toMeasure) {η : ℝ} (hη : 0 ≤ η)
    (hp : Integrable (fun x => cepsDensityWeight η x * p.density x))
    (hq : Integrable (fun x => cepsDensityWeight η x * q.density x)) :
    dEta η ν ρ ≤ cepsWeightedL1 η (fun x => p.density x - q.density x) := by
  unfold dEta
  apply integral_Ioi_le_of_Ioc (cepsWeightedL1_nonneg _ _)
  intro n
  have ht := outTest_signTest η (n : ℝ) ν ρ
  have he := integral_testFn_signTest_sub (R := (n : ℝ)) hη ν ρ
  have hb := abs_integral_sub_le_cepsWeightedL1 p q (L := 1) zero_le_one hp hq
    ht.measurable_testFn (by intro x; simpa only [one_mul] using abs_testFn_le_cepsDensityWeight hη ht x)
  rw [← hν, ← hρ, he, one_mul] at hb
  exact (le_abs_self _).trans hb

theorem variance_test_le_cepsDensityWeight {η : ℝ} (hη : 0 ≤ η) (x : ℝ) :
    |(x - 1) ^ 2| ≤ cepsDensityWeight η x := by
  have h := abs_sub x 1
  simp only [abs_one] at h
  have hsq : (x - 1) ^ 2 ≤ (1 + |x|) ^ 2 := by
    have hh := pow_le_pow_left₀ (abs_nonneg (x - 1)) h 2
    simpa only [sq_abs, add_comm] using hh
  have he : 1 ≤ Real.exp (η * |x|) := Real.one_le_exp (mul_nonneg hη (abs_nonneg _))
  rw [abs_of_nonneg (sq_nonneg _), cepsDensityWeight]
  exact hsq.trans (by nlinarith [sq_nonneg (1 + |x|)])

theorem abs_lawVar_sub_le_cepsWeightedL1 (p q : HellingerDensity (volume : Measure ℝ))
    (ν ρ : ProbabilityMeasure ℝ) (hν : (ν : Measure ℝ) = p.toMeasure)
    (hρ : (ρ : Measure ℝ) = q.toMeasure) (hmeanν : lawMean ν = 1) (hmeanρ : lawMean ρ = 1)
    {η : ℝ} (hη : 0 ≤ η)
    (hp : Integrable (fun x => cepsDensityWeight η x * p.density x))
    (hq : Integrable (fun x => cepsDensityWeight η x * q.density x)) :
    |lawVar ρ - lawVar ν| ≤ cepsWeightedL1 η (fun x => p.density x - q.density x) := by
  rw [lawVar, lawVar, hmeanν, hmeanρ, hν, hρ]
  simpa only [one_mul] using abs_integral_sub_le_cepsWeightedL1 p q (L := 1) zero_le_one hp hq
    (by fun_prop : Measurable fun x : ℝ => (x - 1) ^ 2)
    (by intro x; simpa only [one_mul] using variance_test_le_cepsDensityWeight hη x)

/-- Weighted density differences supply both components of the coupled residual. -/
theorem ceps_residual_inverseOrder_of_density {η e0 : ℝ} (hη : 0 ≤ η)
    (p q : ℝ → HellingerDensity (volume : Measure ℝ)) (ν ρ : ℝ → ProbabilityMeasure ℝ)
    (hν : ∀ eps, e0 ≤ eps → (ν eps : Measure ℝ) = (p eps).toMeasure)
    (hρ : ∀ eps, e0 ≤ eps → (ρ eps : Measure ℝ) = (q eps).toMeasure)
    (hmeanν : ∀ eps, e0 ≤ eps → lawMean (ν eps) = 1)
    (hmeanρ : ∀ eps, e0 ≤ eps → lawMean (ρ eps) = 1)
    (hp : ∀ eps, e0 ≤ eps → Integrable (fun x => cepsDensityWeight η x * (p eps).density x))
    (hq : ∀ eps, e0 ≤ eps → Integrable (fun x => cepsDensityWeight η x * (q eps).density x))
    {j : ℕ} (hrem : IsInverseOrder
      (fun eps => cepsWeightedL1 η (fun x => (p eps).density x - (q eps).density x)) (j + 1)) :
    IsInverseOrder (fun eps => dEta η (ν eps) (ρ eps) + |lawVar (ρ eps) - lawVar (ν eps)|) (j + 1) := by
  obtain ⟨K, er, hr⟩ := hrem
  refine ⟨2 * K, max e0 er, fun eps heps => ?_⟩
  have he0 : e0 ≤ eps := (le_max_left _ _).trans heps
  have he : er ≤ eps := (le_max_right _ _).trans heps
  have hD := dEta_le_cepsWeightedL1 (p eps) (q eps) (ν eps) (ρ eps)
    (hν eps he0) (hρ eps he0) hη (hp eps he0) (hq eps he0)
  have hV := abs_lawVar_sub_le_cepsWeightedL1 (p eps) (q eps) (ν eps) (ρ eps)
    (hν eps he0) (hρ eps he0) (hmeanν eps he0) (hmeanρ eps he0) hη (hp eps he0) (hq eps he0)
  rw [abs_of_nonneg (add_nonneg (dEta_nonneg _ _ _) (abs_nonneg _))]
  have hR := hr eps he
  rw [abs_of_nonneg (cepsWeightedL1_nonneg _ _)] at hR
  linarith

/-- The polynomial factor costs only a fixed loss of exponential weight. -/
theorem cepsDensityWeight_le_exp {η θ : ℝ} (hηθ : η < θ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x, cepsDensityWeight η x ≤ C * Real.exp (θ * |x|) := by
  let δ := θ - η
  have hδ : 0 < δ := sub_pos.mpr hηθ
  refine ⟨1 + 2 / δ + 2 / δ ^ 2, by positivity, fun x => ?_⟩
  let y := |x|
  have hy : 0 ≤ y := abs_nonneg _
  have he : 1 ≤ Real.exp (δ * y) := Real.one_le_exp (mul_nonneg hδ.le hy)
  have h₁ : y ≤ δ⁻¹ * Real.exp (δ * y) := by
    have h := Real.add_one_le_exp (δ * y)
    calc
      y = (δ * y) / δ := by field_simp
      _ ≤ Real.exp (δ * y) / δ := div_le_div_of_nonneg_right (by linarith) hδ.le
      _ = _ := by ring
  have h₂ : y ^ 2 ≤ (2 / δ ^ 2) * Real.exp (δ * y) := by
    have h := Real.pow_div_factorial_le_exp (x := δ * y) (mul_nonneg hδ.le hy) 2
    norm_num [Nat.factorial] at h
    calc
      y ^ 2 = (2 / δ ^ 2) * ((δ * y) ^ 2 / 2) := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left h (by positivity)
  have hp : (1 + y) ^ 2 ≤ (1 + 2 / δ + 2 / δ ^ 2) * Real.exp (δ * y) := by
    rw [div_eq_mul_inv (2 : ℝ) δ]
    nlinarith
  have hh := mul_le_mul_of_nonneg_right hp (Real.exp_nonneg (η * y))
  have heq : Real.exp (δ * y) * Real.exp (η * y) = Real.exp (θ * y) := by
    rw [← Real.exp_add]
    congr 1
    dsimp [δ]
    ring
  simpa only [cepsDensityWeight, y, mul_assoc, heq] using hh

theorem cepsWeightedL1_le_expWeightedL1 {η θ : ℝ} (hηθ : η < θ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f : ℝ → ℝ, Measurable f →
      Integrable (fun x => Real.exp (θ * |x|) * f x) →
      cepsWeightedL1 η f ≤ C * ∫ x, Real.exp (θ * |x|) * |f x| := by
  obtain ⟨C, hC, hb⟩ := cepsDensityWeight_le_exp hηθ
  refine ⟨C, hC, fun f hm hi => ?_⟩
  have hlarge : Integrable (fun x => Real.exp (θ * |x|) * |f x|) := by
    simpa only [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.exp_nonneg _)] using hi.norm
  have hsmall : Integrable (fun x => cepsDensityWeight η x * |f x|) := by
    refine (hlarge.const_mul C).mono' (by unfold cepsDensityWeight; fun_prop) (ae_of_all _ fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (cepsDensityWeight_nonneg _ _) (abs_nonneg _))]
    have h := mul_le_mul_of_nonneg_right (hb x) (abs_nonneg (f x))
    simpa only [mul_assoc] using h
  rw [cepsWeightedL1, ← integral_const_mul]
  apply integral_mono hsmall (hlarge.const_mul C)
  intro x
  have h := mul_le_mul_of_nonneg_right (hb x) (abs_nonneg (f x))
  simpa only [mul_assoc] using h

theorem cepsWeightedL1_inverseOrder_of_expWeightedL1 {η θ e0 : ℝ} (hηθ : η < θ)
    (f : ℝ → ℝ → ℝ)
    (hm : ∀ eps, e0 ≤ eps → Measurable (f eps))
    (hi : ∀ eps, e0 ≤ eps → Integrable (fun x => Real.exp (θ * |x|) * f eps x))
    {n : ℕ} (horder : IsInverseOrder (fun eps => ∫ x, Real.exp (θ * |x|) * |f eps x|) n) :
    IsInverseOrder (fun eps => cepsWeightedL1 η (f eps)) n := by
  obtain ⟨C, hC, hb⟩ := cepsWeightedL1_le_expWeightedL1 hηθ
  obtain ⟨K, er, hr⟩ := horder
  refine ⟨C * K, max e0 er, fun eps heps => ?_⟩
  have he0 : e0 ≤ eps := (le_max_left _ _).trans heps
  have he : er ≤ eps := (le_max_right _ _).trans heps
  have hR := hr eps he
  rw [abs_of_nonneg (integral_nonneg fun x => mul_nonneg (Real.exp_nonneg _) (abs_nonneg _))] at hR
  rw [abs_of_nonneg (cepsWeightedL1_nonneg _ _)]
  exact (hb (f eps) (hm eps he0) (hi eps he0)).trans
    (by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hR hC)

/-- Subtraction cancels any common finite density polynomial exactly. -/
theorem cepsWeightedL1_sub_le_common_remainders {η : ℝ} {f g P : ℝ → ℝ}
    (hf : Integrable (fun x => cepsDensityWeight η x * (f x - P x)))
    (hg : Integrable (fun x => cepsDensityWeight η x * (g x - P x))) :
    cepsWeightedL1 η (fun x => f x - g x) ≤
      cepsWeightedL1 η (fun x => f x - P x) + cepsWeightedL1 η (fun x => g x - P x) := by
  have he : (fun x => (f x - P x) - (g x - P x)) = fun x => f x - g x := by
    funext x
    ring
  simpa only [he] using cepsWeightedL1_sub_le hf hg

theorem cepsWeightedL1_inverseOrder_of_common_expansion {η e0 : ℝ}
    (f g P : ℝ → ℝ → ℝ)
    (hf : ∀ eps, e0 ≤ eps → Integrable (fun x => cepsDensityWeight η x * (f eps x - P eps x)))
    (hg : ∀ eps, e0 ≤ eps → Integrable (fun x => cepsDensityWeight η x * (g eps x - P eps x)))
    {j : ℕ}
    (hrf : IsInverseOrder (fun eps => cepsWeightedL1 η (fun x => f eps x - P eps x)) (j + 1))
    (hrg : IsInverseOrder (fun eps => cepsWeightedL1 η (fun x => g eps x - P eps x)) (j + 1)) :
    IsInverseOrder (fun eps => cepsWeightedL1 η (fun x => f eps x - g eps x)) (j + 1) := by
  obtain ⟨K, er, hr⟩ := hrf.add hrg
  refine ⟨K, max e0 er, fun eps heps => ?_⟩
  have he0 : e0 ≤ eps := (le_max_left _ _).trans heps
  have he : er ≤ eps := (le_max_right _ _).trans heps
  have hb := cepsWeightedL1_sub_le_common_remainders (hf eps he0) (hg eps he0)
  have hR := hr eps he
  rw [abs_of_nonneg (add_nonneg (cepsWeightedL1_nonneg _ _) (cepsWeightedL1_nonneg _ _))] at hR
  rw [abs_of_nonneg (cepsWeightedL1_nonneg _ _)]
  exact hb.trans hR

end

end PGM
