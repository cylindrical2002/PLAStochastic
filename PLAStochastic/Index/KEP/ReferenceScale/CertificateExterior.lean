import PLAStochastic.Index.KEP.ReferenceScale.CertificateMiddleIdentification
import PLAStochastic.Index.KEP.ReferenceScale.GraphTransfer

/-!
# Identification of both actual certificate exteriors

The exterior reward uses the original iid reverse prefix and forward suffix.
The independent insertion is the product-law Markov identity before selecting
a certificate. Zero-step tails are evaluated at their actual endpoints.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory Set

theorem kepCertificateExterior_eq_rows {eps : ℝ} (_heps : 0 ≤ eps)
    (ν : ProbabilityMeasure ℝ) (k i j : ℕ) {φ : ℝ → ℝ} (hφ : Measurable φ)
    {B : ℝ} (_hB : 0 ≤ B) (hφb : ∀ x, |φ x| ≤ B)
    {a : ℝ} (ha : a ∈ Icc (1 / 2 : ℝ) 2) :
    kepCertificateExterior eps ν k i j φ a =
      krRow (Icc 0 (2 * eps)) (ν : Measure ℝ) (-1) (-a) i
        (fun u => krRow (Icc 0 (2 * eps)) (ν : Measure ℝ) 1 a (k - j)
          (fun v => φ (((k : ℝ) + u - v) / a)) (2 * eps)) 0 := by
  let J := Icc (0 : ℝ) (2 * eps)
  let F : ℝ → (ℕ → ℝ) → ℝ := fun u g =>
    krAlive J 1 a (k - j) (2 * eps) g *
      φ (((k : ℝ) + u - kWalk (2 * eps) 1 a g (k - j)) / a)
  have hFm : Measurable (Function.uncurry F) := by
    exact ((measurable_krAlive_right measurableSet_Icc 1 a (k - j) (2 * eps)).comp
      measurable_snd).mul (hφ.comp (((measurable_const.add measurable_fst).sub
        ((measurable_kWalk_prod 1 a (k - j)).comp
          (measurable_const.prodMk measurable_snd))).div_const a))
  have hFb (u : ℝ) (g : ℕ → ℝ) : |F u g| ≤ B := by
    dsimp only [F]
    rw [abs_mul]
    exact (mul_le_mul (abs_krAlive_le_one _ _ _) (hφb _) (abs_nonneg _) zero_le_one).trans_eq
      (one_mul B)
  have hinner (u : ℝ) : (∫ g, F u g ∂iidLaw ν) =
      krRow J (ν : Measure ℝ) 1 a (k - j)
        (fun v => φ (((k : ℝ) + u - v) / a)) (2 * eps) := by
    exact (krRow_eq_integral (J := J) measurableSet_Icc ν 1 a (k - j)
      (φ := fun v => φ (((k : ℝ) + u - v) / a)) (hφ.comp ((measurable_const.sub measurable_id).div_const a)) (fun v => hφb _) (2 * eps)).symm
  have hm : Measurable (fun u => ∫ g, F u g ∂iidLaw ν) :=
    hFm.stronglyMeasurable.integral_prod_right.measurable
  have hb : ∀ u, |∫ g, F u g ∂iidLaw ν| ≤ B := fun u => kr_abs_integral_le (hFb u)
  have hpre (g : ℕ → ℝ) : surv_preInt eps k i j φ a g =
      (krAlive J (-1) (-a) i 0 g * F (kWalk 0 (-1) (-a) g i)
        (fun s => g (s + i)) : ℂ) := by
    unfold surv_preInt
    rw [indicator_of_mem ha]
    rw [kep_prod_indicator_one_complex, kep_prod_indicator_one_complex, mul_one]
    dsimp only [F]
    unfold krAlive J surv_J
    have hs : (fun s => g (i + s)) = fun s => g (s + i) := by
      funext s
      rw [Nat.add_comm]
    rw [hs]
    simp only [Complex.ofReal_mul]
    ring
  have hcast := kepCertificateExterior_complex eps ν k i j φ a
  rw [surv_pref, kep_surv_wint_zero] at hcast
  simp_rw [hpre, ← Complex.ofReal_mul] at hcast
  rw [integral_complex_ofReal] at hcast
  have hreal := Complex.ofReal_injective hcast
  rw [hreal, kr_integral_markov measurableSet_Icc ν (-1) (-a) i hFm hFb 0]
  dsimp only [J] at hinner
  simp_rw [← hinner]
  exact (krRow_eq_integral measurableSet_Icc ν (-1) (-a) i hm hb 0).symm

/-- Exact two-tail graph reward at every compact physical slope. -/
theorem kepCertificateExterior_eq_tailPair (ν : ProbabilityMeasure ℝ) {f : ℝ → ℝ}
    {D eps : ℝ} (hf : Measurable f) (hf0 : ∀ x, 0 ≤ f x) (hfD : ∀ x, f x ≤ D)
    (hν : (ν : Measure ℝ) = volume.withDensity (fun x => ENNReal.ofReal (f x)))
    (heps : 0 ≤ eps) (k i j : ℕ) {φ : ℝ → ℝ} (hφ : Measurable φ)
    {B : ℝ} (hB : 0 ≤ B) (hφb : ∀ x, |φ x| ≤ B)
    {a : ℝ} (ha : a ∈ Icc (1 / 2 : ℝ) 2) :
    kepCertificateExterior eps ν k i j φ a =
      kepTailPairTest (kepLogStep f (-1)) (kepLogStep f 1) (2 * eps)
        (Real.log a) i (k - j) 0 (2 * eps) (fun u v => φ (((k : ℝ) + u - v) / a)) := by
  have ha0 : 0 < a := by linarith [ha.1]
  let H := fun u => krRow (Icc 0 (2 * eps)) (ν : Measure ℝ) 1 a (k - j)
    (fun v => φ (((k : ℝ) + u - v) / a)) (2 * eps)
  have he (u : ℝ) :
      kepTailTest (kepLogStep f 1) (2 * eps) (Real.log a) (k - j) (2 * eps)
        (fun v => φ (((k : ℝ) + u - v) / a)) = H u := by
    rw [kepTailTest_eq_krRow ν hf hf0 hfD hν (Or.inl rfl) (Real.log a) (k - j)
      ⟨by linarith, le_rfl⟩
      (φ := fun v => φ (((k : ℝ) + u - v) / a)) (hφ.comp ((measurable_const.sub measurable_id).div_const a)) (fun v => hφb _),
      Real.exp_log ha0, one_mul]
  have hm : Measurable H := by
    have hp : Measurable (fun p : ℝ × (ℕ → ℝ) =>
        krAlive (Icc 0 (2 * eps)) 1 a (k - j) (2 * eps) p.2 *
          φ (((k : ℝ) + p.1 - kWalk (2 * eps) 1 a p.2 (k - j)) / a)) := by
      exact ((measurable_krAlive_right measurableSet_Icc 1 a (k - j) (2 * eps)).comp
        measurable_snd).mul (hφ.comp (((measurable_const.add measurable_fst).sub
          ((measurable_kWalk_prod 1 a (k - j)).comp
            (measurable_const.prodMk measurable_snd))).div_const a))
    have he' : H = fun u => ∫ g,
        krAlive (Icc 0 (2 * eps)) 1 a (k - j) (2 * eps) g *
          φ (((k : ℝ) + u - kWalk (2 * eps) 1 a g (k - j)) / a) ∂iidLaw ν := by
      funext u
      exact krRow_eq_integral measurableSet_Icc ν 1 a (k - j)
        (φ := fun v => φ (((k : ℝ) + u - v) / a)) (hφ.comp ((measurable_const.sub measurable_id).div_const a)) (fun v => hφb _) (2 * eps)
    rw [he']
    exact hp.stronglyMeasurable.integral_prod_right.measurable
  have hb : ∀ u, |H u| ≤ B := fun u => abs_krRow_le measurableSet_Icc ν 1 a (k - j)
    (φ := fun v => φ (((k : ℝ) + u - v) / a)) (hφ.comp ((measurable_const.sub measurable_id).div_const a)) (fun v => hφb _) (2 * eps)
  rw [kepCertificateExterior_eq_rows heps ν k i j hφ hB hφb ha]
  unfold kepTailPairTest
  simp_rw [he]
  rw [kepTailTest_eq_krRow ν hf hf0 hfD hν (Or.inr rfl) (Real.log a) i
    ⟨le_rfl, by linarith⟩ hm hb, Real.exp_log ha0, neg_one_mul]

end

end PGM
