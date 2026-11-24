import PLAStochastic.Index.KEP.ReferenceScale.ActualCertificateTransfer

/-!
# The true surviving prefix as long certificate graphs and a rare remainder

The certificate is unique almost surely under the actual iid reference law.
The split keeps the original event and the original physical prefix sum. Long
selected bridges with the fixed slope cutoff use the proved second graph
transfer; every omitted pair and complementary slope remains in the explicit
remainder. No rare-event estimate is assumed or asserted here.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory Set

def kepCertificateCoreCutoff (N i j : ℕ) (a : ℝ) : ℝ :=
  if N ≤ j - i then kepCertificateCutoff a else 0

def kepCertificateRareCutoff (N i j : ℕ) (a : ℝ) : ℝ :=
  1 - kepCertificateCoreCutoff N i j a

def kepSurvivingRareTerm (eps : ℝ) (ν : ProbabilityMeasure ℝ) (N k : ℕ)
    (φ : ℝ → ℝ) : ℝ :=
  ∑ ij ∈ certPairs eps k,
    kepCertificateTerm eps ν k ij.1 ij.2 (kepCertificateRareCutoff N ij.1 ij.2) φ

theorem kepCertificateCoreCutoff_bounds (N i j : ℕ) (a : ℝ) :
    0 ≤ kepCertificateCoreCutoff N i j a ∧ kepCertificateCoreCutoff N i j a ≤ 1 := by
  unfold kepCertificateCoreCutoff
  split
  · exact kepCertificateCutoff_bounds a
  · norm_num

theorem measurable_kepCertificateCoreCutoff (N i j : ℕ) :
    Measurable (kepCertificateCoreCutoff N i j) := by
  unfold kepCertificateCoreCutoff
  split
  · exact contDiff_kepCertificateCutoff.continuous.measurable
  · exact measurable_const

theorem kepCertificateTerm_core_add_rare (eps : ℝ) (ν : ProbabilityMeasure ℝ)
    (N k i j : ℕ) {φ : ℝ → ℝ} (hφ : Measurable φ) {B : ℝ}
    (_hB : 0 ≤ B) (hφb : ∀ y, |φ y| ≤ B) :
    (∫ g in {g | certOK eps (gapKeys g) k i j}, φ (gapKeys g k) ∂iidLaw ν) =
      kepCertificateTerm eps ν k i j (kepCertificateCoreCutoff N i j) φ +
      kepCertificateTerm eps ν k i j (kepCertificateRareCutoff N i j) φ := by
  have ha : Measurable (fun g : ℕ → ℝ => certSlope eps (gapKeys g) i j) :=
    measurable_const.div ((rawAsm_measurable_gapKeys j).sub (rawAsm_measurable_gapKeys i))
  have hc := (measurable_kepCertificateCoreCutoff N i j).comp ha
  have htest := hφ.comp (rawAsm_measurable_gapKeys k)
  have hbcore (g : ℕ → ℝ) : |kepCertificateCoreCutoff N i j
      (certSlope eps (gapKeys g) i j) * φ (gapKeys g k)| ≤ B := by
    rw [abs_mul, abs_of_nonneg (kepCertificateCoreCutoff_bounds N i j _).1]
    exact (mul_le_mul (kepCertificateCoreCutoff_bounds N i j _).2 (hφb _)
      (abs_nonneg _) zero_le_one).trans_eq (one_mul B)
  have hbrare (g : ℕ → ℝ) : |kepCertificateRareCutoff N i j
      (certSlope eps (gapKeys g) i j) * φ (gapKeys g k)| ≤ B := by
    have hh := kepCertificateCoreCutoff_bounds N i j (certSlope eps (gapKeys g) i j)
    rw [abs_mul, kepCertificateRareCutoff, abs_of_nonneg (by linarith :
      0 ≤ 1 - kepCertificateCoreCutoff N i j (certSlope eps (gapKeys g) i j))]
    exact (mul_le_mul (by linarith :
      1 - kepCertificateCoreCutoff N i j (certSlope eps (gapKeys g) i j) ≤ 1)
      (hφb _) (abs_nonneg _) zero_le_one).trans_eq (one_mul B)
  have hic : IntegrableOn (fun g => kepCertificateCoreCutoff N i j
      (certSlope eps (gapKeys g) i j) * φ (gapKeys g k))
      {g | certOK eps (gapKeys g) k i j} (iidLaw ν) := by
    refine ((integrable_const B).mono' (hc.mul htest).aestronglyMeasurable
      (ae_of_all _ fun g => ?_)).integrableOn
    simpa only [Real.norm_eq_abs, Pi.mul_apply, Function.comp_apply] using hbcore g
  have hir : IntegrableOn (fun g => kepCertificateRareCutoff N i j
      (certSlope eps (gapKeys g) i j) * φ (gapKeys g k))
      {g | certOK eps (gapKeys g) k i j} (iidLaw ν) := by
    refine ((integrable_const B).mono' ((measurable_const.sub hc).mul htest).aestronglyMeasurable
      (ae_of_all _ fun g => ?_)).integrableOn
    simpa only [Real.norm_eq_abs, Pi.mul_apply, Pi.sub_apply, Function.comp_apply,
      kepCertificateRareCutoff] using hbrare g
  unfold kepCertificateTerm
  rw [← integral_add hic hir]
  apply integral_congr_ae
  exact ae_of_all _ fun g => by dsimp [kepCertificateRareCutoff]; ring

theorem kepSurvivingPrefix_core_add_rare (eps : ℝ) (ν : ProbabilityMeasure ℝ)
    (hνac : (ν : Measure ℝ) ≪ volume) (hνpos : (ν : Measure ℝ) (Iic 0) = 0)
    (N k : ℕ) (hk : 2 * eps < k) {φ : ℝ → ℝ} (hφ : Measurable φ) {B : ℝ}
    (hB : 0 ≤ B) (hφb : ∀ y, |φ y| ≤ B) :
    (∫ g in {g | (k : ℕ∞) < gapSegLen eps g}, φ (gapKeys g k) ∂iidLaw ν) =
      (∑ ij ∈ certPairs eps k,
        kepCertificateTerm eps ν k ij.1 ij.2 (kepCertificateCoreCutoff N ij.1 ij.2) φ) +
      kepSurvivingRareTerm eps ν N k φ := by
  have htest := hφ.comp (rawAsm_measurable_gapKeys k)
  have hi : Integrable (fun g => φ (gapKeys g k)) (wordLaw ν ν ∅) := by
    refine (integrable_const B).mono' htest.aestronglyMeasurable (ae_of_all _ fun g => ?_)
    simpa only [Real.norm_eq_abs] using hφb (gapKeys g k)
  have hh := cert_integral_indicator_eq_sum hνac hνac hνpos hνpos ∅ hk hi
  have hw : wordLaw ν ν ∅ = iidLaw ν := by simp [wordLaw, iidLaw]
  rw [hw, integral_indicator (measurableSet_lt_gapSegLen eps k)] at hh
  simp_rw [integral_indicator (measurableSet_certOK eps k _ _)] at hh
  rw [hh]
  simp_rw [kepCertificateTerm_core_add_rare eps ν N k _ _ hφ hB hφb]
  rw [Finset.sum_add_distrib]
  rfl

def kepSurvivingSecondCore (f f' f'' : ℝ → ℝ) (eps : ℝ) (N k : ℕ) (φ : ℝ → ℝ) : ℝ :=
  ∑ ij ∈ certPairs eps k,
    if N ≤ ij.2 - ij.1 then
      kepCertificateSecondGraph f f' f'' eps ((ij.2 - ij.1 : ℕ) - 2 * eps)
        ij.1 (k - ij.2) (ij.2 - ij.1 - 1) φ
    else 0

/-- The original actual surviving-prefix test has a complete finite graph
representation plus its explicit complementary event. -/
theorem kepReference_surviving_second_core_add_rare {eps : ℝ}
    (heps : kepReferenceClassicalThreshold ≤ eps) {layer : ℕ} (hlayer : 1 ≤ layer)
    (N k : ℕ) (hk : 2 * eps < k)
    {φ φ' φ'' : ℝ → ℝ} (hφ : Continuous φ) (hφ' : Continuous φ')
    (hφ'' : Continuous φ'') (hdφ : ∀ y, HasDerivAt φ (φ' y) y)
    (hddφ : ∀ y, HasDerivAt φ' (φ'' y) y)
    {B : ℝ} (hB : 0 ≤ B) (hφ''b : ∀ y, |φ'' y| ≤ B) :
    let f := (kepReferenceDensity heps hlayer).density
    let f' := gammaScaledFirst (kepReferenceWeights eps layer) (kepReferenceSpan eps layer)
    let f'' := gammaScaledSecond (kepReferenceWeights eps layer) (kepReferenceSpan eps layer)
    (∫ g in {g | (k : ℕ∞) < gapSegLen eps g}, φ'' (gapKeys g k)
      ∂iidLaw (kepReferenceLaw eps layer)) =
      kepSurvivingSecondCore f f' f'' eps N k φ +
        kepSurvivingRareTerm eps (kepReferenceLaw eps layer) N k φ'' := by
  have hac : (kepReferenceLaw eps layer : Measure ℝ) ≪ volume := by
    rw [← kepReferenceDensity_toMeasure heps hlayer]
    exact withDensity_absolutelyContinuous _ _
  rw [kepSurvivingPrefix_core_add_rare eps (kepReferenceLaw eps layer) hac
    (kepReferenceLaw_Iic_zero heps hlayer) N k hk hφ''.measurable hB hφ''b]
  congr 1
  apply Finset.sum_congr rfl
  intro ij hijmem
  obtain ⟨hij, hjk, hd⟩ := mem_certPairs.mp hijmem
  by_cases hN : N ≤ ij.2 - ij.1
  · have hL : ij.1 + (ij.2 - ij.1) = ij.2 := by omega
    have hlen : ij.2 - ij.1 = (ij.2 - ij.1 - 1) + 1 := by omega
    have hdr : 0 < (ij.2 - ij.1 : ℕ) - 2 * eps := by
      rw [Nat.cast_sub hij.le]
      linarith
    have he : kepCertificateCoreCutoff N ij.1 ij.2 = kepCertificateCutoff := by
      funext a
      simp only [kepCertificateCoreCutoff, hN, if_true]
    rw [he]
    rw [if_pos hN]
    exact kepReference_certificate_second_transfer heps hlayer hij hL hjk hdr
      (ij.2 - ij.1 - 1) hlen hφ hφ' hφ'' hdφ hddφ hB hφ''b
  · simp [kepCertificateCoreCutoff, hN, kepCertificateTerm]

end

end PGM
