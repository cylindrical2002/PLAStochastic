import PLAStochastic.Index.KEP.ReferenceScale.CertificateCoarea

/-!
# The original certificate as an independent middle and its exterior reward

The slope cutoff is evaluated on the original selected pair. Permutation and
Fubini use the original iid law and the actual reversed-prefix/forward-suffix
reward. No independence is asserted after conditioning on a certificate.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory Set

def kepCertificateTerm (eps : ℝ) (ν : ProbabilityMeasure ℝ) (k i j : ℕ)
    (χ φ : ℝ → ℝ) : ℝ :=
  ∫ g in {g | certOK eps (gapKeys g) k i j},
    χ (certSlope eps (gapKeys g) i j) * φ (gapKeys g k) ∂iidLaw ν

def kepCertificateExterior (eps : ℝ) (ν : ProbabilityMeasure ℝ) (k i j : ℕ)
    (φ : ℝ → ℝ) (a : ℝ) : ℝ := (surv_pref eps k i j φ ν ν 0 a).re

theorem kep_certSlope_permuted {eps : ℝ} {i j L : ℕ}
    (hL : i + L = j) (g : ℕ → ℝ) :
    surv_slope ((L : ℝ) - 2 * eps) L (fun l => g (surv_pi i j L l)) =
      certSlope eps (gapKeys g) i j := by
  have hkeys : gapKeys (fun l => g (surv_pi i j L l)) L =
      gapKeys g j - gapKeys g i := by
    have hh : gapKeys (fun l => g (surv_pi i j L l)) L =
        gapKeys (fun m => g (i + m)) L := by
      unfold gapKeys
      apply Finset.sum_congr rfl
      intro l hl
      dsimp only
      rw [surv_pi_of_lt (Finset.mem_range.mp hl)]
    rw [hh, gapKeys_shift, hL]
  have hLr : (L : ℝ) = (j : ℝ) - i := by
    have hh := congrArg (Nat.cast (R := ℝ)) hL
    push_cast at hh
    linarith
  simp only [surv_slope, certSlope, hkeys, hLr]

theorem kep_prod_indicator_one_complex {ι : Type*} (S : Finset ι) (J : Set ℝ)
    (y : ι → ℝ) :
    (∏ l ∈ S, J.indicator (fun _ => (1 : ℂ)) (y l)) =
      ((∏ l ∈ S, J.indicator (fun _ => (1 : ℝ)) (y l) : ℝ) : ℂ) := by
  rw [Complex.ofReal_prod]
  apply Finset.prod_congr rfl
  intro l hl
  by_cases h : y l ∈ J <;> simp [h]

theorem kepCertificateExterior_complex (eps : ℝ) (ν : ProbabilityMeasure ℝ)
    (k i j : ℕ) (φ : ℝ → ℝ) (a : ℝ) :
    (kepCertificateExterior eps ν k i j φ a : ℂ) = surv_pref eps k i j φ ν ν 0 a := by
  unfold kepCertificateExterior surv_pref
  rw [kep_surv_wint_zero]
  have hr : ∀ g, (surv_preInt eps k i j φ a g).im = 0 := by
    intro g
    unfold surv_preInt
    rw [kep_prod_indicator_one_complex, kep_prod_indicator_one_complex]
    by_cases ha : a ∈ Icc (1 / 2 : ℝ) 2
    · rw [indicator_of_mem ha]
      simp only [mul_one, ← Complex.ofReal_mul, Complex.ofReal_im]
    · rw [indicator_of_notMem ha]
      simp
  have he : (fun g => surv_preInt eps k i j φ a g) =
      fun g => ((surv_preInt eps k i j φ a g).re : ℂ) := by
    funext g
    apply Complex.ext
    · rfl
    · simpa only [Complex.ofReal_im] using hr g
  rw [he, integral_complex_ofReal]
  simp only [Complex.ofReal_re]

theorem measurable_kepCertificateExterior (eps : ℝ) (ν : ProbabilityMeasure ℝ)
    (k i j : ℕ) {φ : ℝ → ℝ} (hφ : Measurable φ) :
    Measurable (kepCertificateExterior eps ν k i j φ) :=
  Complex.measurable_re.comp (surv_measurable_pref eps k i j hφ ν ν 0)

theorem kepCertificateExterior_eq_zero (eps : ℝ) (ν : ProbabilityMeasure ℝ)
    (k i j : ℕ) (φ : ℝ → ℝ) {a : ℝ} (ha : a ∉ Icc (1 / 2 : ℝ) 2) :
    kepCertificateExterior eps ν k i j φ a = 0 := by
  simp only [kepCertificateExterior, surv_pref_eq_zero eps k i j φ ν ν 0 ha, Complex.zero_re]

theorem abs_kepCertificateExterior_le {eps : ℝ} (heps : 0 ≤ eps)
    (ν : ProbabilityMeasure ℝ) (k i j : ℕ) {φ : ℝ → ℝ} {B : ℝ}
    (hB : 0 ≤ B) (hφ : ∀ x, |φ x| ≤ B) (a : ℝ) :
    |kepCertificateExterior eps ν k i j φ a| ≤ B := by
  unfold kepCertificateExterior surv_pref
  rw [kep_surv_wint_zero]
  refine (Complex.abs_re_le_norm _).trans ?_
  have h := norm_integral_le_of_norm_le_const (μ := iidLaw ν)
    (C := B) (f := surv_preInt eps k i j φ a)
    (ae_of_all _ fun g => surv_norm_preInt_le eps k i j heps hB (fun x _ => hφ x) a g)
  simpa only [probReal_univ, mul_one] using h

/-- Exact disintegration of one original pair, including the original
cutoff and the full exterior reward. -/
theorem kepCertificateTerm_eq_middle {eps : ℝ} (heps : 0 ≤ eps)
    (ν : ProbabilityMeasure ℝ) (hνpos : (ν : Measure ℝ) (Iic 0) = 0)
    {k i j L : ℕ} (hij : i < j) (hL : i + L = j) (hjk : j ≤ k)
    {χ φ : ℝ → ℝ} (hχ : Measurable χ) (hφ : Measurable φ)
    (hχb : ∀ a, |χ a| ≤ 1) (hχ0 : ∀ a, a ∉ Icc (1 / 2 : ℝ) 2 → χ a = 0)
    {B : ℝ} (hB : 0 ≤ B) (hφb : ∀ x, |φ x| ≤ B) (n : ℕ) (hn : L = n + 1) :
    kepCertificateTerm eps ν k i j χ φ =
      ∫ g, kepCertificateMiddle eps ((L : ℝ) - 2 * eps) n
        (fun a => χ a * kepCertificateExterior eps ν k i j φ a) g ∂iidLaw ν := by
  let d := (L : ℝ) - 2 * eps
  let F : (ℕ → ℝ) → ℂ := fun g =>
    (χ (surv_slope d L g) : ℂ) * surv_permInt eps k i j L d φ g
  have hFm : Measurable F :=
    (Complex.measurable_ofReal.comp (hχ.comp (surv_measurable_slope d L))).mul
      (surv_measurable_permInt eps k i j L d hφ)
  have hFb : ∀ g, ‖F g‖ ≤ B := by
    intro g
    dsimp only [F]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact (mul_le_mul (hχb _) (surv_norm_permInt_le eps k i j L d heps hB
      (fun x _ => hφb x) g) (norm_nonneg _) zero_le_one).trans_eq (one_mul B)
  have hfirst : (kepCertificateTerm eps ν k i j χ φ : ℂ) = surv_wint ν ν 0 k F := by
    rw [kep_surv_wint_zero]
    unfold kepCertificateTerm
    rw [← integral_complex_ofReal, ← integral_indicator (measurableSet_certOK eps k i j)]
    have hperm := surv_wint_perm ν ν 0 k (surv_pi_injective hij hL)
      (surv_pi_lt hij hL hjk) hFm
    rw [kep_surv_wint_zero, kep_surv_wint_zero] at hperm
    rw [← hperm]
    apply integral_congr_ae
    have hp := cert_ae_pos_wordLaw (ν := ν) (σ := ν) hνpos hνpos ∅
    rw [wordLaw_empty] at hp
    filter_upwards [hp] with g hg
    dsimp only [F, d]
    rw [kep_certSlope_permuted hL,
      ← surv_certInt_eq_permInt hij hL hjk rfl φ hg]
    unfold surv_certInt
    by_cases hok : certOK eps (gapKeys g) k i j
    · rw [indicator_of_mem hok, indicator_of_mem hok]
      by_cases ha : certSlope eps (gapKeys g) i j ∈ Icc (1 / 2 : ℝ) 2
      · rw [indicator_of_mem ha]
        simp only [one_mul, Complex.ofReal_mul]
      · rw [indicator_of_notMem ha, hχ0 _ ha]
        simp
    · rw [indicator_of_notMem hok, indicator_of_notMem hok]
      simp
  have hcat := surv_wint_cat ν ν 0 L (i + (k - j)) hFm hFb
  have hlen : L + (i + (k - j)) = k := by omega
  rw [hlen] at hcat
  have hinner (g : ℕ → ℝ) : surv_wint ν ν 0 (i + (k - j))
      (fun h => F (surv_cat L g h)) =
      (kepCertificateMiddle eps d n
        (fun a => χ a * kepCertificateExterior eps ν k i j φ a) g : ℂ) := by
    have hslope (h : ℕ → ℝ) : surv_slope d L (surv_cat L g h) = surv_slope d L g := by
      unfold surv_slope gapKeys
      congr 1
      exact Finset.sum_congr rfl fun l hl => surv_cat_apply_lt (Finset.mem_range.mp hl) g h
    have he : (fun h => F (surv_cat L g h)) = fun h =>
        ((χ (surv_slope d L g) : ℂ) *
          ∏ l ∈ Finset.range (L + 1), (surv_J eps).indicator (fun _ => (1 : ℂ))
            (kWalk 0 1 (surv_slope d L g) g l)) *
          surv_preInt eps k i j φ (surv_slope d L g) h := by
      funext h
      dsimp only [F]
      rw [hslope, surv_permInt_cat]
      ring
    rw [he, surv_wint_const_mul]
    change _ * surv_pref eps k i j φ ν ν 0 (surv_slope d L g) = _
    rw [← kepCertificateExterior_complex]
    unfold kepCertificateMiddle surv_slope surv_J
    rw [hn]
    simp only [Nat.add_assoc, Complex.ofReal_mul]
    rw [kep_prod_indicator_one_complex]
    ring
  rw [hcat] at hfirst
  simp_rw [hinner] at hfirst
  rw [kep_surv_wint_zero, integral_complex_ofReal] at hfirst
  exact Complex.ofReal_injective hfirst

end

end PGM
