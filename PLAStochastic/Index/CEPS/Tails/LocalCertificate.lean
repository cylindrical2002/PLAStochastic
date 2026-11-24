import PLAStochastic.Index.CEPS.Actual.Representation

/-!
# Localizing the exact certificate integral in drift

WP8's single-certificate identity is strengthened by an arbitrary bounded
measurable drift weight. Taking a set indicator gives the exact certificate
integral on a drift subdomain, the measure-theoretic prerequisite for S-7.
-/

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter

/-- The drift associated with the certificate slope: `μ = 1/a - 1`. -/
def cepsCertDrift (eps : ℝ) (p : ℕ → ℝ) (i j : ℕ) : ℝ :=
  (p j - p i) / ((j : ℝ) - i - 2 * eps) - 1

theorem measurable_cepsCertDrift (eps : ℝ) (i j : ℕ) :
    Measurable (fun g : ℕ → ℝ => cepsCertDrift eps (gapKeys g) i j) := by
  unfold cepsCertDrift
  exact (((rawAsm_measurable_gapKeys j).sub (rawAsm_measurable_gapKeys i)).div_const _).sub_const _

/-- The middle-block permutation preserves the certificate drift. -/
theorem cepsMidDrift_perm {eps : ℝ} {i L : ℕ} (g : ℕ → ℝ) :
    cepsMidDrift eps L (fun n => g (surv_pi i (i + L) L n)) =
      cepsCertDrift eps (gapKeys g) i (i + L) := by
  have hmid : gapKeys (fun n => g (surv_pi i (i + L) L n)) L =
      gapKeys g (i + L) - gapKeys g i := by
    calc _ = gapKeys (fun n => g (i + n)) L :=
          Finset.sum_congr rfl fun n hn => congrArg g (surv_pi_of_lt (Finset.mem_range.mp hn))
      _ = _ := gapKeys_shift g i L
  simp only [cepsMidDrift, cepsCertDrift, hmid, Nat.cast_add]
  congr 2
  ring

/-- Adding a bounded drift weight commutes with the prefix–suffix Fubini step. -/
theorem integral_cepsPermInt_drift_weight (ν : ProbabilityMeasure ℝ) {eps : ℝ}
    (heps : 0 < eps) {i L r : ℕ} (hL : 2 * eps < L) {t : ℂ} (ht : 0 ≤ t.re)
    {χ : ℝ → ℂ} (hχ : Measurable χ) {M : ℝ} (hbound : ∀ μ, ‖χ μ‖ ≤ M) :
    ∫ h, cepsPermInt t eps i L r h * χ (cepsMidDrift eps L h) ∂(iidLaw ν) =
      ∫ h, (cepsMidAlive eps L h : ℂ) *
        (cepsOuterMean ν t eps i r (i + L + r) (cepsMidDrift eps L h) *
          χ (cepsMidDrift eps L h)) ∂(iidLaw ν) := by
  have hcat := surv_integral_cat ν ν ∅ L
    ((measurable_cepsPermInt t eps i L r).mul (hχ.comp (measurable_cepsMidDrift eps L)))
    (fun h => calc
      ‖cepsPermInt t eps i L r h * χ (cepsMidDrift eps L h)‖
        = ‖cepsPermInt t eps i L r h‖ * ‖χ (cepsMidDrift eps L h)‖ := norm_mul _ _
      _ ≤ 1 * M := mul_le_mul (norm_cepsPermInt_le_one ht heps hL h)
        (hbound _) (norm_nonneg _) zero_le_one
      _ = M := one_mul _)
  simp only [wordLaw_self, Pi.mul_apply, Function.comp_apply] at hcat
  rw [hcat]
  refine integral_congr_ae (Eventually.of_forall fun g => ?_)
  have hdrift : ∀ h' : ℕ → ℝ, cepsMidDrift eps L (surv_cat L g h') = cepsMidDrift eps L g := by
    intro h'
    unfold cepsMidDrift gapKeys
    rw [Finset.sum_congr rfl fun n hn => surv_cat_apply_lt (Finset.mem_range.mp hn) g h']
  have halive : ∀ h' : ℕ → ℝ, cepsMidAlive eps L (surv_cat L g h') = cepsMidAlive eps L g := by
    intro h'
    unfold cepsMidAlive
    rw [hdrift]
    exact krAlive_congr fun n hn => surv_cat_apply_lt hn g h'
  have hshift : ∀ h' : ℕ → ℝ, (fun n => surv_cat L g h' (L + n)) = h' :=
    fun h' => funext fun n => surv_cat_apply_add L n g h'
  simp only [cepsPermInt, hdrift, halive, hshift]
  rw [integral_mul_const, integral_const_mul]
  unfold cepsOuterMean
  ring

/-- The exact single-certificate integral with an arbitrary bounded measurable drift weight. -/
theorem CepsGapDensity.integral_cert_drift_weight {ν : ProbabilityMeasure ℝ} {f : ℝ → ℝ}
    {D : ℝ} (hf : CepsGapDensity ν f D) {eps : ℝ} (heps : 0 < eps)
    {i L r : ℕ} (hL : 2 * eps < L) {t : ℂ} (ht : 0 ≤ t.re)
    {χ : ℝ → ℂ} (hχ : Measurable χ) {M : ℝ} (hbound : ∀ μ, ‖χ μ‖ ≤ M) :
    ∫ g, {g' : ℕ → ℝ | certOK eps (gapKeys g') (i + L + r) i (i + L)}.indicator
        (fun _ => (1 : ℂ)) g * Complex.exp (-t * gapKeys g (i + L + r)) *
        χ (cepsCertDrift eps (gapKeys g) i (i + L)) ∂(iidLaw ν) =
      ∫ μ in Ioi (-1 : ℝ), cepsTripleTerm ν f eps t i L r μ * χ μ := by
  have hL0 : 0 < L := by exact_mod_cast (show (0 : ℝ) < L by linarith)
  have hk : 2 * eps ≤ ((i + L + r : ℕ) : ℝ) := by
    push_cast
    linarith [(Nat.cast_nonneg i : (0 : ℝ) ≤ i), (Nat.cast_nonneg r : (0 : ℝ) ≤ r)]
  have hp := surv_pi_injective (i := i) (j := i + L) (L := L) (by omega) rfl
  have hperm := integral_wordLaw_comp ν ν ∅ hp
    (F := fun h => cepsPermInt t eps i L r h * χ (cepsMidDrift eps L h))
    (((measurable_cepsPermInt t eps i L r).mul
      (hχ.comp (measurable_cepsMidDrift eps L))).aestronglyMeasurable)
  simp only [wordLaw_self] at hperm
  rw [integral_congr_ae (hf.ae_iidLaw_pos.mono fun g hg => by
    rw [ceps_cert_pathwise heps hL t hg, ← cepsMidDrift_perm]), hperm,
    integral_cepsPermInt_drift_weight ν heps hL ht hχ hbound]
  have hmid := hf.integral_midAlive_mul heps hL
      ((measurable_cepsOuterMean ν t eps i r (i + L + r)).mul hχ)
      (fun μ => calc
        ‖cepsOuterMean ν t eps i r (i + L + r) μ * χ μ‖
          = ‖cepsOuterMean ν t eps i r (i + L + r) μ‖ * ‖χ μ‖ := norm_mul _ _
        _ ≤ 1 * M := mul_le_mul (norm_cepsOuterMean_le_one ν ht heps hk μ)
          (hbound μ) (norm_nonneg _) zero_le_one
        _ = M := one_mul _)
  simp only [Pi.mul_apply] at hmid
  rw [hmid, ← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioi fun μ _ => ?_
  rw [cepsTripleTerm, if_neg (by omega : L ≠ 0), cepsBridgeMul]
  ring

/-- The certificate identity on a measurable drift subdomain. -/
theorem CepsGapDensity.integral_cert_drift_set {ν : ProbabilityMeasure ℝ} {f : ℝ → ℝ}
    {D : ℝ} (hf : CepsGapDensity ν f D) {eps : ℝ} (heps : 0 < eps)
    {i L r : ℕ} (hL : 2 * eps < L) {t : ℂ} (ht : 0 ≤ t.re)
    {E : Set ℝ} (hE : MeasurableSet E) :
    ∫ g, {g' : ℕ → ℝ | certOK eps (gapKeys g') (i + L + r) i (i + L)}.indicator
        (fun _ => (1 : ℂ)) g * Complex.exp (-t * gapKeys g (i + L + r)) *
        E.indicator (fun _ => (1 : ℂ)) (cepsCertDrift eps (gapKeys g) i (i + L)) ∂(iidLaw ν) =
      ∫ μ in Ioi (-1 : ℝ) ∩ E, cepsTripleTerm ν f eps t i L r μ := by
  rw [hf.integral_cert_drift_weight (M := 1) heps hL ht (measurable_const.indicator hE)
    (fun μ => by by_cases h : μ ∈ E <;> simp [h])]
  have hi : (fun μ => cepsTripleTerm ν f eps t i L r μ * E.indicator (fun _ => (1 : ℂ)) μ) =
      E.indicator (cepsTripleTerm ν f eps t i L r) := by
    funext μ
    by_cases h : μ ∈ E <;> simp [h]
  rw [hi, integral_indicator hE, Measure.restrict_restrict hE, inter_comm]

end

end PGM
