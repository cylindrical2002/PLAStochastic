import PLAStochastic.Index.GEP.Shadow.ErrorContraction

/-!
# WP3: nondegeneracy of the actual exponential-mark shadow

The shadow has mean one and a uniform upper second moment. Its lower variance
bound follows from the active layer variance and the proved same-tree error
bound. No regularity of the original gap law is assumed.
-/

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory Finset

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {g : ℕ → Ω → ℝ} {μ₀ σ₀ κ₀ eps : ℝ}

theorem one_le_shCount (hg : GapLaw P g μ₀ σ₀ κ₀)
    (heps : epsZero (bIn μ₀ σ₀) (βIn σ₀ (lkap P (inputPairs g))) ≤ eps) (ℓ : ℕ) :
    1 ≤ shCount P eps g ℓ := by
  have hL := (layerOK_all (layerOK_input hg) (bAbs_le_bIn μ₀ σ₀) (βAbs_le_βIn _ _)
    (vIn_pos hg.mu_pos hg.sigma_pos) (vIn_le μ₀ σ₀) KcAbs_le_KcIn heps ℓ).1
  rw [shCount_eq]
  change 1 ≤ ∫ ω, ((epLayerSeq eps g ℓ 0 ω).2 : ℝ) ∂P
  calc 1 = ∫ _ : Ω, (1 : ℝ) ∂P := by simp
    _ ≤ _ := integral_mono_ae (integrable_const _) (hL.cnt2.integrable one_le_two)
      ((ae_one_le_epLayerSeq_count hg heps ℓ 0).mono fun ω hω => by
        change (1 : ℝ) ≤ ((epLayerSeq eps g ℓ 0 ω).2 : ℝ)
        exact_mod_cast hω)

theorem integral_shPair_fst_sub_one_sq (hg : GapLaw P g μ₀ σ₀ κ₀)
    (heps : epsZero (bIn μ₀ σ₀) (βIn σ₀ (lkap P (inputPairs g))) ≤ eps) (ℓ : ℕ) :
    ∫ p, ((shPair P eps g ℓ 0 p).1 - 1) ^ 2 ∂shP P =
      lsig P (epLayerSeq eps g ℓ) ^ 2 / lmean P (epLayerSeq eps g ℓ) ^ 2 := by
  have hm : lmean P (epLayerSeq eps g ℓ) ≠ 0 := by
    rw [← shMean_eq]
    exact (shMean_pos hg heps ℓ).ne'
  simp only [shPair, shTri_fst_eq_actual, shMean_eq]
  have heq : (fun p : Ω × (ℕ → ℝ) =>
      ((epLayerSeq eps g ℓ 0 p.1).1 / lmean P (epLayerSeq eps g ℓ) - 1) ^ 2) =
      fun p => ((epLayerSeq eps g ℓ 0 p.1).1 - lmean P (epLayerSeq eps g ℓ)) ^ 2 /
        lmean P (epLayerSeq eps g ℓ) ^ 2 := by
    funext p
    field_simp
  rw [heq, integral_div, shP,
    integral_fun_fst (fun ω => ((epLayerSeq eps g ℓ 0 ω).1 - lmean P (epLayerSeq eps g ℓ)) ^ 2), lsig_sq]
  simp only [probReal_univ, smul_eq_mul, one_mul, lvar]

theorem integral_shPair_snd_sub_one_sq (hg : GapLaw P g μ₀ σ₀ κ₀)
    (heps : epsZero (bIn μ₀ σ₀) (βIn σ₀ (lkap P (inputPairs g))) ≤ eps) (ℓ : ℕ) :
    ∫ p, ((shPair P eps g ℓ 0 p).2 - 1) ^ 2 ∂shP P =
      (∫ p, (shPair P eps g ℓ 0 p).2 ^ 2 ∂shP P) - 1 := by
  have hL := (layerOK_all (layerOK_input hg) (bAbs_le_bIn μ₀ σ₀) (βAbs_le_βIn _ _)
    (vIn_pos hg.mu_pos hg.sigma_pos) (vIn_le μ₀ σ₀) KcAbs_le_KcIn heps ℓ).1
  obtain ⟨-, hY, -, hYm⟩ := shPair_moments_of_layerOK hg.iid.measurable hL
  have hY1 := hY.integrable one_le_two
  have heq : (fun p => ((shPair P eps g ℓ 0 p).2 - 1) ^ 2) =
      fun p => (shPair P eps g ℓ 0 p).2 ^ 2 - 2 * (shPair P eps g ℓ 0 p).2 + 1 := by
    funext p; ring
  rw [heq, integral_add
    (f := fun p => (shPair P eps g ℓ 0 p).2 ^ 2 - 2 * (shPair P eps g ℓ 0 p).2)
    (g := fun _ => (1 : ℝ)) (hY.integrable_sq.sub (hY1.const_mul _)) (integrable_const _),
    integral_sub (f := fun p => (shPair P eps g ℓ 0 p).2 ^ 2)
      (g := fun p => 2 * (shPair P eps g ℓ 0 p).2) hY.integrable_sq (hY1.const_mul _),
    integral_const_mul, hYm]
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
  ring

theorem shPair_snd_variance_le (hg : GapLaw P g μ₀ σ₀ κ₀)
    (heps : epsZero (bIn μ₀ σ₀) (βIn σ₀ (lkap P (inputPairs g))) ≤ eps) (ℓ : ℕ) :
    ∫ p, ((shPair P eps g ℓ 0 p).2 - 1) ^ 2 ∂shP P ≤ KcIn := by
  have hL := (layerOK_all (layerOK_input hg) (bAbs_le_bIn μ₀ σ₀) (βAbs_le_βIn _ _)
    (vIn_pos hg.mu_pos hg.sigma_pos) (vIn_le μ₀ σ₀) KcAbs_le_KcIn heps ℓ).1
  rw [integral_shPair_snd_sub_one_sq hg heps ℓ]
  have h := integral_shPair_snd_sq_le hg.iid.measurable hL
  have hm := one_le_shCount hg heps ℓ
  have hinv : 1 / shCount P eps g ℓ ≤ 1 := (div_le_one (shCount_pos hg heps ℓ)).2 hm
  linarith

/-- The active variance bounds the passive variance from below, up to the
same-tree error. The elementary squared triangle inequality suffices. -/
theorem shPair_snd_variance_ge_sub (hg : GapLaw P g μ₀ σ₀ κ₀)
    (heps : epsZero (bIn μ₀ σ₀) (βIn σ₀ (lkap P (inputPairs g))) ≤ eps) (ℓ : ℕ) :
    vIn μ₀ σ₀ / 2 - shDist P eps g ℓ ^ 2 ≤
      ∫ p, ((shPair P eps g ℓ 0 p).2 - 1) ^ 2 ∂shP P := by
  have hL := (layerOK_all (layerOK_input hg) (bAbs_le_bIn μ₀ σ₀) (βAbs_le_βIn _ _)
    (vIn_pos hg.mu_pos hg.sigma_pos) (vIn_le μ₀ σ₀) KcAbs_le_KcIn heps ℓ).1
  obtain ⟨hX, hY, -, -⟩ := shPair_moments_of_layerOK hg.iid.measurable hL
  have hI : Integrable (fun p => ((shPair P eps g ℓ 0 p).1 - 1) ^ 2) (shP P) :=
    (hX.sub (memLp_const (1 : ℝ))).integrable_sq
  have hJ : Integrable (fun p => ((shPair P eps g ℓ 0 p).2 - 1) ^ 2) (shP P) :=
    (hY.sub (memLp_const (1 : ℝ))).integrable_sq
  have hD := integrable_shPair_sub_sq hg heps ℓ
  have hpoint : ∀ p, ((shPair P eps g ℓ 0 p).1 - 1) ^ 2 ≤
      2 * ((shPair P eps g ℓ 0 p).1 - (shPair P eps g ℓ 0 p).2) ^ 2 +
      2 * ((shPair P eps g ℓ 0 p).2 - 1) ^ 2 := by
    intro p
    nlinarith [sq_nonneg ((shPair P eps g ℓ 0 p).1 - 2 * (shPair P eps g ℓ 0 p).2 + 1)]
  have hbound : (∫ p, ((shPair P eps g ℓ 0 p).1 - 1) ^ 2 ∂shP P) ≤
      ∫ p, 2 * ((shPair P eps g ℓ 0 p).1 - (shPair P eps g ℓ 0 p).2) ^ 2 +
        2 * ((shPair P eps g ℓ 0 p).2 - 1) ^ 2 ∂shP P :=
    integral_mono hI ((hD.const_mul 2).add (hJ.const_mul 2)) hpoint
  rw [integral_add (f := fun p => 2 * ((shPair P eps g ℓ 0 p).1 -
    (shPair P eps g ℓ 0 p).2) ^ 2)
    (g := fun p => 2 * ((shPair P eps g ℓ 0 p).2 - 1) ^ 2)
    (hD.const_mul 2) (hJ.const_mul 2), integral_const_mul, integral_const_mul,
    ← shDist_sq, integral_shPair_fst_sub_one_sq hg heps ℓ] at hbound
  have hv : vIn μ₀ σ₀ ≤ lsig P (epLayerSeq eps g ℓ) ^ 2 /
      lmean P (epLayerSeq eps g ℓ) ^ 2 :=
    (le_div_iff₀ (sq_pos_of_pos hL.law.mu_pos)).2 hL.var_ge
  linarith

/-- A uniform positive variance bound once the first-layer error is small. -/
theorem shPair_snd_variance_ge (hg : GapLaw P g μ₀ σ₀ κ₀)
    (heps : epsZero (bIn μ₀ σ₀) (βIn σ₀ (lkap P (inputPairs g))) ≤ eps)
    (hscale : cBr (bIn μ₀ σ₀) (vIn μ₀ σ₀) ≤ eps ^ 2)
    (hsmall : 4 * cBr (bIn μ₀ σ₀) (vIn μ₀ σ₀) * (σ₀ ^ 2 / μ₀ ^ 2 + 1) ≤
      vIn μ₀ σ₀ * eps ^ 2) {ℓ : ℕ} (hℓ : 1 ≤ ℓ) :
    vIn μ₀ σ₀ / 4 ≤ ∫ p, ((shPair P eps g ℓ 0 p).2 - 1) ^ 2 ∂shP P := by
  have hε : 0 < eps := zero_lt_one.trans_le ((one_le_epsZero _ _).trans heps)
  have hcb : 0 < cBr (bIn μ₀ σ₀) (vIn μ₀ σ₀) :=
    lt_of_lt_of_le (by have := bAbs_pos.trans_le (bAbs_le_bIn μ₀ σ₀); positivity)
      (le_max_left _ _)
  have herr := shDist_sq_le_first_scale hg heps hscale hℓ
  have hfrac : (σ₀ ^ 2 / μ₀ ^ 2 + 1) /
      (eps ^ 2 / cBr (bIn μ₀ σ₀) (vIn μ₀ σ₀)) ≤ vIn μ₀ σ₀ / 4 := by
    rw [div_div_eq_mul_div, div_le_iff₀ (sq_pos_of_pos hε)]
    nlinarith
  have hv := shPair_snd_variance_ge_sub hg heps ℓ
  linarith

theorem lawMean_shLawPM (hg : GapLaw P g μ₀ σ₀ κ₀)
    (heps : epsZero (bIn μ₀ σ₀) (βIn σ₀ (lkap P (inputPairs g))) ≤ eps) (ℓ : ℕ) :
    lawMean (shLawPM P hg.iid.measurable eps ℓ) = 1 := by
  have hL := (layerOK_all (layerOK_input hg) (bAbs_le_bIn μ₀ σ₀) (βAbs_le_βIn _ _)
    (vIn_pos hg.mu_pos hg.sigma_pos) (vIn_le μ₀ σ₀) KcAbs_le_KcIn heps ℓ).1
  rw [lawMean, coe_shLawPM, shLaw, integral_map (f := fun x : ℝ => x)
    (measurable_shPair hg.iid.measurable P eps ℓ 0).snd.aemeasurable
    aestronglyMeasurable_id]
  exact (shPair_moments_of_layerOK hg.iid.measurable hL).2.2.2

theorem lawVar_shLawPM (hg : GapLaw P g μ₀ σ₀ κ₀)
    (heps : epsZero (bIn μ₀ σ₀) (βIn σ₀ (lkap P (inputPairs g))) ≤ eps) (ℓ : ℕ) :
    lawVar (shLawPM P hg.iid.measurable eps ℓ) =
      ∫ p, ((shPair P eps g ℓ 0 p).2 - 1) ^ 2 ∂shP P := by
  rw [lawVar, lawMean_shLawPM hg heps, coe_shLawPM, shLaw,
    integral_map (measurable_shPair hg.iid.measurable P eps ℓ 0).snd.aemeasurable
      (show AEStronglyMeasurable (fun x : ℝ => (x - 1) ^ 2) (shLaw P eps g ℓ) by fun_prop)]

theorem shLaw_variance_bracket (hg : GapLaw P g μ₀ σ₀ κ₀)
    (heps : epsZero (bIn μ₀ σ₀) (βIn σ₀ (lkap P (inputPairs g))) ≤ eps)
    (hscale : cBr (bIn μ₀ σ₀) (vIn μ₀ σ₀) ≤ eps ^ 2)
    (hsmall : 4 * cBr (bIn μ₀ σ₀) (vIn μ₀ σ₀) * (σ₀ ^ 2 / μ₀ ^ 2 + 1) ≤
      vIn μ₀ σ₀ * eps ^ 2) {ℓ : ℕ} (hℓ : 1 ≤ ℓ) :
    vIn μ₀ σ₀ / 4 ≤ lawVar (shLawPM P hg.iid.measurable eps ℓ) ∧
      lawVar (shLawPM P hg.iid.measurable eps ℓ) ≤ KcIn := by
  rw [lawVar_shLawPM hg heps]
  exact ⟨shPair_snd_variance_ge hg heps hscale hsmall hℓ, shPair_snd_variance_le hg heps ℓ⟩

end

end PGM
