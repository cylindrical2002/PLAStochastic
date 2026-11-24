import PLAStochastic.Index.GEP.Shadow.MarkMoments
import PLAStochastic.Index.GEP.Shadow.Regeneration
import PLAStochastic.Index.GEP.Shadow.Synchronization

/-!
# WP3: error contraction along the actual shadow orbit

The one-step stopped-square bound is applied to the actual normalized shadow
pairs.  Their joint iid law, moments and normalization recursion are all proved
in the imported modules.  Thus `d_ℓ² ≤ d_0² / m_ℓ`, without a density or an
exponential-moment assumption on the original gap law.
-/

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory Finset

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

theorem shDist_sq (P : Measure Ω) (eps : ℝ) (g : ℕ → Ω → ℝ) (ℓ : ℕ) :
    shDist P eps g ℓ ^ 2 =
      ∫ p, ((shPair P eps g ℓ 0 p).1 - (shPair P eps g ℓ 0 p).2) ^ 2 ∂shP P :=
  Real.sq_sqrt (integral_nonneg fun _ => sq_nonneg _)

theorem shDist_nonneg (P : Measure Ω) (eps : ℝ) (g : ℕ → Ω → ℝ) (ℓ : ℕ) :
    0 ≤ shDist P eps g ℓ := Real.sqrt_nonneg _

variable [IsProbabilityMeasure P] {g : ℕ → Ω → ℝ} {μ₀ σ₀ κ₀ eps : ℝ}

theorem shPair_zero_fst (hg : GapLaw P g μ₀ σ₀ κ₀)
    (eps : ℝ) (p : Ω × (ℕ → ℝ)) : (shPair P eps g 0 0 p).1 = g 0 p.1 / μ₀ := by
  have hμ : shMean P eps g 0 = μ₀ := by rw [shMean_eq]; exact hg.mean
  simp only [shPair, shTri_fst_eq_actual, hμ, epLayerSeq, Function.iterate_zero_apply, inputPairs]

private theorem integral_sub_expCoord_sq (a : ℝ) :
    ∫ ξ, (a - expCoord 0 ξ) ^ 2 ∂expSeqMeasure = (a - 1) ^ 2 + 1 := by
  let Z := centred expCoord 1 0
  have hZ1 : Integrable Z expSeqMeasure :=
    (gapLaw_expCoord.memLp_centred 0).integrable (by norm_num)
  have hZ2 : Integrable (fun ξ => Z ξ ^ 2) expSeqMeasure :=
    ((gapLaw_expCoord.memLp_centred 0).mono_exponent (by norm_num : (2 : ENNReal) ≤ 3)).integrable_sq
  have h0 : ∫ ξ, Z ξ ∂expSeqMeasure = 0 := gapLaw_expCoord.integral_centred 0
  have h2 : ∫ ξ, Z ξ ^ 2 ∂expSeqMeasure = 1 := by
    simpa using gapLaw_expCoord.integral_centred_sq 0
  have heq : (fun ξ => (a - expCoord 0 ξ) ^ 2) =
      fun ξ => Z ξ ^ 2 + (2 * (1 - a)) * Z ξ + (a - 1) ^ 2 := by
    funext ξ; dsimp [Z, centred]; ring
  rw [heq, integral_add
    (f := fun ξ => Z ξ ^ 2 + (2 * (1 - a)) * Z ξ) (g := fun _ => (a - 1) ^ 2)
    (hZ2.add (hZ1.const_mul _)) (integrable_const _),
    integral_add (f := fun ξ => Z ξ ^ 2) (g := fun ξ => (2 * (1 - a)) * Z ξ)
      hZ2 (hZ1.const_mul _), integral_const_mul, h0, h2]
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul, mul_zero, add_zero]
  ring

/-- Exact initial squared error: the relative gap variance plus the independent mark variance. -/
theorem shDist_zero_sq (hg : GapLaw P g μ₀ σ₀ κ₀) (eps : ℝ) :
    shDist P eps g 0 ^ 2 = σ₀ ^ 2 / μ₀ ^ 2 + 1 := by
  obtain ⟨hX, hY, -, -⟩ := shPair_moments_of_layerOK (eps := eps) (ℓ := 0)
    hg.iid.measurable (layerOK_input hg)
  have hI : Integrable (fun p =>
      ((shPair P eps g 0 0 p).1 - (shPair P eps g 0 0 p).2) ^ 2) (shP P) :=
    (hX.sub hY).integrable_sq
  rw [shDist_sq, shP, integral_prod _ hI]
  simp_rw [shPair_zero_fst hg, shPair_zero_snd]
  change (∫ ω, ∫ ξ, (g 0 ω / μ₀ - expCoord 0 ξ) ^ 2 ∂expSeqMeasure ∂P) = _
  simp_rw [integral_sub_expCoord_sq]
  have heq : (fun ω => (g 0 ω / μ₀ - 1) ^ 2) =
      fun ω => (g 0 ω - μ₀) ^ 2 / μ₀ ^ 2 := by
    funext ω; field_simp [hg.mu_pos.ne']
  have hIc : Integrable (fun ω => (g 0 ω / μ₀ - 1) ^ 2) P := by
    rw [heq]
    exact ((hg.memLp_centred 0).mono_exponent (by norm_num : (2 : ENNReal) ≤ 3)).integrable_sq.div_const _
  rw [integral_add hIc (integrable_const _), heq, integral_div, hg.var]
  simp

/-- Integrability of the actual shadow error at every layer. -/
theorem integrable_shPair_sub_sq (hg : GapLaw P g μ₀ σ₀ κ₀)
    (heps : epsZero (bIn μ₀ σ₀) (βIn σ₀ (lkap P (inputPairs g))) ≤ eps) (ℓ : ℕ) :
    Integrable (fun p => ((shPair P eps g ℓ 0 p).1 - (shPair P eps g ℓ 0 p).2) ^ 2)
      (shP P) := by
  have hL := (layerOK_all (layerOK_input hg) (bAbs_le_bIn μ₀ σ₀) (βAbs_le_βIn _ _)
    (vIn_pos hg.mu_pos hg.sigma_pos) (vIn_le μ₀ σ₀) KcAbs_le_KcIn heps ℓ).1
  obtain ⟨hX, hY, -, -⟩ := shPair_moments_of_layerOK hg.iid.measurable hL
  exact (hX.sub hY).integrable_sq

/-- The true shadow orbit contracts its squared coupling error by the active mean length. -/
theorem shDist_sq_step_le (hg : GapLaw P g μ₀ σ₀ κ₀)
    (heps : epsZero (bIn μ₀ σ₀) (βIn σ₀ (lkap P (inputPairs g))) ≤ eps) (ℓ : ℕ) :
    shDist P eps g (ℓ + 1) ^ 2 ≤
      shDist P eps g ℓ ^ 2 / actMean eps (shP P) (shPair P eps g ℓ) := by
  have hL := (layerOK_all (layerOK_input hg) (bAbs_le_bIn μ₀ σ₀) (βAbs_le_βIn _ _)
    (vIn_pos hg.mu_pos hg.sigma_pos) (vIn_le μ₀ σ₀) KcAbs_le_KcIn heps ℓ).1
  obtain ⟨hX, hY, hXm, hYm⟩ := shPair_moments_of_layerOK hg.iid.measurable hL
  have h := (sameTree_sq_integral_le (iidSeqE_shPair hg heps ℓ) eps hX hY
    (hXm.trans hYm.symm) (ae_actLen_shPair_ne_top hg heps ℓ)
    (integrable_actLen_shPair hg heps ℓ) (actMean_shPair_pos hg heps ℓ)).2
  rw [shDist_sq, shDist_sq]
  simpa only [shPair_succ_zero hg heps] using h

/-- Squared error is bounded by its initial value divided by the mean original count. -/
theorem shDist_sq_le_initial_div_count (hg : GapLaw P g μ₀ σ₀ κ₀)
    (heps : epsZero (bIn μ₀ σ₀) (βIn σ₀ (lkap P (inputPairs g))) ≤ eps) (ℓ : ℕ) :
    shDist P eps g ℓ ^ 2 ≤ shDist P eps g 0 ^ 2 / shCount P eps g ℓ := by
  induction ℓ with
  | zero => simp only [shCount_zero, div_one, le_refl]
  | succ ℓ ih =>
    calc shDist P eps g (ℓ + 1) ^ 2
        ≤ shDist P eps g ℓ ^ 2 / actMean eps (shP P) (shPair P eps g ℓ) :=
          shDist_sq_step_le hg heps ℓ
      _ ≤ (shDist P eps g 0 ^ 2 / shCount P eps g ℓ) /
          actMean eps (shP P) (shPair P eps g ℓ) :=
          div_le_div_of_nonneg_right ih (actMean_shPair_pos hg heps ℓ).le
      _ = shDist P eps g 0 ^ 2 / shCount P eps g (ℓ + 1) := by
          rw [shCount_succ hg heps, div_div]

/-- A geometric lower bound for the original count of each actual shadow block. -/
theorem pow_le_shCount (hg : GapLaw P g μ₀ σ₀ κ₀)
    (heps : epsZero (bIn μ₀ σ₀) (βIn σ₀ (lkap P (inputPairs g))) ≤ eps) (ℓ : ℕ) :
    (eps ^ 2 / cBr (bIn μ₀ σ₀) (vIn μ₀ σ₀)) ^ ℓ ≤ shCount P eps g ℓ := by
  have hcb : 0 < cBr (bIn μ₀ σ₀) (vIn μ₀ σ₀) :=
    lt_of_lt_of_le (by have := bAbs_pos.trans_le (bAbs_le_bIn μ₀ σ₀); positivity)
      (le_max_left _ _)
  induction ℓ with
  | zero => simp only [pow_zero, shCount_zero, le_refl]
  | succ ℓ ih =>
    rw [pow_succ, shCount_succ hg heps, actMean_shPair_eq_segMean hg heps]
    exact mul_le_mul ih (segMean_bracket hg heps ℓ).1 (by positivity)
      (shCount_pos hg heps ℓ).le

theorem shDist_sq_le_geometric (hg : GapLaw P g μ₀ σ₀ κ₀)
    (heps : epsZero (bIn μ₀ σ₀) (βIn σ₀ (lkap P (inputPairs g))) ≤ eps) (ℓ : ℕ) :
    shDist P eps g ℓ ^ 2 ≤ shDist P eps g 0 ^ 2 /
      (eps ^ 2 / cBr (bIn μ₀ σ₀) (vIn μ₀ σ₀)) ^ ℓ := by
  have hε : 0 < eps := zero_lt_one.trans_le ((one_le_epsZero _ _).trans heps)
  have hcb : 0 < cBr (bIn μ₀ σ₀) (vIn μ₀ σ₀) :=
    lt_of_lt_of_le (by have := bAbs_pos.trans_le (bAbs_le_bIn μ₀ σ₀); positivity)
      (le_max_left _ _)
  exact (shDist_sq_le_initial_div_count hg heps ℓ).trans
    (div_le_div_of_nonneg_left (sq_nonneg _) (by positivity) (pow_le_shCount hg heps ℓ))

/-- Every layer after the first has squared error of order `eps⁻²`. -/
theorem shDist_sq_le_first_scale (hg : GapLaw P g μ₀ σ₀ κ₀)
    (heps : epsZero (bIn μ₀ σ₀) (βIn σ₀ (lkap P (inputPairs g))) ≤ eps)
    (hscale : cBr (bIn μ₀ σ₀) (vIn μ₀ σ₀) ≤ eps ^ 2) {ℓ : ℕ} (hℓ : 1 ≤ ℓ) :
    shDist P eps g ℓ ^ 2 ≤
      (σ₀ ^ 2 / μ₀ ^ 2 + 1) / (eps ^ 2 / cBr (bIn μ₀ σ₀) (vIn μ₀ σ₀)) := by
  have hcb : 0 < cBr (bIn μ₀ σ₀) (vIn μ₀ σ₀) :=
    lt_of_lt_of_le (by have := bAbs_pos.trans_le (bAbs_le_bIn μ₀ σ₀); positivity)
      (le_max_left _ _)
  have hratio : 1 ≤ eps ^ 2 / cBr (bIn μ₀ σ₀) (vIn μ₀ σ₀) :=
    (one_le_div hcb).2 hscale
  have h := (shDist_sq_le_geometric hg heps ℓ).trans
    (div_le_div_of_nonneg_left (sq_nonneg _) (zero_lt_one.trans_le hratio)
      (le_self_pow₀ hratio (by omega : ℓ ≠ 0)))
  rwa [shDist_zero_sq hg] at h

end

end PGM
