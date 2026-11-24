import PLAStochastic.Index.GEP.Shadow.EndpointBridge
import Mathlib.MeasureTheory.Integral.Prod

/-!
# WP3: integrating the conditional mark moments

Conditional on the gaps, the passive mark has mean `N` and centered second
moment `N`, where `N` is the actual block's input count.  This file establishes
integrability on the product space before applying Fubini, then transfers these
identities to the normalized shadow coordinates.
-/

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory Finset Set

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
variable {g : ℕ → Ω → ℝ}

theorem measurable_epLayerSeq_entry (hg : ∀ t, Measurable (g t))
    (eps : ℝ) (ℓ j : ℕ) : Measurable (epLayerSeq eps g ℓ j) := by
  rw [epLayerSeq_eq]
  exact (measurable_pi_apply j).comp ((measurable_pairLayer eps ℓ).comp
    (measurable_seq fun t => (hg t).prodMk measurable_const))

omit [MeasurableSpace Ω] in
/-- Every passive mark is nonnegative, including on the conventional zero-length blocks. -/
theorem ae_nonneg_shTri_mark_fiber (eps : ℝ) (g : ℕ → Ω → ℝ) (ℓ j : ℕ) (ω : Ω) :
    ∀ᵐ ξ ∂expSeqMeasure, 0 ≤ (shTri eps g ℓ j (ω, ξ)).2 := by
  have hall : ∀ᵐ ξ ∂expSeqMeasure, ∀ t, 0 < expCoord t ξ :=
    ae_all_iff.mpr fun t => iidSeq_expCoord.ae_pos_of_expMeasure_one (hasLaw_expCoord 0) t
  filter_upwards [hall] with ξ hξ
  rw [shTri_mark_eq_sum_range]
  exact sum_nonneg fun t _ => (hξ _).le

/-- An integrable actual count makes the passive mark integrable on the full product space. -/
theorem integrable_shTri_mark [IsProbabilityMeasure P]
    (hg : ∀ t, Measurable (g t)) (eps : ℝ) (ℓ j : ℕ)
    (hN : Integrable (fun ω => ((epLayerSeq eps g ℓ j ω).2 : ℝ)) P) :
    Integrable (fun p => (shTri eps g ℓ j p).2) (shP P) := by
  apply (integrable_prod_iff (measurable_shTri hg eps ℓ j).snd.aestronglyMeasurable).mpr
  refine ⟨ae_of_all _ (integrable_shTri_mark_fiber eps g ℓ j), ?_⟩
  have heq : (fun ω => ∫ ξ, ‖(shTri eps g ℓ j (ω, ξ)).2‖ ∂expSeqMeasure) =
      fun ω => ((epLayerSeq eps g ℓ j ω).2 : ℝ) := by
    funext ω
    rw [← integral_shTri_mark_fiber eps g ℓ j ω]
    apply integral_congr_ae
    filter_upwards [ae_nonneg_shTri_mark_fiber eps g ℓ j ω] with ξ hξ
    exact Real.norm_of_nonneg hξ
  rwa [heq]

/-- Unconditional passive mean equals the actual expected count. -/
theorem integral_shTri_mark [IsProbabilityMeasure P]
    (hg : ∀ t, Measurable (g t)) (eps : ℝ) (ℓ j : ℕ)
    (hN : Integrable (fun ω => ((epLayerSeq eps g ℓ j ω).2 : ℝ)) P) :
    ∫ p, (shTri eps g ℓ j p).2 ∂shP P =
      ∫ ω, ((epLayerSeq eps g ℓ j ω).2 : ℝ) ∂P := by
  rw [shP, integral_prod _ (integrable_shTri_mark hg eps ℓ j hN)]
  simp_rw [integral_shTri_mark_fiber]

/-- The mark-count difference has an integrable square as soon as the count is integrable. -/
theorem integrable_shTri_mark_sub_sq [IsProbabilityMeasure P]
    (hg : ∀ t, Measurable (g t)) (eps : ℝ) (ℓ j : ℕ)
    (hN : Integrable (fun ω => ((epLayerSeq eps g ℓ j ω).2 : ℝ)) P) :
    Integrable (fun p => ((shTri eps g ℓ j p).2 -
      ((epLayerSeq eps g ℓ j p.1).2 : ℝ)) ^ 2) (shP P) := by
  have hm : Measurable (fun p : Ω × (ℕ → ℝ) =>
      (shTri eps g ℓ j p).2 - ((epLayerSeq eps g ℓ j p.1).2 : ℝ)) :=
    (measurable_shTri hg eps ℓ j).snd.sub
      ((measurable_natCast_snd.comp (measurable_epLayerSeq_entry hg eps ℓ j)).comp measurable_fst)
  apply (integrable_prod_iff (hm.pow_const 2).aestronglyMeasurable).mpr
  refine ⟨ae_of_all _ (integrable_shTri_mark_sub_sq_fiber eps g ℓ j), ?_⟩
  simpa only [Real.norm_eq_abs, abs_pow, sq_abs, integral_shTri_mark_sub_sq_fiber] using hN

/-- The unconditional centered mark second moment is exactly the expected count. -/
theorem integral_shTri_mark_sub_sq [IsProbabilityMeasure P]
    (hg : ∀ t, Measurable (g t)) (eps : ℝ) (ℓ j : ℕ)
    (hN : Integrable (fun ω => ((epLayerSeq eps g ℓ j ω).2 : ℝ)) P) :
    ∫ p, ((shTri eps g ℓ j p).2 - ((epLayerSeq eps g ℓ j p.1).2 : ℝ)) ^ 2 ∂shP P =
      ∫ ω, ((epLayerSeq eps g ℓ j ω).2 : ℝ) ∂P := by
  rw [shP, integral_prod _ (integrable_shTri_mark_sub_sq hg eps ℓ j hN)]
  simp_rw [integral_shTri_mark_sub_sq_fiber]

/-- Square-integrable counts imply square-integrable passive marks. -/
theorem memLp_shTri_mark [IsProbabilityMeasure P]
    (hg : ∀ t, Measurable (g t)) (eps : ℝ) (ℓ j : ℕ)
    (hN : MemLp (fun ω => ((epLayerSeq eps g ℓ j ω).2 : ℝ)) 2 P) :
    MemLp (fun p => (shTri eps g ℓ j p).2) 2 (shP P) := by
  have hI := integrable_shTri_mark_sub_sq hg eps ℓ j (hN.integrable one_le_two)
  have hN' : MemLp (fun p : Ω × (ℕ → ℝ) => ((epLayerSeq eps g ℓ j p.1).2 : ℝ))
      2 (shP P) := hN.comp_measurePreserving measurePreserving_fst
  have hD : MemLp (fun p => (shTri eps g ℓ j p).2 -
      ((epLayerSeq eps g ℓ j p.1).2 : ℝ)) 2 (shP P) :=
    (memLp_two_iff_integrable_sq
      ((measurable_shTri hg eps ℓ j).snd.aestronglyMeasurable.sub hN'.aestronglyMeasurable)).mpr hI
  convert hD.add hN' using 1
  ext p
  exact (sub_add_cancel _ _).symm

/-- The normalized shadow coordinate has mean one whenever its mean count is positive. -/
theorem integral_shPair_snd [IsProbabilityMeasure P]
    (hg : ∀ t, Measurable (g t)) (eps : ℝ) (ℓ : ℕ)
    (hN : Integrable (fun ω => ((epLayerSeq eps g ℓ 0 ω).2 : ℝ)) P)
    (hm : shCount P eps g ℓ ≠ 0) :
    ∫ p, (shPair P eps g ℓ 0 p).2 ∂shP P = 1 := by
  simp only [shPair]
  rw [integral_div, integral_shTri_mark hg eps ℓ 0 hN]
  change lcount P (epLayerSeq eps g ℓ) / shCount P eps g ℓ = 1
  rw [← shCount_eq]
  exact div_self hm

omit [MeasurableSpace Ω] in
/-- Conditional raw second moment of the mark: `E[M² | gaps] = N² + N`. -/
theorem integral_shTri_mark_sq_fiber (eps : ℝ) (g : ℕ → Ω → ℝ)
    (ℓ j : ℕ) (ω : Ω) :
    ∫ ξ, (shTri eps g ℓ j (ω, ξ)).2 ^ 2 ∂expSeqMeasure =
      ((epLayerSeq eps g ℓ j ω).2 : ℝ) ^ 2 + (epLayerSeq eps g ℓ j ω).2 := by
  let N : ℝ := (epLayerSeq eps g ℓ j ω).2
  let M : (ℕ → ℝ) → ℝ := fun ξ => (shTri eps g ℓ j (ω, ξ)).2
  have hI : Integrable M expSeqMeasure := integrable_shTri_mark_fiber eps g ℓ j ω
  have hD : Integrable (fun ξ => (M ξ - N) ^ 2) expSeqMeasure :=
    integrable_shTri_mark_sub_sq_fiber eps g ℓ j ω
  have hm : ∫ ξ, M ξ ∂expSeqMeasure = N := integral_shTri_mark_fiber eps g ℓ j ω
  have hd : ∫ ξ, (M ξ - N) ^ 2 ∂expSeqMeasure = N :=
    integral_shTri_mark_sub_sq_fiber eps g ℓ j ω
  have heq : (fun ξ => M ξ ^ 2) = fun ξ => (M ξ - N) ^ 2 + (2 * N) * M ξ - N ^ 2 := by
    funext ξ; ring
  change ∫ ξ, M ξ ^ 2 ∂expSeqMeasure = N ^ 2 + N
  rw [heq, integral_sub (f := fun ξ => (M ξ - N) ^ 2 + (2 * N) * M ξ)
    (g := fun _ => N ^ 2) (hD.add (hI.const_mul (2 * N))) (integrable_const _),
    integral_add (f := fun ξ => (M ξ - N) ^ 2) (g := fun ξ => (2 * N) * M ξ)
      hD (hI.const_mul (2 * N)), integral_const_mul, hm, hd]
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
  ring

/-- Unconditional raw second moment, with the full product-space integrability established. -/
theorem integral_shTri_mark_sq [IsProbabilityMeasure P]
    (hg : ∀ t, Measurable (g t)) (eps : ℝ) (ℓ j : ℕ)
    (hN : MemLp (fun ω => ((epLayerSeq eps g ℓ j ω).2 : ℝ)) 2 P) :
    ∫ p, (shTri eps g ℓ j p).2 ^ 2 ∂shP P =
      (∫ ω, ((epLayerSeq eps g ℓ j ω).2 : ℝ) ^ 2 ∂P) +
        ∫ ω, ((epLayerSeq eps g ℓ j ω).2 : ℝ) ∂P := by
  rw [shP, integral_prod _ (memLp_shTri_mark hg eps ℓ j hN).integrable_sq]
  simp_rw [integral_shTri_mark_sq_fiber]
  exact integral_add hN.integrable_sq (hN.integrable one_le_two)

/-- The leading shadow coordinate is square integrable if the actual count is. -/
theorem memLp_shPair_snd [IsProbabilityMeasure P]
    (hg : ∀ t, Measurable (g t)) (eps : ℝ) (ℓ : ℕ)
    (hN : MemLp (fun ω => ((epLayerSeq eps g ℓ 0 ω).2 : ℝ)) 2 P) :
    MemLp (fun p => (shPair P eps g ℓ 0 p).2) 2 (shP P) := by
  simpa only [shPair, div_eq_mul_inv] using
    (memLp_shTri_mark hg eps ℓ 0 hN).mul_const (shCount P eps g ℓ)⁻¹

/-- Exact second moment of the normalized shadow, in terms of the actual input count. -/
theorem integral_shPair_snd_sq [IsProbabilityMeasure P]
    (hg : ∀ t, Measurable (g t)) (eps : ℝ) (ℓ : ℕ)
    (hN : MemLp (fun ω => ((epLayerSeq eps g ℓ 0 ω).2 : ℝ)) 2 P)
    (hm : shCount P eps g ℓ ≠ 0) :
    ∫ p, (shPair P eps g ℓ 0 p).2 ^ 2 ∂shP P =
      lcount2 P (epLayerSeq eps g ℓ) / shCount P eps g ℓ ^ 2 + 1 / shCount P eps g ℓ := by
  simp only [shPair, div_pow]
  rw [integral_div, integral_shTri_mark_sq hg eps ℓ 0 hN]
  change (lcount2 P (epLayerSeq eps g ℓ) + lcount P (epLayerSeq eps g ℓ)) /
    shCount P eps g ℓ ^ 2 = _
  rw [← shCount_eq]
  field_simp

theorem integral_shPair_snd_sq_le [IsProbabilityMeasure P]
    (hg : ∀ t, Measurable (g t)) {eps b β vmin Kc : ℝ} {ℓ : ℕ}
    (hL : LayerOK P (epLayerSeq eps g ℓ) b β vmin Kc) :
    ∫ p, (shPair P eps g ℓ 0 p).2 ^ 2 ∂shP P ≤ Kc + 1 / shCount P eps g ℓ := by
  have hm : 0 < shCount P eps g ℓ := by rw [shCount_eq]; exact hL.cnt_pos
  rw [integral_shPair_snd_sq hg eps ℓ hL.cnt2 hm.ne']
  gcongr
  rw [div_le_iff₀ (sq_pos_of_pos hm), shCount_eq]
  exact hL.cnt_sq

/-- The active normalized coordinate has the original normalized layer law. -/
theorem integral_shPair_fst [IsProbabilityMeasure P]
    (eps : ℝ) (g : ℕ → Ω → ℝ) (ℓ : ℕ) (hm : shMean P eps g ℓ ≠ 0) :
    ∫ p, (shPair P eps g ℓ 0 p).1 ∂shP P = 1 := by
  simp only [shPair, shTri_fst_eq_actual, integral_div, shP]
  rw [integral_fun_fst (fun ω => (epLayerSeq eps g ℓ 0 ω).1)]
  simp only [probReal_univ, smul_eq_mul, one_mul]
  change lmean P (epLayerSeq eps g ℓ) / shMean P eps g ℓ = 1
  rw [← shMean_eq]
  exact div_self hm

/-- Every actual layer invariant provides all moments needed by same-tree synchronization. -/
theorem shPair_moments_of_layerOK [IsProbabilityMeasure P]
    (hg : ∀ t, Measurable (g t)) {eps b β vmin Kc : ℝ} {ℓ : ℕ}
    (hL : LayerOK P (epLayerSeq eps g ℓ) b β vmin Kc) :
    MemLp (fun p => (shPair P eps g ℓ 0 p).1) 2 (shP P) ∧
      MemLp (fun p => (shPair P eps g ℓ 0 p).2) 2 (shP P) ∧
      (∫ p, (shPair P eps g ℓ 0 p).1 ∂shP P) = 1 ∧
      (∫ p, (shPair P eps g ℓ 0 p).2 ∂shP P) = 1 := by
  have hμ : 0 < shMean P eps g ℓ := by rw [shMean_eq]; exact hL.law.mu_pos
  have hm : 0 < shCount P eps g ℓ := by rw [shCount_eq]; exact hL.cnt_pos
  refine ⟨?_, memLp_shPair_snd hg eps ℓ hL.cnt2, integral_shPair_fst eps g ℓ hμ.ne',
    integral_shPair_snd hg eps ℓ (hL.cnt2.integrable one_le_two) hm.ne'⟩
  have hX : MemLp (fun ω => (epLayerSeq eps g ℓ 0 ω).1) 2 P :=
    hL.law.memLp3.mono_exponent (by norm_num)
  have hX' : MemLp (fun p : Ω × (ℕ → ℝ) => (epLayerSeq eps g ℓ 0 p.1).1) 2 (shP P) :=
    hX.comp_measurePreserving measurePreserving_fst
  simpa only [shPair, shTri_fst_eq_actual, div_eq_mul_inv] using
    hX'.mul_const (shMean P eps g ℓ)⁻¹

end

end PGM
