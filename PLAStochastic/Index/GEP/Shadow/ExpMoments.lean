import PLAStochastic.Index.GEP.Shadow.Regeneration
import PLAStochastic.Index.GEP.Shadow.MarkMoments
import PLAStochastic.Index.Model.ExpConcentration
import PLAStochastic.Index.GEP.OrbitClosure.Defs
import PLAStochastic.Index.Endpoint.HyperSegmentMoments

/-!
# Uniform exponential moments of the actual passive shadow

Conditional on the gaps, each passive mark is a sum of exactly its actual input
count many independent Exp(1) variables. The exact conditional moment generating
function and the existing exponential bound for the counts yield a fixed
exponential moment for every normalized shadow layer.

The one-variable Exp(1) integral and finite iid-sum formula are imported from
`ExpConcentration`; no regularity assumption is imposed on the original gap law.
-/

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory Finset Set

theorem integrable_exp_mul_expCoord_sum (a n : ℕ) {t : ℝ} (ht : t < 1) :
    Integrable (fun ξ : ℕ → ℝ => Real.exp (t * ∑ k ∈ range n, ξ (a + k))) expSeqMeasure := by
  simpa only [expSum, Finset.sum_Ico_eq_sum_range, Nat.add_sub_cancel_left, expCoord] using
    integrable_exp_mul_expSum iidSeq_expCoord (hasLaw_expCoord 0) a (a + n) ht

theorem integral_exp_mul_expCoord_sum (a n : ℕ) {t : ℝ} (ht : t < 1) :
    ∫ ξ, Real.exp (t * ∑ k ∈ range n, ξ (a + k)) ∂expSeqMeasure = (1 - t)⁻¹ ^ n := by
  simpa only [mgf, expSum, Finset.sum_Ico_eq_sum_range, Nat.add_sub_cancel_left, expCoord] using
    mgf_expSum iidSeq_expCoord (hasLaw_expCoord 0) a (a + n) ht

variable {Ω : Type*}

theorem integrable_exp_shTri_mark_fiber (eps : ℝ) (g : ℕ → Ω → ℝ) (ℓ j : ℕ)
    (ω : Ω) {t : ℝ} (ht : t < 1) :
    Integrable (fun ξ : ℕ → ℝ => Real.exp (t * (shTri eps g ℓ j (ω, ξ)).2)) expSeqMeasure := by
  simp_rw [shTri_mark_eq_sum_range]
  exact integrable_exp_mul_expCoord_sum _ _ ht

/-- Exact conditional Gamma moment generating function, including the zero-count convention. -/
theorem integral_exp_shTri_mark_fiber (eps : ℝ) (g : ℕ → Ω → ℝ) (ℓ j : ℕ)
    (ω : Ω) {t : ℝ} (ht : t < 1) :
    ∫ ξ, Real.exp (t * (shTri eps g ℓ j (ω, ξ)).2) ∂expSeqMeasure =
      (1 - t)⁻¹ ^ (epLayerSeq eps g ℓ j ω).2 := by
  simp_rw [shTri_mark_eq_sum_range]
  exact integral_exp_mul_expCoord_sum _ _ ht

/-- The Gamma moment is dominated by the count exponential moment at twice the rate. -/
theorem gamma_mgf_le_exp (n : ℕ) {t : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1 / 2) :
    (1 - t)⁻¹ ^ n ≤ Real.exp (2 * t * n) := by
  have hbase : (1 - t)⁻¹ ≤ Real.exp (2 * t) :=
    (inv_one_sub_le_exp ht ht1).trans (Real.exp_le_exp.mpr (by nlinarith))
  calc (1 - t)⁻¹ ^ n ≤ Real.exp (2 * t) ^ n :=
      pow_le_pow_left₀ (inv_nonneg.mpr (by linarith)) hbase n
    _ = Real.exp (2 * t * n) := by rw [← Real.exp_nat_mul]; congr 1; ring

variable [MeasurableSpace Ω] {P : Measure Ω} {g : ℕ → Ω → ℝ}

/-- Transfer an integrable exponential moment of the count to the passive mark.
The normalization `m` can be any positive deterministic scale. -/
theorem shadow_expMom_of_count [IsProbabilityMeasure P]
    (hg : ∀ k, Measurable (g k)) (eps : ℝ) (ℓ j : ℕ) {m θ B : ℝ}
    (hm : 0 < m) (hθ : 0 ≤ θ) (hθm : θ / m ≤ 1 / 2)
    (hN : Integrable (fun ω => Real.exp (2 * θ * (epLayerSeq eps g ℓ j ω).2 / m)) P)
    (hNB : ∫ ω, Real.exp (2 * θ * (epLayerSeq eps g ℓ j ω).2 / m) ∂P ≤ B) :
    Integrable (fun p => Real.exp (θ * (shTri eps g ℓ j p).2 / m)) (shP P) ∧
      ∫ p, Real.exp (θ * (shTri eps g ℓ j p).2 / m) ∂shP P ≤ B := by
  have ht0 : 0 ≤ θ / m := div_nonneg hθ hm.le
  have ht1 : θ / m < 1 := lt_of_le_of_lt hθm (by norm_num)
  have hmeas : Measurable (fun p => Real.exp (θ * (shTri eps g ℓ j p).2 / m)) :=
    ((measurable_const.mul (measurable_shTri hg eps ℓ j).snd).div_const m).exp
  have hfiber (ω : Ω) : Integrable
      (fun ξ => Real.exp (θ * (shTri eps g ℓ j (ω, ξ)).2 / m)) expSeqMeasure := by
    simpa only [div_mul_eq_mul_div] using integrable_exp_shTri_mark_fiber eps g ℓ j ω ht1
  have hfiberEq (ω : Ω) :
      ∫ ξ, Real.exp (θ * (shTri eps g ℓ j (ω, ξ)).2 / m) ∂expSeqMeasure =
        (1 - θ / m)⁻¹ ^ (epLayerSeq eps g ℓ j ω).2 := by
    simpa only [div_mul_eq_mul_div] using integral_exp_shTri_mark_fiber eps g ℓ j ω ht1
  have hbound (ω : Ω) : (1 - θ / m)⁻¹ ^ (epLayerSeq eps g ℓ j ω).2 ≤
      Real.exp (2 * θ * (epLayerSeq eps g ℓ j ω).2 / m) := by
    convert gamma_mgf_le_exp (epLayerSeq eps g ℓ j ω).2 ht0 hθm using 1
    congr 1
    ring
  have hpow : Measurable (fun ω => (1 - θ / m)⁻¹ ^ (epLayerSeq eps g ℓ j ω).2) :=
    (Measurable.of_discrete (f := fun n : ℕ => (1 - θ / m)⁻¹ ^ n)).comp
      (measurable_epLayerSeq_entry hg eps ℓ j).snd
  have hpint : Integrable (fun ω => (1 - θ / m)⁻¹ ^ (epLayerSeq eps g ℓ j ω).2) P :=
    hN.mono' hpow.aestronglyMeasurable (Filter.Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (by positivity) _)]
      exact hbound ω)
  have hint : Integrable (fun p => Real.exp (θ * (shTri eps g ℓ j p).2 / m)) (shP P) := by
    apply (integrable_prod_iff hmeas.aestronglyMeasurable).mpr
    refine ⟨Filter.Eventually.of_forall hfiber, ?_⟩
    simpa only [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), hfiberEq] using hpint
  refine ⟨hint, ?_⟩
  rw [shP, integral_prod _ hint]
  simp_rw [hfiberEq]
  exact (integral_mono hpint hN hbound).trans hNB

/-! ## Absolute exponential constants for all actual shadow layers -/

variable [IsProbabilityMeasure P] {μ₀ σ₀ κ₀ eps : ℝ}

private theorem one_le_shCount_for_expMom (hg : GapLaw P g μ₀ σ₀ κ₀)
    (heps : epsZero (bIn μ₀ σ₀) (βIn σ₀ (lkap P (inputPairs g))) ≤ eps) (ℓ : ℕ) :
    1 ≤ shCount P eps g ℓ := by
  have hL := (layerOK_all (layerOK_input hg) (bAbs_le_bIn μ₀ σ₀) (βAbs_le_βIn _ _)
    (vIn_pos hg.mu_pos hg.sigma_pos) (vIn_le μ₀ σ₀) KcAbs_le_KcIn heps ℓ).1
  have hN : ∀ᵐ ω ∂P, (1 : ℝ) ≤ ((epLayerSeq eps g ℓ 0 ω).2 : ℝ) := by
    filter_upwards [ae_one_le_epLayerSeq_count hg heps ℓ 0] with ω hω
    exact_mod_cast hω
  have h := integral_mono_ae (integrable_const (1 : ℝ)) (hL.cnt2.integrable one_le_two) hN
  rw [shCount_eq]
  simpa only [lcount, integral_const, probReal_univ, one_smul] using h

/-- The passive coordinate has a fixed exponential moment uniformly over every layer,
under the original gap-law hypotheses and the existing `epsK` threshold. -/
theorem expMom_shPair_snd (hg : GapLaw P g μ₀ σ₀ κ₀)
    (heps : epsK (bIn μ₀ σ₀) (βIn σ₀ (lkap P (inputPairs g))) ≤ eps) (ℓ : ℕ) :
    Integrable (fun p => Real.exp ((θK / 2) * (shPair P eps g ℓ 0 p).2)) (shP P) ∧
      ∫ p, Real.exp ((θK / 2) * (shPair P eps g ℓ 0 p).2) ∂shP P ≤ CK := by
  have he0 := epsZero_le_of_epsK_le heps
  have hm := shCount_pos hg he0 ℓ
  have hm1 := one_le_shCount_for_expMom hg he0 ℓ
  have hθm : (θK / 2) / shCount P eps g ℓ ≤ 1 / 2 := by
    rw [div_le_iff₀ hm]
    linarith [θK_le_one]
  obtain ⟨hN, hNB, -⟩ := hyperexp_input hg heps ℓ
  have h2 : 2 * (θK / 2) = θK := by ring
  have hN' : Integrable (fun ω => Real.exp
      (2 * (θK / 2) * (epLayerSeq eps g ℓ 0 ω).2 / shCount P eps g ℓ)) P := by
    simpa only [h2, shCount_eq] using hN
  have hNB' : ∫ ω, Real.exp
      (2 * (θK / 2) * (epLayerSeq eps g ℓ 0 ω).2 / shCount P eps g ℓ) ∂P ≤ CK := by
    simpa only [h2, shCount_eq] using hNB
  simpa only [shPair, mul_div_assoc] using
    shadow_expMom_of_count hg.iid.measurable eps ℓ 0 hm (half_pos θK_pos).le hθm hN' hNB'

/-- The uniform exponential moment holds for every block of the actual layer. -/
theorem expMom_shPair_snd_all (hg : GapLaw P g μ₀ σ₀ κ₀)
    (heps : epsK (bIn μ₀ σ₀) (βIn σ₀ (lkap P (inputPairs g))) ≤ eps) (ℓ j : ℕ) :
    Integrable (fun p => Real.exp ((θK / 2) * (shPair P eps g ℓ j p).2)) (shP P) ∧
      ∫ p, Real.exp ((θK / 2) * (shPair P eps g ℓ j p).2) ∂shP P ≤ CK := by
  have h := expMom_shPair_snd hg heps ℓ
  have hid := ((iidSeqE_shPair hg (epsZero_le_of_epsK_le heps) ℓ).ident j).comp
    (u := fun p : ℝ × ℝ => Real.exp ((θK / 2) * p.2))
    (measurable_const.mul measurable_snd).exp
  exact ⟨hid.integrable_iff.mpr h.1, hid.integral_eq.trans_le h.2⟩

/-- The actual shadow probability law satisfies the same fixed exponential bound. -/
theorem expMom_shLawPM (hg : GapLaw P g μ₀ σ₀ κ₀)
    (heps : epsK (bIn μ₀ σ₀) (βIn σ₀ (lkap P (inputPairs g))) ≤ eps) (ℓ : ℕ) :
    ExpMom (θK / 2) CK (shLawPM P hg.iid.measurable eps ℓ) := by
  have h := expMom_shPair_snd hg heps ℓ
  have hm := (measurable_shPair hg.iid.measurable P eps ℓ 0).snd
  have hF : Measurable (fun x : ℝ => Real.exp ((θK / 2) * x)) :=
    (measurable_const.mul measurable_id).exp
  refine ⟨?_, ?_⟩
  · exact (integrable_map_measure hF.aestronglyMeasurable hm.aemeasurable).mpr h.1
  · change (∫ x, Real.exp ((θK / 2) * x) ∂(shP P).map
      (fun p => (shPair P eps g ℓ 0 p).2)) ≤ CK
    rw [integral_map hm.aemeasurable hF.aestronglyMeasurable]
    exact h.2

end

end PGM
