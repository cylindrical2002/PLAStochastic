import PLAStochastic.Index.GEP.Additive.UnconditionalHeight
import PLAStochastic.Index.Model.ExpSequence
import PLAStochastic.Index.Endpoint.GammaClosure

/-!
# Actual reference-scale budgets from the proved Model G theorem

The mean scale is the actual expected rank span of the exponential endpoint
hierarchy. Its geometric growth and uniform logarithmic discrepancy follow from
the unconditional GEP log-compression sum, including the initial layer.
No spatial derivative or Hellinger scale regularity is asserted here.
-/

set_option autoImplicit false

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory Finset

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

theorem meanSpan_geometric_log_budget {g : ℕ → Ω → ℝ} {μ₀ σ₀ κ₀ : ℝ}
    (hg : GapLaw P g μ₀ σ₀ κ₀) (hpos : ∀ᵐ ω ∂P, 0 < g 0 ω) :
    ∃ eps0 B : ℝ, 2 ≤ eps0 ∧ 0 ≤ B ∧ ∀ eps, eps0 ≤ eps →
      meanSpan P eps g 0 = 1 ∧
      (∀ j, 0 < meanSpan P eps g j) ∧
      (∀ j, 2 * meanSpan P eps g j ≤ meanSpan P eps g (j + 1)) ∧
      Real.log eps ≤ gepLogC eps ∧
      ∀ j : ℕ, |Real.log (meanSpan P eps g j) - j * gepLogC eps| ≤ B := by
  obtain ⟨e1, KF, hF⟩ := sum_abs_log_segMean_sub_le hg hpos
  have hKF : 0 ≤ KF := by simpa using hF e1 le_rfl 1
  let cb := cBr (bIn μ₀ σ₀) (vIn μ₀ σ₀)
  have hcb1 : 1 ≤ cb := one_le_cBr (bAbs_le_bIn μ₀ σ₀)
  have hcb0 : 0 < cb := by linarith
  have hlcb : 0 ≤ Real.log cb := Real.log_nonneg hcb1
  let e0 := max e1 (max (epsZero (bIn μ₀ σ₀) (βIn σ₀ (lkap P (inputPairs g))))
    (max (2 * cb) (max 2 (Real.exp (Real.log cb + KF)))))
  have he02 : 2 ≤ e0 := by simp [e0]
  refine ⟨e0, 2 * Real.log cb + 2 * KF, he02, by positivity, ?_⟩
  intro eps heps
  have heps' := heps
  change max e1 (max _ (max _ (max _ _))) ≤ eps at heps'
  simp only [max_le_iff] at heps'
  obtain ⟨he1, he₀, hecb, he2, heX⟩ := heps'
  have heps0 : 0 < eps := by linarith
  have hepssq : 0 < eps ^ 2 := by positivity
  have hlogbr : ∀ ℓ, Real.log (eps ^ 2) - Real.log cb ≤
      Real.log (segMean P eps (epLayerSeq eps g ℓ)) ∧
      Real.log (segMean P eps (epLayerSeq eps g ℓ)) ≤ Real.log cb + Real.log (eps ^ 2) := by
    intro ℓ
    obtain ⟨h1, h2⟩ := segMean_bracket hg he₀ ℓ
    have hpos' : 0 < eps ^ 2 / cb := div_pos hepssq hcb0
    constructor
    · rw [← Real.log_div hepssq.ne' hcb0.ne']
      exact Real.log_le_log hpos' h1
    · rw [← Real.log_mul hcb0.ne' hepssq.ne']
      exact Real.log_le_log (hpos'.trans_le h1) h2
  have hC1 : |Real.log (segMean P eps (epLayerSeq eps g 1)) - gepLogC eps| ≤ KF := by
    have h := hF eps he1 2
    rwa [sum_Ico_eq_sum_range, show (2 : ℕ) - 1 = 1 from rfl, sum_range_one] at h
  have hlogeps : Real.log cb + KF ≤ Real.log eps := by
    have h := Real.log_le_log (Real.exp_pos _) heX
    rwa [Real.log_exp] at h
  have hc : Real.log eps ≤ gepLogC eps := by
    have h := (hlogbr 1).1
    have h' := (abs_le.mp hC1).2
    rw [Real.log_pow] at h
    norm_num at h
    linarith
  have hC0 : |Real.log (segMean P eps (epLayerSeq eps g 0)) - gepLogC eps| ≤
      2 * Real.log cb + KF := by
    have h0 := hlogbr 0
    have h1 := hlogbr 1
    have hc1 := abs_le.mp hC1
    rw [abs_le]
    constructor <;> linarith
  have hlog : ∀ ℓ : ℕ, |Real.log (meanSpan P eps g ℓ) - ℓ * gepLogC eps| ≤
      2 * Real.log cb + 2 * KF := by
    intro ℓ
    rw [log_meanSpan_eq_sum hg he₀ ℓ]
    have e : ∑ j ∈ range ℓ, Real.log (segMean P eps (epLayerSeq eps g j)) - ℓ * gepLogC eps =
        ∑ j ∈ range ℓ, (Real.log (segMean P eps (epLayerSeq eps g j)) - gepLogC eps) := by
      rw [sum_sub_distrib, sum_const, card_range, nsmul_eq_mul]
    rw [e]
    refine (abs_sum_le_sum_abs _ _).trans ?_
    rcases Nat.eq_zero_or_pos ℓ with h0 | hℓ
    · subst h0
      simp only [range_zero, sum_empty]
      positivity
    · rw [range_eq_Ico, sum_eq_sum_Ico_succ_bot hℓ, zero_add]
      have := hF eps he1 ℓ
      linarith
  have hL := layerOK_all (layerOK_input hg) (bAbs_le_bIn μ₀ σ₀)
    (βAbs_le_βIn _ _) (vIn_pos hg.mu_pos hg.sigma_pos) (vIn_le μ₀ σ₀)
    KcAbs_le_KcIn he₀
  have hmpos : ∀ j, 0 < meanSpan P eps g j := fun j => (hL j).1.cnt_pos
  have hbig : 2 * cb ≤ eps ^ 2 := by nlinarith
  refine ⟨meanSpan_zero P eps g, hmpos, ?_, hc, hlog⟩
  intro j
  change 2 * lcount P (epLayerSeq eps g j) ≤ lcount P (epLayerSeq eps g (j + 1))
  rw [(hL j).2.2.1]
  have hseg := (segMean_bracket hg he₀ j).1
  have htwo : 2 ≤ segMean P eps (epLayerSeq eps g j) := by
    have h := (le_div_iff₀ hcb0).2 hbig
    exact h.trans hseg
  calc
    2 * lcount P (epLayerSeq eps g j) = lcount P (epLayerSeq eps g j) * 2 := mul_comm _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left htwo (hmpos j).le

/-- The actual exponential rank scale used by the Model K comparison. -/
def kepReferenceSpan (eps : ℝ) (j : ℕ) : ℝ :=
  meanSpan expSeqMeasure eps expCoord j

theorem kepReferenceSpan_eq_mean_gap {eps : ℝ} (heps : 0 ≤ eps) (j : ℕ) :
    kepReferenceSpan eps j = lmean expSeqMeasure (epLayerSeq eps expCoord j) :=
  (lmean_eq_lcount_epLayerSeq iidSeq_expCoord (hasLaw_expCoord 0) heps j).symm

theorem kepReferenceSpan_budget :
    ∃ eps0 B : ℝ, 2 ≤ eps0 ∧ 0 ≤ B ∧ ∀ eps, eps0 ≤ eps →
      kepReferenceSpan eps 0 = 1 ∧
      (∀ j, 0 < kepReferenceSpan eps j) ∧
      (∀ j, 2 * kepReferenceSpan eps j ≤ kepReferenceSpan eps (j + 1)) ∧
      Real.log eps ≤ gepLogC eps ∧
      ∀ j : ℕ, |Real.log (kepReferenceSpan eps j) - j * gepLogC eps| ≤ B := by
  exact meanSpan_geometric_log_budget gapLaw_expCoord
    (iidSeq_expCoord.ae_pos_of_expMeasure_one (hasLaw_expCoord 0) 0)

end

end PGM
