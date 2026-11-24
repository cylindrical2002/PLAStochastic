import PLAStochastic.Index.CEPS.Tails.OccupationSeries

/-!
# Exact finite-cutoff budgets for the actual outer tails

The early terms use W-7 interval unions. Negative late terms use the actual
segment tail, whereas positive late terms use the independent drawup endpoint
tail. No final exponential occupation estimate is a hypothesis.
-/

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Finset WienerHopf

/-- Sum a finite uniform norm bound and an absolutely convergent late tail. -/
theorem norm_tsum_le_cutoff {F : ℕ → ℂ} (hF : Summable (fun k => ‖F k‖)) (N : ℕ)
    {A B : ℝ} (hA : 0 ≤ A) (hsmall : ∀ k < N, ‖F k‖ ≤ ((N + 1 : ℕ) : ℝ) ^ 2 * A)
    (hlate : (∑' k, ‖F (k + N)‖) ≤ B) :
    ‖∑' k, F k‖ ≤ ((N + 1 : ℕ) : ℝ) ^ 3 * A + B := by
  refine (norm_tsum_le_tsum_norm hF).trans ?_
  rw [← hF.sum_add_tsum_nat_add N]
  have hs : ∑ k ∈ Finset.range N, ‖F k‖ ≤ (N : ℝ) * ((N + 1 : ℕ) : ℝ) ^ 2 * A := by
    refine (Finset.sum_le_sum fun k hk => hsmall k (Finset.mem_range.mp hk)).trans (le_of_eq ?_)
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    ring
  have hn : (N : ℝ) * ((N + 1 : ℕ) : ℝ) ^ 2 * A ≤ ((N + 1 : ℕ) : ℝ) ^ 3 * A := by
    push_cast
    nlinarith [mul_nonneg (sq_nonneg ((N : ℝ) + 1)) hA, (Nat.cast_nonneg N : (0 : ℝ) ≤ N)]
  linarith

/-- Localized certificate occupations are bounded by actual segment survival. -/
theorem CepsGapDensity.norm_cepsDriftOccupationTerm_le_surv {ν : ProbabilityMeasure ℝ}
    {f : ℝ → ℝ} {D eps : ℝ} (hf : CepsGapDensity ν f D) {E : Set ℝ} (hE : MeasurableSet E)
    {t : ℂ} (ht : 0 ≤ t.re) (k : ℕ) :
    ‖cepsDriftOccupationTerm ν eps E t k‖ ≤ (iidLaw ν).real (survSet eps k) := by
  refine (hf.norm_marked_event_le ht k (measurableSet_cepsDriftEvent eps hE k)).trans
    (measureReal_mono (fun g h => ?_) (measure_ne_top _ _))
  obtain ⟨ij, -, hc, -⟩ := h
  exact cert_lt_gapSegLen_of_certOK hc

/-- Actual segment survival tails summed beyond an arbitrary cutoff. -/
theorem RegLaw.summable_segment_survival_tail {ν : ProbabilityMeasure ℝ}
    {D θ vlo vhi eps : ℝ} (hν : RegLaw D θ vlo vhi ν) (hθ : 0 < θ) (hvlo : 0 < vlo)
    (heps : epsZero (regB vhi) (regBeta D θ vlo) ≤ eps) (N : ℕ) :
    Summable (fun k => (iidLaw ν).real (survSet eps (k + N))) ∧
    (∑' k, (iidLaw ν).real (survSet eps (k + N))) ≤
      (72 / 71 : ℝ) * Real.exp (-(tailRate * regV vlo) * N / eps ^ 2) /
        (1 - Real.exp (-(tailRate * regV vlo) / eps ^ 2)) := by
  have heps0 : 0 < eps := lt_of_lt_of_le zero_lt_one ((one_le_epsZero _ _).trans heps)
  set a := tailRate * regV vlo / eps ^ 2
  have ha : 0 < a := by have hv := regV_pos hvlo; have hr := tailRate_pos; positivity
  have hr0 : 0 ≤ Real.exp (-a) := (Real.exp_pos _).le
  have hr1 : Real.exp (-a) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have hgeom : Summable (fun k : ℕ => (72 / 71 : ℝ) * Real.exp (-a * N) * Real.exp (-a) ^ k) :=
    (summable_geometric_of_lt_one hr0 hr1).mul_left _
  have hle : ∀ k : ℕ, (iidLaw ν).real (survSet eps (k + N)) ≤
      (72 / 71 : ℝ) * Real.exp (-a * N) * Real.exp (-a) ^ k := by
    intro k
    have h := gapSegLen_tail (regV_pos hvlo) heps (hν.momClass hθ hvlo) (k + N)
    have hr := ENNReal.toReal_mono ENNReal.ofReal_ne_top h
    rw [ENNReal.toReal_ofReal (by positivity)] at hr
    refine hr.trans (le_of_eq ?_)
    rw [← Real.exp_nat_mul, mul_assoc, ← Real.exp_add]
    congr 2
    dsimp [a]
    push_cast
    ring
  have hs := hgeom.of_nonneg_of_le (fun _ => measureReal_nonneg) hle
  refine ⟨hs, (hs.tsum_le_tsum hle hgeom).trans (le_of_eq ?_)⟩
  rw [tsum_mul_left, tsum_geometric_of_lt_one hr0 hr1]
  dsimp [a]
  congr 2 <;> ring

/-- A finite-cutoff negative outer-tail budget, using real actual-pair integrals. -/
theorem ceps_negative_tail_cutoff {ν : ProbabilityMeasure ℝ} {D θ vlo vhi eps δ : ℝ}
    (hν : RegLaw D θ vlo vhi ν) (hθ : 0 < θ) (hD : 0 < D) (hvlo : 0 < vlo)
    (hδ : 0 < δ) (hδ1 : δ < 1)
    (heps : epsZero (regB vhi) (regBeta D θ vlo) ≤ eps)
    {f : ℝ → ℝ} (hf : CepsGapDensity ν f D) {t : ℂ} (ht : 0 ≤ t.re) (N : ℕ) :
    ‖∫ μ in Ioo (-1) (-δ), cepsActualPair ν f eps t μ‖ ≤
      ((N + 1 : ℕ) : ℝ) ^ 3 *
        Real.exp (-(driftRate (D * Real.exp θ) θ δ * (2 * eps * (1 - δ)))) +
      (72 / 71 : ℝ) * Real.exp (-(tailRate * regV vlo) * N / eps ^ 2) /
        (1 - Real.exp (-(tailRate * regV vlo) / eps ^ 2)) := by
  obtain ⟨-, heps1, -, -, hfin, hT, -⟩ :=
    momClass_setup (regV_pos hvlo) heps (hν.momClass hθ hvlo)
  have heps0 : 0 < eps := by linarith
  have hsub : Ioo (-1) (-δ) ⊆ Ioi (-1 : ℝ) := fun _ h => h.1
  have hseries := hf.hasSum_cepsDriftOccupation heps0 hfin hT measurableSet_Ioo hsub ht
  have hsurv := summable_measureReal_survSet hfin hT
  have hnorm : Summable (fun k => ‖cepsDriftOccupationTerm ν eps (Ioo (-1) (-δ)) t k‖) :=
    hsurv.1.of_nonneg_of_le (fun _ => norm_nonneg _) (hf.norm_cepsDriftOccupationTerm_le_surv
      measurableSet_Ioo ht)
  rw [← hseries.tsum_eq]
  refine norm_tsum_le_cutoff hnorm N (Real.exp_pos _).le (fun k hk => ?_) ?_
  · refine (hf.norm_negativeOccupation_le hδ1 ht k).trans
      ((measureReal_not_cepsDrawupOK_of_regLaw hν hθ hD hvlo hδ hδ1 heps0.le k).trans ?_)
    gcongr
  · have hlate := hν.summable_segment_survival_tail hθ hvlo heps N
    exact ((hnorm.comp_injective (fun i j h => by omega)).tsum_le_tsum
      (fun k => hf.norm_cepsDriftOccupationTerm_le_surv measurableSet_Ioo ht (k + N))
      hlate.1).trans hlate.2

/-- A finite-cutoff positive outer-tail budget against the actual drawup occupation. -/
theorem ceps_positive_tail_cutoff {ν : ProbabilityMeasure ℝ} {D θ vlo vhi eps δ : ℝ}
    (hν : RegLaw D θ vlo vhi ν) (hθ : 0 < θ) (hD : 0 < D) (hvlo : 0 < vlo)
    (hδ : 0 < δ)
    (heps : epsZero (regB vhi) (regBeta D θ vlo) ≤ eps)
    {f : ℝ → ℝ} (hf : CepsGapDensity ν f D) {t : ℂ} (ht : 0 ≤ t.re) (N : ℕ)
    (hN : 2 * (2 * eps * (1 + δ)) ≤ δ * N / 2) :
    ‖(∑ k ∈ Finset.range (⌊2 * eps⌋₊ + 1), cepsLaplace ν t ^ k) +
      (∫ μ in Ici δ, cepsActualPair ν f eps t μ) -
      cepsDrawupOccupation ν δ (2 * eps * (1 + δ)) t‖ ≤
      ((N + 1 : ℕ) : ℝ) ^ 3 *
        Real.exp (-(driftRate (D * Real.exp θ) θ δ * (2 * eps * (1 - δ)))) +
      Real.exp (-(driftRate (D * Real.exp θ) θ (δ / 2) * δ / 2) * N) /
        (1 - Real.exp (-(driftRate (D * Real.exp θ) θ (δ / 2) * δ / 2))) := by
  obtain ⟨-, heps1, -, -, hfin, hT, -⟩ :=
    momClass_setup (regV_pos hvlo) heps (hν.momClass hθ hvlo)
  have heps0 : 0 < eps := by linarith
  have hδ0 : 0 < 1 + δ := by linarith
  have hp := hf.hasSum_cepsPositiveOccupation heps0 hδ0 hfin hT ht
  have hd := summable_norm_cepsDrawupOccupation_of_regLaw (l := 2 * eps * (1 + δ)) hν hθ hD hvlo hδ hf ht
  have htail := summable_cepsDrawupOK_tail_of_regLaw hν hθ hD hvlo hδ N hN
  have hprob : Summable (fun k => (iidLaw ν).real
      {g | cepsDrawupOK (1 + δ) 1 (2 * eps * (1 + δ)) g k}) :=
    (summable_nat_add_iff N).mp (by simpa only [Nat.add_comm] using htail.1)
  have hnorm : Summable (fun k => ‖cepsPositiveOccupationTerm ν eps δ t k -
      cepsDrawupOccupationTerm ν δ (2 * eps * (1 + δ)) t k‖) := hprob.of_nonneg_of_le (fun _ => norm_nonneg _)
    (hf.norm_positiveOccupation_sub_drawup_le_survival hδ0 ht)
  rw [← hp.tsum_eq, cepsDrawupOccupation, ← hp.summable.tsum_sub hd.of_norm]
  refine norm_tsum_le_cutoff hnorm N (Real.exp_pos _).le (fun k hk => ?_) ?_
  · refine (hf.norm_positiveOccupation_sub_drawup_le hδ0 ht k).trans
      ((measureReal_cepsReverseCross_of_regLaw hν hθ hD hvlo hδ heps0.le k).trans ?_)
    have hc := driftRate_pos hθ (show 0 < D * Real.exp θ by positivity) hδ
    have he : Real.exp (-(driftRate (D * Real.exp θ) θ δ * (2 * eps * (1 + δ)))) ≤
        Real.exp (-(driftRate (D * Real.exp θ) θ δ * (2 * eps * (1 - δ)))) := by
      rw [Real.exp_le_exp]
      apply neg_le_neg
      apply mul_le_mul_of_nonneg_left _ hc.le
      apply mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    exact mul_le_mul (by gcongr) he (Real.exp_pos _).le (sq_nonneg _)
  · exact ((hnorm.comp_injective (fun i j h => by omega)).tsum_le_tsum
      (fun k => hf.norm_positiveOccupation_sub_drawup_le_survival hδ0 ht (k + N))
      (by simpa only [Nat.add_comm] using htail.1)).trans
      (by simpa only [Nat.add_comm] using htail.2)

end

end PGM
