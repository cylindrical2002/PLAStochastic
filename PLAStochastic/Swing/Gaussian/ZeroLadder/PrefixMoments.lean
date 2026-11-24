import PLAStochastic.Swing.Gaussian.ZeroLadder.StoppedMoments

/-! # Genuine finite-prefix moments and independent minimum pieces -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal Topology Classical
namespace SwingRepair
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {X : ℕ → Ω → ℝ}

def ladderPrefixMoment (X : ℕ → Ω → ℝ) (n p : ℕ) : Ω → ℝ :=
  (ladderPositivePrefix X n).indicator (fun ω => (cumulativeSamples X n ω)^p)

theorem cumulativeSamples_measurable_prefix {n : ℕ}
    (hX : ∀ j < n, Measurable (X j)) : Measurable (cumulativeSamples X n) := by
  apply Finset.measurable_sum
  intro j hj
  exact hX j (Finset.mem_range.mp hj)

theorem ladderPositivePrefix_measurable {n : ℕ} (hX : ∀ j < n, Measurable (X j)) :
    MeasurableSet (ladderPositivePrefix X n) := by
  have he : ladderPositivePrefix X n = ⋂ j : ℕ, ⋂ (_ : 0 < j), ⋂ (_ : j ≤ n),
      {ω | 0 < cumulativeSamples X j ω} := by ext ω; simp [ladderPositivePrefix]
  rw [he]
  refine MeasurableSet.iInter fun j => MeasurableSet.iInter fun _ =>
    MeasurableSet.iInter fun hj => ?_
  exact measurableSet_lt measurable_const (cumulativeSamples_measurable_prefix
    (fun l hl => hX l (lt_of_lt_of_le hl hj)))

theorem ladderPrefixMoment_measurable {n : ℕ} (hX : ∀ j < n, Measurable (X j)) (p : ℕ) :
    Measurable (ladderPrefixMoment X n p) :=
  ((cumulativeSamples_measurable_prefix hX).pow_const p).indicator
    (ladderPositivePrefix_measurable hX)

theorem ladderPositivePrefix_eq_survives_ae (hX : ∀ n, Measurable (X n))
    (hi : iIndepFun X μ) (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) (n : ℕ) :
    ladderPositivePrefix X n =ᵐ[μ] gaussianHalfLineSurvives X 0 0 n := by
  filter_upwards [cumulativeSamples_distinct_ae hX hi hG] with ω hω
  apply propext
  change (∀ j, 0 < j → j ≤ n → 0 < cumulativeSamples X j ω) ↔
    ∀ j ≤ n, 0 ≤ gaussianDriftWalk X 0 0 j ω
  simp only [gaussianDriftWalk, zero_add, zero_mul, add_zero]
  constructor
  · intro h j hj
    by_cases hz : j = 0
    · simp [hz]
    · exact (h j (Nat.pos_of_ne_zero hz) hj).le
  · intro h j hj hjn
    exact lt_of_le_of_ne (h j hjn) (fun he => (Nat.ne_of_gt hj)
      (hω (by simpa only [cumulativeSamples_zero] using he.symm)))

theorem ladderPrefixMoment_integral_eq_setIntegral (hX : ∀ n, Measurable (X n))
    (hi : iIndepFun X μ) (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) (n p : ℕ) :
    (∫ ω, ladderPrefixMoment X n p ω ∂μ) =
      ∫ ω in gaussianHalfLineSurvives X 0 0 n, (cumulativeSamples X n ω)^p ∂μ := by
  rw [ladderPrefixMoment, integral_indicator (ladderPositivePrefix_measurable (fun j _ => hX j))]
  exact setIntegral_congr_set (ladderPositivePrefix_eq_survives_ae hX hi hG n)

theorem ladderPrefixMoment_integral_zero (hX : ∀ n, Measurable (X n))
    (hi : iIndepFun X μ) (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) (n : ℕ) :
    (∫ ω, ladderPrefixMoment X n 0 ω ∂μ) = gaussianLadderSurvivalProbability X μ n := by
  rw [ladderPrefixMoment_integral_eq_setIntegral hX hi hG]
  simp [gaussianLadderSurvivalProbability]

theorem ladderPrefixMoment_integral_one (hX : ∀ n, Measurable (X n))
    (hi : iIndepFun X μ) (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) (n : ℕ) :
    (∫ ω, ladderPrefixMoment X n 1 ω ∂μ) = gaussianLadderSurvivingFirstMoment X μ n := by
  simpa [gaussianLadderSurvivingFirstMoment] using
    ladderPrefixMoment_integral_eq_setIntegral hX hi hG n 1

theorem ladderPrefixMoment_integral_two (hX : ∀ n, Measurable (X n))
    (hi : iIndepFun X μ) (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) (n : ℕ) :
    (∫ ω, ladderPrefixMoment X n 2 ω ∂μ) = gaussianLadderSurvivingSecondMoment X μ n :=
  ladderPrefixMoment_integral_eq_setIntegral hX hi hG n 2

theorem ladderPrefixMoment_integrable (hX : ∀ n, Measurable (X n))
    (hi : iIndepFun X μ) (hG : ∀ n, μ.map (X n) = gaussianReal 0 1)
    (n : ℕ) {p : ℕ} (hp : p ≤ 2) : Integrable (ladderPrefixMoment X n p) μ := by
  let := hi.isProbabilityMeasure
  have hA := ladderPositivePrefix_measurable (fun j (_ : j < n) => hX j)
  interval_cases p
  · simpa [ladderPrefixMoment] using (integrable_const (1 : ℝ)).indicator hA
  · simpa [ladderPrefixMoment] using
      ((gaussianZeroWalk_memLp_two hX hi hG n).integrable (by norm_num)).indicator hA
  · exact (gaussianZeroWalk_memLp_two hX hi hG n).integrable_sq.indicator hA

/-- The equality is obtained from the actual iid path law. -/
theorem ladderPrefixMoment_integral_identical {Y : ℕ → Ω → ℝ}
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1)
    (hY : ∀ n, Measurable (Y n)) (hYi : iIndepFun Y μ)
    (hYG : ∀ n, μ.map (Y n) = gaussianReal 0 1) (n p : ℕ) :
    (∫ ω, ladderPrefixMoment Y n p ω ∂μ) = ∫ ω, ladderPrefixMoment X n p ω ∂μ := by
  let γ := Measure.infinitePi (fun _ : ℕ => gaussianReal 0 1)
  let F := ladderPrefixMoment (fun j (w : ℕ → ℝ) => w j) n p
  have hF : Measurable F := ladderPrefixMoment_measurable (fun j _ => measurable_pi_apply j) p
  have hLX : HasLaw (fun ω j => X j ω) γ μ := by
    refine ⟨(measurable_pi_lambda _ hX).aemeasurable, ?_⟩
    rw [hi.map_fun_eq_infinitePi_map hX]
    simp only [hG, γ]
  have hLY : HasLaw (fun ω j => Y j ω) γ μ := by
    refine ⟨(measurable_pi_lambda _ hY).aemeasurable, ?_⟩
    rw [hYi.map_fun_eq_infinitePi_map hY]
    simp only [hYG, γ]
  exact (hLY.integral_comp hF.aestronglyMeasurable).trans
    (hLX.integral_comp hF.aestronglyMeasurable).symm

omit [MeasurableSpace Ω] in
/-- Only the first k original increments determine the reversed-prefix statistic. -/
theorem ladderPrefixMoment_reverse_measurable (k p : ℕ) :
    Measurable[incrementIndexSpace X (Iio k)] (ladderPrefixMoment (ladderReverseNeg X k) k p) := by
  let : MeasurableSpace Ω := incrementIndexSpace X (Iio k)
  apply ladderPrefixMoment_measurable
  intro j hj
  change Measurable (fun ω => -X (ladderReverseIndex k j) ω)
  exact (incrementIndexSpace_eval (show ladderReverseIndex k j ∈ Iio k by
    simp only [ladderReverseIndex, if_pos hj, mem_Iio]; omega)).neg

omit [MeasurableSpace Ω] in
/-- Only the original increments at and after k determine the forward statistic. -/
theorem ladderPrefixMoment_shift_measurable (k n p : ℕ) :
    Measurable[incrementIndexSpace X (Ici k)] (ladderPrefixMoment (fun j => X (k+j)) n p) := by
  let : MeasurableSpace Ω := incrementIndexSpace X (Ici k)
  apply ladderPrefixMoment_measurable
  intro j _
  exact incrementIndexSpace_eval (show k+j ∈ Ici k by simp)

theorem ladderPrefixMoment_reverse_shift_indep (hX : ∀ n, Measurable (X n))
    (hi : iIndepFun X μ) (k n p r : ℕ) :
    IndepFun (ladderPrefixMoment (ladderReverseNeg X k) k p)
      (ladderPrefixMoment (fun j => X (k+j)) n r) μ := by
  have hd : Disjoint (Iio k) (Ici k) := disjoint_left.mpr (by intro j hj hj'; exact not_lt_of_ge (show k ≤ j from hj') (show j < k from hj))
  have hh := indep_iSup_of_disjoint (fun j => (hX j).comap_le) hi.iIndep hd
  exact indep_of_indep_of_le_right
    (indep_of_indep_of_le_left hh (ladderPrefixMoment_reverse_measurable k p).comap_le)
    (ladderPrefixMoment_shift_measurable k n r).comap_le

/-- All minimum-piece product moments factor into the original untransformed
prefix moments; independence is proved on disjoint original increment sets. -/
theorem ladderPrefixMoment_minimum_product_integral (hX : ∀ n, Measurable (X n))
    (hi : iIndepFun X μ) (hG : ∀ n, μ.map (X n) = gaussianReal 0 1)
    (k n p r : ℕ) :
    (∫ ω, ladderPrefixMoment (ladderReverseNeg X k) k p ω *
      ladderPrefixMoment (fun j => X (k+j)) n r ω ∂μ) =
      (∫ ω, ladderPrefixMoment X k p ω ∂μ) * (∫ ω, ladderPrefixMoment X n r ω ∂μ) := by
  obtain ⟨hY, hYi, hYG⟩ := ladderReverseNeg_gaussian hX hi hG k
  have hZi := hi.precomp (g := fun j => k+j) (by intro i j he; dsimp at he; omega)
  rw [(ladderPrefixMoment_reverse_shift_indep hX hi k n p r).integral_fun_mul_eq_mul_integral
    (ladderPrefixMoment_measurable (fun j _ => hY j) p).aestronglyMeasurable
    (ladderPrefixMoment_measurable (fun j _ => hX (k+j)) r).aestronglyMeasurable,
    ladderPrefixMoment_integral_identical hX hi hG hY hYi hYG,
    ladderPrefixMoment_integral_identical hX hi hG (fun j => hX (k+j)) hZi (fun j => hG (k+j))]

theorem ladderPrefixMoment_minimum_product_integrable (hX : ∀ n, Measurable (X n))
    (hi : iIndepFun X μ) (hG : ∀ n, μ.map (X n) = gaussianReal 0 1)
    (k n : ℕ) {p r : ℕ} (hp : p ≤ 2) (hr : r ≤ 2) :
    Integrable (fun ω => ladderPrefixMoment (ladderReverseNeg X k) k p ω *
      ladderPrefixMoment (fun j => X (k+j)) n r ω) μ := by
  obtain ⟨hY, hYi, hYG⟩ := ladderReverseNeg_gaussian hX hi hG k
  have hZi := hi.precomp (g := fun j => k+j) (by intro i j he; dsimp at he; omega)
  exact (ladderPrefixMoment_reverse_shift_indep hX hi k n p r).integrable_mul
    (ladderPrefixMoment_integrable hY hYi hYG k hp)
    (ladderPrefixMoment_integrable (fun j => hX (k+j)) hZi (fun j => hG (k+j)) n hr)

end SwingRepair
