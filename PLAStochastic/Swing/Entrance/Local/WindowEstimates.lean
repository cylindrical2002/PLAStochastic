import PLAStochastic.Swing.Entrance.Local.DriftWindow
import PLAStochastic.Swing.Gaussian.StripExit.Ballot
import PLAStochastic.Swing.Gaussian.ZeroLadder.StrictLadderLaw
import PLAStochastic.Swing.Repair.GeometricRejectionTail
import PLAStochastic.ForMathlib.Probability.StoppedSum.PastFiltration
import PLAStochastic.ForMathlib.Probability.StoppedSum.PredictableWeights

/-!
# Window estimates for the walk after the cut

For the zero-drift Gaussian walk `W = cumulativeSamples X`:

* (E11) ballot: `P(T_D > q) ≤ C_b (D + 1) / √q` for `D ≥ 0` (`zeroDrift_late_le`), and the
  event `{T_D > q}` grows with `D` (`zeroDrift_late_mono`);
* (E12) Kolmogorov: `P(max_{k ≤ q} |W_k| ≥ λ) ≤ q / λ²` (`zeroDrift_maximal_le`).

For the walk with a constant drift `-b`, the crossing pair is compared with the zero-drift pair
on the window: splitting at `{T ≤ q}`, the part read inside the window moves by the
Cameron–Martin bound (E10), and the late part is controlled by `P(T⁰_D > q)` plus the same
bound (`crossingPair_drift_le`, `driftLate_le`).
-/

namespace SwingRepair

noncomputable section

open MeasureTheory ProbabilityTheory Set

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {X : ℕ → Ω → ℝ}

/-! ## (E11) Ballot bound -/

omit [MeasurableSpace Ω] in
theorem zeroDrift_late_eq_survival (D : ℝ) (q : ℕ) :
    {ω | (q : ℕ∞) < zeroDriftCrossing X D ω} =
      gaussianSurvivalEvent (fun n ω => -X n ω) D 0 q := by
  ext ω
  have hneg : ∀ j, cumulativeSamples (fun n ω => -X n ω) j ω = -cumulativeSamples X j ω := by
    intro j
    simp [cumulativeSamples, Finset.sum_neg_distrib]
  simp only [mem_ofPred_eq, zeroDriftCrossing_eq, lt_levelCrossing_iff, gaussianSurvivalEvent,
    gaussianDriftWalk, hneg, Set.mem_Icc, zero_mul, add_zero]
  constructor
  · rintro h j ⟨hj1, hjq⟩
    linarith [h j hj1 hjq]
  · intro h j hj1 hjq
    linarith [h j ⟨hj1, hjq⟩]

omit [MeasurableSpace Ω] in
theorem zeroDrift_late_mono {D D' : ℝ} (hDD : D ≤ D') (q : ℕ) :
    {ω | (q : ℕ∞) < zeroDriftCrossing X D ω} ⊆ {ω | (q : ℕ∞) < zeroDriftCrossing X D' ω} := by
  intro ω h
  simp only [mem_ofPred_eq, zeroDriftCrossing_eq, lt_levelCrossing_iff] at h ⊢
  exact fun j hj hjq => (h j hj hjq).trans hDD

/-- (E11) The zero-drift walk stays below a level `D ≥ 0` up to time `q` with probability at
most `C_b (D + 1) / √q`. -/
theorem zeroDrift_late_le (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) {D : ℝ} (hD : 0 ≤ D) {q : ℕ} (hq : 0 < q) :
    μ.real {ω | (q : ℕ∞) < zeroDriftCrossing X D ω} ≤
      gaussianBallotConstant * (D + 1) * (Real.sqrt q)⁻¹ := by
  rw [zeroDrift_late_eq_survival]
  have h := gaussian_ballot_bound (X := fun n ω => -X n ω) (fun n => (hX n).neg)
    (hi.comp (fun _ x => -x) (fun _ => measurable_neg)) (gaussianIncrement_reflected_law hX hG)
    hD le_rfl (by norm_num) hq
  simpa only [zero_add] using h

/-! ## (E12) Kolmogorov bound -/

/-- (E12) Kolmogorov's maximal inequality for the zero-drift walk. -/
theorem zeroDrift_maximal_le (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) {lam : ℝ} (hlam : 0 < lam) (q : ℕ) :
    μ.real {ω | ∃ k ≤ q, lam ≤ |cumulativeSamples X k ω|} ≤ q / lam ^ 2 := by
  have := hi.isProbabilityMeasure
  have hinc := PGM.indepIncrements_pastFiltration hX hi 0
  have hmemX : ∀ t, MemLp (X t) 2 μ := by
    intro t
    have h := (memLp_map_measure_iff (g := id) aestronglyMeasurable_id (hX t).aemeasurable).mp
      (by rw [hG t]; exact memLp_id_gaussianReal' 2 (by norm_num))
    exact h
  have hY2 : ∀ t, MemLp (fun ω => X t ω - 0) 2 μ := fun t => by
    simpa only [sub_zero] using hmemX t
  have hY0 : ∀ t, ∫ ω, (X t ω - 0) ∂μ = 0 := by
    intro t
    simp only [sub_zero]
    have h := integral_map (μ := μ) (f := fun x : ℝ => x) (hX t).aemeasurable
      aestronglyMeasurable_id
    rw [hG t, integral_id_gaussianReal] at h
    exact h.symm
  have hsq1 : ∀ t, ∫ ω, X t ω ^ 2 ∂μ = 1 := by
    intro t
    rw [← integral_map (f := fun x : ℝ => x ^ 2) (hX t).aemeasurable
      (by fun_prop : Measurable fun x : ℝ => x ^ 2).aestronglyMeasurable, hG t]
    have hv := variance_of_integral_eq_zero (X := id) (μ := gaussianReal 0 1) aemeasurable_id
      integral_id_gaussianReal
    rw [variance_id_gaussianReal] at hv
    simpa using hv.symm
  have hK := PGM.kolmogorov_maximal hinc hY2 hY0 hlam q
  have hS : ∫ ω, PGM.partialSum (fun t ω => X t ω - 0) q ω ^ 2 ∂μ = q := by
    rw [PGM.partialSum_eq_weightedSum_one, PGM.integral_weightedSum_sq hinc
      (PGM.PredictableWeight.one _) hY2 hY0 q]
    simp [hsq1]
  have hps : ∀ k ω, PGM.partialSum (fun t ω => X t ω - 0) k ω = cumulativeSamples X k ω := by
    intro k ω
    simp [PGM.partialSum, cumulativeSamples]
  rw [hS] at hK
  simp only [hps] at hK
  rw [le_div_iff₀ (by positivity), mul_comm]
  exact hK

/-! ## Comparison of the drifted crossing pair with the zero-drift pair -/

/-- The crossing pair counted only when the crossing happens by time `q`. -/
def windowPairFunctional (g : ℝ × ℝ → ℝ) (D : ℝ) (q : ℕ) (x : ℕ → ℝ) : ℝ := by
  classical
  exact if levelCrossing (driftPath x 0) D ≤ (q : ℕ∞) then g (crossingPair D 0 x) else 0

/-- The indicator that no crossing happens by time `q`. -/
def windowLateFunctional (D : ℝ) (q : ℕ) (x : ℕ → ℝ) : ℝ := by
  classical
  exact if levelCrossing (driftPath x 0) D ≤ (q : ℕ∞) then 0 else 1

theorem measurable_crossingPair_fixed (D b : ℝ) : Measurable (crossingPair D b) := by
  have h := measurable_crossingPair.comp
    ((measurable_const (a := ((D, b) : ℝ × ℝ))).prodMk (measurable_id (α := ℕ → ℝ)))
  exact h

theorem measurable_levelCrossing_fixed (D b : ℝ) :
    Measurable fun x : ℕ → ℝ => levelCrossing (driftPath x b) D := by
  have h := measurable_levelCrossing_driftPath.comp
    ((measurable_const (a := ((D, b) : ℝ × ℝ))).prodMk (measurable_id (α := ℕ → ℝ)))
  exact h

theorem measurableSet_crossing_le (D b : ℝ) (q : ℕ) :
    MeasurableSet {x : ℕ → ℝ | levelCrossing (driftPath x b) D ≤ (q : ℕ∞)} :=
  measurable_levelCrossing_fixed D b (MeasurableSet.of_discrete)

theorem measurable_windowPairFunctional {g : ℝ × ℝ → ℝ} (hg : Measurable g) (D : ℝ) (q : ℕ) :
    Measurable (windowPairFunctional g D q) := by
  unfold windowPairFunctional
  exact Measurable.ite (measurableSet_crossing_le D 0 q)
    (hg.comp (measurable_crossingPair_fixed D 0)) measurable_const

theorem measurable_windowLateFunctional (D : ℝ) (q : ℕ) :
    Measurable (windowLateFunctional D q) := by
  unfold windowLateFunctional
  exact Measurable.ite (measurableSet_crossing_le D 0 q) measurable_const measurable_const

theorem windowPairFunctional_local (g : ℝ × ℝ → ℝ) (D : ℝ) (q : ℕ) (x x' : ℕ → ℝ)
    (hxx : ∀ i < q, x i = x' i) :
    windowPairFunctional g D q x = windowPairFunctional g D q x' := by
  have hw := driftPath_eq_of_window hxx 0
  unfold windowPairFunctional
  by_cases hT : levelCrossing (driftPath x 0) D ≤ (q : ℕ∞)
  · have hT' := (levelCrossing_le_congr hw D).mp hT
    rw [if_pos hT, if_pos hT']
    obtain ⟨h1, h2⟩ := crossing_functionals_eq_of_window hw hT
    simp only [crossingPair, h1, h2]
  · have hT' : ¬ levelCrossing (driftPath x' 0) D ≤ (q : ℕ∞) :=
      fun h => hT ((levelCrossing_le_congr hw D).mpr h)
    rw [if_neg hT, if_neg hT']

theorem windowLateFunctional_local (D : ℝ) (q : ℕ) (x x' : ℕ → ℝ)
    (hxx : ∀ i < q, x i = x' i) :
    windowLateFunctional D q x = windowLateFunctional D q x' := by
  have hw := driftPath_eq_of_window hxx 0
  unfold windowLateFunctional
  by_cases hT : levelCrossing (driftPath x 0) D ≤ (q : ℕ∞)
  · rw [if_pos hT, if_pos ((levelCrossing_le_congr hw D).mp hT)]
  · have hT' : ¬ levelCrossing (driftPath x' 0) D ≤ (q : ℕ∞) :=
      fun h => hT ((levelCrossing_le_congr hw D).mpr h)
    rw [if_neg hT, if_neg hT']

theorem crossingPair_split (g : ℝ × ℝ → ℝ) (D : ℝ) (q : ℕ) (x : ℕ → ℝ) :
    g (crossingPair D 0 x) =
      windowPairFunctional g D q x + windowLateFunctional D q x * g (crossingPair D 0 x) := by
  unfold windowPairFunctional windowLateFunctional
  split_ifs <;> ring

theorem windowLateFunctional_nonneg (D : ℝ) (q : ℕ) (x : ℕ → ℝ) :
    0 ≤ windowLateFunctional D q x := by
  unfold windowLateFunctional
  split_ifs <;> norm_num

theorem abs_windowLateFunctional_le (D : ℝ) (q : ℕ) (x : ℕ → ℝ) :
    |windowLateFunctional D q x| ≤ 1 := by
  unfold windowLateFunctional
  split_ifs <;> norm_num

theorem abs_windowPairFunctional_le {g : ℝ × ℝ → ℝ} {C : ℝ} (hC : ∀ p, |g p| ≤ C)
    (D : ℝ) (q : ℕ) (x : ℕ → ℝ) : |windowPairFunctional g D q x| ≤ C := by
  have hC0 : 0 ≤ C := (abs_nonneg _).trans (hC 0)
  unfold windowPairFunctional
  split_ifs
  · exact hC _
  · simpa using hC0

theorem windowLateFunctional_sub (D b : ℝ) (q : ℕ) (x : ℕ → ℝ) :
    windowLateFunctional D q (fun i => x i - b) =
      if (q : ℕ∞) < levelCrossing (driftPath x b) D then 1 else 0 := by
  unfold windowLateFunctional
  rw [← driftPath_sub x b]
  by_cases hT : levelCrossing (driftPath x b) D ≤ (q : ℕ∞)
  · rw [if_pos hT, if_neg (not_lt.mpr hT)]
  · rw [if_neg hT, if_pos (not_le.mp hT)]

/-- The late probability of the drifted walk as an integral. -/
theorem integral_windowLate_eq (hX : ∀ n, Measurable (X n))
    (D b : ℝ) (q : ℕ) :
    ∫ ω, windowLateFunctional D q (fun i => X i ω - b) ∂μ =
      μ.real {ω | (q : ℕ∞) < levelCrossing (driftPath (fun i => X i ω) b) D} := by
  have hset : MeasurableSet {ω | (q : ℕ∞) < levelCrossing (driftPath (fun i => X i ω) b) D} := by
    have hm := (measurable_levelCrossing_fixed D b).comp (measurable_pi_lambda _ hX)
    have := hm (MeasurableSet.of_discrete (s := {t : ℕ∞ | (q : ℕ∞) < t}))
    exact this
  rw [← integral_indicator_one hset]
  congr 1
  funext ω
  rw [windowLateFunctional_sub]
  by_cases hω : (q : ℕ∞) < levelCrossing (driftPath (fun i => X i ω) b) D
  · rw [if_pos hω, indicator_of_mem (show ω ∈ _ from hω)]
    rfl
  · rw [if_neg hω, indicator_of_notMem (show ω ∉ _ from hω)]

variable (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
  (hG : ∀ n, μ.map (X n) = gaussianReal 0 1)
include hX hi hG

/-- A drift `-b` raises the probability of no crossing by time `q` by at most the window
error of (E10). -/
theorem driftLate_le (D b : ℝ) (q : ℕ) :
    μ.real {ω | (q : ℕ∞) < levelCrossing (driftPath (fun i => X i ω) b) D} ≤
      μ.real {ω | (q : ℕ∞) < zeroDriftCrossing X D ω} +
        (2 * |b| * q * gaussianAbsMean + q * b ^ 2) := by
  have := hi.isProbabilityMeasure
  have h := drift_window_bound hX hi hG (measurable_windowLateFunctional D q)
    (abs_windowLateFunctional_le D q) (windowLateFunctional_local D q) b
  rw [integral_windowLate_eq hX D b q] at h
  have h0 := integral_windowLate_eq hX D 0 q (μ := μ)
  simp only [sub_zero] at h0
  rw [h0] at h
  have hz : {ω | (q : ℕ∞) < levelCrossing (driftPath (fun i => X i ω) 0) D} =
      {ω | (q : ℕ∞) < zeroDriftCrossing X D ω} := by
    ext ω
    simp only [mem_ofPred_eq, zeroDriftCrossing_eq, driftPath_zero_cumulative]
  rw [hz] at h
  have := le_abs_self (μ.real {ω | (q : ℕ∞) < levelCrossing (driftPath (fun i => X i ω) b) D} -
    μ.real {ω | (q : ℕ∞) < zeroDriftCrossing X D ω})
  linarith

/-- (E10)+(E11) The drifted crossing pair and the zero-drift pair have expectations within
`2C (window error + P(T⁰_D > q))` for every bounded measurable test function. -/
theorem crossingPair_drift_le {g : ℝ × ℝ → ℝ} (hg : Measurable g) {C : ℝ}
    (hC : ∀ p, |g p| ≤ C) (D b : ℝ) (q : ℕ) :
    |∫ ω, g (crossingPair D b (fun i => X i ω)) ∂μ -
        ∫ ω, g (zeroDriftUndershoot X D ω, zeroDriftOvershoot X D ω) ∂μ| ≤
      2 * C * ((2 * |b| * q * gaussianAbsMean + q * b ^ 2) +
        μ.real {ω | (q : ℕ∞) < zeroDriftCrossing X D ω}) := by
  have := hi.isProbabilityMeasure
  have hC0 : 0 ≤ C := (abs_nonneg _).trans (hC 0)
  set err := 2 * |b| * q * gaussianAbsMean + q * b ^ 2
  set P0 := μ.real {ω | (q : ℕ∞) < zeroDriftCrossing X D ω}
  have hseq : Measurable fun ω (i : ℕ) => X i ω := measurable_pi_lambda _ hX
  have hseqb : Measurable fun ω (i : ℕ) => X i ω - b :=
    measurable_pi_lambda _ fun i => (hX i).sub_const b
  have hWm := measurable_windowPairFunctional hg D q
  have hLm := measurable_windowLateFunctional D q
  have hgp := hg.comp (measurable_crossingPair_fixed D 0)
  -- integrability of the pieces
  have hbdd : ∀ {F : Ω → ℝ} (_ : Measurable F) (B : ℝ) (_ : ∀ ω, |F ω| ≤ B), Integrable F μ :=
    fun hF B hB => Integrable.of_bound hF.aestronglyMeasurable B
      (ae_of_all _ fun ω => by rw [Real.norm_eq_abs]; exact hB ω)
  have hLg : ∀ y : Ω → ℕ → ℝ, Measurable y →
      |∫ ω, windowLateFunctional D q (y ω) * g (crossingPair D 0 (y ω)) ∂μ| ≤
        C * ∫ ω, windowLateFunctional D q (y ω) ∂μ := by
    intro y hy
    have hLi : Integrable (fun ω => windowLateFunctional D q (y ω)) μ :=
      hbdd (hLm.comp hy) 1 fun ω => abs_windowLateFunctional_le D q _
    calc |∫ ω, windowLateFunctional D q (y ω) * g (crossingPair D 0 (y ω)) ∂μ|
        ≤ ∫ ω, |windowLateFunctional D q (y ω) * g (crossingPair D 0 (y ω))| ∂μ :=
          abs_integral_le_integral_abs
      _ ≤ ∫ ω, C * windowLateFunctional D q (y ω) ∂μ := by
          refine integral_mono_of_nonneg (ae_of_all _ fun ω => abs_nonneg _)
            (hLi.const_mul C) (ae_of_all _ fun ω => ?_)
          dsimp only
          rw [abs_mul, abs_of_nonneg (windowLateFunctional_nonneg D q _), mul_comm]
          exact mul_le_mul_of_nonneg_right (hC _) (windowLateFunctional_nonneg D q _)
      _ = C * ∫ ω, windowLateFunctional D q (y ω) ∂μ := integral_const_mul _ _
  have hsplit : ∀ y : Ω → ℕ → ℝ, Measurable y →
      ∫ ω, g (crossingPair D 0 (y ω)) ∂μ =
        ∫ ω, windowPairFunctional g D q (y ω) ∂μ +
          ∫ ω, windowLateFunctional D q (y ω) * g (crossingPair D 0 (y ω)) ∂μ := by
    intro y hy
    rw [integral_congr_ae (ae_of_all _ fun ω => crossingPair_split g D q (y ω))]
    refine integral_add (hbdd (hWm.comp hy) C fun ω => abs_windowPairFunctional_le hC D q _)
      (hbdd ((hLm.comp hy).mul (hgp.comp hy)) C fun ω => ?_)
    rw [abs_mul]
    calc |windowLateFunctional D q (y ω)| * |g (crossingPair D 0 (y ω))| ≤ 1 * C :=
          mul_le_mul (abs_windowLateFunctional_le D q _) (hC _) (abs_nonneg _) zero_le_one
      _ = C := one_mul C
  have hW := drift_window_bound hX hi hG hWm (abs_windowPairFunctional_le hC D q)
    (windowPairFunctional_local g D q) b
  have hLb := driftLate_le hX hi hG D b q
  have hL0 : ∫ ω, windowLateFunctional D q (fun i => X i ω) ∂μ = P0 := by
    have h0 := integral_windowLate_eq hX D 0 q (μ := μ)
    simp only [sub_zero] at h0
    rw [h0]
    congr 1
    ext ω
    simp only [mem_ofPred_eq, zeroDriftCrossing_eq, driftPath_zero_cumulative]
  have hLb' : ∫ ω, windowLateFunctional D q (fun i => X i ω - b) ∂μ ≤ P0 + err := by
    rw [integral_windowLate_eq hX D b q]
    exact hLb
  have e1 : ∫ ω, g (crossingPair D b (fun i => X i ω)) ∂μ =
      ∫ ω, g (crossingPair D 0 (fun i => X i ω - b)) ∂μ := by
    simp_rw [crossingPair_sub D b]
  have e2 : ∫ ω, g (zeroDriftUndershoot X D ω, zeroDriftOvershoot X D ω) ∂μ =
      ∫ ω, g (crossingPair D 0 (fun i => X i ω)) ∂μ := by
    simp_rw [crossingPair_zero_eq]
  rw [e1, e2, hsplit _ hseqb, hsplit _ hseq]
  have hA := hLg _ hseqb
  have hB := hLg _ hseq
  rw [hL0] at hB
  have hW' := abs_sub_le_iff.mp hW
  have hA' := abs_le.mp hA
  have hB' := abs_le.mp hB
  have hCL := mul_le_mul_of_nonneg_left hLb' hC0
  rw [abs_le]
  constructor <;> nlinarith

end

end SwingRepair
