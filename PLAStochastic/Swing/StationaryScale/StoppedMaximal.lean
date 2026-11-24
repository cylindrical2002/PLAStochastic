import PLAStochastic.Swing.StationaryScale.GuardedWalkSquare

/-! # A stopped maximal bound for the actual restart walk

Guarding the walk by "still alive and not yet past the level" turns Wald's
second-moment identity into the maximal estimate
`P(max_{j≤N}|W_j| > λ) ≤ E[N]/λ²` used in Appendix `app:margins`.
-/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology Classical
namespace SwingRepair
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} {X : ℕ → Ω → ℝ}

/-- Alive at index `k` and not yet past the level. -/
def restartMaxGuard (X : ℕ → Ω → ℝ) (E x lam : ℝ) (k : ℕ) : Set Ω :=
  {ω | ((k+1 : ℕ) : WithTop ℕ) ≤ nativeRestartLength X E x ω} ∩
    {ω | ∀ j ≤ k, |cumulativeSamples X j ω| ≤ lam}

omit mΩ in
theorem restartMaxGuard_measurable (X : ℕ → Ω → ℝ) (E x lam : ℝ) (k : ℕ) :
    MeasurableSet[incrementIndexSpace X (Iio k)] (restartMaxGuard X E x lam k) := by
  let : MeasurableSpace Ω := incrementIndexSpace X (Iio k)
  refine MeasurableSet.inter (measurableSet_nativeRestartLength_ge_history X E x k) ?_
  have hW : ∀ j ≤ k, Measurable (cumulativeSamples X j) := by
    intro j hj
    apply Finset.measurable_sum
    intro m hm
    exact incrementIndexSpace_eval (X := X)
      (show m ∈ Set.Iio k from Set.mem_Iio.mpr (by
        have := Finset.mem_range.mp hm
        omega))
  have hset : {ω | ∀ j ≤ k, |cumulativeSamples X j ω| ≤ lam} =
      ⋂ j ∈ Finset.Iic k, {ω | |cumulativeSamples X j ω| ≤ lam} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_iInter, Finset.mem_Iic]
  rw [hset]
  refine MeasurableSet.biInter (Finset.Iic k).countable_toSet (fun j hj => ?_)
  have hjk : j ≤ k := Finset.mem_Iic.mp (by simpa using hj)
  exact measurableSet_le (hW j hjk).abs measurable_const

omit mΩ in
/-- On the first exit the guarded walk freezes at the exit position. -/
theorem guardedWalk_eq_at_first_exit (X : ℕ → Ω → ℝ) (E x lam : ℝ) {n j₀ : ℕ} {ω : Ω}
    (hjn : j₀ ≤ n) (hjN : ((j₀ : ℕ) : WithTop ℕ) ≤ nativeRestartLength X E x ω)
    (hexit : lam < |cumulativeSamples X j₀ ω|)
    (hfirst : ∀ j < j₀, |cumulativeSamples X j ω| ≤ lam) :
    guardedWalk X (restartMaxGuard X E x lam) n ω = cumulativeSamples X j₀ ω := by
  have hsplit : ∀ k ∈ Finset.range n,
      (restartMaxGuard X E x lam k).indicator (fun ω' => X k ω') ω =
        if k < j₀ then X k ω else 0 := by
    intro k hk
    by_cases hkj : k < j₀
    · have hmem : ω ∈ restartMaxGuard X E x lam k := by
        refine ⟨?_, ?_⟩
        · refine le_trans ?_ hjN
          exact WithTop.coe_le_coe.mpr (by omega : k+1 ≤ j₀)
        · intro j hj
          exact hfirst j (by omega)
      rw [Set.indicator_of_mem hmem, if_pos hkj]
    · have hnot : ω ∉ restartMaxGuard X E x lam k := by
        rintro ⟨-, hg⟩
        exact absurd (hg j₀ (by omega)) (by linarith)
      rw [Set.indicator_of_notMem hnot, if_neg hkj]
  rw [guardedWalk, Finset.sum_congr rfl hsplit]
  have hsub : Finset.range j₀ ⊆ Finset.range n := fun k hk =>
    Finset.mem_range.mpr (lt_of_lt_of_le (Finset.mem_range.mp hk) hjn)
  have hzero : ∀ k ∈ Finset.range n, k ∉ Finset.range j₀ →
      (if k < j₀ then X k ω else 0) = 0 := by
    intro k _ hk'
    exact if_neg (by simpa using hk')
  rw [← Finset.sum_subset hsub hzero,
    Finset.sum_congr rfl (fun k hk => if_pos (Finset.mem_range.mp hk))]
  rfl

omit mΩ in
theorem restartMaxGuard_antitone (X : ℕ → Ω → ℝ) (E x lam : ℝ) {k n : ℕ} (hkn : k ≤ n) :
    restartMaxGuard X E x lam n ⊆ restartMaxGuard X E x lam k := by
  rintro ω ⟨halive, hguard⟩
  have halive' : ((n+1 : ℕ) : WithTop ℕ) ≤ nativeRestartLength X E x ω := halive
  refine ⟨?_, fun j hj => hguard j (by omega)⟩
  show ((k+1 : ℕ) : WithTop ℕ) ≤ nativeRestartLength X E x ω
  exact le_trans (WithTop.coe_le_coe.mpr (by omega : k+1 ≤ n+1)) halive' 

omit mΩ in
/-- While the guard still holds the guarded walk is the genuine walk. -/
theorem guardedWalk_eq_of_mem_guard (X : ℕ → Ω → ℝ) (E x lam : ℝ) {n : ℕ} {ω : Ω}
    (hω : ω ∈ restartMaxGuard X E x lam n) :
    guardedWalk X (restartMaxGuard X E x lam) n ω = cumulativeSamples X n ω := by
  have hsplit : ∀ k ∈ Finset.range n,
      (restartMaxGuard X E x lam k).indicator (fun ω' => X k ω') ω = X k ω := by
    intro k hk
    have hkn : k ≤ n := le_of_lt (Finset.mem_range.mp hk)
    exact Set.indicator_of_mem (restartMaxGuard_antitone X E x lam hkn hω) _
  rw [guardedWalk, Finset.sum_congr rfl hsplit]
  rfl

omit mΩ in
/-- The level-crossing events of the guarded walk increase. -/
theorem restartMax_exit_monotone (X : ℕ → Ω → ℝ) (E x lam : ℝ) :
    Monotone (fun n => {ω | lam < |guardedWalk X (restartMaxGuard X E x lam) n ω|}) := by
  have hstep : ∀ n, {ω | lam < |guardedWalk X (restartMaxGuard X E x lam) n ω|} ⊆
      {ω | lam < |guardedWalk X (restartMaxGuard X E x lam) (n+1) ω|} := by
    intro n ω hω
    have hω' : lam < |guardedWalk X (restartMaxGuard X E x lam) n ω| := hω
    have hnot : ω ∉ restartMaxGuard X E x lam n := by
      intro hmem
      rw [guardedWalk_eq_of_mem_guard X E x lam hmem] at hω'
      exact absurd (hmem.2 n le_rfl) (by linarith)
    show lam < |guardedWalk X (restartMaxGuard X E x lam) (n+1) ω|
    rw [guardedWalk_succ, Set.indicator_of_notMem hnot, add_zero]
    exact hω'
  exact monotone_nat_of_le_succ hstep

/-- Chebyshev applied to the guarded walk. -/
theorem measureReal_guardedWalk_exit_le
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1)
    {S : ℕ → Set Ω} (hS : ∀ k, MeasurableSet[incrementIndexSpace X (Iio k)] (S k))
    {lam : ℝ} (hlam : 0 < lam) (n : ℕ) :
    lam^2*μ.real {ω | lam < |guardedWalk X S n ω|} ≤ ∑ k ∈ Finset.range n, μ.real (S k) := by
  let : IsProbabilityMeasure μ := hi.isProbabilityMeasure
  have hSamb : ∀ k, MeasurableSet (S k) := fun k => (incrementIndexSpace_le hX (Iio k)) _ (hS k)
  have hgm : Measurable (guardedWalk X S n) :=
    (guardedWalk_measurable_history hS n).mono (incrementIndexSpace_le hX _) le_rfl
  set A : Set Ω := {ω | lam < |guardedWalk X S n ω|} with hA
  have hAm : MeasurableSet A := measurableSet_lt measurable_const hgm.abs
  have hgsq : Integrable (fun ω => (guardedWalk X S n ω)^2) μ :=
    (memLp_guardedWalk hX hG hSamb n).integrable_sq
  have hdom : ∀ ω, A.indicator (fun _ => lam^2) ω ≤ (guardedWalk X S n ω)^2 := by
    intro ω
    by_cases hω : ω ∈ A
    · rw [Set.indicator_of_mem hω]
      have h : lam < |guardedWalk X S n ω| := hω
      nlinarith [sq_abs (guardedWalk X S n ω), abs_nonneg (guardedWalk X S n ω)]
    · rw [Set.indicator_of_notMem hω]
      exact sq_nonneg _
  have hmono := integral_mono ((integrable_const (lam^2)).indicator hAm) hgsq hdom
  rw [integral_indicator_const _ hAm, smul_eq_mul, mul_comm] at hmono
  rw [integral_guardedWalk_sq hX hi hG hS n] at hmono
  exact hmono

/-- The stopped maximal estimate: the actual restart walk stays below any level
except with probability `E[N]/λ²`. -/
theorem measureReal_restart_maximum_le
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) {E : ℝ} (hE : 0 < E) (x : ℝ)
    {lam : ℝ} (hlam : 0 < lam) :
    μ.real {ω | ∃ j, ((j : ℕ) : WithTop ℕ) ≤ nativeRestartLength X E x ω ∧
      lam < |cumulativeSamples X j ω|} ≤ nativeRestartMean X μ E x/lam^2 := by
  let : IsProbabilityMeasure μ := hi.isProbabilityMeasure
  set S : ℕ → Set Ω := restartMaxGuard X E x lam with hSdef
  have hS : ∀ k, MeasurableSet[incrementIndexSpace X (Iio k)] (S k) :=
    fun k => restartMaxGuard_measurable X E x lam k
  set A : ℕ → Set Ω := fun n => {ω | lam < |guardedWalk X S n ω|} with hAdef
  have hmean : 0 ≤ nativeRestartMean X μ E x := by
    have hb := nativeRestartMean_bounds hX hi hG hE x
    linarith [hb.1]
  have hNint := nativeRestartLengthNat_integrable hX hi hG hE x
  have hNmeas : Measurable (nativeRestartLengthNat X E x) :=
    nativeRestartLengthNat_measurable X hX E |>.comp
      ((measurable_const (a := x)).prodMk measurable_id)
  have hguardsum : ∀ n, (∑ k ∈ Finset.range n, μ.real (S k)) ≤ nativeRestartMean X μ E x := by
    intro n
    refine le_trans (Finset.sum_le_sum (fun k _ => ?_))
      (sum_tail_le_integral_natCast (μ := μ) hNmeas hNint n)
    have hsub : S k ⊆ {ω | ((k+1 : ℕ) : WithTop ℕ) ≤ nativeRestartLength X E x ω} :=
      fun ω hω => hω.1
    have heq : μ.real {ω | ((k+1 : ℕ) : WithTop ℕ) ≤ nativeRestartLength X E x ω} =
        μ.real {ω | k < nativeRestartLengthNat X E x ω} := by
      unfold Measure.real
      rw [measure_nativeRestart_survival_eq hX hi hG hE x k]
    exact le_of_le_of_eq (measureReal_mono hsub) heq
  have hbound : ∀ n, μ.real (A n) ≤ nativeRestartMean X μ E x/lam^2 := by
    intro n
    have hc := measureReal_guardedWalk_exit_le hX hi hG hS hlam n
    rw [le_div_iff₀ (by positivity : (0 : ℝ) < lam^2)]
    calc
      μ.real (A n)*lam^2 = lam^2*μ.real (A n) := by ring
      _ ≤ ∑ k ∈ Finset.range n, μ.real (S k) := hc
      _ ≤ nativeRestartMean X μ E x := hguardsum n
  have hcover : {ω | ∃ j, ((j : ℕ) : WithTop ℕ) ≤ nativeRestartLength X E x ω ∧
      lam < |cumulativeSamples X j ω|} ⊆ ⋃ n, A n := by
    intro ω hω
    obtain ⟨j, hjL, hjexit⟩ := hω
    have hex : ∃ i, lam < |cumulativeSamples X i ω| := ⟨j, hjexit⟩
    set j₀ : ℕ := Nat.find hex with hj₀
    have hj₀exit : lam < |cumulativeSamples X j₀ ω| := Nat.find_spec hex
    have hj₀min : ∀ i < j₀, |cumulativeSamples X i ω| ≤ lam := by
      intro i hi
      exact le_of_not_gt (Nat.find_min hex hi)
    have hj₀le : j₀ ≤ j := Nat.find_le hjexit
    have hj₀L : ((j₀ : ℕ) : WithTop ℕ) ≤ nativeRestartLength X E x ω :=
      le_trans (WithTop.coe_le_coe.mpr hj₀le) hjL
    refine mem_iUnion.mpr ⟨j₀, ?_⟩
    show lam < |guardedWalk X S j₀ ω|
    rw [hSdef, guardedWalk_eq_at_first_exit X E x lam le_rfl hj₀L hj₀exit hj₀min]
    exact hj₀exit
  have hmono : μ (⋃ n, A n) ≤ ENNReal.ofReal (nativeRestartMean X μ E x/lam^2) := by
    rw [(restartMax_exit_monotone X E x lam).measure_iUnion]
    refine iSup_le fun n => ?_
    calc
      μ (A n) = ENNReal.ofReal (μ.real (A n)) := (ENNReal.ofReal_toReal (measure_ne_top _ _)).symm
      _ ≤ _ := ENNReal.ofReal_le_ofReal (hbound n)
  have hfinal := (measure_mono hcover).trans hmono
  have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top hfinal
  rwa [ENNReal.toReal_ofReal (by positivity)] at h

end SwingRepair
