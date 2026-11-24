import PLAStochastic.Swing.Restart.MaximalPrefix.HistoryIndependence
import Mathlib.Probability.Process.HittingTime

/-! Actual drifted Gaussian walks and their first exit from a closed finite strip. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal Topology
namespace SwingRepair
set_option backward.isDefEq.respectTransparency false

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {X : ℕ → Ω → ℝ}

def gaussianDriftWalk (X : ℕ → Ω → ℝ) (x a : ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  x + cumulativeSamples X n ω + a * (n : ℝ)

def gaussianStripExit (X : ℕ → Ω → ℝ) (x a R : ℝ) : Ω → WithTop ℕ :=
  hittingAfter (gaussianDriftWalk X x a) (Icc (0 : ℝ) R)ᶜ 0

/-- Time n reveals exactly increments with indices strictly below n. -/
def gaussianWalkFiltration (X : ℕ → Ω → ℝ) (hX : ∀ n, Measurable (X n)) :
    Filtration ℕ mΩ where
  seq := fun n => incrementIndexSpace X (Iio n)
  mono' := fun _ _ hij => incrementIndexSpace_mono (Iio_subset_Iio hij)
  le' := fun n => incrementIndexSpace_le hX (Iio n)

omit mΩ in
@[simp] theorem gaussianDriftWalk_zero (X : ℕ → Ω → ℝ) (x a : ℝ) (ω : Ω) :
    gaussianDriftWalk X x a 0 ω = x := by simp [gaussianDriftWalk]

omit mΩ in
theorem gaussianDriftWalk_succ (X : ℕ → Ω → ℝ) (x a : ℝ) (n : ℕ) (ω : Ω) :
    gaussianDriftWalk X x a (n + 1) ω = gaussianDriftWalk X x a n ω + X n ω + a := by
  simp only [gaussianDriftWalk, cumulativeSamples_succ, Nat.cast_add, Nat.cast_one]
  ring

omit mΩ in
theorem gaussianDriftWalk_measurable_past (X : ℕ → Ω → ℝ) (x a : ℝ) (n : ℕ) :
    Measurable[incrementIndexSpace X (Iio n)] (gaussianDriftWalk X x a n) := by
  let : MeasurableSpace Ω := incrementIndexSpace X (Iio n)
  unfold gaussianDriftWalk cumulativeSamples
  apply Measurable.add_const
  apply Measurable.const_add
  exact Finset.measurable_sum _ (fun k hk => incrementIndexSpace_eval (Finset.mem_range.mp hk))

theorem gaussianDriftWalk_adapted (hX : ∀ n, Measurable (X n)) (x a : ℝ) :
    Adapted (gaussianWalkFiltration X hX) (gaussianDriftWalk X x a) :=
  gaussianDriftWalk_measurable_past X x a

theorem gaussianStripExit_isStoppingTime (hX : ∀ n, Measurable (X n)) (x a R : ℝ) :
    IsStoppingTime (gaussianWalkFiltration X hX) (gaussianStripExit X x a R) :=
  (gaussianDriftWalk_adapted hX x a).isStoppingTime_hittingAfter measurableSet_Icc.compl

/-- Before the next tested increment, the complete previous trajectory stays in the strip. -/
def gaussianStripSurvives (X : ℕ → Ω → ℝ) (x a R : ℝ) (n : ℕ) : Set Ω :=
  {ω | ∀ j ≤ n, gaussianDriftWalk X x a j ω ∈ Icc (0 : ℝ) R}

omit mΩ in
theorem gaussianStripSurvives_measurable_past (X : ℕ → Ω → ℝ) (x a R : ℝ) (n : ℕ) :
    MeasurableSet[incrementIndexSpace X (Iio n)] (gaussianStripSurvives X x a R n) := by
  unfold gaussianStripSurvives
  simp only [ofPred_forall]
  apply MeasurableSet.iInter
  intro j
  apply MeasurableSet.iInter
  intro hj
  exact ((gaussianDriftWalk_measurable_past X x a j).mono
    (incrementIndexSpace_mono (Iio_subset_Iio hj)) le_rfl) measurableSet_Icc

omit mΩ in
theorem lt_gaussianStripExit_iff (X : ℕ → Ω → ℝ) (x a R : ℝ) (n : ℕ) (ω : Ω) :
    (n : WithTop ℕ) < gaussianStripExit X x a R ω ↔ ω ∈ gaussianStripSurvives X x a R n := by
  constructor
  · intro hn j hj
    have hjc : (j : WithTop ℕ) ≤ n := by exact_mod_cast hj
    exact not_not.mp (notMem_of_lt_hittingAfter (hjc.trans_lt hn) (Nat.zero_le j))
  · intro hs
    apply lt_of_not_ge
    intro hl
    obtain ⟨j, hj, ho⟩ := hittingAfter_le_iff.mp hl
    exact ho (hs j hj.2)

omit mΩ in
theorem gaussianStripExit_eq_succ_iff (X : ℕ → Ω → ℝ) (x a R : ℝ) (n : ℕ) (ω : Ω) :
    gaussianStripExit X x a R ω = (n + 1 : ℕ) ↔
      ω ∈ gaussianStripSurvives X x a R n ∧ gaussianDriftWalk X x a (n + 1) ω ∉ Icc (0 : ℝ) R := by
  constructor
  · intro he
    refine ⟨(lt_gaussianStripExit_iff X x a R n ω).mp (by rw [he]; exact_mod_cast Nat.lt_succ_self n), ?_⟩
    have hh := hittingAfter_mem_set_of_ne_top (u := gaussianDriftWalk X x a)
      (s := (Icc (0 : ℝ) R)ᶜ) (n := 0) (ω := ω)
      (show gaussianStripExit X x a R ω ≠ ⊤ by rw [he]; exact WithTop.coe_ne_top)
    change gaussianDriftWalk X x a (gaussianStripExit X x a R ω).untopA ω ∈ (Icc (0 : ℝ) R)ᶜ at hh
    rw [he] at hh
    exact hh
  · rintro ⟨hs, ho⟩
    have hl := (lt_gaussianStripExit_iff X x a R n ω).mpr hs
    have hu : gaussianStripExit X x a R ω ≤ (n + 1 : ℕ) :=
      hittingAfter_le_of_mem (Nat.zero_le _) ho
    have hf : gaussianStripExit X x a R ω ≠ ⊤ := ne_top_of_le_ne_top WithTop.coe_ne_top hu
    lift gaussianStripExit X x a R ω to ℕ using hf with m hm
    have hl' : n < m := WithTop.coe_lt_coe.mp hl
    have hu' : m ≤ n + 1 := WithTop.coe_le_coe.mp hu
    have he : m = n + 1 := by omega
    exact congrArg (fun k : ℕ => (k : WithTop ℕ)) he

/-- The current increment is independent of precisely the history strictly before it. -/
theorem currentIncrement_indep_past {μ : Measure Ω}
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ) (n : ℕ) :
    Indep (MeasurableSpace.comap (X n) inferInstance) (incrementIndexSpace X (Iio n)) μ := by
  have hd : Disjoint ({n} : Set ℕ) (Iio n) := by simp
  have hh := indep_iSup_of_disjoint (fun k => (hX k).comap_le) hi.iIndep hd
  simpa only [iSup_singleton] using hh

/-- Any measurable past statistic and the actual fresh Gaussian increment have the product law.
The past statistic can contain a survival indicator, a current position, and additional history. -/
theorem past_currentIncrement_jointLaw {μ : Measure Ω}
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) (n : ℕ)
    {α : Type*} [MeasurableSpace α] {Y : Ω → α}
    (hY : Measurable[incrementIndexSpace X (Iio n)] Y) :
    μ.map (fun ω => (Y ω, X n ω)) = (μ.map Y).prod (gaussianReal 0 1) := by
  have := hi.isProbabilityMeasure
  have hYm : Measurable Y := hY.mono (incrementIndexSpace_le hX _) le_rfl
  have hiY : IndepFun (X n) Y μ :=
    indep_of_indep_of_le_right (currentIncrement_indep_past hX hi n) hY.comap_le
  rw [hiY.symm.map_prod_eq_prod_map_map hYm.aemeasurable (hX n).aemeasurable, hG]

end SwingRepair
