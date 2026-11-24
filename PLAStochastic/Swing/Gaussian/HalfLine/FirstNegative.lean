import PLAStochastic.Swing.Gaussian.StripExit.OvershootMoments
import PLAStochastic.Swing.Gaussian.Stopping.CappedExitPosition

/-! The actual first negative position of the drifted Gaussian walk. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal Topology Classical
namespace SwingRepair
set_option backward.isDefEq.respectTransparency false

variable {Ω : Type*} {X : ℕ → Ω → ℝ}

def gaussianHalfLineExit (X : ℕ → Ω → ℝ) (x a : ℝ) : Ω → WithTop ℕ :=
  hittingAfter (gaussianDriftWalk X x a) (Iio 0) 0

def gaussianHalfLineSurvives (X : ℕ → Ω → ℝ) (x a : ℝ) (n : ℕ) : Set Ω :=
  {ω | ∀ j ≤ n, 0 ≤ gaussianDriftWalk X x a j ω}

def gaussianHalfLineExitPosition (X : ℕ → Ω → ℝ) (x a : ℝ) (ω : Ω) : ℝ :=
  gaussianDriftWalk X x a ((gaussianHalfLineExit X x a ω).untopD 0) ω

def gaussianHalfLineOvershoot (X : ℕ → Ω → ℝ) (x a : ℝ) (ω : Ω) : ℝ :=
  if gaussianHalfLineExit X x a ω = ⊤ then 0 else -gaussianHalfLineExitPosition X x a ω

def gaussianHalfLineExitSlice (X : ℕ → Ω → ℝ) (x a : ℝ) (n : ℕ) : Set Ω :=
  gaussianHalfLineSurvives X x a n ∩ {ω | gaussianDriftWalk X x a (n+1) ω < 0}

theorem lt_gaussianHalfLineExit_iff (X : ℕ → Ω → ℝ) (x a : ℝ) (n : ℕ) (ω : Ω) :
    (n : WithTop ℕ) < gaussianHalfLineExit X x a ω ↔ ω ∈ gaussianHalfLineSurvives X x a n := by
  constructor
  · intro hn j hj
    exact le_of_not_gt (notMem_of_lt_hittingAfter
      ((WithTop.coe_le_coe.mpr hj).trans_lt hn) (Nat.zero_le j))
  · intro hs
    apply lt_of_not_ge
    intro hl
    obtain ⟨j, hj, ho⟩ := hittingAfter_le_iff.mp hl
    exact not_lt_of_ge (hs j hj.2) ho

theorem gaussianHalfLineExitPosition_neg {x a : ℝ} {ω : Ω}
    (hτ : gaussianHalfLineExit X x a ω ≠ ⊤) : gaussianHalfLineExitPosition X x a ω < 0 := by
  have hh := hittingAfter_mem_set_of_ne_top (u := gaussianDriftWalk X x a)
    (s := Iio 0) (n := 0) (ω := ω) hτ
  change gaussianDriftWalk X x a (gaussianHalfLineExit X x a ω).untopA ω < 0 at hh
  unfold gaussianHalfLineExitPosition
  lift gaussianHalfLineExit X x a ω to ℕ using hτ with n hn
  exact hh

theorem gaussianHalfLineOvershoot_nonneg (X : ℕ → Ω → ℝ) (x a : ℝ) (ω : Ω) :
    0 ≤ gaussianHalfLineOvershoot X x a ω := by
  unfold gaussianHalfLineOvershoot
  split_ifs with h
  · exact le_rfl
  · exact (neg_pos.mpr (gaussianHalfLineExitPosition_neg h)).le

theorem gaussianHalfLineExit_eq_succ_iff (X : ℕ → Ω → ℝ) (x a : ℝ) (n : ℕ) (ω : Ω) :
    gaussianHalfLineExit X x a ω = (n+1 : ℕ) ↔ ω ∈ gaussianHalfLineExitSlice X x a n := by
  constructor
  · intro he
    refine ⟨(lt_gaussianHalfLineExit_iff X x a n ω).mp
      (by rw [he]; exact WithTop.coe_lt_coe.mpr (Nat.lt_succ_self n)), ?_⟩
    have hh := gaussianHalfLineExitPosition_neg (show gaussianHalfLineExit X x a ω ≠ ⊤ by
      rw [he]; exact WithTop.coe_ne_top)
    change gaussianDriftWalk X x a (n+1) ω < 0
    unfold gaussianHalfLineExitPosition at hh
    rw [he] at hh
    exact hh
  · rintro ⟨hs, ho⟩
    have hl := (lt_gaussianHalfLineExit_iff X x a n ω).mpr hs
    have hu : gaussianHalfLineExit X x a ω ≤ (n+1 : ℕ) := hittingAfter_le_of_mem (Nat.zero_le _) ho
    have hf := ne_top_of_le_ne_top WithTop.coe_ne_top hu
    lift gaussianHalfLineExit X x a ω to ℕ using hf with m hm
    have hl' : n < m := WithTop.coe_lt_coe.mp hl
    have hu' : m ≤ n+1 := WithTop.coe_le_coe.mp hu
    exact congrArg (fun k : ℕ => (k : WithTop ℕ)) (show m=n+1 by omega)

theorem gaussianHalfLineOvershoot_of_slice {x a : ℝ} {n : ℕ} {ω : Ω}
    (hω : ω ∈ gaussianHalfLineExitSlice X x a n) :
    gaussianHalfLineOvershoot X x a ω = -gaussianDriftWalk X x a (n+1) ω := by
  have he := (gaussianHalfLineExit_eq_succ_iff X x a n ω).mpr hω
  rw [gaussianHalfLineOvershoot, if_neg (show gaussianHalfLineExit X x a ω ≠ ⊤ by
    rw [he]; exact WithTop.coe_ne_top), gaussianHalfLineExitPosition, he]
  rfl

theorem gaussianHalfLineFinite_eq_iUnion {x a : ℝ} (hx : 0 ≤ x) :
    {ω | gaussianHalfLineExit X x a ω ≠ ⊤} = ⋃ n, gaussianHalfLineExitSlice X x a n := by
  ext ω
  constructor
  · intro hτ
    obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.mp hτ
    have hnpos : 0 < n := by
      have hp : (0 : WithTop ℕ) < gaussianHalfLineExit X x a ω := by
        apply (lt_gaussianHalfLineExit_iff X x a 0 ω).mpr
        intro j hj
        have : j = 0 := by omega
        simpa [this] using hx
      exact WithTop.coe_lt_coe.mp (hn ▸ hp)
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hnpos)
    exact mem_iUnion.mpr ⟨m, (gaussianHalfLineExit_eq_succ_iff X x a m ω).mp hn.symm⟩
  · intro hω
    obtain ⟨n, hn⟩ := mem_iUnion.mp hω
    change gaussianHalfLineExit X x a ω ≠ ⊤
    rw [(gaussianHalfLineExit_eq_succ_iff X x a n ω).mpr hn]
    exact WithTop.coe_ne_top

theorem gaussianHalfLineExitSlice_disjoint (X : ℕ → Ω → ℝ) (x a : ℝ) :
    Pairwise (fun n m => Disjoint (gaussianHalfLineExitSlice X x a n) (gaussianHalfLineExitSlice X x a m)) := by
  intro n m hnm
  apply disjoint_left.mpr
  intro ω hn hm
  have he := ((gaussianHalfLineExit_eq_succ_iff X x a n ω).mpr hn).symm.trans
    ((gaussianHalfLineExit_eq_succ_iff X x a m ω).mpr hm)
  have he' : n+1=m+1 := WithTop.coe_injective he
  omega

theorem gaussianHalfLine_capped_position_lower {x a : ℝ} (m : ℕ) (ω : Ω) :
    -gaussianHalfLineOvershoot X x a ω ≤
      gaussianDriftWalk X x a (capDiscreteTime (gaussianHalfLineExit X x a ω) m) ω := by
  by_cases hm : (m : WithTop ℕ) < gaussianHalfLineExit X x a ω
  · rw [capDiscreteTime_eq_of_lt hm]
    have hs := ((lt_gaussianHalfLineExit_iff X x a m ω).mp hm) m le_rfl
    linarith [gaussianHalfLineOvershoot_nonneg X x a ω]
  · rw [capDiscreteTime_eq_of_le (le_of_not_gt hm)]
    have ht : gaussianHalfLineExit X x a ω ≠ ⊤ :=
      ne_top_of_le_ne_top WithTop.coe_ne_top (le_of_not_gt hm)
    simp only [gaussianHalfLineOvershoot, if_neg ht, neg_neg]
    exact le_rfl

variable [mΩ : MeasurableSpace Ω]

theorem gaussianHalfLineExit_isStoppingTime (hX : ∀ n, Measurable (X n)) (x a : ℝ) :
    IsStoppingTime (gaussianWalkFiltration X hX) (gaussianHalfLineExit X x a) :=
  (gaussianDriftWalk_adapted hX x a).isStoppingTime_hittingAfter measurableSet_Iio

omit mΩ in
theorem gaussianHalfLineSurvives_measurable_past (X : ℕ → Ω → ℝ) (x a : ℝ) (n : ℕ) :
    MeasurableSet[incrementIndexSpace X (Iio n)] (gaussianHalfLineSurvives X x a n) := by
  unfold gaussianHalfLineSurvives
  simp only [ofPred_forall]
  apply MeasurableSet.iInter
  intro j
  apply MeasurableSet.iInter
  intro hj
  exact ((gaussianDriftWalk_measurable_past X x a j).mono
    (incrementIndexSpace_mono (Iio_subset_Iio hj)) le_rfl) measurableSet_Ici

theorem gaussianHalfLineExitSlice_measurable (hX : ∀ n, Measurable (X n)) (x a : ℝ) (n : ℕ) :
    MeasurableSet (gaussianHalfLineExitSlice X x a n) :=
  (incrementIndexSpace_le hX _ _ (gaussianHalfLineSurvives_measurable_past X x a n)).inter
    (measurableSet_lt (gaussianDriftWalk_measurable hX x a (n+1)) measurable_const)

theorem gaussianHalfLineExitPosition_measurable (hX : ∀ n, Measurable (X n)) (x a : ℝ) :
    Measurable (gaussianHalfLineExitPosition X x a) :=
  countableSelection_measurable (gaussianDriftWalk_measurable hX x a)
    ((gaussianHalfLineExit_isStoppingTime hX x a).measurable'.untopD 0)

theorem gaussianHalfLineOvershoot_measurable (hX : ∀ n, Measurable (X n)) (x a : ℝ) :
    Measurable (gaussianHalfLineOvershoot X x a) :=
  Measurable.ite ((gaussianHalfLineExit_isStoppingTime hX x a).measurable'
    (measurableSet_singleton ⊤)) measurable_const (gaussianHalfLineExitPosition_measurable hX x a).neg

end SwingRepair
