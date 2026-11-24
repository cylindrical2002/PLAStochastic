import PLAStochastic.Swing.Gaussian.StripExit.Walk

/-! The actual stopped exit position, overshoot and disjoint exit slices. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal Topology Classical
namespace SwingRepair
set_option backward.isDefEq.respectTransparency false

variable {Ω : Type*} {X : ℕ → Ω → ℝ}

def gaussianStripExitPosition (X : ℕ → Ω → ℝ) (x a R : ℝ) (ω : Ω) : ℝ :=
  gaussianDriftWalk X x a ((gaussianStripExit X x a R ω).untopD 0) ω

/-- The overshoot of the actual first exit; on paths with no finite exit its value is zero. -/
def gaussianStripOvershoot (X : ℕ → Ω → ℝ) (x a R : ℝ) (ω : Ω) : ℝ :=
  if gaussianStripExit X x a R ω = ⊤ then 0 else
    max 0 (max (-gaussianStripExitPosition X x a R ω) (gaussianStripExitPosition X x a R ω - R))

def gaussianStripLowerExit (X : ℕ → Ω → ℝ) (x a R : ℝ) : Set Ω :=
  {ω | gaussianStripExit X x a R ω ≠ ⊤ ∧ gaussianStripExitPosition X x a R ω < 0}

def gaussianStripUpperExit (X : ℕ → Ω → ℝ) (x a R : ℝ) : Set Ω :=
  {ω | gaussianStripExit X x a R ω ≠ ⊤ ∧ R < gaussianStripExitPosition X x a R ω}

def gaussianStripLowerSlice (X : ℕ → Ω → ℝ) (x a R : ℝ) (n : ℕ) : Set Ω :=
  gaussianStripSurvives X x a R n ∩ {ω | gaussianDriftWalk X x a (n + 1) ω < 0}

def gaussianStripUpperSlice (X : ℕ → Ω → ℝ) (x a R : ℝ) (n : ℕ) : Set Ω :=
  gaussianStripSurvives X x a R n ∩ {ω | R < gaussianDriftWalk X x a (n + 1) ω}

theorem gaussianStripOvershoot_nonneg (X : ℕ → Ω → ℝ) (x a R : ℝ) (ω : Ω) :
    0 ≤ gaussianStripOvershoot X x a R ω := by
  unfold gaussianStripOvershoot
  split_ifs <;> simp

theorem gaussianStripExitPosition_not_mem {x a R : ℝ} {ω : Ω}
    (hτ : gaussianStripExit X x a R ω ≠ ⊤) :
    gaussianStripExitPosition X x a R ω ∉ Icc (0 : ℝ) R := by
  have hh := hittingAfter_mem_set_of_ne_top (u := gaussianDriftWalk X x a)
    (s := (Icc (0 : ℝ) R)ᶜ) (n := 0) (ω := ω) hτ
  change gaussianDriftWalk X x a (gaussianStripExit X x a R ω).untopA ω ∉ Icc (0 : ℝ) R at hh
  unfold gaussianStripExitPosition
  lift gaussianStripExit X x a R ω to ℕ using hτ with n hn
  exact hh

theorem gaussianStripExit_pos {x a R : ℝ} (hx : x ∈ Icc (0 : ℝ) R) (ω : Ω) :
    (0 : WithTop ℕ) < gaussianStripExit X x a R ω := by
  apply (lt_gaussianStripExit_iff X x a R 0 ω).mpr
  intro j hj
  have he : j = 0 := by omega
  simpa only [he, gaussianDriftWalk_zero] using hx

theorem gaussianStripExit_eq_of_lowerSlice {x a R : ℝ} {n : ℕ} {ω : Ω}
    (hω : ω ∈ gaussianStripLowerSlice X x a R n) :
    gaussianStripExit X x a R ω = (n + 1 : ℕ) := by
  apply (gaussianStripExit_eq_succ_iff X x a R n ω).mpr
  refine ⟨hω.1, ?_⟩
  intro hm
  exact (not_lt_of_ge hm.1) hω.2

theorem gaussianStripExit_eq_of_upperSlice {x a R : ℝ} {n : ℕ} {ω : Ω}
    (hω : ω ∈ gaussianStripUpperSlice X x a R n) :
    gaussianStripExit X x a R ω = (n + 1 : ℕ) := by
  apply (gaussianStripExit_eq_succ_iff X x a R n ω).mpr
  refine ⟨hω.1, ?_⟩
  intro hm
  exact (not_lt_of_ge hm.2) hω.2

theorem gaussianStripExitPosition_of_eq {x a R : ℝ} {n : ℕ} {ω : Ω}
    (hτ : gaussianStripExit X x a R ω = (n : WithTop ℕ)) :
    gaussianStripExitPosition X x a R ω = gaussianDriftWalk X x a n ω := by
  rw [gaussianStripExitPosition, hτ]
  rfl

theorem gaussianStripOvershoot_of_lowerExit {x a R : ℝ} (hR : 0 ≤ R) {ω : Ω}
    (hω : ω ∈ gaussianStripLowerExit X x a R) :
    gaussianStripOvershoot X x a R ω = -gaussianStripExitPosition X x a R ω := by
  unfold gaussianStripOvershoot
  have he : gaussianStripExitPosition X x a R ω - R ≤ -gaussianStripExitPosition X x a R ω := by
    linarith [hω.2]
  rw [if_neg hω.1, max_eq_left he, max_eq_right (by linarith [hω.2])]

theorem gaussianStripOvershoot_of_upperExit {x a R : ℝ} (hR : 0 ≤ R) {ω : Ω}
    (hω : ω ∈ gaussianStripUpperExit X x a R) :
    gaussianStripOvershoot X x a R ω = gaussianStripExitPosition X x a R ω - R := by
  unfold gaussianStripOvershoot
  have he : -gaussianStripExitPosition X x a R ω ≤ gaussianStripExitPosition X x a R ω - R := by
    linarith [hω.2]
  rw [if_neg hω.1, max_eq_right he, max_eq_right (by linarith [hω.2])]

theorem gaussianStripLowerSlice_subset {x a R : ℝ} {n : ℕ} :
    gaussianStripLowerSlice X x a R n ⊆ gaussianStripLowerExit X x a R := by
  intro ω hω
  have he := gaussianStripExit_eq_of_lowerSlice hω
  refine ⟨by rw [he]; exact WithTop.coe_ne_top, ?_⟩
  rw [gaussianStripExitPosition_of_eq he]
  exact hω.2

theorem gaussianStripUpperSlice_subset {x a R : ℝ} {n : ℕ} :
    gaussianStripUpperSlice X x a R n ⊆ gaussianStripUpperExit X x a R := by
  intro ω hω
  have he := gaussianStripExit_eq_of_upperSlice hω
  refine ⟨by rw [he]; exact WithTop.coe_ne_top, ?_⟩
  rw [gaussianStripExitPosition_of_eq he]
  exact hω.2

theorem gaussianStripExit_exists_succ {x a R : ℝ} (hx : x ∈ Icc (0 : ℝ) R) {ω : Ω}
    (hτ : gaussianStripExit X x a R ω ≠ ⊤) :
    ∃ n : ℕ, gaussianStripExit X x a R ω = (n + 1 : ℕ) := by
  obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.mp hτ
  have hp := gaussianStripExit_pos (X := X) (a := a) hx ω
  rw [← hn] at hp
  have hnp : 0 < n := WithTop.coe_lt_coe.mp hp
  cases n with
  | zero => omega
  | succ n => exact ⟨n, hn.symm⟩

theorem gaussianStripLowerExit_eq_iUnion {x a R : ℝ} (hx : x ∈ Icc (0 : ℝ) R) :
    gaussianStripLowerExit X x a R = ⋃ n : ℕ, gaussianStripLowerSlice X x a R n := by
  ext ω
  constructor
  · intro hω
    obtain ⟨n, hn⟩ := gaussianStripExit_exists_succ hx hω.1
    apply mem_iUnion.mpr
    refine ⟨n, (gaussianStripExit_eq_succ_iff X x a R n ω).mp hn |>.1, ?_⟩
    change gaussianDriftWalk X x a (n + 1) ω < 0
    rw [← gaussianStripExitPosition_of_eq hn]
    exact hω.2
  · intro hω
    obtain ⟨n, hn⟩ := mem_iUnion.mp hω
    exact gaussianStripLowerSlice_subset hn

theorem gaussianStripUpperExit_eq_iUnion {x a R : ℝ} (hx : x ∈ Icc (0 : ℝ) R) :
    gaussianStripUpperExit X x a R = ⋃ n : ℕ, gaussianStripUpperSlice X x a R n := by
  ext ω
  constructor
  · intro hω
    obtain ⟨n, hn⟩ := gaussianStripExit_exists_succ hx hω.1
    apply mem_iUnion.mpr
    refine ⟨n, (gaussianStripExit_eq_succ_iff X x a R n ω).mp hn |>.1, ?_⟩
    change R < gaussianDriftWalk X x a (n + 1) ω
    rw [← gaussianStripExitPosition_of_eq hn]
    exact hω.2
  · intro hω
    obtain ⟨n, hn⟩ := mem_iUnion.mp hω
    exact gaussianStripUpperSlice_subset hn

theorem gaussianStripLowerSlice_disjoint (X : ℕ → Ω → ℝ) (x a R : ℝ) :
    Pairwise (fun n m => Disjoint (gaussianStripLowerSlice X x a R n) (gaussianStripLowerSlice X x a R m)) := by
  intro n m hnm
  apply disjoint_left.mpr
  intro ω hn hm
  have he := (gaussianStripExit_eq_of_lowerSlice hn).symm.trans (gaussianStripExit_eq_of_lowerSlice hm)
  have he' : n + 1 = m + 1 := WithTop.coe_injective he
  omega

theorem gaussianStripUpperSlice_disjoint (X : ℕ → Ω → ℝ) (x a R : ℝ) :
    Pairwise (fun n m => Disjoint (gaussianStripUpperSlice X x a R n) (gaussianStripUpperSlice X x a R m)) := by
  intro n m hnm
  apply disjoint_left.mpr
  intro ω hn hm
  have he := (gaussianStripExit_eq_of_upperSlice hn).symm.trans (gaussianStripExit_eq_of_upperSlice hm)
  have he' : n + 1 = m + 1 := WithTop.coe_injective he
  omega

theorem gaussianStripLowerUpper_disjoint {x a R : ℝ} (hR : 0 ≤ R) :
    Disjoint (gaussianStripLowerExit X x a R) (gaussianStripUpperExit X x a R) := by
  apply disjoint_left.mpr
  intro ω hl hu
  linarith [hl.2, hu.2]

theorem gaussianStripFinite_eq_lower_union_upper {x a R : ℝ} :
    {ω | gaussianStripExit X x a R ω ≠ ⊤} =
      gaussianStripLowerExit X x a R ∪ gaussianStripUpperExit X x a R := by
  ext ω
  constructor
  · intro hτ
    have ho := gaussianStripExitPosition_not_mem hτ
    by_cases hl : gaussianStripExitPosition X x a R ω < 0
    · exact Or.inl ⟨hτ, hl⟩
    · exact Or.inr ⟨hτ, lt_of_not_ge (fun hu => ho ⟨le_of_not_gt hl, hu⟩)⟩
  · rintro (h | h) <;> exact h.1

variable [mΩ : MeasurableSpace Ω]

theorem gaussianDriftWalk_measurable (hX : ∀ n, Measurable (X n)) (x a : ℝ) (n : ℕ) :
    Measurable (gaussianDriftWalk X x a n) :=
  (gaussianDriftWalk_measurable_past X x a n).mono (incrementIndexSpace_le hX _) le_rfl

theorem gaussianStripExitPosition_measurable (hX : ∀ n, Measurable (X n)) (x a R : ℝ) :
    Measurable (gaussianStripExitPosition X x a R) :=
  countableSelection_measurable (gaussianDriftWalk_measurable hX x a)
    ((gaussianStripExit_isStoppingTime hX x a R).measurable'.untopD 0)

theorem gaussianStripOvershoot_measurable (hX : ∀ n, Measurable (X n)) (x a R : ℝ) :
    Measurable (gaussianStripOvershoot X x a R) := by
  have hp := gaussianStripExitPosition_measurable hX x a R
  exact Measurable.ite ((gaussianStripExit_isStoppingTime hX x a R).measurable'
    (measurableSet_singleton ⊤)) measurable_const (measurable_const.max (hp.neg.max (hp.sub_const R)))

theorem gaussianStripLowerExit_measurable (hX : ∀ n, Measurable (X n)) (x a R : ℝ) :
    MeasurableSet (gaussianStripLowerExit X x a R) :=
  ((gaussianStripExit_isStoppingTime hX x a R).measurable' (measurableSet_singleton ⊤)).compl.inter
    (measurableSet_lt (gaussianStripExitPosition_measurable hX x a R) measurable_const)

theorem gaussianStripUpperExit_measurable (hX : ∀ n, Measurable (X n)) (x a R : ℝ) :
    MeasurableSet (gaussianStripUpperExit X x a R) :=
  ((gaussianStripExit_isStoppingTime hX x a R).measurable' (measurableSet_singleton ⊤)).compl.inter
    (measurableSet_lt measurable_const (gaussianStripExitPosition_measurable hX x a R))

theorem gaussianStripLowerSlice_measurable (hX : ∀ n, Measurable (X n)) (x a R : ℝ) (n : ℕ) :
    MeasurableSet (gaussianStripLowerSlice X x a R n) :=
  (incrementIndexSpace_le hX _ _ (gaussianStripSurvives_measurable_past X x a R n)).inter
    (measurableSet_lt (gaussianDriftWalk_measurable hX x a (n + 1)) measurable_const)

theorem gaussianStripUpperSlice_measurable (hX : ∀ n, Measurable (X n)) (x a R : ℝ) (n : ℕ) :
    MeasurableSet (gaussianStripUpperSlice X x a R n) :=
  (incrementIndexSpace_le hX _ _ (gaussianStripSurvives_measurable_past X x a R n)).inter
    (measurableSet_lt measurable_const (gaussianDriftWalk_measurable hX x a (n + 1)))

end SwingRepair
