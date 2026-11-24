import PLAStochastic.Swing.ConstantEvaluation.Fluctuation.GaussianSequenceLaw
import PLAStochastic.ForMathlib.Probability.RandomWalk.Fluctuation.SparreAndersenIID

/-! # Path reversal for the drifted Gaussian walk (roadmap 1.3, step 1)

With `S_k = W_k + a k`, reversing the first `n` increments `X_0, …, X_{n-1}` maps the
partial sums `S_j` to `S_n - S_{n-j}` and fixes `S_n`.  Since the increments are
exchangeable,

  `∫ 1{S_j ≤ 0 ∀ j < n} g(S_n) = ∫ 1{S_n ≤ S_k ∀ 1 ≤ k ≤ n} g(S_n)`

for every measurable `g : ℝ → ℝ≥0∞`.  The left side is the contribution of the
event `{τ = n}` to the ladder height law; the right side is the event that the terminal
point is a new (weak) descending record relative to the times `1, …, n-1`.
-/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
namespace SwingRepair

variable {Ω : Type*} [MeasurableSpace Ω] {X : ℕ → Ω → ℝ} {μ : Measure Ω}

/-! ### Partial sums of a finite vector -/

/-- The drifted partial sums of a finite vector: `∑_{i<k} (v_i + a)`. -/
def finWalk (a : ℝ) (n : ℕ) (v : Fin n → ℝ) (k : ℕ) : ℝ :=
  ∑ i : Fin n, if (i : ℕ) < k then v i + a else 0

theorem finWalk_measurable (a : ℝ) (n k : ℕ) :
    Measurable (fun v : Fin n → ℝ => finWalk a n v k) := by
  unfold finWalk
  refine Finset.measurable_sum _ fun i _ => ?_
  split_ifs
  · exact (measurable_pi_apply i : Measurable fun v : Fin n → ℝ => v i).add_const a
  · exact measurable_const

theorem finWalk_eq_sum_range (a : ℝ) (n : ℕ) (g : ℕ → ℝ) {k : ℕ} (hk : k ≤ n) :
    finWalk a n (fun i : Fin n => g i) k = ∑ i ∈ Finset.range k, (g i + a) := by
  unfold finWalk
  rw [Finset.sum_fin_eq_sum_range]
  have hfilter : (Finset.range n).filter (fun i => i < k) = Finset.range k := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_range]
    omega
  rw [← hfilter, Finset.sum_filter]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [dif_pos (Finset.mem_range.mp hi)]

omit [MeasurableSpace Ω] in
/-- Along the original order the finite partial sums are the walk. -/
theorem finWalk_original (a : ℝ) (n : ℕ) (ω : Ω) {k : ℕ} (hk : k ≤ n) :
    finWalk a n (fun i : Fin n => X i ω) k = gaussianDriftWalk X 0 a k ω := by
  rw [finWalk_eq_sum_range a n (fun i => X i ω) hk, Finset.sum_add_distrib, Finset.sum_const,
    Finset.card_range, nsmul_eq_mul]
  simp only [gaussianDriftWalk, cumulativeSamples, zero_add]
  ring

omit [MeasurableSpace Ω] in
/-- Along the reversed order the finite partial sums are `S_n - S_{n-k}`. -/
theorem finWalk_reverse (a : ℝ) (n : ℕ) (ω : Ω) {k : ℕ} (hk : k ≤ n) :
    finWalk a n (fun i : Fin n => X (n - 1 - i) ω) k =
      gaussianDriftWalk X 0 a n ω - gaussianDriftWalk X 0 a (n - k) ω := by
  rw [finWalk_eq_sum_range a n (fun i => X (n - 1 - i) ω) hk]
  have hsplit := Finset.sum_range_add_sum_Ico (fun j => X j ω + a) (Nat.sub_le n k)
  have hIco : ∑ j ∈ Finset.Ico (n - k) n, (X j ω + a) =
      ∑ j ∈ Finset.range k, (X (n - k + j) ω + a) := by
    rw [Finset.sum_Ico_eq_sum_range]
    have : n - (n - k) = k := by omega
    rw [this]
  have hrefl := Finset.sum_range_reflect (fun j => X (n - k + j) ω + a) k
  have hcongr : ∑ i ∈ Finset.range k, (X (n - 1 - i) ω + a) =
      ∑ j ∈ Finset.range k, (X (n - k + (k - 1 - j)) ω + a) := by
    refine Finset.sum_congr rfl fun j hj => ?_
    have := Finset.mem_range.mp hj
    congr 3
    omega
  have hwalk : ∀ m, gaussianDriftWalk X 0 a m ω = ∑ j ∈ Finset.range m, (X j ω + a) := by
    intro m
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    simp only [gaussianDriftWalk, cumulativeSamples, zero_add]
    ring
  rw [hcongr, hrefl, ← hIco, hwalk, hwalk]
  linarith

/-! ### The reversal identity -/

/-- Reversing the first `n` coordinates of an i.i.d. sequence preserves the law of
any nonnegative functional. -/
theorem lintegral_reverse_vector (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) (n : ℕ) {G : (Fin n → ℝ) → ℝ≥0∞}
    (hGm : Measurable G) :
    ∫⁻ ω, G (fun i : Fin n => X i ω) ∂μ = ∫⁻ ω, G (fun i : Fin n => X (n - 1 - i) ω) ∂μ := by
  have hprob : IsProbabilityMeasure μ := hi.isProbabilityMeasure
  have h1 := Fluctuation.map_vector_eq_pi hX hi hG (m := n) (fun i => (i : ℕ)) Fin.val_injective
  have h2 := Fluctuation.map_vector_eq_pi hX hi hG (m := n) (fun i => n - 1 - (i : ℕ)) (by
    intro i j h
    have hi := i.isLt
    have hj := j.isLt
    ext
    dsimp only at h
    omega)
  rw [← lintegral_map hGm (measurable_pi_lambda _ fun i => hX _), h1,
    ← lintegral_map hGm (measurable_pi_lambda _ fun i => hX _), h2]

/-- The event that the terminal point is a weak descending record relative to
times `1, …, n`. -/
def terminalRecordSet (X : ℕ → Ω → ℝ) (a : ℝ) (n : ℕ) : Set Ω :=
  {ω | ∀ k, 1 ≤ k → k ≤ n → gaussianDriftWalk X 0 a n ω ≤ gaussianDriftWalk X 0 a k ω}

/-- The event that the first `n` partial sums (times `0, …, n-1`) are nonpositive. -/
def nonposPrefixSet (X : ℕ → Ω → ℝ) (a : ℝ) (n : ℕ) : Set Ω :=
  {ω | ∀ j < n, gaussianDriftWalk X 0 a j ω ≤ 0}

theorem measurableSet_terminalRecordSet (hX : ∀ n, Measurable (X n)) (a : ℝ) (n : ℕ) :
    MeasurableSet (terminalRecordSet X a n) := by
  have : terminalRecordSet X a n = ⋂ k, ⋂ (_ : 1 ≤ k), ⋂ (_ : k ≤ n),
      {ω | gaussianDriftWalk X 0 a n ω ≤ gaussianDriftWalk X 0 a k ω} := by
    ext ω; simp [terminalRecordSet]
  rw [this]
  exact MeasurableSet.iInter fun k => MeasurableSet.iInter fun _ => MeasurableSet.iInter fun _ =>
    measurableSet_le (gaussianDriftWalk_measurable hX 0 a n) (gaussianDriftWalk_measurable hX 0 a k)

theorem measurableSet_nonposPrefixSet (hX : ∀ n, Measurable (X n)) (a : ℝ) (n : ℕ) :
    MeasurableSet (nonposPrefixSet X a n) := by
  have : nonposPrefixSet X a n = ⋂ j, ⋂ (_ : j < n), {ω | gaussianDriftWalk X 0 a j ω ≤ 0} := by
    ext ω; simp [nonposPrefixSet]
  rw [this]
  exact MeasurableSet.iInter fun j => MeasurableSet.iInter fun _ =>
    measurableSet_le (gaussianDriftWalk_measurable hX 0 a j) measurable_const

/-- **Path reversal.** -/
theorem lintegral_nonposPrefix_eq_terminalRecord (hX : ∀ n, Measurable (X n))
    (hi : iIndepFun X μ) (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) (a : ℝ) (n : ℕ)
    {g : ℝ → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ ω, (nonposPrefixSet X a n).indicator (fun ω => g (gaussianDriftWalk X 0 a n ω)) ω ∂μ =
      ∫⁻ ω, (terminalRecordSet X a n).indicator
        (fun ω => g (gaussianDriftWalk X 0 a n ω)) ω ∂μ := by
  set G : (Fin n → ℝ) → ℝ≥0∞ := fun v =>
    {v : Fin n → ℝ | ∀ j < n, finWalk a n v j ≤ 0}.indicator (fun v => g (finWalk a n v n)) v
    with hGdef
  have hset : MeasurableSet {v : Fin n → ℝ | ∀ j < n, finWalk a n v j ≤ 0} := by
    have : {v : Fin n → ℝ | ∀ j < n, finWalk a n v j ≤ 0} =
        ⋂ j, ⋂ (_ : j < n), {v | finWalk a n v j ≤ 0} := by
      ext v; simp
    rw [this]
    exact MeasurableSet.iInter fun j => MeasurableSet.iInter fun _ =>
      measurableSet_le (finWalk_measurable a n j) measurable_const
  have hGm : Measurable G :=
    (hg.comp (finWalk_measurable a n n)).indicator hset
  have h := lintegral_reverse_vector hX hi hG n hGm
  have hL : ∀ ω, G (fun i : Fin n => X i ω) =
      (nonposPrefixSet X a n).indicator (fun ω => g (gaussianDriftWalk X 0 a n ω)) ω := by
    intro ω
    have hmem : (fun i : Fin n => X i ω) ∈ {v : Fin n → ℝ | ∀ j < n, finWalk a n v j ≤ 0} ↔
        ω ∈ nonposPrefixSet X a n := by
      simp only [Set.mem_ofPred_eq, nonposPrefixSet]
      refine forall_congr' fun j => imp_congr_right fun hj => ?_
      rw [finWalk_original a n ω hj.le]
    simp only [hGdef]
    by_cases hP : ω ∈ nonposPrefixSet X a n
    · rw [Set.indicator_of_mem (hmem.mpr hP), Set.indicator_of_mem hP,
        finWalk_original a n ω le_rfl]
    · rw [Set.indicator_of_notMem (fun h => hP (hmem.mp h)), Set.indicator_of_notMem hP]
  have hR : ∀ ω, G (fun i : Fin n => X (n - 1 - i) ω) =
      (terminalRecordSet X a n).indicator (fun ω => g (gaussianDriftWalk X 0 a n ω)) ω := by
    intro ω
    have hmem : (fun i : Fin n => X (n - 1 - i) ω) ∈
        {v : Fin n → ℝ | ∀ j < n, finWalk a n v j ≤ 0} ↔ ω ∈ terminalRecordSet X a n := by
      simp only [Set.mem_ofPred_eq, terminalRecordSet]
      constructor
      · intro h k hk1 hkn
        have := h (n - k) (by omega)
        rw [finWalk_reverse a n ω (Nat.sub_le n k)] at this
        have hnk : n - (n - k) = k := by omega
        rw [hnk] at this
        linarith
      · intro h j hj
        rw [finWalk_reverse a n ω hj.le]
        have := h (n - j) (by omega) (Nat.sub_le n j)
        linarith
    have h0 : gaussianDriftWalk X 0 a 0 ω = 0 := by simp [gaussianDriftWalk, cumulativeSamples]
    simp only [hGdef]
    by_cases hP : ω ∈ terminalRecordSet X a n
    · rw [Set.indicator_of_mem (hmem.mpr hP), Set.indicator_of_mem hP,
        finWalk_reverse a n ω le_rfl, Nat.sub_self, h0, sub_zero]
    · rw [Set.indicator_of_notMem (fun h => hP (hmem.mp h)), Set.indicator_of_notMem hP]
  simp_rw [hL, hR] at h
  exact h

end SwingRepair
