import PLAStochastic.ForMathlib.Probability.Process.IIDRestart.FiniteStoppingIndex

/-!
# Restart at an almost surely finite extended integer stopping time

The stopping time retains its original WithTop-valued definition and stopped
sigma-algebra. The value 0 used by untopD on the null infinite-time event only
defines an everywhere-valued random vector; it is never asserted to produce a
natural-filtration stopping time. Countable additivity is applied directly to
the original stopping-time fibers, whose union has full measure by isFiniteK.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace SwingRepair

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω}

/-- Countable additivity over the finite values of an almost surely finite stopping time. -/
theorem measure_eq_tsum_aeFiniteStoppingTime {f : Filtration ℕ mΩ}
    {τ : Ω → WithTop ℕ} (hτ : IsStoppingTime f τ)
    (isFiniteK : ∀ᵐ ω ∂μ, τ ω ≠ ⊤) {A : Set Ω} (hA : MeasurableSet A) :
    μ A = ∑' n : ℕ, μ (A ∩ {ω | τ ω = (n : WithTop ℕ)}) := by
  have hu : A =ᵐ[μ] ⋃ n : ℕ, A ∩ {ω | τ ω = (n : WithTop ℕ)} := by
    filter_upwards [isFiniteK] with ω hω
    obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.mp hω
    apply propext
    change ω ∈ A ↔ ω ∈ ⋃ n : ℕ, A ∩ {ω | τ ω = (n : WithTop ℕ)}
    simp only [Set.mem_iUnion, Set.mem_inter_iff, Set.mem_ofPred_eq]
    exact ⟨fun ha => ⟨n, ha, hn.symm⟩, fun ⟨_, ha, _⟩ => ha⟩
  calc
    μ A = μ (⋃ n : ℕ, A ∩ {ω | τ ω = (n : WithTop ℕ)}) := measure_congr hu
    _ = ∑' n : ℕ, μ (A ∩ {ω | τ ω = (n : WithTop ℕ)}) := by
      apply measure_iUnion
      · intro i j hij
        apply Set.disjoint_left.mpr
        rintro ω ⟨_, hi⟩ ⟨_, hj⟩
        apply hij
        exact_mod_cast hi.symm.trans hj
      · intro n
        exact hA.inter (f.le n _ (hτ.measurableSet_eq n))

variable {X : ℕ → Ω → ℝ}

/--
Fixed-index independence and identical laws are combined across the original
WithTop stopping-time partition; no modification of its filtration is used.
-/
theorem stoppedSelection_inter_measure_aeFinite {β : Type*} [MeasurableSpace β]
    (hX : ∀ n, Measurable (X n)) {Y : ℕ → Ω → β} {Z : Ω → β}
    (hYm : ∀ n, Measurable (Y n))
    (hiY : ∀ n, Indep (MeasurableSpace.comap (Y n) inferInstance)
      (incrementFiltration X hX n) μ)
    (hidY : ∀ n, IdentDistrib (Y n) Z μ μ)
    {τ : Ω → WithTop ℕ} (hτ : IsStoppingTime (incrementFiltration X hX) τ)
    (isFiniteK : ∀ᵐ ω ∂μ, τ ω ≠ ⊤)
    {A : Set Ω} (hA : MeasurableSet[hτ.measurableSpace] A)
    {B : Set β} (hB : MeasurableSet B) :
    μ (A ∩ (fun ω => Y ((τ ω).untopD 0) ω) ⁻¹' B) = μ A * μ (Z ⁻¹' B) := by
  have hAm : MeasurableSet A := hτ.measurableSpace_le _ hA
  have hY := countableSelection_measurable hYm (hτ.measurable'.untopD 0)
  rw [measure_eq_tsum_aeFiniteStoppingTime hτ isFiniteK (hAm.inter (hY hB))]
  calc
    (∑' n : ℕ, μ ((A ∩ (fun ω => Y ((τ ω).untopD 0) ω) ⁻¹' B) ∩
      {ω | τ ω = (n : WithTop ℕ)})) =
        ∑' n : ℕ, μ (A ∩ {ω | τ ω = (n : WithTop ℕ)}) * μ (Z ⁻¹' B) := by
      apply tsum_congr
      intro n
      have heq : (A ∩ (fun ω => Y ((τ ω).untopD 0) ω) ⁻¹' B) ∩
          {ω | τ ω = (n : WithTop ℕ)} =
          Y n ⁻¹' B ∩ (A ∩ {ω | τ ω = (n : WithTop ℕ)}) := by
        ext ω
        have hindex (hn : τ ω = (n : WithTop ℕ)) : (τ ω).untopD 0 = n := by
          rw [hn]
          rfl
        simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_ofPred_eq]
        constructor
        · rintro ⟨⟨ha, hb⟩, hn⟩
          exact ⟨by simpa only [hindex hn] using hb, ha, hn⟩
        · rintro ⟨hb, ha, hn⟩
          exact ⟨⟨ha, by simpa only [hindex hn] using hb⟩, hn⟩
      rw [heq]
      have hmB : MeasurableSet[MeasurableSpace.comap (Y n) inferInstance]
          (Y n ⁻¹' B) := ⟨B, hB, rfl⟩
      have hslice : MeasurableSet[incrementFiltration X hX n]
          (A ∩ {ω | τ ω = (n : WithTop ℕ)}) :=
        (hτ.measurableSet_inter_eq_iff A n).mp (hA.inter (hτ.measurableSet_eq' n))
      rw [(Indep_iff _ _ μ).mp (hiY n) _ _ hmB hslice]
      rw [(hidY n).measure_mem_eq hB, mul_comm]
    _ = μ A * μ (Z ⁻¹' B) := by
      rw [ENNReal.tsum_mul_right, ← measure_eq_tsum_aeFiniteStoppingTime hτ isFiniteK hAm]

/-- The future finite block is measurable even though the stopping time may be infinite. -/
theorem stoppedBlock_measurable_aeFinite (hX : ∀ n, Measurable (X n))
    {τ : Ω → WithTop ℕ} (hτ : IsStoppingTime (incrementFiltration X hX) τ) (r : ℕ) :
    Measurable (fun ω (j : Fin r) => X ((τ ω).untopD 0 + 1 + j.val) ω) :=
  countableSelection_measurable
    (fun n => measurable_pi_lambda _ fun j : Fin r => hX (n + 1 + j.val))
    (hτ.measurable'.untopD 0)

/-- The iid block restart identity for an almost surely finite extended stopping time. -/
theorem stoppedBlock_inter_measure_aeFinite (hX : ∀ n, Measurable (X n))
    (hi : iIndepFun X μ) (hid : ∀ n, IdentDistrib (X n) (X 0) μ μ)
    {τ : Ω → WithTop ℕ} (hτ : IsStoppingTime (incrementFiltration X hX) τ)
    (isFiniteK : ∀ᵐ ω ∂μ, τ ω ≠ ⊤)
    (r : ℕ) {A : Set Ω} (hA : MeasurableSet[hτ.measurableSpace] A)
    {B : Set (Fin r → ℝ)} (hB : MeasurableSet B) :
    μ (A ∩ (fun ω (j : Fin r) => X ((τ ω).untopD 0 + 1 + j.val) ω) ⁻¹' B) =
      μ A * μ ((fun ω (j : Fin r) => X j.val ω) ⁻¹' B) :=
  stoppedSelection_inter_measure_aeFinite hX
    (fun n => measurable_pi_lambda _ fun j : Fin r => hX (n + 1 + j.val))
    (fun n => futureBlock_indep_incrementFiltration hX hi n r)
    (fun n => futureBlock_identDistrib hX hi hid n r) hτ isFiniteK hA hB

/-- The future finite block has the original joint law at an almost surely finite stopping time. -/
theorem stoppedBlock_identDistrib_aeFinite [IsProbabilityMeasure μ]
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hid : ∀ n, IdentDistrib (X n) (X 0) μ μ)
    {τ : Ω → WithTop ℕ} (hτ : IsStoppingTime (incrementFiltration X hX) τ)
    (isFiniteK : ∀ᵐ ω ∂μ, τ ω ≠ ⊤) (r : ℕ) :
    IdentDistrib (fun ω (j : Fin r) => X ((τ ω).untopD 0 + 1 + j.val) ω)
      (fun ω (j : Fin r) => X j.val ω) μ μ := by
  refine ⟨(stoppedBlock_measurable_aeFinite hX hτ r).aemeasurable,
    (measurable_pi_lambda _ fun j : Fin r => hX j.val).aemeasurable, ?_⟩
  apply Measure.ext
  intro B hB
  rw [Measure.map_apply (stoppedBlock_measurable_aeFinite hX hτ r) hB,
    Measure.map_apply (measurable_pi_lambda _ fun j : Fin r => hX j.val) hB]
  simpa using stoppedBlock_inter_measure_aeFinite hX hi hid hτ isFiniteK r MeasurableSet.univ hB

/-- Independence is from the original extended stopping-time sigma-algebra. -/
theorem stoppedBlock_indep_stopped_aeFinite [IsProbabilityMeasure μ]
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hid : ∀ n, IdentDistrib (X n) (X 0) μ μ)
    {τ : Ω → WithTop ℕ} (hτ : IsStoppingTime (incrementFiltration X hX) τ)
    (isFiniteK : ∀ᵐ ω ∂μ, τ ω ≠ ⊤) (r : ℕ) :
    Indep (MeasurableSpace.comap
      (fun ω (j : Fin r) => X ((τ ω).untopD 0 + 1 + j.val) ω) inferInstance)
      hτ.measurableSpace μ := by
  apply (Indep_iff _ _ μ).mpr
  intro C A hC hA
  rcases hC with ⟨B, hB, rfl⟩
  rw [Set.inter_comm, stoppedBlock_inter_measure_aeFinite hX hi hid hτ isFiniteK r hA hB,
    (stoppedBlock_identDistrib_aeFinite hX hi hid hτ isFiniteK r).measure_mem_eq hB, mul_comm]

end SwingRepair
