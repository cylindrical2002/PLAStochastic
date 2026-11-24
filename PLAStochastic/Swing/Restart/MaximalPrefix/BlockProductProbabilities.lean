import PLAStochastic.Swing.Restart.MaximalPrefix.ThreePointBlocks

/-! # Product probabilities of actual disjoint future Gaussian blocks -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology
namespace SwingRepair
set_option backward.isDefEq.respectTransparency false

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {X : ℕ → Ω → ℝ}

/-- Information generated only by the indicated increment indices. -/
abbrev incrementIndexSpace (X : ℕ → Ω → ℝ) (S : Set ℕ) : MeasurableSpace Ω :=
  ⨆ k ∈ S, MeasurableSpace.comap (X k) inferInstance

omit [MeasurableSpace Ω] in
theorem incrementIndexSpace_mono {S T : Set ℕ} (hST : S ⊆ T) :
    incrementIndexSpace X S ≤ incrementIndexSpace X T :=
  iSup_le (fun k => iSup_le (fun hk => le_iSup_of_le k (le_iSup_of_le (hST hk) le_rfl)))

theorem incrementIndexSpace_le (hX : ∀ n, Measurable (X n)) (S : Set ℕ) :
    incrementIndexSpace X S ≤ (inferInstance : MeasurableSpace Ω) :=
  iSup_le (fun k => iSup_le (fun _ => (hX k).comap_le))

omit [MeasurableSpace Ω] in
theorem incrementIndexSpace_eval {S : Set ℕ} {k : ℕ} (hk : k ∈ S) :
    Measurable[incrementIndexSpace X S] (X k) :=
  measurable_iff_comap_le.mpr (le_iSup_of_le k (le_iSup_of_le hk le_rfl))

omit [MeasurableSpace Ω] in
theorem nativeGaussianBlock_measurable_in {S : Set ℕ} (n r : ℕ)
    (hS : Set.Ico n (n + 2 * r) ⊆ S) :
    Measurable[incrementIndexSpace X S] (nativeGaussianBlock X n r) := by
  let := incrementIndexSpace X S
  unfold nativeGaussianBlock
  apply Finset.measurable_sum
  intro k hk
  exact (incrementIndexSpace_eval (hS (Finset.mem_Ico.mp hk))).const_mul _

def nativeGaussianBlockPass (E : ℝ) (r : ℕ) : ℝ≥0∞ :=
  gaussianReal 0 (2 * (r : ℝ≥0)) (Set.Icc (-4 * E) (4 * E))

def nativeGaussianBlocksPassed (X : ℕ → Ω → ℝ) (E : ℝ) (n r b : ℕ) : Set Ω :=
  {ω | ∀ a < b, |nativeGaussianBlock X (n + 2 * r * a) r ω| ≤ 4 * E}

omit [MeasurableSpace Ω] in
theorem nativeGaussianBlocksPassed_measurable_in (E : ℝ) (n r b : ℕ) :
    MeasurableSet[incrementIndexSpace X (Set.Ico n (n + 2 * r * b))]
      (nativeGaussianBlocksPassed X E n r b) := by
  let := incrementIndexSpace X (Set.Ico n (n + 2 * r * b))
  simp only [nativeGaussianBlocksPassed, Set.ofPred_forall]
  apply MeasurableSet.iInter
  intro a
  apply MeasurableSet.iInter
  intro ha
  apply measurableSet_le _ measurable_const
  apply Measurable.abs
  apply nativeGaussianBlock_measurable_in
  intro k hk
  change n + 2 * r * a ≤ k ∧ k < n + 2 * r * a + 2 * r at hk
  change n ≤ k ∧ k < n + 2 * r * b
  have hab : a + 1 ≤ b := by omega
  have hm := Nat.mul_le_mul_left (2 * r) hab
  rw [Nat.mul_add, Nat.mul_one] at hm
  constructor <;> omega

theorem nativeGaussianBlock_probability (hX : ∀ n, Measurable (X n))
    (hi : iIndepFun X μ) (hG : ∀ n, μ.map (X n) = gaussianReal 0 1)
    (E : ℝ) (n r : ℕ) :
    μ {ω | |nativeGaussianBlock X n r ω| ≤ 4 * E} = nativeGaussianBlockPass E r := by
  have hl := (nativeGaussianBlock_hasLaw hX hi hG n r).measure_eq
    (p := fun z => z ∈ Set.Icc (-4 * E) (4 * E)) measurableSet_Icc
  simpa only [Set.mem_Icc, Set.Icc_def, abs_le, neg_mul, nativeGaussianBlockPass] using! hl

/-- The required block event has exactly the product probability, on the original
Gaussian probability space, with the original disjoint increment indices. -/
theorem nativeGaussianBlocksPassed_probability (hX : ∀ n, Measurable (X n))
    (hi : iIndepFun X μ) (hG : ∀ n, μ.map (X n) = gaussianReal 0 1)
    (E : ℝ) (n r b : ℕ) :
    μ (nativeGaussianBlocksPassed X E n r b) = nativeGaussianBlockPass E r ^ b := by
  have : IsProbabilityMeasure μ := hi.isProbabilityMeasure
  induction b with
  | zero => simp [nativeGaussianBlocksPassed]
  | succ b ih =>
      have he : nativeGaussianBlocksPassed X E n r (b + 1) =
          nativeGaussianBlocksPassed X E n r b ∩
            {ω | |nativeGaussianBlock X (n + 2 * r * b) r ω| ≤ 4 * E} := by
        ext ω
        constructor
        · intro h
          exact ⟨fun a ha => h a (by omega), h b (by omega)⟩
        · rintro ⟨h, hb⟩ a ha
          by_cases hab : a < b
          · exact h a hab
          · have : a = b := by omega
            subst a
            exact hb
      have hd : Disjoint (Set.Ico n (n + 2 * r * b))
          (Set.Ico (n + 2 * r * b) (n + 2 * r * b + 2 * r)) := by
        apply Set.disjoint_left.mpr
        intro k hk₁ hk₂
        exact not_lt_of_ge hk₂.1 hk₁.2
      have hind : Indep (incrementIndexSpace X (Set.Ico n (n + 2 * r * b)))
          (incrementIndexSpace X (Set.Ico (n + 2 * r * b) (n + 2 * r * b + 2 * r))) μ :=
        indep_iSup_of_disjoint (fun k => (hX k).comap_le) hi.iIndep hd
      have hnext : MeasurableSet[incrementIndexSpace X (Set.Ico (n + 2 * r * b) (n + 2 * r * b + 2 * r))]
          {ω | |nativeGaussianBlock X (n + 2 * r * b) r ω| ≤ 4 * E} := by
        let := incrementIndexSpace X (Set.Ico (n + 2 * r * b) (n + 2 * r * b + 2 * r))
        exact measurableSet_le (nativeGaussianBlock_measurable_in _ _ (fun _ hk => hk)).abs measurable_const
      rw [he, (Indep_iff _ _ μ).mp hind _ _
        (nativeGaussianBlocksPassed_measurable_in E n r b) hnext,
        ih, nativeGaussianBlock_probability hX hi hG E _ r, pow_succ]

theorem nativeGaussianBlocksPassed_probability_le (hX : ∀ n, Measurable (X n))
    (hi : iIndepFun X μ) (hG : ∀ n, μ.map (X n) = gaussianReal 0 1)
    {E : ℝ} (hE : 0 < E) (n r b : ℕ) (hr : 8 * E ^ 2 ≤ (r : ℝ)) :
    μ (nativeGaussianBlocksPassed X E n r b) ≤ BrownianAffine.gaussianBlockPass ^ b := by
  rw [nativeGaussianBlocksPassed_probability hX hi hG E n r b]
  apply pow_le_pow_left'
  rw [← nativeGaussianBlock_probability hX hi hG E n r]
  exact nativeGaussianBlock_pass_le hX hi hG hE n r hr

end SwingRepair
