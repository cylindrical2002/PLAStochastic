import PLAStochastic.Swing.Restart.MaximalPrefix.ConditionalBlocks

noncomputable section
open MeasureTheory ProbabilityTheory Set
namespace SwingRepair
set_option backward.isDefEq.respectTransparency false

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω}

/-- Fresh independent future and past coordinates remain independent after adjoining
an arbitrary history independent of their entire joint sigma-algebra. -/
theorem indep_sup_history [IsProbabilityMeasure μ]
    {f p h : MeasurableSpace Ω} (hf : f ≤ mΩ) (hp : p ≤ mΩ) (hh : h ≤ mΩ)
    (hfp : Indep f p μ) (hhist : Indep (f ⊔ p) h μ) : Indep f (h ⊔ p) μ := by
  let : MeasurableSpace Ω := mΩ
  let P : Set (Set Ω) := {s | ∃ a, MeasurableSet[h] a ∧ ∃ b, MeasurableSet[p] b ∧ s = a ∩ b}
  have hP : IsPiSystem P := by
    rintro s ⟨a, ha, b, hb, rfl⟩ t ⟨c, hc, d, hd, rfl⟩ _
    refine ⟨a ∩ c, ha.inter hc, b ∩ d, hb.inter hd, ?_⟩
    ext ω
    simp only [Set.mem_inter_iff]
    tauto
  have hgen : h ⊔ p = MeasurableSpace.generateFrom P := by
    apply le_antisymm
    · apply sup_le
      · intro a ha
        exact MeasurableSpace.measurableSet_generateFrom
          ⟨a, ha, Set.univ, MeasurableSet.univ, by simp⟩
      · intro b hb
        exact MeasurableSpace.measurableSet_generateFrom
          ⟨Set.univ, MeasurableSet.univ, b, hb, by simp⟩
    · apply MeasurableSpace.generateFrom_le
      rintro s ⟨a, ha, b, hb, rfl⟩
      exact ((show h ≤ h ⊔ p from le_sup_left) a ha).inter ((show p ≤ h ⊔ p from le_sup_right) b hb)
  have hfpi : IsPiSystem {s : Set Ω | MeasurableSet[f] s} := by
    intro s hs t ht _
    exact hs.inter ht
  apply IndepSets.indep hf (sup_le hh hp) hfpi hP
    (@MeasurableSpace.generateFrom_measurableSet Ω f).symm hgen
  apply (IndepSets_iff _ _ μ).mpr
  rintro s t hs ⟨a, ha, b, hb, rfl⟩
  have hsb : MeasurableSet[f ⊔ p] (s ∩ b) := ((show f ≤ f ⊔ p from le_sup_left) s hs).inter ((show p ≤ f ⊔ p from le_sup_right) b hb)
  have hsbp := (Indep_iff _ _ μ).mp hfp s b hs hb
  have hab := (Indep_iff _ _ μ).mp hhist b a ((show p ≤ f ⊔ p from le_sup_right) b hb) ha
  have hsab := (Indep_iff _ _ μ).mp hhist (s ∩ b) a hsb ha
  rw [Set.inter_comm b a] at hab
  have heq : s ∩ (a ∩ b) = (s ∩ b) ∩ a := by ext ω; simp only [Set.mem_inter_iff]; tauto
  rw [heq, hsab, hsbp, hab]
  ac_rfl

/-- Independence from the actual history enlarged by all observed increments is
proved from the original iid family and its initial history independence. -/
theorem shiftedIncrements_indep_history
    {X : ℕ → Ω → ℝ} (hX : ∀ k, Measurable (X k)) (hi : iIndepFun X μ)
    {m : MeasurableSpace Ω} (hm : m ≤ mΩ)
    (hinit : Indep (incrementIndexSpace X Set.univ) m μ) (n : ℕ) :
    Indep (incrementIndexSpace (fun k => X (n + k)) Set.univ)
      (m ⊔ incrementIndexSpace X (Set.Iio n)) μ := by
  let : MeasurableSpace Ω := mΩ
  have : IsProbabilityMeasure μ := hi.isProbabilityMeasure
  have hdis : Disjoint (Set.Ici n) (Set.Iio n) := by
    apply Set.disjoint_left.mpr
    intro k hk₁ hk₂
    change n ≤ k at hk₁
    change k < n at hk₂
    omega
  have hfp : Indep (incrementIndexSpace X (Set.Ici n)) (incrementIndexSpace X (Set.Iio n)) μ :=
    indep_iSup_of_disjoint (fun k => (hX k).comap_le) hi.iIndep hdis
  have hbig : incrementIndexSpace X (Set.Ici n) ⊔ incrementIndexSpace X (Set.Iio n) ≤
      incrementIndexSpace X Set.univ :=
    sup_le (incrementIndexSpace_mono (Set.subset_univ _))
      (incrementIndexSpace_mono (Set.subset_univ _))
  have haug := indep_sup_history (incrementIndexSpace_le hX _) (incrementIndexSpace_le hX _)
    hm hfp (indep_of_indep_of_le_left hinit hbig)
  apply indep_of_indep_of_le_left haug
  apply iSup_le
  intro k
  apply iSup_le
  intro _
  exact le_iSup_of_le (n + k) (le_iSup_of_le (by simp) le_rfl)

end SwingRepair
