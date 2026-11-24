import PLAStochastic.Swing.FrozenCarry.DurationTail.BridgeConstraint
import PLAStochastic.Swing.Gaussian.Survival.FiniteToInfinite

/-! Pathwise lower-band and upper-band sandwich for the actual frozen duration. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology Classical
namespace SwingRepair
set_option backward.isDefEq.respectTransparency false
variable {Ω : Type*} {X : ℕ → Ω → ℝ}

def frozenInteriorGood (X : ℕ → Ω → ℝ) (w E r : ℝ) (n : ℕ) : Set Ω :=
  {ω | ∀ j < n, |w+cumulativeSamples X j ω| ≤ r*E}

theorem frozenInteriorGood_measurable [MeasurableSpace Ω]
    (hX : ∀ n, Measurable (X n)) (w E r : ℝ) (n : ℕ) :
    MeasurableSet (frozenInteriorGood X w E r n) := by
  simp only [frozenInteriorGood, Set.ofPred_forall]
  exact MeasurableSet.iInter (fun j => MeasurableSet.iInter (fun _ =>
    measurableSet_le ((Finset.measurable_sum _ (fun k _ => hX k)).const_add w).abs measurable_const))

theorem frozenPrefixLength_lower_band_witness
    {w E r : ℝ} {n : ℕ} (hn : 0 < n) (hE : 0 ≤ E) (hr : r ≤ 2) {ω : Ω}
    (hg : ω ∈ frozenInteriorGood X w E r n)
    (hs : ω ∈ gaussianHalfLineSurvives X (w+(2-r)*E/n) ((2-r)*E/n) (n-1)) :
    (n : WithTop ℕ) ≤ frozenPrefixLength X w E ω := by
  apply (le_frozenPrefixLength_iff X w E n ω).mpr
  refine ⟨-((2-r)*E/n), ?_⟩
  intro j hj
  have hj1 := (Finset.mem_Icc.mp hj).1
  have hjn := (Finset.mem_Icc.mp hj).2
  have hs' := hs (j-1) (by omega)
  have hg' := (abs_le.mp (hg (j-1) (by omega))).2
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  have har : 0 ≤ (2-r)*E/(n : ℝ) := by positivity
  have hjr : (j : ℝ) ≤ n := by exact_mod_cast hjn
  have hja : (j : ℝ) = ((j-1 : ℕ) : ℝ)+1 := by exact_mod_cast (Nat.sub_add_cancel hj1).symm
  have han : ((2-r)*E/(n : ℝ))*(n : ℝ) = (2-r)*E := div_mul_cancel₀ _ hnr.ne'
  have haj := mul_le_mul_of_nonneg_left hjr har
  dsimp only [gaussianDriftWalk] at hs'
  constructor <;> nlinarith

theorem frozenPrefixLength_upper_band_constraint
    {w E r : ℝ} {n : ℕ} (hn : 0 < n) {ω : Ω}
    (hg : ω ∈ frozenInteriorGood X w E r n)
    (hf : (n : WithTop ℕ) ≤ frozenPrefixLength X w E ω) :
    ω ∈ gaussianHalfLineSurvives X (w+(2+r)*E/n) ((2+r)*E/n) (n-1) := by
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  obtain ⟨q, hq⟩ := (le_frozenPrefixLength_iff X w E n ω).mp hf
  have he := (hq n (Finset.mem_Icc.mpr ⟨hn, le_rfl⟩)).1
  have hg' := (abs_le.mp (hg (n-1) (by omega))).1
  have hqlo : -((2+r)*E/n) ≤ q := by
    rw [← neg_div]
    apply (div_le_iff₀ hnr).mpr
    nlinarith
  intro j hj
  have hu := (hq (j+1) (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)).2
  simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one] at hu
  have hp := mul_le_mul_of_nonneg_right hqlo (show 0 ≤ (j : ℝ)+1 by positivity)
  dsimp only [gaussianDriftWalk]
  nlinarith


variable [MeasurableSpace Ω] {μ : Measure Ω}

/-- The actual duration probability is bracketed by the true drifted survival probabilities. -/
theorem frozenPrefixLength_interior_probability_sandwich [IsFiniteMeasure μ]
    {w E r : ℝ} {n : ℕ} (hn : 0 < n) (hE : 0 ≤ E) (hr : r ≤ 2) :
    gaussianInfiniteSurvival X μ (w+(2-r)*E/n) ((2-r)*E/n)-
      μ.real (frozenInteriorGood X w E r n)ᶜ ≤
        μ.real {ω | (n : WithTop ℕ) ≤ frozenPrefixLength X w E ω} ∧
    μ.real {ω | (n : WithTop ℕ) ≤ frozenPrefixLength X w E ω} ≤
      μ.real (gaussianHalfLineSurvives X (w+(2+r)*E/n) ((2+r)*E/n) (n-1))+
        μ.real (frozenInteriorGood X w E r n)ᶜ := by
  constructor
  · apply le_trans (le_measureReal_sdiff (μ := μ) (s₁ :=
      {ω | gaussianHalfLineExit X (w+(2-r)*E/n) ((2-r)*E/n) ω = ⊤}) (s₂ :=
      (frozenInteriorGood X w E r n)ᶜ))
    refine measureReal_mono ?_ (measure_ne_top μ _)
    rintro ω ⟨hs, hg⟩
    apply frozenPrefixLength_lower_band_witness hn hE hr (not_not.mp hg)
    apply (lt_gaussianHalfLineExit_iff _ _ _ _ _).mp
    rw [hs]
    exact WithTop.coe_lt_top _
  · apply le_trans (measureReal_mono ?_ (measure_ne_top μ _)) (measureReal_union_le _ _)
    intro ω hω
    by_cases hg : ω ∈ frozenInteriorGood X w E r n
    · exact Or.inl (frozenPrefixLength_upper_band_constraint hn hg hω)
    · exact Or.inr hg

end SwingRepair
