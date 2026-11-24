import PLAStochastic.Index.CEPS.Reward.MarkovSplit
import PLAStochastic.Index.CEPS.Reward.BoundedPassage
import PLAStochastic.ForMathlib.Probability.RandomWalk.WienerHopf.LadderHeight

/-! # The first-passage reward as a first-ladder integral

For bounded measurable overshoot tests, deterministic-time independence and the
actual ladder density give the probabilistic renewal expression.
-/

noncomputable section
open MeasureTheory Set Complex Filter
namespace PGM.WienerHopf

def passageTestContinuation (s : ℂ) (φ : ℝ → ℂ) (x : ℝ) (p : ℝ × (ℕ → ℝ)) : ℂ :=
  if x < p.1 then φ (p.1 - x) else passageTestReward s φ (x - p.1) p.2

theorem measurable_passageTestContinuation (s : ℂ) {φ : ℝ → ℂ}
    (hφ : Measurable φ) (x : ℝ) :
    Measurable (passageTestContinuation s φ x) :=
  Measurable.ite (measurableSet_lt measurable_const measurable_fst)
    (hφ.comp (measurable_fst.sub measurable_const)) ((measurable_passageTestReward s hφ).comp
      ((measurable_const.sub measurable_fst).prodMk measurable_snd))

theorem norm_passageTestContinuation_le {s : ℂ} (hs : ‖s‖ ≤ 1) {φ : ℝ → ℂ}
    {B : ℝ} (hB : 0 ≤ B) (hφB : ∀ y, ‖φ y‖ ≤ B) (x : ℝ)
    (p : ℝ × (ℕ → ℝ)) : ‖passageTestContinuation s φ x p‖ ≤ B := by
  unfold passageTestContinuation
  split_ifs
  · exact hφB _
  · exact norm_passageTestReward_le hs hB hφB _ _

variable {ρ : Measure ℝ} [IsProbabilityMeasure ρ]

theorem passageTestContinuation_integral (s : ℂ) (φ : ℝ → ℂ) (x h : ℝ) :
    (∫ η, passageTestContinuation s φ x (h, η) ∂pathLaw ρ) =
      if x < h then φ (h - x) else passageTestTransform ρ s φ (x - h) := by
  by_cases hh : x < h
  · simp [passageTestContinuation, hh]
  · simp only [passageTestContinuation, hh, if_false, passageTestTransform]

theorem passageTestTransform_eq_ladder_integral {f : ℝ → ℝ}
    (hf0 : ∀ y, 0 ≤ f y) (hfm : Measurable f)
    (hρ : ρ = volume.withDensity (fun y => ENNReal.ofReal (f y)))
    {s : ℂ} (hs : ‖s‖ ≤ 1) {φ : ℝ → ℂ} (hφ : Measurable φ)
    {B : ℝ} (hB : 0 ≤ B) (hφB : ∀ y, ‖φ y‖ ≤ B) {x : ℝ} (hx : 0 ≤ x) :
    passageTestTransform ρ s φ x = ∫ h : ℝ, ladderDensity ρ f (Ioi 0) s h *
      (if x < h then φ (h - x) else passageTestTransform ρ s φ (x - h)) := by
  let H := passageTestContinuation s φ x
  let Φ : ℝ → ℂ := fun h => ∫ η, H (h, η) ∂pathLaw ρ
  have hH : Measurable H := measurable_passageTestContinuation s hφ x
  have hHu : StronglyMeasurable (Function.uncurry (fun h η => H (h, η))) := hH.stronglyMeasurable
  have hΦ : Measurable Φ := hHu.integral_prod_right.measurable
  have hΦB : ∀ h, ‖Φ h‖ ≤ B := by
    intro h
    have hi : Integrable (fun η => H (h, η)) (pathLaw ρ) :=
      (integrable_const B).mono'
        (hH.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable
        (Eventually.of_forall fun η => norm_passageTestContinuation_le hs hB hφB x (h, η))
    apply (norm_integral_le_integral_norm _).trans
    calc
      _ ≤ ∫ _ : ℕ → ℝ, B ∂pathLaw ρ := integral_mono hi.norm
        (integrable_const _) (fun η => norm_passageTestContinuation_le hs hB hφB x (h, η))
      _ = B := by simp
  have hR := integrable_passageTestReward (ρ := ρ) hs hφ hB hφB x
  have heq : passageTestTransform ρ s φ x =
      ∫ ω in {ω | firstEntry (Ioi 0) ω < ⊤},
        s ^ (firstEntry (Ioi 0) ω).toNat * Φ (entryValue (Ioi 0) ω) ∂pathLaw ρ := by
    rw [setIntegral_entry_eq_tsum measurableSet_Ioi hs hΦ hΦB]
    have ht : passageTestTransform ρ s φ x =
        ∫ ω in {ω | firstEntry (Ioi 0) ω < ⊤}, passageTestReward s φ x ω ∂pathLaw ρ := by
      apply (setIntegral_eq_integral_of_forall_compl_eq_zero _).symm
      intro ω hω
      exact passageTestReward_eq_of_asc_top hx (not_lt_top_iff.mp hω)
    rw [ht, setOf_firstEntry_lt_top_eq_iUnion,
      integral_iUnion (fun n => measurableSet_firstEntry_eq measurableSet_Ioi n)
        (pairwise_disjoint_firstEntry_eq (Ioi 0)) hR.integrableOn]
    apply tsum_congr
    intro n
    calc
      _ = ∫ ω in {ω | firstEntry (Ioi 0) ω = (n : ℕ∞)},
          s ^ n * H (partialSum n ω, shift n ω) ∂pathLaw ρ := by
        apply setIntegral_congr_fun (measurableSet_firstEntry_eq measurableSet_Ioi n)
        intro ω hω
        exact passageTestReward_split hx hω
      _ = s ^ n * ∫ ω in {ω | firstEntry (Ioi 0) ω = (n : ℕ∞)},
          H (partialSum n ω, shift n ω) ∂pathLaw ρ := integral_const_mul _ _
      _ = _ := by
        rw [setIntegral_ladder_shift n hH hB (norm_passageTestContinuation_le hs hB hφB x)]
  rw [heq, setIntegral_entry_eq_integral_ladderDensity measurableSet_Ioi hf0 hfm hρ hs hΦ hΦB]
  apply integral_congr_ae (Eventually.of_forall fun h => ?_)
  dsimp [Φ, H]
  rw [passageTestContinuation_integral]

end PGM.WienerHopf
