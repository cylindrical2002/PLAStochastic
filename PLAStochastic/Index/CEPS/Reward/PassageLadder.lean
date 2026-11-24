import PLAStochastic.Index.CEPS.Reward.MarkovSplit
import PLAStochastic.ForMathlib.Probability.RandomWalk.WienerHopf.LadderHeight

/-! # The first-passage reward as a first-ladder integral

For bounded exponential marks, deterministic-time independence and the
actual ladder density give the probabilistic renewal expression.
-/

noncomputable section
open MeasureTheory Set Complex Filter
namespace PGM.WienerHopf

def passageContinuation (s a : ℂ) (x : ℝ) (p : ℝ × (ℕ → ℝ)) : ℂ :=
  if x < p.1 then cexp (-a * (p.1 - x : ℝ)) else passageReward s a (x - p.1) p.2

theorem measurable_passageContinuation (s a : ℂ) (x : ℝ) :
    Measurable (passageContinuation s a x) :=
  Measurable.ite (measurableSet_lt measurable_const measurable_fst)
    (by fun_prop) ((measurable_passageReward s a).comp
      ((measurable_const.sub measurable_fst).prodMk measurable_snd))

theorem norm_passageContinuation_le_one {s a : ℂ} (hs : ‖s‖ ≤ 1) (ha : 0 ≤ a.re)
    (x : ℝ) (p : ℝ × (ℕ → ℝ)) : ‖passageContinuation s a x p‖ ≤ 1 := by
  unfold passageContinuation
  split_ifs with h
  · rw [norm_exp]
    apply Real.exp_le_one_iff.mpr
    simp only [mul_re, neg_re, neg_im, ofReal_re, ofReal_im, mul_zero, sub_zero]
    exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr ha) (by linarith)
  · exact norm_passageReward_le_one hs ha _ _

variable {ρ : Measure ℝ} [IsProbabilityMeasure ρ]

theorem passageContinuation_integral (s a : ℂ) (x h : ℝ) :
    (∫ η, passageContinuation s a x (h, η) ∂pathLaw ρ) =
      if x < h then cexp (-a * (h - x : ℝ)) else passageTransform ρ s a (x - h) := by
  by_cases hh : x < h
  · simp [passageContinuation, hh]
  · simp only [passageContinuation, hh, if_false, passageTransform]

theorem passageTransform_eq_ladder_integral {f : ℝ → ℝ}
    (hf0 : ∀ y, 0 ≤ f y) (hfm : Measurable f)
    (hρ : ρ = volume.withDensity (fun y => ENNReal.ofReal (f y)))
    {s a : ℂ} (hs : ‖s‖ ≤ 1) (ha : 0 ≤ a.re) {x : ℝ} (hx : 0 ≤ x) :
    passageTransform ρ s a x = ∫ h : ℝ, ladderDensity ρ f (Ioi 0) s h *
      (if x < h then cexp (-a * (h - x : ℝ)) else passageTransform ρ s a (x - h)) := by
  let H := passageContinuation s a x
  let φ : ℝ → ℂ := fun h => ∫ η, H (h, η) ∂pathLaw ρ
  have hH : Measurable H := measurable_passageContinuation s a x
  have hHu : StronglyMeasurable (Function.uncurry (fun h η => H (h, η))) := hH.stronglyMeasurable
  have hφ : Measurable φ := hHu.integral_prod_right.measurable
  have hφB : ∀ h, ‖φ h‖ ≤ 1 := by
    intro h
    have hi : Integrable (fun η => H (h, η)) (pathLaw ρ) :=
      (integrable_const (1 : ℝ)).mono'
        (hH.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable
        (Eventually.of_forall fun η => norm_passageContinuation_le_one hs ha x (h, η))
    apply (norm_integral_le_integral_norm _).trans
    calc
      _ ≤ ∫ _ : ℕ → ℝ, (1 : ℝ) ∂pathLaw ρ := integral_mono hi.norm
        (integrable_const _) (fun η => norm_passageContinuation_le_one hs ha x (h, η))
      _ = 1 := by simp
  have hR := integrable_passageReward (ρ := ρ) hs ha x
  have heq : passageTransform ρ s a x =
      ∫ ω in {ω | firstEntry (Ioi 0) ω < ⊤},
        s ^ (firstEntry (Ioi 0) ω).toNat * φ (entryValue (Ioi 0) ω) ∂pathLaw ρ := by
    rw [setIntegral_entry_eq_tsum measurableSet_Ioi hs hφ hφB]
    have ht : passageTransform ρ s a x =
        ∫ ω in {ω | firstEntry (Ioi 0) ω < ⊤}, passageReward s a x ω ∂pathLaw ρ := by
      apply (setIntegral_eq_integral_of_forall_compl_eq_zero _).symm
      intro ω hω
      exact passageReward_eq_of_asc_top hx (not_lt_top_iff.mp hω)
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
        exact passageReward_split hx hω
      _ = s ^ n * ∫ ω in {ω | firstEntry (Ioi 0) ω = (n : ℕ∞)},
          H (partialSum n ω, shift n ω) ∂pathLaw ρ := integral_const_mul _ _
      _ = _ := by
        rw [setIntegral_ladder_shift n hH zero_le_one (norm_passageContinuation_le_one hs ha x)]
  rw [heq, setIntegral_entry_eq_integral_ladderDensity measurableSet_Ioi hf0 hfm hρ hs hφ hφB]
  apply integral_congr_ae (Eventually.of_forall fun h => ?_)
  dsimp [φ, H]
  rw [passageContinuation_integral]

end PGM.WienerHopf
