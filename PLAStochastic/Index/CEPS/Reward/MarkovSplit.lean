import PLAStochastic.Index.CEPS.Reward.Passage
import PLAStochastic.ForMathlib.Probability.RandomWalk.WienerHopf.Renewal

/-! # Fixed-time Markov splitting on a ladder-epoch event -/

noncomputable section
open MeasureTheory ProbabilityTheory Set Complex Filter
namespace PGM.WienerHopf

variable {ρ : Measure ℝ} [IsProbabilityMeasure ρ]

/-- Independence is used only at the deterministic time `n`; the event is a prefix event. -/
theorem setIntegral_ladder_shift (n : ℕ) {H : ℝ × (ℕ → ℝ) → ℂ}
    (hH : Measurable H) {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ p, ‖H p‖ ≤ C) :
    (∫ ω in {ω | firstEntry (Ioi 0) ω = (n : ℕ∞)},
      H (partialSum n ω, shift n ω) ∂pathLaw ρ) =
    ∫ ω in {ω | firstEntry (Ioi 0) ω = (n : ℕ∞)},
      (∫ η, H (partialSum n ω, η) ∂pathLaw ρ) ∂pathLaw ρ := by
  let F : (ℕ → ℝ) → (ℕ → ℝ) := fun ω => extendPrefix n (seqPrefix n ω)
  have hF : Measurable F := (measurable_extendPrefix n).comp (measurable_seqPrefix n)
  have hFd : DependsOnPrefix n F := by
    intro ω ω' h
    apply congrArg (extendPrefix n)
    funext i
    exact h i i.isLt
  let Φ : (ℕ → ℝ) × (ℕ → ℝ) → ℂ := fun p =>
    if firstEntry (Ioi 0) p.1 = (n : ℕ∞) then H (partialSum n p.1, p.2) else 0
  have hΦ : Measurable Φ :=
    Measurable.ite ((measurableSet_firstEntry_eq measurableSet_Ioi n).preimage measurable_fst)
      (hH.comp (((measurable_partialSum n).comp measurable_fst).prodMk measurable_snd))
      measurable_const
  have hΦb : ∀ p, ‖Φ p‖ ≤ C := by
    intro p
    dsimp [Φ]
    split_ifs
    · exact hC _
    · simpa using hC0
  have hΦi : Integrable Φ (((pathLaw ρ).map F).prod (pathLaw ρ)) :=
    (integrable_const C).mono' hΦ.aestronglyMeasurable (Eventually.of_forall hΦb)
  have hi := indepFun_of_dependsOnPrefix (ρ := ρ) hF hFd measurable_id
  have hmap := hi.map_prod_eq_prod_map_map hF.aemeasurable (measurable_shift n).aemeasurable
  change (pathLaw ρ).map (fun ω => (F ω, shift n ω)) =
    ((pathLaw ρ).map F).prod ((pathLaw ρ).map (shift n)) at hmap
  rw [(measurePreserving_shift n).map_eq] at hmap
  have heq : (∫ ω, Φ (F ω, shift n ω) ∂pathLaw ρ) =
      ∫ ω, ∫ η, Φ (F ω, η) ∂pathLaw ρ ∂pathLaw ρ := by
    rw [← integral_map (hF.prodMk (measurable_shift n)).aemeasurable hΦ.aestronglyMeasurable,
      hmap, integral_prod Φ hΦi,
      integral_map hF.aemeasurable hΦ.stronglyMeasurable.integral_prod_right.aestronglyMeasurable]
  have hSn : ∀ ω, partialSum n (F ω) = partialSum n ω := fun ω =>
    (dependsOnPrefix_partialSum n).eq_comp ω |>.symm
  have hEn : ∀ ω, firstEntry (Ioi 0) (F ω) = (n : ℕ∞) ↔
      firstEntry (Ioi 0) ω = (n : ℕ∞) := fun ω =>
    firstEntry_eq_congr (fun _ hi => extendPrefix_seqPrefix_apply hi ω)
  rw [← integral_indicator (measurableSet_firstEntry_eq measurableSet_Ioi n),
    ← integral_indicator (measurableSet_firstEntry_eq measurableSet_Ioi n)]
  calc
    _ = ∫ ω, Φ (F ω, shift n ω) ∂pathLaw ρ := by
      refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
      simp only [Φ, hSn, hEn, indicator, mem_ofPred_eq]
    _ = _ := heq
    _ = _ := by
      refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
      dsimp [Φ]
      simp only [hSn, hEn]
      by_cases hω : firstEntry (Ioi 0) ω = (n : ℕ∞)
      · simp only [hω, if_true, indicator_of_mem
          (show ω ∈ {ω | firstEntry (Ioi 0) ω = (n : ℕ∞)} from hω)]
      · simp only [hω, if_false, integral_zero, indicator_of_notMem
          (show ω ∉ {ω | firstEntry (Ioi 0) ω = (n : ℕ∞)} from hω)]

end PGM.WienerHopf
