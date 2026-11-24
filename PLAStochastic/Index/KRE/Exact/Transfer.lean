import PLAStochastic.Index.KRE.Exact.Main

/-! # The exact height law on sorted iid Model K samples -/

namespace PGM
noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology
universe u

theorem identDistrib_reHeight_kKeys {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
    {f : ℝ → ℝ} {fmin fmax Lf eps : ℝ} {n : ℕ} (hf : DensityK f 0 1 fmin fmax Lf)
    {X : ℕ → Ω → ℝ} (hX : ∀ i, HasLaw (X i) (densityLaw f 0 1) P) (hind : iIndepFun X P) :
    IdentDistrib (fun ω => reHeight eps (kKeys X n ω) n)
      (fun ω => reHeight eps (renyiKeys f n ω) n) P expSeqMeasure := by
  have hXn : iIndepFun (fun i : Fin n => X i) P := hind.precomp Fin.val_injective
  have hEn : iIndepFun (fun j : Fin (n + 1) => expCoord j) expSeqMeasure :=
    iidSeq_expCoord.indep.precomp Fin.val_injective
  have hid := identDistrib_sortVec_quantK_gammaRatio hf (fun i : Fin n => hX i) hXn
    (fun j : Fin (n + 1) => hasLaw_expCoord j) hEn
  have hH := hid.comp (measurable_reHeight_extendKeys eps n)
  refine hH.trans (IdentDistrib.of_ae_eq hH.aemeasurable_snd ?_)
  apply Filter.Eventually.of_forall
  intro ω
  simp only [Function.comp_def]
  apply reHeight_congr
  intro i hi
  rw [extendKeys_of_lt _ hi]
  simp only [Renyi.gammaRatio]
  rw [gammaSum_expCoord ω (k := i + 1) (by omega), gammaSum_expCoord ω le_rfl]
  rfl

/-- The sorted iid sample has the same exact integer height with failure
probability at most `63/N²`, outside the two windows. -/
theorem K_RE_exact_probability {f : ℝ → ℝ} {fmin fmax Lf : ℝ}
    (hf : DensityK f 0 1 fmin fmax Lf)
    (hnc : ∃ x ∈ Set.Icc (0 : ℝ) 1, ∃ y ∈ Set.Icc (0 : ℝ) 1, f x ≠ f y) :
    ∃ K : ℝ, 0 < K ∧ ∀ {N : ℕ → ℕ} {ε : ℕ → ℝ},
      Tendsto (fun k => (N k : ℝ)) atTop atTop → Tendsto ε atTop atTop →
      Tendsto (fun k => Real.log (ε k) / Real.log (N k)) atTop (𝓝 0) →
      ∀ᶠ k in atTop, ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω)
        [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ),
        (∀ i, HasLaw (X i) (densityLaw f 0 1) P) → iIndepFun X P →
        KREOutside (kreZ (N k) (ε k)) (greW K (N k) (ε k)) →
        P.real {ω | reHeight (ε k) (kKeys X (N k) ω) (N k) ≠
          kreExactHeight (kreZ (N k) (ε k))} ≤ 63 / (N k : ℝ) ^ 2 := by
  obtain ⟨K, hK, h⟩ := K_RE_exact hf hnc
  refine ⟨K, hK, fun {N ε} hN hε hεN => ?_⟩
  filter_upwards [h hN hε hεN] with k hk
  intro Ω _ P _ X hX hind hwin
  obtain ⟨E, _, hbad, hgood⟩ := hk
  have hid := identDistrib_reHeight_kKeys (eps := ε k) (n := N k) hf hX hind
  have hlaw := hid.measure_mem_eq (s := {j : ℕ | j ≠ kreExactHeight (kreZ (N k) (ε k))})
    ((Set.to_countable _).measurableSet)
  have hreal := congrArg ENNReal.toReal hlaw
  change P.real {ω | reHeight (ε k) (kKeys X (N k) ω) (N k) ≠ _} =
    expSeqMeasure.real {ω | reHeight (ε k) (renyiKeys f (N k) ω) (N k) ≠ _} at hreal
  rw [hreal]
  apply le_trans (measureReal_mono ?_) hbad
  intro ω hω hE
  exact hω (hgood ω hE hwin)

end
end PGM
