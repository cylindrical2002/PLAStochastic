import PLAStochastic.Index.GEP.Shadow.MarkMoments
import PLAStochastic.Index.Endpoint.GammaClosure

/-!
# WP3: the conditional Gamma law of every actual shadow block

After the gap path is fixed, its block boundaries are deterministic and the
marks remain independent exponentials. Thus a block containing `N ≥ 1` original
gaps has mark sum `Gamma(N,1)`. This identity is valid for arbitrary measurable
gap inputs; neither a density nor a moment assumption is needed here.
-/

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory Finset Set

theorem hasLaw_expCoord_sum (a : ℕ) {n : ℕ} (hn : 0 < n) :
    HasLaw (fun ξ => ∑ t ∈ range n, expCoord (a + t) ξ) (gammaMeasure (n : ℝ) 1)
      expSeqMeasure := by
  have hm : Measurable (fun ξ => ∑ t ∈ range n, expCoord (a + t) ξ) :=
    Finset.measurable_sum _ fun t _ => measurable_expCoord _
  refine ⟨hm.aemeasurable, Measure.ext fun A hA => ?_⟩
  rw [Measure.map_apply hm hA]
  have hind := iidSeq_expCoord.indep.precomp
    (g := fun i : Fin n => a + (i : ℕ)) (fun i j hij => Fin.val_injective (Nat.add_left_cancel hij))
  have h := measure_scaleInv_inter_sum (P := expSeqMeasure) hn
    (X := fun i : Fin n => expCoord (a + i)) (fun _ => 1) (fun _ => le_rfl)
    (fun i => by simpa only [Nat.cast_one, expMeasure] using hasLaw_expCoord (a + i))
    hind (S := Set.univ) MeasurableSet.univ (fun _ _ _ _ => Set.mem_univ _) hA
  simp only [Set.mem_univ, true_and, Set.ofPred_true, measure_univ, one_mul,
    sum_const, card_univ, Fintype.card_fin, smul_eq_mul, mul_one] at h
  convert h using 1
  congr 1
  ext ξ
  change (∑ t ∈ range n, expCoord (a + t) ξ) ∈ A ↔
    (∑ i : Fin n, expCoord (a + i) ξ) ∈ A
  rw [Fin.sum_univ_eq_sum_range (fun t => expCoord (a + t) ξ) n]

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {g : ℕ → Ω → ℝ}

omit [MeasurableSpace Ω] in
theorem hasLaw_shTri_mark_fiber (eps : ℝ) (g : ℕ → Ω → ℝ) (ℓ j : ℕ) (ω : Ω)
    (hN : 1 ≤ (epLayerSeq eps g ℓ j ω).2) :
    HasLaw (fun ξ => (shTri eps g ℓ j (ω, ξ)).2)
      (gammaMeasure ((epLayerSeq eps g ℓ j ω).2 : ℝ) 1) expSeqMeasure := by
  simpa only [shTri_mark_eq_sum_range, expCoord] using
    hasLaw_expCoord_sum (pairRank (seq (epLayerSeq eps g ℓ) ω) j) (by omega :
      0 < (epLayerSeq eps g ℓ j ω).2)

/-- Joint count/mark law, with no condition on the distribution of the gap input. -/
theorem measure_shTri_mark_count [SFinite P] (hg : ∀ t, Measurable (g t))
    (eps : ℝ) (ℓ j : ℕ) {m : ℕ} (hm : 1 ≤ m) {A : Set ℝ} (hA : MeasurableSet A) :
    shP P {p | (shTri eps g ℓ j p).2 ∈ A ∧ (epLayerSeq eps g ℓ j p.1).2 = m} =
      P {ω | (epLayerSeq eps g ℓ j ω).2 = m} * gammaMeasure (m : ℝ) 1 A := by
  have hN : Measurable (fun ω => (epLayerSeq eps g ℓ j ω).2) :=
    (measurable_epLayerSeq_entry hg eps ℓ j).snd
  have hB : MeasurableSet {ω | (epLayerSeq eps g ℓ j ω).2 = m} := hN (measurableSet_singleton m)
  have hS : MeasurableSet {p : Ω × (ℕ → ℝ) |
      (shTri eps g ℓ j p).2 ∈ A ∧ (epLayerSeq eps g ℓ j p.1).2 = m} :=
    ((measurable_shTri hg eps ℓ j).snd hA).inter (hB.preimage measurable_fst)
  rw [shP, Measure.prod_apply hS]
  have hfiber : (fun ω => expSeqMeasure ((Prod.mk ω) ⁻¹'
      {p : Ω × (ℕ → ℝ) | (shTri eps g ℓ j p).2 ∈ A ∧
        (epLayerSeq eps g ℓ j p.1).2 = m})) =
      {ω | (epLayerSeq eps g ℓ j ω).2 = m}.indicator (fun _ => gammaMeasure (m : ℝ) 1 A) := by
    funext ω
    by_cases hω : (epLayerSeq eps g ℓ j ω).2 = m
    · rw [Set.indicator_of_mem (show ω ∈ {ω | (epLayerSeq eps g ℓ j ω).2 = m} from hω)]
      have h := (hasLaw_shTri_mark_fiber eps g ℓ j ω (hω ▸ hm)).measure_eq
        (p := fun x => x ∈ A) hA
      simpa only [Set.preimage, Set.mem_ofPred_eq, hω, and_true, Set.ofPred_mem_eq] using h
    · rw [Set.indicator_of_notMem (show ω ∉ {ω | (epLayerSeq eps g ℓ j ω).2 = m} from hω)]
      have hempty : (Prod.mk ω) ⁻¹'
          {p : Ω × (ℕ → ℝ) | (shTri eps g ℓ j p).2 ∈ A ∧
            (epLayerSeq eps g ℓ j p.1).2 = m} = ∅ := by
        ext ξ; simp [hω]
      rw [hempty, measure_empty]
  rw [hfiber, lintegral_indicator_const hB, mul_comm]

/-- The mark/count projection has a Gamma kernel at every layer. -/
theorem gammaKernel_shTri [IsProbabilityMeasure P] (hg : ∀ t, Measurable (g t))
    (eps : ℝ) (ℓ : ℕ) :
    GammaKernel (shP P) (fun j p => ((shTri eps g ℓ j p).2, (shTri eps g ℓ j p).1.2)) := by
  intro m A hA hm
  simp only [shTri_fst_eq_actual]
  rw [measure_shTri_mark_count hg eps ℓ 0 hm hA]
  congr 1
  have hB : MeasurableSet {ω | (epLayerSeq eps g ℓ 0 ω).2 = m} :=
    (measurable_epLayerSeq_entry hg eps ℓ 0).snd (measurableSet_singleton m)
  exact ((measurePreserving_fst : MeasurePreserving Prod.fst (shP P) P).measure_preimage hB.nullMeasurableSet).symm

end

end PGM
