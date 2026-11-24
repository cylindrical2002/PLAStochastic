import PLAStochastic.Index.GEP.Shadow.Defs

/-!
# WP3: synchronization on the same stopping tree

The active stopping time is adapted to the filtration of the full iid pairs, so
the centered differences have independent increments even when the two entries
of each pair are dependent.  The existing stopped-square estimate therefore gives
`E[(X⁺ - Y⁺)²] ≤ E[(X - Y)²] / C`, with integrability and for unbounded stopping
times of finite mean.  This is the inequality needed for contraction of the
shadow error.  The exact equality (MS) of `memory-route.md` §2 is not asserted here.
-/

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory Set Finset
open scoped ENNReal

variable {Ω E : Type*} [mΩ : MeasurableSpace Ω] [MeasurableSpace E]
variable {P : Measure Ω} {W : ℕ → Ω → E}

/-- The past of an iid sequence with values in an arbitrary measurable space. -/
def IIDSeqE.filtration (h : IIDSeqE P W) : Filtration ℕ mΩ where
  seq t := ⨆ s ∈ Set.Iio t, MeasurableSpace.comap (W s) inferInstance
  mono' := fun _ _ hst => biSup_mono fun _ hs => lt_of_lt_of_le hs hst
  le' := fun _ => iSup₂_le fun s _ => (h.measurable s).comap_le

theorem IIDSeqE.measurable_lt (h : IIDSeqE P W) {s t : ℕ} (hst : s < t) :
    Measurable[h.filtration t] (W s) :=
  (comap_measurable (W s)).mono (le_iSup₂ (f := fun s (_ : s ∈ Set.Iio t) =>
    MeasurableSpace.comap (W s) inferInstance) s hst) le_rfl

/-- Applying a measurable real function to each iid entry gives independent increments
for the full sequence filtration, not just for the transformed sequence. -/
theorem IIDSeqE.indepIncrements (h : IIDSeqE P W) (f : E → ℝ) (hf : Measurable f) :
    IndepIncrements P h.filtration (fun t ω => f (W t ω)) where
  measurable t := hf.comp (h.measurable_lt (Nat.lt_succ_self t))
  indep t := by
    have hd : Disjoint ({t} : Set ℕ) (Set.Iio t) := by simp
    have hind := indep_iSup_of_disjoint (fun k => (h.measurable k).comap_le) h.indep.iIndep hd
    simp only [Set.mem_singleton_iff, iSup_iSup_eq_left] at hind
    exact indep_of_indep_of_le_left hind (hf.comp (comap_measurable (W t))).comap_le

/-- A measurable observable has the same integral at every entry. -/
theorem IIDSeqE.integral_comp (h : IIDSeqE P W) {f : E → ℝ} (hf : Measurable f) (t : ℕ) :
    ∫ ω, f (W t ω) ∂P = ∫ ω, f (W 0 ω) ∂P :=
  ((h.ident t).comp hf).integral_eq

variable {V : ℕ → Ω → ℝ × ℝ}

/-- Active stopping is predictable for the filtration of both active and passive entries. -/
theorem IIDSeqE.actLen_stopping (h : IIDSeqE P V) (eps : ℝ) (t : ℕ) :
    MeasurableSet[h.filtration t] {ω | (t : ℕ∞) < actLen eps V ω} := by
  have hle : gapFiltration (fun s ω => (V s ω).1)
      (fun s => (h.measurable s).fst) t ≤ h.filtration t :=
    iSup₂_le fun _ hs => (h.measurable_lt hs).fst.comap_le
  exact hle _ (gapSegLen_lt_measurable (fun s => (h.measurable s).fst) eps t)

/-- Wald's identity for any integrable observable of the pairs, stopped by the active
tree. In particular, normalization by `C` preserves the mean of either coordinate. -/
theorem IIDSeqE.actStopped_integral (h : IIDSeqE P V) (eps : ℝ)
    {f : ℝ × ℝ → ℝ} (hf : Measurable f) (hi : Integrable (fun ω => f (V 0 ω)) P)
    (hfin : ∀ᵐ ω ∂P, actLen eps V ω ≠ ⊤)
    (hT : Integrable (fun ω => ((actLen eps V ω).toNat : ℝ)) P)
    (hC : actMean eps P V ≠ 0) :
    Integrable (fun ω => (∑ t ∈ range (actLen eps V ω).toNat, f (V t ω)) /
      actMean eps P V) P ∧
    ∫ ω, (∑ t ∈ range (actLen eps V ω).toNat, f (V t ω)) / actMean eps P V ∂P =
      ∫ ω, f (V 0 ω) ∂P := by
  let Z : ℕ → Ω → ℝ := fun t ω => f (V t ω)
  have hZ := h.indepIncrements f hf
  have hZi : ∀ t, Integrable (Z t) P := fun t => ((h.ident t).comp hf).integrable_iff.mpr hi
  have hZa : ∀ t, ∫ ω, |Z t ω| ∂P ≤ ∫ ω, |Z 0 ω| ∂P :=
    fun t => (h.integral_comp (continuous_abs.measurable.comp hf) t).le
  have hZT := lintegral_enat_eq_ofReal_integral hfin hT
  have hTfin : ∫⁻ ω, (actLen eps V ω : ℝ≥0∞) ∂P ≠ ⊤ := by
    rw [hZT]
    exact ENNReal.ofReal_ne_top
  have heq : (fun ω => ∑ t ∈ range (actLen eps V ω).toNat, Z t ω) =ᵐ[P]
      fun ω => ∑' t : ℕ, {ω | (t : ℕ∞) < actLen eps V ω}.indicator (Z t) ω := by
    filter_upwards [hfin] with ω hω
    exact ((wald_hasSum_indicator Z (ENat.natCast_toNat hω).symm).tsum_eq).symm
  have hI := (wald_integrable hZ (h.actLen_stopping eps) hZi hZa hTfin).congr heq.symm
  refine ⟨hI.div_const _, ?_⟩
  rw [integral_div, integral_congr_ae heq,
    wald_integral hZ (h.actLen_stopping eps) hZi (h.integral_comp hf) hZa hTfin,
    hZT, ENNReal.toReal_ofReal (integral_toNat_nonneg _)]
  change (∫ ω, f (V 0 ω) ∂P) * actMean eps P V / actMean eps P V = _
  exact mul_div_cancel_right₀ _ hC

/-- Same-tree error contraction, with no independence requirement within a pair.
The hypotheses require only equal means, square-integrable entries and a finite-mean
active stopping time.  Both sums use the active tree. -/
theorem sameTree_sq_integral_le [IsProbabilityMeasure P] (h : IIDSeqE P V) (eps : ℝ)
    (hX : MemLp (fun ω => (V 0 ω).1) 2 P) (hY : MemLp (fun ω => (V 0 ω).2) 2 P)
    (hmean : ∫ ω, (V 0 ω).1 ∂P = ∫ ω, (V 0 ω).2 ∂P)
    (hfin : ∀ᵐ ω ∂P, actLen eps V ω ≠ ⊤)
    (hT : Integrable (fun ω => ((actLen eps V ω).toNat : ℝ)) P)
    (hC : 0 < actMean eps P V) :
    Integrable (fun ω => (stopSum eps (fun t => (V t ω).1) / actMean eps P V -
      actSum eps V ω / actMean eps P V) ^ 2) P ∧
    ∫ ω, (stopSum eps (fun t => (V t ω).1) / actMean eps P V -
      actSum eps V ω / actMean eps P V) ^ 2 ∂P ≤
        (∫ ω, ((V 0 ω).1 - (V 0 ω).2) ^ 2 ∂P) / actMean eps P V := by
  let Z : ℕ → Ω → ℝ := fun t ω => (V t ω).1 - (V t ω).2
  have hf : Measurable (fun p : ℝ × ℝ => p.1 - p.2) := measurable_fst.sub measurable_snd
  have hZ := h.indepIncrements _ hf
  have hZ2 : ∀ t, MemLp (Z t) 2 P := fun t =>
    ((h.ident t).comp hf).memLp_iff.mpr (hX.sub hY)
  have hZ0 : ∀ t, ∫ ω, Z t ω ∂P = 0 := by
    intro t
    rw [show (∫ ω, Z t ω ∂P) = ∫ ω, Z 0 ω ∂P from h.integral_comp hf t]
    exact (integral_sub (hX.integrable one_le_two) (hY.integrable one_le_two)).trans
      (sub_eq_zero.mpr hmean)
  have hvar : ∀ t, ∫ ω, Z t ω ^ 2 ∂P ≤ ∫ ω, Z 0 ω ^ 2 ∂P := by
    intro t
    exact (h.integral_comp (hf.pow_const 2) t).le
  obtain ⟨hI, hbound⟩ := stoppedSumE_sq_integral_le hZ (h.actLen_stopping eps)
    hZ2 hZ0 hvar hfin hT
  have heq : (fun ω => (stopSum eps (fun t => (V t ω).1) / actMean eps P V -
      actSum eps V ω / actMean eps P V) ^ 2) =
      fun ω => stoppedSumE Z (actLen eps V) ω ^ 2 / actMean eps P V ^ 2 := by
    funext ω
    simp only [stoppedSumE, partialSum, Z, sum_sub_distrib, stopSum, gapKeys, actSum, actLen]
    ring
  rw [heq]
  refine ⟨hI.div_const _, ?_⟩
  rw [integral_div]
  calc (∫ ω, stoppedSumE Z (actLen eps V) ω ^ 2 ∂P) / actMean eps P V ^ 2
      ≤ ((∫ ω, Z 0 ω ^ 2 ∂P) * actMean eps P V) / actMean eps P V ^ 2 :=
        div_le_div_of_nonneg_right hbound (sq_nonneg _)
    _ = (∫ ω, ((V 0 ω).1 - (V 0 ω).2) ^ 2 ∂P) / actMean eps P V := by
      dsimp only [Z]
      field_simp

end

end PGM
