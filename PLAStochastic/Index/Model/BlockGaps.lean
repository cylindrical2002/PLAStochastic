import PLAStochastic.Index.Model.GapLaw
import PLAStochastic.ForMathlib.Probability.StoppedSum.PredictableWeights
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.IdentDistrib

/-!
# Block sums of iid gaps

For gaps `X` and a block length `d`, `blockGap X d j = X (j d) + ⋯ + X (j d + d - 1)` is the
sum of the `j`-th block of `d` consecutive gaps.  The walk with the block gaps is the walk
with the original gaps observed at multiples of `d` (`gapKeys_blockGap`).
-/

noncomputable section

namespace PGM

open MeasureTheory ProbabilityTheory Finset

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

/-- Sums of consecutive blocks of `d` gaps: `blockGap X d j = X (j d) + ⋯ + X (j d + d - 1)`. -/
def blockGap (X : ℕ → Ω → ℝ) (d : ℕ) : ℕ → Ω → ℝ :=
  fun j ω => ∑ i ∈ Finset.range d, X (j * d + i) ω

omit mΩ in
/-- The block walk is the walk subsampled at multiples of `d`. -/
theorem gapKeys_blockGap (X : ℕ → Ω → ℝ) (d : ℕ) (ω : Ω) (j : ℕ) :
    gapKeys (seq (blockGap X d) ω) j = gapKeys (seq X ω) (j * d) := by
  induction j with
  | zero => simp [gapKeys]
  | succ j ih =>
    simp only [gapKeys, seq, blockGap] at ih ⊢
    rw [sum_range_succ, ih, add_mul, one_mul, sum_range_add]

/-- Distinct (block, position) pairs give distinct gap indices. -/
theorem blockIndex_injective (d : ℕ) :
    Function.Injective (fun p : ℕ × Fin d => p.1 * d + (p.2 : ℕ)) := by
  rintro ⟨j, i⟩ ⟨j', i'⟩ h
  change j * d + (i : ℕ) = j' * d + (i' : ℕ) at h
  have hi := i.isLt
  have hi' := i'.isLt
  have hjj : j = j' := by
    rcases lt_trichotomy j j' with hlt | heq | hgt
    · exfalso
      have : (j + 1) * d ≤ j' * d := Nat.mul_le_mul_right d hlt
      rw [add_mul, one_mul] at this
      linarith
    · exact heq
    · exfalso
      have : (j' + 1) * d ≤ j * d := Nat.mul_le_mul_right d hgt
      rw [add_mul, one_mul] at this
      linarith
  subst hjj
  obtain rfl : i = i' := Fin.ext (by omega)
  rfl

namespace IIDSeq

variable {P : Measure Ω} {X : ℕ → Ω → ℝ}

/-- Block sums of an iid sequence over disjoint consecutive blocks are iid. -/
theorem block (h : IIDSeq P X) (d : ℕ) : IIDSeq P (blockGap X d) := by
  have hP := h.indep.isProbabilityMeasure
  set ν : Measure ℝ := P.map (X 0) with hν
  have hν1 : IsProbabilityMeasure ν := Measure.isProbabilityMeasure_map (h.measurable 0).aemeasurable
  have hmap : ∀ t, P.map (X t) = ν := fun t => (h.ident t).map_eq
  -- the block vectors
  let V : ℕ → Ω → (Fin d → ℝ) := fun j ω i => X (j * d + i) ω
  have hVm : ∀ j, Measurable (V j) := fun j => measurable_pi_lambda _ fun i => h.measurable _
  -- the gaps indexed by (block, position)
  let Z : ℕ × Fin d → Ω → ℝ := fun p => X (p.1 * d + p.2)
  have hZ : iIndepFun Z P := h.indep.precomp (blockIndex_injective d)
  have hZm : ∀ p, Measurable (Z p) := fun p => h.measurable _
  have hZlaw : P.map (fun ω p => Z p ω) = Measure.infinitePi (fun _ : ℕ × Fin d => ν) := by
    rw [hZ.map_fun_eq_infinitePi_map hZm]
    congr 1
    funext p
    exact hmap _
  have hVlaw : P.map (fun ω j => V j ω) =
      Measure.infinitePi (fun _ : ℕ => Measure.infinitePi (fun _ : Fin d => ν)) := by
    have : (fun ω j => V j ω) = (MeasurableEquiv.curry ℕ (Fin d) ℝ) ∘ (fun ω p => Z p ω) := rfl
    rw [this, ← Measure.map_map (MeasurableEquiv.measurable _) (measurable_pi_lambda _ hZm),
      hZlaw, Measure.infinitePi_map_curry (fun _ _ => ν)]
  have hVj : ∀ j, P.map (V j) = Measure.infinitePi (fun _ : Fin d => ν) := by
    intro j
    have : V j = (fun v : ℕ → Fin d → ℝ => v j) ∘ (fun ω j => V j ω) := rfl
    rw [this, ← Measure.map_map (measurable_pi_apply j) (measurable_pi_lambda _ hVm), hVlaw,
      Measure.infinitePi_map_eval]
  have hVind : iIndepFun V P := by
    rw [iIndepFun_iff_map_fun_eq_infinitePi_map hVm, hVlaw]
    congr 1
    funext j
    exact (hVj j).symm
  have hsum : ∀ j, blockGap X d j = (fun v : Fin d → ℝ => ∑ i, v i) ∘ V j := by
    intro j
    funext ω
    simp only [blockGap, Function.comp_apply, V]
    exact (Fin.sum_univ_eq_sum_range (fun i => X (j * d + i) ω) d).symm
  have hg : Measurable (fun v : Fin d → ℝ => ∑ i, v i) := by fun_prop
  refine ⟨fun j => ?_, ?_, fun j => ?_⟩
  · rw [hsum j]
    exact hg.comp (hVm j)
  · have := hVind.comp (fun _ => fun v : Fin d → ℝ => ∑ i, v i) (fun _ => hg)
    convert this using 1
    funext j
    exact hsum j
  · rw [hsum j, hsum 0]
    exact (IdentDistrib.mk (hVm j).aemeasurable (hVm 0).aemeasurable
      ((hVj j).trans (hVj 0).symm)).comp hg

end IIDSeq

omit mΩ in
/-- The centred first block is a partial sum of the centred gaps. -/
theorem blockGap_zero_sub (X : ℕ → Ω → ℝ) (d : ℕ) (μ : ℝ) (ω : Ω) :
    blockGap X d 0 ω - d * μ =
      weightedSum (fun _ _ => (1 : ℝ)) (centred X μ) d ω := by
  simp only [blockGap, weightedSum, centred, zero_mul, zero_add, one_mul, sum_sub_distrib,
    sum_const, card_range, nsmul_eq_mul]

namespace GapLaw

variable {P : Measure Ω} {X : ℕ → Ω → ℝ} {μ σ κ : ℝ}

/-- Block sums of `d ≥ 1` iid gaps form an iid gap law with mean `d μ`, variance `d σ^2`
and centred absolute third moment at most `2 d √d σ^3 + d κ`. -/
theorem block (hX : GapLaw P X μ σ κ) {d : ℕ} (hd : 1 ≤ d) :
    GapLaw P (blockGap X d) (d * μ) (Real.sqrt d * σ)
      (2 * d * Real.sqrt d * σ ^ 3 + d * κ) := by
  have hP := hX.iid.indep.isProbabilityMeasure
  have hY3 : ∀ t, MemLp (centred X μ t) 3 P := hX.memLp_centred
  have hY2 : ∀ t, MemLp (centred X μ t) 2 P := fun t => (hY3 t).mono_exponent (by norm_num)
  have hY0 : ∀ t, ∫ ω, centred X μ t ω ∂P = 0 := hX.integral_centred
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  refine ⟨hX.iid.block d, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have : blockGap X d 0 = fun ω => ∑ i ∈ range d, X i ω := by
      funext ω; simp [blockGap]
    rw [this]
    exact memLp_finsetSum _ fun i _ => hX.memLp_three i
  · simp only [blockGap, zero_mul, zero_add]
    rw [integral_finsetSum _ fun i _ => (hX.memLp_three i).integrable (by norm_num)]
    simp [hX.iid.integral_eq, hX.mean]
  · simp_rw [blockGap_zero_sub]
    rw [integral_weightedSum_sq hX.indepIncrements (PredictableWeight.one _) hY2 hY0 d]
    simp [hX.integral_centred_sq, mul_pow, Real.sq_sqrt hd0.le]
  · simp_rw [blockGap_zero_sub]
    have := integral_abs_weightedSum_cube_le_of_unit hX.indepIncrements
      (PredictableWeight.one _) (fun _ _ => by simp) hY3 hY0 hX.sigma_pos.le
      (fun t => (hX.integral_centred_sq t).le) hX.integral_centred_abs_cube d
    linarith
  · exact mul_pos hd0 hX.mu_pos
  · exact mul_pos (Real.sqrt_pos.2 hd0) hX.sigma_pos

end GapLaw

end PGM
