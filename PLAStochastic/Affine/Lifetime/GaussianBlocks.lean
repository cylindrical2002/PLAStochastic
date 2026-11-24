import PLAStochastic.Affine.Error.Attainment
import PLAStochastic.Affine.Error.TimeProcess
import PLAStochastic.Affine.Error.Measurable
import Mathlib.Probability.BrownianMotion.Basic

/-!
# Independent Gaussian three-point obstructions

The block variables and their laws are derived from the pre-Brownian hypothesis.
No independent-increment or variance conclusion is assumed separately.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace BrownianAffine

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  {B : ℝ≥0 → Ω → ℝ}

def eightIncrement (B : ℝ≥0 → Ω → ℝ) (k : ℕ) (ω : Ω) : ℝ :=
  B (8 * ((k + 1 : ℕ) : ℝ≥0)) ω - B (8 * k) ω

/-- Exactly the three-point variable used in the manuscript's exponential-tail proof. -/
def gaussianBlock (B : ℝ≥0 → Ω → ℝ) (j : ℕ) (ω : Ω) : ℝ :=
  (B (16 * j + 8) ω - (B (16 * j) ω + B (16 * j + 16) ω) / 2) / 2

omit [MeasurableSpace Ω] in
theorem gaussianBlock_eq_increments (B : ℝ≥0 → Ω → ℝ) (j : ℕ) :
    gaussianBlock B j = fun ω => (eightIncrement B (2 * j) ω -
      eightIncrement B (2 * j + 1) ω) / 4 := by
  funext ω
  unfold gaussianBlock eightIncrement
  norm_num only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
  have h₀ : (8 : ℝ≥0) * (2 * j) = 16 * j := by ring
  have h₁ : (8 : ℝ≥0) * (2 * j + 1) = 16 * j + 8 := by ring
  have h₂ : (8 : ℝ≥0) * (2 * j + 1 + 1) = 16 * j + 16 := by ring
  rw [h₀, h₁, h₂]
  ring

theorem eightIncrement_iIndepFun (hB : IsPreBrownianReal B P) :
    iIndepFun (eightIncrement B) P := by
  apply hB.hasIndepIncrements.nat (t := fun k : ℕ => 8 * (k : ℝ≥0))
  intro i j hij
  exact mul_le_mul_of_nonneg_left (Nat.cast_le.mpr hij) (by norm_num)

theorem eightIncrement_hasLaw (hB : IsPreBrownianReal B P) (k : ℕ) :
    HasLaw (eightIncrement B k) (gaussianReal 0 8) P := by
  have hvar : nndist ((8 * ((k + 1 : ℕ) : ℝ≥0) : ℝ≥0) : ℝ)
      ((8 * k : ℝ≥0) : ℝ) = 8 := by
    apply NNReal.coe_injective
    change dist ((8 * ((k + 1 : ℕ) : ℝ≥0) : ℝ≥0) : ℝ)
      ((8 * k : ℝ≥0) : ℝ) = (8 : ℝ)
    rw [Real.dist_eq]
    push_cast
    rw [show (8 : ℝ) * (k + 1) - 8 * k = 8 by ring]
    norm_num
  have h := hB.hasLaw_sub (8 * ((k + 1 : ℕ) : ℝ≥0)) (8 * k)
  convert h using 1
  congr 1
  exact congrArg (gaussianReal 0) hvar.symm

theorem gaussianBlock_hasLaw (hB : IsPreBrownianReal B P) (j : ℕ) :
    HasLaw (gaussianBlock B j) (gaussianReal 0 1) P := by
  have h₀ := eightIncrement_hasLaw hB (2 * j)
  have h₁ := eightIncrement_hasLaw hB (2 * j + 1)
  have hind := (eightIncrement_iIndepFun hB).indepFun (by omega : 2 * j ≠ 2 * j + 1)
  have hneg := gaussianReal_neg h₁
  have hsum := gaussianReal_add_gaussianReal_of_indepFun
    (hind.comp measurable_id measurable_neg) h₀.map_eq hneg.map_eq
  have hdiff : HasLaw (fun ω => eightIncrement B (2 * j) ω - eightIncrement B (2 * j + 1) ω)
      (gaussianReal 0 16) P := by
    refine ⟨h₀.aemeasurable.sub h₁.aemeasurable, ?_⟩
    simpa only [Function.comp_def, id_eq, Pi.add_def, Pi.neg_def, zero_add, neg_zero,
      sub_eq_add_neg, show (8 : ℝ≥0) + 8 = 16 by norm_num] using hsum
  rw [gaussianBlock_eq_increments]
  have hv : (16 : ℝ≥0) / ⟨(4 : ℝ) ^ 2, sq_nonneg _⟩ = 1 := by
    have hm : (⟨(4 : ℝ) ^ 2, sq_nonneg _⟩ : ℝ≥0) = 16 := by
      apply Subtype.ext
      norm_num
    rw [hm]
    norm_num
  convert gaussianReal_div_const hdiff 4 using 1
  congr 1
  · simp
  · exact hv.symm

/-- The entire block process is jointly Gaussian, as a finite linear transform of B. -/
theorem gaussianBlock_isGaussianProcess (hB : IsPreBrownianReal B P) :
    IsGaussianProcess (gaussianBlock B) P := by
  classical
  apply hB.isGaussianProcess.of_isGaussianProcess
  intro j
  refine ⟨{(16 : ℝ≥0) * j, (16 : ℝ≥0) * j + 8, (16 : ℝ≥0) * j + 16},
    { toFun := fun x => (x ⟨16 * j + 8, by simp⟩ -
          (x ⟨16 * j, by simp⟩ + x ⟨16 * j + 16, by simp⟩) / 2) / 2
      map_add' := by intro x y; simp only [Pi.add_apply]; ring
      map_smul' := by intro c x; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring }, ?_⟩
  intro ω
  rfl

theorem gaussianBlock_indepFun (hB : IsPreBrownianReal B P) {i j : ℕ} (hij : i ≠ j) :
    IndepFun (gaussianBlock B i) (gaussianBlock B j) P := by
  have hpair := (eightIncrement_iIndepFun hB).indepFun_prodMk_prodMk₀
    (fun k => (eightIncrement_hasLaw hB k).aemeasurable)
    (2 * i) (2 * i + 1) (2 * j) (2 * j + 1)
    (by omega) (by omega) (by omega) (by omega)
  have h := hpair.comp (φ := fun x : ℝ × ℝ => (x.1 - x.2) / 4)
    (ψ := fun x : ℝ × ℝ => (x.1 - x.2) / 4) (by fun_prop) (by fun_prop)
  simpa only [gaussianBlock_eq_increments, Function.comp_def] using h

/-- Pairwise independent blocks are jointly independent because their joint laws are Gaussian. -/
theorem gaussianBlock_iIndepFun (hB : IsPreBrownianReal B P) :
    iIndepFun (gaussianBlock B) P := by
  classical
  have hg := gaussianBlock_isGaussianProcess hB
  apply iIndepFun_iff_finset.mpr
  intro s
  apply (hg.hasGaussianLaw s).iIndepFun_of_covariance_eq_zero
  intro i j hij
  exact (gaussianBlock_indepFun hB (Subtype.val_injective.ne hij)).covariance_eq_zero
    (hg.hasGaussianLaw_eval i).memLp_two (hg.hasGaussianLaw_eval j).memLp_two

def gaussianBlockPass : ℝ≥0∞ := gaussianReal 0 1 (Set.Icc (-1 : ℝ) 1)

theorem gaussianBlock_pass_probability (hB : IsPreBrownianReal B P) (j : ℕ) :
    P {ω | |gaussianBlock B j ω| ≤ 1} = gaussianBlockPass := by
  have h := (gaussianBlock_hasLaw hB j).measure_eq (p := fun x => x ∈ Set.Icc (-1 : ℝ) 1)
    measurableSet_Icc
  simpa only [Set.mem_Icc, Set.Icc_def, abs_le, gaussianBlockPass] using h

/-- The exact finite-block probability is the nth power of the standard-normal pass probability. -/
theorem gaussianBlocks_probability (hB : IsPreBrownianReal B P) (n : ℕ) :
    P {ω | ∀ j < n, |gaussianBlock B j ω| ≤ 1} = gaussianBlockPass ^ n := by
  classical
  have h := (gaussianBlock_iIndepFun hB).measure_inter_preimage_eq_mul (Finset.range n)
    (sets := fun _ => Set.Icc (-1 : ℝ) 1) (fun _ _ => measurableSet_Icc)
  have hset : {ω | ∀ j < n, |gaussianBlock B j ω| ≤ 1} =
      ⋂ j ∈ Finset.range n, (gaussianBlock B j) ⁻¹' Set.Icc (-1 : ℝ) 1 := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_iInter, Finset.mem_range, Set.mem_preimage,
      Set.mem_Icc, abs_le]
  rw [hset, h]
  have heach : ∀ j, P ((gaussianBlock B j) ⁻¹' Set.Icc (-1 : ℝ) 1) = gaussianBlockPass := by
    intro j
    change P {ω | -1 ≤ gaussianBlock B j ω ∧ gaussianBlock B j ω ≤ 1} = _
    simpa only [abs_le] using gaussianBlock_pass_probability hB j
  simp only [heach, Finset.prod_const, Finset.card_range]

/-- The standard normal has positive probability of passing the block test. -/
theorem gaussianBlockPass_pos : 0 < gaussianBlockPass := by
  apply pos_iff_ne_zero.mpr
  intro hz
  have hv := (gaussianReal_absolutelyContinuous' 0 (by norm_num : (1 : ℝ≥0) ≠ 0)) hz
  norm_num [gaussianBlockPass, Real.volume_Icc] at hv

/-- The pass probability is strictly smaller than one; no numerical approximation is used. -/
theorem gaussianBlockPass_lt_one : gaussianBlockPass < 1 := by
  by_contra h
  have hq : gaussianReal 0 1 (Set.Icc (-1 : ℝ) 1) = 1 :=
    le_antisymm prob_le_one (le_of_not_gt h)
  have hz : gaussianReal 0 1 (Set.Icc (-1 : ℝ) 1)ᶜ = 0 := by
    rw [measure_compl measurableSet_Icc (measure_ne_top _ _), measure_univ, hq, tsub_self]
  have hv := (gaussianReal_absolutelyContinuous' 0 (by norm_num : (1 : ℝ≥0) ≠ 0)) hz
  have hsub : Set.Ioi (1 : ℝ) ⊆ (Set.Icc (-1 : ℝ) 1)ᶜ := by
    intro x hx hmem
    exact (not_le_of_gt hx) hmem.2
  have hmono := measure_mono (μ := (volume : Measure ℝ)) hsub
  rw [hv, Real.volume_Ioi] at hmono
  exact (by simp : ¬ (∞ : ℝ≥0∞) ≤ 0) hmono

/-- Three residual bounds force the manuscript's normalized midpoint deviation to be small. -/
theorem three_point_affine_obstruction (s a b y₀ yₘ y₁ : ℝ)
    (h₀ : |y₀ - a * s - b| ≤ 1)
    (hₘ : |yₘ - a * (s + 8) - b| ≤ 1)
    (h₁ : |y₁ - a * (s + 16) - b| ≤ 1) :
    |(yₘ - (y₀ + y₁) / 2) / 2| ≤ 1 := by
  rw [abs_le] at h₀ hₘ h₁ ⊢
  constructor <;> linarith

/-- Attainment turns the actual optimal error event into every three-point block constraint. -/
theorem optimalTimeError_implies_blocks (f : C(ℝ, ℝ)) (n : ℕ)
    (herr : optimalTimeError f (16 * n) ≤ 1) :
    ∀ j < n, |(f (16 * j + 8) - (f (16 * j) + f (16 * j + 16)) / 2) / 2| ≤ 1 := by
  have hT : (0 : ℝ) ≤ 16 * n := by positivity
  rw [optimalTimeError_eq_interval hT f] at herr
  obtain ⟨a, b, hfit⟩ := (optimalError_le_iff_exists_fit hT (intervalPath f (16 * n))).mp herr
  intro j hj
  have hj' : (j : ℝ) + 1 ≤ n := by exact_mod_cast (show j + 1 ≤ n by omega)
  have h₀ := hfit ⟨16 * j, by constructor; positivity; nlinarith⟩
  have hₘ := hfit ⟨16 * j + 8, by constructor; positivity; nlinarith⟩
  have h₁ := hfit ⟨16 * j + 16, by constructor; positivity; nlinarith⟩
  exact three_point_affine_obstruction (16 * j) a b _ _ _ h₀ hₘ h₁

/-- Any a.e. continuous realization of the Brownian path inherits the exponential grid tail. -/
theorem optimalTimeError_probability_le (hB : IsPreBrownianReal B P)
    (F : Ω → C(ℝ, ℝ))
    (hF : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, F ω t = B t ω) (n : ℕ) :
    P {ω | optimalTimeError (F ω) (16 * n) ≤ 1} ≤ gaussianBlockPass ^ n := by
  rw [← gaussianBlocks_probability hB n]
  apply measure_mono_ae
  filter_upwards [hF] with ω hω
  intro herr j hj
  have hblock := optimalTimeError_implies_blocks (F ω) n herr j hj
  have h₀ := hω (16 * j)
  have hₘ := hω (16 * j + 8)
  have h₁ := hω (16 * j + 16)
  norm_num only [NNReal.coe_mul, NNReal.coe_add, NNReal.coe_natCast, NNReal.coe_ofNat] at h₀ hₘ h₁
  rw [h₀, hₘ, h₁] at hblock
  exact hblock

theorem anchoredTimeError_probability_le (hB : IsPreBrownianReal B P)
    (F : Ω → C(ℝ, ℝ))
    (hF : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, F ω t = B t ω) (n : ℕ) :
    P {ω | anchoredTimeError (F ω) (16 * n) ≤ 1} ≤ gaussianBlockPass ^ n := by
  apply le_trans (measure_mono ?_) (optimalTimeError_probability_le hB F hF n)
  intro ω hω
  exact (optimalTimeError_le_anchoredTimeError (F ω) (16 * n)).trans hω

/-- Brownian continuity supplies the required path realization on one full-measure event. -/
theorem processPath_represents_brownian (hB : IsBrownianReal B P) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0, processPath B ω t = B t ω := by
  filter_upwards [hB.cont] with ω hω
  exact processPath_apply_of_continuous hω

/-- The actual Brownian optimal-error event has an exponential upper bound at times 16n. -/
theorem optimalProcessError_probability_le (hB : IsBrownianReal B P) (n : ℕ) :
    P {ω | optimalProcessError B (16 * n) ω ≤ 1} ≤ gaussianBlockPass ^ n := by
  have h := optimalTimeError_probability_le hB.toIsPreBrownianReal (processPath B)
    (processPath_represents_brownian hB) n
  simpa only [optimalProcessError, NNReal.coe_mul, NNReal.coe_natCast, NNReal.coe_ofNat] using! h

theorem anchoredProcessError_probability_le (hB : IsBrownianReal B P) (n : ℕ) :
    P {ω | anchoredProcessError B (16 * n) ω ≤ 1} ≤ gaussianBlockPass ^ n := by
  have h := anchoredTimeError_probability_le hB.toIsPreBrownianReal (processPath B)
    (processPath_represents_brownian hB) n
  simpa only [anchoredProcessError, NNReal.coe_mul, NNReal.coe_natCast, NNReal.coe_ofNat] using! h

end BrownianAffine
