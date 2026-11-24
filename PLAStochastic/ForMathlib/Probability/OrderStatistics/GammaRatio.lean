import PLAStochastic.ForMathlib.Probability.OrderStatistics.OrderedSimplex
import Mathlib.Probability.Distributions.Exponential
import Mathlib.Probability.HasLaw
import Mathlib.Probability.Independence.Basic
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.LinearAlgebra.Matrix.Block

/-!
# Normalized partial sums of exponential variables

For iid `Exp(1)` variables `E 0, …, E n` with partial sums `Γ k = E 0 + ⋯ + E (k-1)`, the
ratio vector `(Γ 1 / Γ (n+1), …, Γ n / Γ (n+1))` has law `n! • volume.restrict (simplex n)`
(`map_gammaRatio_exp`).

The proof has three steps.

* The joint density of `(E 0, …, E n)` is `∏ i, exponentialPDF 1 (e i)`.  The partial-sum map
  `psMap n : e ↦ (Γ 1, …, Γ (n+1))` is linear, lower triangular with unit diagonal, hence
  preserves Lebesgue measure, and it carries this density to
  `coneDensity n γ = 1{0 ≤ γ₀ ≤ ⋯ ≤ γₙ} · exp (-γₙ)`.
* Splitting `γ = (γ', s)` with `s = γₙ`, the section of `{ratioMap γ ∈ A} ∩ cone` at `s > 0`
  is `s • (A ∩ closedSimplex n)`, of Lebesgue measure `sⁿ · volume (A ∩ closedSimplex n)`.
* `∫₀^∞ sⁿ e^{-s} ds = Γ(n+1) = n!`, and `closedSimplex n` differs from `simplex n` by a
  null set.
-/

noncomputable section

namespace PGM.Renyi

open MeasureTheory ProbabilityTheory Set Function
open scoped ENNReal Nat

variable {n : ℕ}

/-- Partial sums `gammaSum e k = ∑_{i < k} e i` of a tuple `e : Fin (n + 1) → ℝ`. -/
def gammaSum (e : Fin (n + 1) → ℝ) (k : ℕ) : ℝ :=
  ∑ i ∈ Finset.univ.filter (fun i : Fin (n + 1) => (i : ℕ) < k), e i

/-- The Rényi ratios `(Γ 1 / Γ (n+1), …, Γ n / Γ (n+1))` with `Γ k = gammaSum e k`. -/
def gammaRatio (e : Fin (n + 1) → ℝ) : Fin n → ℝ :=
  fun i => gammaSum e ((i : ℕ) + 1) / gammaSum e (n + 1)

theorem gammaSum_zero (e : Fin (n + 1) → ℝ) : gammaSum e 0 = 0 := by
  simp [gammaSum]

theorem gammaSum_succ (e : Fin (n + 1) → ℝ) (k : Fin (n + 1)) :
    gammaSum e ((k : ℕ) + 1) = gammaSum e k + e k := by
  have hset : (Finset.univ.filter fun i : Fin (n + 1) => (i : ℕ) < (k : ℕ) + 1) =
      insert k (Finset.univ.filter fun i : Fin (n + 1) => (i : ℕ) < k) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Fin.ext_iff]
    omega
  rw [gammaSum, hset, Finset.sum_insert (by simp), add_comm]
  rfl

theorem gammaSum_last (e : Fin (n + 1) → ℝ) : gammaSum e (n + 1) = ∑ i, e i := by
  rw [gammaSum, Finset.filter_true_of_mem fun i _ => i.isLt]

/-! ### The partial-sum map -/

/-- The lower-triangular all-ones matrix. -/
def psMatrix (m : ℕ) : Matrix (Fin m) (Fin m) ℝ :=
  fun j k => if (k : ℕ) < (j : ℕ) + 1 then 1 else 0

/-- The partial-sum map `e ↦ (Γ 1, …, Γ (n+1))`. -/
def psMap (n : ℕ) : (Fin (n + 1) → ℝ) →ₗ[ℝ] Fin (n + 1) → ℝ :=
  Matrix.toLin' (psMatrix (n + 1))

theorem psMap_apply (e : Fin (n + 1) → ℝ) (j : Fin (n + 1)) :
    psMap n e j = gammaSum e ((j : ℕ) + 1) := by
  simp only [psMap, Matrix.toLin'_apply, Matrix.mulVec, dotProduct, psMatrix, gammaSum,
    Finset.sum_filter, ite_mul, one_mul, zero_mul]

theorem det_psMap : LinearMap.det (psMap n) = 1 := by
  rw [psMap, LinearMap.det_toLin', Matrix.det_of_isLowerTriangular]
  · simp [psMatrix]
  · intro j k hjk
    rw [OrderDual.toDual_lt_toDual, Fin.lt_def] at hjk
    simp only [psMatrix]
    rw [if_neg (by omega)]

theorem measurePreserving_psMap : MeasurePreserving (psMap n) volume volume := by
  refine ⟨(psMap n).continuous_of_finiteDimensional.measurable, ?_⟩
  rw [Measure.map_linearMap_addHaar_eq_smul_addHaar volume (by rw [det_psMap]; norm_num),
    det_psMap]
  simp

/-! ### The cone density -/

/-- The closed ordered cone `{0 ≤ γ₀ ≤ ⋯ ≤ γ_{m-1}}`. -/
def cone (m : ℕ) : Set (Fin m → ℝ) :=
  {γ | Monotone γ ∧ ∀ i, 0 ≤ γ i}

/-- The joint density `1{0 ≤ γ₀ ≤ ⋯ ≤ γₙ} · exp (-γₙ)` of the partial sums. -/
def coneDensity (n : ℕ) : (Fin (n + 1) → ℝ) → ℝ≥0∞ :=
  (cone (n + 1)).indicator fun γ => ENNReal.ofReal (Real.exp (-γ (Fin.last n)))

/-- The ratio map `γ ↦ (γ₀ / γₙ, …, γ_{n-1} / γₙ)`. -/
def ratioMap (n : ℕ) (γ : Fin (n + 1) → ℝ) : Fin n → ℝ :=
  fun i => γ i.castSucc / γ (Fin.last n)

theorem measurableSet_cone (m : ℕ) : MeasurableSet (cone m) := by
  have : cone m = (⋂ i, ⋂ j, ⋂ (_ : i ≤ j), {γ : Fin m → ℝ | γ i ≤ γ j}) ∩
      ⋂ i, {γ | 0 ≤ γ i} := by
    ext γ
    simp [cone, Monotone]
  rw [this]
  exact (MeasurableSet.iInter fun i => MeasurableSet.iInter fun j => MeasurableSet.iInter
    fun _ => measurableSet_le (measurable_pi_apply i) (measurable_pi_apply j)).inter
    (MeasurableSet.iInter fun i => measurableSet_le measurable_const (measurable_pi_apply i))

theorem measurable_coneDensity : Measurable (coneDensity n) :=
  (ENNReal.measurable_ofReal.comp
    (Real.measurable_exp.comp (measurable_pi_apply _).neg)).indicator (measurableSet_cone _)

theorem measurable_ratioMap : Measurable (ratioMap n) :=
  measurable_pi_lambda _ fun _ => (measurable_pi_apply _).div (measurable_pi_apply _)

theorem gammaRatio_eq (e : Fin (n + 1) → ℝ) : gammaRatio e = ratioMap n (psMap n e) := by
  funext i
  simp [gammaRatio, ratioMap, psMap_apply]

theorem gammaRatio_eq_comp :
    (gammaRatio : (Fin (n + 1) → ℝ) → Fin n → ℝ) = ratioMap n ∘ psMap n :=
  funext gammaRatio_eq

theorem measurable_gammaRatio : Measurable (gammaRatio : (Fin (n + 1) → ℝ) → Fin n → ℝ) := by
  rw [gammaRatio_eq_comp]
  exact measurable_ratioMap.comp measurePreserving_psMap.measurable

theorem psMap_mem_cone_iff (e : Fin (n + 1) → ℝ) : psMap n e ∈ cone (n + 1) ↔ ∀ i, 0 ≤ e i := by
  constructor
  · rintro ⟨hmono, hnn⟩ ⟨k, hk⟩
    cases k with
    | zero =>
      have h := hnn ⟨0, hk⟩
      rw [psMap_apply, gammaSum_succ, gammaSum_zero, zero_add] at h
      exact h
    | succ k =>
      have h := hmono (show (⟨k, by omega⟩ : Fin (n + 1)) ≤ ⟨k + 1, hk⟩ from
        Fin.mk_le_mk.2 (Nat.le_succ k))
      rw [psMap_apply, psMap_apply, gammaSum_succ e ⟨k + 1, hk⟩] at h
      simp only at h
      linarith
  · intro he
    refine ⟨fun i j hij => ?_, fun i => ?_⟩
    · rw [psMap_apply, psMap_apply, gammaSum, gammaSum]
      refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun k _ _ => he k
      intro k
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      have := Fin.le_iff_val_le_val.1 hij
      omega
    · rw [psMap_apply, gammaSum]
      exact Finset.sum_nonneg fun k _ => he k

/-- The product exponential density is the cone density of the partial sums. -/
theorem prod_exponentialPDF_eq (e : Fin (n + 1) → ℝ) :
    ∏ i, exponentialPDF 1 (e i) = coneDensity n (psMap n e) := by
  by_cases he : ∀ i, 0 ≤ e i
  · rw [coneDensity, indicator_of_mem ((psMap_mem_cone_iff e).2 he), psMap_apply]
    simp only [Fin.val_last]
    rw [gammaSum_last]
    simp_rw [exponentialPDF_of_nonneg (he _), one_mul]
    rw [← ENNReal.ofReal_prod_of_nonneg fun i _ => (Real.exp_pos _).le, ← Real.exp_sum,
      Finset.sum_neg_distrib]
  · rw [coneDensity, indicator_of_notMem fun h => he ((psMap_mem_cone_iff e).1 h)]
    simp only [not_forall, not_le] at he
    obtain ⟨i, hi⟩ := he
    exact Finset.prod_eq_zero (Finset.mem_univ i) (exponentialPDF_of_neg hi)

/-- Pushing a density along a measure-preserving map. -/
theorem map_withDensity_comp {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {ν : Measure β} {T : α → β} (hT : MeasurePreserving T μ ν)
    {f : β → ℝ≥0∞} (hf : Measurable f) :
    (μ.withDensity (f ∘ T)).map T = ν.withDensity f := by
  ext s hs
  rw [Measure.map_apply hT.measurable hs, withDensity_apply _ (hT.measurable hs),
    withDensity_apply _ hs, ← hT.map_eq, setLIntegral_map hs hf hT.measurable]
  rfl

/-! ### Slicing the cone -/

theorem snoc_mem_cone_iff {γ : Fin n → ℝ} {s : ℝ} :
    (Fin.snoc γ s : Fin (n + 1) → ℝ) ∈ cone (n + 1) ↔
      Monotone γ ∧ (∀ i, 0 ≤ γ i) ∧ (∀ i, γ i ≤ s) ∧ 0 ≤ s := by
  constructor
  · rintro ⟨hmono, hnn⟩
    refine ⟨fun i j hij => ?_, fun i => ?_, fun i => ?_, ?_⟩
    · simpa using hmono (Fin.castSucc_le_castSucc_iff.2 hij)
    · simpa using hnn i.castSucc
    · simpa using hmono (Fin.le_last i.castSucc)
    · simpa using hnn (Fin.last n)
  · rintro ⟨hmono, hnn, hle, hs⟩
    refine ⟨fun a b hab => ?_, fun a => ?_⟩
    · induction b using Fin.lastCases with
      | last =>
        induction a using Fin.lastCases with
        | last => simp
        | cast i => simpa using hle i
      | cast j =>
        induction a using Fin.lastCases with
        | last => exact absurd hab (not_le.2 (Fin.castSucc_lt_last j))
        | cast i => simpa using hmono (Fin.castSucc_le_castSucc_iff.1 hab)
    · induction a using Fin.lastCases with
      | last => simpa using hs
      | cast i => simpa using hnn i

theorem inv_smul_mem_closedSimplex_iff {γ : Fin n → ℝ} {s : ℝ} (hs : 0 < s) :
    s⁻¹ • γ ∈ closedSimplex n ↔ Monotone γ ∧ (∀ i, 0 ≤ γ i) ∧ ∀ i, γ i ≤ s := by
  have hs' : 0 < s⁻¹ := inv_pos.2 hs
  simp only [closedSimplex, mem_ofPred_eq, Monotone, Pi.smul_apply, smul_eq_mul]
  refine and_congr ?_ (and_congr ?_ ?_)
  · exact forall_congr' fun i => forall_congr' fun j => imp_congr_right fun _ =>
      mul_le_mul_iff_right₀ hs'
  · exact forall_congr' fun i => by rw [mul_nonneg_iff_of_pos_left hs']
  · exact forall_congr' fun i => by rw [inv_mul_le_iff₀ hs, mul_one]

theorem ratioMap_snoc (γ : Fin n → ℝ) (s : ℝ) :
    ratioMap n (Fin.snoc γ s : Fin (n + 1) → ℝ) = s⁻¹ • γ := by
  funext i
  simp [ratioMap, div_eq_inv_mul]

theorem preimage_snoc_eq {A : Set (Fin n → ℝ)} {s : ℝ} (hs : 0 < s) :
    (fun γ : Fin n → ℝ => (Fin.snoc γ s : Fin (n + 1) → ℝ)) ⁻¹' (ratioMap n ⁻¹' A ∩ cone (n + 1)) =
      (fun γ : Fin n → ℝ => s⁻¹ • γ) ⁻¹' (A ∩ closedSimplex n) := by
  ext γ
  simp only [mem_preimage, mem_inter_iff]
  rw [ratioMap_snoc, snoc_mem_cone_iff, inv_smul_mem_closedSimplex_iff hs]
  simp [hs.le]

/-- The Lebesgue integral of the section of the density at `γₙ = s ≠ 0`. -/
theorem lintegral_snoc {A : Set (Fin n → ℝ)} (hA : MeasurableSet A) {s : ℝ} (hs : s ≠ 0) :
    ∫⁻ γ : Fin n → ℝ, (ratioMap n ⁻¹' A).indicator (coneDensity n) (Fin.snoc γ s) =
      (Ioi 0).indicator (fun s : ℝ => ENNReal.ofReal (s ^ n * Real.exp (-s))) s *
        volume (A ∩ closedSimplex n) := by
  rcases lt_or_gt_of_ne hs with hneg | hpos
  · have hzero : ∀ γ : Fin n → ℝ,
        (ratioMap n ⁻¹' A).indicator (coneDensity n) (Fin.snoc γ s) = 0 := by
      intro γ
      refine indicator_apply_eq_zero.2 fun _ => ?_
      rw [coneDensity, indicator_of_notMem]
      intro h
      exact absurd (snoc_mem_cone_iff.1 h).2.2.2 (not_le.2 hneg)
    simp_rw [hzero, lintegral_zero]
    rw [indicator_of_notMem (show s ∉ Ioi 0 from not_lt.2 hneg.le), zero_mul]
  · have hpt : (fun γ : Fin n → ℝ =>
        (ratioMap n ⁻¹' A).indicator (coneDensity n) (Fin.snoc γ s)) =
        ((fun γ : Fin n → ℝ => s⁻¹ • γ) ⁻¹' (A ∩ closedSimplex n)).indicator
          fun _ => ENNReal.ofReal (Real.exp (-s)) := by
      funext γ
      rw [coneDensity, indicator_indicator, ← preimage_snoc_eq hpos]
      by_cases hγ : (Fin.snoc γ s : Fin (n + 1) → ℝ) ∈ ratioMap n ⁻¹' A ∩ cone (n + 1)
      · rw [indicator_of_mem hγ, indicator_of_mem (show γ ∈ _ from hγ)]
        simp
      · rw [indicator_of_notMem hγ, indicator_of_notMem (show γ ∉ _ from hγ)]
    have hmeas : MeasurableSet ((fun γ : Fin n → ℝ => s⁻¹ • γ) ⁻¹' (A ∩ closedSimplex n)) :=
      (measurable_const_smul s⁻¹) (hA.inter measurableSet_closedSimplex)
    rw [hpt, lintegral_indicator_const hmeas, Measure.addHaar_preimage_smul _ (inv_ne_zero hs),
      Module.finrank_fin_fun, indicator_of_mem (show s ∈ Ioi 0 from hpos), inv_pow, inv_inv,
      abs_of_pos (pow_pos hpos n), ← mul_assoc, ← ENNReal.ofReal_mul (Real.exp_pos _).le,
      mul_comm (Real.exp (-s))]

/-- `∫₀^∞ sⁿ e^{-s} ds = n!`. -/
theorem lintegral_pow_mul_exp_neg (n : ℕ) :
    ∫⁻ s in Ioi (0 : ℝ), ENNReal.ofReal (s ^ n * Real.exp (-s)) = n ! := by
  have hfun : (fun x : ℝ => Real.exp (-x) * x ^ ((n : ℝ) + 1 - 1)) =
      fun x => x ^ n * Real.exp (-x) := by
    funext x
    rw [add_sub_cancel_right, Real.rpow_natCast, mul_comm]
  have hint : IntegrableOn (fun x : ℝ => x ^ n * Real.exp (-x)) (Ioi 0) := by
    rw [← hfun]
    exact Real.GammaIntegral_convergent (by positivity)
  have hval : ∫ x in Ioi (0 : ℝ), x ^ n * Real.exp (-x) = n ! := by
    rw [← hfun, ← Real.Gamma_eq_integral (by positivity), Real.Gamma_nat_eq_factorial]
  rw [← ofReal_integral_eq_lintegral_ofReal hint, hval, ENNReal.ofReal_natCast]
  exact (ae_restrict_iff' measurableSet_Ioi).2
    (Filter.Eventually.of_forall fun x hx => by
      have : (0 : ℝ) < x := hx
      positivity)

/-- The ratio of the partial sums under the cone density is `n!` times Lebesgue measure on the
simplex. -/
theorem map_ratioMap_coneDensity :
    (volume.withDensity (coneDensity n)).map (ratioMap n) =
      (n ! : ℝ≥0∞) • volume.restrict (simplex n) := by
  ext A hA
  rw [Measure.map_apply measurable_ratioMap hA,
    withDensity_apply _ (measurable_ratioMap hA), ← lintegral_indicator (measurable_ratioMap hA),
    Measure.smul_apply, smul_eq_mul, restrict_simplex_eq_closedSimplex,
    Measure.restrict_apply hA]
  set F := (ratioMap n ⁻¹' A).indicator (coneDensity n) with hF
  have hFm : Measurable F := measurable_coneDensity.indicator (measurable_ratioMap hA)
  let eqv := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) (Fin.last n)
  have h := (volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) (Fin.last n)).symm
  rw [← h.lintegral_comp_emb eqv.symm.measurableEmbedding F, Measure.volume_eq_prod,
    lintegral_prod (fun p => F (eqv.symm p)) (hFm.comp eqv.symm.measurable).aemeasurable]
  have hsymm : ∀ (s : ℝ) (γ : Fin n → ℝ), eqv.symm (s, γ) = Fin.snoc γ s := by
    intro s γ
    simp [eqv, MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv, Fin.insertNth_last']
  simp_rw [hsymm]
  have hae : ∀ᵐ s : ℝ, s ≠ 0 := measure_eq_zero_iff_ae_notMem.1 (measure_singleton (0 : ℝ))
  rw [lintegral_congr_ae (hae.mono fun s hs => lintegral_snoc hA hs), lintegral_mul_const,
    lintegral_indicator measurableSet_Ioi, lintegral_pow_mul_exp_neg]
  exact (ENNReal.measurable_ofReal.comp
    ((measurable_id.pow_const n).mul (Real.measurable_exp.comp measurable_neg))).indicator
    measurableSet_Ioi

theorem expMeasure_one_eq : expMeasure 1 = volume.withDensity (exponentialPDF 1) :=
  rfl

/-- The law of `n + 1` iid `Exp(1)` variables, in partial-sum coordinates, has the cone
density. -/
theorem map_psMap_pi_expMeasure :
    (Measure.pi fun _ : Fin (n + 1) => expMeasure 1).map (psMap n) =
      volume.withDensity (coneDensity n) := by
  have : IsProbabilityMeasure (volume.withDensity (exponentialPDF 1)) :=
    expMeasure_one_eq ▸ isProbabilityMeasure_expMeasure one_pos
  have hdens : (fun e : Fin (n + 1) → ℝ => ∏ i, exponentialPDF 1 (e i)) =
      coneDensity n ∘ psMap n := by
    funext e
    exact prod_exponentialPDF_eq e
  rw [expMeasure_one_eq,
    pi_withDensity (exponentialPDF 1) (measurable_exponentialPDFReal 1).ennreal_ofReal, hdens]
  exact map_withDensity_comp measurePreserving_psMap measurable_coneDensity

/-- **Normalized exponential partial sums.**  If `E 0, …, E n` are independent `Exp(1)`
variables and `Γ k = ∑_{i < k} E i`, then `(Γ 1 / Γ (n+1), …, Γ n / Γ (n+1))` has density `n!`
on the open simplex `{0 < u₀ < ⋯ < u_{n-1} < 1}`. -/
theorem map_gammaRatio_exp {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {E : Fin (n + 1) → Ω → ℝ} (hE : ∀ i, HasLaw (E i) (expMeasure 1) P)
    (hind : iIndepFun E P) :
    P.map (fun ω => gammaRatio fun i => E i ω) = (n ! : ℝ≥0∞) • volume.restrict (simplex n) := by
  have hX := hind.hasLaw_pi hE
  have hmap : P.map (fun ω => gammaRatio fun i => E i ω) =
      (P.map fun ω i => E i ω).map gammaRatio :=
    (AEMeasurable.map_map_of_aemeasurable measurable_gammaRatio.aemeasurable hX.aemeasurable).symm
  rw [hmap, hX.map_eq, gammaRatio_eq_comp, ← Measure.map_map measurable_ratioMap
    measurePreserving_psMap.measurable, map_psMap_pi_expMeasure]
  exact map_ratioMap_coneDensity

end PGM.Renyi
