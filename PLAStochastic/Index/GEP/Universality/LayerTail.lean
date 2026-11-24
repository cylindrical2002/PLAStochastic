import PLAStochastic.Index.GEP.Universality.ClassProperties
import PLAStochastic.Index.GEP.OrbitClosure.OrbitMoments
import PLAStochastic.ForMathlib.Probability.StoppedSum.StoppedMoments

/-!
# WP5, D0: the layer tail and the stopped-sum moments on the class

Blueprint `kmt-blueprint/main.tex` Lemma 8.1 (`lem:tail`) and the moment inputs of the proof of
Theorem 8.7, on the canonical space `iidLaw ν`:

* `UnivClass.momClass`: the class sits in `MomClass vhi (max κ₃ 0 / √vlo³) vlo`, so the WP2
  tail `gapSegLen_tail` applies with the **absolute** rate `tailRate` on the scale `eps²/vlo`;
* `UnivClass.gapSegLen_tail_real`: `P(T > m) ≤ (72/71) e^{-tailRate · vlo · m / eps²}`;
* `UnivClass.lawC_le`: `E T ≤ cPlus eps²/vlo`, and `T < ∞` a.s.;
* `UnivClass.lintegral_stopSum_sub_sq_le`: `E (S_T - T)² ≤ v · E T`.

The blueprint scales by `G = eps²/v`; here the tail is written on `eps²/vlo`, and the rate
`r_T = tailRate · vlo/vhi` on `G` is recovered in the assembly from `v ≤ vhi`.
-/

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

variable {vlo vhi κ₃ B θ : ℝ} {ν : ProbabilityMeasure ℝ}

/-- The exponential moment of the class in the integrable form. -/
theorem UnivClass.expMom' (h : UnivClass vlo vhi κ₃ B θ ν) : ExpMom θ B ν := by
  have hint : Integrable (fun x => Real.exp (θ * x)) (ν : Measure ℝ) := by
    refine ⟨by fun_prop, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ fun x => (Real.exp_pos _).le)]
    exact h.expMom.trans_lt ENNReal.ofReal_lt_top
  refine ⟨hint, ?_⟩
  have h1 := h.expMom
  rw [← ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ fun x => (Real.exp_pos _).le),
    ENNReal.ofReal_le_ofReal_iff'] at h1
  rcases h1 with h1 | h1
  · exact h1
  · exact absurd h1 (not_le.2 (integral_exp_pos hint))

theorem UnivClass.B_pos (h : UnivClass vlo vhi κ₃ B θ ν) : 0 < B :=
  (integral_exp_pos h.expMom'.integrable).trans_le h.expMom'.le

/-- The third-moment parameter of the class as a normalised bound. -/
def univBeta (vlo κ₃ : ℝ) : ℝ := max κ₃ 0 / Real.sqrt vlo ^ 3

/-- The class lies in the WP2 moment class with `b = vhi`, `β = univBeta`, `vmin = vlo`. -/
theorem UnivClass.momClass (h : UnivClass vlo vhi κ₃ B θ ν) (hvlo : 0 < vlo) :
    MomClass vhi (univBeta vlo κ₃) vlo ν := by
  refine ⟨h.pos, h.memLp3, h.mean, h.var_ge, h.var_le, ?_⟩
  have hint := h.integrable_third
  have h3 : ∫ x, |x - 1| ^ 3 ∂(ν : Measure ℝ) ≤ max κ₃ 0 := by
    have := h.third
    rw [← ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ fun x => by positivity),
      ENNReal.ofReal_le_ofReal_iff'] at this
    rcases this with h1 | h1
    · exact h1.trans (le_max_left _ _)
    · exact h1.trans (le_max_right _ _)
  have hv : Real.sqrt vlo ^ 3 ≤ Real.sqrt (lawVar ν) ^ 3 :=
    pow_le_pow_left₀ (Real.sqrt_nonneg _) (Real.sqrt_le_sqrt h.var_ge) 3
  have hs : 0 < Real.sqrt vlo ^ 3 := by positivity
  calc ∫ x, |x - 1| ^ 3 ∂(ν : Measure ℝ) ≤ max κ₃ 0 := h3
    _ = univBeta vlo κ₃ * Real.sqrt vlo ^ 3 := by unfold univBeta; field_simp
    _ ≤ univBeta vlo κ₃ * Real.sqrt (lawVar ν) ^ 3 :=
        mul_le_mul_of_nonneg_left hv (by unfold univBeta; positivity)

/-- The stopping tail on the class (blueprint Lemma 8.1), rate `tailRate · vlo / eps²`. -/
theorem UnivClass.gapSegLen_tail_real (h : UnivClass vlo vhi κ₃ B θ ν) (hvlo : 0 < vlo)
    {eps : ℝ} (heps : epsZero vhi (univBeta vlo κ₃) ≤ eps) (m : ℕ) :
    (iidLaw ν).real {g | (m : ℕ∞) < gapSegLen eps g} ≤
      72 / 71 * Real.exp (-(tailRate * vlo) * m / eps ^ 2) := by
  have := gapSegLen_tail hvlo heps (h.momClass hvlo) m
  rw [← ofReal_measureReal] at this
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 this

/-- Finiteness and the mean bracket of the first segment on the class. -/
theorem UnivClass.oneLayer (h : UnivClass vlo vhi κ₃ B θ ν) (hvlo : 0 < vlo)
    {eps : ℝ} (heps : epsZero vhi (univBeta vlo κ₃) ≤ eps) :
    (∀ᵐ g ∂(iidLaw ν), gapSegLen eps g ≠ ⊤) ∧
      eps ^ 2 / (128 * vhi) ≤ lawC eps ν ∧ lawC eps ν ≤ cPlus * eps ^ 2 / vlo :=
  momClass_oneLayer hvlo heps (h.momClass hvlo)

/-- The centred gaps `g t - 1` on the canonical space are a `GapLaw` with mean one. -/
theorem UnivClass.gapLaw (h : UnivClass vlo vhi κ₃ B θ ν) (hvlo : 0 < vlo) :
    GapLaw (iidLaw ν) gapCoord 1 (Real.sqrt (lawVar ν)) (∫ x, |x - 1| ^ 3 ∂(ν : Measure ℝ)) := by
  have hv0 : 0 < lawVar ν := hvlo.trans_le h.var_ge
  exact gapLaw_iidLaw h.memLp3 h.mean one_pos (Real.sq_sqrt hv0.le).symm (Real.sqrt_pos.2 hv0)
    le_rfl

/-- `E T = lawC` as a lower integral of the `ℕ∞`-valued stopping time. -/
theorem UnivClass.lintegral_gapSegLen_eq (h : UnivClass vlo vhi κ₃ B θ ν) (hvlo : 0 < vlo)
    {eps : ℝ} (heps : epsZero vhi (univBeta vlo κ₃) ≤ eps) :
    ∫⁻ g, ((gapSegLen eps g : ℕ∞) : ℝ≥0∞) ∂(iidLaw ν) = ENNReal.ofReal (lawC eps ν) := by
  obtain ⟨-, -, -, -, hfin, hT1, -, -, -⟩ := momClass_setup hvlo heps (h.momClass hvlo)
  have hae : ∀ᵐ g ∂(iidLaw ν), ((gapSegLen eps g : ℕ∞) : ℝ≥0∞) =
      ENNReal.ofReal (((gapSegLen eps g).toNat : ℝ)) := by
    filter_upwards [hfin] with g hg
    obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.1 hg
    rw [← hn]
    simp
  rw [lintegral_congr_ae hae, ← ofReal_integral_eq_lintegral_ofReal hT1
    (ae_of_all _ fun g => by positivity)]
  rfl

/-- **Second moment of the endpoint shift**: `E (S_T - T)² ≤ v · E T` (as lower integrals). -/
theorem UnivClass.lintegral_stopSum_sub_sq_le (h : UnivClass vlo vhi κ₃ B θ ν) (hvlo : 0 < vlo)
    {eps : ℝ} (heps : epsZero vhi (univBeta vlo κ₃) ≤ eps) :
    ∫⁻ g, ENNReal.ofReal ((stopSum eps g - ((gapSegLen eps g).toNat : ℝ)) ^ 2) ∂(iidLaw ν) ≤
      ENNReal.ofReal (lawVar ν) * ENNReal.ofReal (lawC eps ν) := by
  rw [← h.lintegral_gapSegLen_eq hvlo heps]
  have hX := h.gapLaw hvlo
  have hfin := (h.oneLayer hvlo heps).1
  have hY2 : ∀ t, MemLp (centred gapCoord 1 t) 2 (iidLaw ν) :=
    fun t => (hX.memLp_centred t).mono_exponent (by norm_num)
  have hσ : ∀ t, ∫ g, centred gapCoord 1 t g ^ 2 ∂(iidLaw ν) ≤ lawVar ν := fun t => by
    rw [hX.integral_centred_sq, Real.sq_sqrt (hvlo.trans_le h.var_ge).le]
  have key := lintegral_stoppedSumE_sq_le hX.indepIncrements
    (T := gapSegLen eps) (fun t => gapSegLen_lt_measurable (X := gapCoord) (fun t => measurable_pi_apply t) eps t)
    hY2 hX.integral_centred hσ hfin
  have e : ∀ g : ℕ → ℝ, stoppedSumE (centred gapCoord 1) (gapSegLen eps) g =
      stopSum eps g - ((gapSegLen eps g).toNat : ℝ) := by
    intro g
    simp only [stoppedSumE, partialSum, centred, gapCoord, Finset.sum_sub_distrib,
      Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one, stopSum, gapKeys]
  simp_rw [e] at key
  exact key

end

end PGM
