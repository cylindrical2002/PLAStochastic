import PLAStochastic.Index.GEP.Universality.StoppedExpMoment
import PLAStochastic.Index.GEP.Universality.WeightedDistanceTools
import PLAStochastic.Index.GEP.Shadow.FirstLayerEnvelope

/-!
# WP5, D4: the endpoint-shift term

Blueprint `kmt-blueprint/main.tex`, proof of Theorem 8.7, "endpoint shift": with
`U = v S_T/ε²` (the law `rawLaw ε ν`) and `V = v T/ε²`,

  `d_γ(Law U, Law V) ≤ K_A / ε`,

from the coupling bound, Hölder, `E (S_T - T)² ≤ v E T`, the stopped exponential moment and
the exponential tail of `T`.  Also the scaled tail `P(r ≤ V) ≤ (72/71) e · e^{-r' r}` with
`r' = tailRate · vlo / vhi`, used again for the far tail of the main term.
-/

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

variable {vlo vhi κ₃ B θ : ℝ} {ν : ProbabilityMeasure ℝ}

/-- `U = v S_T / ε²`. -/
def rawU (eps : ℝ) (ν : ProbabilityMeasure ℝ) (g : ℕ → ℝ) : ℝ := lawVar ν * stopSum eps g / eps ^ 2

/-- `V = v T / ε²`. -/
def rawV (eps : ℝ) (ν : ProbabilityMeasure ℝ) (g : ℕ → ℝ) : ℝ :=
  lawVar ν * ((gapSegLen eps g).toNat : ℝ) / eps ^ 2

theorem measurable_rawU (eps : ℝ) (ν : ProbabilityMeasure ℝ) : Measurable (rawU eps ν) :=
  (measurable_const.mul (measurable_stopSum eps)).div_const _

theorem measurable_rawV (eps : ℝ) (ν : ProbabilityMeasure ℝ) : Measurable (rawV eps ν) :=
  (measurable_const.mul (measurable_toNat_gapSegLen eps)).div_const _

theorem rawLaw_eq_lawPM (eps : ℝ) (ν : ProbabilityMeasure ℝ) :
    rawLaw eps ν = lawPM (iidLaw ν) (measurable_rawU eps ν) := rfl

/-- The tail rate on the Brownian time scale. -/
def rPrime (vlo vhi : ℝ) : ℝ := tailRate * vlo / vhi

/-- The tail constant `(72/71) e`. -/
def cTail : ℝ := 72 / 71 * Real.exp 1

theorem cTail_pos : 0 < cTail := by unfold cTail; positivity

theorem rPrime_pos (hvlo : 0 < vlo) (hvhi : 0 < vhi) : 0 < rPrime vlo vhi := by
  unfold rPrime; have := tailRate_pos; positivity

/-- `ε² ≥ 10000 v` on the class at the standard threshold. -/
theorem UnivClass.sq_ge (h : UnivClass vlo vhi κ₃ B θ ν) (hvlo : 0 < vlo) {eps : ℝ}
    (heps : epsZero vhi (univBeta vlo κ₃) ≤ eps) : 10000 * lawVar ν ≤ eps ^ 2 := by
  have hM := h.momClass hvlo
  have hv0 : 0 < lawVar ν := hvlo.trans_le h.var_ge
  set σ := Real.sqrt (lawVar ν) with hσ
  have hσpos : 0 < σ := Real.sqrt_pos.2 hv0
  have hσ2 : σ ^ 2 = lawVar ν := Real.sq_sqrt hv0.le
  have hκ : 0 ≤ ∫ x, |x - 1| ^ 3 ∂(ν : Measure ℝ) := integral_nonneg fun _ => by positivity
  obtain ⟨c1, -, -, -, -, -, -⟩ := largeConditions one_pos hσpos hκ
    (by rw [hσ2, one_pow, mul_one]; exact hM.var_le) hM.third_le heps
  rw [one_pow, one_mul, hσ2, le_div_iff₀ hv0] at c1
  linarith

/-- **Scaled tail**: `P(r ≤ V) ≤ cTail · e^{-r' r}` for `r > 0`. -/
theorem UnivClass.tail_rawV (h : UnivClass vlo vhi κ₃ B θ ν) (hvlo : 0 < vlo) {eps : ℝ}
    (heps : epsZero vhi (univBeta vlo κ₃) ≤ eps) {r : ℝ} (hr : 0 < r) :
    (iidLaw ν).real {g | r ≤ rawV eps ν g} ≤ cTail * Real.exp (-(rPrime vlo vhi * r)) := by
  have hv0 : 0 < lawVar ν := hvlo.trans_le h.var_ge
  have hvhi : 0 < vhi := hvlo.trans_le (h.var_ge.trans h.var_le)
  have heps1 : 1 ≤ eps := (one_le_epsZero _ _).trans heps
  have hE : 0 < eps ^ 2 := by positivity
  set x := r * eps ^ 2 / lawVar ν with hx
  have hx0 : 0 < x := by positivity
  set M := ⌈x⌉₊ with hM
  have hM1 : 1 ≤ M := Nat.one_le_iff_ne_zero.2 (by
    intro h0
    have := Nat.ceil_eq_zero.1 h0
    linarith)
  have hsub : {g : ℕ → ℝ | r ≤ rawV eps ν g} ⊆ {g | ((M - 1 : ℕ) : ℕ∞) < gapSegLen eps g} := by
    intro g hg
    simp only [Set.mem_ofPred_eq, rawV] at hg ⊢
    have hx' : x ≤ ((gapSegLen eps g).toNat : ℝ) := by
      rw [hx, div_le_iff₀ hv0]
      rw [le_div_iff₀ hE] at hg
      linarith
    have hMle : M ≤ (gapSegLen eps g).toNat := Nat.ceil_le.2 hx'
    have hne : gapSegLen eps g ≠ ⊤ := by
      intro htop
      rw [htop, ENat.toNat_top] at hMle
      omega
    obtain ⟨t, ht⟩ := ENat.ne_top_iff_exists.1 hne
    rw [← ht] at hMle ⊢
    rw [ENat.toNat_natCast] at hMle
    exact_mod_cast (show M - 1 < t by omega)
  have htail := h.gapSegLen_tail_real hvlo heps (M - 1)
  refine (measureReal_mono hsub).trans (htail.trans ?_)
  -- `(M - 1) ≥ x - 1`, and `tailRate · vlo ≤ ε²`
  have hM1' : (x : ℝ) - 1 ≤ ((M - 1 : ℕ) : ℝ) := by
    rw [Nat.cast_sub hM1, Nat.cast_one]
    linarith [Nat.le_ceil x]
  have hrT : tailRate * vlo ≤ eps ^ 2 := by
    have := h.sq_ge hvlo heps
    have := tailRate_le_one
    have := tailRate_pos
    nlinarith [h.var_ge]
  have hrT0 : 0 ≤ tailRate * vlo := by have := tailRate_pos; positivity
  -- `-(tailRate vlo)(M-1)/ε² ≤ 1 - tailRate vlo r/vhi`
  have h1 : tailRate * vlo * (x - 1) / eps ^ 2 ≤ tailRate * vlo * ((M - 1 : ℕ) : ℝ) / eps ^ 2 := by
    gcongr
  have h2 : tailRate * vlo * (x - 1) / eps ^ 2 = tailRate * vlo * r / lawVar ν - tailRate * vlo / eps ^ 2 := by
    rw [hx]; field_simp
  have h3 : tailRate * vlo / eps ^ 2 ≤ 1 := by rw [div_le_one hE]; exact hrT
  have h4 : tailRate * vlo / vhi * r ≤ tailRate * vlo * r / lawVar ν := by
    rw [div_mul_eq_mul_div, div_le_div_iff₀ hvhi hv0]
    have := mul_le_mul_of_nonneg_left h.var_le (by positivity : 0 ≤ tailRate * vlo * r)
    linarith
  have h5 : -(tailRate * vlo) * ((M - 1 : ℕ) : ℝ) / eps ^ 2 =
      -(tailRate * vlo * ((M - 1 : ℕ) : ℝ) / eps ^ 2) := by ring
  have hfinal : -(tailRate * vlo) * ((M - 1 : ℕ) : ℝ) / eps ^ 2 ≤ 1 + -(tailRate * vlo / vhi * r) := by
    rw [h5]; linarith
  unfold cTail rPrime
  rw [mul_assoc (72 / 71), ← Real.exp_add]
  exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 hfinal) (by norm_num)

/-! ## The endpoint-shift constant and bound -/

/-- `K_A = √(cPlus vhi³ / vlo) · √(2 (1 + cTail))`. -/
def kEndpoint (vlo vhi : ℝ) : ℝ :=
  Real.sqrt (cPlus * vhi ^ 3 / vlo) * Real.sqrt (2 * (1 + cTail))

/-- **Endpoint shift** (blueprint Theorem 8.7, first term): `d_γ(Law U, Law V) ≤ K_A / ε`. -/
theorem endpoint_term_le (h : UnivClass vlo vhi κ₃ B θ ν) (hvlo : 0 < vlo) (hθ : 0 < θ)
    {eps γ : ℝ} (heps : epsZero vhi (univBeta vlo κ₃) ≤ eps) (hγ : 0 < γ)
    (hγr : 16 * γ ≤ rPrime vlo vhi)
    (hE2 : 2 * γ * vhi / eps ^ 2 ≤ min (θ / 4) (θ ^ 2 / (16 * B))) :
    dEtaL γ (lawPM (iidLaw ν) (measurable_rawU eps ν)) (lawPM (iidLaw ν) (measurable_rawV eps ν)) ≤
      ENNReal.ofReal (kEndpoint vlo vhi / eps) := by
  have hv0 : 0 < lawVar ν := hvlo.trans_le h.var_ge
  have hvhi : 0 < vhi := hvlo.trans_le (h.var_ge.trans h.var_le)
  have heps1 : 1 ≤ eps := (one_le_epsZero _ _).trans heps
  have hepspos : 0 < eps := by linarith
  have hE : 0 < eps ^ 2 := by positivity
  have hr' := rPrime_pos hvlo hvhi
  have hC := cTail_pos
  set P := iidLaw ν with hP
  set c := lawVar ν / eps ^ 2 with hc
  have hc0 : 0 < c := by positivity
  -- Step 1: coupling bound
  refine (dEtaL_map_le P (measurable_rawU eps ν) (measurable_rawV eps ν) hγ.le).trans ?_
  -- Step 2: Hölder
  set f : (ℕ → ℝ) → ℝ≥0∞ := fun g => ENNReal.ofReal (|rawU eps ν g - rawV eps ν g|) with hf
  set gg : (ℕ → ℝ) → ℝ≥0∞ := fun g => ENNReal.ofReal (Real.exp (γ * max (rawU eps ν g) (rawV eps ν g))) with hgg
  have hfm : Measurable f :=
    ((measurable_rawU eps ν).sub (measurable_rawV eps ν)).abs.ennreal_ofReal
  have hggm : Measurable gg :=
    (measurable_const.mul ((measurable_rawU eps ν).max (measurable_rawV eps ν))).exp.ennreal_ofReal
  have hprod : ∀ g, ENNReal.ofReal (|rawU eps ν g - rawV eps ν g| * Real.exp (γ * max (rawU eps ν g) (rawV eps ν g))) = (f * gg) g := by
    intro g; simp only [Pi.mul_apply, hf, hgg]; rw [ENNReal.ofReal_mul (abs_nonneg _)]
  simp_rw [hprod]
  refine (ENNReal.lintegral_mul_le_Lp_mul_Lq P Real.HolderConjugate.two_two hfm.aemeasurable
    hggm.aemeasurable).trans ?_
  -- Step 3: the second moment factor
  have hsq : ∫⁻ g, f g ^ (2 : ℝ) ∂P ≤ ENNReal.ofReal (cPlus * vhi ^ 3 / vlo / eps ^ 2) := by
    have e : ∀ g, f g ^ (2 : ℝ) = ENNReal.ofReal (c ^ 2 * (stopSum eps g - ((gapSegLen eps g).toNat : ℝ)) ^ 2) := by
      intro g
      simp only [hf, ENNReal.rpow_two]
      rw [← ENNReal.ofReal_pow (abs_nonneg _), sq_abs]
      congr 1
      simp only [rawU, rawV, hc]
      ring
    simp_rw [e]
    have hcsq : ∀ g, ENNReal.ofReal (c ^ 2 * (stopSum eps g - ((gapSegLen eps g).toNat : ℝ)) ^ 2) =
        ENNReal.ofReal (c ^ 2) * ENNReal.ofReal ((stopSum eps g - ((gapSegLen eps g).toNat : ℝ)) ^ 2) :=
      fun g => ENNReal.ofReal_mul (by positivity)
    simp_rw [hcsq]
    have hm2 : Measurable fun g : ℕ → ℝ =>
        ENNReal.ofReal ((stopSum eps g - ((gapSegLen eps g).toNat : ℝ)) ^ 2) :=
      (((measurable_stopSum eps).sub (measurable_toNat_gapSegLen eps)).pow_const 2).ennreal_ofReal
    rw [lintegral_const_mul _ hm2]
    calc ENNReal.ofReal (c ^ 2) * ∫⁻ g, ENNReal.ofReal ((stopSum eps g - ((gapSegLen eps g).toNat : ℝ)) ^ 2) ∂P
        ≤ ENNReal.ofReal (c ^ 2) * (ENNReal.ofReal (lawVar ν) * ENNReal.ofReal (lawC eps ν)) := by
          gcongr
          exact h.lintegral_stopSum_sub_sq_le hvlo heps
      _ = ENNReal.ofReal (c ^ 2 * lawVar ν * lawC eps ν) := by
          rw [← ENNReal.ofReal_mul hv0.le, ← ENNReal.ofReal_mul (by positivity)]
          ring_nf
      _ ≤ ENNReal.ofReal (cPlus * vhi ^ 3 / vlo / eps ^ 2) := by
          refine ENNReal.ofReal_le_ofReal ?_
          have hCle := (h.oneLayer hvlo heps).2.2
          have hvle := h.var_le
          have hcP := cPlus_pos
          calc c ^ 2 * lawVar ν * lawC eps ν ≤ c ^ 2 * lawVar ν * (cPlus * eps ^ 2 / vlo) := by
                gcongr
            _ = cPlus * lawVar ν ^ 3 / vlo / eps ^ 2 := by rw [hc]; field_simp
            _ ≤ cPlus * vhi ^ 3 / vlo / eps ^ 2 := by gcongr
  -- Step 4: the exponential factor
  have hexpU : ∫⁻ g, ENNReal.ofReal (Real.exp (2 * γ * rawU eps ν g)) ∂P ≤ ENNReal.ofReal (1 + cTail) := by
    have hlam : 0 < 2 * γ * c := by positivity
    have hlamθ : 2 * γ * c ≤ θ / 4 := by
      have := hE2; rw [hc]
      calc 2 * γ * (lawVar ν / eps ^ 2) ≤ 2 * γ * vhi / eps ^ 2 := by
            rw [mul_div_assoc']
            gcongr
            exact h.var_le
        _ ≤ θ / 4 := this.trans (min_le_left _ _)
    have hlamB : 2 * γ * c ≤ θ ^ 2 / (16 * B) := by
      have := hE2; rw [hc]
      calc 2 * γ * (lawVar ν / eps ^ 2) ≤ 2 * γ * vhi / eps ^ 2 := by
            rw [mul_div_assoc']
            gcongr
            exact h.var_le
        _ ≤ θ ^ 2 / (16 * B) := this.trans (min_le_right _ _)
    have e : ∀ g, Real.exp (2 * γ * rawU eps ν g) = Real.exp (2 * γ * c * stopSum eps g) := by
      intro g; simp only [rawU, hc]; ring_nf
    simp_rw [e]
    refine (lintegral_exp_stopSum_le h hvlo hθ heps hlam hlamθ hlamB).trans ?_
    have e2 : ∀ g, Real.exp (4 * (2 * γ * c) * ((gapSegLen eps g).toNat : ℝ)) =
        Real.exp (8 * γ * rawV eps ν g) := by
      intro g; simp only [rawV, hc]; ring_nf
    simp_rw [e2]
    have htail : ∀ r : ℝ, 0 < r → P.real {g | r ≤ rawV eps ν g} ≤ cTail * Real.exp (-(rPrime vlo vhi * r)) :=
      fun r hr => h.tail_rawV hvlo heps hr
    have hV0 : ∀ g, 0 ≤ rawV eps ν g := fun g => by simp only [rawV]; positivity
    have h8 := lintegral_exp_le_of_tail_real P (measurable_rawV eps ν) hV0 hC.le (by positivity)
      (show 8 * γ ≤ rPrime vlo vhi / 2 by linarith) htail
    calc (∫⁻ g, ENNReal.ofReal (Real.exp (8 * γ * rawV eps ν g)) ∂P) ^ ((1 : ℝ) / 2)
        ≤ ENNReal.ofReal (1 + cTail) ^ ((1 : ℝ) / 2) := by gcongr
      _ ≤ ENNReal.ofReal (1 + cTail) := by
          rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num)]
          refine ENNReal.ofReal_le_ofReal ?_
          exact Real.rpow_le_self_of_one_le (by linarith) (by norm_num)
  have hexpV : ∫⁻ g, ENNReal.ofReal (Real.exp (2 * γ * rawV eps ν g)) ∂P ≤ ENNReal.ofReal (1 + cTail) := by
    have htail : ∀ r : ℝ, 0 < r → P.real {g | r ≤ rawV eps ν g} ≤ cTail * Real.exp (-(rPrime vlo vhi * r)) :=
      fun r hr => h.tail_rawV hvlo heps hr
    have hV0 : ∀ g, 0 ≤ rawV eps ν g := fun g => by simp only [rawV]; positivity
    exact lintegral_exp_le_of_tail_real P (measurable_rawV eps ν) hV0 hC.le (by positivity)
      (show 2 * γ ≤ rPrime vlo vhi / 2 by linarith) htail
  have hexp : ∫⁻ g, gg g ^ (2 : ℝ) ∂P ≤ ENNReal.ofReal (2 * (1 + cTail)) := by
    have e : ∀ g, gg g ^ (2 : ℝ) ≤ ENNReal.ofReal (Real.exp (2 * γ * rawU eps ν g)) +
        ENNReal.ofReal (Real.exp (2 * γ * rawV eps ν g)) := by
      intro g
      simp only [hgg, ENNReal.rpow_two]
      rw [← ENNReal.ofReal_pow (Real.exp_pos _).le, ← Real.exp_nat_mul]
      push_cast
      rcases le_total (rawU eps ν g) (rawV eps ν g) with hUV | hUV
      · rw [max_eq_right hUV]
        refine le_add_left (ENNReal.ofReal_le_ofReal (le_of_eq ?_))
        ring_nf
      · rw [max_eq_left hUV]
        refine le_add_right (ENNReal.ofReal_le_ofReal (le_of_eq ?_))
        ring_nf
    calc ∫⁻ g, gg g ^ (2 : ℝ) ∂P
        ≤ ∫⁻ g, (ENNReal.ofReal (Real.exp (2 * γ * rawU eps ν g)) +
            ENNReal.ofReal (Real.exp (2 * γ * rawV eps ν g))) ∂P := lintegral_mono e
      _ = (∫⁻ g, ENNReal.ofReal (Real.exp (2 * γ * rawU eps ν g)) ∂P) +
            ∫⁻ g, ENNReal.ofReal (Real.exp (2 * γ * rawV eps ν g)) ∂P :=
          lintegral_add_left ((measurable_const.mul (measurable_rawU eps ν)).exp.ennreal_ofReal) _
      _ ≤ ENNReal.ofReal (1 + cTail) + ENNReal.ofReal (1 + cTail) := add_le_add hexpU hexpV
      _ = ENNReal.ofReal (2 * (1 + cTail)) := by
          rw [← ENNReal.ofReal_add (by positivity) (by positivity)]; congr 1; ring
  -- Step 5: combine
  calc (∫⁻ g, f g ^ (2 : ℝ) ∂P) ^ (1 / (2 : ℝ)) * (∫⁻ g, gg g ^ (2 : ℝ) ∂P) ^ (1 / (2 : ℝ))
      ≤ ENNReal.ofReal (cPlus * vhi ^ 3 / vlo / eps ^ 2) ^ (1 / (2 : ℝ)) *
          ENNReal.ofReal (2 * (1 + cTail)) ^ (1 / (2 : ℝ)) := by gcongr
    _ = ENNReal.ofReal (kEndpoint vlo vhi / eps) := by
        have hA0 : 0 ≤ cPlus * vhi ^ 3 / vlo / eps ^ 2 :=
          div_nonneg (div_nonneg (mul_nonneg cPlus_pos.le (pow_nonneg hvhi.le 3)) hvlo.le) hE.le
        have hB0 : 0 ≤ 2 * (1 + cTail) := by linarith [cTail_pos]
        rw [ENNReal.ofReal_rpow_of_nonneg hA0 (by norm_num),
          ENNReal.ofReal_rpow_of_nonneg hB0 (by norm_num),
          ← ENNReal.ofReal_mul (by positivity)]
        congr 1
        unfold kEndpoint
        rw [← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow, Real.sqrt_div' _ hE.le, Real.sqrt_sq hepspos.le]
        ring

end

end PGM
