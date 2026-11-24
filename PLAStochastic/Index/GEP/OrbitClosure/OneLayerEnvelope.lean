import PLAStochastic.Index.GEP.OrbitClosure.JointStop
import PLAStochastic.Index.GEP.OrbitClosure.StoppingSums
import PLAStochastic.Index.GEP.OrbitClosure.SumDensity

/-!
# WP2: the one-layer envelope (`density-tail.md` §2 proposition, with `prop:transfer`)

For `ρ` in `MomClass b β vmin` with `E e^{θ₁ X} ≤ B₁` and a local bound `Dm`, the next
normalised layer law satisfies `lawPhi eps ρ ≤ K e^{-c z} 1_{z > 0} dz` for all
`eps ≥ e₁(Dm)`, with `K, c` **independent of `Dm`**.  This independence is the forgetting of
`prop:transfer` (`research/2026-09-25-kep-proof/tex/main.tex` L272–356) and makes the orbit
induction close with the fixed bound `max(D, K)`.

Proof of `stopLaw_le`:
1. `map_stopSum_eq_sum`: `Law(S_T) = ∑_t ν_t`, `ν_t = stopMeas eps ρ t` (`T < ∞` a.s. by
   `momClass_oneLayer`).
2. `F n = L₀/√n + Dm e^{-c₂(n-2)/Dm²}` from `locBd_convPow` (`n ≥ 2`) and `F 1 ≥ Dm`
   (`convPow_one`); `F` is nonincreasing.
3. `stopMeas_le_kernel` for `t > 2 eps`, `stopMeas_eq_zero` otherwise; `withDensity_tsum`.
4. `C₁ F(⌊t/2⌋)/t ≤ √3 C₁ L₀ t^{-3/2} + C₁ t⁻¹ Dm e^{-c₂(⌊t/2⌋-2)/Dm²}`, then `sum_kernel_le`
   and `sum_aux_le`: `∑_t h_t(a) ≤ K'/E · e^{-(γ₁/4) a/E}` for `a ≥ 0`, `K' = C₁(√3 L₀ K + 1)`.
5. `S_T > 0` a.s. (positive gaps, `T ≥ 1`) restricts the bound to `(0, ∞)`.

Proof of `lawPhi_envelope`: `lawPhi eps ρ = Law(S_T / C)`, `C = lawC eps ρ`;
`map_div_const_le` rescales; `eps²/(128 b) ≤ C ≤ cPlus eps²/vmin` (`momClass_oneLayer`) gives
`C h(C z) ≤ (cPlus K'/vmin) e^{-(γ₁/(512 b)) z}`.
-/

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

/-- A local bound is monotone in its constant. -/
private theorem locBd_mono_one {D D' : ℝ} {μ : Measure ℝ} (h : LocBd D μ) (hDD : D ≤ D') :
    LocBd D' μ := fun A hA =>
  (h A hA).trans (mul_le_mul_left (ENNReal.ofReal_le_ofReal hDD) _)

/-- `⌊t/2⌋ ≥ t/3` in the form `t⁻¹ ⌊t/2⌋^{-1/2} ≤ √3 t^{-3/2}` (also for `t ≤ 1`). -/
private theorem inv_mul_inv_sqrt_half_le (t : ℕ) :
    (t : ℝ)⁻¹ * (Real.sqrt ((t / 2 : ℕ) : ℝ))⁻¹ ≤ Real.sqrt 3 * ((t : ℝ) * Real.sqrt t)⁻¹ := by
  rcases Nat.eq_zero_or_pos (t / 2) with h0 | hr
  · rw [h0, Nat.cast_zero, Real.sqrt_zero, inv_zero, mul_zero]
    positivity
  · have ht2 : 2 ≤ t := by omega
    have ht0 : (0 : ℝ) < t := by exact_mod_cast (show 0 < t by omega)
    have hr0 : (0 : ℝ) < ((t / 2 : ℕ) : ℝ) := by exact_mod_cast hr
    have htr : (t : ℝ) ≤ 3 * ((t / 2 : ℕ) : ℝ) := by exact_mod_cast (show t ≤ 3 * (t / 2) by omega)
    have hsq : Real.sqrt t ≤ Real.sqrt 3 * Real.sqrt ((t / 2 : ℕ) : ℝ) := by
      rw [← Real.sqrt_mul (by norm_num)]
      exact Real.sqrt_le_sqrt htr
    have e1 : (t : ℝ)⁻¹ * (Real.sqrt ((t / 2 : ℕ) : ℝ))⁻¹ =
        1 / ((t : ℝ) * Real.sqrt ((t / 2 : ℕ) : ℝ)) := by
      rw [one_div, mul_inv]
    have e2 : Real.sqrt 3 * ((t : ℝ) * Real.sqrt t)⁻¹ = Real.sqrt 3 / ((t : ℝ) * Real.sqrt t) := by
      rw [div_eq_mul_inv]
    rw [e1, e2, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_left hsq ht0.le]

/-- A stop has a positive key: `ν_t(-∞, 0] = 0`. -/
private theorem stopMeas_Iic_eq_zero {eps : ℝ} (heps : 0 ≤ eps) {ρ : ProbabilityMeasure ℝ}
    (hpos : (ρ : Measure ℝ) (Iic 0) = 0) (t : ℕ) : stopMeas eps ρ t (Iic 0) = 0 := by
  rcases Nat.eq_zero_or_pos t with rfl | ht
  · rw [stopMeas_eq_zero heps ρ (by simp only [Nat.cast_zero]; linarith)]
    rfl
  · have hm : Measurable fun g : ℕ → ℝ => gapKeys g t :=
      (measurable_pi_apply t).comp measurable_gapKeys
    rw [stopMeas, Measure.map_apply hm measurableSet_Iic]
    refine le_antisymm ((Measure.restrict_apply_le _ _).trans (le_of_eq ?_)) zero_le
    rw [measure_eq_zero_iff_ae_notMem]
    filter_upwards [ae_pos_iidLaw hpos] with g hg
    simp only [Set.mem_preimage, Set.mem_Iic, not_le, gapKeys]
    exact Finset.sum_pos (fun i _ => hg i) (Finset.nonempty_range_iff.2 ht.ne')

/-- The law of the stopped sum is the sum of the joint stopping measures. -/
theorem map_stopSum_eq_sum {eps : ℝ} {ρ : ProbabilityMeasure ℝ}
    (hfin : ∀ᵐ g ∂(iidLaw ρ), gapSegLen eps g ≠ ⊤) :
    (iidLaw ρ).map (stopSum eps) = Measure.sum (stopMeas eps ρ) := by
  ext A hA
  rw [Measure.map_apply (measurable_stopSum eps) hA, Measure.sum_apply _ hA]
  have hT : Measurable (gapSegLen eps) := (isStoppingRule_gapSegLen eps).measurable
  set B : ℕ → Set (ℕ → ℝ) := fun t => {g | gapSegLen eps g = (t : ℕ∞)} with hBdef
  have hB : ∀ t, MeasurableSet (B t) := fun t => hT (measurableSet_singleton _)
  have hS : ∀ t, stopMeas eps ρ t A = iidLaw ρ (stopSum eps ⁻¹' A ∩ B t) := by
    intro t
    have hm : Measurable fun g : ℕ → ℝ => gapKeys g t :=
      (measurable_pi_apply t).comp measurable_gapKeys
    rw [stopMeas, Measure.map_apply hm hA, Measure.restrict_apply (hm hA)]
    congr 1
    ext g
    simp only [Set.mem_inter_iff, Set.mem_preimage, hBdef, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨?_, h2⟩
      rw [stopSum, h2, ENat.toNat_natCast]
      exact h1
    · rintro ⟨h1, h2⟩
      refine ⟨?_, h2⟩
      rw [stopSum, h2, ENat.toNat_natCast] at h1
      exact h1
  simp_rw [hS]
  have hdisj : Pairwise (Function.onFun Disjoint fun t => stopSum eps ⁻¹' A ∩ B t) := by
    intro i j hij
    refine Set.disjoint_left.2 fun g hi hj => hij ?_
    have := hi.2.symm.trans hj.2
    exact_mod_cast this
  rw [← measure_iUnion hdisj fun t => (measurable_stopSum eps hA).inter (hB t)]
  refine measure_congr ?_
  filter_upwards [hfin] with g hg
  obtain ⟨t, ht⟩ := ENat.ne_top_iff_exists.1 hg
  apply propext
  constructor
  · intro h
    exact Set.mem_iUnion.2 ⟨t, h, ht.symm⟩
  · intro h
    obtain ⟨_, h1, _⟩ := Set.mem_iUnion.1 h
    exact h1

/-- Rescaling a density bound: `Law(X / C)` has density `C h(C z)`. -/
theorem map_div_const_le {μ : Measure ℝ} {h : ℝ → ℝ}
    (hμ : μ ≤ volume.withDensity fun x => ENNReal.ofReal (h x)) {C : ℝ} (hC : 0 < C) :
    μ.map (fun x => x / C) ≤ volume.withDensity fun z => ENNReal.ofReal (C * h (C * z)) := by
  rw [Measure.le_iff] at hμ ⊢
  intro A hA
  have hmeas : Measurable fun x : ℝ => x / C := measurable_id.div_const C
  have hpre : MeasurableSet ((fun x : ℝ => x / C) ⁻¹' A) := hmeas hA
  rw [Measure.map_apply hmeas hA]
  refine (hμ _ hpre).trans (le_of_eq ?_)
  rw [withDensity_apply _ hpre, withDensity_apply _ hA]
  have hvol : (volume : Measure ℝ) = ENNReal.ofReal C • (volume.map fun z => C * z) := by
    rw [Real.map_volume_mul_left hC.ne', smul_smul, ← ENNReal.ofReal_mul hC.le,
      abs_of_pos (inv_pos.2 hC), mul_inv_cancel₀ hC.ne', ENNReal.ofReal_one, one_smul]
  have hemb : MeasurableEmbedding fun z : ℝ => C * z :=
    (Homeomorph.mulLeft₀ C hC.ne').measurableEmbedding
  calc ∫⁻ x in (fun x => x / C) ⁻¹' A, ENNReal.ofReal (h x)
      = ∫⁻ x, ((fun x => x / C) ⁻¹' A).indicator (fun x => ENNReal.ofReal (h x)) x :=
        (lintegral_indicator hpre _).symm
    _ = ENNReal.ofReal C * ∫⁻ z, ((fun x => x / C) ⁻¹' A).indicator
          (fun x => ENNReal.ofReal (h x)) (C * z) := by
        conv_lhs => rw [hvol]
        rw [lintegral_smul_measure, hemb.lintegral_map, smul_eq_mul]
    _ = ENNReal.ofReal C * ∫⁻ z, A.indicator (fun z => ENNReal.ofReal (h (C * z))) z := by
        congr 1
        refine lintegral_congr fun z => ?_
        have e : C * z / C = z := mul_div_cancel_left₀ z hC.ne'
        by_cases hz : z ∈ A
        · rw [Set.indicator_of_mem (show C * z ∈ (fun x => x / C) ⁻¹' A by
            rw [Set.mem_preimage, e]; exact hz), Set.indicator_of_mem hz]
        · rw [Set.indicator_of_notMem (show C * z ∉ (fun x => x / C) ⁻¹' A by
            rw [Set.mem_preimage, e]; exact hz), Set.indicator_of_notMem hz]
    _ = ∫⁻ z in A, ENNReal.ofReal (C * h (C * z)) := by
        rw [lintegral_indicator hA, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        refine lintegral_congr fun z => ?_
        rw [ENNReal.ofReal_mul hC.le]

/-- **The stopped sum has an exponential density envelope** on the time scale `E = eps²`. -/
theorem stopLaw_le {b β vmin θ₁ B₁ : ℝ} (hvmin0 : 0 < vmin) (hvb : vmin ≤ b) (hβ1 : 1 ≤ β)
    (hθ₁ : 0 < θ₁) (hB₁ : 0 < B₁) :
    ∃ K γ : ℝ, 0 < K ∧ 0 < γ ∧ ∀ Dm : ℝ, 0 < Dm → ∃ e : ℝ, ∀ eps, e ≤ eps →
      ∀ ρ : ProbabilityMeasure ℝ, MomClass b β vmin ρ → ExpMom θ₁ B₁ ρ →
        LocBd Dm (ρ : Measure ℝ) →
        (iidLaw ρ).map (stopSum eps) ≤ volume.withDensity fun a =>
          ENNReal.ofReal ((Ioi (0 : ℝ)).indicator
            (fun a => K / eps ^ 2 * Real.exp (-γ * a / eps ^ 2)) a) := by
  obtain ⟨L₀, c₂, hL₀, hc₂, hloc⟩ := locBd_convPow hvmin0 hvb hβ1
  obtain ⟨C₁, γ₁, e₃, hC₁, hγ₁, hker⟩ := stopMeas_le_kernel (b := b) (β := β) hvmin0 hθ₁ hB₁
  obtain ⟨K₁, hK₁, hsumk⟩ := sum_kernel_le hγ₁
  refine ⟨C₁ * (Real.sqrt 3 * L₀ * K₁ + 1), γ₁ / 4, by positivity, by positivity,
    fun Dm hDm => ?_⟩
  obtain ⟨e₄, hsuma⟩ := sum_aux_le hγ₁ hc₂ hDm
  refine ⟨max (max e₃ e₄) (epsZero b β), fun eps heps ρ hρ hexp hρD => ?_⟩
  have he₃ : e₃ ≤ eps := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) heps
  have he₄ : e₄ ≤ eps := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) heps
  have hez : epsZero b β ≤ eps := le_trans (le_max_right _ _) heps
  have heps1 : 1 ≤ eps := (one_le_epsZero b β).trans hez
  have heps0 : 0 ≤ eps := by linarith
  have hE1 : 1 ≤ eps ^ 2 := by nlinarith
  obtain ⟨hfin, -, -⟩ := momClass_oneLayer hvmin0 hez hρ
  -- the local bounds `F n = L₀/√n + Dm e^{-c₂(n-2)/Dm²}`
  set F : ℕ → ℝ := fun n => L₀ / Real.sqrt n + Dm * Real.exp (-c₂ * ((n : ℝ) - 2) / Dm ^ 2)
    with hFdef
  have hF : ∀ n, 1 ≤ n → LocBd (F n) (convPow (ρ : Measure ℝ) n) := by
    intro n hn
    rcases Nat.lt_or_ge n 2 with hn2 | hn2
    · obtain rfl : n = 1 := by omega
      rw [convPow_one]
      refine locBd_mono_one hρD ?_
      have e : -c₂ * (((1 : ℕ) : ℝ) - 2) / Dm ^ 2 = c₂ / Dm ^ 2 := by push_cast; ring
      have h1 : 1 ≤ Real.exp (-c₂ * (((1 : ℕ) : ℝ) - 2) / Dm ^ 2) :=
        Real.one_le_exp (by rw [e]; positivity)
      have h2 : 0 ≤ L₀ / Real.sqrt ((1 : ℕ) : ℝ) := by positivity
      show Dm ≤ L₀ / Real.sqrt ((1 : ℕ) : ℝ) + Dm * Real.exp (-c₂ * (((1 : ℕ) : ℝ) - 2) / Dm ^ 2)
      nlinarith
    · exact hloc ρ Dm hDm hρ hρD n hn2
  have hFa : ∀ n m, 1 ≤ n → n ≤ m → F m ≤ F n := by
    intro n m hn hnm
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
    have hnm' : (n : ℝ) ≤ m := by exact_mod_cast hnm
    exact add_le_add (div_le_div_of_nonneg_left hL₀.le (Real.sqrt_pos.2 hn0)
      (Real.sqrt_le_sqrt hnm')) (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2
        (div_le_div_of_nonneg_right (by nlinarith) (sq_nonneg Dm))) hDm.le)
  -- the densities of the joint stopping measures
  set dens : ℕ → ℝ → ℝ≥0∞ := fun t a => ENNReal.ofReal (C₁ / t * F (t / 2) *
    Real.exp (-γ₁ * (eps ^ 2 / t + t / eps ^ 2 + qdev t a))) with hdens
  have hmd : ∀ t, Measurable (dens t) := by
    intro t
    have hq : Measurable fun x : ℝ => qdev t x :=
      Continuous.measurable (by unfold qdev; fun_prop)
    simp only [hdens]
    fun_prop
  have hν : ∀ t, stopMeas eps ρ t ≤ volume.withDensity (dens t) := by
    intro t
    by_cases ht : 2 * eps < t
    · exact hker eps he₃ ρ hρ hexp F hF hFa t ht
    · rw [stopMeas_eq_zero heps0 ρ (not_lt.1 ht)]
      exact Measure.zero_le _
  have hν' : ∀ t A, MeasurableSet A →
      stopMeas eps ρ t A ≤ ∫⁻ x in A, (Ioi 0).indicator (dens t) x := by
    intro t A hA
    rw [setLIntegral_indicator measurableSet_Ioi]
    calc stopMeas eps ρ t A ≤ stopMeas eps ρ t (Ioi 0 ∩ A ∪ Iic 0) := by
          refine measure_mono fun x hx => ?_
          by_cases h0 : 0 < x
          · exact Or.inl ⟨h0, hx⟩
          · exact Or.inr (not_lt.1 h0)
      _ ≤ stopMeas eps ρ t (Ioi 0 ∩ A) + stopMeas eps ρ t (Iic 0) := measure_union_le _ _
      _ = stopMeas eps ρ t (Ioi 0 ∩ A) := by
          rw [stopMeas_Iic_eq_zero heps0 hρ.pos t, add_zero]
      _ ≤ volume.withDensity (dens t) (Ioi 0 ∩ A) := hν t _
      _ = ∫⁻ x in Ioi 0 ∩ A, dens t x := withDensity_apply _ (measurableSet_Ioi.inter hA)
  -- the pointwise bound of the density series
  have hterm : ∀ t : ℕ, ∀ x : ℝ, dens t x ≤
      ENNReal.ofReal (Real.sqrt 3 * C₁ * L₀) * ENNReal.ofReal (((t : ℝ) * Real.sqrt t)⁻¹ *
          Real.exp (-γ₁ * (eps ^ 2 / t + t / eps ^ 2 + qdev t x))) +
        ENNReal.ofReal C₁ * ENNReal.ofReal ((t : ℝ)⁻¹ *
          (Dm * Real.exp (-c₂ * (((t / 2 : ℕ) : ℝ) - 2) / Dm ^ 2)) *
          Real.exp (-γ₁ * (eps ^ 2 / t + t / eps ^ 2 + qdev t x))) := by
    intro t x
    rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul hC₁.le,
      ← ENNReal.ofReal_add (by positivity) (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    set ex := Real.exp (-γ₁ * (eps ^ 2 / t + t / eps ^ 2 + qdev t x)) with hex
    set e2 := Real.exp (-c₂ * (((t / 2 : ℕ) : ℝ) - 2) / Dm ^ 2) with he2
    have hFt : F (t / 2) = L₀ / Real.sqrt ((t / 2 : ℕ) : ℝ) + Dm * e2 := rfl
    rw [hFt]
    calc C₁ / t * (L₀ / Real.sqrt ((t / 2 : ℕ) : ℝ) + Dm * e2) * ex
        = C₁ * L₀ * ex * ((t : ℝ)⁻¹ * (Real.sqrt ((t / 2 : ℕ) : ℝ))⁻¹) +
            C₁ * ((t : ℝ)⁻¹ * (Dm * e2) * ex) := by ring
      _ ≤ C₁ * L₀ * ex * (Real.sqrt 3 * ((t : ℝ) * Real.sqrt t)⁻¹) +
            C₁ * ((t : ℝ)⁻¹ * (Dm * e2) * ex) :=
          add_le_add_left (mul_le_mul_of_nonneg_left (inv_mul_inv_sqrt_half_le t)
            (by positivity)) _
      _ = Real.sqrt 3 * C₁ * L₀ * (((t : ℝ) * Real.sqrt t)⁻¹ * ex) +
            C₁ * ((t : ℝ)⁻¹ * (Dm * e2) * ex) := by ring
  have hpt : ∀ x : ℝ, ∑' t, (Ioi 0).indicator (dens t) x ≤
      ENNReal.ofReal ((Ioi (0 : ℝ)).indicator (fun a => C₁ * (Real.sqrt 3 * L₀ * K₁ + 1) /
        eps ^ 2 * Real.exp (-(γ₁ / 4) * a / eps ^ 2)) x) := by
    intro x
    by_cases hx : x ∈ Ioi (0 : ℝ)
    · simp_rw [Set.indicator_of_mem hx]
      have hx0 : 0 ≤ x := le_of_lt hx
      calc ∑' t, dens t x
          ≤ ∑' t : ℕ, (ENNReal.ofReal (Real.sqrt 3 * C₁ * L₀) *
              ENNReal.ofReal (((t : ℝ) * Real.sqrt t)⁻¹ *
                Real.exp (-γ₁ * (eps ^ 2 / t + t / eps ^ 2 + qdev t x))) +
            ENNReal.ofReal C₁ * ENNReal.ofReal ((t : ℝ)⁻¹ *
              (Dm * Real.exp (-c₂ * (((t / 2 : ℕ) : ℝ) - 2) / Dm ^ 2)) *
              Real.exp (-γ₁ * (eps ^ 2 / t + t / eps ^ 2 + qdev t x)))) :=
            ENNReal.tsum_le_tsum fun t => hterm t x
        _ = ENNReal.ofReal (Real.sqrt 3 * C₁ * L₀) *
              ∑' t : ℕ, ENNReal.ofReal (((t : ℝ) * Real.sqrt t)⁻¹ *
                Real.exp (-γ₁ * (eps ^ 2 / t + t / eps ^ 2 + qdev t x))) +
            ENNReal.ofReal C₁ * ∑' t : ℕ, ENNReal.ofReal ((t : ℝ)⁻¹ *
              (Dm * Real.exp (-c₂ * (((t / 2 : ℕ) : ℝ) - 2) / Dm ^ 2)) *
              Real.exp (-γ₁ * (eps ^ 2 / t + t / eps ^ 2 + qdev t x))) := by
            rw [ENNReal.tsum_add, ENNReal.tsum_mul_left, ENNReal.tsum_mul_left]
        _ ≤ ENNReal.ofReal (Real.sqrt 3 * C₁ * L₀) *
              ENNReal.ofReal (K₁ / eps ^ 2 * Real.exp (-(γ₁ / 4) * x / eps ^ 2)) +
            ENNReal.ofReal C₁ *
              ENNReal.ofReal (1 / eps ^ 2 * Real.exp (-(γ₁ / 4) * x / eps ^ 2)) := by
            gcongr
            · exact hsumk _ hE1 x hx0
            · exact hsuma eps he₄ x hx0
        _ = ENNReal.ofReal (C₁ * (Real.sqrt 3 * L₀ * K₁ + 1) / eps ^ 2 *
              Real.exp (-(γ₁ / 4) * x / eps ^ 2)) := by
            rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul hC₁.le,
              ← ENNReal.ofReal_add (by positivity) (by positivity)]
            congr 1
            ring
    · simp_rw [Set.indicator_of_notMem hx]
      simp
  rw [map_stopSum_eq_sum hfin, Measure.le_iff]
  intro A hA
  rw [Measure.sum_apply _ hA, withDensity_apply _ hA]
  calc ∑' t, stopMeas eps ρ t A ≤ ∑' t, ∫⁻ x in A, (Ioi 0).indicator (dens t) x :=
        ENNReal.tsum_le_tsum fun t => hν' t A hA
    _ = ∫⁻ x in A, ∑' t, (Ioi 0).indicator (dens t) x :=
        (lintegral_tsum fun t => ((hmd t).indicator measurableSet_Ioi).aemeasurable).symm
    _ ≤ _ := lintegral_mono fun x => hpt x

/-- **The one-layer envelope.**  `K` and `c` do not depend on the input density bound `Dm`;
only the threshold does. -/
theorem lawPhi_envelope {b β vmin θ₁ B₁ : ℝ} (hvmin0 : 0 < vmin) (hvb : vmin ≤ b)
    (hβ1 : 1 ≤ β) (hθ₁ : 0 < θ₁) (hB₁ : 0 < B₁) :
    ∃ K c : ℝ, 0 < K ∧ 0 < c ∧ ∀ Dm : ℝ, 0 < Dm → ∃ e₁ : ℝ, ∀ eps, e₁ ≤ eps →
      ∀ ρ : ProbabilityMeasure ℝ, MomClass b β vmin ρ → ExpMom θ₁ B₁ ρ →
        LocBd Dm (ρ : Measure ℝ) → EnvBd K c (lawPhi eps ρ : Measure ℝ) := by
  obtain ⟨K', γ, hK', hγ, hstop⟩ := stopLaw_le hvmin0 hvb hβ1 hθ₁ hB₁
  have hb0 : 0 < b := hvmin0.trans_le hvb
  have hcP := cPlus_pos
  refine ⟨cPlus * K' / vmin, γ / (128 * b), by positivity, by positivity, fun Dm hDm => ?_⟩
  obtain ⟨e, he⟩ := hstop Dm hDm
  refine ⟨max e (epsZero b β), fun eps heps ρ hρ hexp hρD => ?_⟩
  have he' : e ≤ eps := le_trans (le_max_left _ _) heps
  have hez : epsZero b β ≤ eps := le_trans (le_max_right _ _) heps
  have heps1 : 1 ≤ eps := (one_le_epsZero b β).trans hez
  obtain ⟨-, hCm, hCp⟩ := momClass_oneLayer hvmin0 hez hρ
  set C := lawC eps ρ with hCdef
  have hE : 0 < eps ^ 2 := by positivity
  have hC : 0 < C := lt_of_lt_of_le (by positivity) hCm
  have hmap := map_div_const_le (he eps he' ρ hρ hexp hρD) hC
  have hlaw : (lawPhi eps ρ : Measure ℝ) =
      ((iidLaw ρ).map (stopSum eps)).map (fun x => x / C) := by
    have hdiv : Measurable fun x : ℝ => x / C := measurable_id.div_const C
    rw [Measure.map_map hdiv (measurable_stopSum eps)]
    rfl
  unfold EnvBd
  rw [hlaw]
  refine hmap.trans (withDensity_mono (Filter.Eventually.of_forall fun z => ?_))
  refine ENNReal.ofReal_le_ofReal ?_
  simp only [envFun, Set.indicator_apply, Set.mem_Ioi]
  by_cases hz : 0 < z
  · have hCz : 0 < C * z := mul_pos hC hz
    rw [if_pos hCz, if_pos hz]
    have h1 : C / eps ^ 2 ≤ cPlus / vmin := by
      rw [div_le_div_iff₀ hE hvmin0]
      rw [le_div_iff₀ hvmin0] at hCp
      linarith
    have h2 : 1 / (128 * b) ≤ C / eps ^ 2 := by
      rw [div_le_div_iff₀ (by positivity) hE]
      rw [div_le_iff₀ (by positivity)] at hCm
      linarith
    have hex : Real.exp (-γ * (C * z) / eps ^ 2) ≤ Real.exp (-(γ / (128 * b)) * z) := by
      refine Real.exp_le_exp.2 ?_
      have : γ / (128 * b) * z ≤ γ * (C * z) / eps ^ 2 := by
        calc γ / (128 * b) * z = γ * z * (1 / (128 * b)) := by ring
          _ ≤ γ * z * (C / eps ^ 2) := mul_le_mul_of_nonneg_left h2 (by positivity)
          _ = γ * (C * z) / eps ^ 2 := by ring
      rw [neg_mul, neg_mul, neg_div]
      exact neg_le_neg this
    calc C * (K' / eps ^ 2 * Real.exp (-γ * (C * z) / eps ^ 2))
        = C / eps ^ 2 * K' * Real.exp (-γ * (C * z) / eps ^ 2) := by ring
      _ ≤ cPlus / vmin * K' * Real.exp (-(γ / (128 * b)) * z) := by gcongr
      _ = cPlus * K' / vmin * Real.exp (-(γ / (128 * b)) * z) := by ring
  · have hCz : ¬ 0 < C * z := not_lt.2 (mul_nonpos_of_nonneg_of_nonpos hC.le (not_lt.1 hz))
    rw [if_neg hCz, if_neg hz, mul_zero]

end

end PGM
