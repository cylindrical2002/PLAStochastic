import PLAStochastic.Index.GEP.Response.Score.SegmentLengthDerivative

/-!
# WP4 leaf 4A-S, part 6: the derivative of the output test along the mixture path

`F_φ(ν) = E[φ_ψ(S_T / C_ε(ν))]` depends on `s` through the law of the path and through the
normalisation `C(s) = C_ε(ν_s)`.  Relative to the base law `ν̄ = ν_{s₀}` (a stopped functional,
`integral_stopped`),

  `F_φ(ν_s) = E_ν̄[L_s · φ_ψ(S_T / C(s))]`,  `L_s = ∏_{j<T} (1 + (s - s₀) h(g_j))`.

For a.e. path the integrand is differentiable at `s₀`: `L` is a polynomial, `C` is differentiable
(`hasDerivAt_lawC_mix`), and `φ_ψ` is differentiable at `Y = S_T / C(s₀)` because `Y` has an
absolutely continuous law and `φ_ψ' = ψ` Lebesgue-a.e. (`OutTest.ae_hasDerivAt_testFn`).  The
integrand is Lipschitz near `s₀` with constant `K (e^{κT} + e^{θ Y})` (AM–GM, `lip_key_bound`),
integrable by the stopping moment and the output moment (`joint-response.md` §5; PD §8.1 (29),
with Cauchy–Schwarz replaced by AM–GM).  Hence (`hasDerivAt_outFn_mix`)

  `d/ds F_φ(ν_s)|_{s₀} = ∫ I_φ d(ν₁ - ν₀) - (κ_φ / C) ∫ J_C d(ν₁ - ν₀) = ∫ J_φ d(ν₁ - ν₀)`,

with `I_φ = outIns` identified through `integral_tsum_insert` (PD (33)–(35)).
-/

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal NNReal

variable {ν₀ ν₁ : ProbabilityMeasure ℝ} {f₀ f₁ : ℝ → ℝ}

/-! ## Real inequalities -/

/-- `(n+1) q^n Y e^{2ηY} ≤ (4/κ) e^{κ/4} η⁻¹ (e^{κn} + e^{θ Y})` when `q ≤ e^{κ/4}`, `6η ≤ θ`. -/
theorem lip_key_bound {κ q η θ Y : ℝ} (hκ : 0 < κ) (hq1 : 1 ≤ q) (hq : q ≤ Real.exp (κ / 4))
    (hη : 0 < η) (hηθ : 6 * η ≤ θ) (hY : 0 ≤ Y) (n : ℕ) :
    ((n : ℝ) + 1) * q ^ n * (Y * Real.exp (2 * η * Y)) ≤
      4 / κ * Real.exp (κ / 4) / η * (Real.exp (κ * n) + Real.exp (θ * Y)) := by
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have h1 : (n : ℝ) + 1 ≤ 4 / κ * Real.exp (κ / 4) * Real.exp (κ / 4 * n) := by
    have := le_exp_div (t := (n : ℝ) + 1) (show 0 < κ / 4 by positivity)
    calc (n : ℝ) + 1 ≤ Real.exp (κ / 4 * ((n : ℝ) + 1)) / (κ / 4) := this
      _ = 4 / κ * Real.exp (κ / 4) * Real.exp (κ / 4 * n) := by
          rw [show κ / 4 * ((n : ℝ) + 1) = κ / 4 + κ / 4 * n by ring, Real.exp_add]
          field_simp
  have h2 : q ^ n ≤ Real.exp (κ / 4 * n) := by
    calc q ^ n ≤ Real.exp (κ / 4) ^ n := pow_le_pow_left₀ (by linarith) hq n
      _ = Real.exp (κ / 4 * n) := by rw [← Real.exp_nat_mul]; ring_nf
  have h3 : Y * Real.exp (2 * η * Y) ≤ Real.exp (3 * η * Y) / η := by
    have := le_exp_div (t := Y) hη
    calc Y * Real.exp (2 * η * Y) ≤ Real.exp (η * Y) / η * Real.exp (2 * η * Y) :=
          mul_le_mul_of_nonneg_right this (Real.exp_pos _).le
      _ = Real.exp (3 * η * Y) / η := by
          rw [div_mul_eq_mul_div, ← Real.exp_add]; ring_nf
  have h4 : Real.exp (κ / 2 * n) * Real.exp (3 * η * Y) ≤
      Real.exp (κ * n) + Real.exp (θ * Y) := by
    have hsq := two_mul_le_add_sq (Real.exp (κ / 2 * n)) (Real.exp (3 * η * Y))
    have e1 : Real.exp (κ / 2 * n) ^ 2 = Real.exp (κ * n) := by
      rw [← Real.exp_nat_mul]; ring_nf
    have e2 : Real.exp (3 * η * Y) ^ 2 = Real.exp (6 * η * Y) := by
      rw [← Real.exp_nat_mul]; ring_nf
    have e3 : Real.exp (6 * η * Y) ≤ Real.exp (θ * Y) :=
      Real.exp_le_exp.2 (mul_le_mul_of_nonneg_right hηθ hY)
    have hp : 0 ≤ Real.exp (κ / 2 * n) * Real.exp (3 * η * Y) := by positivity
    nlinarith
  have hA : 0 ≤ 4 / κ * Real.exp (κ / 4) := by positivity
  calc ((n : ℝ) + 1) * q ^ n * (Y * Real.exp (2 * η * Y))
      ≤ (4 / κ * Real.exp (κ / 4) * Real.exp (κ / 4 * n)) * Real.exp (κ / 4 * n) *
          (Real.exp (3 * η * Y) / η) := by
        gcongr
    _ = 4 / κ * Real.exp (κ / 4) / η * (Real.exp (κ / 2 * n) * Real.exp (3 * η * Y)) := by
        rw [show κ / 2 * (n : ℝ) = κ / 4 * n + κ / 4 * n by ring, Real.exp_add]
        field_simp
    _ ≤ 4 / κ * Real.exp (κ / 4) / η * (Real.exp (κ * n) + Real.exp (θ * Y)) := by
        gcongr

variable {η M : ℝ} {ψ : ℝ → ℝ}

/-- **The pointwise Lipschitz estimate** of `L_s φ(S / C(s))`. -/
theorem out_lip_pt (hψ : OutTest η M ψ) (hη : 0 < η) {κ q θ K₀ L C₀ c c' S l l' ds : ℝ}
    (hκ : 0 < κ) (hq1 : 1 ≤ q) (hq : q ≤ Real.exp (κ / 4)) (hηθ : 6 * η ≤ θ) (hK₀ : 0 ≤ K₀)
    (hC₀ : 0 < C₀) (hc : C₀ / 2 ≤ c) (hc' : C₀ / 2 ≤ c') (hcc : |c - c'| ≤ L * ds)
    (hds : 0 ≤ ds) (hS : 0 ≤ S) (n : ℕ) (hl' : |l'| ≤ q ^ n)
    (hll : |l - l'| ≤ n * q ^ n * (K₀ * ds)) :
    |l * testFn ψ (S / c) - l' * testFn ψ (S / c')| ≤
      (2 * K₀ * M + 4 * M * |L| / C₀) * (4 / κ * Real.exp (κ / 4) / η) *
        (Real.exp (κ * n) + Real.exp (θ * (S / C₀))) * ds := by
  have hM := hψ.nonneg
  set Y := S / C₀ with hYdef
  have hY : 0 ≤ Y := div_nonneg hS hC₀.le
  have hcpos : 0 < c := lt_of_lt_of_le (half_pos hC₀) hc
  have hc'pos : 0 < c' := lt_of_lt_of_le (half_pos hC₀) hc'
  have ha : 0 ≤ S / c := div_nonneg hS hcpos.le
  have hb : 0 ≤ S / c' := div_nonneg hS hc'pos.le
  have ha2 : S / c ≤ 2 * Y := by
    rw [hYdef, div_le_iff₀ hcpos]
    have : S / C₀ * C₀ = S := div_mul_cancel₀ S hC₀.ne'
    nlinarith
  have hb2 : S / c' ≤ 2 * Y := by
    rw [hYdef, div_le_iff₀ hc'pos]
    have : S / C₀ * C₀ = S := div_mul_cancel₀ S hC₀.ne'
    nlinarith
  have hA : |testFn ψ (S / c)| ≤ M * Real.exp (2 * η * Y) * (2 * Y) := by
    calc |testFn ψ (S / c)| ≤ M * Real.exp (η * (S / c)) * (S / c) := hψ.abs_testFn_le hη.le ha
      _ ≤ M * Real.exp (η * (2 * Y)) * (2 * Y) := by gcongr
      _ = M * Real.exp (2 * η * Y) * (2 * Y) := by ring_nf
  have hab : |S / c - S / c'| ≤ 4 * Y / C₀ * (|L| * ds) := by
    rw [div_sub_div _ _ hcpos.ne' hc'pos.ne', abs_div, abs_of_pos (mul_pos hcpos hc'pos)]
    have e : S * c' - c * S = S * (c' - c) := by ring
    rw [e, abs_mul, abs_of_nonneg hS, abs_sub_comm]
    have hcc' : |c - c'| ≤ |L| * ds := hcc.trans (by gcongr; exact le_abs_self L)
    have hden : C₀ ^ 2 / 4 ≤ c * c' := by nlinarith
    rw [div_le_iff₀ (mul_pos hcpos hc'pos)]
    calc S * |c - c'| ≤ S * (|L| * ds) := mul_le_mul_of_nonneg_left hcc' hS
      _ = 4 * Y / C₀ * (|L| * ds) * (C₀ ^ 2 / 4) := by rw [hYdef]; field_simp
      _ ≤ 4 * Y / C₀ * (|L| * ds) * (c * c') := by gcongr
  have hB : |testFn ψ (S / c) - testFn ψ (S / c')| ≤
      M * Real.exp (2 * η * Y) * (4 * Y / C₀ * (|L| * ds)) := by
    calc |testFn ψ (S / c) - testFn ψ (S / c')|
        ≤ M * Real.exp (η * max (S / c) (S / c')) * |S / c - S / c'| :=
          hψ.abs_testFn_sub_le hη.le ha hb
      _ ≤ M * Real.exp (η * (2 * Y)) * (4 * Y / C₀ * (|L| * ds)) := by
          have := max_le ha2 hb2
          gcongr
      _ = M * Real.exp (2 * η * Y) * (4 * Y / C₀ * (|L| * ds)) := by ring_nf
  have hkey := lip_key_bound hκ hq1 hq hη hηθ hY n
  have e : l * testFn ψ (S / c) - l' * testFn ψ (S / c') =
      (l - l') * testFn ψ (S / c) + l' * (testFn ψ (S / c) - testFn ψ (S / c')) := by ring
  rw [e]
  have hqn : 0 ≤ q ^ n := by positivity
  calc |(l - l') * testFn ψ (S / c) + l' * (testFn ψ (S / c) - testFn ψ (S / c'))|
      ≤ |l - l'| * |testFn ψ (S / c)| + |l'| * |testFn ψ (S / c) - testFn ψ (S / c')| := by
        rw [← abs_mul, ← abs_mul]; exact abs_add_le _ _
    _ ≤ (n * q ^ n * (K₀ * ds)) * (M * Real.exp (2 * η * Y) * (2 * Y)) +
          q ^ n * (M * Real.exp (2 * η * Y) * (4 * Y / C₀ * (|L| * ds))) := by
        gcongr
    _ = (2 * K₀ * M * n + 4 * M * |L| / C₀) * q ^ n * (Y * Real.exp (2 * η * Y)) * ds := by
        ring
    _ ≤ (2 * K₀ * M + 4 * M * |L| / C₀) * ((n + 1) * q ^ n * (Y * Real.exp (2 * η * Y))) *
          ds := by
        have h0 : 0 ≤ Y * Real.exp (2 * η * Y) := by positivity
        have h1 : 2 * K₀ * M * n + 4 * M * |L| / C₀ ≤
            (2 * K₀ * M + 4 * M * |L| / C₀) * (n + 1) := by
          have : 0 ≤ 4 * M * |L| / C₀ := by positivity
          have : 0 ≤ 2 * K₀ * M := by positivity
          have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
          nlinarith
        have := mul_le_mul_of_nonneg_right h1 (mul_nonneg (mul_nonneg hqn h0) hds)
        linarith [this]
    _ ≤ (2 * K₀ * M + 4 * M * |L| / C₀) * (4 / κ * Real.exp (κ / 4) / η *
          (Real.exp (κ * n) + Real.exp (θ * Y))) * ds := by
        gcongr
    _ = _ := by ring

/-! ## The output test as a stopped functional -/

theorem isStoppedFn_stopSum (eps : ℝ) : IsStoppedFn eps (stopSum eps) := by
  intro t g g' hT h
  have hT' : gapSegLen eps g' = t := (gapSegLen_eq_congr h).1 hT
  rw [stopSum, stopSum, hT, hT', ENat.toNat_natCast]
  exact gapKeys_congr h t le_rfl

theorem outFn_eq_integral (eps : ℝ) (ν : ProbabilityMeasure ℝ) (hψ : OutTest η M ψ) :
    outFn eps ν ψ = ∫ g, testFn ψ (stopSum eps g / lawC eps ν) ∂(iidLaw ν) := by
  rw [outFn]
  change ∫ y, testFn ψ y ∂((iidLaw ν).map fun g => stopSum eps g / lawC eps ν) = _
  exact integral_map ((measurable_stopSum eps).div_const _).aemeasurable
    hψ.measurable_testFn.aestronglyMeasurable

/-- **The output test along the path under the base law.** -/
theorem outFn_mix_eq (hS : MixSetup ν₀ ν₁ f₀ f₁) {s₀ : ℝ} (hs₀ : s₀ ∈ Ioo (0 : ℝ) 1) {s : ℝ}
    (hs : s ∈ Icc (0 : ℝ) 1) {eps : ℝ}
    (hfin : ∀ᵐ g ∂(iidLaw (mixPM ν₀ ν₁ s)), gapSegLen eps g ≠ ⊤)
    (hfin₀ : ∀ᵐ g ∂(iidLaw (mixPM ν₀ ν₁ s₀)), gapSegLen eps g ≠ ⊤) (hψ : OutTest η M ψ) :
    outFn eps (mixPM ν₀ ν₁ s) ψ = ∫ g, stopLik eps (mixRatio f₀ f₁ s₀ s) g *
      testFn ψ (stopSum eps g / lawC eps (mixPM ν₀ ν₁ s)) ∂(iidLaw (mixPM ν₀ ν₁ s₀)) := by
  rw [outFn_eq_integral eps _ hψ]
  have hΦm : Measurable fun g => testFn ψ (stopSum eps g / lawC eps (mixPM ν₀ ν₁ s)) :=
    hψ.measurable_testFn.comp ((measurable_stopSum eps).div_const _)
  have hΦ : IsStoppedFn eps fun g => testFn ψ (stopSum eps g / lawC eps (mixPM ν₀ ν₁ s)) :=
    (isStoppedFn_stopSum eps).comp fun x => testFn ψ (x / lawC eps (mixPM ν₀ ν₁ s))
  rw [(integral_stopped eps (mixPM ν₀ ν₁ s₀) (mixPM ν₀ ν₁ s)
    (measurable_mixRatioNN hS.meas₀ hS.meas₁ s₀ s) (hS.eq_withDensity hs₀ hs) hfin hfin₀
    hΦm hΦ).2]
  refine integral_congr_ae (Eventually.of_forall fun g => ?_)
  simp only [stopLik, hS.coe_ratioNN hs₀ hs]

/-! ## Identification of the direct term with the insertion kernel -/

/-- The derivative of the stopped likelihood at the base point, `∑_{i<T} h(g_i)`. -/
def lDer (eps : ℝ) (h : ℝ → ℝ) (g : ℕ → ℝ) : ℝ :=
  ∑ i ∈ Finset.range (gapSegLen eps g).toNat, h (g i)

theorem measurable_lDer (eps : ℝ) {h : ℝ → ℝ} (hh : Measurable h) : Measurable (lDer eps h) := by
  have hm : Measurable fun p : (ℕ → ℝ) × ℕ => ∑ i ∈ Finset.range p.2, h (p.1 i) :=
    measurable_from_prod_countable_left fun n => by
      change Measurable fun x : ℕ → ℝ => ∑ i ∈ Finset.range n, h (x i)
      exact Finset.measurable_sum _ fun i _ => hh.comp (measurable_pi_apply i)
  exact hm.comp (measurable_id.prodMk (measurable_gapSegLen_toNat eps))

/-- **`E[Φ ∑_{i<T} h(g_i)] = ∫ I_Φ d(ν₁ - ν₀)`** with the insertion kernel `insKernel`. -/
theorem integral_lDer_mul_eq (hS : MixSetup ν₀ ν₁ f₀ f₁) {s₀ : ℝ} (hs₀ : s₀ ∈ Ioo (0 : ℝ) 1)
    {eps : ℝ} (hfin₀ : ∀ᵐ g ∂(iidLaw (mixPM ν₀ ν₁ s₀)), gapSegLen eps g ≠ ⊤)
    {Φ : (ℕ → ℝ) → ℝ} (hΦm : Measurable Φ)
    (hTΦ : Integrable (fun g => ((gapSegLen eps g).toNat : ℝ) * |Φ g|)
      (iidLaw (mixPM ν₀ ν₁ s₀))) :
    Integrable (insKernel eps (mixPM ν₀ ν₁ s₀) Φ) (ν₀ : Measure ℝ) ∧
      Integrable (insKernel eps (mixPM ν₀ ν₁ s₀) Φ) (ν₁ : Measure ℝ) ∧
      ∫ g, lDer eps (mixScore f₀ f₁ s₀) g * Φ g ∂(iidLaw (mixPM ν₀ ν₁ s₀)) =
        ∫ x, insKernel eps (mixPM ν₀ ν₁ s₀) Φ x ∂(ν₁ : Measure ℝ) -
          ∫ x, insKernel eps (mixPM ν₀ ν₁ s₀) Φ x ∂(ν₀ : Measure ℝ) := by
  set νb := mixPM ν₀ ν₁ s₀ with hνb
  set G : ℕ → ℕ → (ℕ → ℝ) → ℝ := fun _ j =>
    {g : ℕ → ℝ | (j : ℕ∞) < gapSegLen eps g}.indicator Φ with hG
  have hGm : ∀ i j, Measurable (G i j) := fun _ j =>
    hΦm.indicator (measurableSet_lt_gapSegLen eps j)
  have hsum : ∑' i, ∑ j ∈ ({i} : Finset ℕ), ∫⁻ g, ‖G i j g‖ₑ ∂(iidLaw νb) ≠ ⊤ := by
    simp only [Finset.sum_singleton]
    rw [← lintegral_tsum fun i => (hGm i i).enorm.aemeasurable]
    refine ne_top_of_le_ne_top hTΦ.2.ne (lintegral_mono_ae ?_)
    filter_upwards [hfin₀] with g hg
    obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.1 hg
    have e : ∀ i : ℕ, ‖G i i g‖ₑ = ‖Φ g‖ₑ *
        {g : ℕ → ℝ | (i : ℕ∞) < gapSegLen eps g}.indicator (fun _ => (1 : ℝ≥0∞)) g := by
      intro i
      simp only [hG]
      by_cases hi : g ∈ {g : ℕ → ℝ | (i : ℕ∞) < gapSegLen eps g}
      · rw [Set.indicator_of_mem hi, Set.indicator_of_mem hi, mul_one]
      · rw [Set.indicator_of_notMem hi, Set.indicator_of_notMem hi, mul_zero, enorm_zero]
    simp_rw [e]
    rw [tsum_mul_indicator_lt hn.symm, Finset.sum_const, Finset.card_range, nsmul_eq_mul, ← hn,
      ENat.toNat_natCast, enorm_mul, Real.enorm_natCast, Real.enorm_abs, mul_comm]
  obtain ⟨hI₀, hI₁, hE⟩ := integral_tsum_insert νb ν₀ ν₁ (hS.measurable_score s₀)
    (hS.abs_score_le hs₀) (hS.score hs₀) ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
    (hS.le_smul_left hs₀) (hS.le_smul_right hs₀) (fun i => ({i} : Finset ℕ)) G hGm hsum
  have hk : (fun y => ∑' i, ∑ j ∈ ({i} : Finset ℕ),
      ∫ g, G i j (Function.update g j y) ∂(iidLaw νb)) = insKernel eps νb Φ := by
    funext y
    rw [insKernel]
    refine tsum_congr fun i => ?_
    rw [Finset.sum_singleton]
    refine integral_congr_ae (Eventually.of_forall fun g => ?_)
    have hupd : ∀ j < i, Function.update g i y j = g j := fun j hj =>
      Function.update_of_ne (Nat.ne_of_lt hj) _ _
    simp only [hG]
    by_cases hgi : (i : ℕ∞) < gapSegLen eps g
    · rw [Set.indicator_of_mem (show Function.update g i y ∈
        {g : ℕ → ℝ | (i : ℕ∞) < gapSegLen eps g} from (lt_gapSegLen_congr hupd).2 hgi),
        Set.indicator_of_mem (show g ∈ {g : ℕ → ℝ | (i : ℕ∞) < gapSegLen eps g} from hgi)]
    · rw [Set.indicator_of_notMem (show Function.update g i y ∉
        {g : ℕ → ℝ | (i : ℕ∞) < gapSegLen eps g} from fun h => hgi ((lt_gapSegLen_congr hupd).1 h)),
        Set.indicator_of_notMem (show g ∉ {g : ℕ → ℝ | (i : ℕ∞) < gapSegLen eps g} from hgi)]
  rw [hk] at hI₀ hI₁ hE
  refine ⟨hI₀, hI₁, ?_⟩
  rw [← hE]
  refine integral_congr_ae ?_
  filter_upwards [hfin₀] with g hg
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.1 hg
  have e : ∀ i : ℕ, ∑ j ∈ ({i} : Finset ℕ), G i j g * mixScore f₀ f₁ s₀ (g j) =
      (mixScore f₀ f₁ s₀ (g i) * Φ g) *
        {g : ℕ → ℝ | (i : ℕ∞) < gapSegLen eps g}.indicator (fun _ => (1 : ℝ)) g := by
    intro i
    rw [Finset.sum_singleton]
    simp only [hG]
    by_cases hi : g ∈ {g : ℕ → ℝ | (i : ℕ∞) < gapSegLen eps g}
    · rw [Set.indicator_of_mem hi, Set.indicator_of_mem hi, mul_one, mul_comm]
    · rw [Set.indicator_of_notMem hi, Set.indicator_of_notMem hi, mul_zero, zero_mul]
  simp_rw [e]
  rw [tsum_mul_indicator_lt hn.symm, lDer, ← hn, ENat.toNat_natCast, Finset.sum_mul]

/-! ## The derivative -/

/-- A.e. differentiability of the test at the normalised output. -/
theorem ae_hasDerivAt_testFn_output (hψ : OutTest η M ψ) {eps : ℝ} {ν : ProbabilityMeasure ℝ}
    (hac : (lawPhi eps ν : Measure ℝ) ≪ volume) (hC : 0 < lawC eps ν)
    (hSpos : ∀ᵐ g ∂(iidLaw ν), 0 < stopSum eps g) :
    ∀ᵐ g ∂(iidLaw ν), HasDerivAt (testFn ψ) (ψ (stopSum eps g / lawC eps ν))
      (stopSum eps g / lawC eps ν) := by
  have h1 : ∀ᵐ y ∂(lawPhi eps ν : Measure ℝ), 0 < y → HasDerivAt (testFn ψ) (ψ y) y :=
    hac.ae_le hψ.ae_hasDerivAt_testFn
  have h2 := ae_of_ae_map (((measurable_stopSum eps).div_const (lawC eps ν)).aemeasurable) h1
  filter_upwards [h2, hSpos] with g hg hg0 using hg (div_pos hg0 hC)

theorem stopLik_mixRatio_base (eps s₀ : ℝ) (g : ℕ → ℝ) :
    stopLik eps (mixRatio f₀ f₁ s₀ s₀) g = 1 := by
  simp [stopLik, mixRatio]

/-- **The derivative of the output test along the mixture path** (JR §5; PD §8.3). -/
theorem hasDerivAt_outFn_mix (hS : MixSetup ν₀ ν₁ f₀ f₁) {s₀ : ℝ} (hs₀ : s₀ ∈ Ioo (0 : ℝ) 1)
    {eps : ℝ} (hfin : ∀ s ∈ Icc (0 : ℝ) 1, ∀ᵐ g ∂(iidLaw (mixPM ν₀ ν₁ s)), gapSegLen eps g ≠ ⊤)
    {κ θY : ℝ} (hκ : 0 < κ)
    (hexp : Integrable (fun g => Real.exp (κ * (gapSegLen eps g).toNat))
      (iidLaw (mixPM ν₀ ν₁ s₀)))
    (hCpos : 0 < lawC eps (mixPM ν₀ ν₁ s₀))
    (hY : Integrable (fun g => Real.exp (θY * (stopSum eps g / lawC eps (mixPM ν₀ ν₁ s₀))))
      (iidLaw (mixPM ν₀ ν₁ s₀)))
    (hac : (lawPhi eps (mixPM ν₀ ν₁ s₀) : Measure ℝ) ≪ volume)
    (hSpos : ∀ᵐ g ∂(iidLaw (mixPM ν₀ ν₁ s₀)), 0 < stopSum eps g)
    (hη : 0 < η) (hηθ : 6 * η ≤ θY) (hψ : OutTest η M ψ) :
    HasDerivAt (fun s => outFn eps (mixPM ν₀ ν₁ s) ψ)
      (∫ x, outJ eps (mixPM ν₀ ν₁ s₀) ψ x ∂(ν₁ : Measure ℝ) -
        ∫ x, outJ eps (mixPM ν₀ ν₁ s₀) ψ x ∂(ν₀ : Measure ℝ)) s₀ := by
  set νb := mixPM ν₀ ν₁ s₀ with hνb
  set P := iidLaw νb with hP
  set C₀ := lawC eps νb with hC₀
  set K₀ := scoreBd s₀ with hK₀def
  have hK₀ := (scoreBd_pos hs₀).le
  have hM := hψ.nonneg
  have hs₀I : s₀ ∈ Icc (0 : ℝ) 1 := ⟨hs₀.1.le, hs₀.2.le⟩
  have hfin₀ := hfin s₀ hs₀I
  obtain ⟨hJ₀, hJ₁, hCd, L, hL⟩ := hasDerivAt_lawC_mix hS hs₀ hfin hκ hexp
  set C' := ∫ x, lawJC eps νb x ∂(ν₁ : Measure ℝ) - ∫ x, lawJC eps νb x ∂(ν₀ : Measure ℝ)
    with hC'
  set Cf : ℝ → ℝ := fun s => lawC eps (mixPM ν₀ ν₁ s) with hCf
  set ρ := baseRad s₀ κ with hρ
  have hρ0 : 0 < ρ := baseRad_pos hs₀ hκ
  set δ := min ρ (C₀ / (2 * (|L| + 1))) with hδ
  have hδ0 : 0 < δ := lt_min hρ0 (by positivity)
  have hδρ : δ ≤ ρ := min_le_left _ _
  have hball : Metric.ball s₀ δ ⊆ Metric.ball s₀ ρ := Metric.ball_subset_ball hδρ
  have hCnear : ∀ s ∈ Metric.ball s₀ δ, C₀ / 2 ≤ Cf s := by
    intro s hs
    have h1 := hL s (hball hs) s₀ (Metric.mem_ball_self hρ0)
    have hs' : |s - s₀| < δ := Metric.mem_ball.1 hs
    have h2 : |L| * |s - s₀| ≤ C₀ / 2 := by
      have : δ ≤ C₀ / (2 * (|L| + 1)) := min_le_right _ _
      have hLd : |L| * |s - s₀| ≤ (|L| + 1) * δ := by
        have := abs_nonneg L
        nlinarith [abs_nonneg (s - s₀)]
      calc |L| * |s - s₀| ≤ (|L| + 1) * δ := hLd
        _ ≤ (|L| + 1) * (C₀ / (2 * (|L| + 1))) := by gcongr
        _ = C₀ / 2 := by field_simp
    have h3 : L * |s - s₀| ≤ |L| * |s - s₀| :=
      mul_le_mul_of_nonneg_right (le_abs_self L) (abs_nonneg _)
    have h4 := (abs_le.1 h1).1
    simp only [hCf] at h4 ⊢
    linarith
  set q := 1 + ρ * K₀ with hq
  have hq1 : 1 ≤ q := by have := hρ0.le; nlinarith
  have hqe : q ≤ Real.exp (κ / 4) := pow_baseRad_le hs₀ hκ
  set Y : (ℕ → ℝ) → ℝ := fun g => stopSum eps g / C₀ with hYdef
  set F : ℝ → (ℕ → ℝ) → ℝ := fun s g =>
    stopLik eps (mixRatio f₀ f₁ s₀ s) g * testFn ψ (stopSum eps g / Cf s) with hF
  set K₂ := (2 * K₀ * M + 4 * M * |L| / C₀) * (4 / κ * Real.exp (κ / 4) / η) with hK₂
  set bnd : (ℕ → ℝ) → ℝ := fun g =>
    K₂ * (Real.exp (κ * (gapSegLen eps g).toNat) + Real.exp (θY * Y g)) with hbnd
  have hbnd_int : Integrable bnd P := (hexp.add hY).const_mul K₂
  have hK₂0 : 0 ≤ K₂ := by positivity
  have hbnd0 : ∀ g, 0 ≤ bnd g := fun g => by positivity
  -- the Lipschitz estimate
  have hlip : ∀ᵐ g ∂P, ∀ s ∈ Metric.ball s₀ δ, ∀ s' ∈ Metric.ball s₀ δ,
      |F s g - F s' g| ≤ bnd g * |s - s'| := by
    filter_upwards [hSpos] with g hg s hs s' hs'
    have hs1 : |s - s₀| ≤ ρ := (Metric.mem_ball.1 (hball hs)).le
    have hs2 : |s' - s₀| ≤ ρ := (Metric.mem_ball.1 (hball hs')).le
    have hl' : |stopLik eps (mixRatio f₀ f₁ s₀ s') g| ≤ q ^ (gapSegLen eps g).toNat :=
      abs_prod_le_pow fun j _ => abs_mixRatio_le_of_near hS hs₀ hs2 _
    have hll := abs_prod_mixRatio_sub_le hS hs₀ hρ0.le hs1 hs2 (gapSegLen eps g).toNat g
    exact out_lip_pt (l := stopLik eps (mixRatio f₀ f₁ s₀ s) g)
      (l' := stopLik eps (mixRatio f₀ f₁ s₀ s') g) hψ hη hκ hq1 hqe hηθ hK₀ hCpos
      (hCnear s hs) (hCnear s' hs') (hL s (hball hs) s' (hball hs')) (abs_nonneg (s - s'))
      hg.le _ hl' hll
  -- integrability at the base point
  have hF₀ : ∀ g, F s₀ g = testFn ψ (Y g) := fun g => by
    show stopLik eps (mixRatio f₀ f₁ s₀ s₀) g * testFn ψ (stopSum eps g / C₀) =
      testFn ψ (stopSum eps g / C₀)
    rw [stopLik_mixRatio_base, one_mul]
  have hkey0 : ∀ᵐ g ∂P, |testFn ψ (Y g)| ≤
      M * (4 / κ * Real.exp (κ / 4) / η * (1 + Real.exp (θY * Y g))) := by
    filter_upwards [hSpos] with g hg
    have hY0 : 0 ≤ Y g := div_nonneg hg.le hCpos.le
    have h1 := lip_key_bound hκ le_rfl (Real.one_le_exp (by positivity)) hη hηθ hY0 0
    simp only [Nat.cast_zero, zero_add, pow_zero, one_mul, mul_zero, Real.exp_zero] at h1
    calc |testFn ψ (Y g)| ≤ M * Real.exp (η * Y g) * Y g := hψ.abs_testFn_le hη.le hY0
      _ = M * (Y g * Real.exp (η * Y g)) := by ring
      _ ≤ M * (Y g * Real.exp (2 * η * Y g)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
            (Real.exp_le_exp.2 (by nlinarith)) hY0) hM
      _ ≤ _ := by gcongr
  have hΦm : Measurable fun g => testFn ψ (Y g) :=
    hψ.measurable_testFn.comp ((measurable_stopSum eps).div_const _)
  have hFint : Integrable (F s₀) P := by
    have e : F s₀ = fun g => testFn ψ (Y g) := funext hF₀
    rw [e]
    exact (((integrable_const (1 : ℝ)).add hY).const_mul _ |>.const_mul M).mono'
      hΦm.aestronglyMeasurable (by
        filter_upwards [hkey0] with g hg
        rw [Real.norm_eq_abs]
        simpa [mul_assoc] using hg)
  -- the derivative of the integrand
  set F' : (ℕ → ℝ) → ℝ := fun g =>
    lDer eps (mixScore f₀ f₁ s₀) g * testFn ψ (Y g) +
      ψ (Y g) * ((0 * C₀ - stopSum eps g * C') / C₀ ^ 2) with hF'
  have hF'm : Measurable F' :=
    ((measurable_lDer eps (hS.measurable_score s₀)).mul hΦm).add
      ((hψ.1.comp ((measurable_stopSum eps).div_const _)).mul
        (((measurable_stopSum eps).mul_const C').const_sub _ |>.div_const _))
  have hdiff : ∀ᵐ g ∂P, HasDerivAt (fun s => F s g) (F' g) s₀ := by
    filter_upwards [ae_hasDerivAt_testFn_output hψ hac hCpos hSpos] with g hg
    have hdiv : HasDerivAt (fun s => stopSum eps g / Cf s)
        ((0 * Cf s₀ - stopSum eps g * C') / Cf s₀ ^ 2) s₀ :=
      (hasDerivAt_const s₀ (stopSum eps g)).fun_div hCd hCpos.ne'
    have hcomp := hg.comp s₀ hdiv
    have hprod := (hasDerivAt_prod_mixRatio (f₀ := f₀) (f₁ := f₁) s₀
      (gapSegLen eps g).toNat g).mul hcomp
    have e1 : ∏ j ∈ Finset.range (gapSegLen eps g).toNat, mixRatio f₀ f₁ s₀ s₀ (g j) = 1 :=
      stopLik_mixRatio_base eps s₀ g
    rw [e1, one_mul] at hprod
    exact hprod
  have hderiv := hasDerivAt_integral_of_dominated_loc_of_lip (μ := P) (F := F) (F' := F')
    (x₀ := s₀) (bound := bnd) (Metric.ball_mem_nhds s₀ hδ0)
    (Eventually.of_forall fun s => ((measurable_stopLik eps (hS.measurable_ratio s₀ s)).mul
      (hψ.measurable_testFn.comp ((measurable_stopSum eps).div_const _))).aestronglyMeasurable)
    hFint hF'm.aestronglyMeasurable
    (by
      filter_upwards [hlip] with g hg
      exact LipschitzOnWith.of_dist_le_mul fun s hs s' hs' => by
        rw [Real.dist_eq, Real.dist_eq, Real.coe_nnabs, abs_of_nonneg (hbnd0 g)]
        exact hg s hs s' hs')
    hbnd_int hdiff
  -- the two parts of the derivative
  have hkap : ∫ g, ψ (Y g) * ((0 * C₀ - stopSum eps g * C') / C₀ ^ 2) ∂P =
      -(outKappa eps νb ψ * (C' / C₀)) := by
    have e : ∀ g, ψ (Y g) * ((0 * C₀ - stopSum eps g * C') / C₀ ^ 2) =
        -(C' / C₀) * (Y g * ψ (Y g)) := fun g => by
      simp only [hYdef]; field_simp; ring
    simp_rw [e]
    rw [integral_const_mul, outKappa]
    have hmap : ∫ y, y * ψ y ∂(lawPhi eps νb : Measure ℝ) = ∫ g, Y g * ψ (Y g) ∂P := by
      change ∫ y, y * ψ y ∂((iidLaw νb).map fun g => stopSum eps g / lawC eps νb) = _
      exact integral_map ((measurable_stopSum eps).div_const _).aemeasurable
        (measurable_id.mul hψ.1).aestronglyMeasurable
    rw [hmap]; ring
  have hkapint : Integrable (fun g => ψ (Y g) * ((0 * C₀ - stopSum eps g * C') / C₀ ^ 2)) P := by
    have e : (fun g => ψ (Y g) * ((0 * C₀ - stopSum eps g * C') / C₀ ^ 2)) =
        fun g => -(C' / C₀) * (Y g * ψ (Y g)) := funext fun g => by
      simp only [hYdef]; field_simp; ring
    rw [e]
    refine Integrable.const_mul ?_ _
    refine (((integrable_const (1 : ℝ)).add hY).const_mul
        (M * (1 / η * (4 / κ * Real.exp (κ / 4))))).mono'
      ((measurable_id.mul hψ.1).comp ((measurable_stopSum eps).div_const _)).aestronglyMeasurable
      ?_
    filter_upwards [hSpos] with g hg
    have hY0 : 0 ≤ Y g := div_nonneg hg.le hCpos.le
    have h1 := lip_key_bound hκ le_rfl (Real.one_le_exp (by positivity)) hη hηθ hY0 0
    simp only [Nat.cast_zero, zero_add, pow_zero, one_mul, mul_zero, Real.exp_zero] at h1
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hY0]
    calc Y g * |ψ (Y g)| ≤ Y g * (M * Real.exp (η * Y g)) :=
          mul_le_mul_of_nonneg_left (hψ.2 _ hY0) hY0
      _ ≤ M * (Y g * Real.exp (2 * η * Y g)) := by
          rw [mul_left_comm]
          gcongr
          nlinarith
      _ ≤ M * (4 / κ * Real.exp (κ / 4) / η * (1 + Real.exp (θY * Y g))) := by gcongr
      _ = _ := by simp only [Pi.add_apply]; ring
  have hdirint : Integrable (fun g => lDer eps (mixScore f₀ f₁ s₀) g * testFn ψ (Y g)) P := by
    have := hderiv.1.sub hkapint
    refine this.congr (Eventually.of_forall fun g => ?_)
    simp only [hF', Pi.sub_apply]; ring
  -- the direct term as an insertion kernel
  have hTΦ : Integrable (fun g => ((gapSegLen eps g).toNat : ℝ) * |testFn ψ (Y g)|) P := by
    refine (((hexp.add hY).const_mul (4 / κ * Real.exp (κ / 4) / η)).const_mul M).mono'
      ((measurable_from_top.comp (measurable_gapSegLen_toNat eps)).mul
        hΦm.abs).aestronglyMeasurable ?_
    filter_upwards [hSpos] with g hg
    have hY0 : 0 ≤ Y g := div_nonneg hg.le hCpos.le
    have h1 := lip_key_bound hκ le_rfl (Real.one_le_exp (by positivity)) hη hηθ hY0
      (gapSegLen eps g).toNat
    rw [one_pow, mul_one] at h1
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have hT0 : (0 : ℝ) ≤ (gapSegLen eps g).toNat := Nat.cast_nonneg _
    calc ((gapSegLen eps g).toNat : ℝ) * |testFn ψ (Y g)|
        ≤ ((gapSegLen eps g).toNat + 1 : ℝ) * (M * (Y g * Real.exp (2 * η * Y g))) := by
          refine mul_le_mul (by linarith) ?_ (abs_nonneg _) (by linarith)
          calc |testFn ψ (Y g)| ≤ M * Real.exp (η * Y g) * Y g := hψ.abs_testFn_le hη.le hY0
            _ = M * (Y g * Real.exp (η * Y g)) := by ring
            _ ≤ M * (Y g * Real.exp (2 * η * Y g)) :=
                mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
                  (Real.exp_le_exp.2 (by nlinarith)) hY0) hM
      _ = M * (((gapSegLen eps g).toNat + 1 : ℝ) * (Y g * Real.exp (2 * η * Y g))) := by ring
      _ ≤ M * (4 / κ * Real.exp (κ / 4) / η * (Real.exp (κ * (gapSegLen eps g).toNat) +
            Real.exp (θY * Y g))) := by gcongr
  obtain ⟨hI₀, hI₁, hdir⟩ := integral_lDer_mul_eq hS hs₀ hfin₀ hΦm hTΦ
  -- assemble
  have hloc : ∀ s ∈ Icc (0 : ℝ) 1, outFn eps (mixPM ν₀ ν₁ s) ψ = ∫ g, F s g ∂P := fun s hs =>
    outFn_mix_eq hS hs₀ hs (hfin s hs) hfin₀ hψ
  have hfinal : ∫ g, F' g ∂P = ∫ x, outJ eps νb ψ x ∂(ν₁ : Measure ℝ) -
      ∫ x, outJ eps νb ψ x ∂(ν₀ : Measure ℝ) := by
    rw [hF', integral_add hdirint hkapint, hkap]
    change (∫ g, lDer eps (mixScore f₀ f₁ s₀) g *
      testFn ψ (stopSum eps g / lawC eps νb) ∂P) + _ = _
    rw [hdir]
    have hsplit : ∀ {μ : Measure ℝ}, Integrable (outIns eps νb ψ) μ →
        Integrable (lawJC eps νb) μ →
        ∫ x, outJ eps νb ψ x ∂μ = ∫ x, outIns eps νb ψ x ∂μ -
          outKappa eps νb ψ * ((∫ x, lawJC eps νb x ∂μ) / C₀) := by
      intro μ h1 h2
      rw [show (fun x => outJ eps νb ψ x) = fun x => outIns eps νb ψ x -
          outKappa eps νb ψ * (lawJC eps νb x / C₀) from rfl,
        integral_sub h1 ((h2.div_const C₀).const_mul _), integral_const_mul, integral_div]
    rw [hsplit hI₁ hJ₁, hsplit hI₀ hJ₀, hC']
    change _ = (∫ x, insKernel eps νb (fun g => testFn ψ (stopSum eps g / lawC eps νb)) x
        ∂(ν₁ : Measure ℝ) - _) - (∫ x, insKernel eps νb
        (fun g => testFn ψ (stopSum eps g / lawC eps νb)) x ∂(ν₀ : Measure ℝ) - _)
    ring
  rw [← hfinal]
  refine hderiv.2.congr_of_eventuallyEq ?_
  filter_upwards [Icc_mem_nhds hs₀.1 hs₀.2] with s hs using hloc s hs

end

end PGM
