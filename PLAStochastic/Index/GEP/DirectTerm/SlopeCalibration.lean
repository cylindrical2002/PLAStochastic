import PLAStochastic.Index.GEP.DirectTerm.CoarseBound
import PLAStochastic.Index.Endpoint.NextLayerMoments

/-!
# WP4 leaf `DirectTerm`, part 3: calibration of the slope

`direct-endpoint-response.md` (DT) §3 (6).  If the insertion kernel `I_F` is within
`E₀ e^{α' y}` of an affine function `a' + b' y` (`ν`-a.e.), the slope `b'` is fixed by one
calibration direction.  We use the unbounded direction `b(y) = y - 1`, for which
`∫ b dν = 0` and `∫ y b(y) dν = v(ν) ≥ v₋` (`RegLaw.abs_slope_le`), so no truncation is needed.

* **Insertion identity** (`integral_insKernel_mul`, PD (33)): for a weight `b`,
  `∫ I_Φ b dν = E[∑_i 1_{i<T} Φ b(g_i)]`, by single-gap insertion (`integral_update`) and
  Fubini; on `{T < ∞}` the right side is `Φ ∑_{i<T} b(g_i)` (`tsum_indicator_mul_eq`).
  For `b(y) = y - 1` this is `E[F(S_T)(S_T - T)]`.
* **Wald** (`integral_sq_stopSum_sub_le`): `E(S_T - T)² ≤ v(ν) C_ε` (`stoppedSumE_sq_integral_le`).
* **Output moment** (`integral_sq_test_le`): `E F(S_T)² ≤ E e^{θK S_T/C} ≤ CK` when
  `|F y| ≤ e^{κ y}` and `2κC ≤ θK`.
* Cauchy–Schwarz then gives `|∫ I_F (y-1) dν| ≤ √(CK · v₊ · C) ≤ K ε`, and
  `|b'| ≤ K₅ (ε + E₀)` (`calib_bound`).  The integrability of every term comes from the coarse
  bound of `PLAStochastic/Index/GEP/DirectTerm/CoarseBound.lean` (`kernel_coarse`).
-/

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal NNReal

variable {D θ vlo vhi : ℝ}

/-! ## The coarse facts in one package -/

/-- **Kernel facts** from the coarse bound: measurability, the pointwise bound, and the summable
majorant of the insertion series. -/
theorem kernel_coarse (hD : 0 < D) (hθ : 0 < θ) (hvlo : 0 < vlo) (hv : vlo ≤ vhi) :
    ∃ κ₁ K₁ e₁ : ℝ, 0 < κ₁ ∧ 0 ≤ K₁ ∧ 1 ≤ e₁ ∧ ∀ eps, e₁ ≤ eps → ∀ ν : ProbabilityMeasure ℝ,
      RegLaw D θ vlo vhi ν → ∀ κ : ℝ, 0 ≤ κ → κ * eps ^ 2 ≤ κ₁ → ∀ F : ℝ → ℝ, Measurable F →
      (∀ y, 0 ≤ y → |F y| ≤ Real.exp (κ * y)) →
        Measurable (insKernel eps ν (fun g => F (stopSum eps g))) ∧
        (∀ x, 0 ≤ x → |insKernel eps ν (fun g => F (stopSum eps g)) x| ≤
          K₁ * eps ^ 4 * Real.exp (κ * x)) ∧
        (∀ x, 0 ≤ x → ∑' i : ℕ, ∫⁻ g, ‖{g : ℕ → ℝ | (i : ℕ∞) < gapSegLen eps g}.indicator
          (fun g => F (stopSum eps (Function.update g i x))) g‖ₑ ∂(iidLaw ν) ≤
            ENNReal.ofReal (K₁ * eps ^ 4 * Real.exp (κ * x))) := by
  obtain ⟨κ₁, K₁, e₁, hκ₁, hK₁, he₁, hco⟩ := coarse_bound hD hθ hvlo hv
  refine ⟨κ₁, K₁, e₁, hκ₁, hK₁, he₁, fun eps heps ν hν κ hκ0 hκ F hF hFb => ?_⟩
  have heps0 : 0 ≤ eps := by linarith
  have hb : ∀ x : ℝ, 0 ≤ x → _ := fun x hx => insKernel_bound hν hFb hx
    (by positivity) (hco eps heps ν hν κ hκ0 hκ x)
  exact ⟨measurable_insKernel eps ν (hF.comp (measurable_stopSum eps)),
    fun x hx => (hb x hx).2, fun x hx => (hb x hx).1⟩

/-! ## The insertion identity against a weight -/

theorem measurable_lintegral_update (ν : ProbabilityMeasure ℝ) (i : ℕ) {G : (ℕ → ℝ) → ℝ≥0∞}
    (hG : Measurable G) : Measurable fun y => ∫⁻ g, G (Function.update g i y) ∂(iidLaw ν) :=
  (hG.comp (measurable_update_pair i)).lintegral_prod_right'

/-- **Insertion identity** (PD (33); DT §3): `∫ I_Φ b dν = E[∑_i 1_{i<T} Φ b(g_i)]`. -/
theorem integral_insKernel_mul {ν : ProbabilityMeasure ℝ} (eps : ℝ) {Φ : (ℕ → ℝ) → ℝ}
    (hΦ : Measurable Φ) {b : ℝ → ℝ} (hb : Measurable b)
    (hsum : ∑' i : ℕ, ∫⁻ y, (∫⁻ g, ‖({g : ℕ → ℝ | (i : ℕ∞) < gapSegLen eps g}.indicator Φ)
      (Function.update g i y)‖ₑ ∂(iidLaw ν)) * ‖b y‖ₑ ∂(ν : Measure ℝ) ≠ ⊤) :
    ∫ y, insKernel eps ν Φ y * b y ∂(ν : Measure ℝ) =
      ∫ g, ∑' i : ℕ, ({g : ℕ → ℝ | (i : ℕ∞) < gapSegLen eps g}.indicator Φ) g * b (g i)
        ∂(iidLaw ν) := by
  set P := iidLaw ν with hP
  set G : ℕ → (ℕ → ℝ) → ℝ := fun i => {g : ℕ → ℝ | (i : ℕ∞) < gapSegLen eps g}.indicator Φ
    with hG
  have hGm : ∀ i, Measurable (G i) := fun i => hΦ.indicator (measurableSet_lt_gapSegLen eps i)
  set K : ℕ → ℝ → ℝ := fun i y => ∫ g, G i (Function.update g i y) ∂P with hK
  have hKm : ∀ i, Measurable (K i) := fun i => measurable_integral_update ν i (hGm i)
  set H : ℕ → (ℕ → ℝ) → ℝ := fun i g => G i g * b (g i) with hH
  have hHm : ∀ i, Measurable (H i) := fun i => (hGm i).mul (hb.comp (measurable_pi_apply i))
  have hKb : ∀ i, ∫⁻ y, ‖K i y * b y‖ₑ ∂(ν : Measure ℝ) ≤
      ∫⁻ y, (∫⁻ g, ‖G i (Function.update g i y)‖ₑ ∂P) * ‖b y‖ₑ ∂(ν : Measure ℝ) := by
    intro i
    refine lintegral_mono fun y => ?_
    rw [enorm_mul]
    gcongr
    exact enorm_integral_le_lintegral_enorm _
  have hHe : ∀ i, ∫⁻ g, ‖H i g‖ₑ ∂P =
      ∫⁻ y, (∫⁻ g, ‖G i (Function.update g i y)‖ₑ ∂P) * ‖b y‖ₑ ∂(ν : Measure ℝ) := by
    intro i
    rw [lintegral_update ν i (hHm i).enorm]
    refine lintegral_congr fun y => ?_
    rw [← lintegral_mul_const' _ _ enorm_ne_top]
    refine lintegral_congr fun g => ?_
    simp only [hH, Function.update_self, enorm_mul]
  have hsumH : ∑' i, ∫⁻ g, ‖H i g‖ₑ ∂P ≠ ⊤ := by
    simp_rw [hHe]
    exact hsum
  have hsumK : ∑' i, ∫⁻ y, ‖K i y * b y‖ₑ ∂(ν : Measure ℝ) ≠ ⊤ :=
    ne_top_of_le_ne_top hsum (ENNReal.tsum_le_tsum hKb)
  have hHint : ∀ i, Integrable (H i) P := fun i => ⟨(hHm i).aestronglyMeasurable, by
    rw [hasFiniteIntegral_iff_enorm]
    exact (ne_top_of_le_ne_top hsumH (ENNReal.le_tsum i)).lt_top⟩
  have hterm : ∀ i, ∫ y, K i y * b y ∂(ν : Measure ℝ) = ∫ g, H i g ∂P := by
    intro i
    rw [integral_update ν i (hHm i) (hHint i)]
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    simp only [hH, hK, Function.update_self]
    rw [integral_mul_const]
  calc ∫ y, insKernel eps ν Φ y * b y ∂(ν : Measure ℝ)
      = ∫ y, ∑' i, K i y * b y ∂(ν : Measure ℝ) := by
        refine integral_congr_ae (Eventually.of_forall fun y => ?_)
        simp only
        rw [insKernel_eq_tsum_update, tsum_mul_right]
    _ = ∑' i, ∫ y, K i y * b y ∂(ν : Measure ℝ) :=
        integral_tsum (fun i => ((hKm i).mul hb).aestronglyMeasurable) hsumK
    _ = ∑' i, ∫ g, H i g ∂P := tsum_congr hterm
    _ = ∫ g, ∑' i, H i g ∂P :=
        (integral_tsum (fun i => (hHm i).aestronglyMeasurable) hsumH).symm

/-- On `{T = n}`, `∑_i 1_{i<T} Φ b(g_i) = Φ ∑_{i<n} b(g_i)`. -/
theorem tsum_indicator_mul_eq {eps : ℝ} {g : ℕ → ℝ} {n : ℕ} (hn : gapSegLen eps g = n)
    (Φ : (ℕ → ℝ) → ℝ) (b : ℝ → ℝ) :
    ∑' i : ℕ, ({g : ℕ → ℝ | (i : ℕ∞) < gapSegLen eps g}.indicator Φ) g * b (g i) =
      Φ g * ∑ i ∈ Finset.range n, b (g i) := by
  have e : ∀ i : ℕ, ({g : ℕ → ℝ | (i : ℕ∞) < gapSegLen eps g}.indicator Φ) g * b (g i) =
      (Φ g * b (g i)) * {g : ℕ → ℝ | (i : ℕ∞) < gapSegLen eps g}.indicator (fun _ => (1 : ℝ)) g := by
    intro i
    by_cases hi : g ∈ {g : ℕ → ℝ | (i : ℕ∞) < gapSegLen eps g}
    · rw [indicator_of_mem hi, indicator_of_mem hi, mul_one]
    · rw [indicator_of_notMem hi, indicator_of_notMem hi, mul_zero, zero_mul]
  simp_rw [e]
  rw [tsum_mul_indicator_lt hn, Finset.mul_sum]

/-! ## Wald and the output moment -/

/-- **Wald**: `E(S_T - T)² ≤ v(ν) C_ε`. -/
theorem integral_sq_stopSum_sub_le {ν : ProbabilityMeasure ℝ} (hν : RegLaw D θ vlo vhi ν)
    (hθ : 0 < θ) (hvlo : 0 < vlo) {eps : ℝ} (heps : epsZero (regB vhi) (regBeta D θ vlo) ≤ eps) :
    Integrable (fun g => (stopSum eps g - ((gapSegLen eps g).toNat : ℝ)) ^ 2) (iidLaw ν) ∧
      ∫ g, (stopSum eps g - ((gapSegLen eps g).toNat : ℝ)) ^ 2 ∂(iidLaw ν) ≤
        lawVar ν * lawC eps ν := by
  have hm := hν.momClass hθ hvlo
  obtain ⟨-, -, -, -, hfin, hT1, -⟩ := momClass_setup (regV_pos hvlo) heps hm
  have hv0 : 0 < lawVar ν := hvlo.trans_le hν.var_ge
  have hX : GapLaw (iidLaw ν) gapCoord 1 (Real.sqrt (lawVar ν))
      (∫ x, |x - 1| ^ 3 ∂(ν : Measure ℝ)) :=
    gapLaw_iidLaw hm.memLp3 hm.mean one_pos (Real.sq_sqrt hv0.le).symm (Real.sqrt_pos.2 hv0)
      le_rfl
  have hY2 : ∀ t, MemLp (centred gapCoord 1 t) 2 (iidLaw ν) :=
    fun t => (hX.memLp_centred t).mono_exponent (by norm_num)
  have hσ : ∀ t, ∫ g, centred gapCoord 1 t g ^ 2 ∂(iidLaw ν) ≤ lawVar ν := fun t => by
    rw [hX.integral_centred_sq, Real.sq_sqrt hv0.le]
  obtain ⟨hI, hle⟩ := stoppedSumE_sq_integral_le hX.indepIncrements (T := gapSegLen eps)
    (fun t => gapSegLen_lt_measurable (X := gapCoord) (fun t => measurable_pi_apply t) eps t)
    hY2 hX.integral_centred hσ hfin hT1
  have e : ∀ g : ℕ → ℝ, stoppedSumE (centred gapCoord 1) (gapSegLen eps) g =
      stopSum eps g - ((gapSegLen eps g).toNat : ℝ) := by
    intro g
    simp only [stoppedSumE, partialSum, centred, gapCoord, Finset.sum_sub_distrib,
      Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one, stopSum, gapKeys]
  simp_rw [e] at hI hle
  exact ⟨hI, hle⟩

/-- **The output moment of a test**: `E F(S_T)² ≤ CK` when `|F y| ≤ e^{κy}`, `2κC ≤ θK`. -/
theorem integral_sq_test_le {ν : ProbabilityMeasure ℝ} {eps κ : ℝ}
    (hE : ExpMom θK CK (lawPhi eps ν)) (hpos : ∀ᵐ g ∂(iidLaw ν), 0 < stopSum eps g)
    (hC : 0 < lawC eps ν) (hκC : 2 * κ * lawC eps ν ≤ θK) {F : ℝ → ℝ}
    (hF : Measurable F) (hFb : ∀ y, 0 ≤ y → |F y| ≤ Real.exp (κ * y)) :
    MemLp (fun g => F (stopSum eps g)) 2 (iidLaw ν) ∧
      ∫ g, F (stopSum eps g) ^ 2 ∂(iidLaw ν) ≤ CK := by
  obtain ⟨hint, hle⟩ := integrable_exp_output hE
  have hFm : Measurable fun g => F (stopSum eps g) := hF.comp (measurable_stopSum eps)
  have hdom : ∀ᵐ g ∂(iidLaw ν), ‖F (stopSum eps g) ^ 2‖ ≤
      Real.exp (θK * (stopSum eps g / lawC eps ν)) := by
    filter_upwards [hpos] with g hg
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have h1 := hFb _ hg.le
    have h2 : F (stopSum eps g) ^ 2 ≤ Real.exp (κ * stopSum eps g) ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) h1 2
    refine h2.trans ?_
    rw [← Real.exp_nat_mul]
    apply Real.exp_le_exp.2
    have hY : 0 ≤ stopSum eps g / lawC eps ν := by positivity
    have : (2 : ℕ) * (κ * stopSum eps g) = (2 * κ * lawC eps ν) * (stopSum eps g / lawC eps ν) := by
      field_simp
      push_cast
      ring
    rw [this]
    exact mul_le_mul_of_nonneg_right hκC hY
  have hsq : Integrable (fun g => F (stopSum eps g) ^ 2) (iidLaw ν) :=
    hint.mono' (hFm.pow_const 2).aestronglyMeasurable hdom
  refine ⟨(memLp_two_iff_integrable_sq hFm.aestronglyMeasurable).2 hsq, ?_⟩
  refine le_trans (integral_mono_ae hsq hint ?_) hle
  filter_upwards [hdom] with g hg
  exact (le_abs_self _).trans (by rwa [Real.norm_eq_abs] at hg)

/-! ## The slope from one calibration direction -/

/-- `∫ e^{α'y} |y - 1| dν ≤ (1 + 4/θ) (2D/θ)` for `α' ≤ θ/4`. -/
theorem RegLaw.integral_exp_abs_sub_one_le {ν : ProbabilityMeasure ℝ} (hν : RegLaw D θ vlo vhi ν)
    (hθ : 0 < θ) {α' : ℝ} (hα' : α' ≤ θ / 4) :
    Integrable (fun y => Real.exp (α' * y) * |y - 1|) (ν : Measure ℝ) ∧
      ∫ y, Real.exp (α' * y) * |y - 1| ∂(ν : Measure ℝ) ≤ (1 + 4 / θ) * (2 * D / θ) := by
  have hE := hν.expMom hθ
  have hdom : ∀ᵐ y ∂(ν : Measure ℝ), ‖Real.exp (α' * y) * |y - 1|‖ ≤
      (1 + 4 / θ) * Real.exp (θ / 2 * y) := by
    filter_upwards [hν.ae_pos] with y hy
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have h1 : Real.exp (α' * y) ≤ Real.exp (θ / 4 * y) :=
      Real.exp_le_exp.2 (mul_le_mul_of_nonneg_right hα' hy.le)
    have h2 : Real.exp (θ / 4 * y) ≤ Real.exp (θ / 2 * y) :=
      Real.exp_le_exp.2 (mul_le_mul_of_nonneg_right (by linarith) hy.le)
    have h3 : y * Real.exp (θ / 4 * y) ≤ Real.exp (θ / 2 * y) / (θ / 2 - θ / 4) :=
      mul_exp_le_exp_div (by linarith)
    have h4 : Real.exp (θ / 2 * y) / (θ / 2 - θ / 4) = 4 / θ * Real.exp (θ / 2 * y) := by
      field_simp; ring
    have h5 : |y - 1| ≤ y + 1 := by rw [abs_le]; constructor <;> linarith
    calc Real.exp (α' * y) * |y - 1| ≤ Real.exp (θ / 4 * y) * (y + 1) :=
          mul_le_mul h1 h5 (abs_nonneg _) (Real.exp_pos _).le
      _ = y * Real.exp (θ / 4 * y) + Real.exp (θ / 4 * y) := by ring
      _ ≤ 4 / θ * Real.exp (θ / 2 * y) + Real.exp (θ / 2 * y) := by linarith
      _ = (1 + 4 / θ) * Real.exp (θ / 2 * y) := by ring
  have hint : Integrable (fun y => Real.exp (α' * y) * |y - 1|) (ν : Measure ℝ) :=
    (hE.integrable.const_mul _).mono' (by fun_prop) hdom
  refine ⟨hint, ?_⟩
  calc ∫ y, Real.exp (α' * y) * |y - 1| ∂(ν : Measure ℝ)
      ≤ ∫ y, (1 + 4 / θ) * Real.exp (θ / 2 * y) ∂(ν : Measure ℝ) :=
        integral_mono_ae hint (hE.integrable.const_mul _) (by
          filter_upwards [hdom] with y hy
          exact (le_abs_self _).trans (by rwa [Real.norm_eq_abs] at hy))
    _ = (1 + 4 / θ) * ∫ y, Real.exp (θ / 2 * y) ∂(ν : Measure ℝ) := integral_const_mul _ _
    _ ≤ (1 + 4 / θ) * (2 * D / θ) := by
        gcongr
        exact hE.le

/-- **The slope** (DT (6)): if `|I - (a' + b' y)| ≤ E₀ e^{α' y}` `ν`-a.e., then
`|b'| v₋ ≤ |∫ I(y)(y-1) dν| + E₀ (1 + 4/θ)(2D/θ)`. -/
theorem RegLaw.abs_slope_le {ν : ProbabilityMeasure ℝ} (hν : RegLaw D θ vlo vhi ν) (hθ : 0 < θ)
    {I : ℝ → ℝ} (hI : Integrable (fun y => I y * (y - 1)) (ν : Measure ℝ)) {a' b' E₀ α' : ℝ}
    (hα' : α' ≤ θ / 4) (hE₀ : 0 ≤ E₀)
    (hae : ∀ᵐ y ∂(ν : Measure ℝ), |I y - (a' + b' * y)| ≤ E₀ * Real.exp (α' * y)) :
    |b'| * vlo ≤ |∫ y, I y * (y - 1) ∂(ν : Measure ℝ)| + E₀ * ((1 + 4 / θ) * (2 * D / θ)) := by
  obtain ⟨hx2, -⟩ := hν.tail_sq hθ
  obtain ⟨hx1, -⟩ := hν.tail_mean hθ
  have hmean := hν.mean
  rw [lawMean] at hmean
  have hy1 : Integrable (fun y : ℝ => y - 1) (ν : Measure ℝ) := hx1.sub (integrable_const 1)
  have hyy : Integrable (fun y : ℝ => y * (y - 1)) (ν : Measure ℝ) := by
    have : (fun y : ℝ => y * (y - 1)) = fun y => y ^ 2 - y := by funext y; ring
    rw [this]; exact hx2.sub hx1
  have h0 : ∫ y, (y - 1) ∂(ν : Measure ℝ) = 0 := by
    rw [integral_sub hx1 (integrable_const 1), hmean]; simp
  have hvar : ∫ y, y * (y - 1) ∂(ν : Measure ℝ) = lawVar ν := by
    rw [lawVar, hν.mean]
    have : (fun y : ℝ => y * (y - 1)) = fun y => (y - 1) ^ 2 + (y - 1) := by funext y; ring
    have hsq1 : Integrable (fun y : ℝ => (y - 1) ^ 2) (ν : Measure ℝ) := by
      have e2 : (fun y : ℝ => (y - 1) ^ 2) = fun y => y ^ 2 - 2 * y + 1 := by funext y; ring
      rw [e2]; exact (hx2.sub (hx1.const_mul 2)).add (integrable_const 1)
    rw [this, integral_add hsq1 hy1, h0, add_zero]
  set R : ℝ → ℝ := fun y => (I y - (a' + b' * y)) * (y - 1) with hR
  have hRe : R = fun y => I y * (y - 1) - (a' * (y - 1) + b' * (y * (y - 1))) := by
    funext y; rw [hR]; ring
  have hRi : Integrable R (ν : Measure ℝ) := by
    rw [hRe]; exact hI.sub ((hy1.const_mul a').add (hyy.const_mul b'))
  have hsplit : ∫ y, I y * (y - 1) ∂(ν : Measure ℝ) = ∫ y, R y ∂(ν : Measure ℝ) + b' * lawVar ν := by
    have : (fun y => I y * (y - 1)) = fun y => R y + (a' * (y - 1) + b' * (y * (y - 1))) := by
      funext y; rw [hR]; ring
    rw [this, integral_add (f := R) (g := fun y => a' * (y - 1) + b' * (y * (y - 1))) hRi
        ((hy1.const_mul a').add (hyy.const_mul b')),
      integral_add (f := fun y => a' * (y - 1)) (g := fun y => b' * (y * (y - 1)))
        (hy1.const_mul a') (hyy.const_mul b'), integral_const_mul, integral_const_mul,
      h0, hvar]
    ring
  obtain ⟨hEi, hEle⟩ := hν.integral_exp_abs_sub_one_le hθ hα'
  have hRle : |∫ y, R y ∂(ν : Measure ℝ)| ≤ E₀ * ((1 + 4 / θ) * (2 * D / θ)) := by
    calc |∫ y, R y ∂(ν : Measure ℝ)| ≤ ∫ y, ‖R y‖ ∂(ν : Measure ℝ) := by
          rw [← Real.norm_eq_abs]; exact norm_integral_le_integral_norm _
      _ ≤ ∫ y, E₀ * (Real.exp (α' * y) * |y - 1|) ∂(ν : Measure ℝ) := by
          refine integral_mono_ae hRi.norm (hEi.const_mul E₀) ?_
          filter_upwards [hae] with y hy
          rw [hR, Real.norm_eq_abs, abs_mul]
          calc |I y - (a' + b' * y)| * |y - 1| ≤ E₀ * Real.exp (α' * y) * |y - 1| :=
                mul_le_mul_of_nonneg_right hy (abs_nonneg _)
            _ = E₀ * (Real.exp (α' * y) * |y - 1|) := by ring
      _ = E₀ * ∫ y, Real.exp (α' * y) * |y - 1| ∂(ν : Measure ℝ) := integral_const_mul _ _
      _ ≤ E₀ * ((1 + 4 / θ) * (2 * D / θ)) := by gcongr
  have hb : |b'| * lawVar ν ≤ |∫ y, I y * (y - 1) ∂(ν : Measure ℝ)| +
      E₀ * ((1 + 4 / θ) * (2 * D / θ)) := by
    have hv0 : 0 ≤ lawVar ν := integral_nonneg fun _ => sq_nonneg _
    have e : b' * lawVar ν = ∫ y, I y * (y - 1) ∂(ν : Measure ℝ) - ∫ y, R y ∂(ν : Measure ℝ) := by
      rw [hsplit]; ring
    calc |b'| * lawVar ν = |b' * lawVar ν| := by rw [abs_mul, abs_of_nonneg hv0]
      _ = |∫ y, I y * (y - 1) ∂(ν : Measure ℝ) - ∫ y, R y ∂(ν : Measure ℝ)| := by rw [e]
      _ ≤ |∫ y, I y * (y - 1) ∂(ν : Measure ℝ)| + |∫ y, R y ∂(ν : Measure ℝ)| := abs_sub _ _
      _ ≤ _ := by linarith
  calc |b'| * vlo ≤ |b'| * lawVar ν := mul_le_mul_of_nonneg_left hν.var_ge (abs_nonneg _)
    _ ≤ _ := hb

/-! ## The calibration bound -/

/-- **Calibration of the slope** (DT (6)): if `I_F` is `ν`-a.e. within `E₀ e^{α' y}` of an
affine function `a' + b' y`, then `|b'| ≤ K₅ (ε + E₀)`. -/
theorem calib_bound (hD : 0 < D) (hθ : 0 < θ) (hvlo : 0 < vlo) (hv : vlo ≤ vhi) :
    ∃ κ₂ K₅ e₅ : ℝ, 0 < κ₂ ∧ 0 ≤ K₅ ∧ 1 ≤ e₅ ∧ ∀ eps, e₅ ≤ eps → ∀ ν : ProbabilityMeasure ℝ,
      RegLaw D θ vlo vhi ν → ∀ κ : ℝ, 0 ≤ κ → κ * eps ^ 2 ≤ κ₂ → ∀ F : ℝ → ℝ, Measurable F →
      (∀ y, 0 ≤ y → |F y| ≤ Real.exp (κ * y)) →
      ∀ a' b' E₀ α' : ℝ, α' ≤ θ / 4 → 0 ≤ E₀ →
        (∀ᵐ y ∂(ν : Measure ℝ), |insKernel eps ν (fun g => F (stopSum eps g)) y -
          (a' + b' * y)| ≤ E₀ * Real.exp (α' * y)) →
        |b'| ≤ K₅ * (eps + E₀) := by
  obtain ⟨κ₁, K₁, e₁, hκ₁, hK₁, he₁, hker⟩ := kernel_coarse hD hθ hvlo hv
  obtain ⟨e₀, he₀1, hfacts⟩ := regLaw_facts hD hθ hvlo hv
  have hrv := regV_pos hvlo
  have hcP := cPlus_pos
  have hθK := θK_pos
  have hCK := CK_pos
  set Kc := (1 + 4 / θ) * (2 * D / θ) with hKc
  have hKc0 : 0 ≤ Kc := by positivity
  set Ks := Real.sqrt (CK * vhi * (cPlus / regV vlo)) with hKs
  refine ⟨min (min κ₁ (θ / 8)) (θK * regV vlo / (2 * cPlus)), max Ks Kc / vlo,
    max (max e₁ e₀) (epsZero (regB vhi) (regBeta D θ vlo)),
    lt_min (lt_min hκ₁ (by positivity)) (by positivity), by positivity,
    le_trans he₁ (le_trans (le_max_left _ _) (le_max_left _ _)), ?_⟩
  intro eps heps ν hν κ hκ0 hκ F hF hFb a' b' E₀ α' hα' hE₀ hae
  have he1 : e₁ ≤ eps := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) heps
  have he0 : e₀ ≤ eps := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) heps
  have hez : epsZero (regB vhi) (regBeta D θ vlo) ≤ eps := le_trans (le_max_right _ _) heps
  have heps1 : 1 ≤ eps := he₁.trans he1
  have heps0 : 0 < eps := by linarith
  have he2 : 1 ≤ eps ^ 2 := one_le_pow₀ heps1
  have hκa : κ * eps ^ 2 ≤ κ₁ := hκ.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hκb : κ * eps ^ 2 ≤ θ / 8 := hκ.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hκc : κ * eps ^ 2 ≤ θK * regV vlo / (2 * cPlus) := hκ.trans (min_le_right _ _)
  have hκθ : κ ≤ θ / 4 := by nlinarith
  obtain ⟨hfin, hCm, -, hE, -, hpos⟩ := hfacts eps he0 ν hν
  obtain ⟨-, -, hCp⟩ := momClass_oneLayer hrv hez (hν.momClass hθ hvlo)
  have hb0 : 0 < regB vhi := hrv.trans_le (regV_le_regB hv)
  have hC0 : 0 < lawC eps ν := lt_of_lt_of_le (by positivity) hCm
  have hκC : 2 * κ * lawC eps ν ≤ θK := by
    calc 2 * κ * lawC eps ν ≤ 2 * κ * (cPlus * eps ^ 2 / regV vlo) := by gcongr
      _ = 2 * cPlus / regV vlo * (κ * eps ^ 2) := by field_simp
      _ ≤ 2 * cPlus / regV vlo * (θK * regV vlo / (2 * cPlus)) := by gcongr
      _ = θK := by field_simp
  set I := insKernel eps ν (fun g => F (stopSum eps g)) with hIdef
  obtain ⟨hIm, hIb, hIs⟩ := hker eps he1 ν hν κ hκ0 hκa F hF hFb
  -- integrability of `I(y)(y-1)`
  obtain ⟨hEi, -⟩ := hν.integral_exp_abs_sub_one_le hθ hκθ
  have hIint : Integrable (fun y => I y * (y - 1)) (ν : Measure ℝ) := by
    refine (hEi.const_mul (K₁ * eps ^ 4)).mono' (hIm.mul (measurable_id.sub_const 1)).aestronglyMeasurable ?_
    filter_upwards [hν.ae_pos] with y hy
    rw [Real.norm_eq_abs, abs_mul]
    calc |I y| * |y - 1| ≤ K₁ * eps ^ 4 * Real.exp (κ * y) * |y - 1| :=
          mul_le_mul_of_nonneg_right (hIb y hy.le) (abs_nonneg _)
      _ = K₁ * eps ^ 4 * (Real.exp (κ * y) * |y - 1|) := by ring
  -- the insertion identity
  have hΦm : Measurable fun g => F (stopSum eps g) := hF.comp (measurable_stopSum eps)
  have hsum : ∑' i : ℕ, ∫⁻ y, (∫⁻ g, ‖({g : ℕ → ℝ | (i : ℕ∞) < gapSegLen eps g}.indicator
      (fun g => F (stopSum eps g))) (Function.update g i y)‖ₑ ∂(iidLaw ν)) * ‖y - 1‖ₑ
        ∂(ν : Measure ℝ) ≠ ⊤ := by
    have hmi : ∀ i : ℕ, Measurable fun y => ∫⁻ g, ‖({g : ℕ → ℝ | (i : ℕ∞) < gapSegLen eps g}.indicator
        (fun g => F (stopSum eps g))) (Function.update g i y)‖ₑ ∂(iidLaw ν) := fun i =>
      measurable_lintegral_update ν i (hΦm.indicator (measurableSet_lt_gapSegLen eps i)).enorm
    have hmi' : ∀ i : ℕ, AEMeasurable (fun y => (∫⁻ g, ‖({g : ℕ → ℝ | (i : ℕ∞) < gapSegLen eps g}.indicator
        (fun g => F (stopSum eps g))) (Function.update g i y)‖ₑ ∂(iidLaw ν)) * ‖y - 1‖ₑ)
        (ν : Measure ℝ) := fun i =>
      ((hmi i).mul ((measurable_id.sub_const (1 : ℝ)).enorm)).aemeasurable
    rw [← lintegral_tsum hmi']
    have hbd : ∀ᵐ y ∂(ν : Measure ℝ), ∑' i : ℕ, (∫⁻ g, ‖({g : ℕ → ℝ | (i : ℕ∞) < gapSegLen eps g}.indicator
        (fun g => F (stopSum eps g))) (Function.update g i y)‖ₑ ∂(iidLaw ν)) * ‖y - 1‖ₑ ≤
        ENNReal.ofReal (K₁ * eps ^ 4 * (Real.exp (κ * y) * |y - 1|)) := by
      filter_upwards [hν.ae_pos] with y hy
      rw [ENNReal.tsum_mul_right]
      have e : ∀ i : ℕ, ∫⁻ g, ‖({g : ℕ → ℝ | (i : ℕ∞) < gapSegLen eps g}.indicator
          (fun g => F (stopSum eps g))) (Function.update g i y)‖ₑ ∂(iidLaw ν) =
          ∫⁻ g, ‖{g : ℕ → ℝ | (i : ℕ∞) < gapSegLen eps g}.indicator
            (fun g => F (stopSum eps (Function.update g i y))) g‖ₑ ∂(iidLaw ν) := fun i =>
        lintegral_congr fun g => by
          rw [← indicator_update_eq eps (fun g => F (stopSum eps g)) i y g]
      simp_rw [e]
      calc (∑' i : ℕ, ∫⁻ g, ‖{g : ℕ → ℝ | (i : ℕ∞) < gapSegLen eps g}.indicator
            (fun g => F (stopSum eps (Function.update g i y))) g‖ₑ ∂(iidLaw ν)) * ‖y - 1‖ₑ
          ≤ ENNReal.ofReal (K₁ * eps ^ 4 * Real.exp (κ * y)) * ENNReal.ofReal |y - 1| := by
            rw [Real.enorm_eq_ofReal_abs]
            gcongr
            exact hIs y hy.le
        _ = ENNReal.ofReal (K₁ * eps ^ 4 * (Real.exp (κ * y) * |y - 1|)) := by
            rw [← ENNReal.ofReal_mul (by positivity)]; ring_nf
    refine ne_top_of_le_ne_top ?_ (lintegral_mono_ae hbd)
    rw [← ofReal_integral_eq_lintegral_ofReal (hEi.const_mul _)
      (Eventually.of_forall fun y => by positivity)]
    exact ENNReal.ofReal_ne_top
  have hid := integral_insKernel_mul (b := fun y : ℝ => y - 1) eps hΦm
    (measurable_id.sub_const 1) hsum
  have hrhs : ∫ g, ∑' i : ℕ, ({g : ℕ → ℝ | (i : ℕ∞) < gapSegLen eps g}.indicator
      (fun g => F (stopSum eps g))) g * (g i - 1) ∂(iidLaw ν) =
      ∫ g, F (stopSum eps g) * (stopSum eps g - ((gapSegLen eps g).toNat : ℝ)) ∂(iidLaw ν) := by
    refine integral_congr_ae ?_
    filter_upwards [hfin] with g hg
    obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.1 hg
    rw [tsum_indicator_mul_eq hn.symm (fun g => F (stopSum eps g)) (fun y => y - 1)]
    congr 1
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one,
      stopSum, ← hn, ENat.toNat_natCast]
    rfl
  -- Cauchy–Schwarz
  obtain ⟨hW2i, hW2⟩ := integral_sq_stopSum_sub_le hν hθ hvlo hez
  obtain ⟨hF2, hF2le⟩ := integral_sq_test_le hE hpos hC0 hκC hF hFb
  have hWm : Measurable fun g : ℕ → ℝ => stopSum eps g - ((gapSegLen eps g).toNat : ℝ) :=
    (measurable_stopSum eps).sub (measurable_toNat_gapSegLen eps)
  have hWmem : MemLp (fun g : ℕ → ℝ => stopSum eps g - ((gapSegLen eps g).toNat : ℝ)) 2
      (iidLaw ν) := (memLp_two_iff_integrable_sq hWm.aestronglyMeasurable).2 hW2i
  have hCS := sq_integral_mul_le hF2 hWmem
  have hvν : lawVar ν ≤ vhi := hν.var_le
  have habs : |∫ y, I y * (y - 1) ∂(ν : Measure ℝ)| ≤ Ks * eps := by
    have hsq : (∫ y, I y * (y - 1) ∂(ν : Measure ℝ)) ^ 2 ≤ CK * vhi * (cPlus / regV vlo) * eps ^ 2 := by
      rw [hid, hrhs]
      refine hCS.trans ?_
      have hW0 : 0 ≤ ∫ g, (stopSum eps g - ((gapSegLen eps g).toNat : ℝ)) ^ 2 ∂(iidLaw ν) :=
        integral_nonneg fun _ => sq_nonneg _
      have hv0 : 0 ≤ lawVar ν := integral_nonneg fun _ => sq_nonneg _
      calc (∫ g, F (stopSum eps g) ^ 2 ∂(iidLaw ν)) *
            ∫ g, (stopSum eps g - ((gapSegLen eps g).toNat : ℝ)) ^ 2 ∂(iidLaw ν)
          ≤ CK * (lawVar ν * lawC eps ν) := mul_le_mul hF2le hW2 hW0 hCK.le
        _ ≤ CK * (vhi * (cPlus * eps ^ 2 / regV vlo)) := by
            have : 0 ≤ vhi := hvlo.le.trans hv
            gcongr
        _ = CK * vhi * (cPlus / regV vlo) * eps ^ 2 := by ring
    have h := Real.abs_le_sqrt hsq
    have hvhi : 0 < vhi := hvlo.trans_le hv
    rwa [Real.sqrt_mul (by positivity), Real.sqrt_sq heps0.le] at h
  have hsl := hν.abs_slope_le hθ hIint hα' hE₀ hae
  have hvl : 0 < vlo := hvlo
  rw [div_mul_eq_mul_div, le_div_iff₀ hvl]
  calc |b'| * vlo ≤ |∫ y, I y * (y - 1) ∂(ν : Measure ℝ)| + E₀ * Kc := hsl
    _ ≤ Ks * eps + E₀ * Kc := by linarith
    _ ≤ max Ks Kc * eps + max Ks Kc * E₀ := by
        have h1 : Ks ≤ max Ks Kc := le_max_left _ _
        have h2 : Kc ≤ max Ks Kc := le_max_right _ _
        nlinarith
    _ = max Ks Kc * (eps + E₀) := by ring

end

end PGM
