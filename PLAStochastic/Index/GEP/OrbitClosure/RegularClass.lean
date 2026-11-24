import PLAStochastic.Index.GEP.OrbitClosure.Defs
import PLAStochastic.Index.GEP.LayerLaw.WeightedDistance
import PLAStochastic.Index.Endpoint.HyperSegmentMoments
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic

/-!
# WP2: conversions between `RegLaw` and the measure-form classes

* From a regular law: `RegLaw.momClass` (class constants `regB`, `regBeta`, `regV`),
  `RegLaw.expMom` (`E e^{θX/2} ≤ 2D/θ`, from `RegLaw.lintegral_exp_le`), `RegLaw.envBd`.
* Monotonicity: `ExpMom.mono`, `EnvBd.mono`, and `EnvBd.locBd` (`K e^{-cx} ≤ K`).
* Back to a regular law: `regLaw_of_envBd`.  A law dominated by `K e^{-cx} 1_{x>0} dx` is
  absolutely continuous; take `f = min((dρ/dx).toReal, envFun K c)`
  (`Measure.withDensity_rnDeriv_eq`, `ae_le_of_forall_setLIntegral_le_of_sigmaFinite`).

The third-moment constant uses `∫_0^∞ (x + 1)³ e^{-θx} dx = 6/θ⁴ + 6/θ³ + 3/θ² + 1/θ` and
`|x - 1| ≤ x + 1` on `x ≥ 0`.
-/

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

/-- The third-moment bound of `RegLaw D θ`: `D ∫_0^∞ (x + 1)³ e^{-θx} dx`. -/
def regKappa (D θ : ℝ) : ℝ := D * (6 / θ ^ 4 + 6 / θ ^ 3 + 3 / θ ^ 2 + 1 / θ)

/-- Upper variance constant of the orbit class. -/
def regB (vhi : ℝ) : ℝ := max vhi bAbs

/-- Third-moment constant of the orbit class. -/
def regBeta (D θ vlo : ℝ) : ℝ := max (max 1 βAbs) (regKappa D θ / Real.sqrt vlo ^ 3)

/-- Lower variance constant of the orbit class. -/
def regV (vlo : ℝ) : ℝ := min vlo (deltaVar / 2)

theorem bAbs_le_regB (vhi : ℝ) : bAbs ≤ regB vhi := le_max_right _ _

theorem βAbs_le_regBeta (D θ vlo : ℝ) : βAbs ≤ regBeta D θ vlo :=
  (le_max_right _ _).trans (le_max_left _ _)

theorem one_le_regBeta (D θ vlo : ℝ) : 1 ≤ regBeta D θ vlo :=
  (le_max_left _ _).trans (le_max_left _ _)

theorem regV_pos {vlo : ℝ} (h : 0 < vlo) : 0 < regV vlo :=
  lt_min h (half_pos deltaVar_pos)

theorem regV_le_half (vlo : ℝ) : regV vlo ≤ deltaVar / 2 := min_le_right _ _

theorem regV_le_regB {vlo vhi : ℝ} (h : vlo ≤ vhi) : regV vlo ≤ regB vhi :=
  (min_le_left _ _).trans (h.trans (le_max_left _ _))

variable {D θ vlo vhi : ℝ}

/-! ### Auxiliary integrals -/

/-- `∫_0^∞ x^k e^{-cx} dx = k!/c^{k+1}`, with integrability. -/
private theorem integral_pow_mul_exp_Ioi (k : ℕ) {c : ℝ} (hc : 0 < c) :
    IntegrableOn (fun x : ℝ => x ^ k * Real.exp (-(c * x))) (Ioi 0) ∧
      ∫ x in Ioi (0 : ℝ), x ^ k * Real.exp (-(c * x)) = (k.factorial : ℝ) / c ^ (k + 1) := by
  have hk : (0 : ℝ) < ↑k + 1 := by positivity
  have key := Real.integral_rpow_mul_exp_neg_mul_Ioi hk hc
  have e : ∀ x ∈ Ioi (0 : ℝ), x ^ ((↑k + 1 : ℝ) - 1) * Real.exp (-(c * x)) =
      x ^ k * Real.exp (-(c * x)) := by
    intro x _
    rw [add_sub_cancel_right, Real.rpow_natCast]
  have key' : ∫ x in Ioi (0 : ℝ), x ^ k * Real.exp (-(c * x)) =
      (1 / c) ^ ((k : ℝ) + 1) * Real.Gamma ((k : ℝ) + 1) := by
    rw [← key]; exact (setIntegral_congr_fun measurableSet_Ioi e).symm
  have hval : ∫ x in Ioi (0 : ℝ), x ^ k * Real.exp (-(c * x)) = (k.factorial : ℝ) / c ^ (k + 1) := by
    rw [key', Real.Gamma_nat_eq_factorial, one_div, Real.inv_rpow hc.le, ← Real.rpow_natCast c (k + 1)]
    push_cast
    ring
  refine ⟨.of_integral_ne_zero ?_, hval⟩
  rw [hval]; positivity

/-- `∫_0^∞ D (x+1)³ e^{-θx} dx = regKappa D θ`. -/
private theorem integral_cube_mul_exp {D θ : ℝ} (hθ : 0 < θ) :
    IntegrableOn (fun x : ℝ => D * ((x + 1) ^ 3 * Real.exp (-(θ * x)))) (Ioi 0) ∧
      ∫ x in Ioi (0 : ℝ), D * ((x + 1) ^ 3 * Real.exp (-(θ * x))) = regKappa D θ := by
  obtain ⟨i3, v3⟩ := integral_pow_mul_exp_Ioi 3 hθ
  obtain ⟨i2, v2⟩ := integral_pow_mul_exp_Ioi 2 hθ
  obtain ⟨i1, v1⟩ := integral_pow_mul_exp_Ioi 1 hθ
  obtain ⟨i0, v0⟩ := integral_pow_mul_exp_Ioi 0 hθ
  have e : (fun x : ℝ => D * ((x + 1) ^ 3 * Real.exp (-(θ * x)))) = fun x =>
      D * (x ^ 3 * Real.exp (-(θ * x)) + 3 * (x ^ 2 * Real.exp (-(θ * x))) +
        3 * (x ^ 1 * Real.exp (-(θ * x))) + x ^ 0 * Real.exp (-(θ * x))) := by
    ext x; ring
  set μ := volume.restrict (Ioi (0 : ℝ)) with hμ
  have j3 : Integrable (fun x : ℝ => x ^ 3 * Real.exp (-(θ * x))) μ := i3
  have j2 : Integrable (fun x : ℝ => 3 * (x ^ 2 * Real.exp (-(θ * x)))) μ := i2.const_mul 3
  have j1 : Integrable (fun x : ℝ => 3 * (x ^ 1 * Real.exp (-(θ * x)))) μ := i1.const_mul 3
  have j0 : Integrable (fun x : ℝ => x ^ 0 * Real.exp (-(θ * x))) μ := i0
  have j32 : Integrable (fun x : ℝ => x ^ 3 * Real.exp (-(θ * x)) +
      3 * (x ^ 2 * Real.exp (-(θ * x)))) μ := j3.add j2
  have j321 : Integrable (fun x : ℝ => x ^ 3 * Real.exp (-(θ * x)) +
      3 * (x ^ 2 * Real.exp (-(θ * x))) + 3 * (x ^ 1 * Real.exp (-(θ * x)))) μ := j32.add j1
  have jS : Integrable (fun x : ℝ => x ^ 3 * Real.exp (-(θ * x)) +
      3 * (x ^ 2 * Real.exp (-(θ * x))) + 3 * (x ^ 1 * Real.exp (-(θ * x))) +
        x ^ 0 * Real.exp (-(θ * x))) μ := j321.add j0
  refine ⟨e ▸ jS.const_mul D, ?_⟩
  rw [e, integral_const_mul, integral_add j321 j0, integral_add j32 j1, integral_add j3 j2,
    integral_const_mul, integral_const_mul, v3, v2, v1, v0]
  unfold regKappa
  norm_num [Nat.factorial]
  left
  ring

/-- Lower integrals of functions dominated by `(x+1)³` on `(0,∞)` are at most `regKappa`. -/
private theorem RegLaw.lintegral_le_regKappa {ν : ProbabilityMeasure ℝ}
    (h : RegLaw D θ vlo vhi ν) (hθ : 0 < θ) {g : ℝ → ℝ} (hg : Measurable g)
    (hg0 : ∀ x, 0 ≤ g x) (hgle : ∀ x, 0 < x → g x ≤ (x + 1) ^ 3) :
    ∫⁻ x, ENNReal.ofReal (g x) ∂(ν : Measure ℝ) ≤ ENNReal.ofReal (regKappa D θ) := by
  obtain ⟨f, hfm, hf0, hfz, hfD, hν⟩ := h.density
  have hD := h.D_nonneg
  obtain ⟨hI, hval⟩ := integral_cube_mul_exp (D := D) hθ
  rw [hν, lintegral_withDensity_eq_lintegral_mul _ hfm.ennreal_ofReal hg.ennreal_ofReal]
  calc ∫⁻ x, ((fun x => ENNReal.ofReal (f x)) * fun x => ENNReal.ofReal (g x)) x
      ≤ ∫⁻ x, (Ioi (0 : ℝ)).indicator
          (fun x => ENNReal.ofReal (D * ((x + 1) ^ 3 * Real.exp (-(θ * x))))) x := by
        refine lintegral_mono fun x => ?_
        simp only [Pi.mul_apply]
        rcases le_or_gt x 0 with hx | hx
        · rw [hfz x hx]; simp
        · rw [Set.indicator_of_mem (show x ∈ Ioi (0 : ℝ) from hx), ← ENNReal.ofReal_mul (hf0 x)]
          apply ENNReal.ofReal_le_ofReal
          calc f x * g x ≤ D * Real.exp (-θ * x) * (x + 1) ^ 3 :=
                mul_le_mul (hfD x) (hgle x hx) (hg0 x) (by positivity)
            _ = D * ((x + 1) ^ 3 * Real.exp (-(θ * x))) := by rw [neg_mul]; ring
    _ = ENNReal.ofReal (regKappa D θ) := by
        rw [lintegral_indicator measurableSet_Ioi, ← hval,
          ofReal_integral_eq_lintegral_ofReal hI
            ((ae_restrict_iff' measurableSet_Ioi).2 (ae_of_all _ fun x hx => by
              have hx0 : (0 : ℝ) < x := hx
              positivity))]

/-- A regular law puts no mass on `(-∞, 0]`. -/
private theorem RegLaw.measure_Iic_zero {ν : ProbabilityMeasure ℝ} (h : RegLaw D θ vlo vhi ν) :
    (ν : Measure ℝ) (Iic 0) = 0 := by
  obtain ⟨f, -, -, hfz, -, hν⟩ := h.density
  rw [hν, withDensity_apply _ measurableSet_Iic]
  refine (setLIntegral_congr_fun measurableSet_Iic (g := fun _ => (0 : ENNReal)) ?_).trans
    (by simp)
  intro y hy
  simp [hfz y hy]

/-- A regular law is in the orbit moment class. -/
theorem RegLaw.momClass {ν : ProbabilityMeasure ℝ} (h : RegLaw D θ vlo vhi ν) (hθ : 0 < θ)
    (hvlo : 0 < vlo) : MomClass (regB vhi) (regBeta D θ vlo) (regV vlo) ν := by
  have hpos := h.measure_Iic_zero
  have hae : ∀ᵐ x ∂(ν : Measure ℝ), 0 < x := by
    filter_upwards [compl_mem_ae_iff.2 hpos] with x hx
    simpa using hx
  have hD := h.D_nonneg
  -- the third moment
  have h3 : ∫⁻ x, ENNReal.ofReal (|x - 1| ^ 3) ∂(ν : Measure ℝ) ≤ ENNReal.ofReal (regKappa D θ) :=
    h.lintegral_le_regKappa hθ (by fun_prop) (fun x => by positivity) fun x hx => by
      gcongr
      rw [abs_le]; constructor <;> linarith
  have hx3 : ∫⁻ x, ENNReal.ofReal (|x| ^ (3 : ℝ)) ∂(ν : Measure ℝ) ≤
      ENNReal.ofReal (regKappa D θ) :=
    h.lintegral_le_regKappa hθ (continuous_abs.rpow_const fun _ => Or.inr (by norm_num)).measurable
      (fun x => by positivity) fun x hx => by
      rw [abs_of_pos hx, show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
      gcongr
      linarith
  have hmem : MemLp id 3 (ν : Measure ℝ) := by
    rw [← integrable_norm_rpow_iff aestronglyMeasurable_id (by norm_num) (by norm_num)]
    simp only [id, Real.norm_eq_abs, ENNReal.toReal_ofNat]
    refine ⟨(continuous_abs.rpow_const fun _ => Or.inr (by norm_num)).aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ fun x => by positivity)]
    exact lt_of_le_of_lt hx3 ENNReal.ofReal_lt_top
  have hint3 : Integrable (fun x => |x - 1| ^ 3) (ν : Measure ℝ) := by
    refine ⟨by fun_prop, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ fun x => by positivity)]
    exact lt_of_le_of_lt h3 ENNReal.ofReal_lt_top
  have hthird : ∫ x, |x - 1| ^ 3 ∂(ν : Measure ℝ) ≤ regKappa D θ := by
    rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun x => by positivity)
      hint3.aestronglyMeasurable]
    have hk : 0 ≤ regKappa D θ := by unfold regKappa; positivity
    calc (∫⁻ x, ENNReal.ofReal (|x - 1| ^ 3) ∂(ν : Measure ℝ)).toReal
        ≤ (ENNReal.ofReal (regKappa D θ)).toReal :=
          ENNReal.toReal_mono ENNReal.ofReal_ne_top h3
      _ = regKappa D θ := ENNReal.toReal_ofReal hk
  have hsq : Real.sqrt vlo ^ 3 ≤ Real.sqrt (lawVar ν) ^ 3 := by
    gcongr; exact h.var_ge
  have hsv : 0 < Real.sqrt vlo ^ 3 := by positivity
  refine ⟨hpos, hmem, h.mean, (min_le_left _ _).trans h.var_ge,
    h.var_le.trans (le_max_left _ _), ?_⟩
  calc ∫ x, |x - 1| ^ 3 ∂(ν : Measure ℝ) ≤ regKappa D θ := hthird
    _ = regKappa D θ / Real.sqrt vlo ^ 3 * Real.sqrt vlo ^ 3 := by field_simp
    _ ≤ regBeta D θ vlo * Real.sqrt (lawVar ν) ^ 3 := by
        refine mul_le_mul (le_max_right _ _) hsq hsv.le ?_
        exact le_trans zero_le_one (one_le_regBeta D θ vlo)

/-- A regular law has the exponential moment `E e^{θX/2} ≤ 2D/θ`. -/
theorem RegLaw.expMom {ν : ProbabilityMeasure ℝ} (h : RegLaw D θ vlo vhi ν) (hθ : 0 < θ) :
    ExpMom (θ / 2) (2 * D / θ) ν := by
  have hl := h.lintegral_exp_le (a := θ / 2) (by linarith)
  have e : D / (θ - θ / 2) = 2 * D / θ := by field_simp; ring
  rw [e] at hl
  have hm : Measurable fun x : ℝ => Real.exp (θ / 2 * x) := by fun_prop
  have hint : Integrable (fun x => Real.exp (θ / 2 * x)) (ν : Measure ℝ) := by
    refine ⟨hm.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ fun x => (Real.exp_pos _).le)]
    exact lt_of_le_of_lt hl ENNReal.ofReal_lt_top
  refine ⟨hint, ?_⟩
  rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun x => (Real.exp_pos _).le)
    hm.aestronglyMeasurable]
  have h2 : 0 ≤ 2 * D / θ := by have := h.D_nonneg; positivity
  calc (∫⁻ x, ENNReal.ofReal (Real.exp (θ / 2 * x)) ∂(ν : Measure ℝ)).toReal
      ≤ (ENNReal.ofReal (2 * D / θ)).toReal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hl
    _ = 2 * D / θ := ENNReal.toReal_ofReal h2

/-- A regular law is dominated by its envelope. -/
theorem RegLaw.envBd {ν : ProbabilityMeasure ℝ} (h : RegLaw D θ vlo vhi ν) :
    EnvBd D θ (ν : Measure ℝ) := by
  obtain ⟨f, -, -, hfz, hfD, hν⟩ := h.density
  unfold EnvBd
  rw [hν]
  refine withDensity_mono (ae_of_all _ fun x => ENNReal.ofReal_le_ofReal ?_)
  unfold envFun
  rcases le_or_gt x 0 with hx | hx
  · rw [hfz x hx, Set.indicator_of_notMem (show x ∉ Ioi (0 : ℝ) from not_lt.2 hx)]
  · rw [Set.indicator_of_mem (show x ∈ Ioi (0 : ℝ) from hx)]
    simpa [neg_mul] using hfD x

theorem ExpMom.mono {θ B θ' B' : ℝ} {ρ : ProbabilityMeasure ℝ} (h : ExpMom θ B ρ)
    (hpos : (ρ : Measure ℝ) (Iic 0) = 0) (hθ' : 0 ≤ θ') (hθθ : θ' ≤ θ) (hB : B ≤ B') :
    ExpMom θ' B' ρ := by
  have hae : ∀ᵐ x ∂(ρ : Measure ℝ), Real.exp (θ' * x) ≤ Real.exp (θ * x) := by
    filter_upwards [compl_mem_ae_iff.2 hpos] with x hx
    have hx0 : 0 < x := by simpa using hx
    exact Real.exp_le_exp.2 (by nlinarith)
  have hint : Integrable (fun x => Real.exp (θ' * x)) (ρ : Measure ℝ) :=
    h.integrable.mono' (by fun_prop) (by
      filter_upwards [hae] with x hx
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact hx)
  have _ := hθ'
  exact ⟨hint, (integral_mono_ae hint h.integrable hae).trans (h.le.trans hB)⟩

theorem EnvBd.mono {K c K' c' : ℝ} {μ : Measure ℝ} (h : EnvBd K c μ) (hK0 : 0 ≤ K)
    (hK : K ≤ K') (hc : c' ≤ c) : EnvBd K' c' μ := by
  refine le_trans h (withDensity_mono (ae_of_all _ fun x => ENNReal.ofReal_le_ofReal ?_))
  unfold envFun
  rcases le_or_gt x 0 with hx | hx
  · rw [Set.indicator_of_notMem (show x ∉ Ioi (0 : ℝ) from not_lt.2 hx),
      Set.indicator_of_notMem (show x ∉ Ioi (0 : ℝ) from not_lt.2 hx)]
  · rw [Set.indicator_of_mem (show x ∈ Ioi (0 : ℝ) from hx),
      Set.indicator_of_mem (show x ∈ Ioi (0 : ℝ) from hx)]
    exact mul_le_mul hK (Real.exp_le_exp.2 (by nlinarith)) (Real.exp_pos _).le (hK0.trans hK)

theorem EnvBd.locBd {K c : ℝ} {μ : Measure ℝ} (h : EnvBd K c μ) (hK0 : 0 ≤ K) (hc : 0 ≤ c) :
    LocBd K μ := by
  intro A hA
  calc μ A ≤ (volume.withDensity fun x => ENNReal.ofReal (envFun K c x)) A :=
        Measure.le_iff'.1 h A
    _ = ∫⁻ x in A, ENNReal.ofReal (envFun K c x) := withDensity_apply _ hA
    _ ≤ ∫⁻ _ in A, ENNReal.ofReal K := by
        refine lintegral_mono fun x => ENNReal.ofReal_le_ofReal ?_
        unfold envFun
        by_cases hx : x ∈ Ioi (0 : ℝ)
        · rw [Set.indicator_of_mem hx]
          have hx0 : (0 : ℝ) < x := hx
          have : Real.exp (-c * x) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith)
          nlinarith
        · rw [Set.indicator_of_notMem hx]; exact hK0
    _ = ENNReal.ofReal K * volume A := by rw [setLIntegral_const]

/-- **Back to a regular law**: mean one, a variance bracket and an envelope give `RegLaw`. -/
theorem regLaw_of_envBd_of_moments {b vmin K c : ℝ} {ρ : ProbabilityMeasure ℝ}
    (hmean : lawMean ρ = 1) (hvlo : vmin ≤ lawVar ρ) (hvhi : lawVar ρ ≤ b)
    (hE : EnvBd K c (ρ : Measure ℝ)) (hK : 0 ≤ K) :
    RegLaw K c vmin b ρ := by
  set g : ℝ → ENNReal := fun x => ENNReal.ofReal (envFun K c x) with hg_def
  have hgm : Measurable g := by
    refine Measurable.ennreal_ofReal ?_
    unfold envFun
    exact (measurable_const.mul (measurable_const.mul measurable_id).exp).indicator
      measurableSet_Ioi
  have hac : (ρ : Measure ℝ) ≪ volume :=
    (Measure.absolutelyContinuous_of_le hE).trans (withDensity_absolutelyContinuous _ _)
  have hρ : (ρ : Measure ℝ) = volume.withDensity ((ρ : Measure ℝ).rnDeriv volume) :=
    (Measure.withDensity_rnDeriv_eq _ _ hac).symm
  have hle : (ρ : Measure ℝ).rnDeriv volume ≤ᵐ[volume] g := by
    refine ae_le_of_forall_setLIntegral_le_of_sigmaFinite (Measure.measurable_rnDeriv _ _)
      fun s hs _ => ?_
    rw [← withDensity_apply _ hs, ← hρ, ← withDensity_apply _ hs]
    exact Measure.le_iff'.1 hE s
  have henv0 : ∀ x, 0 ≤ envFun K c x := fun x => by
    unfold envFun
    by_cases hx : x ∈ Ioi (0 : ℝ)
    · rw [Set.indicator_of_mem hx]; positivity
    · rw [Set.indicator_of_notMem hx]
  set f : ℝ → ℝ := fun x => min (((ρ : Measure ℝ).rnDeriv volume x).toReal) (envFun K c x)
    with hf_def
  have hfm : Measurable f :=
    (Measure.measurable_rnDeriv _ _).ennreal_toReal.min (by
      unfold envFun
      exact (measurable_const.mul (measurable_const.mul measurable_id).exp).indicator
        measurableSet_Ioi)
  have hfae : (fun x => ENNReal.ofReal (f x)) =ᵐ[volume] (ρ : Measure ℝ).rnDeriv volume := by
    filter_upwards [hle, Measure.rnDeriv_lt_top (ρ : Measure ℝ) volume] with x hx hxt
    simp only [hf_def]
    have htr : ((ρ : Measure ℝ).rnDeriv volume x).toReal ≤ envFun K c x := by
      have := ENNReal.toReal_mono ENNReal.ofReal_ne_top hx
      rwa [ENNReal.toReal_ofReal (henv0 x)] at this
    rw [min_eq_left htr, ENNReal.ofReal_toReal hxt.ne]
  refine ⟨⟨f, hfm, fun x => le_min ENNReal.toReal_nonneg (henv0 x), fun x hx => ?_,
    fun x => ?_, ?_⟩, hmean, hvlo, hvhi⟩
  · refine le_antisymm ?_ (le_min ENNReal.toReal_nonneg (henv0 x))
    refine (min_le_right _ _).trans_eq ?_
    unfold envFun
    exact Set.indicator_of_notMem (show x ∉ Ioi (0 : ℝ) from not_lt.2 hx) _
  · refine (min_le_right _ _).trans ?_
    unfold envFun
    by_cases hx : x ∈ Ioi (0 : ℝ)
    · rw [Set.indicator_of_mem hx]
    · rw [Set.indicator_of_notMem hx]; positivity
  · rw [withDensity_congr_ae hfae]
    exact hρ

/-- The moment class plus an envelope give `RegLaw`. -/
theorem regLaw_of_envBd {b β vmin K c : ℝ} {ρ : ProbabilityMeasure ℝ}
    (hM : MomClass b β vmin ρ) (hE : EnvBd K c (ρ : Measure ℝ)) (hK : 0 ≤ K) :
    RegLaw K c vmin b ρ :=
  regLaw_of_envBd_of_moments hM.mean hM.var_ge hM.var_le hE hK

end

end PGM
