import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic

/-! # Polynomial moments from a genuine exponential tail

An exponential tail on the integer grid already forces every polynomial moment
to be finite, with a bound depending only on the tail constants.  This is the
tail-integration step used for the uniform first-restart margin moments.
-/
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology
namespace SwingRepair
set_option backward.isDefEq.respectTransparency false

/-- The explicit majorant series of a `k`-th moment under an exponential tail. -/
def expTailMomentSum (c : ℝ) (k : ℕ) : ℝ :=
  ∑' n : ℕ, ((n : ℝ)+1)^k*Real.exp (-c*(n : ℝ))

theorem summable_expTailMoment {c : ℝ} (hc : 0 < c) (k : ℕ) :
    Summable (fun n : ℕ => ((n : ℝ)+1)^k*Real.exp (-c*(n : ℝ))) := by
  set r : ℝ := Real.exp (-c) with hr
  have hr0 : 0 < r := Real.exp_pos _
  have hr1 : ‖r‖ < 1 := by
    rw [Real.norm_of_nonneg hr0.le, hr]
    exact Real.exp_lt_one_iff.mpr (by linarith)
  have hbase : Summable (fun n : ℕ => (n : ℝ)^k*r^n) :=
    summable_pow_mul_geometric_of_norm_lt_one k hr1
  have hshift : Summable (fun n : ℕ => (((n+1 : ℕ) : ℝ))^k*r^(n+1)) :=
    (summable_nat_add_iff 1).mpr hbase
  have hmul := hshift.mul_left r⁻¹
  apply hmul.congr
  intro n
  have hpow : Real.exp (-c*(n : ℝ)) = r^n := by
    rw [hr, ← Real.exp_nat_mul]
    congr 1
    ring
  have hrn : r^(n+1) = r*r^n := by ring
  rw [hpow, hrn]
  push_cast
  field_simp

theorem expTailMomentSum_nonneg (c : ℝ) (k : ℕ) : 0 ≤ expTailMomentSum c k :=
  tsum_nonneg fun n => by positivity

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {X : Ω → ℝ}

/-- Binwise tail integration: an exponential tail on the integers bounds every
polynomial moment by an explicit convergent series. -/
theorem lintegral_pow_le_of_expTail
    (hX : Measurable X) (hn : ∀ᵐ ω ∂μ, 0 ≤ X ω) {C c : ℝ} (hC : 0 ≤ C) (hc : 0 < c)
    (htail : ∀ n : ℕ, μ {ω | (n : ℝ) ≤ X ω} ≤ ENNReal.ofReal (C*Real.exp (-c*(n : ℝ))))
    (k : ℕ) :
    (∫⁻ ω, ENNReal.ofReal (X ω^k) ∂μ) ≤ ENNReal.ofReal (C*expTailMomentSum c k) := by
  set S : ℕ → Set Ω := fun n => {ω | (n : ℝ) ≤ X ω} with hS
  have hSm (n : ℕ) : MeasurableSet (S n) := measurableSet_le measurable_const hX
  set F : ℕ → Ω → ℝ≥0∞ := fun n => (S n).indicator (fun _ => ENNReal.ofReal (((n : ℝ)+1)^k)) with hF
  have hFm (n : ℕ) : Measurable (F n) := measurable_const.indicator (hSm n)
  have hpoint : (fun ω => ENNReal.ofReal (X ω^k)) ≤ᵐ[μ] (fun ω => ∑' n, F n ω) := by
    filter_upwards [hn] with ω hω
    set n := ⌊X ω⌋₊ with hn'
    have hlo : (n : ℝ) ≤ X ω := Nat.floor_le hω
    have hhi : X ω ≤ (n : ℝ)+1 := (Nat.lt_floor_add_one _).le
    calc
      ENNReal.ofReal (X ω^k) ≤ ENNReal.ofReal (((n : ℝ)+1)^k) :=
        ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ hω hhi k)
      _ = F n ω := by simp only [hF, Set.indicator_of_mem (show ω ∈ S n from hlo)]
      _ ≤ ∑' n, F n ω := ENNReal.le_tsum n
  have hsum := summable_expTailMoment hc k
  calc
    (∫⁻ ω, ENNReal.ofReal (X ω^k) ∂μ) ≤ ∫⁻ ω, ∑' n, F n ω ∂μ := lintegral_mono_ae hpoint
    _ = ∑' n : ℕ, ENNReal.ofReal (((n : ℝ)+1)^k)*μ (S n) := by
      rw [lintegral_tsum (fun n => (hFm n).aemeasurable)]
      exact tsum_congr fun n => lintegral_indicator_const (hSm n) _
    _ ≤ ∑' n : ℕ, ENNReal.ofReal (((n : ℝ)+1)^k)*ENNReal.ofReal (C*Real.exp (-c*(n : ℝ))) :=
      ENNReal.tsum_le_tsum fun n => mul_le_mul' (le_refl _) (htail n)
    _ = ∑' n : ℕ, ENNReal.ofReal (C*(((n : ℝ)+1)^k*Real.exp (-c*(n : ℝ)))) := by
      refine tsum_congr fun n => ?_
      rw [← ENNReal.ofReal_mul (by positivity)]
      congr 1
      ring
    _ = ENNReal.ofReal (C*expTailMomentSum c k) := by
      rw [expTailMomentSum, ← tsum_mul_left,
        ENNReal.ofReal_tsum_of_nonneg (fun n => by positivity) (hsum.mul_left C)]

/-- The corresponding Bochner statement, including integrability. -/
theorem integrable_pow_of_expTail
    (hX : Measurable X) (hn : ∀ᵐ ω ∂μ, 0 ≤ X ω) {C c : ℝ} (hC : 0 ≤ C) (hc : 0 < c)
    (htail : ∀ n : ℕ, μ {ω | (n : ℝ) ≤ X ω} ≤ ENNReal.ofReal (C*Real.exp (-c*(n : ℝ))))
    (k : ℕ) : Integrable (fun ω => X ω^k) μ := by
  have hnonneg : 0 ≤ᵐ[μ] fun ω => X ω^k := by
    filter_upwards [hn] with ω hω using pow_nonneg hω k
  apply (lintegral_ofReal_ne_top_iff_integrable (hX.pow_const k).aestronglyMeasurable hnonneg).mp
  exact ((lintegral_pow_le_of_expTail hX hn hC hc htail k).trans_lt ENNReal.ofReal_lt_top).ne

theorem integral_pow_le_of_expTail
    (hX : Measurable X) (hn : ∀ᵐ ω ∂μ, 0 ≤ X ω) {C c : ℝ} (hC : 0 ≤ C) (hc : 0 < c)
    (htail : ∀ n : ℕ, μ {ω | (n : ℝ) ≤ X ω} ≤ ENNReal.ofReal (C*Real.exp (-c*(n : ℝ))))
    (k : ℕ) : (∫ ω, X ω^k ∂μ) ≤ C*expTailMomentSum c k := by
  have hnonneg : 0 ≤ᵐ[μ] fun ω => X ω^k := by
    filter_upwards [hn] with ω hω using pow_nonneg hω k
  rw [integral_eq_lintegral_of_nonneg_ae hnonneg (hX.pow_const k).aestronglyMeasurable]
  have h := lintegral_pow_le_of_expTail hX hn hC hc htail k
  have := ENNReal.toReal_mono ENNReal.ofReal_ne_top h
  rwa [ENNReal.toReal_ofReal (mul_nonneg hC (expTailMomentSum_nonneg c k))] at this

/-! ## Exponential moments

The same integer-grid tail also controls every exponential moment of order
strictly below the tail rate.  This is the form required by a uniform renewal
theorem, which asks for a finite exponential moment rather than polynomial ones.
-/

/-- The explicit majorant series of an exponential moment under an exponential tail. -/
def expTailExpMomentSum (c θ : ℝ) : ℝ :=
  ∑' n : ℕ, Real.exp (θ*((n : ℝ)+1))*Real.exp (-c*(n : ℝ))

theorem expTail_exp_term_eq (c θ : ℝ) (n : ℕ) :
    Real.exp (θ*((n : ℝ)+1))*Real.exp (-c*(n : ℝ)) =
      Real.exp θ*(Real.exp (θ-c))^n := by
  rw [← Real.exp_add, ← Real.exp_nat_mul, ← Real.exp_add]
  congr 1
  ring

theorem summable_expTailExpMoment {c θ : ℝ} (hθc : θ < c) :
    Summable (fun n : ℕ => Real.exp (θ*((n : ℝ)+1))*Real.exp (-c*(n : ℝ))) := by
  have hr : ‖Real.exp (θ-c)‖ < 1 := by
    rw [Real.norm_of_nonneg (Real.exp_pos _).le]
    exact Real.exp_lt_one_iff.mpr (by linarith)
  have hbase : Summable (fun n : ℕ => Real.exp θ*(Real.exp (θ-c))^n) :=
    (summable_geometric_of_norm_lt_one hr).mul_left _
  exact hbase.congr (fun n => (expTail_exp_term_eq c θ n).symm)

theorem expTailExpMomentSum_nonneg (c θ : ℝ) : 0 ≤ expTailExpMomentSum c θ :=
  tsum_nonneg fun n => by positivity

/-- Binwise tail integration for an exponential moment. -/
theorem lintegral_exp_le_of_expTail
    (hX : Measurable X) (hn : ∀ᵐ ω ∂μ, 0 ≤ X ω) {C c θ : ℝ} (hC : 0 ≤ C)
    (hθ : 0 ≤ θ) (hθc : θ < c)
    (htail : ∀ n : ℕ, μ {ω | (n : ℝ) ≤ X ω} ≤ ENNReal.ofReal (C*Real.exp (-c*(n : ℝ)))) :
    (∫⁻ ω, ENNReal.ofReal (Real.exp (θ*X ω)) ∂μ) ≤
      ENNReal.ofReal (C*expTailExpMomentSum c θ) := by
  set S : ℕ → Set Ω := fun n => {ω | (n : ℝ) ≤ X ω} with hS
  have hSm (n : ℕ) : MeasurableSet (S n) := measurableSet_le measurable_const hX
  set F : ℕ → Ω → ℝ≥0∞ :=
    fun n => (S n).indicator (fun _ => ENNReal.ofReal (Real.exp (θ*((n : ℝ)+1)))) with hF
  have hFm (n : ℕ) : Measurable (F n) := measurable_const.indicator (hSm n)
  have hpoint : (fun ω => ENNReal.ofReal (Real.exp (θ*X ω))) ≤ᵐ[μ] (fun ω => ∑' n, F n ω) := by
    filter_upwards [hn] with ω hω
    set n := ⌊X ω⌋₊ with hn'
    have hlo : (n : ℝ) ≤ X ω := Nat.floor_le hω
    have hhi : X ω ≤ (n : ℝ)+1 := (Nat.lt_floor_add_one _).le
    calc
      ENNReal.ofReal (Real.exp (θ*X ω)) ≤ ENNReal.ofReal (Real.exp (θ*((n : ℝ)+1))) := by
        refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr ?_)
        exact mul_le_mul_of_nonneg_left hhi hθ
      _ = F n ω := by simp only [hF, Set.indicator_of_mem (show ω ∈ S n from hlo)]
      _ ≤ ∑' n, F n ω := ENNReal.le_tsum n
  have hsum := summable_expTailExpMoment hθc
  calc
    (∫⁻ ω, ENNReal.ofReal (Real.exp (θ*X ω)) ∂μ) ≤ ∫⁻ ω, ∑' n, F n ω ∂μ :=
      lintegral_mono_ae hpoint
    _ = ∑' n : ℕ, ENNReal.ofReal (Real.exp (θ*((n : ℝ)+1)))*μ (S n) := by
      rw [lintegral_tsum (fun n => (hFm n).aemeasurable)]
      exact tsum_congr fun n => lintegral_indicator_const (hSm n) _
    _ ≤ ∑' n : ℕ, ENNReal.ofReal (Real.exp (θ*((n : ℝ)+1)))*
          ENNReal.ofReal (C*Real.exp (-c*(n : ℝ))) :=
      ENNReal.tsum_le_tsum fun n => mul_le_mul' (le_refl _) (htail n)
    _ = ∑' n : ℕ, ENNReal.ofReal
          (C*(Real.exp (θ*((n : ℝ)+1))*Real.exp (-c*(n : ℝ)))) := by
      refine tsum_congr fun n => ?_
      rw [← ENNReal.ofReal_mul (by positivity)]
      congr 1
      ring
    _ = ENNReal.ofReal (C*expTailExpMomentSum c θ) := by
      rw [expTailExpMomentSum, ← tsum_mul_left,
        ENNReal.ofReal_tsum_of_nonneg (fun n => by positivity) (hsum.mul_left C)]

theorem integrable_exp_of_expTail
    (hX : Measurable X) (hn : ∀ᵐ ω ∂μ, 0 ≤ X ω) {C c θ : ℝ} (hC : 0 ≤ C)
    (hθ : 0 ≤ θ) (hθc : θ < c)
    (htail : ∀ n : ℕ, μ {ω | (n : ℝ) ≤ X ω} ≤ ENNReal.ofReal (C*Real.exp (-c*(n : ℝ)))) :
    Integrable (fun ω => Real.exp (θ*X ω)) μ := by
  have hnonneg : 0 ≤ᵐ[μ] fun ω => Real.exp (θ*X ω) :=
    Filter.Eventually.of_forall fun ω => (Real.exp_pos _).le
  have hmeas : Measurable (fun ω => Real.exp (θ*X ω)) :=
    Real.measurable_exp.comp (measurable_const.mul hX)
  apply (lintegral_ofReal_ne_top_iff_integrable hmeas.aestronglyMeasurable hnonneg).mp
  exact ((lintegral_exp_le_of_expTail hX hn hC hθ hθc htail).trans_lt
    ENNReal.ofReal_lt_top).ne

theorem integral_exp_le_of_expTail
    (hX : Measurable X) (hn : ∀ᵐ ω ∂μ, 0 ≤ X ω) {C c θ : ℝ} (hC : 0 ≤ C)
    (hθ : 0 ≤ θ) (hθc : θ < c)
    (htail : ∀ n : ℕ, μ {ω | (n : ℝ) ≤ X ω} ≤ ENNReal.ofReal (C*Real.exp (-c*(n : ℝ)))) :
    (∫ ω, Real.exp (θ*X ω) ∂μ) ≤ C*expTailExpMomentSum c θ := by
  have hnonneg : 0 ≤ᵐ[μ] fun ω => Real.exp (θ*X ω) :=
    Filter.Eventually.of_forall fun ω => (Real.exp_pos _).le
  have hmeas : Measurable (fun ω => Real.exp (θ*X ω)) :=
    Real.measurable_exp.comp (measurable_const.mul hX)
  rw [integral_eq_lintegral_of_nonneg_ae hnonneg hmeas.aestronglyMeasurable]
  have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top
    (lintegral_exp_le_of_expTail hX hn hC hθ hθc htail)
  rwa [ENNReal.toReal_ofReal (mul_nonneg hC (expTailExpMomentSum_nonneg c θ))] at h

end SwingRepair
