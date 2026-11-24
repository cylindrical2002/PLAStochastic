import PLAStochastic.Affine.Process.DriftedSurvival.GridLower
import PLAStochastic.Swing.DenseSampling.CarriedPrefix.BoundedSurvivalMeasurable

/-! # A concrete carried slope supplies the boundary-sensitive lower bound -/
noncomputable section
open MeasureTheory ProbabilityTheory BrownianAffine Filter Set
open scoped NNReal ENNReal Topology
namespace SwingRepair
set_option backward.isDefEq.respectTransparency false

/-- The complete finite carried fit event, with no a priori slope bound. -/
def nativeCarriedFit (D : ℕ → ℝ) (w ε h : ℝ) (N : ℕ) : Prop :=
  ∃ m : ℝ, ∀ j : ℕ, j ≤ N → w + D j - m * (((j : ℝ)+1)*h) ∈ Icc 0 (2*ε)

/-- The candidate m=-1/t links its carried point to a genuine fresh-grid strip.
It uses feasibility alone, so it applies to every feasible selector. -/
theorem nativeCarriedFit_of_candidate {D : ℕ → ℝ} {w h t : ℝ} {N : ℕ}
    (hD : D 0 = 0) (hcarry : w+h/t ∈ Icc 0 2)
    (hf : ∀ j : ℕ, j ≤ N → w + D 1 + 2*h/t + (D (j+1)-D 1) +
      (1/t)*((j : ℝ)*h) ∈ Icc 0 2) : nativeCarriedFit D w 1 h (N+1) := by
  refine ⟨-1/t, ?_⟩
  intro j hj
  cases j with
  | zero =>
    simp only [Nat.cast_zero, zero_add, one_mul, hD, add_zero]
    convert hcarry using 1 <;> ring_nf
  | succ j =>
    have hb := hf j (by omega)
    convert hb using 1 <;> push_cast <;> ring_nf

/-- The first positive increment creates a boundary distance comparable to
w_+ + sqrt(h), uniformly over the allowed slightly negative carried states. -/
theorem nativeCarriedLower_state_bounds {w M h t z : ℝ} (_hM : 0 ≤ M) (hh : 0 < h)
    (hw : -M*h ≤ w) (hMh : 2*M*h ≤ Real.sqrt h)
    (hMt : M*t ≤ 1) (ht : 0 < t) (htsmall : t ≤ 1/32)
    (hdt : 8*(max w 0 + Real.sqrt h) ≤ t)
    (hz : z ∈ Icc (Real.sqrt h) (2*Real.sqrt h)) :
    w+h/t ∈ Icc 0 2 ∧
      (max w 0 + Real.sqrt h)/2 ≤ w+z+2*h/t ∧ w+z+2*h/t ≤ t/2 := by
  have hs := Real.sqrt_nonneg h
  have hsq := Real.sq_sqrt hh.le
  have hmax : w ≤ max w 0 := le_max_left _ _
  have hmax0 : 0 ≤ max w 0 := le_max_right _ _
  have hdiv : 0 ≤ h/t := div_nonneg hh.le ht.le
  have hdivs : h/t ≤ Real.sqrt h := (div_le_iff₀ ht).mpr (by nlinarith)
  have hMt' : M ≤ 1/t := (le_div_iff₀ ht).mpr hMt
  have hcarry0 : 0 ≤ w+h/t := by
    have hm := mul_le_mul_of_nonneg_right hMt' hh.le
    rw [one_div_mul_eq_div] at hm
    linarith
  have h2 : 2*h/t = 2*(h/t) := by ring
  rw [h2]
  refine ⟨⟨hcarry0, by nlinarith⟩, ?_, ?_⟩
  · by_cases hw0 : 0 ≤ w
    · rw [max_eq_left hw0]
      linarith [hz.1]
    · rw [max_eq_right (le_of_not_ge hw0)]
      nlinarith [hz.1]
  · nlinarith [hz.2]

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

/-- The actual Brownian carried-fit tail is bounded below at every small target
time. No carry independence or renewal hypothesis is used. -/
theorem measureReal_nativeCarriedFit_lower (hB : IsBrownianReal B μ)
    {h T : ℝ≥0} (hh : 0 < h) (hT : 0 < T) (hTs : (T : ℝ) ≤ 1/32)
    {w M : ℝ} (hM : 0 ≤ M) (hw : -M*(h : ℝ) ≤ w)
    (hMh : 2*M*(h : ℝ) ≤ Real.sqrt (h : ℝ)) (hMt : M*(T : ℝ) ≤ 1)
    (hdt : 8*(max w 0+Real.sqrt (h : ℝ)) ≤ (T : ℝ))
    (N : ℕ) (hN : (N : ℝ≥0)*h ≤ T) :
    (Real.exp (-1)*((max w 0+Real.sqrt (h : ℝ))/(2*(T : ℝ)))) *
      gaussianFirstPositivePass.toReal ≤
      μ.real {ω | nativeCarriedFit (fun j => B ((j : ℝ≥0)*h) ω) w 1 (h : ℝ) (N+1)} := by
  let : IsProbabilityMeasure μ := hB.isGaussianProcess.isProbabilityMeasure
  let V (z : ℝ) := w+z+2*(h : ℝ)/(T : ℝ)
  have hv₀ : 0 ≤ (max w 0+Real.sqrt (h : ℝ))/2 := by positivity
  have hrange : ∀ z ∈ Icc (Real.sqrt (h : ℝ)) (2*Real.sqrt (h : ℝ)),
      (max w 0+Real.sqrt (h : ℝ))/2 ≤ V z ∧ V z ≤ (T : ℝ)/2 := by
    intro z hz
    exact (nativeCarriedLower_state_bounds hM (by exact_mod_cast hh) hw hMh hMt
      (by exact_mod_cast hT) hTs hdt hz).2
  have hb := measureReal_brownian_random_start_grid_survival_ge hB hh hT hTs V
    (by fun_prop) hv₀ hrange N hN
  have heq : ((max w 0+Real.sqrt (h : ℝ))/2)/(T : ℝ) =
      (max w 0+Real.sqrt (h : ℝ))/(2*(T : ℝ)) := by ring
  rw [heq] at hb
  apply hb.trans
  apply ENNReal.toReal_mono (measure_ne_top μ _)
  apply measure_mono_ae
  filter_upwards [hB.eval_zero_ae_eq_zero] with ω hz hω
  have hcarry := (nativeCarriedLower_state_bounds hM (by exact_mod_cast hh) hw hMh hMt
    (by exact_mod_cast hT) hTs hdt hω.1).1
  apply nativeCarriedFit_of_candidate (t := (T : ℝ)) (by simpa using hz) hcarry
  intro j hj
  have hg := hω.2 j hj
  simpa only [V, NNReal.coe_mul, NNReal.coe_natCast, Nat.cast_add, Nat.cast_one,
    add_mul, one_mul, add_comm] using hg

end SwingRepair
