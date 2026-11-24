import PLAStochastic.Index.GEP.Kernel.Row.FreeDensity

/-!
# WP4 kernel rows: boundary survival from the one-sided linear survival input

Source: `influence-lipschitz.md` §3, first display: from either boundary of the band `[0, w]`,
for the forward step `1 - aX` and the reverse step `aX - 1`, `s_n ≤ K (n^{-1/2} + A/w)` when
`|a - 1| ≤ A/w`, and hence `s_n ≤ K (1 + A) n^{-1/2}` for `n ≤ w²`.

The one-sided linear survival bound is the interface `KrLinearSurvival D θ vlo vhi K`, which is
literally the conclusion of `linearSurvival_regLaw` (`GEPLinearSurvivalClass`, developed in a
separate module); this file only uses it as a hypothesis, so that it depends on compiled modules
only.  All four boundary/direction cases reduce to the same event inclusion
`{walk stays in [0, w] up to n} ⊆ {∀ j ≤ n, ±a (S_j - j) ≤ |1 - a| j}` (`krSurv_bdry_le`).
-/

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

variable {J : Set ℝ} {β a : ℝ} (ν : ProbabilityMeasure ℝ)

/-- **Interface**: the class-uniform one-sided linear survival bound
(the statement of `linearSurvival_regLaw D θ vlo vhi hD hθ hvlo hv` for its constant `K`). -/
def KrLinearSurvival (D θ vlo vhi K : ℝ) : Prop :=
  ∀ ν : ProbabilityMeasure ℝ, RegLaw D θ vlo vhi ν →
    ∀ a : ℝ, 1 / 2 ≤ |a| → |a| ≤ 2 → ∀ ρ : ℝ, 0 ≤ ρ → ∀ δ : ℝ, 0 ≤ δ → ∀ n : ℕ, 1 ≤ n →
      (iidLaw ν).real {g | ∀ j ≤ n, a * (gapKeys g j - j) ≤ δ + ρ * j} ≤
        K * (1 + δ) * ((Real.sqrt n)⁻¹ + ρ)

/-! ## Survival is bounded by the probability of any event containing the alive paths -/

theorem krSurv_le_measureReal (hJ : MeasurableSet J) {E : Set (ℕ → ℝ)} (hE : MeasurableSet E)
    (n : ℕ) (y₀ : ℝ) (hsub : ∀ g, (∀ j ≤ n, kWalk y₀ β a g j ∈ J) → g ∈ E) :
    krSurv J (ν : Measure ℝ) β a n y₀ ≤ (iidLaw ν).real E := by
  rw [krSurv_eq_integral hJ ν β a n y₀, ← integral_indicator_one hE]
  refine integral_mono (kr_integrable_of_bdd (measurable_krAlive_right hJ β a n y₀)
    (abs_krAlive_le_one n y₀)) ((integrable_const 1).indicator hE) fun g => ?_
  by_cases hg : ∀ j ≤ n, kWalk y₀ β a g j ∈ J
  · rw [indicator_of_mem (hsub g hg), Pi.one_apply]
    exact krAlive_le_one _ _ _
  · push Not at hg
    obtain ⟨j, hj, hjJ⟩ := hg
    have h0 : krAlive J β a n y₀ g = 0 := by
      unfold krAlive
      exact Finset.prod_eq_zero (Finset.mem_range.2 (Nat.lt_succ_of_le hj))
        (by simp [indicator_of_notMem hjJ])
    rw [h0]
    exact indicator_nonneg (fun _ _ => zero_le_one) _

theorem kr_measurableSet_linEvent (a' ρ δ : ℝ) (n : ℕ) :
    MeasurableSet {g : ℕ → ℝ | ∀ j ≤ n, a' * (gapKeys g j - j) ≤ δ + ρ * j} := by
  have e : {g : ℕ → ℝ | ∀ j ≤ n, a' * (gapKeys g j - j) ≤ δ + ρ * j} =
      ⋂ j ∈ Finset.range (n + 1), {g : ℕ → ℝ | a' * (gapKeys g j - j) ≤ δ + ρ * j} := by
    ext g
    simp
  rw [e]
  refine Finset.measurableSet_biInter _ fun j _ => measurableSet_le ?_ measurable_const
  exact (((measurable_pi_apply j).comp measurable_gapKeys).sub_const _).const_mul _

/-! ## The four boundary cases -/

/-- **Boundary survival from the linear survival input.**  For the band `Icc 0 w`, the forward
step `(β, a') = (1, a)` or the reverse step `(β, a') = (-1, -a)`, and the start `b ∈ {0, w}`,
`s_n(b) ≤ K (n^{-1/2} + |1 - a|)`. -/
theorem krSurv_bdry_le {D θ vlo vhi K : ℝ} (hLS : KrLinearSurvival D θ vlo vhi K)
    (hν : RegLaw D θ vlo vhi ν) (ha₁ : 1 / 2 ≤ |a|) (ha₂ : |a| ≤ 2) {w : ℝ} {n : ℕ} (hn : 1 ≤ n)
    {β a' b : ℝ} (hβ : (β = 1 ∧ a' = a) ∨ (β = -1 ∧ a' = -a)) (hb : b = 0 ∨ b = w) :
    krSurv (Icc 0 w) (ν : Measure ℝ) β a' n b ≤ K * ((Real.sqrt n)⁻¹ + |1 - a|) := by
  have hρ : 0 ≤ |1 - a| := abs_nonneg _
  have h₁ : ∀ j : ℕ, (1 - a) * (j : ℝ) ≤ |1 - a| * j := fun j =>
    mul_le_mul_of_nonneg_right (le_abs_self _) (Nat.cast_nonneg _)
  have h₂ : ∀ j : ℕ, (a - 1) * (j : ℝ) ≤ |1 - a| * j := fun j => by
    rw [abs_sub_comm]
    exact mul_le_mul_of_nonneg_right (le_abs_self _) (Nat.cast_nonneg _)
  have hneg₁ : 1 / 2 ≤ |-a| := by rwa [abs_neg]
  have hneg₂ : |-a| ≤ 2 := by rwa [abs_neg]
  -- the linear survival bound for slope `±a`, `δ = 0`, `ρ = |1 - a|`
  have hLa := hLS ν hν a ha₁ ha₂ |1 - a| hρ 0 le_rfl n hn
  have hLna := hLS ν hν (-a) hneg₁ hneg₂ |1 - a| hρ 0 le_rfl n hn
  simp only [add_zero, mul_one] at hLa hLna
  rcases hβ with ⟨hβ, ha'⟩ | ⟨hβ, ha'⟩ <;> rcases hb with hb | hb <;> subst hβ <;>
    rw [ha', hb]
  · -- forward from `0`: `0 ≤ j - a S_j`
    refine (krSurv_le_measureReal ν measurableSet_Icc (kr_measurableSet_linEvent a |1 - a| 0 n) n 0
      fun g hg j hj => ?_).trans hLa
    have h := (hg j hj).1
    simp only [kWalk] at h
    have := h₁ j
    simp only [zero_add]
    linarith
  · -- forward from `w`: `w + j - a S_j ≤ w`
    refine (krSurv_le_measureReal ν measurableSet_Icc (kr_measurableSet_linEvent (-a) |1 - a| 0 n)
      n w fun g hg j hj => ?_).trans hLna
    have h := (hg j hj).2
    simp only [kWalk] at h
    have := h₂ j
    simp only [zero_add]
    linarith
  · -- reverse from `0`: `0 ≤ -j + a S_j`
    refine (krSurv_le_measureReal ν measurableSet_Icc (kr_measurableSet_linEvent (-a) |1 - a| 0 n)
      n 0 fun g hg j hj => ?_).trans hLna
    have h := (hg j hj).1
    simp only [kWalk] at h
    have := h₂ j
    simp only [zero_add]
    linarith
  · -- reverse from `w`: `w - j + a S_j ≤ w`
    refine (krSurv_le_measureReal ν measurableSet_Icc (kr_measurableSet_linEvent a |1 - a| 0 n) n w
      fun g hg j hj => ?_).trans hLa
    have h := (hg j hj).2
    simp only [kWalk] at h
    have := h₁ j
    simp only [zero_add]
    linarith

/-- Near-critical slopes `|a - 1| ≤ 1/2` satisfy the slope window of the linear survival input. -/
theorem kr_slope_window {a : ℝ} (ha : |a - 1| ≤ 1 / 2) : 1 / 2 ≤ |a| ∧ |a| ≤ 2 := by
  rw [abs_le] at ha
  constructor
  · rw [le_abs]; left; linarith
  · rw [abs_le]; constructor <;> linarith

/-- Boundary survival with the near-critical slope `|a - 1| ≤ A / w`: `s_n(b) ≤ K (n^{-1/2} + A/w)`. -/
theorem krSurv_bdry_le_near {D θ vlo vhi K : ℝ} (hLS : KrLinearSurvival D θ vlo vhi K)
    (hν : RegLaw D θ vlo vhi ν) (hK : 0 ≤ K) {w A : ℝ} (haA : |a - 1| ≤ A / w)
    (ha₁ : 1 / 2 ≤ |a|) (ha₂ : |a| ≤ 2) {n : ℕ} (hn : 1 ≤ n)
    {β a' b : ℝ} (hβ : (β = 1 ∧ a' = a) ∨ (β = -1 ∧ a' = -a)) (hb : b = 0 ∨ b = w) :
    krSurv (Icc 0 w) (ν : Measure ℝ) β a' n b ≤ K * ((Real.sqrt n)⁻¹ + A / w) := by
  refine (krSurv_bdry_le ν hLS hν ha₁ ha₂ hn hβ hb).trans ?_
  rw [abs_sub_comm] at haA
  exact mul_le_mul_of_nonneg_left (add_le_add le_rfl haA) hK

/-- **Medium-time boundary survival**: for `n ≤ w²`, `s_n(b) ≤ K (1 + A) / √n`. -/
theorem krSurv_bdry_le_medium {D θ vlo vhi K : ℝ} (hLS : KrLinearSurvival D θ vlo vhi K)
    (hν : RegLaw D θ vlo vhi ν) (hK : 0 ≤ K) {w A : ℝ} (hw : 0 < w) (hA : 0 ≤ A)
    (haA : |a - 1| ≤ A / w) (ha₁ : 1 / 2 ≤ |a|) (ha₂ : |a| ≤ 2) {n : ℕ} (hn : 1 ≤ n)
    (hnw : (n : ℝ) ≤ w ^ 2)
    {β a' b : ℝ} (hβ : (β = 1 ∧ a' = a) ∨ (β = -1 ∧ a' = -a)) (hb : b = 0 ∨ b = w) :
    krSurv (Icc 0 w) (ν : Measure ℝ) β a' n b ≤ K * (1 + A) / Real.sqrt n := by
  refine (krSurv_bdry_le_near ν hLS hν hK haA ha₁ ha₂ hn hβ hb).trans ?_
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hs : 0 < Real.sqrt n := Real.sqrt_pos.2 hn0
  have hsw : Real.sqrt n ≤ w := by
    rw [show w = Real.sqrt (w ^ 2) from (Real.sqrt_sq hw.le).symm]
    exact Real.sqrt_le_sqrt hnw
  have hAw : A / w ≤ A / Real.sqrt n := div_le_div_of_nonneg_left hA hs hsw
  calc K * ((Real.sqrt n)⁻¹ + A / w) ≤ K * ((Real.sqrt n)⁻¹ + A / Real.sqrt n) := by gcongr
    _ = K * (1 + A) / Real.sqrt n := by field_simp

end

end PGM
