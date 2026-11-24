import PLAStochastic.Affine.Process.DriftedSurvival.SmallTimeLower
import PLAStochastic.Affine.Process.DriftedSurvival.GridUpper

/-! # Independent first increment and a near-boundary grid continuation -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology
namespace BrownianAffine
set_option backward.isDefEq.respectTransparency false
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

/-- A sectionwise probability lower bound is integrated against an independent
initial state; the state itself is not declared independent of its past. -/
theorem IndepFun.measure_lower_of_sections {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [IsProbabilityMeasure μ] {X : Ω → α} {Y : Ω → β}
    (hX : AEMeasurable X μ) (hY : AEMeasurable Y μ) (hi : IndepFun X Y μ)
    {A : Set α} (hA : MeasurableSet A) {E : Set (α × β)} (hE : MeasurableSet E)
    {c : ℝ≥0∞} (hc : ∀ x ∈ A, c ≤ μ (Y ⁻¹' (Prod.mk x ⁻¹' E))) :
    c * μ (X ⁻¹' A) ≤ μ ((fun ω => (X ω, Y ω)) ⁻¹' E) := by
  have heq := IndepFun.map_prod_eq_prod_map_map hX hY hi
  rw [← Measure.map_apply_of_aemeasurable (hX.prodMk hY) hE, heq, Measure.prod_apply hE]
  rw [← Measure.map_apply_of_aemeasurable hX hA]
  have hb : A.indicator (fun _ => c) ≤ fun x => (μ.map Y) (Prod.mk x ⁻¹' E) := by
    intro x
    by_cases hx : x ∈ A
    · rw [Set.indicator_of_mem hx]
      dsimp only
      rw [Measure.map_apply_of_aemeasurable hY
        (hE.preimage (show Measurable (Prod.mk x) from measurable_prodMk_left))]
      exact hc x hx
    · simp only [Set.indicator_of_notMem hx]
      exact bot_le
  have hl := lintegral_mono (μ := μ.map X) hb
  simpa only [lintegral_indicator hA, lintegral_const, Measure.restrict_apply_univ] using hl

def gaussianFirstPositivePass : ℝ≥0∞ := gaussianReal 0 1 (Icc (1 : ℝ) 2)

theorem gaussianFirstPositivePass_pos : 0 < gaussianFirstPositivePass := by
  apply pos_iff_ne_zero.mpr
  intro hz
  have hv := (gaussianReal_absolutelyContinuous' 0 (by norm_num : (1 : ℝ≥0) ≠ 0)) hz
  norm_num [gaussianFirstPositivePass, Real.volume_Icc] at hv

theorem brownian_first_positive_pass_probability (hB : IsBrownianReal B μ)
    {h : ℝ≥0} (hh : 0 < h) :
    μ {ω | B h ω ∈ Icc (Real.sqrt (h : ℝ)) (2 * Real.sqrt (h : ℝ))} = gaussianFirstPositivePass := by
  have hs : 0 < Real.sqrt (h : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hh)
  have hl := gaussianReal_div_const (hB.hasLaw_eval h) (Real.sqrt (h : ℝ))
  have hvar : h / (NNReal.mk ((Real.sqrt (h : ℝ))^2) (sq_nonneg _)) = 1 := by
    have heq : (NNReal.mk ((Real.sqrt (h : ℝ))^2) (sq_nonneg _)) = h := by
      ext
      exact Real.sq_sqrt h.coe_nonneg
    rw [heq, div_self hh.ne']
  rw [zero_div, hvar] at hl
  have hp := hl.measure_eq (p := fun z => z ∈ Icc (1 : ℝ) 2) measurableSet_Icc
  convert hp using 1
  · congr 1
    ext ω
    simp only [mem_ofPred_eq, mem_Icc, le_div_iff₀ hs, div_le_iff₀ hs, one_mul]
  · rfl

theorem indepFun_brownian_first_gridFuture (hB : IsBrownianReal B μ) (h : ℝ≥0) :
    IndepFun (B h) (fun ω (j : ℕ) => B (h + (j : ℝ≥0)*h) ω - B h ω) μ := by
  have hi := (hB.indepFun_shift h).comp
    (measurable_pi_lambda _ (fun j : ℕ => measurable_pi_apply ((j : ℝ≥0)*h)))
    (measurable_pi_apply (⟨h, show h ∈ Set.Iic h from Set.mem_Iic.mpr le_rfl⟩ : Set.Iic h))
  simpa only [Function.comp_def] using hi.symm

/-- Every fixed start in the small boundary layer has the same genuine lower
bound for a finite future grid. -/
theorem measureReal_brownian_grid_survival_small_ge (hB : IsBrownianReal B μ)
    {T : ℝ≥0} (hT : 0 < T) (hTs : (T : ℝ) ≤ 1/32)
    {x : ℝ} (hx : 0 ≤ x) (hxT : x ≤ (T : ℝ)/2) (h : ℝ≥0) (N : ℕ)
    (hN : (N : ℝ≥0)*h ≤ T) :
    Real.exp (-1)*(x/(T : ℝ)) ≤
      μ.real (brownianDriftedGridStripEvent B x (1/(T : ℝ)) 2 h N) := by
  let : IsProbabilityMeasure μ := hB.isGaussianProcess.isProbabilityMeasure
  apply (measureReal_drifted_strip_survival_small_ge hB hT hTs hx hxT).trans
  apply measureReal_mono (μ := μ)
  intro ω hω j hj
  exact hω ((j : ℝ≥0)*h) ((mul_le_mul_of_nonneg_right (by exact_mod_cast hj) (show (0 : ℝ≥0) ≤ h from bot_le)).trans hN)

/-- An initial positive increment buys a uniformly positive starting distance.
The continuation bound is integrated using actual Brownian independence. -/
theorem measureReal_brownian_random_start_grid_survival_ge (hB : IsBrownianReal B μ)
    {h T : ℝ≥0} (hh : 0 < h) (hT : 0 < T) (hTs : (T : ℝ) ≤ 1/32)
    (V : ℝ → ℝ) (hV : Measurable V) {v₀ : ℝ} (hv₀ : 0 ≤ v₀)
    (hVrange : ∀ z ∈ Icc (Real.sqrt (h : ℝ)) (2*Real.sqrt (h : ℝ)),
      v₀ ≤ V z ∧ V z ≤ (T : ℝ)/2)
    (N : ℕ) (hN : (N : ℝ≥0)*h ≤ T) :
    (Real.exp (-1)*(v₀/(T : ℝ))) * gaussianFirstPositivePass.toReal ≤
      μ.real {ω | B h ω ∈ Icc (Real.sqrt (h : ℝ)) (2*Real.sqrt (h : ℝ)) ∧
        ∀ j : ℕ, j ≤ N → V (B h ω) + (B (h+(j : ℝ≥0)*h) ω - B h ω) +
          (1/(T : ℝ))*(((j : ℝ≥0)*h) : ℝ) ∈ Icc 0 2} := by
  let : IsProbabilityMeasure μ := hB.isGaussianProcess.isProbabilityMeasure
  let A : Set ℝ := Icc (Real.sqrt (h : ℝ)) (2*Real.sqrt (h : ℝ))
  let E : Set (ℝ × (ℕ → ℝ)) := {p | p.1 ∈ A ∧ ∀ j : ℕ, j ≤ N →
    V p.1 + p.2 j + (1/(T : ℝ))*(((j : ℝ≥0)*h) : ℝ) ∈ Icc 0 2}
  have hE : MeasurableSet E := by
    apply (measurableSet_Icc.preimage measurable_fst).inter
    change MeasurableSet {p : ℝ × (ℕ → ℝ) | ∀ j : ℕ, j ≤ N →
      V p.1 + p.2 j + (1/(T : ℝ))*(((j : ℝ≥0)*h) : ℝ) ∈ Icc 0 2}
    have heq : {p : ℝ × (ℕ → ℝ) | ∀ j : ℕ, j ≤ N →
        V p.1 + p.2 j + (1/(T : ℝ))*(((j : ℝ≥0)*h) : ℝ) ∈ Icc 0 2} =
        ⋂ j : ℕ, ⋂ (_ : j ≤ N), {p : ℝ × (ℕ → ℝ) |
          V p.1 + p.2 j + (1/(T : ℝ))*(((j : ℝ≥0)*h) : ℝ) ∈ Icc 0 2} := by
      ext p
      simp
    rw [heq]
    apply MeasurableSet.iInter
    intro j
    apply MeasurableSet.iInter
    intro _
    exact measurableSet_Icc.preimage (((hV.comp measurable_fst).add
      ((measurable_pi_apply j).comp measurable_snd)).add_const _)
  let Y (ω : Ω) (j : ℕ) := B (h+(j : ℝ≥0)*h) ω - B h ω
  have hY : AEMeasurable Y μ := aemeasurable_pi_lambda _
    (fun j => (hB.aemeasurable _).sub (hB.aemeasurable h))
  have hs : ∀ z ∈ A, ENNReal.ofReal (Real.exp (-1)*(v₀/(T : ℝ))) ≤
      μ (Y ⁻¹' (Prod.mk z ⁻¹' E)) := by
    intro z hz
    have hr := hVrange z hz
    have hb := measureReal_brownian_grid_survival_small_ge (hB.shift h) hT hTs
      (hv₀.trans hr.1) hr.2 h N hN
    have hm : Real.exp (-1)*(v₀/(T : ℝ)) ≤
        μ.real (brownianDriftedGridStripEvent (fun t ω => B (h+t) ω-B h ω)
          (V z) (1/(T : ℝ)) 2 h N) :=
      (mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hr.1 T.coe_nonneg)
        (Real.exp_nonneg _)).trans hb
    have heq : Y ⁻¹' (Prod.mk z ⁻¹' E) =
        brownianDriftedGridStripEvent (fun t ω => B (h+t) ω-B h ω)
          (V z) (1/(T : ℝ)) 2 h N := by
      ext ω
      simp only [mem_preimage, E, mem_ofPred_eq, hz, true_and, Y,
        brownianDriftedGridStripEvent]
    rw [heq]
    exact ENNReal.ofReal_le_of_le_toReal hm
  have hb := IndepFun.measure_lower_of_sections (hB.aemeasurable h) hY
    (indepFun_brownian_first_gridFuture hB h) measurableSet_Icc hE hs
  have hp : μ ((B h) ⁻¹' A) = gaussianFirstPositivePass :=
    brownian_first_positive_pass_probability hB hh
  rw [hp] at hb
  have hr := ENNReal.toReal_mono (measure_ne_top μ _) hb
  have heq : ((fun ω => (B h ω, Y ω)) ⁻¹' E) =
      {ω | B h ω ∈ Icc (Real.sqrt (h : ℝ)) (2*Real.sqrt (h : ℝ)) ∧
        ∀ j : ℕ, j ≤ N → V (B h ω) + (B (h+(j : ℝ≥0)*h) ω - B h ω) +
          (1/(T : ℝ))*(((j : ℝ≥0)*h) : ℝ) ∈ Icc 0 2} := by
    ext ω
    rfl
  rw [heq] at hr
  simpa only [measureReal_def, ENNReal.toReal_mul, ENNReal.toReal_ofReal
    (mul_nonneg (Real.exp_nonneg _) (div_nonneg hv₀ T.coe_nonneg))] using hr

end BrownianAffine
