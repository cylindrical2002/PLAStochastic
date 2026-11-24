import PLAStochastic.Affine.Sampled.MeshError
import PLAStochastic.Affine.Lifetime.BrownianProcess

/-!
# Measurable actual sampled Brownian lifetimes

The finite-grid fitting error is measurable through its actual finite vector
of Brownian observations. The lifetime is reduced to a countable infimum over
the actual grid, without imposing continuity on its stepwise error process.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology

namespace BrownianAffine

theorem finiteMeshAnchoredError_eq_of_floor_eq (f : C(ℝ, ℝ)) {S T h : ℝ}
    (hST : ⌊S / h⌋₊ = ⌊T / h⌋₊) :
    finiteMeshAnchoredError f S h = finiteMeshAnchoredError f T h := by
  unfold finiteMeshAnchoredError meshAnchoredSubspace meshValues meshTimes MeshIndex
  rw [hST]

/-- The finite-grid error at a horizon is exactly its value at the last observed grid point. -/
theorem finiteMeshAnchoredError_at_last_sample (f : C(ℝ, ℝ))
    (T h : ℝ≥0) (hh : h ≠ 0) :
    finiteMeshAnchoredError f ((⌊(T : ℝ) / h⌋₊ : ℝ≥0) * h) h =
      finiteMeshAnchoredError f T h := by
  apply finiteMeshAnchoredError_eq_of_floor_eq
  have hh' : (h : ℝ) ≠ 0 := by exact_mod_cast hh
  simp only [NNReal.coe_natCast, mul_div_cancel_right₀ _ hh', Nat.floor_natCast]

/-- Exact countable representation of the actual first infeasible grid time. -/
theorem finiteMeshAnchoredLifetime_eq_iInf (f : C(ℝ, ℝ)) (h : ℝ≥0) (hh : h ≠ 0) (ε : ℝ) :
    finiteMeshAnchoredLifetime f h ε =
      ⨅ n : ℕ, if ε < finiteMeshAnchoredError f ((n : ℝ≥0) * h) h
        then (((n : ℝ≥0) * h : ℝ≥0) : ℝ≥0∞) else ⊤ := by
  have hhpos : 0 < (h : ℝ) := by exact_mod_cast (pos_of_ne_zero hh)
  apply le_antisymm
  · apply le_iInf
    intro n
    split_ifs with hn
    · exact firstExceedance_le_of_exceeds hn
    · exact le_top
  · unfold finiteMeshAnchoredLifetime firstExceedance
    apply le_iInf
    intro T
    split_ifs with hT
    · let n : ℕ := ⌊(T : ℝ) / h⌋₊
      have hn : ε < finiteMeshAnchoredError f ((n : ℝ≥0) * h) h := by
        rw [finiteMeshAnchoredError_at_last_sample f T h hh]
        exact hT
      apply (iInf_le _ n).trans
      rw [if_pos hn]
      exact_mod_cast meshFloor_mul_le T.coe_nonneg hhpos
    · exact le_top

def finiteMeshProcessError {Ω : Type*} (B : ℝ≥0 → Ω → ℝ)
    (T h : ℝ≥0) (ω : Ω) : ℝ := finiteMeshAnchoredError (processPath B ω) T h

def finiteMeshProcessLifetime {Ω : Type*} (B : ℝ≥0 → Ω → ℝ)
    (h : ℝ≥0) (ε : ℝ) (ω : Ω) : ℝ≥0∞ :=
  finiteMeshAnchoredLifetime (processPath B ω) h ε

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

/-- No continuous-path-space measurability is assumed: only the finite observations are used. -/
theorem aemeasurable_finiteMeshProcessError (hB : IsBrownianReal B μ) (T h : ℝ≥0) :
    AEMeasurable (finiteMeshProcessError B T h) μ := by
  let t : MeshIndex T h → ℝ≥0 := fun i =>
    ⟨meshTimes T h i, mul_nonneg (Nat.cast_nonneg _) h.coe_nonneg⟩
  have hv : AEMeasurable (fun ω (i : MeshIndex T h) => B (t i) ω) μ :=
    aemeasurable_pi_lambda _ (fun i => hB.aemeasurable (t i))
  have he := (bestError_lipschitz (meshAnchoredSubspace T h)).continuous.measurable.comp_aemeasurable hv
  apply he.congr
  filter_upwards [hB.cont] with ω hω
  apply congrArg (bestError (meshAnchoredSubspace T h))
  funext i
  exact (processPath_apply_of_continuous hω (t i)).symm

/-- The first infeasible sampled time is a.e. measurable, despite its discontinuous error process. -/
theorem aemeasurable_finiteMeshProcessLifetime (hB : IsBrownianReal B μ)
    (h : ℝ≥0) (hh : h ≠ 0) (ε : ℝ) :
    AEMeasurable (finiteMeshProcessLifetime B h ε) μ := by
  have hi (n : ℕ) : AEMeasurable (fun ω =>
      if ε < finiteMeshProcessError B ((n : ℝ≥0) * h) h ω
      then (((n : ℝ≥0) * h : ℝ≥0) : ℝ≥0∞) else ⊤) μ := by
    exact (Measurable.ite (measurableSet_lt measurable_const measurable_id)
      measurable_const measurable_const).comp_aemeasurable
      (aemeasurable_finiteMeshProcessError hB ((n : ℝ≥0) * h) h)
  have hm := AEMeasurable.iInf hi
  convert hm using 1
  funext ω
  exact finiteMeshAnchoredLifetime_eq_iInf (processPath B ω) h hh ε

omit [MeasurableSpace Ω] in
/-- Deterministic mesh convergence applies to every continuous representative simultaneously. -/
theorem finiteMeshProcessLifetime_tendsto (ε : ℝ)
    {ι : Type*} {l : Filter ι} {h : ι → ℝ≥0}
    (hh : ∀ i, h i ≠ 0) (hconv : Tendsto (fun i => (h i : ℝ)) l (𝓝 0)) (ω : Ω) :
    Tendsto (fun i => finiteMeshProcessLifetime B (h i) ε ω) l
      (𝓝 (anchoredProcessLifetime B ε ω)) :=
  tendsto_finiteMeshAnchoredLifetime (processPath B ω) ε
    (fun i => by exact_mod_cast (pos_of_ne_zero (hh i))) hconv

end BrownianAffine
