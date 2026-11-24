import PLAStochastic.Index.Model.IIDGaps
import PLAStochastic.ForMathlib.Probability.StoppedSum.PredictableWeights

/-!
# Setting for the one-layer segment-length bounds

`GapLaw P X μ σ κ`: the gaps `X t` are iid with mean `μ > 0`, variance `σ^2 > 0`
and centred absolute third moment at most `κ`.  `layerSegLen eps X ω` is the
number of keys in the first ALG-OPT segment of the walk with these gaps.
-/

namespace PGM

open MeasureTheory ProbabilityTheory Finset

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

/-- iid gaps with the three moment parameters used by the one-layer bounds. -/
structure GapLaw (P : Measure Ω) (X : ℕ → Ω → ℝ) (μ σ κ : ℝ) : Prop where
  iid : IIDSeq P X
  memLp3 : MemLp (X 0) 3 P
  mean : ∫ ω, X 0 ω ∂P = μ
  var : ∫ ω, (X 0 ω - μ) ^ 2 ∂P = σ ^ 2
  third : ∫ ω, |X 0 ω - μ| ^ 3 ∂P ≤ κ
  mu_pos : 0 < μ
  sigma_pos : 0 < σ

/-- Number of keys in the first ALG-OPT segment of the layer. -/
noncomputable def layerSegLen (eps : ℝ) (X : ℕ → Ω → ℝ) (ω : Ω) : ℕ∞ :=
  gapSegLen eps (seq X ω)

/-- Centred gaps. -/
def centred (X : ℕ → Ω → ℝ) (μ : ℝ) : ℕ → Ω → ℝ := fun t ω => X t ω - μ

omit mΩ in
theorem gapKeys_eq_centred (X : ℕ → Ω → ℝ) (μ : ℝ) (ω : Ω) (k : ℕ) :
    gapKeys (seq X ω) k = k * μ + partialSum (centred X μ) k ω := by
  simp only [gapKeys, seq, partialSum, centred, sum_sub_distrib, sum_const, card_range,
    nsmul_eq_mul]
  ring

namespace GapLaw

variable {P : Measure Ω} {X : ℕ → Ω → ℝ} {μ σ κ : ℝ}

theorem memLp_three (h : GapLaw P X μ σ κ) (t : ℕ) : MemLp (X t) 3 P :=
  (h.iid.memLp_iff t).2 h.memLp3

theorem memLp_centred (h : GapLaw P X μ σ κ) [IsProbabilityMeasure P] (t : ℕ) :
    MemLp (centred X μ t) 3 P :=
  (h.memLp_three t).sub (memLp_const μ)

theorem integral_centred (h : GapLaw P X μ σ κ) [IsProbabilityMeasure P] (t : ℕ) :
    ∫ ω, centred X μ t ω ∂P = 0 := by
  simp only [centred]
  rw [integral_sub ((h.memLp_three t).integrable (by norm_num)) (integrable_const μ),
    h.iid.integral_eq t, h.mean]
  simp

theorem integral_centred_sq (h : GapLaw P X μ σ κ) (t : ℕ) :
    ∫ ω, centred X μ t ω ^ 2 ∂P = σ ^ 2 := by
  simp only [centred]; rw [h.iid.integral_sq_sub_eq t μ, h.var]

theorem integral_centred_abs_cube (h : GapLaw P X μ σ κ) (t : ℕ) :
    ∫ ω, |centred X μ t ω| ^ 3 ∂P ≤ κ := by
  simp only [centred]; rw [h.iid.integral_abs_sub_pow_three_eq t μ]; exact h.third

theorem indepIncrements (h : GapLaw P X μ σ κ) :
    IndepIncrements P (gapFiltration X h.iid.measurable) (centred X μ) :=
  h.iid.indepIncrements μ

/-- The gaps seen from index `m` on have the same law parameters. -/
theorem shift (h : GapLaw P X μ σ κ) (m : ℕ) : GapLaw P (fun t => X (m + t)) μ σ κ where
  iid := h.iid.shift m
  memLp3 := by simpa using h.memLp_three m
  mean := by simp only [add_zero]; rw [h.iid.integral_eq m, h.mean]
  var := by simp only [add_zero]; rw [h.iid.integral_sq_sub_eq m μ, h.var]
  third := by simp only [add_zero]; rw [h.iid.integral_abs_sub_pow_three_eq m μ]; exact h.third
  mu_pos := h.mu_pos
  sigma_pos := h.sigma_pos

theorem kappa_nonneg (h : GapLaw P X μ σ κ) : 0 ≤ κ :=
  le_trans (integral_nonneg fun _ => by positivity) h.third

end GapLaw

end PGM
