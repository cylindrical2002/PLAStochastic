import PLAStochastic.Brownian.Construction.CompactModification
import PLAStochastic.Brownian.Construction.PointwiseModification

/-! Construction of a continuous modification and a canonical Brownian probability space. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology Classical
namespace BrownianAffine
set_option backward.isDefEq.respectTransparency false

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

/-- The continuous limit is an actual modification, one fixed coordinate at a time. -/
theorem continuousPolygonModification_ae_eq (hB : IsPreBrownianReal B μ) (t : ℝ≥0) :
    continuousPolygonModification B t =ᵐ[μ] B t := by
  filter_upwards [preBrownian_polygon_tendsto_modification_ae hB,
    preBrownian_polygon_tendsto_coordinate_ae hB t] with ω hmod hcoord
  exact tendsto_nhds_unique (hmod t) hcoord

theorem isBrownianReal_continuousPolygonModification (hB : IsPreBrownianReal B μ) :
    IsBrownianReal (continuousPolygonModification B) μ where
  toIsPreBrownianReal := hB.congr (fun t => (continuousPolygonModification_ae_eq hB t).symm)
  cont := preBrownian_continuousPolygonModification_continuous_ae hB

/-- Fix the exceptional paths to zero so that every sample path is continuous. -/
def brownianContinuousVersion (B : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  if ∀ K : ℕ, CauchySeq (fun n => dyadicCompactPath B K n ω) then
    continuousPolygonModification B t ω else 0

omit [MeasurableSpace Ω] in
theorem continuous_brownianContinuousVersion (B : ℝ≥0 → Ω → ℝ) (ω : Ω) :
    Continuous (fun t => brownianContinuousVersion B t ω) := by
  by_cases h : ∀ K : ℕ, CauchySeq (fun n => dyadicCompactPath B K n ω)
  · simpa only [brownianContinuousVersion, if_pos h] using continuous_continuousPolygonModification B ω h
  · simpa only [brownianContinuousVersion, if_neg h] using (continuous_const : Continuous (fun _ : ℝ≥0 => (0 : ℝ)))

theorem brownianContinuousVersion_ae_eq (hB : IsPreBrownianReal B μ) (t : ℝ≥0) :
    brownianContinuousVersion B t =ᵐ[μ] B t := by
  filter_upwards [preBrownian_compactPaths_cauchy_ae hB, continuousPolygonModification_ae_eq hB t] with ω hω he
  simpa only [brownianContinuousVersion, if_pos hω] using he

/-- Every real pre-Brownian law admits the explicitly constructed continuous version. -/
theorem isBrownianReal_brownianContinuousVersion (hB : IsPreBrownianReal B μ) :
    IsBrownianReal (brownianContinuousVersion B) μ where
  toIsPreBrownianReal := hB.congr (fun t => (brownianContinuousVersion_ae_eq hB t).symm)
  cont := Eventually.of_forall (continuous_brownianContinuousVersion B)

/-- The canonical continuous Brownian process on the constructed projective probability space. -/
def canonicalBrownian : ℝ≥0 → (ℝ≥0 → ℝ) → ℝ := brownianContinuousVersion canonicalPreBrownian

theorem continuous_canonicalBrownian (ω : ℝ≥0 → ℝ) : Continuous (canonicalBrownian · ω) :=
  continuous_brownianContinuousVersion canonicalPreBrownian ω

/-- The actual existence theorem has no auxiliary Brownian-process hypothesis. -/
theorem isBrownianReal_canonicalBrownian : IsBrownianReal canonicalBrownian canonicalPreBrownianMeasure :=
  isBrownianReal_brownianContinuousVersion isPreBrownianReal_canonicalPreBrownian

theorem canonicalBrownian_ae_eq_coordinate (t : ℝ≥0) :
    canonicalBrownian t =ᵐ[canonicalPreBrownianMeasure] (fun ω => ω t) :=
  brownianContinuousVersion_ae_eq isPreBrownianReal_canonicalPreBrownian t

/-- A real Brownian probability space exists, with everywhere continuous sample paths. -/
theorem exists_continuous_brownian_probability_space :
    ∃ (P : Measure (ℝ≥0 → ℝ)) (W : ℝ≥0 → (ℝ≥0 → ℝ) → ℝ),
      IsProbabilityMeasure P ∧ IsBrownianReal W P ∧ ∀ ω, Continuous (W · ω) :=
  ⟨canonicalPreBrownianMeasure, canonicalBrownian, inferInstance,
    isBrownianReal_canonicalBrownian, continuous_canonicalBrownian⟩

end BrownianAffine
