import PLAStochastic.Index.KEP.ReferenceScale.GammaRegularity
import PLAStochastic.Index.GEP.Kernel.Row.ClassUniform
import Mathlib.MeasureTheory.Measure.OpenPos

/-!
# Uniform killed-band data for the actual smooth reference density

The regular-law density representative need only be measurable. Its envelope
passes to the actual continuous Gamma representative by uniqueness of densities
and density of a full Lebesgue-measure set. Thus all pointwise kernel estimates
use the same representative as the proved classical derivatives.
-/

set_option autoImplicit false

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory Set

theorem kepReferenceDensity_envelope_of_regular {eps : ℝ}
    (heps : kepReferenceClassicalThreshold ≤ eps) {j : ℕ} (hj : 1 ≤ j)
    {D θ vlo vhi : ℝ} (hD : 0 < D) (hθ : 0 < θ)
    (hreg : RegLaw D θ vlo vhi (kepReferenceLaw eps j)) :
    (∀ x, (kepReferenceDensity heps hj).density x ≤ D) ∧
      ∀ x, (kepReferenceDensity heps hj).density x ≤ D * Real.exp (-θ * x) := by
  let p := kepReferenceDensity heps hj
  obtain ⟨g, hg, hg0, -, hgD, hge, hνg⟩ :=
    kr_regLaw_density (kepReferenceLaw eps j) hD hθ hreg
  have he : volume.withDensity (fun x => ENNReal.ofReal (p.density x)) =
      volume.withDensity (fun x => ENNReal.ofReal (g x)) := by
    change p.toMeasure = _
    rw [kepReferenceDensity_toMeasure heps hj, hνg]
  have hae := (withDensity_eq_iff_of_sigmaFinite
    p.measurable.ennreal_ofReal.aemeasurable hg.ennreal_ofReal.aemeasurable).mp he
  have hfg : p.density =ᵐ[volume] g := by
    filter_upwards [hae] with x hx
    have hh := congrArg ENNReal.toReal hx
    simpa only [ENNReal.toReal_ofReal (p.nonneg x), ENNReal.toReal_ofReal (hg0 x)] using hh
  have hc : Continuous p.density := continuous_iff_continuousAt.mpr
    fun x => ((kepReferenceDensity_classical heps hj).2.1 x).continuousAt
  have hDae : ∀ᵐ x ∂volume, p.density x ≤ D := by
    filter_upwards [hfg] with x hx
    rw [hx]
    exact hgD x
  have heae : ∀ᵐ x ∂volume, p.density x ≤ D * Real.exp (-θ * x) := by
    filter_upwards [hfg] with x hx
    rw [hx]
    exact hge x
  have hcD : IsClosed {x | p.density x ≤ D} := isClosed_le hc continuous_const
  have hce : IsClosed {x | p.density x ≤ D * Real.exp (-θ * x)} :=
    isClosed_le hc (continuous_const.mul ((continuous_const.mul continuous_id).rexp))
  have hDset : {x | p.density x ≤ D} = univ := by
    rw [← hcD.closure_eq]
    exact (Measure.dense_of_ae hDae).closure_eq
  have heset : {x | p.density x ≤ D * Real.exp (-θ * x)} = univ := by
    rw [← hce.closure_eq]
    exact (Measure.dense_of_ae heae).closure_eq
  constructor
  · intro x
    have hx : x ∈ {x | p.density x ≤ D} := by rw [hDset]; trivial
    exact hx
  · intro x
    have hx : x ∈ {x | p.density x ≤ D * Real.exp (-θ * x)} := by rw [heset]; trivial
    exact hx

/-- All class constants are selected before epsilon, the layer index and the
band. `A = w` covers the entire compact physical slope interval `[1/2, 2]`. -/
theorem kepReferenceBand_uniform :
    ∃ D θ vlo vhi K L eps0 : ℝ,
      0 < D ∧ 0 < θ ∧ 0 < vlo ∧ vlo ≤ vhi ∧ 0 < K ∧ 0 < L ∧
      kepReferenceClassicalThreshold ≤ eps0 ∧
      ∀ eps, eps0 ≤ eps → ∀ heps : kepReferenceClassicalThreshold ≤ eps,
        ∀ j, ∀ hj : 1 ≤ j,
        ∀ w a : ℝ, 1 ≤ w → 1 / 2 ≤ a → a ≤ 2 →
          KrBand D θ vlo vhi K L (kepReferenceLaw eps j)
            (kepReferenceDensity heps hj).density w w a 1 a ∧
          KrBand D θ vlo vhi K L (kepReferenceLaw eps j)
            (kepReferenceDensity heps hj).density w w a (-1) (-a) := by
  obtain ⟨D, θ, vlo, vhi, e0, hD, hθ, hvlo, hvhi, hreg⟩ := kepReferenceLaw_regular
  obtain ⟨K, hK, hLS⟩ := krLinearSurvival_exists D θ vlo vhi hD hθ hvlo hvhi
  obtain ⟨L, hFree⟩ := krFreeBound_exists D θ vlo vhi hD hθ hvlo hvhi
  refine ⟨D, θ, vlo, vhi, K, L, max kepReferenceClassicalThreshold e0,
    hD, hθ, hvlo, hvhi, hK, hFree.1, le_max_left _ _, ?_⟩
  intro eps he heps j hj w a hw ha ha2
  have hr := hreg eps ((le_max_right _ _).trans he) j
  have hp := kepReferenceDensity_envelope_of_regular heps hj hD hθ hr
  have hc := kepReferenceDensity_classical heps hj
  have ha0 : 0 ≤ a := by linarith
  have haA : |a - 1| ≤ w / w := by
    rw [div_self (by linarith : w ≠ 0), abs_le]
    constructor <;> linarith
  have hν : (kepReferenceLaw eps j : Measure ℝ) = volume.withDensity
      (fun x => ENNReal.ofReal ((kepReferenceDensity heps hj).density x)) := by
    rw [← kepReferenceDensity_toMeasure heps hj]
    rfl
  have H : KrBand D θ vlo vhi K L (kepReferenceLaw eps j)
      (kepReferenceDensity heps hj).density w w a 1 a :=
    { hD := hD, hθ := hθ, hvlo := hvlo, hvhi := hvhi, hLS := hLS, hFree := hFree,
      hν := hr, hK := hK.le, hf := (kepReferenceDensity heps hj).measurable,
      hf0 := (kepReferenceDensity heps hj).nonneg, hfz := hc.1, hfD := hp.1, hfe := hp.2,
      hνf := hν, hw := hw, hA := by linarith, haA := haA,
      ha₁ := by rwa [abs_of_nonneg ha0], ha₂ := by rwa [abs_of_nonneg ha0],
      hβ := Or.inl ⟨rfl, rfl⟩ }
  exact ⟨H, H.rev⟩

end

end PGM
