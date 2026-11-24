import PLAStochastic.Index.GEP.Additive.UnconditionalHeight
import PLAStochastic.Index.GEP.LayerLaw.ActualLayers
import PLAStochastic.Index.GEP.LayerLaw.WeightedDistance
import PLAStochastic.Index.Algorithm.AffineInvariance
import PLAStochastic.Index.Algorithm.MeasurableEndpointHeight
import PLAStochastic.Index.CEPS.OrbitLimit
import Mathlib.Probability.Independence.InfinitePi

/-!
# Model G endpoint height with constants depending only on the gap law

* `H_G_EP_additive_law`: let `ν₀` be a law on `(0, ∞)` with the Model G moments
  (`L³`, mean `μ₀ > 0`, variance `σ₀² > 0`, centred absolute third moment at most `κ₀`).
  Then one pair `ε₀, K` serves every probability space, every iid sample `g` with
  marginal `ν₀` (each `g i` a.e. measurable) and every offset `x₀`:
  `|E H_EP - log n / log C_ε| ≤ K` for all `ε ≥ ε₀` and `n ≥ 2`.
  The constants are those of `H_G_EP_additive` on the canonical space `iidLaw ν₀`.  The
  height ignores the offset (translation invariance) and is a measurable function of the gap
  sequence, whose joint law is `iidLaw ν₀` by independence, so the expectation is the same on
  every sample space.
* `tendsto_log_lawC_expPM_orbit`: the limit defining `gepLogC` exists for all large `ε`:
  `log C_ε(Φ_ε^j Exp(1)) → gepLogC ε` as `j → ∞`.  This is the Exp(1) instance of
  `tendsto_log_lawC_orbit`.
-/

set_option autoImplicit false

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology

universe u

/-- **Existence of the compression limit.** For all sufficiently large `eps`, the orbit of the
Exp(1) reference law has `log C_ε(Φ_ε^j Exp(1)) → gepLogC eps`. -/
theorem tendsto_log_lawC_expPM_orbit :
    ∃ e0 : ℝ, ∀ eps, e0 ≤ eps →
      Tendsto (fun j : ℕ => Real.log (lawC eps ((lawPhi eps)^[j] expPM))) atTop
        (𝓝 (gepLogC eps)) := by
  obtain ⟨e0, h⟩ := tendsto_log_lawC_orbit one_pos one_pos one_pos le_rfl
  exact ⟨e0, fun eps heps => h eps heps expPM regLaw_expPM⟩

/-- **P-GEP, law form.** For a gap law `ν₀` on `(0, ∞)` with the Model G moments, the constants
`ε₀, K` of the additive endpoint height bound depend only on `ν₀`: the same pair serves every
probability space, every iid gap sample with marginal `ν₀` and every offset `x0`. -/
theorem H_G_EP_additive_law (ν₀ : ProbabilityMeasure ℝ) {μ₀ σ₀ κ₀ : ℝ}
    (h3 : MemLp id 3 (ν₀ : Measure ℝ)) (hmean : ∫ x, x ∂(ν₀ : Measure ℝ) = μ₀)
    (hvar : ∫ x, (x - μ₀) ^ 2 ∂(ν₀ : Measure ℝ) = σ₀ ^ 2)
    (hthird : ∫ x, |x - μ₀| ^ 3 ∂(ν₀ : Measure ℝ) ≤ κ₀) (hμ₀ : 0 < μ₀) (hσ₀ : 0 < σ₀)
    (hpos : (ν₀ : Measure ℝ) (Set.Ioi 0) = 1) :
    ∃ eps0 K : ℝ, ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) (g : ℕ → Ω → ℝ),
      (∀ i, HasLaw (g i) (ν₀ : Measure ℝ) P) → iIndepFun g P → ∀ x0 : Ω → ℝ,
      ∀ eps, eps0 ≤ eps → ∀ n : ℕ, 2 ≤ n →
        |∫ ω, (epHeight eps (fun t => x0 ω + gapKeys (seq g ω) t) n : ℝ) ∂P -
            Real.log n / Real.log (gepC eps)| ≤ K := by
  have hG : GapLaw (iidLaw ν₀) gapCoord μ₀ σ₀ κ₀ :=
    gapLaw_iidLaw h3 hmean hμ₀ (by rw [lawVar, lawMean, hmean]; exact hvar) hσ₀ hthird
  have hν₀pos : ∀ᵐ x ∂(ν₀ : Measure ℝ), 0 < x :=
    mem_ae_iff.mpr ((prob_compl_eq_zero_iff measurableSet_Ioi).mpr hpos)
  have hgpos : ∀ᵐ z ∂(iidLaw ν₀), 0 < gapCoord 0 z :=
    (measurePreserving_eval_infinitePi (fun _ : ℕ => (ν₀ : Measure ℝ)) 0).quasiMeasurePreserving.ae
      hν₀pos
  obtain ⟨eps0, K, hK⟩ := H_G_EP_additive hG hgpos (fun _ => 0)
  refine ⟨eps0, K, fun {Ω} _ P g hg hind x0 eps heps n hn => ?_⟩
  have hF : Measurable fun z : ℕ → ℝ => (epHeight eps (gapKeys z) n : ℝ) :=
    measurable_from_nat.comp ((measurable_epHeight eps n).comp measurable_gapKeys)
  have hlaw : HasLaw (fun ω i => g i ω) (iidLaw ν₀) P :=
    hind.hasLaw_infinitePi (μ := fun _ => (ν₀ : Measure ℝ)) hg
      (aemeasurable_pi_iff.2 fun i => (hg i).aemeasurable)
  have hshift (p : ℕ → ℝ) (c : ℝ) : epHeight eps (fun t => c + p t) n = epHeight eps p n := by
    have h := epHeight_affine (eps := eps) (p := p) (s := 1) (c := c) one_ne_zero n
    simp only [one_mul] at h
    rw [← h]
    congr 1
    funext t
    ring
  have hP : ∫ ω, (epHeight eps (fun t => x0 ω + gapKeys (seq g ω) t) n : ℝ) ∂P =
      ∫ z, (epHeight eps (gapKeys z) n : ℝ) ∂(iidLaw ν₀) := by
    rw [← hlaw.integral_comp hF.aestronglyMeasurable]
    congr 1
    funext ω
    simp only [Function.comp_apply, hshift]
    rfl
  have hQ : ∫ z, (epHeight eps (gapKeys z) n : ℝ) ∂(iidLaw ν₀) =
      ∫ z, (epHeight eps (fun t => (fun _ : ℕ → ℝ => (0 : ℝ)) z + gapKeys (seq gapCoord z) t) n
        : ℝ) ∂(iidLaw ν₀) := by
    congr 1
    funext z
    rw [hshift]
    rfl
  rw [hP, hQ]
  exact hK eps heps n hn

end

end PGM
