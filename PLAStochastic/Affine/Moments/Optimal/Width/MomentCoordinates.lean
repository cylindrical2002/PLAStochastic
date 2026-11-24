import PLAStochastic.Affine.Moments.Optimal.Width.ExtremaWeight
import PLAStochastic.Affine.Extrema.Contact.Coordinates
import Mathlib.MeasureTheory.Group.Prod

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal
namespace BrownianAffine
set_option backward.isDefEq.respectTransparency false

/-- Width, initial point, first-contact time, time gap, and translated endpoint. -/
def optimalMomentCoordinates (p : ExtremaVector) : ExtremaVector :=
  (-p.2.1,p.1-p.2.1,p.2.2.1,p.2.2.1+p.2.2.2.1,p.2.2.2.2-p.2.1)

theorem continuous_optimalMomentCoordinates : Continuous optimalMomentCoordinates := by
  unfold optimalMomentCoordinates
  fun_prop

theorem optimalMomentCoordinates_injective : Function.Injective optimalMomentCoordinates := by
  intro p q h
  have h1 := congrArg (fun p : ExtremaVector => p.1) h
  have h2 := congrArg (fun p : ExtremaVector => p.2.1) h
  have h3 := congrArg (fun p : ExtremaVector => p.2.2.1) h
  have h4 := congrArg (fun p : ExtremaVector => p.2.2.2.1) h
  have h5 := congrArg (fun p : ExtremaVector => p.2.2.2.2) h
  dsimp only [optimalMomentCoordinates] at h1 h2 h3 h4 h5
  apply Prod.ext (by linarith)
  apply Prod.ext (by linarith)
  apply Prod.ext h3
  exact Prod.ext (by linarith) (by linarith)

private theorem measurePreserving_optimalLevelCoordinates :
    MeasurePreserving (fun p : ℝ × ℝ => (-p.2,p.1-p.2)) volume volume := by
  have h := (Measure.measurePreserving_neg (volume : Measure ℝ)).prod
    (MeasurePreserving.id (volume : Measure ℝ))
  exact h.comp (measurePreserving_prod_sub_swap volume volume)

/-- The physical five-variable transformation has unit Lebesgue Jacobian. -/
theorem lintegral_optimalMomentCoordinates {F : ExtremaVector → ℝ≥0∞} (hF : Measurable F) :
    (∫⁻ p : ExtremaVector, F (optimalMomentCoordinates p))=∫⁻ p, F p := by
  let G : (ℝ × ℝ) → ℝ≥0∞ := fun q => ∫⁻ p : ℝ × ℝ × ℝ,
    F (q.1,q.2,p.1,p.1+p.2.1,p.2.2+q.1)
  have hG : Measurable G := (hF.comp (f := fun p : (ℝ × ℝ) × (ℝ × ℝ × ℝ) =>
    (p.1.1,p.1.2,p.2.1,p.2.1+p.2.2.1,p.2.2.2+p.1.1)) (by fun_prop)).lintegral_prod_right'
  have hL := measurePreserving_optimalLevelCoordinates.lintegral_comp hG
  have hH : Measurable (fun p : ExtremaVector => F (optimalMomentCoordinates p)) :=
    hF.comp continuous_optimalMomentCoordinates.measurable
  change (∫⁻ p, F (optimalMomentCoordinates p) ∂volume.prod volume)=_
  rw [lintegral_prod _ hH.aemeasurable]
  have he (r : ℝ) : (∫⁻ p : ℝ × ℝ × ℝ × ℝ, F (optimalMomentCoordinates (r,p)))=
      ∫⁻ x : ℝ, G (-x,r-x) := by
    have hm : Measurable (fun p : ℝ × ℝ × ℝ × ℝ => F (optimalMomentCoordinates (r,p))) :=
      hH.comp (by fun_prop)
    rw [show (volume : Measure (ℝ × ℝ × ℝ × ℝ))=volume.prod volume from rfl,
      lintegral_prod _ hm.aemeasurable]
    rfl
  simp only [he]
  have hm : Measurable (fun p : ℝ × ℝ => G (-p.2,p.1-p.2)) :=
    hG.comp measurePreserving_optimalLevelCoordinates.measurable
  rw [←lintegral_prod _ hm.aemeasurable]
  change (∫⁻ p : ℝ × ℝ, G (-p.2,p.1-p.2))=_
  rw [hL]
  exact lintegral_orderedContactCoordinates hF

theorem measurePreserving_optimalMomentCoordinates :
    MeasurePreserving optimalMomentCoordinates volume volume := by
  refine ⟨continuous_optimalMomentCoordinates.measurable,?_⟩
  apply Measure.ext
  intro S hS
  rw [Measure.map_apply continuous_optimalMomentCoordinates.measurable hS,
    ←lintegral_indicator_one (hS.preimage continuous_optimalMomentCoordinates.measurable),
    ←lintegral_indicator_one hS]
  have h := lintegral_optimalMomentCoordinates ((measurable_const (a := (1 : ℝ≥0∞))).indicator hS)
  convert! h using 1

/-- The transformed domain retains both positive space coordinates and a positive time simplex. -/
def optimalMomentDomain : Set ExtremaVector :=
  {p | 0<p.1 ∧ p.2.1∈Ioo 0 p.1 ∧ p.2.2.2.2∈Ioo 0 p.1 ∧
    0<p.2.2.1 ∧ 0<p.2.2.2.1 ∧ p.2.2.1+p.2.2.2.1<1}

theorem optimalMomentCoordinates_preimage_ordered :
    optimalMomentCoordinates ⁻¹' orderedExtremaDomain=optimalMomentDomain := by
  ext p
  simp only [mem_preimage,orderedExtremaDomain,optimalMomentDomain,optimalMomentCoordinates,
    mem_ofPred_eq,mem_Ioo]
  constructor
  · rintro ⟨h1,h2,h3,h4,h5,h6,h7⟩
    exact ⟨by linarith,⟨by linarith,by linarith⟩,⟨by linarith,by linarith⟩,
      h5,by linarith,h7⟩
  · rintro ⟨h1,⟨h2,h3⟩,⟨h4,h5⟩,h6,h7,h8⟩
    exact ⟨by linarith,by linarith,by linarith,by linarith,h6,by linarith,h8⟩

theorem measurableSet_optimalMomentDomain : MeasurableSet optimalMomentDomain := by
  rw [←optimalMomentCoordinates_preimage_ordered]
  exact measurableSet_orderedExtremaDomain.preimage continuous_optimalMomentCoordinates.measurable

/-- All real test integrals admit the same unit-Jacobian spatial/time transformation. -/
theorem integral_orderedExtrema_coordinates (F : ExtremaVector → ℝ) :
    (∫ p in orderedExtremaDomain, F p)=
      ∫ p in optimalMomentDomain, F (optimalMomentCoordinates p) := by
  have h := measurePreserving_optimalMomentCoordinates.setIntegral_preimage_emb
    (continuous_optimalMomentCoordinates.measurableEmbedding optimalMomentCoordinates_injective)
    F orderedExtremaDomain
  rw [optimalMomentCoordinates_preimage_ordered] at h
  exact h.symm

/-- The genuine positive boundary kernel after width and lag coordinates. -/
def optimalMomentPhysicalIntegrand (q : ℝ) (p : ExtremaVector) : ℝ :=
  Real.exp ((p.2.2.2.2-p.2.1)^2/2) / p.1^(2*q+1) * p.2.2.2.1 *
    heatBoundaryLeft p.1 p.2.2.1 p.2.1 * heatCrossBoundary p.1 p.2.2.2.1 *
    heatBoundaryRight p.1 (1-p.2.2.1-p.2.2.2.1) p.2.2.2.2

theorem optimalMomentPhysicalIntegrand_eq (q : ℝ) {p : ExtremaVector} (hp : p∈optimalMomentDomain) :
    orderedExtremaDensity (optimalMomentCoordinates p) *
      optimalExtremaMomentWeight q (optimalMomentCoordinates p)=optimalMomentPhysicalIntegrand q p/4 := by
  unfold orderedExtremaDensity orderedContactDensityKernel optimalExtremaMomentWeight
    optimalMomentCoordinates optimalMomentPhysicalIntegrand
  simp only [sub_neg_eq_add,neg_neg]
  rw [show p.1-p.2.1+p.2.1=p.1 by ring,
    show p.2.2.1+p.2.2.2.1-p.2.2.1=p.2.2.2.1 by ring,
    show p.2.2.2.2-p.2.1+p.2.1=p.2.2.2.2 by ring,abs_of_pos hp.2.2.2.2.1]
  ring

/-- The manuscript's five-dimensional moment integral follows from the actual law,
not from an assumed ordered-density formula. -/
theorem optimalUnitLifetime_moment_physical_density {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B μ)
    {q : ℝ} (hq : 0<q) :
    (∫ ω, optimalUnitLifetime B ω^q ∂μ)=
      (2:ℝ)^(2*q)*q*Real.sqrt (2*Real.pi)/2 *
        ∫ p in optimalMomentDomain, optimalMomentPhysicalIntegrand q p := by
  rw [optimalUnitLifetime_moment_ordered_density hB hq,
    integral_orderedExtrema_coordinates]
  have he : (∫ p in optimalMomentDomain, orderedExtremaDensity (optimalMomentCoordinates p)*
      optimalExtremaMomentWeight q (optimalMomentCoordinates p))=
      (∫ p in optimalMomentDomain, optimalMomentPhysicalIntegrand q p)/4 := by
    rw [←integral_div]
    exact setIntegral_congr_fun measurableSet_optimalMomentDomain (fun p hp => optimalMomentPhysicalIntegrand_eq q hp)
  rw [he]
  ring

end BrownianAffine
