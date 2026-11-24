import PLAStochastic.Index.CEPS.Scaled.ComplexJetHalfFactors
import PLAStochastic.Index.CEPS.Scaled.ComplexJetDependence
import PLAStochastic.ForMathlib.Analysis.Complex.ParametricMeasurability

/-! # Drift measurability of the complex finite-jet kernel factors

For an arbitrary complex jet vector, the finite-jet roots, the spatial unit, the removable
quotient and the spatial kernel are measurable in the drift, scale and frequency (jointly with
the spatial variable where they are functions of it). The moving slopes of the entire spatial
kernel are slopes of entire functions, hence pointwise limits of measurable difference quotients;
so the bridge, entrance, half bridge and half entrance are measurable in the drift with no
non-degeneracy assumption.
-/

noncomputable section
open Complex Set MeasureTheory
namespace PGM

theorem continuous_cepsCgfComplexJetPolynomial (p : ℕ → ℂ) (N : ℕ) :
    Continuous (cepsCgfComplexJetPolynomial p N) := by
  unfold cepsCgfComplexJetPolynomial
  fun_prop

theorem continuous_cepsCanonComplexJetPolynomial (p : ℕ → ℂ) (N : ℕ) :
    Continuous fun x : ℂ × ℂ × ℂ => cepsCanonComplexJetPolynomial p N x.1 x.2.1 x.2.2 := by
  unfold cepsCanonComplexJetPolynomial
  fun_prop

theorem continuous_quadraticExpUnit : Continuous fun x : ℂ × ℂ => quadraticExpUnit x.1 x.2 :=
  continuous_iff_continuousAt.2 fun x => (quadraticExpUnit_joint_analyticAt x).continuousAt

/-- Inner slopes of the spatial kernel are entire. -/
theorem cepsComplexKernelGJetModel_dslope_differentiable (p : ℕ → ℂ) (N : ℕ) (lam : ℝ)
    (z b c : ℂ) : Differentiable ℂ (dslope (cepsComplexKernelGJetModel p N lam z b) c) :=
  differentiable_dslope (cepsComplexKernelGJetModel_spatial_differentiable p N lam z b) c

variable {α : Type*} [MeasurableSpace α] {lam : α → ℝ} {z b : α → ℂ}

theorem measurable_cepsCanonComplexJetPolynomial_comp (p : ℕ → ℂ) (N : ℕ) {μ q ζ : α → ℂ}
    (hμ : Measurable μ) (hq : Measurable q) (hζ : Measurable ζ) :
    Measurable fun a => cepsCanonComplexJetPolynomial p N (μ a) (q a) (ζ a) := by
  have h := (continuous_cepsCanonComplexJetPolynomial p N).measurable.comp
    (hμ.prodMk (hq.prodMk hζ))
  simpa only [Function.comp_def] using h

theorem measurable_cepsComplexCumulantRootBase (p : ℕ → ℂ) (hlam : Measurable lam)
    (hz : Measurable z) (sign : ℂ) :
    Measurable fun a => cepsComplexCumulantRootBase p (lam a) (z a) sign := by
  have hl : Measurable fun a => ((lam a : ℝ) : ℂ) := Complex.measurable_ofReal.comp hlam
  unfold cepsComplexCumulantRootBase Complex.sqrt
  fun_prop

theorem measurable_cepsComplexCumulantRootGap (p : ℕ → ℂ) (hlam : Measurable lam)
    (hz : Measurable z) (sign : ℂ) :
    Measurable fun a => cepsComplexCumulantRootGap p (lam a) (z a) sign := by
  have hl : Measurable fun a => ((lam a : ℝ) : ℂ) := Complex.measurable_ofReal.comp hlam
  have hB := measurable_cepsComplexCumulantRootBase p hlam hz sign
  unfold cepsComplexCumulantRootGap
  fun_prop

theorem measurable_cepsComplexCumulantRootModel (p : ℕ → ℂ) (N : ℕ) (hlam : Measurable lam)
    (hz : Measurable z) (hb : Measurable b) (sign : ℂ) (k : ℕ) :
    Measurable fun a => cepsComplexCumulantRootModel p N (lam a) (z a) sign k (b a) := by
  induction k with
  | zero => exact measurable_cepsComplexCumulantRootBase p hlam hz sign
  | succ k ih =>
    have hl : Measurable fun a => ((lam a : ℝ) : ℂ) := Complex.measurable_ofReal.comp hlam
    have hP := (continuous_cepsCgfComplexJetPolynomial p N).measurable
    have hG := measurable_cepsComplexCumulantRootGap p hlam hz sign
    have hPg : Measurable fun a => cepsCgfComplexJetPolynomial p N
        (b a * cepsComplexCumulantRootModel p N (lam a) (z a) sign k (b a)) :=
      hP.comp (hb.mul ih)
    simp only [cepsComplexCumulantRootModel, quadraticNewtonStep]
    fun_prop

theorem measurable_uncurry_cepsComplexCumulantQuotientSpatialUnit (p : ℕ → ℂ) (N : ℕ)
    (hlam : Measurable lam) (hz : Measurable z) (hb : Measurable b) :
    Measurable (Function.uncurry fun a ξ =>
      cepsComplexCumulantQuotientSpatialUnit p N (lam a) (z a) (b a) ξ) := by
  have hl : Measurable fun x : α × ℂ => ((lam x.1 : ℝ) : ℂ) :=
    Complex.measurable_ofReal.comp (hlam.comp measurable_fst)
  have hz' : Measurable fun x : α × ℂ => z x.1 := hz.comp measurable_fst
  have hb' : Measurable fun x : α × ℂ => b x.1 := hb.comp measurable_fst
  have hP : Measurable fun x : α × ℂ => cepsCgfComplexJetPolynomial p N (b x.1 * x.2) :=
    (continuous_cepsCgfComplexJetPolynomial p N).measurable.comp (hb'.mul measurable_snd)
  have hT : Measurable fun x : α × ℂ =>
      cepsComplexCumulantQuadraticEquation p N (lam x.1) (z x.1) (b x.1) x.2 := by
    unfold cepsComplexCumulantQuadraticEquation
    fun_prop
  exact continuous_quadraticExpUnit.measurable.comp (hb'.prodMk hT)

theorem measurable_uncurry_cepsComplexCumulantJetQuotient (p : ℕ → ℂ) (N : ℕ)
    (hlam : Measurable lam) (hz : Measurable z) (hb : Measurable b) :
    Measurable (Function.uncurry fun a ξ =>
      cepsComplexCumulantJetQuotient p N (lam a) (z a) (b a) ξ) := by
  have hU := measurable_uncurry_cepsComplexCumulantQuotientSpatialUnit p N hlam hz hb
  have hd (a : α) := cepsComplexCumulantQuotientSpatialUnit_differentiable p N (lam a) (z a) (b a)
  have hP := measurable_cepsComplexCumulantRootModel p N hlam hz hb 1 N
  have hM := measurable_cepsComplexCumulantRootModel p N hlam hz hb (-1) N
  have h1 := measurable_uncurry_dslope_param hU hP fun a => hd a _
  exact measurable_uncurry_dslope_param h1 hM fun a => differentiable_dslope (hd a) _ _

theorem measurable_uncurry_cepsComplexKernelGJetModel (p : ℕ → ℂ) (N : ℕ)
    (hlam : Measurable lam) (hz : Measurable z) (hb : Measurable b) :
    Measurable (Function.uncurry fun a ξ =>
      cepsComplexKernelGJetModel p N (lam a) (z a) (b a) ξ) := by
  have hl : Measurable fun x : α × ℂ => ((lam x.1 : ℝ) : ℂ) :=
    Complex.measurable_ofReal.comp (hlam.comp measurable_fst)
  have hz' : Measurable fun x : α × ℂ => z x.1 := hz.comp measurable_fst
  have hb' : Measurable fun x : α × ℂ => b x.1 := hb.comp measurable_fst
  have hQ := measurable_uncurry_cepsComplexCumulantJetQuotient p N hlam hz hb
  have hC : Measurable fun x : α × ℂ => cepsCanonComplexJetPolynomial p N
      (b x.1 * (lam x.1 : ℂ)) (cepsComplexScaledDiscount (lam x.1) (z x.1) (b x.1))
        (b x.1 * x.2) := by
    refine measurable_cepsCanonComplexJetPolynomial_comp p N (hb'.mul hl) ?_ (hb'.mul measurable_snd)
    unfold cepsComplexScaledDiscount
    fun_prop
  have hQ' : Measurable fun x : α × ℂ =>
      cepsComplexCumulantJetQuotient p N (lam x.1) (z x.1) (b x.1) x.2 := hQ
  unfold cepsComplexKernelGJetModel
  fun_prop

theorem measurable_cepsComplexKernelGJetModel_comp (p : ℕ → ℂ) (N : ℕ)
    (hlam : Measurable lam) (hz : Measurable z) (hb : Measurable b) {ξ : α → ℂ}
    (hξ : Measurable ξ) :
    Measurable fun a => cepsComplexKernelGJetModel p N (lam a) (z a) (b a) (ξ a) :=
  (measurable_uncurry_cepsComplexKernelGJetModel p N hlam hz hb).comp (measurable_id.prodMk hξ)

theorem measurable_cepsComplexCumulantJetQuotient_comp (p : ℕ → ℂ) (N : ℕ)
    (hlam : Measurable lam) (hz : Measurable z) (hb : Measurable b) {ξ : α → ℂ}
    (hξ : Measurable ξ) :
    Measurable fun a => cepsComplexCumulantJetQuotient p N (lam a) (z a) (b a) (ξ a) :=
  (measurable_uncurry_cepsComplexCumulantJetQuotient p N hlam hz hb).comp (measurable_id.prodMk hξ)

/-- The first moving slope of the spatial kernel is jointly measurable. -/
theorem measurable_uncurry_cepsComplexKernelGJetModel_dslope (p : ℕ → ℂ) (N : ℕ)
    (hlam : Measurable lam) (hz : Measurable z) (hb : Measurable b) (sign : ℂ) :
    Measurable (Function.uncurry fun a => dslope (cepsComplexKernelGJetModel p N (lam a) (z a) (b a))
      (cepsComplexCumulantRootModel p N (lam a) (z a) sign N (b a))) :=
  measurable_uncurry_dslope_param (measurable_uncurry_cepsComplexKernelGJetModel p N hlam hz hb)
    (measurable_cepsComplexCumulantRootModel p N hlam hz hb sign N)
    fun _ => cepsComplexKernelGJetModel_spatial_differentiable p N _ _ _ _

theorem measurable_cepsComplexKernelDenominatorJetModel (p : ℕ → ℂ) (N : ℕ)
    (hlam : Measurable lam) (hz : Measurable z) (hb : Measurable b) :
    Measurable fun a => cepsComplexKernelDenominatorJetModel p N (lam a) (z a) (b a) :=
  measurable_dslope_param (measurable_uncurry_cepsComplexKernelGJetModel p N hlam hz hb)
    (measurable_cepsComplexCumulantRootModel p N hlam hz hb (-1) N)
    (measurable_cepsComplexCumulantRootModel p N hlam hz hb 1 N)
    fun _ => cepsComplexKernelGJetModel_spatial_differentiable p N _ _ _ _

theorem measurable_cepsComplexKernelEntranceSlopeJetModel (p : ℕ → ℂ) (N : ℕ)
    (hlam : Measurable lam) (hz : Measurable z) (hb : Measurable b) :
    Measurable fun a => cepsComplexKernelEntranceSlopeJetModel p N (lam a) (z a) (b a) :=
  measurable_dslope_param (measurable_uncurry_cepsComplexKernelGJetModel_dslope p N hlam hz hb (-1))
    (measurable_cepsComplexCumulantRootModel p N hlam hz hb 1 N) (hb.mul hz)
    fun _ => cepsComplexKernelGJetModel_dslope_differentiable p N _ _ _ _ _

theorem measurable_cepsComplexKernelBridgeJetModel (p : ℕ → ℂ) (N : ℕ)
    (hlam : Measurable lam) (hz : Measurable z) (hb : Measurable b) :
    Measurable fun a => cepsComplexKernelBridgeJetModel p N (lam a) (z a) (b a) := by
  have hGP := measurable_cepsComplexKernelGJetModel_comp p N hlam hz hb
    (measurable_cepsComplexCumulantRootModel p N hlam hz hb 1 N)
  have hGM := measurable_cepsComplexKernelGJetModel_comp p N hlam hz hb
    (measurable_cepsComplexCumulantRootModel p N hlam hz hb (-1) N)
  have hD := measurable_cepsComplexKernelDenominatorJetModel p N hlam hz hb
  unfold cepsComplexKernelBridgeJetModel
  fun_prop

theorem measurable_cepsComplexKernelEntranceJetModel (p : ℕ → ℂ) (N : ℕ)
    (hlam : Measurable lam) (hz : Measurable z) (hb : Measurable b) :
    Measurable fun a => cepsComplexKernelEntranceJetModel p N (lam a) (z a) (b a) := by
  have hl : Measurable fun a => ((lam a : ℝ) : ℂ) := Complex.measurable_ofReal.comp hlam
  have hC : Measurable fun a => cepsCanonComplexJetPolynomial p N (b a * (lam a : ℂ))
      (cepsComplexScaledDiscount (lam a) (z a) (b a)) (b a ^ 2 * z a) := by
    refine measurable_cepsCanonComplexJetPolynomial_comp p N (hb.mul hl) ?_ ((hb.pow_const 2).mul hz)
    unfold cepsComplexScaledDiscount
    fun_prop
  have hS := measurable_cepsComplexKernelEntranceSlopeJetModel p N hlam hz hb
  have hQ := measurable_cepsComplexCumulantJetQuotient_comp p N hlam hz hb (hb.mul hz)
  have hD := measurable_cepsComplexKernelDenominatorJetModel p N hlam hz hb
  unfold cepsComplexKernelEntranceJetModel
  fun_prop

theorem measurable_cepsComplexKernelHalfEntranceJetModel (p : ℕ → ℂ) (N : ℕ)
    (hlam : Measurable lam) (hz : Measurable z) (hb : Measurable b) :
    Measurable fun a => cepsComplexKernelHalfEntranceJetModel p N (lam a) (z a) (b a) := by
  have hl : Measurable fun a => ((lam a : ℝ) : ℂ) := Complex.measurable_ofReal.comp hlam
  have hC : Measurable fun a => cepsCanonComplexJetPolynomial p N (b a * (lam a : ℂ))
      (cepsComplexScaledDiscount (lam a) (z a) (b a)) (b a ^ 2 * z a) := by
    refine measurable_cepsCanonComplexJetPolynomial_comp p N (hb.mul hl) ?_ ((hb.pow_const 2).mul hz)
    unfold cepsComplexScaledDiscount
    fun_prop
  have hQ := measurable_cepsComplexCumulantJetQuotient_comp p N hlam hz hb (hb.mul hz)
  have hM := measurable_cepsComplexCumulantRootModel p N hlam hz hb (-1) N
  unfold cepsComplexKernelHalfEntranceJetModel
  fun_prop

theorem measurable_cepsComplexKernelHalfBridgeJetModel (p : ℕ → ℂ) (N : ℕ)
    (hlam : Measurable lam) (hz : Measurable z) (hb : Measurable b) :
    Measurable fun a => cepsComplexKernelHalfBridgeJetModel p N (lam a) (z a) (b a) := by
  have hP := measurable_cepsComplexCumulantRootModel p N hlam hz hb 1 N
  have hM := measurable_cepsComplexCumulantRootModel p N hlam hz hb (-1) N
  have hG := measurable_cepsComplexKernelGJetModel_comp p N hlam hz hb hP
  unfold cepsComplexKernelHalfBridgeJetModel
  fun_prop

/-! ### The drift alone, at fixed complex jets, frequency and scale -/

theorem cepsComplexKernelBridgeJetModel_measurable_drift (d N : ℕ) (q : Fin d → ℂ) (z h : ℂ) :
    Measurable fun lam : ℝ => cepsComplexKernelBridgeJetModel (cepsComplexJetPad d q) N lam z h :=
  measurable_cepsComplexKernelBridgeJetModel (cepsComplexJetPad d q) N measurable_id
    measurable_const measurable_const

theorem cepsComplexKernelEntranceJetModel_measurable_drift (d N : ℕ) (q : Fin d → ℂ) (z h : ℂ) :
    Measurable fun lam : ℝ => cepsComplexKernelEntranceJetModel (cepsComplexJetPad d q) N lam z h :=
  measurable_cepsComplexKernelEntranceJetModel (cepsComplexJetPad d q) N measurable_id
    measurable_const measurable_const

theorem cepsComplexKernelHalfBridgeJetModel_measurable_drift (d N : ℕ) (q : Fin d → ℂ)
    (z h : ℂ) :
    Measurable fun lam : ℝ =>
      cepsComplexKernelHalfBridgeJetModel (cepsComplexJetPad d q) N lam z h :=
  measurable_cepsComplexKernelHalfBridgeJetModel (cepsComplexJetPad d q) N measurable_id
    measurable_const measurable_const

theorem cepsComplexKernelHalfEntranceJetModel_measurable_drift (d N : ℕ) (q : Fin d → ℂ)
    (z h : ℂ) :
    Measurable fun lam : ℝ =>
      cepsComplexKernelHalfEntranceJetModel (cepsComplexJetPad d q) N lam z h :=
  measurable_cepsComplexKernelHalfEntranceJetModel (cepsComplexJetPad d q) N measurable_id
    measurable_const measurable_const

end PGM
