import PLAStochastic.Affine.Moments.Optimal.Spatial.KernelDerivatives
import PLAStochastic.Affine.Moments.Optimal.Spatial.Diagonal
import PLAStochastic.ForMathlib.Analysis.Calculus.CompactParameterIntegral

/-! # Actual spatial integration commutes with the moment recursion -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology
namespace BrownianAffine
set_option backward.isDefEq.respectTransparency false

def optimalSpatialSquare : Set (ℝ×ℝ) := Icc 0 1 ×ˢ Icc 0 1

theorem isCompact_optimalSpatialSquare : IsCompact optimalSpatialSquare := isCompact_Icc.prod isCompact_Icc

/-- Coordinates are ordered `(b,a)`, as in the displayed spatial integrals. -/
def weightedSpatialIntegral (F : ℝ → ℝ → ℝ) (h : ℝ) : ℝ :=
  ∫ p : ℝ×ℝ in optimalSpatialSquare, Real.cosh (h*(p.1-p.2))*F p.2 p.1

theorem weightedSpatialIntegral_eq_open {F : ℝ → ℝ → ℝ}
    (hF : Continuous (fun p : ℝ×ℝ => F p.1 p.2)) (h : ℝ) :
    weightedSpatialIntegral F h=
      ∫ b : ℝ in Ioo 0 1, ∫ a : ℝ in Ioo 0 1, Real.cosh (h*(b-a))*F a b := by
  have hc : Continuous (fun p : ℝ×ℝ => Real.cosh (h*(p.1-p.2))*F p.2 p.1) :=
    (by fun_prop : Continuous (fun p : ℝ×ℝ => Real.cosh (h*(p.1-p.2)))).mul
      (hF.comp continuous_swap)
  have hi := hc.continuousOn.integrableOn_compact (μ := (volume : Measure (ℝ×ℝ))) isCompact_optimalSpatialSquare
  unfold weightedSpatialIntegral optimalSpatialSquare
  change (∫ p : ℝ×ℝ in Icc 0 1 ×ˢ Icc 0 1, Real.cosh (h*(p.1-p.2))*F p.2 p.1
    ∂(volume : Measure ℝ).prod volume)=_
  rw [setIntegral_prod _ hi]
  simp_rw [integral_Icc_eq_integral_Ioc,integral_Ioc_eq_integral_Ioo]

/-- Compact domination supplies all interchange conditions; none is assumed as a law. -/
theorem hasDerivAt_weightedSpatialIntegral {F G : ℝ → ℝ → ℝ → ℝ}
    (hF : ∀ x, 0 < x → Continuous (fun p : ℝ×ℝ => F x p.1 p.2))
    (hG : ContinuousOn (fun p : ℝ×(ℝ×ℝ) => G p.1 p.2.1 p.2.2) (Ioi 0 ×ˢ Set.univ))
    (hd : ∀ x, 0 < x → ∀ a b, HasDerivAt (F · a b) (-x*G x a b) x)
    {x : ℝ} (hx : 0 < x) (h : ℝ) :
    HasDerivAt (fun k : ℝ => weightedSpatialIntegral (F k) h)
      (-x*weightedSpatialIntegral (G x) h) x := by
  let W : ℝ → (ℝ×ℝ) → ℝ := fun k p => Real.cosh (h*(p.1-p.2))*F k p.2 p.1
  let W' : ℝ → (ℝ×ℝ) → ℝ := fun k p => -k*(Real.cosh (h*(p.1-p.2))*G k p.2 p.1)
  have hw (k : ℝ) (hk : 0 < k) : Continuous (W k) :=
    (by fun_prop : Continuous (fun p : ℝ×ℝ => Real.cosh (h*(p.1-p.2)))).mul
      ((hF k hk).comp continuous_swap)
  have hc : ContinuousOn (fun p : ℝ×(ℝ×ℝ) => G p.1 p.2.2 p.2.1) (Ioi 0 ×ˢ Set.univ) := by
    apply hG.comp (by fun_prop : Continuous (fun p : ℝ×(ℝ×ℝ) => (p.1,(p.2.2,p.2.1)))).continuousOn
    intro p hp
    exact ⟨hp.1,Set.mem_univ _⟩
  have hw' : ContinuousOn (Function.uncurry W') (Ioi 0 ×ˢ optimalSpatialSquare) := by
    have hc' : Continuous (fun p : ℝ×(ℝ×ℝ) => Real.cosh (h*(p.2.1-p.2.2))) := by fun_prop
    exact (continuous_fst.neg.continuousOn.mul (hc'.continuousOn.mul hc)).mono
      (fun p hp => ⟨hp.1,Set.mem_univ _⟩)
  have hd' (k : ℝ) (hk : 0 < k) (p : ℝ×ℝ) (hp : p∈optimalSpatialSquare) :
      HasDerivAt (W · p) (W' k p) k := by
    convert! (hd k hk p.2 p.1).const_mul (Real.cosh (h*(p.1-p.2))) using 1
    dsimp only [W']
    ring
  have hdint := hasDerivAt_compactParameterIntegral (μ := (volume : Measure (ℝ×ℝ))) isCompact_optimalSpatialSquare hw hw' hd' hx
  convert! hdint using 1
  unfold weightedSpatialIntegral
  dsimp only [W']
  rw [integral_const_mul]

/-- The zeroth weighted kernel integral is exactly the manuscript's B₀. -/
theorem weightedSpatialIntegral_zero (k h : ℝ) :
    weightedSpatialIntegral (spatialLaplaceFormula0 k) h=optimalSpatialB 0 k h := by
  rw [weightedSpatialIntegral_eq_open (continuous_spatialLaplaceFormula0 k),optimalSpatialB,
    optimalSpatialGenerating_eq_open]
  simp_rw [spatialLaplaceFormula0_eq,optimalMomentLaplaceKernel]
  have he (a b : ℝ) : Real.cosh (h*(b-a))*
      (8*centeredCoth k/Real.sinh k^3*Real.sinh (k*(1-a))*Real.sinh (k*b))=
      (8*centeredCoth k/Real.sinh k^3)*
        (Real.cosh (h*(b-a))*Real.sinh (k*(1-a))*Real.sinh (k*b)) := by ring
  simp_rw [he,integral_const_mul]

/-- One actual compact integration step in the manuscript's differential recursion. -/
theorem weightedSpatialIntegral_step {F G : ℝ → ℝ → ℝ → ℝ} {n : ℕ} {h : ℝ}
    (hF : ∀ x, 0 < x → Continuous (fun p : ℝ×ℝ => F x p.1 p.2))
    (hG : ContinuousOn (fun p : ℝ×(ℝ×ℝ) => G p.1 p.2.1 p.2.2) (Ioi 0 ×ˢ Set.univ))
    (hd : ∀ x, 0 < x → ∀ a b, HasDerivAt (F · a b) (-x*G x a b) x)
    (heq : ∀ x, 0 < x → weightedSpatialIntegral (F x) h=optimalSpatialB n x h)
    {x : ℝ} (hx : 0 < x) :
    weightedSpatialIntegral (G x) h=optimalSpatialB (n+1) x h := by
  have hdiff := hasDerivAt_weightedSpatialIntegral hF hG hd hx h
  have he : (optimalSpatialB n · h) =ᶠ[𝓝 x] (fun k => weightedSpatialIntegral (F k) h) := by
    filter_upwards [Ioi_mem_nhds hx] with k hk
    exact (heq k hk).symm
  have hb := hdiff.congr_of_eventuallyEq he
  change weightedSpatialIntegral (G x) h = -deriv (optimalSpatialB n · h) x/x
  rw [hb.deriv]
  field_simp

theorem weightedSpatialIntegral_one {x : ℝ} (hx : 0 < x) (h : ℝ) :
    weightedSpatialIntegral (spatialLaplaceFormula1 x) h=optimalSpatialB 1 x h := by
  exact weightedSpatialIntegral_step
    (fun k _ => continuous_spatialLaplaceFormula0 k) continuousOn_spatialLaplaceFormula1
    (fun k hk a b => hasDerivAt_spatialLaplaceFormula0 hk.ne' a b)
    (fun k hk => weightedSpatialIntegral_zero k h) hx

theorem weightedSpatialIntegral_two {x : ℝ} (hx : 0 < x) (h : ℝ) :
    weightedSpatialIntegral (spatialLaplaceFormula2 x) h=optimalSpatialB 2 x h := by
  exact weightedSpatialIntegral_step
    (fun k _ => continuous_spatialLaplaceFormula1 k) continuousOn_spatialLaplaceFormula2
    (fun k hk a b => hasDerivAt_spatialLaplaceFormula1 hk.ne' a b)
    (fun k hk => weightedSpatialIntegral_one hk h) hx

theorem weightedSpatialIntegral_three {x : ℝ} (hx : 0 < x) (h : ℝ) :
    weightedSpatialIntegral (spatialLaplaceFormula3 x) h=optimalSpatialB 3 x h := by
  exact weightedSpatialIntegral_step
    (fun k _ => continuous_spatialLaplaceFormula2 k) continuousOn_spatialLaplaceFormula3
    (fun k hk a b => hasDerivAt_spatialLaplaceFormula2 hk.ne' a b)
    (fun k hk => weightedSpatialIntegral_two hk h) hx

/-- The actual double spatial integral equals the displayed L1. -/
theorem integral_spatialLaplaceFormula0_diagonal {k : ℝ} (hk : 0 < k) :
    (∫ b : ℝ in Ioo 0 1, ∫ a : ℝ in Ioo 0 1,
      Real.cosh (k*(b-a))*spatialLaplaceFormula0 k a b)=optimalRawIntegrandOne k := by
  rw [←weightedSpatialIntegral_eq_open (continuous_spatialLaplaceFormula0 k),
    weightedSpatialIntegral_zero k k,optimalSpatialB_zero_diagonal hk]

/-- The actual double spatial integral equals the displayed L2. -/
theorem integral_spatialLaplaceFormula1_diagonal {k : ℝ} (hk : 0 < k) :
    (∫ b : ℝ in Ioo 0 1, ∫ a : ℝ in Ioo 0 1,
      Real.cosh (k*(b-a))*spatialLaplaceFormula1 k a b)=optimalRawIntegrandTwo k := by
  rw [←weightedSpatialIntegral_eq_open (continuous_spatialLaplaceFormula1 k),
    weightedSpatialIntegral_one hk k,optimalSpatialB_one_diagonal hk]

/-- The actual double spatial integral equals the displayed L3. -/
theorem integral_spatialLaplaceFormula2_diagonal {k : ℝ} (hk : 0 < k) :
    (∫ b : ℝ in Ioo 0 1, ∫ a : ℝ in Ioo 0 1,
      Real.cosh (k*(b-a))*spatialLaplaceFormula2 k a b)=optimalRawIntegrandThree k := by
  rw [←weightedSpatialIntegral_eq_open (continuous_spatialLaplaceFormula2 k),
    weightedSpatialIntegral_two hk k,optimalSpatialB_two_diagonal hk]

/-- The actual double spatial integral equals the displayed L4. -/
theorem integral_spatialLaplaceFormula3_diagonal {k : ℝ} (hk : 0 < k) :
    (∫ b : ℝ in Ioo 0 1, ∫ a : ℝ in Ioo 0 1,
      Real.cosh (k*(b-a))*spatialLaplaceFormula3 k a b)=optimalRawIntegrandFour k := by
  rw [←weightedSpatialIntegral_eq_open (continuous_spatialLaplaceFormula3 k),
    weightedSpatialIntegral_three hk k,optimalSpatialB_three_diagonal hk]

end BrownianAffine
