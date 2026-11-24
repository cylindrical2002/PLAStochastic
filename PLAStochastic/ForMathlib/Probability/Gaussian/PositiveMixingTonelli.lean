import PLAStochastic.ForMathlib.Probability.Gaussian.CoshLaplaceMixture

/-! # Positive Gaussian mixing without an a priori finiteness assumption -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ENNReal
namespace BrownianAffine
set_option backward.isDefEq.respectTransparency false

theorem integrable_gaussianMomentKernel (n : ℕ) (d : ℝ) {T : ℝ} (hT : 0 < T) :
    IntegrableOn (fun k : ℝ => Real.cosh (d*k)*(T^n*Real.exp (-(k^2/2)*T))) (Ioi 0) volume := by
  have he : (fun k : ℝ => Real.cosh (d*k)*(T^n*Real.exp (-(k^2/2)*T)))=
      fun k : ℝ => T^n*(Real.cosh (d*k)*Real.exp (-T*k^2/2)) := by
    funext k
    rw [show -(k^2/2)*T=-T*k^2/2 by ring]
    ring
  rw [he]
  exact (integrable_coshGaussian hT d).integrableOn.const_mul (T^n)

theorem gaussianMomentKernel_integral (n : ℕ) (d : ℝ) {T : ℝ} (hT : 0 < T) :
    T^((n:ℝ)-1/2)*Real.exp (d^2/(2*T))=
      Real.sqrt (2/Real.pi)*∫ k : ℝ in Ioi 0, Real.cosh (d*k)*(T^n*Real.exp (-(k^2/2)*T)) := by
  have he (k : ℝ) : Real.cosh (d*k)*(T^n*Real.exp (-(k^2/2)*T))=
      T^n*(Real.cosh (d*k)*Real.exp (-T*k^2/2)) := by
    rw [show -(k^2/2)*T=-T*k^2/2 by ring]
    ring
  simp_rw [he]
  rw [integral_const_mul,integral_coshGaussian_Ioi hT d]
  have hs : Real.sqrt (2/Real.pi)*Real.sqrt (Real.pi/(2*T))=1/Real.sqrt T := by
    rw [←Real.sqrt_mul (by positivity : 0 ≤ 2/Real.pi),
      show (2/Real.pi)*(Real.pi/(2*T))=1/T by field_simp,
      Real.sqrt_div (by norm_num : (0:ℝ) ≤ 1),Real.sqrt_one]
  rw [Real.rpow_sub hT,Real.rpow_natCast,←Real.sqrt_eq_rpow]
  calc
    _ = T^n*((1/Real.sqrt T)*Real.exp (d^2/(2*T))) := by ring
    _ = _ := by rw [←hs]; ring

theorem gaussianMomentKernel_lintegral (n : ℕ) (d : ℝ) {T : ℝ} (hT : 0 < T) :
    ENNReal.ofReal (T^((n:ℝ)-1/2)*Real.exp (d^2/(2*T)))=
      ENNReal.ofReal (Real.sqrt (2/Real.pi))*
        ∫⁻ k : ℝ in Ioi 0, ENNReal.ofReal (Real.cosh (d*k))*
          ENNReal.ofReal (T^n*Real.exp (-(k^2/2)*T)) := by
  rw [gaussianMomentKernel_integral n d hT,ENNReal.ofReal_mul (Real.sqrt_nonneg _),
    ofReal_integral_eq_lintegral_ofReal (integrable_gaussianMomentKernel n d hT)
      (Eventually.of_forall fun k => by have := Real.cosh_pos (d*k); positivity)]
  simp_rw [ENNReal.ofReal_mul (Real.cosh_pos _).le]

/-- The Gaussian identity and genuine Tonelli apply even when either side is infinite. -/
theorem gaussianLaplaceTonelli (n : ℕ) (d : ℝ) {G : ℝ → ℝ≥0∞} (hG : Measurable G) :
    (∫⁻ T : ℝ in Ioi 0, ENNReal.ofReal (T^((n:ℝ)-1/2)*Real.exp (d^2/(2*T)))*G T)=
      ENNReal.ofReal (Real.sqrt (2/Real.pi))*
        ∫⁻ k : ℝ in Ioi 0, ENNReal.ofReal (Real.cosh (d*k))*
          ∫⁻ T : ℝ in Ioi 0, ENNReal.ofReal (T^n*Real.exp (-(k^2/2)*T))*G T := by
  let H : ℝ → ℝ → ℝ≥0∞ := fun k T =>
    ENNReal.ofReal (Real.cosh (d*k))*ENNReal.ofReal (T^n*Real.exp (-(k^2/2)*T))
  have hm (T : ℝ) : Measurable (H · T) := by unfold H; fun_prop
  have hj : Measurable (fun p : ℝ×ℝ => H p.2 p.1*G p.1) := by
    exact (by unfold H; fun_prop : Measurable (fun p : ℝ×ℝ => H p.2 p.1)).mul
      (hG.comp measurable_fst)
  calc
    _ = ∫⁻ T : ℝ in Ioi 0, ENNReal.ofReal (Real.sqrt (2/Real.pi))*
        ∫⁻ k : ℝ in Ioi 0, H k T*G T := by
      apply setLIntegral_congr_fun measurableSet_Ioi
      intro T hT
      dsimp only
      rw [gaussianMomentKernel_lintegral n d hT,lintegral_mul_const (G T) (hm T)]
      exact mul_assoc _ _ _
    _ = ENNReal.ofReal (Real.sqrt (2/Real.pi))*
        ∫⁻ T : ℝ in Ioi 0, ∫⁻ k : ℝ in Ioi 0, H k T*G T :=
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ = ENNReal.ofReal (Real.sqrt (2/Real.pi))*
        ∫⁻ k : ℝ in Ioi 0, ∫⁻ T : ℝ in Ioi 0, H k T*G T := by
      congr 1
      exact lintegral_lintegral_swap hj.aemeasurable
    _ = _ := by
      congr 1
      apply setLIntegral_congr_fun measurableSet_Ioi
      intro k hk
      dsimp only [H]
      simp only [mul_assoc]
      exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top

end BrownianAffine
