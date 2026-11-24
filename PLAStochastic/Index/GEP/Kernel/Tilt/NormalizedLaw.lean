import PLAStochastic.Index.GEP.StrongApprox.Tilt.Recentered
import PLAStochastic.Index.GEP.StrongApprox.Saddle.Parameters
import PLAStochastic.Index.GEP.OrbitClosure.OneLayerEnvelope

/-!
# Mean-normalized exponential tilts stay in a uniform regular class

The tilted coordinate has its actual mean, which is generally not one.
Dividing by that mean produces the regular probability law used downstream.
-/

namespace PGM
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal NNReal

/-- The actual mean of the tilted original gap. -/
def kernelTiltMean (ν : ProbabilityMeasure ℝ) (lam : ℝ) : ℝ :=
  ∫ x : ℝ, x ∂centeredTilt ν lam

/-- Normalization by the actual tilted mean, at the measure level. -/
def kernelTiltNormalized (ν : ProbabilityMeasure ℝ) (lam : ℝ) : Measure ℝ :=
  (centeredTilt ν lam).map (fun x => x / kernelTiltMean ν lam)

/-- Subtracting a constant from the exponent leaves the tilted law unchanged. -/
theorem kernel_centeredTilt_eq_raw (ν : ProbabilityMeasure ℝ) (lam : ℝ) :
    centeredTilt ν lam = (ν : Measure ℝ).tilted (fun x => lam * x) := by
  have hh := tilted_tilted (μ := (ν : Measure ℝ)) (f := fun _ : ℝ => -lam)
    (integrable_const (Real.exp (-lam))) (fun x : ℝ => lam * x)
  have he : (fun _ : ℝ => -lam) + (fun x : ℝ => lam * x) =
      (fun x : ℝ => lam * (x - 1)) := by funext x; dsimp; ring
  rw [tilted_const, he] at hh
  exact hh.symm

variable {vlo vhi κ₃ B θ : ℝ} {ν : ProbabilityMeasure ℝ}

theorem UnivClass.kernel_integrable_exp_raw (h : UnivClass vlo vhi κ₃ B θ ν)
    {lam : ℝ} (hlam : |lam| ≤ θ) :
    Integrable (fun x : ℝ => Real.exp (lam * x)) (ν : Measure ℝ) := by
  convert (h.integrable_exp_centered hlam).const_mul (Real.exp lam) using 1
  funext x
  rw [← Real.exp_add]
  congr 1
  ring

/-- The first cumulant derivative is the centered tilted mean. -/
theorem UnivClass.kernelTiltMean_eq (h : UnivClass vlo vhi κ₃ B θ ν)
    {lam : ℝ} (hlam : |lam| < θ) :
    kernelTiltMean ν lam = 1 + deriv (cgf (fun x : ℝ => x - 1) (ν : Measure ℝ)) lam := by
  let := h.isProbabilityMeasure_centeredTilt hlam.le
  have hi : Integrable (fun x : ℝ => x - 1) (centeredTilt ν lam) :=
    (memLp_tilted_mul (h.centered_mem_interior hlam) (1 : ℝ≥0)).integrable (by norm_num)
  have hx : Integrable (fun x : ℝ => x) (centeredTilt ν lam) := by
    convert! hi.add (integrable_const 1) using 1
    funext x
    simp
  have hm := h.integral_centered_centeredTilt hlam
  rw [integral_sub hx (integrable_const 1)] at hm
  simp only [integral_const, probReal_univ, one_smul] at hm
  dsimp [kernelTiltMean]
  linarith

/-- A uniform Lipschitz bound for the true tilted mean around one. -/
theorem UnivClass.kernelTiltMean_sub_one_le (h : UnivClass vlo vhi κ₃ B θ ν)
    (hvlo : 0 < vlo) (hθ : 0 < θ) {lam : ℝ} (hlam : |lam| ≤ saTiltRadius vlo B θ) :
    |kernelTiltMean ν lam - 1| ≤ (5 / 4 * vhi) * |lam| := by
  let r := saTiltRadius vlo B θ
  have hr : 0 < r := saTiltRadius_pos hvlo hθ
  have hlt : |lam| < θ := (hlam.trans (saTiltRadius_le_half vlo B hθ)).trans_lt (by linarith)
  have hd : ∀ t ∈ Icc (-r) r,
      DifferentiableAt ℝ (deriv (cgf (fun x : ℝ => x - 1) (ν : Measure ℝ))) t := by
    intro t ht
    have ht' : |t| < θ := ((abs_le.mpr ht).trans
      (saTiltRadius_le_half vlo B hθ)).trans_lt (by linarith)
    simpa only [Function.iterate_one] using
      (analyticOnNhd_cgf.iterated_deriv 1 t (h.centered_mem_interior ht')).differentiableAt
  have hb : ∀ t ∈ Icc (-r) r,
      ‖deriv (deriv (cgf (fun x : ℝ => x - 1) (ν : Measure ℝ))) t‖ ≤ 5 / 4 * vhi := by
    intro t ht
    have hv := h.centered_cgf_variance_bracket hvlo hθ (abs_le.mpr ht)
    have hV : 0 ≤ iteratedDeriv 2 (cgf (fun x : ℝ => x - 1) (ν : Measure ℝ)) t := by
      linarith [h.var_ge]
    have hident : deriv (deriv (cgf (fun x : ℝ => x - 1) (ν : Measure ℝ))) t =
        iteratedDeriv 2 (cgf (fun x : ℝ => x - 1) (ν : Measure ℝ)) t := by
      rw [show (2 : ℕ) = 1 + 1 by norm_num, iteratedDeriv_succ, iteratedDeriv_one]
    rw [Real.norm_eq_abs, hident, abs_of_nonneg hV]
    linarith [h.var_le]
  have hh := (convex_Icc (-r) r).norm_image_sub_le_of_norm_deriv_le hd hb
    (show (0 : ℝ) ∈ Icc (-r) r from ⟨by linarith, hr.le⟩) (abs_le.mp hlam)
  simp only [h.deriv_centered_cgf_zero hθ, sub_zero, Real.norm_eq_abs] at hh
  rw [h.kernelTiltMean_eq hlt]
  simpa only [add_sub_cancel_left] using hh

/-- Normalizing the true mean gives exactly mean one. -/
theorem kernelTiltNormalized_mean {lam : ℝ} {ρ : ProbabilityMeasure ℝ}
    (hρ : (ρ : Measure ℝ) = kernelTiltNormalized ν lam) (hm : kernelTiltMean ν lam ≠ 0) :
    lawMean ρ = 1 := by
  unfold lawMean
  rw [hρ, kernelTiltNormalized, integral_map (by fun_prop) (by fun_prop), integral_div]
  exact div_self hm

/-- The normalized variance uses the actual tilted mean squared. -/
theorem UnivClass.kernelTiltNormalized_var (h : UnivClass vlo vhi κ₃ B θ ν)
    {lam : ℝ} (hlam : |lam| < θ) {ρ : ProbabilityMeasure ℝ}
    (hρ : (ρ : Measure ℝ) = kernelTiltNormalized ν lam) :
    lawVar ρ = iteratedDeriv 2 (cgf (fun x : ℝ => x - 1) (ν : Measure ℝ)) lam /
      kernelTiltMean ν lam ^ 2 := by
  let := h.isProbabilityMeasure_centeredTilt hlam.le
  have hv : Var[id; centeredTilt ν lam] =
      iteratedDeriv 2 (cgf (fun x : ℝ => x - 1) (ν : Measure ℝ)) lam := by
    have hh := h.variance_centeredTilt hlam
    change Var[(fun x : ℝ => id x - 1); centeredTilt ν lam] = _ at hh
    rw [variance_sub_const measurable_id.aestronglyMeasurable 1] at hh
    exact hh
  have hlaw : lawVar ρ = Var[id; (ρ : Measure ℝ)] := by
    rw [variance_eq_integral measurable_id.aemeasurable]
    rfl
  rw [hlaw, hρ, kernelTiltNormalized, variance_id_map (by fun_prop)]
  simp_rw [div_eq_mul_inv]
  rw [variance_mul_const]
  change Var[id; centeredTilt ν lam] * (kernelTiltMean ν lam)⁻¹ ^ 2 = _
  rw [hv]
  ring


/-- Tilting the original density preserves a fixed exponential envelope. -/
theorem RegLaw.kernelTilt_envBd {D : ℝ} (h : RegLaw D θ vlo vhi ν)
    (hD : 0 ≤ D) (hθ : 0 < θ) (hvlo : 0 < vlo) {lam : ℝ} (hlam : |lam| ≤ θ / 2) :
    EnvBd (D * Real.exp θ) (θ / 2) (centeredTilt ν lam) := by
  let M := ∫ x : ℝ, Real.exp (lam * (x - 1)) ∂(ν : Measure ℝ)
  have hM : 1 ≤ M := (h.univClass hθ hvlo).one_le_integral_exp_centered hlam
  obtain ⟨f, hf, hf0, hfz, hfbd, hfm⟩ := h.density
  change (ν : Measure ℝ).withDensity (fun x => ENNReal.ofReal (Real.exp (lam * (x - 1)) / M)) ≤ _
  rw [hfm, ← withDensity_mul volume hf.ennreal_ofReal (by fun_prop)]
  apply withDensity_mono (ae_of_all _ fun x => ?_)
  simp only [Pi.mul_apply]
  rw [← ENNReal.ofReal_mul (hf0 x)]
  apply ENNReal.ofReal_le_ofReal
  by_cases hx : 0 < x
  · rw [envFun, indicator_of_mem (show x ∈ Ioi (0 : ℝ) from hx)]
    have hex : -θ * x + lam * (x - 1) ≤ θ + (-(θ / 2) * x) := by
      have hm := mul_le_mul_of_nonneg_right (abs_le.mp hlam).2 hx.le
      have hn := (neg_le_abs lam).trans hlam
      nlinarith
    calc
      f x * (Real.exp (lam * (x - 1)) / M) ≤ f x * Real.exp (lam * (x - 1)) :=
        mul_le_mul_of_nonneg_left (div_le_self (Real.exp_nonneg _) hM) (hf0 x)
      _ ≤ (D * Real.exp (-θ * x)) * Real.exp (lam * (x - 1)) :=
        mul_le_mul_of_nonneg_right (hfbd x) (Real.exp_nonneg _)
      _ = D * Real.exp (-θ * x + lam * (x - 1)) := by rw [Real.exp_add]; ring
      _ ≤ D * Real.exp (θ + (-(θ / 2) * x)) :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hex) hD
      _ = (D * Real.exp θ) * Real.exp (-(θ / 2) * x) := by rw [Real.exp_add]; ring
  · rw [hfz x (not_lt.mp hx), zero_mul, envFun,
      indicator_of_notMem (show x ∉ Ioi (0 : ℝ) from hx)]

/-- The density Jacobian and the exponential scale both follow the actual mean. -/
theorem kernel_envBd_map_div {μ : Measure ℝ} {D θ m : ℝ} (h : EnvBd D θ μ)
    (hD : 0 ≤ D) (hθ : 0 ≤ θ) (hmlo : 1 / 2 ≤ m) (hmhi : m ≤ 2) :
    EnvBd (2 * D) (θ / 2) (μ.map (fun x => x / m)) := by
  have hm : 0 < m := by linarith
  have hmap := map_div_const_le h hm
  apply hmap.trans (withDensity_mono (ae_of_all _ fun z => ?_))
  apply ENNReal.ofReal_le_ofReal
  simp only [envFun, indicator_apply, mem_Ioi]
  by_cases hz : 0 < z
  · rw [if_pos hz, if_pos (mul_pos hm hz)]
    have hex : Real.exp (-θ * (m * z)) ≤ Real.exp (-(θ / 2) * z) := by
      apply Real.exp_le_exp.mpr
      have hh := mul_le_mul_of_nonneg_right hmlo (show 0 ≤ θ * z by positivity)
      nlinarith
    calc
      m * (D * Real.exp (-θ * (m * z))) = (m * D) * Real.exp (-θ * (m * z)) := by ring
      _ ≤ (2 * D) * Real.exp (-(θ / 2) * z) :=
        mul_le_mul (mul_le_mul_of_nonneg_right hmhi hD) hex (Real.exp_nonneg _) (by positivity)
  · rw [if_neg hz, if_neg (not_lt.mpr (mul_nonpos_of_nonneg_of_nonpos hm.le (not_lt.mp hz))), mul_zero]

/-- A concrete class-uniform radius also controls the change in the mean. -/
def kernelTiltClassRadius (D θ vlo vhi : ℝ) : ℝ :=
  min (saTiltRadius vlo (2 * D / θ) (θ / 2)) (1 / (4 * vhi))

theorem kernelTiltClassRadius_pos {D θ vlo vhi : ℝ}
    (hθ : 0 < θ) (hvlo : 0 < vlo) (hv : vlo ≤ vhi) :
    0 < kernelTiltClassRadius D θ vlo vhi := by
  have hvhi : 0 < vhi := hvlo.trans_le hv
  exact lt_min (saTiltRadius_pos hvlo (by positivity)) (by positivity)

/-- The tilted mean is uniformly bounded away from zero before normalization. -/
theorem RegLaw.kernelTiltMean_bounds {D : ℝ} (h : RegLaw D θ vlo vhi ν)
    (hθ : 0 < θ) (hvlo : 0 < vlo) (hv : vlo ≤ vhi)
    {lam : ℝ} (hlam : |lam| ≤ kernelTiltClassRadius D θ vlo vhi) :
    1 / 2 ≤ kernelTiltMean ν lam ∧ kernelTiltMean ν lam ≤ 2 := by
  have hvhi : 0 < vhi := hvlo.trans_le hv
  have hrad : |lam| ≤ saTiltRadius vlo (2 * D / θ) (θ / 2) :=
    hlam.trans (min_le_left _ _)
  have hsmall : |lam| ≤ 1 / (4 * vhi) := hlam.trans (min_le_right _ _)
  have hm := (h.univClass hθ hvlo).kernelTiltMean_sub_one_le hvlo (by positivity) hrad
  have hh := (le_div_iff₀ (show 0 < 4 * vhi by positivity)).1 hsmall
  have hb : |kernelTiltMean ν lam - 1| ≤ 1 / 2 := by nlinarith
  have hb' := abs_le.mp hb
  constructor <;> linarith

/-- **Uniform regular class after a small tilt and actual-mean normalization.**
Every displayed class parameter and the tilt radius precede the choice of law
and tilt. The measure identity records the actual transformed law. -/
theorem kernel_regLaw_normalized_tilt (D θ vlo vhi : ℝ)
    (hD : 0 < D) (hθ : 0 < θ) (hvlo : 0 < vlo) (hv : vlo ≤ vhi) :
    0 < kernelTiltClassRadius D θ vlo vhi ∧
      ∀ ν : ProbabilityMeasure ℝ, RegLaw D θ vlo vhi ν →
      ∀ lam : ℝ, |lam| ≤ kernelTiltClassRadius D θ vlo vhi →
        (1 / 2 ≤ kernelTiltMean ν lam ∧ kernelTiltMean ν lam ≤ 2) ∧
        ∃ ρ : ProbabilityMeasure ℝ, (ρ : Measure ℝ) = kernelTiltNormalized ν lam ∧
          RegLaw (2 * D * Real.exp θ) (θ / 4) (3 * vlo / 16) (5 * vhi) ρ := by
  refine ⟨kernelTiltClassRadius_pos hθ hvlo hv, ?_⟩
  intro ν hν lam hlam
  have hU := hν.univClass hθ hvlo
  have hm := hν.kernelTiltMean_bounds hθ hvlo hv hlam
  have hmpos : 0 < kernelTiltMean ν lam := by linarith [hm.1]
  have hrad : |lam| ≤ saTiltRadius vlo (2 * D / θ) (θ / 2) :=
    hlam.trans (min_le_left _ _)
  have hhalf : |lam| ≤ (θ / 2) / 2 := hrad.trans (saTiltRadius_le_half _ _ (by positivity))
  have hl : |lam| < θ / 2 := hhalf.trans_lt (by linarith)
  let := hU.isProbabilityMeasure_centeredTilt hl.le
  let ρ : ProbabilityMeasure ℝ := ⟨kernelTiltNormalized ν lam,
    Measure.isProbabilityMeasure_map (by fun_prop)⟩
  have hρ : (ρ : Measure ℝ) = kernelTiltNormalized ν lam := rfl
  refine ⟨hm, ρ, hρ, ?_⟩
  apply regLaw_of_envBd_of_moments (kernelTiltNormalized_mean hρ hmpos.ne')
  · rw [hU.kernelTiltNormalized_var hl hρ, le_div_iff₀ (sq_pos_of_pos hmpos)]
    have hV := (hU.centered_cgf_variance_bracket hvlo (by positivity) hrad).1
    have hm2 : kernelTiltMean ν lam ^ 2 ≤ 4 := by nlinarith [hm.1, hm.2]
    have hb := mul_le_mul_of_nonneg_left hm2 (show 0 ≤ 3 * vlo / 16 by positivity)
    nlinarith [hν.var_ge]
  · rw [hU.kernelTiltNormalized_var hl hρ, div_le_iff₀ (sq_pos_of_pos hmpos)]
    have hV := (hU.centered_cgf_variance_bracket hvlo (by positivity) hrad).2
    have hm2 : 1 / 4 ≤ kernelTiltMean ν lam ^ 2 := by nlinarith [hm.1]
    have hb := mul_le_mul_of_nonneg_left hm2 (show 0 ≤ 5 * vhi by linarith)
    nlinarith [hν.var_le]
  · rw [hρ]
    have hE := hν.kernelTilt_envBd hD.le hθ hvlo hl.le
    have he := kernel_envBd_map_div hE (by positivity) (by positivity) hm.1 hm.2
    rw [show 2 * (D * Real.exp θ) = 2 * D * Real.exp θ by ring,
      show (θ / 2) / 2 = θ / 4 by ring] at he
    exact he
  · positivity

end
end PGM
