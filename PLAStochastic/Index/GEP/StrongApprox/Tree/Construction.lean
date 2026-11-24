import PLAStochastic.Index.GEP.StrongApprox.Tree.Leaves
import PLAStochastic.Index.GEP.StrongApprox.Coupling.OfBlockCoupling

/-! # The dyadic coupling for the actual smoothed source and Gaussian block laws -/

namespace PGM

noncomputable section

open MeasureTheory Measure ProbabilityTheory
open scoped NNReal

/-- The actual source sum density at a bottom-up dyadic level. -/
def saSourceTreeDensity (ν : ProbabilityMeasure ℝ) (s : ℝ) (m j : ℕ) : ℝ → ℝ :=
  saCenteredSumDensity ν s (m * 2 ^ j)

theorem saSourceTreeRegular (ν : ProbabilityMeasure ℝ) {s : ℝ} (hs : 0 < s)
    {m : ℕ} (hm : 0 < m) (j : ℕ) : SADensity (saSourceTreeDensity ν s m j) :=
  saDensity_centeredSum ν hs (Nat.mul_pos hm (by positivity))

theorem saSourceTree_step (ν : ProbabilityMeasure ℝ) {s : ℝ} (hs : 0 < s)
    {m : ℕ} (hm : 0 < m) (j : ℕ) :
    ((saSourceTreeRegular ν hs hm (j + 1)).law : Measure ℝ) =
      ((saSourceTreeRegular ν hs hm j).sumDensity.law : Measure ℝ) := by
  have he := saSumDensity_centeredSum ν hs (Nat.mul_pos hm (show 0 < 2 ^ j by positivity))
  have hn : 2 * (m * 2 ^ j) = m * 2 ^ (j + 1) := by rw [pow_succ]; ring
  rw [hn] at he
  exact congrArg (fun p : ℝ → ℝ => volume.withDensity (fun x => ENNReal.ofReal (p x))) he.symm

/-- The matching centered Gaussian sum density at a bottom-up dyadic level. -/
def saGaussianTreeDensity (V : ℝ) (m j : ℕ) : ℝ → ℝ :=
  gaussianPDFReal 0 (((m * 2 ^ j : ℕ) : ℝ≥0) * Real.toNNReal V)

theorem saGaussianTreeRegular {V : ℝ} (hV : 0 < V) {m : ℕ} (hm : 0 < m) (j : ℕ) :
    SADensity (saGaussianTreeDensity V m j) := by
  apply saDensity_gaussianPDF
  exact mul_ne_zero (by exact_mod_cast (Nat.mul_pos hm (show 0 < 2 ^ j by positivity)).ne')
    (by simp [Real.toNNReal_eq_zero, hV.not_ge])

theorem saGaussianTree_step {V : ℝ} (hV : 0 < V) {m : ℕ} (hm : 0 < m) (j : ℕ) :
    ((saGaussianTreeRegular hV hm (j + 1)).law : Measure ℝ) =
      ((saGaussianTreeRegular hV hm j).sumDensity.law : Measure ℝ) := by
  have hv : (((m * 2 ^ j : ℕ) : ℝ≥0) * Real.toNNReal V) ≠ 0 :=
    mul_ne_zero (by exact_mod_cast (Nat.mul_pos hm (show 0 < 2 ^ j by positivity)).ne')
      (by simp [Real.toNNReal_eq_zero, hV.not_ge])
  have he := saSumDensity_gaussian hv
  have hv' : ((m * 2 ^ j : ℕ) : ℝ≥0) * Real.toNNReal V +
      ((m * 2 ^ j : ℕ) : ℝ≥0) * Real.toNNReal V =
        ((m * 2 ^ (j + 1) : ℕ) : ℝ≥0) * Real.toNNReal V := by
    push_cast
    rw [pow_succ]
    ring
  rw [hv'] at he
  exact congrArg (fun p : ℝ → ℝ => volume.withDensity (fun x => ENNReal.ofReal (p x))) he.symm

/-- The common-uniform construction, specialized to the actual source and matching Gaussian laws. -/
def saDyadicLeafCoupling (ν : ProbabilityMeasure ℝ) {s : ℝ} (hs : 0 < s)
    {m : ℕ} (hm : 0 < m) (hV : 0 < lawVar ν + s ^ 2) (J : ℕ) :
    Measure ((Fin (2 ^ J) → ℝ) × (Fin (2 ^ J) → ℝ)) :=
  (saTreeSharedLaw J).map (fun z =>
    (saTreeFlattenFin J (saTreeFromUniform (saSourceTreeRegular ν hs hm) J z),
      saTreeFlattenFin J (saTreeFromUniform (saGaussianTreeRegular hV hm) J z)))

theorem saDyadicLeafCoupling_laws (ν : ProbabilityMeasure ℝ) {s : ℝ} (hs : 0 < s)
    {m : ℕ} (hm : 0 < m) (hV : 0 < lawVar ν + s ^ 2) (J : ℕ) :
    let π := saDyadicLeafCoupling ν hs hm hV J
    IsProbabilityMeasure π ∧
      π.fst = Measure.pi (fun _ : Fin (2 ^ J) =>
        ((saDensity_centeredSum ν hs hm).law : Measure ℝ)) ∧
      π.snd = Measure.pi (fun _ : Fin (2 ^ J) =>
        gaussianReal 0 ((m : ℝ≥0) * Real.toNNReal (lawVar ν + s ^ 2))) := by
  have hp := (measurable_saTreeFlattenFin J).comp
    (measurable_saTreeFromUniform (saSourceTreeRegular ν hs hm) J)
  have hq := (measurable_saTreeFlattenFin J).comp
    (measurable_saTreeFromUniform (saGaussianTreeRegular hV hm) J)
  have hpair : Measurable (fun z =>
      (saTreeFlattenFin J (saTreeFromUniform (saSourceTreeRegular ν hs hm) J z),
        saTreeFlattenFin J (saTreeFromUniform (saGaussianTreeRegular hV hm) J z))) := hp.prodMk hq
  refine ⟨isProbabilityMeasure_map hpair.aemeasurable, ?_, ?_⟩
  · change ((saTreeSharedLaw J).map _).map Prod.fst = _
    rw [Measure.map_map measurable_fst hpair]
    change (saTreeSharedLaw J).map (fun z =>
      saTreeFlattenFin J (saTreeFromUniform (saSourceTreeRegular ν hs hm) J z)) = _
    simpa only [SADensity.law, saSourceTreeDensity, saCenteredSumDensity, pow_zero, mul_one] using
      saTreeFromUniform_flattenFin_law (saSourceTreeRegular ν hs hm) (saSourceTree_step ν hs hm) J
  · change ((saTreeSharedLaw J).map _).map Prod.snd = _
    rw [Measure.map_map measurable_snd hpair]
    change (saTreeSharedLaw J).map (fun z =>
      saTreeFlattenFin J (saTreeFromUniform (saGaussianTreeRegular hV hm) J z)) = _
    rw [saTreeFromUniform_flattenFin_law (saGaussianTreeRegular hV hm) (saGaussianTree_step hV hm) J]
    congr 1
    funext i
    change volume.withDensity (fun x => ENNReal.ofReal
      (saGaussianTreeDensity (lawVar ν + s ^ 2) m 0 x)) = _
    simp only [saGaussianTreeDensity, pow_zero, mul_one]
    exact (gaussianReal_of_var_ne_zero 0 (mul_ne_zero (by exact_mod_cast hm.ne')
      (by simp [Real.toNNReal_eq_zero, hV.not_ge]))).symm

end

end PGM
