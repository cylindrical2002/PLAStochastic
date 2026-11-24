import PLAStochastic.Index.GEP.StrongApprox.Tree.Events
import PLAStochastic.Index.GEP.StrongApprox.Coupling.WalkTails

/-! # Reducing tree defects to source-total and normal-innovation tails -/

namespace PGM

noncomputable section

open MeasureTheory Measure ProbabilityTheory Set Function

/-- Standard normal innovation obtained from a shared uniform. -/
def saGaussianInnovation : ℝ → ℝ := saQuantile (cdf (gaussianReal 0 1))

theorem measurable_saGaussianInnovation : Measurable saGaussianInnovation :=
  (saCDF_gaussianReal 0 one_ne_zero).measurable_quantile

theorem saGaussianInnovation_law : saUniform.map saGaussianInnovation = gaussianReal 0 1 :=
  saQuantile_map_uniform _ (saCDF_gaussianReal 0 one_ne_zero)

theorem saGaussianInnovation_cdf {u : ℝ} (hu : u ∈ Ioo 0 1) :
    cdf (gaussianReal 0 1) (saGaussianInnovation u) = u :=
  (saCDF_gaussianReal 0 one_ne_zero).apply_quantile hu

/-- The innovation at any internal node is a standard uniform. -/
theorem saTreeUniformNode_snd_law {p : ℕ → ℝ → ℝ} (hp : ∀ j, SADensity (p j))
    (hstep : ∀ j, ((hp (j + 1)).law : Measure ℝ) = ((hp j).sumDensity.law : Measure ℝ))
    (J d : ℕ) (hd : d < J) (i : SATreeIndex d) :
    (saTreeSharedLaw J).map (fun z => (saTreeUniformNode hp J d z i).2) = saUniform := by
  have he := congrArg (fun μ : Measure (ℝ × ℝ) => μ.map Prod.snd)
    (saTreeUniformNode_law hp hstep J d hd i)
  rw [Measure.map_map measurable_snd (measurable_saTreeUniformNode hp J d i),
    Measure.map_snd_prod, measure_univ, one_smul] at he
  exact he

/-- The total at an internal node has the prescribed aggregation law. -/
theorem saTreeUniformNode_fst_law {p : ℕ → ℝ → ℝ} (hp : ∀ j, SADensity (p j))
    (hstep : ∀ j, ((hp (j + 1)).law : Measure ℝ) = ((hp j).sumDensity.law : Measure ℝ))
    (J d : ℕ) (hd : d < J) (i : SATreeIndex d) :
    (saTreeSharedLaw J).map (fun z => (saTreeUniformNode hp J d z i).1) = (hp (J - d)).law := by
  have he := congrArg (fun μ : Measure (ℝ × ℝ) => μ.map Prod.fst)
    (saTreeUniformNode_law hp hstep J d hd i)
  rw [Measure.map_map measurable_fst (measurable_saTreeUniformNode hp J d i),
    Measure.map_fst_prod, measure_univ, one_smul] at he
  exact he

/-- The actual normal innovation at each node has the standard Gaussian law. -/
theorem saTreeGaussianInnovation_law {p : ℕ → ℝ → ℝ} (hp : ∀ j, SADensity (p j))
    (hstep : ∀ j, ((hp (j + 1)).law : Measure ℝ) = ((hp j).sumDensity.law : Measure ℝ))
    (J d : ℕ) (hd : d < J) (i : SATreeIndex d) :
    (saTreeSharedLaw J).map (fun z => saGaussianInnovation (saTreeUniformNode hp J d z i).2) =
      gaussianReal 0 1 := by
  rw [← saGaussianInnovation_law, ← saTreeUniformNode_snd_law hp hstep J d hd i,
    Measure.map_map measurable_saGaussianInnovation (measurable_saTreeUniformNode hp J d i).snd]
  rfl

/-- Gaussian parent values cancel exactly. Only source-total moderation and the fresh normal
innovation enter a local defect bound. -/
theorem saTreeSplitDefect_bad_bound {p q : ℕ → ℝ → ℝ}
    (hp : ∀ j, SADensity (p j)) (hq : ∀ j, SADensity (q j))
    (hstep : ∀ j, ((hp (j + 1)).law : Measure ℝ) = ((hp j).sumDensity.law : Measure ℝ))
    (J d : ℕ) (hd : d < J) (i : SATreeIndex d) (σ A Z D : ℝ)
    (hgauss : ∀ a z : ℝ,
      saSplitQuantile (hq (J - d - 1)) a (cdf (gaussianReal 0 1) z) = a / 2 + σ * z)
    (hlocal : ∀ a z : ℝ, |a| ≤ A → |z| ≤ Z →
      |saSplitQuantile (hp (J - d - 1)) a (cdf (gaussianReal 0 1) z) - a / 2 - σ * z| ≤ D) :
    (saTreeSharedLaw J).real {z | D < |saTreeSplitDefect hp hq J d z i|} ≤
      ((hp (J - d)).law : Measure ℝ).real {a | A < |a|} +
        (gaussianReal 0 1).real {z | Z < |z|} := by
  let total := fun z => (saTreeUniformNode hp J d z i).1
  let unif := fun z => (saTreeUniformNode hp J d z i).2
  let norm := fun z => saGaussianInnovation (unif z)
  have htotal : Measurable total := (measurable_saTreeUniformNode hp J d i).fst
  have hunif : Measurable unif := (measurable_saTreeUniformNode hp J d i).snd
  have hnorm : Measurable norm := measurable_saGaussianInnovation.comp hunif
  have hu0 : (saTreeSharedLaw J).real {z | unif z ∉ Ioo 0 1} = 0 := by
    change (saTreeSharedLaw J).real (unif ⁻¹' (Ioo (0 : ℝ) 1)ᶜ) = 0
    rw [← map_measureReal_apply hunif measurableSet_Ioo.compl,
      saTreeUniformNode_snd_law hp hstep J d hd i]
    simp [saUniform, Measure.real]
  have ht : (saTreeSharedLaw J).real {z | A < |total z|} =
      ((hp (J - d)).law : Measure ℝ).real {a | A < |a|} := by
    change (saTreeSharedLaw J).real (total ⁻¹' {a : ℝ | A < |a|}) = _
    rw [← map_measureReal_apply htotal
      (measurableSet_lt measurable_const measurable_id.abs : MeasurableSet {a : ℝ | A < |a|}),
      saTreeUniformNode_fst_law hp hstep J d hd i]
  have hn : (saTreeSharedLaw J).real {z | Z < |norm z|} =
      (gaussianReal 0 1).real {z | Z < |z|} := by
    change (saTreeSharedLaw J).real (norm ⁻¹' {a : ℝ | Z < |a|}) = _
    rw [← map_measureReal_apply hnorm
      (measurableSet_lt measurable_const measurable_id.abs : MeasurableSet {a : ℝ | Z < |a|}),
      saTreeGaussianInnovation_law hp hstep J d hd i]
  have hsub : {z | D < |saTreeSplitDefect hp hq J d z i|} ⊆
      {z | unif z ∉ Ioo 0 1} ∪ ({z | A < |total z|} ∪ {z | Z < |norm z|}) := by
    intro z hz
    by_contra he
    have hu : unif z ∈ Ioo 0 1 := by simpa using (not_or.mp he).1
    have ha : |total z| ≤ A := le_of_not_gt (not_or.mp (not_or.mp he).2).1
    have hz' : |norm z| ≤ Z := le_of_not_gt (not_or.mp (not_or.mp he).2).2
    have hcdf : cdf (gaussianReal 0 1) (norm z) = unif z := saGaussianInnovation_cdf hu
    have hui : (saTreeUniformNode hq J d z i).2 = unif z :=
      (saTreeNode_uniform_eq hp hq J d _ _ z.2 i).symm
    have hdef : saTreeSplitDefect hp hq J d z i =
        saSplitQuantile (hp (J - d - 1)) (total z) (unif z) - total z / 2 - σ * norm z := by
      have hg := hgauss (saTreeUniformNode hq J d z i).1 (norm z)
      rw [hcdf] at hg
      unfold saTreeSplitDefect
      rw [hui, hg]
      dsimp only [total, unif]
      ring
    change D < |saTreeSplitDefect hp hq J d z i| at hz
    rw [hdef, ← hcdf] at hz
    exact (not_lt_of_ge (hlocal (total z) (norm z) ha hz')) hz
  calc
    _ ≤ (saTreeSharedLaw J).real
        ({z | unif z ∉ Ioo 0 1} ∪ ({z | A < |total z|} ∪ {z | Z < |norm z|})) :=
      measureReal_mono hsub
    _ ≤ (saTreeSharedLaw J).real {z | unif z ∉ Ioo 0 1} +
        ((saTreeSharedLaw J).real {z | A < |total z|} +
          (saTreeSharedLaw J).real {z | Z < |norm z|}) :=
      (measureReal_union_le _ _).trans (add_le_add le_rfl (measureReal_union_le _ _))
    _ = _ := by rw [hu0, ht, hn, zero_add]

/-- The normal part of the node failure probability has an explicit Chernoff bound. -/
theorem saTreeSplitDefect_bad_bound_exp {p q : ℕ → ℝ → ℝ}
    (hp : ∀ j, SADensity (p j)) (hq : ∀ j, SADensity (q j))
    (hstep : ∀ j, ((hp (j + 1)).law : Measure ℝ) = ((hp j).sumDensity.law : Measure ℝ))
    (J d : ℕ) (hd : d < J) (i : SATreeIndex d) (σ A Z D : ℝ) (hZ : 0 ≤ Z)
    (hgauss : ∀ a z : ℝ,
      saSplitQuantile (hq (J - d - 1)) a (cdf (gaussianReal 0 1) z) = a / 2 + σ * z)
    (hlocal : ∀ a z : ℝ, |a| ≤ A → |z| ≤ Z →
      |saSplitQuantile (hp (J - d - 1)) a (cdf (gaussianReal 0 1) z) - a / 2 - σ * z| ≤ D) :
    (saTreeSharedLaw J).real {z | D < |saTreeSplitDefect hp hq J d z i|} ≤
      ((hp (J - d)).law : Measure ℝ).real {a | A < |a|} + 2 * Real.exp (-(Z ^ 2 / 2)) := by
  apply (saTreeSplitDefect_bad_bound hp hq hstep J d hd i σ A Z D hgauss hlocal).trans
  apply add_le_add le_rfl
  simpa using sa_gaussian_abs_tail (v := 1) (by norm_num) hZ

/-- Root quantile error fails only when the shared standard normal innovation leaves its window. -/
theorem saTreeRootError_bad_bound {p q : ℕ → ℝ → ℝ}
    (hp : ∀ j, SADensity (p j)) (hq : ∀ j, SADensity (q j))
    (J : ℕ) (σ R Z : ℝ)
    (hgauss : ∀ z : ℝ, saQuantile (cdf ((hq J).law : Measure ℝ))
      (cdf (gaussianReal 0 1) z) = σ * z)
    (hlocal : ∀ z : ℝ, |z| ≤ Z →
      |saQuantile (cdf ((hp J).law : Measure ℝ)) (cdf (gaussianReal 0 1) z) - σ * z| ≤ R) :
    (saTreeSharedLaw J).real {z | R < |saTreeRootError hp hq J z|} ≤
      (gaussianReal 0 1).real {z | Z < |z|} := by
  have hroot : (saTreeSharedLaw J).map Prod.fst = saUniform := by
    change (saUniform.prod (saTreeNoiseLaw J)).map Prod.fst = _
    simp
  have hnorm : (saTreeSharedLaw J).map (fun z => saGaussianInnovation z.1) =
      gaussianReal 0 1 := by
    rw [← saGaussianInnovation_law, ← hroot,
      Measure.map_map measurable_saGaussianInnovation measurable_fst]
    rfl
  have hu0 : (saTreeSharedLaw J).real {z | z.1 ∉ Ioo 0 1} = 0 := by
    change (saTreeSharedLaw J).real (Prod.fst ⁻¹' (Ioo (0 : ℝ) 1)ᶜ) = 0
    rw [← map_measureReal_apply measurable_fst measurableSet_Ioo.compl, hroot]
    simp [saUniform, Measure.real]
  have hn : (saTreeSharedLaw J).real {z | Z < |saGaussianInnovation z.1|} =
      (gaussianReal 0 1).real {z | Z < |z|} := by
    change (saTreeSharedLaw J).real ((fun z => saGaussianInnovation z.1) ⁻¹' {a : ℝ | Z < |a|}) = _
    rw [← map_measureReal_apply (show Measurable (fun z : ℝ × SATreeNoise J =>
      saGaussianInnovation z.1) from measurable_saGaussianInnovation.comp measurable_fst)
      (measurableSet_lt measurable_const measurable_id.abs : MeasurableSet {a : ℝ | Z < |a|}), hnorm]
  have hsub : {z | R < |saTreeRootError hp hq J z|} ⊆
      {z | z.1 ∉ Ioo 0 1} ∪ {z | Z < |saGaussianInnovation z.1|} := by
    intro z hz
    by_contra he
    have hu : z.1 ∈ Ioo 0 1 := by simpa using (not_or.mp he).1
    have hz' : |saGaussianInnovation z.1| ≤ Z := le_of_not_gt (not_or.mp he).2
    have hcdf := saGaussianInnovation_cdf hu
    have hb := hlocal (saGaussianInnovation z.1) hz'
    have hg := hgauss (saGaussianInnovation z.1)
    rw [hcdf] at hb hg
    exact (not_lt_of_ge (show |saTreeRootError hp hq J z| ≤ R by
      simpa only [saTreeRootError, hg] using hb)) hz
  calc
    _ ≤ (saTreeSharedLaw J).real
        ({z | z.1 ∉ Ioo 0 1} ∪ {z | Z < |saGaussianInnovation z.1|}) := measureReal_mono hsub
    _ ≤ (saTreeSharedLaw J).real {z | z.1 ∉ Ioo 0 1} +
        (saTreeSharedLaw J).real {z | Z < |saGaussianInnovation z.1|} := measureReal_union_le _ _
    _ = _ := by rw [hu0, hn, zero_add]

/-- Explicit root-failure tail for the common-uniform tree. -/
theorem saTreeRootError_bad_bound_exp {p q : ℕ → ℝ → ℝ}
    (hp : ∀ j, SADensity (p j)) (hq : ∀ j, SADensity (q j))
    (J : ℕ) (σ R Z : ℝ) (hZ : 0 ≤ Z)
    (hgauss : ∀ z : ℝ, saQuantile (cdf ((hq J).law : Measure ℝ))
      (cdf (gaussianReal 0 1) z) = σ * z)
    (hlocal : ∀ z : ℝ, |z| ≤ Z →
      |saQuantile (cdf ((hp J).law : Measure ℝ)) (cdf (gaussianReal 0 1) z) - σ * z| ≤ R) :
    (saTreeSharedLaw J).real {z | R < |saTreeRootError hp hq J z|} ≤ 2 * Real.exp (-(Z ^ 2 / 2)) := by
  apply (saTreeRootError_bad_bound hp hq J σ R Z hgauss hlocal).trans
  simpa using sa_gaussian_abs_tail (v := 1) (by norm_num) hZ

/-- Directly consumable tree estimate from scalar root/split quantile bounds and source-total tails.
The Gaussian innovations and their marginal tail estimates are supplied by the construction. -/
theorem saTreeLeafPair_moderated_bad_bound {p q : ℕ → ℝ → ℝ}
    (hp : ∀ j, SADensity (p j)) (hq : ∀ j, SADensity (q j))
    (hstep : ∀ j, ((hp (j + 1)).law : Measure ℝ) = ((hp j).sumDensity.law : Measure ℝ))
    (J : ℕ) (σroot R D Z : ℝ) (σ A : ℕ → ℝ) (hR : 0 ≤ R) (hD : 0 ≤ D) (hZ : 0 ≤ Z)
    (hgaussRoot : ∀ z : ℝ, saQuantile (cdf ((hq J).law : Measure ℝ))
      (cdf (gaussianReal 0 1) z) = σroot * z)
    (hroot : ∀ z : ℝ, |z| ≤ Z →
      |saQuantile (cdf ((hp J).law : Measure ℝ)) (cdf (gaussianReal 0 1) z) - σroot * z| ≤ R)
    (hgaussSplit : ∀ d < J, ∀ a z : ℝ,
      saSplitQuantile (hq (J - d - 1)) a (cdf (gaussianReal 0 1) z) = a / 2 + σ d * z)
    (hlocal : ∀ d < J, ∀ a z : ℝ, |a| ≤ A d → |z| ≤ Z →
      |saSplitQuantile (hp (J - d - 1)) a (cdf (gaussianReal 0 1) z) - a / 2 - σ d * z| ≤ D) :
    ((saTreeSharedLaw J).map (saTreeLeafPair hp hq J)).real
      (saLeafBad (2 ^ J) (((J : ℝ) + 1) * (R + 2 * D))) ≤
        2 * Real.exp (-(Z ^ 2 / 2)) + ∑ d ∈ Finset.range J, (2 ^ d : ℕ) *
          (((hp (J - d)).law : Measure ℝ).real {a | A d < |a|} + 2 * Real.exp (-(Z ^ 2 / 2))) := by
  apply saTreeLeafPair_bad_bound hp hq J hR hD
    (saTreeRootError_bad_bound_exp hp hq J σroot R Z hZ hgaussRoot hroot)
  intro d hd i
  exact saTreeSplitDefect_bad_bound_exp hp hq hstep J d hd i (σ d) (A d) Z D hZ
    (hgaussSplit d hd) (hlocal d hd)

end

end PGM
