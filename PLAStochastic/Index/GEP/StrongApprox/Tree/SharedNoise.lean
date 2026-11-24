import PLAStochastic.Index.GEP.StrongApprox.Tree.ProductRearrangement
import PLAStochastic.Index.GEP.StrongApprox.Quantile.GaussianSplit

/-! # A finite dyadic tree driven by shared uniform innovations -/

namespace PGM

noncomputable section

open MeasureTheory Measure ProbabilityTheory Set Function
open scoped ENNReal

attribute [local fun_prop] SADensity.measurable_splitQuantile

/-- One uniform at each internal node, in a finite recursive product space. -/
def SATreeNoise : ℕ → Type
  | 0 => PUnit
  | J + 1 => ℝ × SATreeNoise J × SATreeNoise J

instance instMeasurableSpaceSATreeNoise (J : ℕ) : MeasurableSpace (SATreeNoise J) := by
  induction J with
  | zero => exact inferInstanceAs (MeasurableSpace PUnit)
  | succ J ih =>
    letI := ih
    exact inferInstanceAs (MeasurableSpace (ℝ × SATreeNoise J × SATreeNoise J))

/-- Leaf values in their left-to-right recursive product order. -/
def SATreeValues : ℕ → Type
  | 0 => ℝ
  | J + 1 => SATreeValues J × SATreeValues J

instance instMeasurableSpaceSATreeValues (J : ℕ) : MeasurableSpace (SATreeValues J) := by
  induction J with
  | zero => exact inferInstanceAs (MeasurableSpace ℝ)
  | succ J ih =>
    letI := ih
    exact inferInstanceAs (MeasurableSpace (SATreeValues J × SATreeValues J))

/-- The product law of all independent internal-node uniforms. -/
def saTreeNoiseLaw : (J : ℕ) → Measure (SATreeNoise J)
  | 0 => Measure.dirac PUnit.unit
  | J + 1 => saUniform.prod ((saTreeNoiseLaw J).prod (saTreeNoiseLaw J))

instance isProbabilityMeasure_saTreeNoiseLaw (J : ℕ) :
    IsProbabilityMeasure (saTreeNoiseLaw J) := by
  induction J with
  | zero => exact inferInstanceAs (IsProbabilityMeasure (Measure.dirac PUnit.unit))
  | succ J ih =>
    let := ih
    exact inferInstanceAs (IsProbabilityMeasure
      (saUniform.prod ((saTreeNoiseLaw J).prod (saTreeNoiseLaw J))))

/-- The product law of iid leaves in recursive product coordinates. -/
def saTreeLeafLaw (μ : Measure ℝ) : (J : ℕ) → Measure (SATreeValues J)
  | 0 => μ
  | J + 1 => (saTreeLeafLaw μ J).prod (saTreeLeafLaw μ J)

instance isProbabilityMeasure_saTreeLeafLaw (μ : Measure ℝ) [IsProbabilityMeasure μ] (J : ℕ) :
    IsProbabilityMeasure (saTreeLeafLaw μ J) := by
  induction J with
  | zero => exact inferInstanceAs (IsProbabilityMeasure μ)
  | succ J ih =>
    let := ih
    exact inferInstanceAs (IsProbabilityMeasure ((saTreeLeafLaw μ J).prod (saTreeLeafLaw μ J)))

/-- Recursive inverse conditional-CDF splitting, with the same noise coordinates for every law. -/
def saTreeRun {p : ℕ → ℝ → ℝ} (hp : ∀ j, SADensity (p j)) :
    (J : ℕ) → ℝ → SATreeNoise J → SATreeValues J
  | 0, a, _ => a
  | J + 1, a, z =>
    (saTreeRun hp J (saSplitQuantile (hp J) a z.1) z.2.1,
      saTreeRun hp J (a - saSplitQuantile (hp J) a z.1) z.2.2)

/-- All finite tree outputs are jointly measurable in the parent total and innovations. -/
theorem measurable_saTreeRun {p : ℕ → ℝ → ℝ} (hp : ∀ j, SADensity (p j)) (J : ℕ) :
    Measurable (uncurry (saTreeRun hp J)) := by
  induction J with
  | zero => exact measurable_fst
  | succ J ih =>
    have hq : Measurable (fun z : ℝ × SATreeNoise (J + 1) =>
        saSplitQuantile (hp J) z.1 z.2.1) :=
      (hp J).measurable_splitQuantile.comp
        (f := fun z : ℝ × SATreeNoise (J + 1) => (z.1, z.2.1)) (by fun_prop)
    exact (ih.comp (f := fun z : ℝ × SATreeNoise (J + 1) =>
      (saSplitQuantile (hp J) z.1 z.2.1, z.2.2.1))
      (hq.prodMk measurable_snd.snd.fst)).prodMk
      (ih.comp (f := fun z : ℝ × SATreeNoise (J + 1) =>
        (z.1 - saSplitQuantile (hp J) z.1 z.2.1, z.2.2.2))
        ((measurable_fst.sub hq).prodMk measurable_snd.snd.snd))

/-- The full recursion reconstructs independent leaf laws, not just correct node marginals. -/
theorem saTreeRun_law {p : ℕ → ℝ → ℝ} (hp : ∀ j, SADensity (p j))
    (hstep : ∀ j, ((hp (j + 1)).law : Measure ℝ) = ((hp j).sumDensity.law : Measure ℝ))
    (J : ℕ) :
    (((hp J).law : Measure ℝ).prod (saTreeNoiseLaw J)).map (uncurry (saTreeRun hp J)) =
      saTreeLeafLaw ((hp 0).law : Measure ℝ) J := by
  induction J with
  | zero =>
    change (((hp 0).law : Measure ℝ).prod (saTreeNoiseLaw 0)).map Prod.fst = (hp 0).law
    simp
  | succ J ih =>
    have hsplit := (hp J).splitQuantile_subtree_law (saTreeNoiseLaw J)
    have hmap := congrArg (fun μ => μ.map
      (Prod.map (uncurry (saTreeRun hp J)) (uncurry (saTreeRun hp J)))) hsplit
    rw [Measure.map_map ((measurable_saTreeRun hp J).prodMap (measurable_saTreeRun hp J))
      (by fun_prop)] at hmap
    rw [← map_prod_map _ _ (measurable_saTreeRun hp J) (measurable_saTreeRun hp J), ih] at hmap
    change (((hp (J + 1)).law : Measure ℝ).prod
      (saUniform.prod ((saTreeNoiseLaw J).prod (saTreeNoiseLaw J)))).map
      (fun z : ℝ × (ℝ × SATreeNoise J × SATreeNoise J) =>
        (saTreeRun hp J (saSplitQuantile (hp J) z.1 z.2.1) z.2.2.1,
          saTreeRun hp J (z.1 - saSplitQuantile (hp J) z.1 z.2.1) z.2.2.2)) =
      (saTreeLeafLaw ((hp 0).law : Measure ℝ) J).prod (saTreeLeafLaw ((hp 0).law : Measure ℝ) J)
    rw [hstep J]
    exact hmap

/-- Deterministic sum of the recursive leaf vector. -/
def saTreeSum : (J : ℕ) → SATreeValues J → ℝ
  | 0, x => x
  | J + 1, x => saTreeSum J x.1 + saTreeSum J x.2

/-- Every split preserves the parent total exactly, hence so does the whole leaf vector. -/
theorem saTreeSum_run {p : ℕ → ℝ → ℝ} (hp : ∀ j, SADensity (p j)) (J : ℕ)
    (a : ℝ) (z : SATreeNoise J) : saTreeSum J (saTreeRun hp J a z) = a := by
  induction J generalizing a with
  | zero => rfl
  | succ J ih =>
    change saTreeSum J (saTreeRun hp J (saSplitQuantile (hp J) a z.1) z.2.1) +
      saTreeSum J (saTreeRun hp J (a - saSplitQuantile (hp J) a z.1) z.2.2) = a
    rw [ih, ih]
    ring

/-- One root uniform followed by all the internal-node innovations. -/
def saTreeSharedLaw (J : ℕ) : Measure (ℝ × SATreeNoise J) :=
  saUniform.prod (saTreeNoiseLaw J)

instance isProbabilityMeasure_saTreeSharedLaw (J : ℕ) :
    IsProbabilityMeasure (saTreeSharedLaw J) := inferInstanceAs
      (IsProbabilityMeasure (saUniform.prod (saTreeNoiseLaw J)))

/-- A complete iid leaf vector sampled from shared root and split uniforms. -/
def saTreeFromUniform {p : ℕ → ℝ → ℝ} (hp : ∀ j, SADensity (p j)) (J : ℕ)
    (z : ℝ × SATreeNoise J) : SATreeValues J :=
  saTreeRun hp J (saQuantile (cdf ((hp J).law : Measure ℝ)) z.1) z.2

theorem measurable_saTreeFromUniform {p : ℕ → ℝ → ℝ}
    (hp : ∀ j, SADensity (p j)) (J : ℕ) : Measurable (saTreeFromUniform hp J) :=
  (measurable_saTreeRun hp J).comp
    (((hp J).regularCDF.measurable_quantile.comp measurable_fst).prodMk measurable_snd)

/-- The root total has its required law and is independent of every internal innovation. -/
theorem saTreeRootInput_law {p : ℕ → ℝ → ℝ} (hp : ∀ j, SADensity (p j)) (J : ℕ) :
    (saTreeSharedLaw J).map
      (fun z => (saQuantile (cdf ((hp J).law : Measure ℝ)) z.1, z.2)) =
        ((hp J).law : Measure ℝ).prod (saTreeNoiseLaw J) := by
  have he := map_prod_map saUniform (saTreeNoiseLaw J)
    (hp J).regularCDF.measurable_quantile measurable_id
  rw [saQuantile_map_uniform _ (hp J).regularCDF, Measure.map_id] at he
  exact he.symm

/-- The root quantile and all conditional splits give exactly the iid leaf law. -/
theorem saTreeFromUniform_law {p : ℕ → ℝ → ℝ} (hp : ∀ j, SADensity (p j))
    (hstep : ∀ j, ((hp (j + 1)).law : Measure ℝ) = ((hp j).sumDensity.law : Measure ℝ))
    (J : ℕ) : (saTreeSharedLaw J).map (saTreeFromUniform hp J) =
      saTreeLeafLaw ((hp 0).law : Measure ℝ) J := by
  have hprod := map_prod_map saUniform (saTreeNoiseLaw J)
    (hp J).regularCDF.measurable_quantile measurable_id
  rw [saQuantile_map_uniform _ (hp J).regularCDF, Measure.map_id] at hprod
  rw [← saTreeRun_law hp hstep J, hprod,
    Measure.map_map (measurable_saTreeRun hp J)
      ((hp J).regularCDF.measurable_quantile.prodMap measurable_id)]
  rfl

/-- Two density hierarchies on the same innovations form a genuine leaf-vector coupling. -/
theorem saTree_shared_coupling {p q : ℕ → ℝ → ℝ}
    (hp : ∀ j, SADensity (p j)) (hq : ∀ j, SADensity (q j))
    (hpstep : ∀ j, ((hp (j + 1)).law : Measure ℝ) = ((hp j).sumDensity.law : Measure ℝ))
    (hqstep : ∀ j, ((hq (j + 1)).law : Measure ℝ) = ((hq j).sumDensity.law : Measure ℝ))
    (J : ℕ) :
    let π := (saTreeSharedLaw J).map (fun z => (saTreeFromUniform hp J z, saTreeFromUniform hq J z))
    IsProbabilityMeasure π ∧
      π.map Prod.fst = saTreeLeafLaw ((hp 0).law : Measure ℝ) J ∧
      π.map Prod.snd = saTreeLeafLaw ((hq 0).law : Measure ℝ) J := by
  have hm := (measurable_saTreeFromUniform hp J).prodMk (measurable_saTreeFromUniform hq J)
  refine ⟨Measure.isProbabilityMeasure_map hm.aemeasurable, ?_, ?_⟩
  · rw [Measure.map_map measurable_fst hm]
    exact saTreeFromUniform_law hp hpstep J
  · rw [Measure.map_map measurable_snd hm]
    exact saTreeFromUniform_law hq hqstep J

end

end PGM
