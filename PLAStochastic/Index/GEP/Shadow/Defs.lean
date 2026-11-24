import PLAStochastic.Index.GEP.Additive.OfInputs
import PLAStochastic.Index.GEP.LayerLaw.ActualLayers

/-!
# WP3 (`ShadowDefects`): shared definitions of the exponential-mark shadow

Design note: `research/2026-09-28-lean-gep-additive/wp3-design.md`.
Mathematical source: `research/2026-09-28-gep-closure/memory-route.md` §2–7.

This file contains definitions only (and the measurability facts needed to state them); it has
no `sorry`.

## The exponential-mark shadow

Attach iid `Exp(1)` marks `ξ k` to the input gaps `g k`, independently of the gaps: the sample
space is `Ω × (ℕ → ℝ)` with `shP P = P ⊗ expSeqMeasure` (`PLAStochastic/Index/Model/ExpSequence.lean`).  A *triple*
`((gap, count), mark) : Tri` carries a layer gap, its number of input gaps, and the sum of the
marks of those input gaps.  The layer map on triples (`triLayerMap`) cuts by the **gap**
component only (the actual ALG-OPT tree) and sums all three components over each segment, so
its `(gap, count)` projection is the existing pair layer map `layerMap` of `PLAStochastic/Index/Algorithm/EndpointHierarchy.lean`.

* `shTri eps g ℓ j` is triple `j` of layer `ℓ` built on the input triples `((g k, 1), ξ k)`;
* `shMean`, `shCount` are `μ_ℓ = E gap_ℓ` and `m_ℓ = E N_ℓ` (`lmean`, `lcount` of the actual
  layer on `shP P`);
* `shPair P eps g ℓ i = (X_{ℓ,i}, Y_{ℓ,i}) = (gap/μ_ℓ, mark/m_ℓ)` is the normalised
  (active, passive) pair; `shLaw P eps g ℓ = Law(Y_{ℓ,0}) = η_ℓ` is the shadow law.

## Paired sequences `V : ℕ → Ω → ℝ × ℝ`

For a sequence of (active, passive) pairs, `actLen` is the ALG-OPT segment length `T_X` of the
active components, `pasLen` that of the passive components (`T_Y`), `actSum = ∑_{i<T_X} Y_i`
(`A^X`), `pasSum = ∑_{i<T_Y} Y_i` (`A^Y`, which is `stopSum` of the passive path), and `actMean`,
`pasMean` are `C_X = E T_X`, `C_Y = E T_Y`.

`ShadowClass P V eps prm D d` collects the hypotheses of the paired density transfer and of the
tree switch (`memory-route.md` §4–6) for one layer: iid pairs, positive components with mean
one, passive exponential moment and variance bracket, passive density `≤ D`, exponential tail
and mean bracket of the active stop on the scale `eps²`, and `‖X - Y‖₂ ≤ d`.

`DensityLe μ φ` is the measure form of "`μ` has a density bounded by `φ`".
-/

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory Finset Set

/-! ## Triples and their layer map -/

/-- A triple `((gap, count), mark)`. -/
abbrev Tri := (ℝ × ℕ) × ℝ

/-- The first ALG-OPT segment length of a triple sequence: that of its gap components. -/
def triSegLen (eps : ℝ) (w : ℕ → Tri) : ℕ∞ := pairSegLen eps (fun s => (w s).1)

/-- Restart after the first segment. -/
def triShift (eps : ℝ) : (ℕ → Tri) → ℕ → Tri := shiftBy (triSegLen eps)

/-- The aggregated triple of the first segment. -/
def triBlock (eps : ℝ) (w : ℕ → Tri) : Tri := ∑ t ∈ range (triSegLen eps w).toNat, w t

/-- One layer on triple sequences: cut by the gaps, sum all components. -/
def triLayerMap (eps : ℝ) (w : ℕ → Tri) : ℕ → Tri :=
  fun j => triBlock eps ((triShift eps)^[j] w)

/-- Layer `ℓ` on triple sequences. -/
def triLayer (eps : ℝ) (ℓ : ℕ) (w : ℕ → Tri) : ℕ → Tri := (triLayerMap eps)^[ℓ] w

theorem isStoppingRule_triSegLen (eps : ℝ) : IsStoppingRule (triSegLen eps) := by
  intro t
  obtain ⟨S, hS, hSeq⟩ := isStoppingRule_pairSegLen eps t
  refine ⟨(fun v : Fin t → Tri => fun i => (v i).1) ⁻¹' S,
    (measurable_pi_lambda _ fun i => (measurable_pi_apply i).fst) hS, ?_⟩
  ext w
  change seqPrefix t (fun s => (w s).1) ∈ S ↔
    (fun s => (w s).1) ∈ {z : ℕ → ℝ × ℕ | (t : ℕ∞) < pairSegLen eps z}
  rw [← hSeq]
  rfl

theorem measurable_triSegLen (eps : ℝ) : Measurable (triSegLen eps) :=
  (isStoppingRule_triSegLen eps).measurable

theorem measurable_triBlock (eps : ℝ) : Measurable (triBlock eps) := by
  have hm : Measurable (fun p : (ℕ → Tri) × ℕ => ∑ t ∈ Finset.range p.2, p.1 t) :=
    measurable_from_prod_countable_left fun n => by
      change Measurable fun z : ℕ → Tri => ∑ t ∈ Finset.range n, z t
      exact Finset.measurable_sum _ fun t _ => measurable_pi_apply t
  exact hm.comp (measurable_id.prodMk
    ((Measurable.of_discrete (f := ENat.toNat)).comp (measurable_triSegLen eps)))

theorem measurable_triShift (eps : ℝ) : Measurable (triShift eps) :=
  measurable_shiftBy (isStoppingRule_triSegLen eps)

theorem measurable_triLayerMap (eps : ℝ) : Measurable (triLayerMap eps) :=
  measurable_pi_lambda _ fun j =>
    (measurable_triBlock eps).comp ((measurable_triShift eps).iterate j)

theorem measurable_triLayer (eps : ℝ) (ℓ : ℕ) : Measurable (triLayer eps ℓ) :=
  (measurable_triLayerMap eps).iterate ℓ

/-! ## The product space and the shadow layers -/

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The sample space of gaps and independent `Exp(1)` marks: `P ⊗ expSeqMeasure`. -/
def shP (P : Measure Ω) : Measure (Ω × (ℕ → ℝ)) := P.prod expSeqMeasure

instance (P : Measure Ω) [IsProbabilityMeasure P] : IsProbabilityMeasure (shP P) := by
  unfold shP; infer_instance

/-- The input gaps read on the product space. -/
def shGap (g : ℕ → Ω → ℝ) : ℕ → Ω × (ℕ → ℝ) → ℝ := fun t p => g t p.1

/-- The input triples `((g t, 1), ξ t)`. -/
def shInput (g : ℕ → Ω → ℝ) : ℕ → Ω × (ℕ → ℝ) → Tri := fun t p => ((g t p.1, 1), p.2 t)

/-- Triple `j` of layer `ℓ` of the shadowed hierarchy. -/
def shTri (eps : ℝ) (g : ℕ → Ω → ℝ) (ℓ : ℕ) : ℕ → Ω × (ℕ → ℝ) → Tri :=
  fun j p => triLayer eps ℓ (seq (shInput g) p) j

theorem measurable_shInput {g : ℕ → Ω → ℝ} (hg : ∀ t, Measurable (g t)) (t : ℕ) :
    Measurable (shInput g t) :=
  (((hg t).comp measurable_fst).prodMk measurable_const).prodMk
    ((measurable_pi_apply t).comp measurable_snd)

theorem measurable_shTri {g : ℕ → Ω → ℝ} (hg : ∀ t, Measurable (g t)) (eps : ℝ) (ℓ j : ℕ) :
    Measurable (shTri eps g ℓ j) :=
  (measurable_pi_apply j).comp
    ((measurable_triLayer eps ℓ).comp (measurable_seq (measurable_shInput hg)))

/-- `μ_ℓ`: the mean actual gap of layer `ℓ` (on the product space). -/
def shMean (P : Measure Ω) (eps : ℝ) (g : ℕ → Ω → ℝ) (ℓ : ℕ) : ℝ :=
  lmean (shP P) (epLayerSeq eps (shGap g) ℓ)

/-- `m_ℓ`: the mean number of input gaps in a layer-`ℓ` segment. -/
def shCount (P : Measure Ω) (eps : ℝ) (g : ℕ → Ω → ℝ) (ℓ : ℕ) : ℝ :=
  lcount (shP P) (epLayerSeq eps (shGap g) ℓ)

/-- The normalised (active, passive) pairs `(X_{ℓ,i}, Y_{ℓ,i}) = (gap/μ_ℓ, mark/m_ℓ)`. -/
def shPair (P : Measure Ω) (eps : ℝ) (g : ℕ → Ω → ℝ) (ℓ : ℕ) :
    ℕ → Ω × (ℕ → ℝ) → ℝ × ℝ :=
  fun i p => ((shTri eps g ℓ i p).1.1 / shMean P eps g ℓ,
    (shTri eps g ℓ i p).2 / shCount P eps g ℓ)

theorem measurable_shPair {g : ℕ → Ω → ℝ} (hg : ∀ t, Measurable (g t)) (P : Measure Ω)
    (eps : ℝ) (ℓ i : ℕ) : Measurable (shPair P eps g ℓ i) :=
  ((measurable_shTri hg eps ℓ i).fst.fst.div_const _).prodMk
    ((measurable_shTri hg eps ℓ i).snd.div_const _)

/-- The shadow law `η_ℓ = Law(Y_{ℓ,0})`. -/
def shLaw (P : Measure Ω) (eps : ℝ) (g : ℕ → Ω → ℝ) (ℓ : ℕ) : Measure ℝ :=
  (shP P).map fun p => (shPair P eps g ℓ 0 p).2

/-- The shadow law as a probability measure. -/
def shLawPM (P : Measure Ω) [IsProbabilityMeasure P] {g : ℕ → Ω → ℝ}
    (hg : ∀ t, Measurable (g t)) (eps : ℝ) (ℓ : ℕ) : ProbabilityMeasure ℝ :=
  ⟨shLaw P eps g ℓ,
    Measure.isProbabilityMeasure_map (measurable_shPair hg P eps ℓ 0).snd.aemeasurable⟩

theorem coe_shLawPM (P : Measure Ω) [IsProbabilityMeasure P] {g : ℕ → Ω → ℝ}
    (hg : ∀ t, Measurable (g t)) (eps : ℝ) (ℓ : ℕ) :
    ((shLawPM P hg eps ℓ : ProbabilityMeasure ℝ) : Measure ℝ) = shLaw P eps g ℓ := rfl

/-! ## Paired sequences: the two trees -/

/-- `T_X`: the ALG-OPT segment length of the active components. -/
def actLen (eps : ℝ) (V : ℕ → Ω → ℝ × ℝ) (ω : Ω) : ℕ∞ :=
  gapSegLen eps (fun t => (V t ω).1)

/-- `T_Y`: the ALG-OPT segment length of the passive components. -/
def pasLen (eps : ℝ) (V : ℕ → Ω → ℝ × ℝ) (ω : Ω) : ℕ∞ :=
  gapSegLen eps (fun t => (V t ω).2)

/-- `A^X = ∑_{i < T_X} Y_i`: the passive sum along the active tree. -/
def actSum (eps : ℝ) (V : ℕ → Ω → ℝ × ℝ) (ω : Ω) : ℝ :=
  ∑ t ∈ range (actLen eps V ω).toNat, (V t ω).2

/-- `A^Y = ∑_{i < T_Y} Y_i`: the passive sum along its own tree. -/
def pasSum (eps : ℝ) (V : ℕ → Ω → ℝ × ℝ) (ω : Ω) : ℝ :=
  ∑ t ∈ range (pasLen eps V ω).toNat, (V t ω).2

/-- `C_X = E T_X`. -/
def actMean (eps : ℝ) (P : Measure Ω) (V : ℕ → Ω → ℝ × ℝ) : ℝ :=
  ∫ ω, ((actLen eps V ω).toNat : ℝ) ∂P

/-- `C_Y = E T_Y`. -/
def pasMean (eps : ℝ) (P : Measure Ω) (V : ℕ → Ω → ℝ × ℝ) : ℝ :=
  ∫ ω, ((pasLen eps V ω).toNat : ℝ) ∂P

omit [MeasurableSpace Ω] in
theorem pasSum_eq_stopSum (eps : ℝ) (V : ℕ → Ω → ℝ × ℝ) (ω : Ω) :
    pasSum eps V ω = stopSum eps (fun t => (V t ω).2) := rfl

/-- `d_ℓ = ‖X_{ℓ,0} - Y_{ℓ,0}‖₂`. -/
def shDist (P : Measure Ω) (eps : ℝ) (g : ℕ → Ω → ℝ) (ℓ : ℕ) : ℝ :=
  Real.sqrt (∫ p, ((shPair P eps g ℓ 0 p).1 - (shPair P eps g ℓ 0 p).2) ^ 2 ∂(shP P))

/-- The coupling distance `‖A^X/C_X - A^Y/C_Y‖₂` of layer `ℓ`: a coupling of `η_{ℓ+1}` and
`Φ_ε η_ℓ` (`memory-route.md` (tree-W2)). -/
def shW (P : Measure Ω) (eps : ℝ) (g : ℕ → Ω → ℝ) (ℓ : ℕ) : ℝ :=
  Real.sqrt (∫ p, (actSum eps (shPair P eps g ℓ) p / actMean eps (shP P) (shPair P eps g ℓ) -
    pasSum eps (shPair P eps g ℓ) p / pasMean eps (shP P) (shPair P eps g ℓ)) ^ 2 ∂(shP P))

/-! ## Densities, iid sequences, the shadow class -/

/-- `μ` has a density bounded by `φ`: `μ A ≤ ∫_A φ` for every Borel set `A`. -/
def DensityLe (μ : Measure ℝ) (φ : ℝ → ℝ) : Prop :=
  ∀ A : Set ℝ, MeasurableSet A → μ A ≤ ∫⁻ x in A, ENNReal.ofReal (φ x)

/-- An iid sequence with values in a measurable space. -/
structure IIDSeqE {E : Type*} [MeasurableSpace E] (P : Measure Ω) (W : ℕ → Ω → E) : Prop where
  measurable : ∀ t, Measurable (W t)
  indep : iIndepFun W P
  ident : ∀ t, IdentDistrib (W t) (W 0) P P

/-- The fixed parameters of the shadow class: passive variance bracket `[vlo, vhi]`, passive
exponential moment `E e^{θ Y} ≤ B`, active stopping tail `P(T_X > R) ≤ At e^{-aT R/eps²}`
and active mean bracket `cm eps² ≤ C_X ≤ cp eps²`. -/
structure ShadowPrm where
  vlo : ℝ
  vhi : ℝ
  θ : ℝ
  B : ℝ
  At : ℝ
  aT : ℝ
  cm : ℝ
  cp : ℝ

/-- Admissible shadow parameters. -/
def ShadowPrm.Valid (prm : ShadowPrm) : Prop :=
  0 < prm.vlo ∧ prm.vlo ≤ prm.vhi ∧ 0 < prm.θ ∧ 0 < prm.B ∧ 0 ≤ prm.At ∧ 0 < prm.aT ∧
    0 < prm.cm ∧ prm.cm ≤ prm.cp

/-- The shadow class of one layer (`memory-route.md` §4–6): iid (active, passive) pairs,
positive components of mean one, `X ∈ L²`, passive exponential moment, variance bracket and
density `≤ D`, exponential tail and mean bracket of the active stop, and `E (X - Y)² ≤ d²`.
No density, exponential moment or non-lattice condition is imposed on the active component. -/
structure ShadowClass (P : Measure Ω) (V : ℕ → Ω → ℝ × ℝ) (eps : ℝ) (prm : ShadowPrm)
    (D d : ℝ) : Prop where
  iid : IIDSeqE P V
  pos_act : ∀ᵐ ω ∂P, 0 < (V 0 ω).1
  pos_pas : ∀ᵐ ω ∂P, 0 < (V 0 ω).2
  memLp_act : MemLp (fun ω => (V 0 ω).1) 2 P
  mean_act : ∫ ω, (V 0 ω).1 ∂P = 1
  mean_pas : ∫ ω, (V 0 ω).2 ∂P = 1
  exp_int : Integrable (fun ω => Real.exp (prm.θ * (V 0 ω).2)) P
  exp_le : ∫ ω, Real.exp (prm.θ * (V 0 ω).2) ∂P ≤ prm.B
  var_ge : prm.vlo ≤ ∫ ω, ((V 0 ω).2 - 1) ^ 2 ∂P
  var_le : ∫ ω, ((V 0 ω).2 - 1) ^ 2 ∂P ≤ prm.vhi
  density : DensityLe (P.map fun ω => (V 0 ω).2) (fun _ => D)
  tail_act : ∀ R : ℕ, P.real {ω | (R : ℕ∞) < actLen eps V ω} ≤
    prm.At * Real.exp (-(prm.aT * R / eps ^ 2))
  mean_len_ge : prm.cm * eps ^ 2 ≤ actMean eps P V
  mean_len_le : actMean eps P V ≤ prm.cp * eps ^ 2
  dist : ∫ ω, ((V 0 ω).1 - (V 0 ω).2) ^ 2 ∂P ≤ d ^ 2

end

end PGM
