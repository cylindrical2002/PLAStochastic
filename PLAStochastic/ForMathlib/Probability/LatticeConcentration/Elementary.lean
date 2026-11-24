import PLAStochastic.ForMathlib.Probability.LatticeConcentration.Defs
import Mathlib.Probability.Independence.Basic

/-!
# Laws on `ℤ`: elementary facts on `lconc` and `convFin`

Shared by the lattice concentration inequalities (`PLAStochastic.ForMathlib.Probability.LatticeConcentration.KolmogorovRogozin`, `PLAStochastic.ForMathlib.Probability.LatticeConcentration.Kesten`) and
the renewal bounds (`PLAStochastic.ForMathlib.Probability.LatticeConcentration.RenewalOneTime`).

* The concentration function: `lconc_le`, `lconc_nonneg`, `window_le_lconc` (a window of `c`
  consecutive integers has mass at most `lconc μ c`) and its atom forms `atom_le_lconc`,
  `atom_le_ofReal_lconc`.
* `conv_apply_singleton`: `(μ ∗ ν) {j} = ∫⁻ y, ν {j - y} ∂μ`.
* `isProbabilityMeasure_convFin` (constant family: `isProbabilityMeasure_convFin_const`).
* `map_sum_eq_convFin`: the law of a sum of independent integer variables is the `convFin` of
  their laws; `map_sum_range_eq_convFin` is the iid form over `Finset.range n`.
-/

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory

/-! ## The concentration function `lconc` -/

theorem lconc_le {μ : Measure ℤ} {c : ℕ} {t : ℝ}
    (h : ∀ x : ℤ, (μ (Set.Ico x (x + c))).toReal ≤ t) : lconc μ c ≤ t :=
  ciSup_le h

theorem lconc_nonneg (μ : Measure ℤ) (c : ℕ) : 0 ≤ lconc μ c :=
  Real.iSup_nonneg fun _ => ENNReal.toReal_nonneg

theorem bddAbove_window (μ : Measure ℤ) [IsFiniteMeasure μ] (c : ℕ) :
    BddAbove (Set.range fun x : ℤ => (μ (Set.Ico x (x + c))).toReal) :=
  ⟨(μ Set.univ).toReal, by
    rintro _ ⟨x, rfl⟩
    exact ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono (Set.subset_univ _))⟩

theorem window_le_lconc (μ : Measure ℤ) [IsFiniteMeasure μ] (c : ℕ) (x : ℤ) :
    (μ (Set.Ico x (x + c))).toReal ≤ lconc μ c :=
  le_ciSup (bddAbove_window μ c) x

theorem Ico_one (x : ℤ) : Set.Ico x (x + 1) = {x} := by
  ext y; simp only [Set.mem_Ico, Set.mem_singleton_iff]; omega

theorem atom_le_lconc (μ : Measure ℤ) [IsFiniteMeasure μ] (x : ℤ) :
    (μ {x}).toReal ≤ lconc μ 1 := by
  have := window_le_lconc μ 1 x
  rwa [Nat.cast_one, Ico_one] at this

theorem atom_le_ofReal_lconc (μ : Measure ℤ) [IsFiniteMeasure μ] (x : ℤ) :
    μ {x} ≤ ENNReal.ofReal (lconc μ 1) := by
  rw [← ENNReal.ofReal_toReal (measure_ne_top μ _)]
  exact ENNReal.ofReal_le_ofReal (atom_le_lconc μ x)

/-! ## Convolution on `ℤ` -/

theorem conv_apply_singleton (μ ν : Measure ℤ) [SFinite ν] (j : ℤ) :
    (μ ∗ ν) {j} = ∫⁻ y, ν {j - y} ∂μ := by
  rw [Measure.conv, Measure.map_apply measurable_add (MeasurableSet.of_discrete),
    Measure.prod_apply (measurable_add (MeasurableSet.of_discrete))]
  congr 1
  ext y
  congr 1
  ext z
  simp only [Set.mem_preimage, Set.mem_singleton_iff]
  omega

/-! ## Finite convolutions -/

/-- `convFin` of probability measures is a probability measure. -/
theorem isProbabilityMeasure_convFin :
    ∀ (m : ℕ) (μ : Fin m → Measure ℤ), (∀ i, IsProbabilityMeasure (μ i)) →
      IsProbabilityMeasure (convFin m μ)
  | 0, _, _ => by rw [convFin]; infer_instance
  | m + 1, μ, hμ => by
    rw [convFin]
    have := isProbabilityMeasure_convFin m (fun i => μ i.castSucc) (fun i => hμ _)
    have := hμ (Fin.last m)
    infer_instance

theorem isProbabilityMeasure_convFin_const (μ : Measure ℤ) [IsProbabilityMeasure μ] (n : ℕ) :
    IsProbabilityMeasure (convFin n (fun _ => μ)) :=
  isProbabilityMeasure_convFin n _ fun _ => inferInstance

/-- The law of a sum of independent integer variables is the `convFin` of their laws. -/
theorem map_sum_eq_convFin {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] :
    ∀ (m : ℕ) (X : Fin m → Ω → ℤ), (∀ i, Measurable (X i)) → iIndepFun X P →
      P.map (fun ω => ∑ i, X i ω) = convFin m (fun i => P.map (X i))
  | 0, X, _, _ => by
    simp only [Finset.univ_eq_empty, Finset.sum_empty, convFin]
    rw [Measure.map_const, measure_univ, one_smul]
  | m + 1, X, hX, hind => by
    have hsplit : (fun ω => ∑ i, X i ω) =
        (fun ω => ∑ i : Fin m, X i.castSucc ω) + X (Fin.last m) := by
      funext ω
      simp [Fin.sum_univ_castSucc]
    have hindep : IndepFun (fun ω => ∑ i : Fin m, X i.castSucc ω) (X (Fin.last m)) P := by
      have h := hind.indepFun_finsetSum_of_notMem hX
        (s := Finset.univ.map Fin.castSuccEmb) (i := Fin.last m) (by simp)
      convert h using 1
      funext ω
      simp [Finset.sum_apply]
    have hmeas : Measurable (fun ω => ∑ i : Fin m, X i.castSucc ω) :=
      Finset.measurable_sum _ (fun i _ => hX _)
    rw [hsplit, hindep.map_add_eq_map_conv_map₀ hmeas.aemeasurable (hX _).aemeasurable,
      map_sum_eq_convFin m (fun i => X i.castSucc) (fun i => hX _)
        (hind.precomp (Fin.castSucc_injective m)), convFin]

/-- The law of `X₀ + ⋯ + X_{n-1}` for iid `Xᵢ ∼ μ` is `convFin n μ`. -/
theorem map_sum_range_eq_convFin {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {X : ℕ → Ω → ℤ} {μ : Measure ℤ} (hX : ∀ i, Measurable (X i))
    (hind : iIndepFun X P) (hlaw : ∀ i, P.map (X i) = μ) (n : ℕ) :
    P.map (fun ω => ∑ i ∈ Finset.range n, X i ω) = convFin n (fun _ => μ) := by
  have e : (fun ω => ∑ i ∈ Finset.range n, X i ω) = fun ω => ∑ i : Fin n, X i ω := by
    funext ω; exact (Fin.sum_univ_eq_sum_range (fun i => X i ω) n).symm
  rw [e, map_sum_eq_convFin n (fun i : Fin n => X i) (fun i => hX i)
    (hind.precomp Fin.val_injective)]
  simp only [hlaw]

/-- A window of `c` consecutive integers carries at most `lconc μ c`. -/
theorem window_le_ofReal_lconc (μ : Measure ℤ) [IsFiniteMeasure μ] (c : ℕ) (x : ℤ) :
    μ (Set.Ico x (x + c)) ≤ ENNReal.ofReal (lconc μ c) := by
  rw [← ENNReal.ofReal_toReal (measure_ne_top μ _)]
  exact ENNReal.ofReal_le_ofReal (window_le_lconc μ c x)

end

end PGM
