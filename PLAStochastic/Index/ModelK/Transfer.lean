import PLAStochastic.Index.ModelK.ConstantDensity

/-!
# Model K transfer for a general density

Let `X 0, X 1, …` be iid with a Model K density `f` on `[A, B]` (`DensityK`), and let the keys
for sample size `n` be the sorted first `n` samples (`kKeys X n`).  By the Rényi representation
(`identDistrib_sortVec_quantK_gammaRatio`), the sorted sample has the law of
`quantK f A B (Γ (i+1) / Γ (n+1))`, where `Γ (t+1) = E 0 + ⋯ + E t` (`expPartial t`) are the
partial sums of the canonical iid `Exp(1)` sequence.  Hence the expectation of any height that
reads only the first `n` keys transfers to the canonical sequence (`integral_height_kKeys`),
in particular for both heights (`integral_epHeight_kKeys`, `integral_reHeight_kKeys`).
-/

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory Finset

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {f : ℝ → ℝ} {A B fmin fmax Lf : ℝ}

/-- The partial sum `Γ (t+1) = E 0 + ⋯ + E t` of the canonical iid `Exp(1)` sequence. -/
def expPartial (t : ℕ) (ω : ℕ → ℝ) : ℝ := ∑ i ∈ range (t + 1), expCoord i ω

theorem measurable_expPartial (t : ℕ) : Measurable (expPartial t) :=
  Finset.measurable_sum _ fun i _ => measurable_expCoord i

theorem expPartial_succ (t : ℕ) (ω : ℕ → ℝ) :
    expPartial (t + 1) ω = expPartial t ω + expCoord (t + 1) ω :=
  Finset.sum_range_succ _ _

theorem expPartial_eq (t : ℕ) (ω : ℕ → ℝ) :
    expPartial t ω = expCoord 0 ω + ∑ i ∈ range t, expCoord (i + 1) ω := by
  rw [expPartial, Finset.sum_range_succ', add_comm]

/-- **Transfer for a height reading the first `n` keys.**  Its expectation on the Model K keys
equals its expectation on the keys `quantK f A B (Γ (t+1) / Γ (n+1))` of the canonical iid
`Exp(1)` sequence. -/
theorem integral_height_kKeys (hf : DensityK f A B fmin fmax Lf)
    {X : ℕ → Ω → ℝ} (hX : ∀ i, HasLaw (X i) (densityLaw f A B) P) (hind : iIndepFun X P)
    {n : ℕ} {h : (ℕ → ℝ) → ℕ} (hmeas : Measurable fun v : Fin n → ℝ => h (extendKeys v))
    (hcongr : ∀ p p' : ℕ → ℝ, (∀ i < n, p i = p' i) → h p = h p') :
    ∫ ω, (h (kKeys X n ω) : ℝ) ∂P =
      ∫ ω', (h (fun t => quantK f A B (expPartial t ω' / expPartial n ω')) : ℝ)
        ∂expSeqMeasure := by
  have hXn : iIndepFun (fun i : Fin n => X i) P := hind.precomp Fin.val_injective
  have hEn : iIndepFun (fun j : Fin (n + 1) => expCoord j) expSeqMeasure :=
    iidSeq_expCoord.indep.precomp Fin.val_injective
  have hid := identDistrib_sortVec_quantK_gammaRatio hf (fun i : Fin n => hX i) hXn
    (fun j : Fin (n + 1) => hasLaw_expCoord j) hEn
  have hu : Measurable fun v : Fin n → ℝ => (h (extendKeys v) : ℝ) :=
    measurable_from_nat.comp hmeas
  have hint := (hid.comp hu).integral_eq
  simp only [Function.comp_def] at hint
  rw [show (fun ω => (h (kKeys X n ω) : ℝ)) =
    fun ω => (h (extendKeys (Renyi.sortVec fun i : Fin n => X i ω)) : ℝ) from rfl, hint]
  refine integral_congr_ae (Filter.Eventually.of_forall fun ω' => ?_)
  simp only
  congr 1
  apply hcongr
  intro i hi
  rw [extendKeys_of_lt _ hi]
  simp only [Renyi.gammaRatio]
  rw [gammaSum_expCoord ω' (k := i + 1) (by omega), gammaSum_expCoord ω' le_rfl]
  rfl

/-- **Transfer, ALG-PGM.**  The expected endpoint height on `n` sorted Model K samples equals
that on the keys `quantK f A B (Γ (t+1) / Γ (n+1))` of the canonical iid `Exp(1)` sequence. -/
theorem integral_epHeight_kKeys (hf : DensityK f A B fmin fmax Lf)
    {X : ℕ → Ω → ℝ} (hX : ∀ i, HasLaw (X i) (densityLaw f A B) P) (hind : iIndepFun X P)
    (eps : ℝ) (n : ℕ) :
    ∫ ω, (epHeight eps (kKeys X n ω) n : ℝ) ∂P =
      ∫ ω', (epHeight eps (fun t => quantK f A B (expPartial t ω' / expPartial n ω')) n : ℝ)
        ∂expSeqMeasure :=
  integral_height_kKeys (h := fun p => epHeight eps p n) hf hX hind
    (measurable_epHeight_extendKeys eps n) (fun _ _ hpp => epHeight_congr hpp)

/-- **Transfer, ALG-RE.**  The expected rank-equispaced height on `n` sorted Model K samples
equals that on the keys `quantK f A B (Γ (t+1) / Γ (n+1))` of the canonical iid `Exp(1)`
sequence. -/
theorem integral_reHeight_kKeys (hf : DensityK f A B fmin fmax Lf)
    {X : ℕ → Ω → ℝ} (hX : ∀ i, HasLaw (X i) (densityLaw f A B) P) (hind : iIndepFun X P)
    (eps : ℝ) (n : ℕ) :
    ∫ ω, (reHeight eps (kKeys X n ω) n : ℝ) ∂P =
      ∫ ω', (reHeight eps (fun t => quantK f A B (expPartial t ω' / expPartial n ω')) n : ℝ)
        ∂expSeqMeasure :=
  integral_height_kKeys (h := fun p => reHeight eps p n) hf hX hind
    (measurable_reHeight_extendKeys eps n) (fun _ _ hpp => reHeight_congr hpp)

end

end PGM
