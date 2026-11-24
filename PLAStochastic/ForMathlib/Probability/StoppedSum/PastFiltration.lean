import PLAStochastic.ForMathlib.Probability.StoppedSum.IndepIncrements

/-!
# The strict past of an independent sequence

For measurable `X : ℕ → Ω → ℝ` the strict past `pastFiltration X _ t = σ(X 0, …, X (t - 1))`
is a filtration, and for an independent sequence the increments `X t - c` are independent of
the strict past: `IndepIncrements P (pastFiltration X _) (fun t ω => X t ω - c)`. This is the
input of the Kolmogorov maximal inequality for partial sums of independent variables.
-/

namespace PGM

open MeasureTheory ProbabilityTheory

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {X : ℕ → Ω → ℝ}

/-- The strict past `σ(X 0, …, X (t - 1))` of a sequence. -/
def pastFiltration (X : ℕ → Ω → ℝ) (hX : ∀ t, Measurable (X t)) : Filtration ℕ mΩ where
  seq t := ⨆ s ∈ Set.Iio t, MeasurableSpace.comap (X s) inferInstance
  mono' := fun _ _ hst => biSup_mono fun _ hs => lt_of_lt_of_le hs hst
  le' := fun _ => iSup₂_le fun s _ => (hX s).comap_le

theorem pastFiltration_measurable_lt (hX : ∀ t, Measurable (X t)) {s t : ℕ} (hst : s < t) :
    Measurable[pastFiltration X hX t] (X s) :=
  (comap_measurable (X s)).mono (le_iSup₂ (f := fun s (_ : s ∈ Set.Iio t) =>
    MeasurableSpace.comap (X s) inferInstance) s hst) le_rfl

/-- The centred terms of an independent sequence have independent increments for the strict
past. -/
theorem indepIncrements_pastFiltration (hX : ∀ t, Measurable (X t)) (hi : iIndepFun X P)
    (c : ℝ) : IndepIncrements P (pastFiltration X hX) (fun t ω => X t ω - c) where
  measurable t := (pastFiltration_measurable_lt hX (Nat.lt_succ_self t)).sub_const c
  indep t := by
    have hd : Disjoint ({t} : Set ℕ) (Set.Iio t) := by simp
    have hind := indep_iSup_of_disjoint (fun k => (hX k).comap_le) hi.iIndep hd
    simp only [Set.mem_singleton_iff, iSup_iSup_eq_left] at hind
    exact indep_of_indep_of_le_left hind ((comap_measurable (X t)).sub_const c).comap_le

end PGM
