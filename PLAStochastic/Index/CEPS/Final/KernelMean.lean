import PLAStochastic.Index.CEPS.Final.KernelDefs
import PLAStochastic.Index.CEPS.Total.KernelCoefficients
import PLAStochastic.Index.CEPS.Total.MeanReality
import PLAStochastic.Index.CEPS.Total.MeanRaw

/-! # The unconditional finite-jet normal mean expansion -/

noncomputable section
open Complex MeasureTheory PowerSeries Finset
namespace PGM

/-- The first of the three normal kernel premises, with concrete finite mixed-jet coefficients. -/
theorem cepsKernel_normal_mean :
    CepsNormalMeanExpansion cepsKernelJetBase cepsNormalDn cepsKernelCs := by
  intro P
  obtain ⟨mE, HE⟩ := ceps_normal_mean_raw_expansion P
  obtain ⟨mR, HR⟩ := ceps_normal_mean_series_real P
  let m := max mE (max mR (max cepsLevelOrder (P + 3)))
  have hmE : mE ≤ m := le_max_left _ _
  have hmR : mR ≤ m := (le_max_left _ _).trans (le_max_right _ _)
  have hm6 : cepsLevelOrder ≤ m :=
    (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have hmP : P + 3 ≤ m :=
    (le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  refine ⟨m, fun D θ vlo vhi η hD hθ hvlo hv hη => ?_⟩
  obtain ⟨rE, hrE, K, E, HE'⟩ := HE D θ vlo vhi η hD hθ hvlo hv hη
  obtain ⟨rR, hrR, HR'⟩ := HR D θ vlo vhi η hD hθ hvlo hv hη
  obtain ⟨rJ, hrJ, HJ⟩ := ceps_normal_series_coefficients_eq_kernel P hm6 hmP
    D θ vlo vhi η hθ hvlo hη
  refine ⟨min rE (min rR rJ), lt_min hrE (lt_min hrR hrJ), K, E,
    fun eps heps ν hν => ?_⟩
  have he := HE' eps heps ν (hν.mono hmE (min_le_left _ _))
  have hr := HR' ν (hν.mono hmR ((min_le_right _ _).trans (min_le_left _ _)))
  have hj := HJ ν (hν.mono (le_refl m) ((min_le_right _ _).trans (min_le_right _ _)))
  have hc (j : ℕ) (hjp : j ≤ P) :
      coeff j (cepsScaledMeanSeries
          ((cepsLevelDomain (cepsLevelIndex ν)).contour η hη)
          ((ν : Measure ℝ).map fun x => 1 - x) P) =
        (cepsKernelCs j (cepsJetLaw ν) : ℂ) := by
    have hji := (hj j hjp 0).2
    have him := hr j hjp
    rw [hji] at him
    rw [hji]
    apply Complex.ext
    · rfl
    · simpa only [ofReal_im] using him
  convert he using 2
  apply congrArg (fun t : ℂ => cepsNormalDn eps ν + t)
  apply sum_congr rfl
  intro j hjp
  rw [hc j (by have := mem_range.mp hjp; omega)]
  simp only [cepsKernelJetBase, ofReal_mul]

end PGM
