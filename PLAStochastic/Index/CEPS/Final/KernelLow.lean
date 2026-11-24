import PLAStochastic.Index.CEPS.Final.KernelDefs
import PLAStochastic.Index.CEPS.Total.KernelCoefficients
import PLAStochastic.Index.CEPS.Total.LowRaw

/-! # The unconditional finite-jet normal low-frequency expansion -/

noncomputable section
open Complex MeasureTheory PowerSeries Finset
namespace PGM

/-- The second normal kernel premise, with concrete finite mixed-jet coefficients. -/
theorem cepsKernel_normal_low :
    CepsNormalLowExpansion cepsKernelJetBase cepsNormalGn cepsKernelGk := by
  intro N
  obtain ⟨mE, HE⟩ := ceps_normal_low_raw_expansion N
  let m := max mE (max cepsLevelOrder (N + 3))
  have hmE : mE ≤ m := le_max_left _ _
  have hm6 : cepsLevelOrder ≤ m := (le_max_left _ _).trans (le_max_right _ _)
  have hmN : N + 3 ≤ m := (le_max_right _ _).trans (le_max_right _ _)
  refine ⟨m, fun D θ vlo vhi η hD hθ hvlo hv hη => ?_⟩
  obtain ⟨rE, hrE, K, R, E, hR, HE'⟩ := HE D θ vlo vhi η hD hθ hvlo hv hη
  obtain ⟨rJ, hrJ, HJ⟩ := ceps_normal_series_coefficients_eq_kernel N hm6 hmN
    D θ vlo vhi η hθ hvlo hη
  refine ⟨min rE rJ, lt_min hrE hrJ, K, R, E, hR, N + 4,
    fun eps heps ν hν y hy => ?_⟩
  have he := HE' eps heps ν (hν.mono hmE (min_le_left _ _)) y hy
  have hj := HJ ν (hν.mono (le_refl m) (min_le_right _ _))
  convert he using 2
  apply congrArg (fun t : ℂ => cepsNormalGn eps ν (I * y) - t)
  apply sum_congr rfl
  intro j hjp
  rw [(hj j (by have := mem_range.mp hjp; omega) y).1]
  rfl

end PGM
