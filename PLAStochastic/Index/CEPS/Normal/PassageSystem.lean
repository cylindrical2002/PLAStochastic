import PLAStochastic.Index.CEPS.Normal.Algebra

/-! # The full normal two-passage system and its unique solution -/

noncomputable section
open Complex
namespace PGM.CepsNormalData

variable (a : CepsNormalData) (L : ℂ → ℂ → ℂ → ℂ) (μ q l : ℂ)

def PassageSystem (u v : ℂ → ℂ) : Prop :=
  (∀ t, u t = 1 - (a.βp - t) * exp (L μ q t) -
    a.overshootPlus L μ q (a.βp - t) * v a.βp) ∧
  (∀ t, v t = exp ((a.βm - t) * l) * a.overshootMinus L μ q (t - a.βm) *
    (1 - u a.βm))

theorem passageXY_system (hQp : a.Q a.βp ≠ 0) (hQm : a.Q a.βm ≠ 0)
    (hΔ : a.delta L μ q l ≠ 0) :
    a.passageX L μ q l = a.eta * exp (L μ q a.βm) +
      a.overshootPlus L μ q a.eta * a.passageY L μ q l := by
  unfold passageY passageX
  field_simp [hΔ]
  rw [delta, pi_eq_overshoots a L μ q hQp hQm]
  ring

theorem upperExit_rootMinus (hQp : a.Q a.βp ≠ 0) (hQm : a.Q a.βm ≠ 0)
    (hΔ : a.delta L μ q l ≠ 0) :
    1 - a.upperExit L μ q a.βm l = a.passageX L μ q l := by
  rw [upperExit, ← eta, passageXY_system a L μ q l hQp hQm hΔ]
  ring

theorem lowerExit_rootPlus : a.lowerExit L μ q a.βp l = a.passageY L μ q l := by
  unfold lowerExit passageY
  rw [← eta]
  have he : (a.βm - a.βp) * l = -a.eta * l := by rw [eta]; ring
  rw [he]
  rfl

theorem passageSystem_exits (hQp : a.Q a.βp ≠ 0) (hQm : a.Q a.βm ≠ 0)
    (hΔ : a.delta L μ q l ≠ 0) :
    a.PassageSystem L μ q l (fun t => a.upperExit L μ q t l)
      (fun t => a.lowerExit L μ q t l) := by
  constructor
  · intro t
    dsimp
    rw [lowerExit_rootPlus]
    rfl
  · intro t
    dsimp
    rw [upperExit_rootMinus a L μ q l hQp hQm hΔ]
    rfl

/-- C-7(i): the complete functions solving the normal two-passage equations are unique. -/
theorem passageSystem_unique (hQp : a.Q a.βp ≠ 0) (hQm : a.Q a.βm ≠ 0)
    (hΔ : a.delta L μ q l ≠ 0) :
    ∃! p : (ℂ → ℂ) × (ℂ → ℂ), a.PassageSystem L μ q l p.1 p.2 := by
  refine ⟨((fun t => a.upperExit L μ q t l), (fun t => a.lowerExit L μ q t l)),
    passageSystem_exits a L μ q l hQp hQm hΔ, ?_⟩
  intro p hp
  have hReduced :
      (1 - p.1 a.βm) = a.eta * exp (L μ q a.βm) +
        a.overshootPlus L μ q a.eta * p.2 a.βp ∧
      p.2 a.βp = a.decay l * a.overshootMinus L μ q a.eta * (1 - p.1 a.βm) := by
    constructor
    · have h := hp.1 a.βm
      rw [← eta] at h
      linear_combination -h
    · have h := hp.2 a.βp
      rw [← eta] at h
      have he : (a.βm - a.βp) * l = -a.eta * l := by rw [eta]; ring
      simpa only [he, decay] using h
  obtain ⟨s, hs, huniq⟩ := passage_system_unique a L μ q l hQp hQm hΔ
  have hActual := huniq (1 - p.1 a.βm, p.2 a.βp) hReduced
  have hExplicit := huniq (a.passageX L μ q l, a.passageY L μ q l)
    ⟨passageXY_system a L μ q l hQp hQm hΔ, rfl⟩
  have hcoord := hActual.trans hExplicit.symm
  have hx := congrArg Prod.fst hcoord
  have hy := congrArg Prod.snd hcoord
  dsimp at hx hy
  apply Prod.ext
  · funext t
    rw [hp.1 t, hy]
    rfl
  · funext t
    rw [hp.2 t, hx]
    rfl

end PGM.CepsNormalData
