import PLAStochastic.Index.CEPS.Jets.JF

/-!
# X8: jets on signed densities and the interface JF

Entry point of `Index/CEPS/Jets/`:

* `cepsJet`, `cepsJetLaw`, `cepsJetCoeff`, `cepsJetCode`, `cepsJetWeight`, `cepsJetDim`
  (`Jets.Basic`, `Jets.Defs`): the jet vector (cumulants `κ_{k+2}` and the contour jets
  `∂_q^n ∂_ζ^m ∂_μ^j L(0; 0, 0)` on the fixed line `cepsJetLine`), its codes and weights, and the
  JF coefficients;
* `cepsJet_cumulant_eq`, `cepsJet_contour_eq`, `cepsJetLaw_eq_cepsJet` (`Jets.Consistency`):
  agreement with the derivatives of `cepsCgf` and of `CepsCanonDomain.canonL` at the origin;
* `cepsJetCoeff_triangular`, `cepsJetLaw_expansion`, `cepsJF_of_eq` (`Jets.Defs`, `Jets.JF`):
  the interface `CepsJF`.
-/
