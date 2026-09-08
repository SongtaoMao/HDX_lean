import HDXLean.RiemannRochEvaluation
import HDXLean.AlgebraicGeometryCauchyBinet
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-!
# Multiplication matrices in a basis of point evaluations

The evaluation basis, actual linear matrix entries, and rank-one coordinate
factorization are constructed here rather than supplied as final certificates.
These are non-algorithmic linear-algebra steps from Section 4.
-/

namespace HDXLean.EvaluationMultiplication

open scoped BigOperators

variable {F W I : Type*} [Field F] [DecidableEq F]
  [AddCommGroup W] [Module F W] [FiniteDimensional F W] [Fintype I]

omit [DecidableEq F] [Fintype I] in
/-- A spanning family of evaluations contains a basis of the correct size.
The selected point indices are obtained from membership in the actual
evaluation family, not assumed as a separate construction field. -/
theorem exists_evaluation_basis {t : ℕ} (e : I → Module.Dual F W)
    (hspan : Submodule.span F (Set.range e) = ⊤)
    (hdim : Module.finrank F W = t) :
    ∃ b : Module.Basis (Fin t) F (Module.Dual F W),
      ∀ i, ∃ j, e j = b i := by
  classical
  let b := Module.Basis.ofSpan hspan.ge
  let := FiniteDimensional.fintypeBasisIndex b
  have hc : Fintype.card _ = t :=
    (Module.finrank_eq_card_basis b).symm.trans
      (Subspace.dual_finrank_eq.trans hdim)
  let reindex := (Fintype.equivFin _).trans (finCongr hc)
  refine ⟨b.reindex reindex, ?_⟩
  intro i
  rw [Module.Basis.reindex_apply]
  exact Module.Basis.ofSpan_subset hspan.ge ⟨reindex.symm i, rfl⟩

section Matrix

variable {U V : Type*} [AddCommGroup U] [Module F U]
  [AddCommGroup V] [Module F V]
variable {t k m : ℕ}

/-- The matrix entry is literally evaluation of the product function by
the functional represented by the coordinate vector. -/
noncomputable def entry (b : Module.Basis (Fin t) F (Module.Dual F W))
    (multiply : U →ₗ[F] V →ₗ[F] W) (u : Fin k → U) (v : Fin m → V)
    (r : Fin k) (c : Fin m) : CoordinateSpace F t →ₗ[F] F :=
  (Module.Dual.eval F W (multiply (u r) (v c))).comp b.equivFun.symm.toLinearMap

omit [DecidableEq F] [FiniteDimensional F W] [Fintype I] in
/-- Evaluating the actual multiplication matrix at a selected point is
rank one, by multiplicativity of that point evaluation. -/
theorem entry_at_point (b : Module.Basis (Fin t) F (Module.Dual F W))
    (multiply : U →ₗ[F] V →ₗ[F] W) (u : Fin k → U) (v : Fin m → V)
    (e : I → Module.Dual F W) (eU : I → Module.Dual F U)
    (eV : I → Module.Dual F V)
    (hmul : ∀ i u v, e i (multiply u v) = eU i u * eV i v)
    (i : I) (r : Fin k) (c : Fin m) :
    entry b multiply u v r c (b.equivFun (e i)) = eU i (u r) * eV i (v c) := by
  change b.equivFun.symm (b.equivFun (e i)) (multiply (u r) (v c)) = _
  rw [b.equivFun.symm_apply_apply, hmul]

/-- Construction of the legacy multiplication-matrix interface from
primitive function multiplication and point evaluations. -/
noncomputable def matrixData (b : Module.Basis (Fin t) F (Module.Dual F W))
    (multiply : U →ₗ[F] V →ₗ[F] W) (u : Fin k → U) (v : Fin m → V)
    (e : I → Module.Dual F W) (eU : I → Module.Dual F U)
    (eV : I → Module.Dual F V)
    (hmul : ∀ i u v, e i (multiply u v) = eU i u * eV i v)
    (D : DirectionSet F t I) (hD : ∀ i, D.representative i = b.equivFun (e i)) :
    MultiplicationMatrixData D where
  Row := Fin k
  Column := Fin m
  entry := entry b multiply u v
  uEvaluation i r := eU i (u r)
  zEvaluation i c := eV i (v c)
  entry_at_evaluation := by
    intro i r c
    rw [hD]
    exact entry_at_point b multiply u v e eU eV hmul i r c

omit [DecidableEq F] [FiniteDimensional F W] [Fintype I] in
/-- Expanding a functional in an evaluation basis produces the literal
`U * diagonal x * Z^T` formula. -/
theorem entry_eq_sum (b : Module.Basis (Fin t) F (Module.Dual F W))
    (multiply : U →ₗ[F] V →ₗ[F] W) (u : Fin k → U) (v : Fin m → V)
    (e : I → Module.Dual F W) (eU : I → Module.Dual F U)
    (eV : I → Module.Dual F V)
    (hmul : ∀ i u v, e i (multiply u v) = eU i u * eV i v)
    (selected : Fin t → I) (hselected : ∀ i, e (selected i) = b i)
    (r : Fin k) (c : Fin m) (x : CoordinateSpace F t) :
    entry b multiply u v r c x =
      ∑ i, eU (selected i) (u r) * x i * eV (selected i) (v c) := by
  have hx := b.sum_repr (b.equivFun.symm x)
  have he := LinearMap.congr_fun hx (multiply (u r) (v c))
  change b.equivFun.symm x (multiply (u r) (v c)) = _
  rw [← he]
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro i _
  have hcoord : b.repr (b.equivFun.symm x) i = x i := by
    rw [← Module.Basis.equivFun_apply, b.equivFun.apply_symm_apply]
  rw [hcoord, ← hselected, hmul]
  ring

/-- The structural factorization is filled internally once the basis
points have been selected. It is not an independent literature assumption. -/
noncomputable def factorization (b : Module.Basis (Fin t) F (Module.Dual F W))
    (multiply : U →ₗ[F] V →ₗ[F] W) (u : Fin k → U) (v : Fin m → V)
    (e : I → Module.Dual F W) (eU : I → Module.Dual F U)
    (eV : I → Module.Dual F V)
    (hmul : ∀ i u v, e i (multiply u v) = eU i u * eV i v)
    (selected : Fin t → I) (hselected : ∀ i, e (selected i) = b i)
    (D : DirectionSet F t I) (hD : ∀ i, D.representative i = b.equivFun (e i)) :
    CoordinateRankOneFactorization D
      (matrixData b multiply u v e eU eV hmul D hD) where
  coordinateU r i := eU (selected i) (u r)
  coordinateZ c i := eV (selected i) (v c)
  entry_eq_sum_rankOne := by
    intro r c x
    exact entry_eq_sum b multiply u v e eU eV hmul selected hselected r c x

end Matrix

end HDXLean.EvaluationMultiplication
