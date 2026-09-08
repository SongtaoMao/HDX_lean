# Abelian Cayley High-Dimensional Expanders with Polylogarithmic Degree

Lean 4 formalization of the mathematical constructions in the paper, covering
both main theorems and their supporting arguments in Sections 2–5.
Cited external results are explicit mathematical inputs; their proofs are
not repeated. Algorithmic explicitness and computational complexity are
outside the formalized scope.

Repository: [SongtaoMao/HDX_lean](https://github.com/SongtaoMao/HDX_lean).

## Build

The project pins Lean and Mathlib to `v4.33.0`. With Lean installed through
Elan, run the following commands from the repository root:

```sh
lake exe cache get
lake build
```

`lean-toolchain`, `lakefile.toml`, and `lake-manifest.json` fix the toolchain
and dependencies. Do not update these pins merely to reproduce the development.
The repository contains source files, not precompiled build artifacts.

Targeted checks of the main entry points and new construction modules have
passed. A clean full build of this published snapshot has not yet been
recorded; publication itself is not a verification certificate.

## Main entry points

Import [HDXLean.MainTheoremCited](HDXLean/MainTheoremCited.lean) for the
assembled route from explicit cited data:

```lean
import HDXLean.MainTheoremCited

#check HDXLean.Paper.theorem_1_2_from_cited_data
#check HDXLean.Paper.mainTheorems_from_cited_data
```

`Paper.mainTheorems_from_cited_data` takes `Paper.CitedInputs` and proves
`Paper.MainConclusions`, the conjunction

```text
for every lambda > 0, Nonempty (TwoDimensionalFamily lambda);
for every d >= 2, Nonempty (LinearDegreeHigherDimensionalFamily d).
```

Import `HDXLean` for the entire development. The earlier entry points in
[MainTheorem.lean](HDXLean/MainTheorem.lean) remain available for compatibility;
the new route constructs their Section 4 and relation-compiler inputs and
reuses the existing proofs.

### Theorem 1.2 — Two-dimensional complexes

For every fixed `lambda > 0`, the conclusion is an infinite family of simple,
pure, unweighted, translation-invariant two-dimensional Cayley complexes
on `F₂^n`, with `n` tending to infinity. The global one-skeleton and vertex
links are connected. Each vertex-link walk has stationary mean-zero norm
at most `lambda`. Cayley degree is polynomial in `n`, and every edge has
the same triangle codegree, bounded by `O_lambda(log n)`.

`Paper.TwoDimensionalCitedInput` supplies a common cited curve/Riemann–Roch
model and tower, determinantal and finite-field trace facts, and the cited
origin-link propagation statement. Direction sets, matrix entries, genericity,
independent minors, and the actual quotient-complex compiler are constructed
internally from those inputs.

### Theorem 1.3 — Higher-dimensional complexes

For each fixed `d >= 2`, the conclusion is an infinite family of pure,
measured, translation-invariant abelian Cayley complexes of dimension `d`
on binary vector spaces. All positive-dimensional links, including the
global one-skeleton, are connected. Every codimension-two link has two-sided
stationary mean-zero norm at most `1/d`. Cayley degree is `Theta_d(n)`, where
`n` is the ambient binary dimension and the number of vertices is `2^n`.

The input is `GolowichProduct.LiteratureInput` in
[GolowichCited.lean](HDXLean/GolowichCited.lean). Its two fields state the
cited product construction and nonempty-link theorem. The remaining
construction, measure, coordinate, and spectral deductions are internal.

Here local expansion does not mean a uniform global spectral gap or a
`1/d` bound for links of every dimension.

## Correspondence with the paper

| Paper part | Main source files |
| --- | --- |
| Shared graphs, measured complexes, links, and Cayley semantics | [Basic](HDXLean/Basic.lean), [Families](HDXLean/Families.lean) |
| Section 2: actual quotient construction and relation compiler | [RelationQuotient](HDXLean/RelationQuotient.lean), [RelationTriangleComplex](HDXLean/RelationTriangleComplex.lean), [RelationCompilerAssembly](HDXLean/RelationCompilerAssembly.lean) |
| Section 3: affine relation matrices, kernels, and spectra | [AffineRelation](HDXLean/AffineRelation.lean), [AffineRelationKernel](HDXLean/AffineRelationKernel.lean), [AffineRelationSpectrum](HDXLean/AffineRelationSpectrum.lean), [SectionThreeFamily](HDXLean/SectionThreeFamily.lean) |
| Section 4: common cited curve model and direction/minor construction | [CurveRiemannRochCited](HDXLean/CurveRiemannRochCited.lean), [CurveRiemannRochLevel](HDXLean/CurveRiemannRochLevel.lean), [CurveTowerAssembly](HDXLean/CurveTowerAssembly.lean) |
| Section 4: polynomial independence and evaluation | [OneGenericMatrix](HDXLean/OneGenericMatrix.lean), [PolynomialMinorBridge](HDXLean/PolynomialMinorBridge.lean), [BooleanCubeMinorExpansion](HDXLean/BooleanCubeMinorExpansion.lean), [EvaluationProductRealization](HDXLean/EvaluationProductRealization.lean) |
| Section 5: graph products, skeleton measures, and local expansion | [GolowichCited](HDXLean/GolowichCited.lean), [MeasuredSkeleton](HDXLean/MeasuredSkeleton.lean), [SectionFiveFormalized](HDXLean/SectionFiveFormalized.lean), [GolowichProduct](HDXLean/GolowichProduct.lean) |
| Global spectral gap and exact codimension-two eigenvalue | [ProductExactSpectrum](HDXLean/ProductExactSpectrum.lean) |
| Both main conclusions | [MainTheoremCited](HDXLean/MainTheoremCited.lean) |

The actual quotient construction includes dimension equal to matrix nullity,
binary coordinate transport, uniform measure, exact degree and codegree,
global connectedness, and identification of the native origin link with
the counting-Gram graph.

The Section 4 construction uses one common evaluation basis for directions,
matrix coordinates, and product reconstruction. It derives 1-genericity
after scalar extension and transports polynomial independence to independence
of functions on the finite coordinate space.

## Cited inputs and verification boundaries

- The curve and tower input is an axiomatic function-space presentation of
  the cited Garcia–Stichtenoth and Stichtenoth results. It includes actual
  subspaces, algebra-map evaluations, Riemann–Roch dimensions, zero bounds,
  and geometric integrality. It is not a separate scheme-level construction
  or a reproof of Riemann–Roch.
- `EisenbudMinimalGeneratorsInput` is a general combined determinantal
  corollary of Eisenbud's Theorem 6.4 and Corollary A2.61. The intervening
  general height, grade, and localization normalization remains within
  this cited boundary; actual matrix genericity and coefficient transport
  are proved internally.
- `RelationCompiler.OriginLinkPropagationInput` states the cited propagation
  from the actual origin link to all vertex links. It does not assume the
  full compiler output, dimension, degree, or counting conclusions.
- Finite-field trace and Golowich product results retain their explicit
  hypotheses. Exact-spectrum statements use a separate `ExactSpectrumInput`.
- The separately cited optimal-degree comparison is in
  [OptimalDegreeCited.lean](HDXLean/OptimalDegreeCited.lean), not part of
  `MainConclusions`.

A successful Lean check proves the displayed implication relative to its
inputs. It does not by itself prove consistency of all cited assumptions
or establish that their mathematical interpretation matches every sentence
in the manuscript. Illustrative examples and discussion statements are
not all separately formalized. Open problems are not asserted as solved.

The earlier `WeightedLift*` modules are retained mathematical proofs for
a preceding construction. The current Theorem 1.3 uses the graph-product
route instead. No algorithm, encoding procedure, or complexity guarantee
is claimed by this repository.
