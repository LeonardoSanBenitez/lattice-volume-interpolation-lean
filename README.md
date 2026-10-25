# Lean formalization of *Interpolating between volume and lattice point enumerator with successive minima*

This repository contains machine-checked Lean 4 and Mathlib proofs for the mathematical results in Ansgar Freyer and Eduardo Lucas's paper [*Interpolating between volume and lattice point enumerator with successive minima*](https://link.springer.com/article/10.1007/s00605-022-01713-1) (Monatshefte für Mathematik 198 (2022), 717–740). Statement and equation numbers follow the published version; the mathematics was read from [arXiv:2105.13090v2](https://arxiv.org/abs/2105.13090v2). I am not an author of the paper; this is an independent formalization intended to make its results mechanically checkable and reusable.

The development proves Theorems 1.1, 1.3 and 1.4, Corollary 1.2, Propositions 1.5 and 1.6, the anti-blocking reduction (Theorem 3.1 with Lemmas 3.2 and 3.3 and Claims 1 and 2), Claim 3, Lemmas 5.1–5.3, the equality and sharpness cases stated in the paper, and the consequences the paper draws from Conjecture 2 (as implications with the conjecture as an explicit hypothesis; the limit $\operatorname{vol}(rK)/G(rK)\to1$ is also proved unconditionally). Results the paper cites and uses are proved as well: Minkowski's second theorem in both directions, van der Corput's theorem, Davenport's inequality, the Rogers–Shephard inequality in the form of Eq. (4.1), the covering-radius bound (4.2), Pick's theorem for convex lattice polygons, the Henk–Schürmann–Wills boundary inequality (5.2), and the Betke–Henk–Wills lattice-point bound in dimensions 2 and 3. Conjectures 1 and 2 and the three bounds quoted only for context (the Betke–Henk–Wills two-sided bound, Malikiosis's bound (1.3) and Schymura's inequality (1.11)) are stated as Lean propositions and are neither proved nor assumed.

Every declaration named in `catalog.json` compiles without proof placeholders under the pinned toolchain, and `#print axioms` reports only `propext`, `Classical.choice` and `Quot.sound` for each of them.

## Build

Install Lean through [elan](https://github.com/leanprover/elan), then run from the repository root:

```text
lake exe cache get
lake build
```

The toolchain is Lean `v4.31.0` with the matching Mathlib release. The project depends on [discrete-minkowski-lean](https://github.com/LeonardoSanBenitez/discrete-minkowski-lean), a formalization of Tointon's *New bounds in the discrete analogue of Minkowski's second theorem*, pinned to a fixed commit; it supplies the successive minima, the gauge bridges and the upper half of Minkowski's second theorem. Corollary 1.2 is stated there as an assumption, `DiscreteMinkowski.FreyerLucasBound`, and is proved here in exactly that form.

To check the axioms of any result, add a line such as `#print axioms LatticeVolumeInterpolation.theorem_1_1_upper` to a file that imports `LatticeVolumeInterpolation`.

## Where each result is

`catalog.json` lists every statement of the paper with its location, the Lean declarations that formalize it, its dependencies, any added hypothesis, the proof route where it differs from the paper's, and remarks on the printed text. The main theorems:

| Paper | Lean declaration |
|---|---|
| Theorem 1.1, Eq. (1.8) | `theorem_1_1_upper` |
| Theorem 1.1, Eq. (1.9) | `theorem_1_1_lower` |
| Corollary 1.2 | `corollary_1_2` |
| Theorem 1.3, Eq. (1.12) and its tightness | `theorem_1_3_paper`, `theorem_1_3_tight_for_boxes` |
| Theorem 1.4, Eqs. (1.13), (1.14) and the product form | `theorem_1_4_upper`, `theorem_1_4_lower`, `theorem_1_4_lower_product_form` |
| Proposition 1.5 | `proposition_1_5_symmetric_lattice_polygon` |
| Proposition 1.6, Eqs. (1.15), (1.16) and their tightness | `proposition_1_6_upper`, `proposition_1_6_lower`, `proposition_1_6_tight_for_cubes` |
| Theorem 3.1 | `theorem_3_1` |
| Lemmas 3.3, 5.1, 5.2, 5.3 | `lemma_3_3`, `lemma_5_1`, `concave_integral_chord_le` and `concave_integral_le_tangent`, `lemma_5_3` |

All names are in the namespace `LatticeVolumeInterpolation`.

## Files

Definitions and notation:

- `LviBasic.lean` imports the discrete-minkowski dependency that the development builds on.
- `PaperNotation.lean` defines the class of convex bodies, the support function and the lattice point enumerator, and proves the support function is an attained maximum.
- `SuccessiveMinimaBridge.lean` states the central symmetral, the gauge and the successive minima in the paper's notation.
- `GaugeMinima.lean` proves that each successive minimum is the least gauge of a lattice vector outside the span of the previous minimal vectors, including when minima coincide.
- `DilationBridge.lean` proves that dilating a body is equivalent to refining the lattice, for lattice counts and successive minima.
- `StandardLattice.lean` sets up $\mathbb Z^n$ as a discrete, spanning lattice of covolume one.
- `CoordinateLattice.lean`, `BoxCounts.lean` and `CoordinateMinima.lean` count lattice points of axis-parallel boxes and compute their successive minima.
- `RealRectangles.lean` handles boxes with real side lengths.

Section 1 (statements quoted from other work, equality cases):

- `MinkowskiLower.lean` proves the lower bound of Minkowski's second theorem by the convex hull of segments realizing the minima.
- `MinkowskiBounds.lean` assembles both bounds of Eq. (1.2) and proves that the simplex and the cube attain them.
- `ProductBoundLimit.lean` proves that any bound of the form (1.4) implies Minkowski's upper bound, by the limit over refined lattices.
- `PaperConjectures.lean` states Conjectures 1 and 2.
- `QuotedStatements.lean` states the Betke–Henk–Wills two-sided bound, Malikiosis's bound (1.3) and Schymura's inequality (1.11).
- `UniversalConjectureBounds.lean` derives the two universal bounds that follow from Conjecture 2.
- `RatioConjectureLimit.lean` derives the limit $\operatorname{vol}(rK)/G(rK)\to1$ from Conjecture 2; `UnconditionalRatioLimit.lean` proves it without the conjecture, from Proposition 1.6.
- `BoxEquality.lean` proves the equality cases of Conjecture 1 and of Eq. (1.7) for integer boxes.
- `SimplexCounts.lean`, `SimplexLattice.lean`, `SimplexInteriorCounts.lean`, `SimplexInteriorLattice.lean`, `SimplexMinima.lean`, `SimplexVolume.lean` and `SimplexEquality.lean` count the lattice points of integer dilates of the standard simplex and of their interiors, compute $\lambda_i(mT_n)=2/m$ and $\operatorname{vol}(mT_n)=m^n/n!$, and prove that these dilates attain Eqs. (1.5) and (1.6).
- `EqualityCasesPaperNotation.lean` states the box and simplex equality cases with $G(B)$ and $G(\operatorname{int}B)$, and proves the sharpness of the lattice-tile display.
- `ThinBoxComparison.lean` proves the comparison of the constants in Eqs. (1.15) and (1.8) for the elongated box after Proposition 1.6.

Dimensions 2 and 3 of Conjecture 1 (cited in Section 1, proved following Malikiosis's argument):

- `SeparatedIntervals.lean`, `SeparatedRows.lean` and `MinimaDifferenceAvoidance.lean` prove the one-dimensional separated-interval count, its residue-grouped planar form, and that the minima keep scaled lattice differences out of the difference body.
- `PlanarFloorProduct.lean` proves $G(K)\le\lfloor2/\lambda_1+1\rfloor\lfloor2/\lambda_2+1\rfloor$ for every planar convex body.
- `LatticeEmptyTranslate.lean`, `LatticeCosetTranslate.lean`, `LatticePeriodLines.lean`, `SeparatedPlanarFamily.lean`, `PlanarPeriodAlignment.lean`, `PlanarRankTwo.lean` and `RepairedPlanarFamily.lean` prove the planar family theorem that the three-dimensional case slices into.
- `AdaptedMinimaCoordinates.lean`, `SpatialSlices.lean`, `SpatialPeriodBound.lean` and `SpatialFloorProduct.lean` prove the three-dimensional bound for every convex body in $\mathbb R^3$.

Section 2:

- `VanDerCorput.lean` proves van der Corput's theorem by averaging over a fundamental domain.
- `ProjectedLattice.lean` and `ProjectedLatticeInstances.lean` prove that the projection of a lattice along a lattice subspace is a lattice.

Section 3 (anti-blocking bodies):

- `AntiBlocking.lean` defines anti-blocking bodies, sections and projections onto coordinate subspaces.
- `CoordShaking.lean` defines the Blaschke shaking along a coordinate direction and proves that it is compact and convex, preserves volume, and does not decrease the lattice point count (Lemma 3.2 v)).
- `ShakingInterior.lean` proves Lemma 3.2 vi).
- `GeneralOrthShaking.lean` proves Lemma 3.2 i)–iv) for an arbitrary direction in any dimension.
- `ShakingIterate.lean` iterates the shakings and proves Claim 2.
- `ClaimOne.lean` proves Claim 1.
- `Triangularize.lean` makes the minimal vectors upper triangular by a unimodular change of coordinates.
- `Unimodular.lean` proves that volume, lattice counts and successive minima are invariant under it.
- `TheoremThreeOne.lean` proves Theorem 3.1.
- `MinimaAntiBlocking.lean` proves Lemma 3.3.

Section 4:

- `BetaIntegral.lean`, `JoinVolume.lean`, `WeightedSimplex.lean` and `GeneralRogersShephard.lean` prove Eq. (4.1) for every compact convex body.
- `Davenport.lean` proves Davenport's inequality for anti-blocking bodies by the prism decomposition after the proof of Theorem 1.1.
- `ProjectionShaking.lean` and `GeneralDavenport.lean` prove Davenport's inequality for every compact convex body.
- `AntiBlockingUpperBound.lean` and `TheoremOneOne.lean` prove Eq. (1.8) for anti-blocking bodies; `UpperBound.lean` proves Eq. (1.8) in general and Corollary 1.2.
- `CoveringRadius.lean` and `CoveringRadiusAttainment.lean` define the covering radius, prove the minimum is attained, and prove Eq. (4.2).
- `CoveringTile.lean` proves Eq. (1.15) with the paper's tile; `PropOneSix.lean` proves Eq. (1.16) and Eq. (1.9).
- `Tiles.lean` proves the tightness of Proposition 1.6 for cubes and the lattice-tile display.
- `ReverseSchymura.lean` proves Claim 3 and Theorem 1.3; `TheoremOneThreeTight.lean` proves its tightness for boxes.
- `OrthogonalLatticeSplit.lean`, `OrthogonalLatticeDiscrete.lean`, `ProjectedCovolume.lean` and `ProjectedDeterminantBound.lean` prove $\det(\mathbb Z^n|L_I^\perp)\ge\operatorname{vol}_k(P_I)^{-1}$, the inequality stated after Theorem 1.3.

Section 5 (the plane):

- `ConcaveIntegralBounds.lean` proves Lemma 5.2.
- `GeneralShaking.lean` defines the shaking $\mathrm{sh}_{u,\ell}$ against a line, proves its convexity and Lemma 5.3.
- `ShakingTranslations.lean` proves that the reduction does not depend on the intercept of the diagonal.
- `LemmaFiveOne.lean` proves Lemma 5.1.
- `PlanarSections.lean`, `TheoremOneFourCore.lean` and `TheoremOneFourLower.lean` count lattice points of the reduced body row by row.
- `TheoremOneFour.lean` proves Theorem 1.4, its product form and Eq. (5.3).
- `PlanarRows.lean` and `Pick.lean` prove Pick's theorem, Eq. (5.1), for convex lattice polygons.
- `BoundarySections.lean`, `BoundaryRowCount.lean`, `BoundaryMinima.lean` and `BoundaryFirstDirection.lean` prove the Henk–Schürmann–Wills inequality (5.2) for centrally symmetric lattice polygons.
- `PropOneFive.lean` proves Proposition 1.5.

`LatticeVolumeInterpolation.lean` is the umbrella module importing the complete development.

## Remarks on the printed text

These are made explicit in the formalization; none of them affects a main result.

- Eqs. (1.10) and (1.11), and the sum after the prism decomposition following the proof of Theorem 1.1, need the $k=0$ term $\operatorname{vol}_n(K)$ (the empty index set). Without it they fail already for $n=1$, $K=[0,1]$, where $G(K)=2$. The formalization sums over all $I\subseteq[n]$, as Eq. (1.12) does.
- In the Betke–Henk–Wills display before Conjecture 1, the cited Corollary 2.1 has the lower factors $2/\lambda_i-1$; the formalization records both forms.
- The recursive description of $\lambda_i$ through the gauge in Section 2 is formalized with the span of the previous minimal vectors excluded, so that it also holds when minima coincide (for $[-1,1]^2$, $\lambda_1=\lambda_2$).
- The equality case for Eq. (1.7) is proved for boxes $\prod_i[-m_i,m_i]$ with integer $m_i$; a box of odd integral side length such as $[-\tfrac12,\tfrac12]$ is not an equality case.
- The confirmations of Conjecture 1 in dimensions 2 and 3 are proved for all convex bodies, not only origin-symmetric ones.
- Cited results are proved by these routes: Davenport's inequality by successive coordinate shakings followed by the paper's prism decomposition; Eq. (4.1) by lifting projected points into the body, which gives exactly the displayed form; the Henk–Schürmann–Wills inequality by counting horizontal rows instead of facets; Pick's theorem for convex lattice polygons, which is the case Proposition 1.5 needs.

## Citation
If you use or reference the content of this repository, please cite the original work:
```
@article{freyer2022interpolating,
      title={Interpolating between volume and lattice point enumerator with successive minima},
      author={Ansgar Freyer and Eduardo Lucas},
      journal={Monatshefte f{\"u}r Mathematik 198(4), 717--740},
      year={2022},
      doi={10.1007/s00605-022-01713-1},
      eprint={2105.13090},
      archivePrefix={arXiv},
      url={https://link.springer.com/article/10.1007/s00605-022-01713-1},
}
```
