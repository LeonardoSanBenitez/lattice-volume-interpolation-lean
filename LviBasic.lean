import DiscreteMinkowski

/-!
Shared notation and paper-specific bridges for the formalization of Freyer--Lucas,
"Interpolating between volume and lattice point enumerator with successive minima".

Catalog: `catalog.json`.

The development deliberately depends on the mechanically verified `DiscreteMinkowski`
layer at commit `bce1544`, whose vocabulary for convex bodies, lattice points, gauges,
and successive minima matches the paper. The `Lvi` prefix prevents a flat-module collision
with the dependency's existing `Basic` module.
-/

namespace LatticeVolumeInterpolation

open scoped BigOperators

end LatticeVolumeInterpolation
