import Mathlib.Algebra.Module.ZLattice.Covolume
import Mathlib.Analysis.InnerProductSpace.ProdL2
import OrthogonalLatticeDiscrete

/-!
# Covolumes under orthogonal lattice projection

Infrastructure for catalog item `projected_lattice_determinant_bound`, the sentence
after Theorem 1.3. All measures on subspaces are their intrinsic Euclidean volume.
The determinant of a lattice basis adapted to a subspace factors into its subspace
and projected determinants; the lifts need not be perpendicular to the subspace.
-/

open Set Module MeasureTheory Matrix

namespace LatticeVolumeInterpolation

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

private theorem covolume_orthonormal_coordinates
    (Λ : Submodule ℤ E) [DiscreteTopology Λ] [IsZLattice ℝ Λ]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Basis ι ℤ Λ) (o : OrthonormalBasis ι ℝ E) :
    ZLattice.covolume Λ volume = |(o.toBasis.toMatrix (fun i => (b i : E))).det| := by
  have hunit : volume.real (ZSpan.fundamentalDomain o.toBasis) = 1 := by
    calc
      _ = volume.real (parallelepiped o.toBasis) :=
        measureReal_congr (ZSpan.fundamentalDomain_ae_parallelepiped o.toBasis volume)
      _ = 1 := by simp [measureReal_def, o.volume_parallelepiped]
  simpa [hunit, Basis.det_apply, Function.comp_def] using
    ZLattice.covolume_eq_det_mul_measureReal Λ volume b o.toBasis

/-- An adapted lattice basis gives the ambient/subspace/projection covolume identity.
Only the first block must lie in the subspace; the other block consists of arbitrary
lifts of a basis of the projected lattice. -/
theorem covolume_factor_of_adapted_basis
    (L : Submodule ℝ E) (Λ : Submodule ℤ E)
    (K : Submodule ℤ L) (P : Submodule ℤ Lᗮ)
    [DiscreteTopology Λ] [IsZLattice ℝ Λ]
    [DiscreteTopology K] [IsZLattice ℝ K]
    [DiscreteTopology P] [IsZLattice ℝ P]
    {ι κ : Type*} [Finite ι] [Finite κ]
    (b : Basis (ι ⊕ κ) ℤ Λ) (c : Basis ι ℤ K) (d : Basis κ ℤ P)
    (hc : ∀ i, (b (.inl i) : E) = ((c i : L) : E))
    (hd : ∀ i, Lᗮ.orthogonalProjectionOnto (b (.inr i) : E) = (d i : Lᗮ)) :
    ZLattice.covolume Λ volume =
      ZLattice.covolume K volume * ZLattice.covolume P volume := by
  classical
  letI := Fintype.ofFinite ι
  letI := Fintype.ofFinite κ
  let oc : OrthonormalBasis ι ℝ L := (stdOrthonormalBasis ℝ L).reindex
    (Fintype.equivFinOfCardEq (finrank_eq_card_basis (c.ofZLatticeBasis ℝ K)).symm).symm
  let od : OrthonormalBasis κ ℝ Lᗮ := (stdOrthonormalBasis ℝ Lᗮ).reindex
    (Fintype.equivFinOfCardEq (finrank_eq_card_basis (d.ofZLatticeBasis ℝ P)).symm).symm
  let o := (oc.prod od).map L.orthogonalDecomposition.symm
  have hleft (i : ι) : o (.inl i) = (oc i : E) := by
    simp [o, OrthonormalBasis.prod_apply]
  have hright (i : κ) : o (.inr i) = (od i : E) := by
    simp [o, OrthonormalBasis.prod_apply]
  let A := oc.toBasis.toMatrix (fun i => (c i : L))
  let D := od.toBasis.toMatrix (fun i => (d i : Lᗮ))
  let B : Matrix ι κ ℝ := fun i j => inner ℝ (oc i : E) (b (.inr j) : E)
  have hmatrix : o.toBasis.toMatrix (fun i => (b i : E)) = fromBlocks A B 0 D := by
    ext i j
    simp only [Basis.toMatrix_apply, OrthonormalBasis.coe_toBasis_repr_apply,
      OrthonormalBasis.repr_apply_apply]
    cases i with
    | inl i =>
      cases j with
      | inl j => simp [A, hleft, hc, Basis.toMatrix_apply,
          OrthonormalBasis.coe_toBasis_repr_apply, OrthonormalBasis.repr_apply_apply]
      | inr j => simp [B, hleft]
    | inr i =>
      cases j with
      | inl j =>
        simp only [fromBlocks_apply₂₁, Matrix.zero_apply, hright, hc]
        exact L.inner_left_of_mem_orthogonal (c j : L).property (od i).property
      | inr j =>
        simp only [fromBlocks_apply₂₂, D, Basis.toMatrix_apply,
          OrthonormalBasis.coe_toBasis_repr_apply, OrthonormalBasis.repr_apply_apply, hright]
        rw [← hd j]
        exact (Lᗮ.inner_orthogonalProjectionOnto_eq_of_mem_left (od i) _).symm
  rw [covolume_orthonormal_coordinates Λ b o, hmatrix, det_fromBlocks_zero₂₁, abs_mul,
    ← covolume_orthonormal_coordinates K c oc,
    ← covolume_orthonormal_coordinates P d od]

/-- The ambient covolume is the product of the full section and projected covolumes.
The lattice hypotheses ensure finite positive intrinsic covolumes; no orthogonal
integral lift or primitive choice of the originally selected vectors is assumed. -/
theorem covolume_section_mul_projection
    (Λ : Submodule ℤ E) (L : Submodule ℝ E)
    [DiscreteTopology Λ] [IsZLattice ℝ Λ]
    [DiscreteTopology (sectionLattice Λ L)] [IsZLattice ℝ (sectionLattice Λ L)]
    [DiscreteTopology (orthogonalImageLattice Λ L)]
    [IsZLattice ℝ (orthogonalImageLattice Λ L)] :
    ZLattice.covolume Λ volume =
      ZLattice.covolume (sectionLattice Λ L) volume *
        ZLattice.covolume (orthogonalImageLattice Λ L) volume := by
  classical
  let K := sectionLattice Λ L
  let P := orthogonalImageLattice Λ L
  let c := Module.Free.chooseBasis ℤ K
  let d := Module.Free.chooseBasis ℤ P
  obtain ⟨s, hs⟩ := exists_latticeSplit Λ L
  let e := latticeSplitEquiv Λ L s hs
  let b := (c.prod d).map e
  apply covolume_factor_of_adapted_basis L Λ K P b c d
  · intro i
    simp [b, e, latticeSplitEquiv, sectionLatticeInclusion, Basis.prod_apply]
  · intro i
    have hs_apply : latticeProjection Λ L (s (d i)) = d i := DFunLike.congr_fun hs (d i)
    have hproj : Lᗮ.orthogonalProjectionOnto ((s (d i) : Λ) : E) = (d i : Lᗮ) :=
      congrArg Subtype.val hs_apply
    simpa [b, e, latticeSplitEquiv, sectionLatticeInclusion, Basis.prod_apply] using hproj

/-- A full sublattice has at least the covolume of the lattice containing it.
This instantiates the lattice-index theorem; positivity rules out the infinite-index
value zero before using that a positive integer index is at least one. -/
theorem covolume_mono_sublattice (M K : Submodule ℤ E)
    [DiscreteTopology M] [IsZLattice ℝ M] [DiscreteTopology K] [IsZLattice ℝ K]
    (hMK : M ≤ K) : ZLattice.covolume K volume ≤ ZLattice.covolume M volume := by
  have hindex := ZLattice.covolume_div_covolume_eq_relIndex' M K hMK
  have hpos : (0 : ℝ) < (M.toAddSubgroup.relIndex K.toAddSubgroup : ℝ) := by
    rw [← hindex]
    exact div_pos (ZLattice.covolume_pos M volume) (ZLattice.covolume_pos K volume)
  have hn : 1 ≤ M.toAddSubgroup.relIndex K.toAddSubgroup := by
    exact Nat.succ_le_iff.mpr (by exact_mod_cast hpos)
  have hratio : (1 : ℝ) ≤ ZLattice.covolume M volume / ZLattice.covolume K volume := by
    rw [hindex]
    exact_mod_cast hn
  simpa using (le_div_iff₀ (ZLattice.covolume_pos K volume)).mp hratio

/-- The projected covolume bound in the paper's intrinsic zonotope-volume notation.
The selected vectors are a real basis of the subspace but need not be primitive
in the ambient lattice. Discreteness and spanning of the projected lattice are
derived internally from the integral basis vectors and ambient lattice. -/
theorem projected_covolume_ge_reciprocal_zonotope
    (Λ : Submodule ℤ E) (L : Submodule ℝ E)
    [DiscreteTopology Λ] [IsZLattice ℝ Λ]
    {ι : Type*} [Fintype ι] (v : Basis ι ℝ L)
    (hv : ∀ i, ((v i : L) : E) ∈ Λ) :
    ZLattice.covolume Λ volume / volume.real (parallelepiped v) ≤
      ZLattice.covolume (orthogonalImageLattice Λ L) volume := by
  classical
  letI : DiscreteTopology (orthogonalImageLattice Λ L) :=
    orthogonalImageLattice_discrete Λ L v hv
  letI : IsZLattice ℝ (orthogonalImageLattice Λ L) :=
    ⟨orthogonalImageLattice_span_top Λ L⟩
  let K := sectionLattice Λ L
  let M := Submodule.span ℤ (Set.range v)
  letI : DiscreteTopology K := sectionLattice_discrete Λ L
  letI : IsZLattice ℝ K := ⟨by
    apply top_le_iff.mp
    rw [← v.span_eq]
    exact Submodule.span_mono (by rintro _ ⟨i, rfl⟩; exact hv i)⟩
  have hMK : M ≤ K := Submodule.span_le.mpr (by rintro _ ⟨i, rfl⟩; exact hv i)
  have hMvol : ZLattice.covolume M volume = volume.real (parallelepiped v) := by
    rw [ZLattice.covolume_eq_measure_fundamentalDomain M volume
      (ZSpan.isAddFundamentalDomain v volume)]
    exact measureReal_congr (ZSpan.fundamentalDomain_ae_parallelepiped v volume)
  rw [← hMvol]
  apply (div_le_iff₀ (ZLattice.covolume_pos M volume)).mpr
  calc
    ZLattice.covolume Λ volume = ZLattice.covolume K volume *
        ZLattice.covolume (orthogonalImageLattice Λ L) volume :=
      covolume_section_mul_projection Λ L
    _ ≤ ZLattice.covolume M volume *
        ZLattice.covolume (orthogonalImageLattice Λ L) volume :=
      mul_le_mul_of_nonneg_right (covolume_mono_sublattice M K hMK)
        (ZLattice.covolume_pos _ volume).le
    _ = _ := mul_comm _ _

end
end LatticeVolumeInterpolation
