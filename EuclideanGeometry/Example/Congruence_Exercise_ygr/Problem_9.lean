import EuclideanGeometry.Foundation.Index
import EuclideanGeometry.Foundation.Axiom.Triangle.Basic_trash
import EuclideanGeometry.Foundation.Axiom.Triangle.Congruence_trash

noncomputable section

namespace EuclidGeom

namespace Congruence_Exercise_ygr

namespace Problem_9
/-
In $\triangle ABC$, $D$ lies on $BC$, $BA = BD$, $E$ lies on $AC$ and $BE$ is the angle bisector of $\angle ABC$.

(1) Prove that $\triangle ABE \congr_a \triangle DBE$.

(2) If $\angle BAC = 100^\circ, \angle ACB = 50^\circ$, prove that $\angle DEC = 50^\circ$.
-/
structure Setting1 (Plane : Type _) [EuclideanPlane Plane] where
  -- construct $\triangle ABC$.
  A : Plane
  B : Plane
  C : Plane
  ABC_nd : ¬ colinear A B C
  B_ne_A : PtNe B A := ⟨(ne_of_not_colinear ABC_nd).2.2⟩
  A_ne_C : PtNe A C := ⟨(ne_of_not_colinear ABC_nd).2.1⟩
  C_ne_B : PtNe C B := ⟨(ne_of_not_colinear ABC_nd).1⟩
  -- $D$ lies on $BC$, $BA = BD$.
  D : Plane
  D_int : D LiesInt (SEG B C)
  BA_eq_BD : (SEG B A).length = (SEG B D).length
  -- $E$ lies on $AC$.
  E : Plane
  E_int : E LiesInt (SEG A C)
  -- $B \neq D$ and $B \neq E$.
  B_ne_D : PtNe B D := ⟨D_int.ne_source.symm⟩
  B_ne_E : PtNe B E := sorry
  -- $BE$ is the angle bisector of $\angle ABC$.
  BE_bisec : ∠ A B E = - (∠ D B E)
-- $A, B, E$ are not colinear.
lemma ABE_nd {Plane : Type _} [EuclideanPlane Plane] {e : Setting1 Plane} : ¬ colinear e.A e.B e.E := by sorry
-- $D, B, E$ are not colinear.
lemma DBE_nd {Plane : Type _} [EuclideanPlane Plane] {e : Setting1 Plane} : ¬ colinear e.D e.B e.E := by sorry
attribute [instance] Setting1.B_ne_A
attribute [instance] Setting1.A_ne_C
attribute [instance] Setting1.C_ne_B
attribute [instance] Setting1.B_ne_D
attribute [instance] Setting1.B_ne_E
-- $D \neq E$.
instance D_ne_E {Plane : Type _} [EuclideanPlane Plane] {e : Setting1 Plane} : PtNe e.D e.E := sorry
-- $C \neq E$.
instance C_ne_E {Plane : Type _} [EuclideanPlane Plane] {e : Setting1 Plane} : PtNe e.C e.E := sorry
-- $C \neq D$.
instance C_ne_D {Plane : Type _} [EuclideanPlane Plane] {e : Setting1 Plane} : PtNe e.C e.D := sorry
-- $E \neq A$.
instance E_ne_A {Plane : Type _} [EuclideanPlane Plane] {e : Setting1 Plane} : PtNe e.E e.A := sorry

-- Prove that $\triangle ABE \congr_a \triangle DBE$.
theorem Result1 {Plane : Type _} [EuclideanPlane Plane] {e : Setting1 Plane} : (TRI_nd e.A e.B e.E ABE_nd) ≅ₐ (TRI_nd e.D e.B e.E DBE_nd) := by
  /-
  In $\triangle ABE$ and $\triangle DBE$,
  \bullet \qquad $BE = BE$,
  \bullet \qquad $\angle ABE = - \angle DBE$,
  \bullet \qquad $BA = BD$,
  Thus $\triangle ABE \congr_a \triangle DBE$ (by SAS).
  -/
  -- We have that $B, A, E$ are not colinear because $A, B, E$ are not colinear.
  have BAE_nd : ¬ colinear e.B e.A e.E := flip_colinear_fst_snd.mt ABE_nd
  -- We have that $B, D, E$ are not colinear because $D, B, E$ are not colinear.
  have BDE_nd : ¬ colinear e.B e.D e.E := flip_colinear_fst_snd.mt DBE_nd
  -- $\triangle BAE \congr_a \triangle BDE$ (by SAS).
  have BAE_congr_BDE : (TRI_nd e.B e.A e.E BAE_nd) ≅ₐ (TRI_nd e.B e.D e.E BDE_nd) := by
    apply TriangleND.acongr_of_SAS
    -- $BE = BE$
    · rfl
    -- $\angle ABE = - \angle DBE$
    · exact e.BE_bisec
    -- $BA = BD$
    · exact e.BA_eq_BD
  -- Then $\triangle ABE \congr_a \triangle DBE$.
  exact BAE_congr_BDE.flip_acongr.perm_acongr.perm_acongr

structure Setting2 (Plane : Type _) [EuclideanPlane Plane] extends Setting1 Plane where
  BAC_val : ∠ B A C = (5 : ℝ) / (9 : ℝ) * π
  ACB_val : ∠ A C B = (5 : ℝ) / (18 : ℝ) * π

theorem Result2 {Plane : Type _} [EuclideanPlane Plane] {e : Setting2 Plane} : ∠ e.D e.E e.C = (5 : ℝ) / (18 : ℝ) * π := by
  /-
  Question number one gives that $\triangle ABE \congr_a \triangle DBE$, $\angle EDB = - \angle BDE = \angle BAE = - \angle EAB = - \angle CAB = \angle BAC = \frac{5\pi}{9}$, $\angle DEC = \pi - \angle ECD - \angle CDE = \pi - \angle ACB - \angle CDE = \pi - \angle ACB - (\angle CDB - \angle EDB) = \pi - \angle ACB - (\pi - \angle e.E e.D e.B) = \frac{5\pi}{18}.
  -/
  -- Question number one gives that $\triangle ABE \congr_a \triangle DBE$.
  have result1 : (TRI_nd e.A e.B e.E ABE_nd) ≅ₐ (TRI_nd e.D e.B e.E DBE_nd) := Result1
  -- $\angle EDB = - \angle BDE = \angle BAE = - \angle EAB = - \angle CAB = \angle BAC = \frac{5\pi}{9}$
  have EDB_val : ∠ e.E e.D e.B = ((5 : ℝ) / (9 : ℝ) * π) := by
    calc
      -- $\angle EDB = \angle BDE$ by symmetry
      _ = - ∠ e.B e.D e.E := neg_value_of_rev_ang
      -- $- \angle BDE = \angle BAE$ by $\triangle ABE \congr_a \triangle DBE$
      _ = ∠ e.B e.A e.E := result1.angle₁.symm
      -- $\angle BAE = - \angle EAB$ by symmetry
      _ = - ∠ e.E e.A e.B := neg_value_of_rev_ang
      -- $- \angle EAB = - \angle CAB$ because angle $EAB$ and angle $CAB$ are the same angle.
      _ = - ∠ e.C e.A e.B := by
        have : e.E LiesInt (RAY e.A e.C) := by
          show e.E LiesInt (SEG_nd e.A e.C).toRay
          exact SegND.lies_int_toRay_of_lies_int e.E_int
        simp only [eq_ang_val_of_liesint_liesint this (Ray.snd_pt_lies_int_mk_pt_pt e.A e.B)]
      -- $- \angle CAB = \angle BAC$ by symmetry
      _ = ∠ e.B e.A e.C := neg_value_of_rev_ang.symm
      -- $\angle BAC = \frac{5\pi}{9}$
      _ = _ := e.BAC_val
  -- $\angle DEC = \pi - \angle ECD - \angle CDE = \pi - \angle ACB - \angle CDE = \pi - \angle ACB - (\angle CDB - \angle EDB) = \pi - \angle ACB - (\pi - \angle e.E e.D e.B) = \frac{5\pi}{18}$
  calc
    -- $\angle DEC = \pi - \angle ECD - \angle CDE$ because the sum of $\triangle DCE$ is $\pi$.
    _ = π - ∠ e.E e.C e.D - ∠ e.C e.D e.E := by
      have DCE_nd : ¬ colinear e.D e.C e.E := by sorry
      have : ∠ e.C e.D e.E + ∠ e.E e.C e.D + ∠ e.D e.E e.C = π := TriangleND.angle_sum_eq_pi_of_tri_nd (TRI_nd e.D e.C e.E DCE_nd)
      rw [← this]
      abel
    -- $\pi - \angle ECD - \angle CDE = \pi - \angle ACB - \angle CDE$ because the angle $ACB$ and the angle $ECD$ are the same angle.
    _ = π - ∠ e.A e.C e.B - ∠ e.C e.D e.E := by
      have : ∠ e.A e.C e.B = ∠ e.E e.C e.D := by
        apply eq_ang_val_of_liesint_liesint
        show e.E LiesInt (SEG_nd e.C e.A).toRay
        exact SegND.lies_int_toRay_of_lies_int (SegND.lies_int_rev_iff_lies_int.mp e.E_int)
        show e.D LiesInt (SEG_nd e.C e.B).toRay
        exact SegND.lies_int_toRay_of_lies_int (SegND.lies_int_rev_iff_lies_int.mp e.D_int)
      rw [this]
    -- $\pi - \angle ACB - \angle CDE = \pi - \angle ACB - (\angle CDB - \angle EDB)$ because $\angle CDE = \angle CDB - \angle EDB$
    _ = π - ∠ e.A e.C e.B - (∠ e.C e.D e.B - ∠ e.E e.D e.B) := by
      have : ∠ e.C e.D e.E + ∠ e.E e.D e.B = ∠ e.C e.D e.B := by sorry -- apply ang_value_eq_ang_value_add_ang_value
      rw [← this]
      abel
    -- $\angle CDB = \pi$ because $D$ lies on $BC$, so $\pi - \angle ACB - (\angle CDB - \angle EDB) = \pi - \angle ACB - (\pi - \angle e.E e.D e.B)$
    _ = π - ∠ e.A e.C e.B - (π - ∠ e.E e.D e.B) := by
      rw [val_eq_pi_of_liesint $ Seg.lies_int_rev_iff_lies_int.mpr e.D_int]
    -- plug $\angle ACB = \frac{5\pi}{18}$ and $\angle EDB = \frac{5\pi}{9}$ into the expression and by calculation we have $\pi - \angle ACB - (\pi - \angle e.E e.D e.B) = \frac{5\pi}{18}$.
    _ = _ := by
      simp [e.ACB_val, EDB_val]
      norm_cast
      congr
      rw [← sub_mul]
      norm_num

end Problem_9
end Congruence_Exercise_ygr
