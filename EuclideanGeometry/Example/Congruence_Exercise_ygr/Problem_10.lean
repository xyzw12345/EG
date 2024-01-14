import EuclideanGeometry.Foundation.Index
import EuclideanGeometry.Foundation.Axiom.Triangle.Basic_trash

noncomputable section

namespace EuclidGeom

namespace Congruence_Exercise_ygr

namespace Problem_10
/-
$E, F$ lies on segment $BC$, $AB \parallel CD$, $\angle BAE = \angle CDF$, $BE = CF$.

Prove that $AE = DF$.
-/
structure Setting (Plane : Type _) [EuclideanPlane Plane] where
  -- $E, F$ lies on segment $BC$
  B : Plane
  C : Plane
  B_ne_C : PtNe B C
  E : Plane
  F : Plane
  E_int : E LiesInt (SEG_nd B C)
  F_int : F LiesInt (SEG_nd B C)
  -- $A$, $D$ lies on two opposite sides of line $BC$.
  A : Plane
  D : Plane
  AD_opposite : IsOnOppositeSide A D (SEG_nd B C)
  A_ne_B : PtNe A B
  C_ne_D : PtNe C D
  -- $AB \parallel CD$
  AB_para_CD : (SEG_nd A B) ∥ (SEG_nd C D)
  -- $D \neq F$
  D_ne_F : PtNe D F := by sorry
  -- $A \neq E$
  A_ne_E : PtNe A E := by sorry
  -- $\angle BAE = \angle CDF
  BAE_eq_CDF : ∠ B A E = (∠ C D F)
  -- $BE = CF$
  BE_eq_CF : (SEG B E).length = (SEG C F).length

attribute [instance] Setting.B_ne_C
attribute [instance] Setting.A_ne_B
attribute [instance] Setting.C_ne_D
attribute [instance] Setting.D_ne_F
attribute [instance] Setting.A_ne_E

-- Prove that $AE = DF$.
theorem Result {Plane : Type _} [EuclideanPlane Plane] {e : Setting Plane} : (SEG e.A e.E).length = (SEG e.D e.F).length := by
  /-
  Because $AB \parallel CD$ and $A, D$ lies on the opposite sides of line $BC$, angle $ABC$ and angle $DCB$ are alternate interior angles.
  In $\triangle ABE$ and $\triangle DCF$,
  \bullet \qquad $\angle BAE = \angle CDF$,
  \bullet \qquad $\angle EBA = \angle FCD$ because $\angle EBA = - \angle ABC$, $\angle FCD = - \angle DCF$, and angle $ABC$ and angle $DCB$ are alternate interior angles
  \bullet \qquad $BE = CF$
  Thus $\triangle ABE \cong \triangle DCF$ (by AAS).
  Thus $AE = DF$.
  -/
  -- We have $A, B, E$ are not collinear and $D, C, F$ are not collinear, and therefore $E \neq B, F \neq C$.
  have ABE_nd : ¬ colinear e.A e.B e.E := by sorry
  haveI E_ne_B : PtNe e.E e.B := ⟨(ne_of_not_colinear ABE_nd).1⟩
  have DCF_nd : ¬ colinear e.D e.C e.F := by sorry
  haveI F_ne_C : PtNe e.F e.C := ⟨(ne_of_not_colinear DCF_nd).1⟩
  -- Because $AB \parallel CD$ and $A, D$ lies on the opposite sides of line $BC$, angle $ABC$ and angle $DCB$ are alternate interior angles.
  have : IsAlternateIntAng (ANG e.A e.B e.C) (ANG e.D e.C e.B) := by
    sorry
  -- In $\triangle ABE$ and $\triangle DCF$,
  have ABE_cong_DCF : (TRI_nd e.A e.B e.E ABE_nd) ≅ (TRI_nd e.D e.C e.F DCF_nd) := by
    apply TriangleND.congr_of_AAS
    -- $\angle BAE = \angle CDF
    exact e.BAE_eq_CDF
    -- $\angle EBA = \angle FCD$ because $\angle EBA = - \angle ABC$, $\angle FCD = - \angle DCF$, and angle $ABC$ and angle $DCB$ are alternate interior angles.
    calc
      -- $\angle EBA = - \angle ABE$ by symmetry
      _ = - ∠ e.A e.B e.E := neg_value_of_rev_ang
      -- $- \angle ABE = - \angle ABC$ because angle $ABE$ and angle $ABC$ are the same angle
      _ = - ∠ e.A e.B e.C := by
        have : ∠ e.A e.B e.C = ∠ e.A e.B e.E := by
          apply eq_ang_val_of_liesint_liesint (Ray.snd_pt_lies_int_mk_pt_pt e.B e.A)
          exact SegND.lies_int_toRay_of_lies_int e.E_int
        rw [this]
      -- $- \angle ABC = - \angle DCB$ because angle $ABC$ and angle $DCB$ are alternate interior angles
      _ = - ∠ e.D e.C e.B := by simp only [value_eq_of_isalternateintang this]
      -- $- \angle DCB = - \angle DCF$ because angle $DCB$ and angle $DCF$ are the same angle
      _ = - ∠ e.D e.C e.F := by
        have : ∠ e.D e.C e.B = ∠ e.D e.C e.F := by
          apply eq_ang_val_of_liesint_liesint (Ray.snd_pt_lies_int_mk_pt_pt e.C e.D)
          exact SegND.lies_int_toRay_of_lies_int (SegND.lies_int_rev_iff_lies_int.mpr e.F_int)
        rw [this]
      -- $- \angle DCF = \angle FCD$ by symmetry
      _ = _ := neg_value_of_rev_ang.symm
    -- $BE = CF$
    exact e.BE_eq_CF
  -- Thus $\triangle ABE \cong \triangle DCF$ by AAS.
  -- AE = EA = FD = DF$ by congruence.
  calc
    -- $AE = EA$ by symmetry
    _ = (SEG e.E e.A).length := length_of_rev_eq_length'
    -- $EA = FD$ by congruence
    _ = (SEG e.F e.D).length := ABE_cong_DCF.edge₂
    -- $FD = DF$ by symmetry
    _ = _ := length_of_rev_eq_length'

end Problem_10
end Congruence_Exercise_ygr
