import EuclideanGeometry.Foundation.Index
import EuclideanGeometry.Foundation.Axiom.Triangle.Basic_trash
import EuclideanGeometry.Foundation.Axiom.Triangle.Congruence_trash

noncomputable section

namespace EuclidGeom

namespace Congruence_Exercise_ygr

namespace Problem_22
/-
$E, F$ lies on $AC$, $AE = CF$, $\angle CBE = \angle ADF$, $AD \parallel BC$.

Prove that $AD = CB$.
-/
structure Setting (Plane : Type _) [EuclideanPlane Plane] where
  A : Plane
  C : Plane
  E : Plane
  F : Plane
  A_ne_C : PtNe A C
  A_ne_E : PtNe A E
  A_ne_F : PtNe A F
  C_ne_E : PtNe C E
  C_ne_F : PtNe C F
  E_ne_F : PtNe E F
  -- $E, F$ lies on $AC$
  E_int : E LiesInt (SEG A C)
  F_int : F LiesInt (SEG A C)
  -- $AE = CF$
  AE_eq_CF : (SEG A E).length = (SEG C F).length
  B : Plane
  D : Plane
  BD_opposite : IsOnOppositeSide B D (LIN A C)
  B_ne_C : PtNe B C
  B_ne_D : PtNe B D
  A_ne_D : PtNe A D
  D_ne_F : PtNe D F
  B_ne_E : PtNe B E
  -- $\angle CBE = \angle ADF$
  CBE_eq_ADF : ∠ C B E = (∠ A D F)
  -- $AD \parallel BC$
  AD_para_BC : (SEG_nd A D) ∥ (SEG_nd B C)

attribute [instance] Setting.A_ne_C
attribute [instance] Setting.A_ne_E
attribute [instance] Setting.A_ne_F
attribute [instance] Setting.C_ne_E
attribute [instance] Setting.C_ne_F
attribute [instance] Setting.E_ne_F
attribute [instance] Setting.B_ne_C
attribute [instance] Setting.B_ne_D
attribute [instance] Setting.A_ne_D
attribute [instance] Setting.D_ne_F
attribute [instance] Setting.B_ne_E

-- Prove that $AD = CB$.
theorem Result1 {Plane : Type _} [EuclideanPlane Plane] {e : Setting Plane} : (SEG e.A e.D).length = (SEG e.C e.B).length := by
  have DAF_nd : ¬ colinear e.D e.A e.F := by sorry
  have BCE_nd : ¬ colinear e.B e.C e.E := by sorry
  have DAF_cong_BCE : (TRI_nd e.D e.A e.F DAF_nd) ≅ (TRI_nd e.B e.C e.E BCE_nd) := by
    apply TriangleND.congr_of_AAS
    · exact e.CBE_eq_ADF.symm
    · sorry
    · calc
      _ = (SEG e.A e.C).length - (SEG e.F e.C).length := by sorry
      _ = (SEG e.A e.C).length - (SEG e.A e.E).length := by sorry
      _ = (SEG e.E e.C).length := by
        have : (SEG e.A e.C).length = (SEG e.A e.E).length + (SEG e.E e.C).length := length_eq_length_add_length e.E_int
        rw [this]
        norm_num
      _ = _ := length_of_rev_eq_length'

  sorry

end Problem_22
end Congruence_Exercise_ygr
