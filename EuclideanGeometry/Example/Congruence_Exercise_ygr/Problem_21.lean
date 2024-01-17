import EuclideanGeometry.Foundation.Index
import EuclideanGeometry.Foundation.Axiom.Triangle.Basic_trash

noncomputable section

namespace EuclidGeom

namespace Congruence_Exercise_ygr

namespace Problem_21
/-
$AC$ bisects $\angle BAD$, $CE \perp AB$ intersects line $AB$ at $E$, $CF \perp AD$ intersects line $AD$ at $F$, and $BC = CD$. $E$ lies on $AB$, $D$ lieson $AF$.

(1) Prove that $\triangle BCE \cong \triangle DCF$.
(2) Prove that $AB + AD = 2AE$.
-/
structure Setting (Plane : Type _) [EuclideanPlane Plane] where
  A : Plane
  B : Plane
  C : Plane
  D : Plane
  A_ne_B : PtNe A B
  A_ne_C : PtNe A C
  A_ne_D : PtNe A D
  B_ne_C : PtNe B C
  B_ne_D : PtNe B D
  C_ne_D : PtNe C D
  -- $AC$ bisects $\angle BAD$
  AC_bisec : ∠ B A C = (∠ C A D)
  E : Plane
  -- $CE \perp AB$ intersects line $AB$ at $E$
  E_perp_foot : E = perp_foot C (LIN A B)
  -- $E$ lies on $AB$
  E_int : E LiesInt (SEG A B)
  F : Plane
  -- $CF \perp AD$ intersects line $AD$ at $F$
  F_perp_foot : F = perp_foot C (LIN A D)
  -- $D$ lieson $AF$
  D_int : D LiesInt (SEG A F)
  -- $BC = CD$
  BC_eq_CD : (SEG B C).length = (SEG C D).length
  BCE_nd : ¬ colinear B C E
  DCF_nd : ¬ colinear D C F

/-
attribute [instance] Setting.B_ne_C
attribute [instance] Setting.A_ne_B
attribute [instance] Setting.C_ne_D
attribute [instance] Setting.A_ne_C
attribute [instance] Setting.A_ne_D
attribute [instance] Setting.B_ne_D
attribute [instance] Setting.A_ne_E
attribute [instance] Setting.B_ne_E
attribute [instance] Setting.C_ne_E
attribute [instance] Setting.D_ne_E
-/

-- Prove that $\triangle BCE \cong \triangle DCF$.
theorem Result1 {Plane : Type _} [EuclideanPlane Plane] {e : Setting Plane} : (TRI_nd e.B e.C e.E e.BCE_nd) ≅ₐ (TRI_nd e.D e.C e.F e.DCF_nd) := by sorry

-- Prove that $AB + AD = 2AE$.
theorem Result2 {Plane : Type _} [EuclideanPlane Plane] {e : Setting Plane} : (SEG e.A e.B).length + (SEG e.A e.D).length = 2 * (SEG e.A e.E).length := by sorry

end Problem_21
end Congruence_Exercise_ygr
