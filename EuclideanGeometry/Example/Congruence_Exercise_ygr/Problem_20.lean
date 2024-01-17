import EuclideanGeometry.Foundation.Index
import EuclideanGeometry.Foundation.Axiom.Triangle.Basic_trash

noncomputable section

namespace EuclidGeom

namespace Congruence_Exercise_ygr

namespace Problem_20
/-
$A, B, C, D, E$ are at general positions, $AC = AE$, $\angle ACB = \angle DEA$, $\angle EAB = \angle DAC$.

Prove that $\triangle ABC \congr_a \triangle ADE$.
-/
structure Setting (Plane : Type _) [EuclideanPlane Plane] where
  -- construct five points $A, B, C, D, E$, they are at general positions.
  A : Plane
  B : Plane
  C : Plane
  D : Plane
  E : Plane
  A_ne_B : PtNe A B
  A_ne_C : PtNe A C
  A_ne_D : PtNe A D
  B_ne_C : PtNe B C
  B_ne_D : PtNe B D
  C_ne_D : PtNe C D
  A_ne_E : PtNe A E
  B_ne_E : PtNe B E
  C_ne_E : PtNe C E
  D_ne_E : PtNe D E
  ABD_nd : ¬ colinear A B D
  ABC_nd : ¬ colinear A B C
  ABE_nd : ¬ colinear A B E
  ACD_nd : ¬ colinear A C D
  ACE_nd : ¬ colinear A C E
  ADE_nd : ¬ colinear A D E
  BCD_nd : ¬ colinear B C D
  BCE_nd : ¬ colinear B C E
  BDE_nd : ¬ colinear B D E
  CDE_nd : ¬ colinear C D E
  -- $AC = AE$
  AC_eq_AE : (SEG A C).length = (SEG A E).length
  -- $\angle ACB = \angle DEA$
  ACB_eq_DEA : ∠ A C B = (∠ D E A)
  -- $\angle EAB = \angle DAC$
  EAB_eq_DAC : ∠ E A B = (∠ D A C)

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

-- Prove that $\triangle ABC \congr_a \triangle ADE$.
theorem Result {Plane : Type _} [EuclideanPlane Plane] {e : Setting Plane} : (TRI_nd e.A e.B e.C e.ABC_nd) ≅ₐ (TRI_nd e.A e.D e.E e.ADE_nd) := by
  /-
  In $\triangle ABC$ and $\triangle ADE$,
  $\bullet \qquad \angle CAB = \angle CAE + \angle EAB = \angle CAE + \angle DAC = \angle DAE = - \angle EAD$,
  $\bullet \qquad AC = AE$,
  $\bullet \qquad \angle BCA = - \angle ACB = - \angle DEA$,
  Thus $\triangle ABC \cong_a \triangle ADE$ (by ASA).
  -/
  -- $\angle BAC \cong_a \angle DAE$ (by ASA)
  have : (TRI_nd e.B e.A e.C (flip_colinear_fst_snd.mt e.ABC_nd)) ≅ₐ (TRI_nd e.D e.A e.E (flip_colinear_fst_snd.mt e.ADE_nd)) := by
    apply TriangleND.acongr_of_ASA
    -- $\angle CAB = - \angle EAD$
    calc
      -- $\angle CAB = \angle CAE + \angle EAB$ by ????????????????????
      _ = ∠ e.C e.A e.E + ∠ e.E e.A e.B := by sorry -- ang_value_eq_ang_value_add_ang_value
      -- $\angle CAE + \angle EAB = \angle CAE + \angle DAC$ because $\angle EAB = \angle DAC$
      _ = ∠ e.C e.A e.E + ∠ e.D e.A e.C := by rw [e.EAB_eq_DAC]
      -- $\angle CAE + \angle DAC = \angle DAE$ by ????????????????????
      _ = ∠ e.D e.A e.E := by sorry -- ang_value_eq_ang_value_add_ang_value
      -- $\angle DAE = - \angle EAD$ by symmetry
      _ = _ := neg_value_of_rev_ang
    -- $AC = AE$
    exact e.AC_eq_AE
    -- $\angle BCA = - \angle DEA$
    calc
      -- $\angle BCA = - \angle ACB$ by symmetry
      _ = - ∠ e.A e.C e.B := neg_value_of_rev_ang
      -- $- \angle ACB = - \angle DEA$ by condition
      _ = _ := by
        rw [e.ACB_eq_DEA]
        rfl
  -- $\angle ABD \cong_a \angle ADE$ follows
  exact this.perm_acongr.flip_acongr

end Problem_20
end Congruence_Exercise_ygr
