import EuclideanGeometry.Foundation.Index
import EuclideanGeometry.Foundation.Axiom.Triangle.Basic_trash

noncomputable section

namespace EuclidGeom

namespace Congruence_Exercise_ygr

namespace Problem_16
/-
Let $D$ be a point inside $\triangle ABC$, $\angle CBD = \angle DCB$, $\angle ADB = - \angle CDA$.

Prove that $AB = AC$.
-/
structure Setting (Plane : Type _) [EuclideanPlane Plane] where
  A : Plane
  B : Plane
  C : Plane
  ABC_nd : ¬ colinear A B C
  D : Plane
  ABD_nd : ¬ colinear A B D
  ACD_nd : ¬ colinear A C D
  BCD_nd : ¬ colinear B C D
  B_ne_C : PtNe B C := ⟨(ne_of_not_colinear ABC_nd).1.symm⟩
  B_ne_D : PtNe B D := ⟨(ne_of_not_colinear ABD_nd).1.symm⟩
  C_ne_D : PtNe C D := ⟨(ne_of_not_colinear ACD_nd).1.symm⟩
  A_ne_B : PtNe A B := ⟨(ne_of_not_colinear ABC_nd).2.2.symm⟩
  A_ne_C : PtNe A C := ⟨(ne_of_not_colinear ABC_nd).2.1⟩
  A_ne_D : PtNe A D := ⟨(ne_of_not_colinear ABD_nd).2.1⟩
  CBD_eq_DCB : ∠ C B D = (∠ D C B)
  ADB_eq_neg_CDA : ∠ A D B = - ∠ C D A

attribute [instance] Setting.B_ne_C
attribute [instance] Setting.A_ne_B
attribute [instance] Setting.C_ne_D
attribute [instance] Setting.A_ne_C
attribute [instance] Setting.A_ne_D
attribute [instance] Setting.B_ne_D

-- Prove that $AB = AC$.
theorem Result {Plane : Type _} [EuclideanPlane Plane] {e : Setting Plane} : (SEG e.A e.B).length = (SEG e.A e.C).length := by
  have DB_eq_DC : (SEG e.D e.B).length = (SEG e.D e.C).length := sorry
  have DAB_acongr_DCA : (TRI_nd e.D e.A e.B (perm_colinear_snd_trd_fst.mt e.ABD_nd)) ≅ₐ (TRI_nd e.D e.C e.A (flip_colinear_fst_trd.mt e.ACD_nd)) := by
    apply TriangleND.acongr_of_SAS
    sorry
    sorry
    sorry
  calc
    _ = (SEG e.C e.A).length := sorry
    _ = _ := length_of_rev_eq_length'

end Problem_16
end Congruence_Exercise_ygr
