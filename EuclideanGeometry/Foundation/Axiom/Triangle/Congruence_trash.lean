import EuclideanGeometry.Foundation.Axiom.Triangle.Congruence

noncomputable section
namespace EuclidGeom

variable {P : Type _} [EuclideanPlane P]

theorem Triangle.IsCongr.unique_of_eq_eq {tr₁ tr₂ : Triangle P} (h : tr₁.IsCongr tr₂) (p₁ : tr₁.point₁ = tr₂.point₁) (p₂ : tr₁.point₂ = tr₂.point₂) [hne : PtNe tr₁.point₁ tr₁.point₂] : tr₁.point₃ = tr₂.point₃ := sorry

theorem acongr_of_AAS_variant (tr_nd₁ tr_nd₂ : TriangleND P) (a₁ : tr_nd₁.angle₁.dvalue = - tr_nd₂.angle₁.dvalue) (a₂ : tr_nd₁.angle₂.value = - tr_nd₂.angle₂.value) (e₃ : tr_nd₁.edge₁.length = tr_nd₂.edge₁.length) : tr_nd₁ ≅ₐ tr_nd₂ := by sorry

-- ShenZiJun
theorem height₃_eq_of_congr {tr_nd₁ tr_nd₂ : TriangleND P} (h : tr_nd₁.IsCongr tr_nd₂) : (SEG tr_nd₁.point₃ (perp_foot tr_nd₁.point₃ (LIN tr_nd₁.point₁ tr_nd₁.point₂))).length = (SEG tr_nd₂.point₃ (perp_foot tr_nd₂.point₃ (LIN tr_nd₂.point₁ tr_nd₂.point₂))).length := by sorry

namespace TriangleND

-- ShenZiJun
theorem congr_of_HL_variant {tr_nd₁ tr_nd₂ : TriangleND P} (h₁ : tr_nd₁.angle₁.dvalue = ↑(π / 2)) (h₂ : tr_nd₂.angle₁.value = tr_nd₁.angle₁.value) (e₁ : tr_nd₁.edge₁.length = tr_nd₂.edge₁.length) (e₂ : tr_nd₁.edge₂.length = tr_nd₂.edge₂.length) : tr_nd₁ ≅ tr_nd₂ := by sorry

namespace IsACongr

theorem flip_acongr {tr_nd₁ tr_nd₂ : TriangleND P} (h : tr_nd₁.IsACongr tr_nd₂) : (flip_vertices tr_nd₁).IsACongr (flip_vertices tr_nd₂) := sorry

end IsACongr

end TriangleND

end EuclidGeom
