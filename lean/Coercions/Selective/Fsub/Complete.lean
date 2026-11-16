import Coercions.Selective.Fsub.Sub
import Coercions.Selective.Fsub.Lift
/-!
# Completeness

`Sub.toCert` translates a declarative derivation into a certificate by structural
recursion: axioms become steps, `trans` becomes `;`, and the structural rules become
the combined lifts. Coercion existence therefore coincides with full F-sub subtyping.
-/
namespace SelFsub

def Sub.toCert {Γ : Ctx n} {S T : Ty n} : Sub Γ S T → Cert n
  | .refl (A := A) => .step A A
  | .top (A := A) => .step A .top
  | .bound x => .step (.var x) (Γ.lookup x)
  | .trans h₁ h₂ => .seq h₁.toCert h₂.toCert
  | .arr h₁ h₂ => Cert.arr h₁.toCert h₂.toCert
  | .all h₁ h₂ => Cert.all h₁.toCert h₂.toCert

theorem Sub.toCert_typed {Γ : Ctx n} {S T : Ty n} : (h : Sub Γ S T) → CTy Γ h.toCert S T
  | .refl => .step .refl
  | .top => .step .top
  | .bound x => .step (.bound x)
  | .trans h₁ h₂ => .seq h₁.toCert_typed h₂.toCert_typed
  | .arr h₁ h₂ => .arr h₁.toCert_typed h₂.toCert_typed
  | .all h₁ h₂ => .all h₁.toCert_typed h₂.toCert_typed

theorem coercion_iff : (∃ c, CTy Γ c S T) ↔ Nonempty (Sub Γ S T) :=
  ⟨fun ⟨_, h⟩ => coercion_sound h, fun ⟨h⟩ => ⟨h.toCert, h.toCert_typed⟩⟩

end SelFsub
