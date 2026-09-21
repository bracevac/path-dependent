import Coercions.Oopsla16.Typing

/-!
# Derived rules

What the reference has to prove, and what it costs there.
-/

namespace Oopsla16

open FCdot (Kind Sig BVar Rename)

/-- Reflexivity of subtyping, `stpd_refl` at `dot.v:908`.

The reference proves this by induction on a *fuel* bound over a type-size
measure: `stpd_refl_aux` (`dot.v:874`) takes `tsize T1 < n`, because
`stp_bindx` compares the **opened** bodies and opening replaces a bound
variable by a free one, so the recursive call is not on a structural subterm.
It therefore needs `tsize` (`dot.v:856`), `open_preserves_size` (`dot.v:866`),
and, in the `fun` and `bind` cases, `closed_open` and `closed_upgrade_gh` from
the closedness family — about fifty-five lines together, on top of that family.

Here `stp_bindx` compares the bodies themselves, and the closedness premise is
the indexing, so this is a plain structural recursion on the type. -/
def Stp.refl {σ : Sig} {G : Store σ σ} :
    {s : Sig} → (T : Ty σ s) → {Γ : Ctx σ s} → Stp G Γ T T
  | _, .TBot, _ => .stp_bot
  | _, .TTop, _ => .stp_top
  | _, .TFun _ T1 T2, _ => .stp_fun (Stp.refl T1) (Stp.refl T2)
  | _, .TTyp _ T1 T2, _ => .stp_typ (Stp.refl T1) (Stp.refl T2)
  | _, .TSel _ _, _ => .stp_selx
  | _, .TBind T, _ => .stp_bindx (Stp.refl T)
  | _, .TAnd T1 T2, _ => .stp_and2 (.stp_and11 (Stp.refl T1)) (.stp_and12 (Stp.refl T2))
  | _, .TOr T1 T2, _ => .stp_or1 (.stp_or21 (Stp.refl T1)) (.stp_or22 (Stp.refl T2))

/-- Every type member declaration includes itself; the `TTyp` instance of
reflexivity, spelled out because it is what a selection's bounds need. -/
def Stp.refl_typ {σ s : Sig} {G : Store σ σ} {Γ : Ctx σ s} (l : Lb) (S T : Ty σ s) :
    Stp G Γ (.TTyp l S T) (.TTyp l S T) := Stp.refl _

end Oopsla16
