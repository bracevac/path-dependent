import LambdaP.Repaired.StructuralRuntimeTyping

/-!
Explicitly ranked certificates for the mutually defined structural path and
subtyping derivations.

The judgments themselves live in `Prop`, so their proof terms cannot be
reliably eliminated to compute a height.  These mirrors put the rank in an
ordinary index instead.  The rank is source-derivation bookkeeping, not a
step index on semantic approximation.  Every recursive premise has a
strictly smaller rank than its constructor's result.
-/

namespace LambdaP.Repaired

mutual

inductive Path.SizedCheck : {n : Nat} -> (Gamma : Ctx n) ->
    (R : Path n -> Path n -> Prop) -> {k : Kind} ->
    Nat -> Path n -> Tau n k -> Prop where
| var :
    Ctx.Binds Gamma x T ->
    Path.SizedCheck Gamma R 1 (.var x) (Tau.ty T)
| sub :
    Path.SizedCheck Gamma R rc p d1 ->
    Tau.SizedSub Gamma R rs d1 d2 ->
    Path.SizedCheck Gamma R (rc + rs + 1) p d2
| promote :
    Path.SizedCheck Gamma R rc p (Tau.ty U) ->
    Tau.SizedSub Gamma R rs
      (Tau.ty (Ty.Single p)) (Tau.ty T) ->
    Path.SizedCheck Gamma R (rc + rs + 1) p (Tau.ty T)
| fst :
    Path.SizedCheck Gamma R r p (Tau.ty (Ty.Pair S a d)) ->
    Path.SizedCheck Gamma R (r + 1) p.fst (Tau.ty S)
| sel_r :
    Path.SizedCheck Gamma R r p (Tau.ty (Ty.Pair S a d)) ->
    Path.SizedCheck Gamma R (r + 1) (p.sel a) (d.open p.fst)
| sel_l :
    Path.SizedCheck Gamma R rp p (Tau.ty (Ty.Pair S b d')) ->
    Path.SizedCheck Gamma R rt (p.fst.sel a) d ->
    a ≠ b ->
    Path.SizedCheck Gamma R (rp + rt + 1) (p.sel a) d

inductive Tau.SizedSub : {n : Nat} -> (Gamma : Ctx n) ->
    (R : Path n -> Path n -> Prop) -> {k : Kind} ->
    Nat -> Tau n k -> Tau n k -> Prop where
| refl : Tau.SizedSub Gamma R 1 d d
| trans :
    Tau.SizedSub Gamma R r1 d1 d2 ->
    Tau.SizedSub Gamma R r2 d2 d3 ->
    Tau.SizedSub Gamma R (r1 + r2 + 1) d1 d3
| conv :
    Tau.StructConv R d1 d2 ->
    Tau.SizedSub Gamma R 1 d1 d2
| bot : Tau.SizedSub Gamma R 1 (Tau.ty Ty.Bot) (Tau.ty T)
| top : Tau.SizedSub Gamma R 1 (Tau.ty T) (Tau.ty Ty.Top)
| widen :
    Path.SizedCheck Gamma R r p (Tau.ty T) ->
    Tau.SizedSub Gamma R (r + 1)
      (Tau.ty (Ty.Single p)) (Tau.ty T)
| symm :
    Path.SizedCheck Gamma R r p (Tau.ty (Ty.Single q)) ->
    Tau.SizedSub Gamma R (r + 1)
      (Tau.ty (Ty.Single q)) (Tau.ty (Ty.Single p))
| sel_hi :
    Path.SizedCheck Gamma R rc (p.sel A) (Tau.intv S T) ->
    Tau.SizedSub Gamma R rb (Tau.ty S) (Tau.ty T) ->
    Tau.SizedSub Gamma R (rc + rb + 1)
      (Tau.ty (Ty.TSel p A)) (Tau.ty T)
| sel_lo :
    Path.SizedCheck Gamma R rc (p.sel A) (Tau.intv S T) ->
    Tau.SizedSub Gamma R rb (Tau.ty S) (Tau.ty T) ->
    Tau.SizedSub Gamma R (rc + rb + 1)
      (Tau.ty S) (Tau.ty (Ty.TSel p A))
| fun :
    Tau.SizedSub Gamma R rd (Tau.ty S') (Tau.ty S) ->
    Tau.SizedSub (Gamma.snoc S') (Path.ScopedLift R) rc
      (Tau.ty T) (Tau.ty T') ->
    Tau.SizedSub Gamma R (rd + rc + 1)
      (Tau.ty (Ty.Fun S T)) (Tau.ty (Ty.Fun S' T'))
| pair_fst :
    Tau.SizedSub Gamma R rf (Tau.ty S) (Tau.ty S') ->
    Tau.SizedSub Gamma R (rf + 1)
      (Tau.ty (Ty.Pair S a d)) (Tau.ty (Ty.Pair S' a d))
| pair_single_member :
    Path.SizedCheck Gamma R rp p (Tau.ty P) ->
    Tau.SizedSub (Gamma.snoc (Ty.Single p)) (Path.ScopedLift R) rm d d' ->
    Tau.SizedSub Gamma R ro (d.open p) (d'.open p) ->
    Tau.SizedSub Gamma R (rp + rm + ro + 1)
      (Tau.ty (Ty.Pair (Ty.Single p) a d))
      (Tau.ty (Ty.Pair (Ty.Single p) a d'))
| bounds :
    Tau.SizedSub Gamma R rl (Tau.ty S') (Tau.ty S) ->
    Tau.SizedSub Gamma R ru (Tau.ty T) (Tau.ty T') ->
    Tau.SizedSub Gamma R rn (Tau.ty S) (Tau.ty T) ->
    Tau.SizedSub Gamma R (rl + ru + rn + 1)
      (Tau.intv S T) (Tau.intv S' T')

end

mutual

theorem Path.SizedCheck.erase
    (h : Path.SizedCheck Gamma R r p d) :
    Path.StructCheck Gamma R p d := by
  cases h with
  | var hb => exact .var hb
  | sub hp hs => exact .sub hp.erase hs.erase
  | promote hp hs => exact .promote hp.erase hs.erase
  | fst hp => exact .fst hp.erase
  | sel_r hp => exact .sel_r hp.erase
  | sel_l hp ht hne => exact .sel_l hp.erase ht.erase hne

theorem Tau.SizedSub.erase
    (h : Tau.SizedSub Gamma R r d1 d2) :
    Tau.StructSub Gamma R d1 d2 := by
  cases h with
  | refl => exact .refl
  | trans h1 h2 => exact .trans h1.erase h2.erase
  | conv hc => exact .conv hc
  | bot => exact .bot
  | top => exact .top
  | widen hp => exact .widen hp.erase
  | symm hp => exact .symm hp.erase
  | sel_hi hp hb => exact .sel_hi hp.erase hb.erase
  | sel_lo hp hb => exact .sel_lo hp.erase hb.erase
  | «fun» hd hc => exact .fun hd.erase hc.erase
  | pair_fst hf => exact .pair_fst hf.erase
  | pair_single_member hp hm ho =>
      exact .pair_single_member hp.erase hm.erase ho.erase
  | bounds hl hu hn => exact .bounds hl.erase hu.erase hn.erase

end

private abbrev CheckSizedMotive
    {n : Nat} (Gamma : Ctx n) (R : Path n -> Path n -> Prop)
    {k : Kind} (p : Path n) (d : Tau n k)
    (_ : Path.StructCheck Gamma R p d) : Prop :=
  exists r, Path.SizedCheck Gamma R r p d

private abbrev SubSizedMotive
    {n : Nat} (Gamma : Ctx n) (R : Path n -> Path n -> Prop)
    {k : Kind} (d1 d2 : Tau n k)
    (_ : Tau.StructSub Gamma R d1 d2) : Prop :=
  exists r, Tau.SizedSub Gamma R r d1 d2

private theorem Path.StructCheck.toSizedAux
    (h : Path.StructCheck Gamma R p d) :
    exists r, Path.SizedCheck Gamma R r p d := by
  induction h using Path.StructCheck.rec
      (motive_2 := SubSizedMotive) with
  | var hb => exact ⟨1, .var hb⟩
  | sub hp hs ihp ihs =>
      obtain ⟨rp, hp'⟩ := ihp
      obtain ⟨rs, hs'⟩ := ihs
      exact ⟨rp + rs + 1, .sub hp' hs'⟩
  | promote hp hs ihp ihs =>
      obtain ⟨rp, hp'⟩ := ihp
      obtain ⟨rs, hs'⟩ := ihs
      exact ⟨rp + rs + 1, .promote hp' hs'⟩
  | fst hp ih =>
      obtain ⟨r, hp'⟩ := ih
      exact ⟨r + 1, .fst hp'⟩
  | sel_r hp ih =>
      obtain ⟨r, hp'⟩ := ih
      exact ⟨r + 1, .sel_r hp'⟩
  | sel_l hp ht hne ihp iht =>
      obtain ⟨rp, hp'⟩ := ihp
      obtain ⟨rt, ht'⟩ := iht
      exact ⟨rp + rt + 1, .sel_l hp' ht' hne⟩
  | refl => exact ⟨1, .refl⟩
  | trans h1 h2 ih1 ih2 =>
      obtain ⟨r1, h1'⟩ := ih1
      obtain ⟨r2, h2'⟩ := ih2
      exact ⟨r1 + r2 + 1, .trans h1' h2'⟩
  | conv hc => exact ⟨1, .conv hc⟩
  | bot => exact ⟨1, .bot⟩
  | top => exact ⟨1, .top⟩
  | widen hp ih =>
      obtain ⟨r, hp'⟩ := ih
      exact ⟨r + 1, .widen hp'⟩
  | symm hp ih =>
      obtain ⟨r, hp'⟩ := ih
      exact ⟨r + 1, .symm hp'⟩
  | sel_hi hp hb ihp ihb =>
      obtain ⟨rp, hp'⟩ := ihp
      obtain ⟨rb, hb'⟩ := ihb
      exact ⟨rp + rb + 1, .sel_hi hp' hb'⟩
  | sel_lo hp hb ihp ihb =>
      obtain ⟨rp, hp'⟩ := ihp
      obtain ⟨rb, hb'⟩ := ihb
      exact ⟨rp + rb + 1, .sel_lo hp' hb'⟩
  | «fun» hd hc ihd ihc =>
      obtain ⟨rd, hd'⟩ := ihd
      obtain ⟨rc, hc'⟩ := ihc
      exact ⟨rd + rc + 1, .fun hd' hc'⟩
  | pair_fst hf ihf =>
      obtain ⟨rf, hf'⟩ := ihf
      exact ⟨rf + 1, .pair_fst hf'⟩
  | pair_single_member hp hm ho ihp ihm iho =>
      obtain ⟨rp, hp'⟩ := ihp
      obtain ⟨rm, hm'⟩ := ihm
      obtain ⟨ro, ho'⟩ := iho
      exact ⟨rp + rm + ro + 1, .pair_single_member hp' hm' ho'⟩
  | bounds hl hu hn ihl ihu ihn =>
      obtain ⟨rl, hl'⟩ := ihl
      obtain ⟨ru, hu'⟩ := ihu
      obtain ⟨rn, hn'⟩ := ihn
      exact ⟨rl + ru + rn + 1, .bounds hl' hu' hn'⟩

private theorem Tau.StructSub.toSizedAux
    (h : Tau.StructSub Gamma R d1 d2) :
    exists r, Tau.SizedSub Gamma R r d1 d2 := by
  induction h using Tau.StructSub.rec
      (motive_1 := CheckSizedMotive) with
  | var hb => exact ⟨1, .var hb⟩
  | sub hp hs ihp ihs =>
      obtain ⟨rp, hp'⟩ := ihp
      obtain ⟨rs, hs'⟩ := ihs
      exact ⟨rp + rs + 1, .sub hp' hs'⟩
  | promote hp hs ihp ihs =>
      obtain ⟨rp, hp'⟩ := ihp
      obtain ⟨rs, hs'⟩ := ihs
      exact ⟨rp + rs + 1, .promote hp' hs'⟩
  | fst hp ih =>
      obtain ⟨r, hp'⟩ := ih
      exact ⟨r + 1, .fst hp'⟩
  | sel_r hp ih =>
      obtain ⟨r, hp'⟩ := ih
      exact ⟨r + 1, .sel_r hp'⟩
  | sel_l hp ht hne ihp iht =>
      obtain ⟨rp, hp'⟩ := ihp
      obtain ⟨rt, ht'⟩ := iht
      exact ⟨rp + rt + 1, .sel_l hp' ht' hne⟩
  | refl => exact ⟨1, .refl⟩
  | trans h1 h2 ih1 ih2 =>
      obtain ⟨r1, h1'⟩ := ih1
      obtain ⟨r2, h2'⟩ := ih2
      exact ⟨r1 + r2 + 1, .trans h1' h2'⟩
  | conv hc => exact ⟨1, .conv hc⟩
  | bot => exact ⟨1, .bot⟩
  | top => exact ⟨1, .top⟩
  | widen hp ih =>
      obtain ⟨r, hp'⟩ := ih
      exact ⟨r + 1, .widen hp'⟩
  | symm hp ih =>
      obtain ⟨r, hp'⟩ := ih
      exact ⟨r + 1, .symm hp'⟩
  | sel_hi hp hb ihp ihb =>
      obtain ⟨rp, hp'⟩ := ihp
      obtain ⟨rb, hb'⟩ := ihb
      exact ⟨rp + rb + 1, .sel_hi hp' hb'⟩
  | sel_lo hp hb ihp ihb =>
      obtain ⟨rp, hp'⟩ := ihp
      obtain ⟨rb, hb'⟩ := ihb
      exact ⟨rp + rb + 1, .sel_lo hp' hb'⟩
  | «fun» hd hc ihd ihc =>
      obtain ⟨rd, hd'⟩ := ihd
      obtain ⟨rc, hc'⟩ := ihc
      exact ⟨rd + rc + 1, .fun hd' hc'⟩
  | pair_fst hf ihf =>
      obtain ⟨rf, hf'⟩ := ihf
      exact ⟨rf + 1, .pair_fst hf'⟩
  | pair_single_member hp hm ho ihp ihm iho =>
      obtain ⟨rp, hp'⟩ := ihp
      obtain ⟨rm, hm'⟩ := ihm
      obtain ⟨ro, ho'⟩ := iho
      exact ⟨rp + rm + ro + 1, .pair_single_member hp' hm' ho'⟩
  | bounds hl hu hn ihl ihu ihn =>
      obtain ⟨rl, hl'⟩ := ihl
      obtain ⟨ru, hu'⟩ := ihu
      obtain ⟨rn, hn'⟩ := ihn
      exact ⟨rl + ru + rn + 1, .bounds hl' hu' hn'⟩

theorem Path.StructCheck.toSized
    (h : Path.StructCheck Gamma R p d) :
    exists r, Path.SizedCheck Gamma R r p d :=
  h.toSizedAux

theorem Tau.StructSub.toSized
    (h : Tau.StructSub Gamma R d1 d2) :
    exists r, Tau.SizedSub Gamma R r d1 d2 :=
  h.toSizedAux

end LambdaP.Repaired
