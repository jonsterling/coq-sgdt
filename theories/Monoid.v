From SGDT Require Import Prelude.
From HB Require Import structures.

HB.mixin Record IsMonoid A :=
  {emp : A;
   add : A -> A -> A;
   addA : associative add;
   addL : left_id emp add;
   addR : right_id emp add}.

HB.structure Definition Monoid := {A & IsMonoid A}.

Notation ϵ := emp.
Infix "⊕" := add (at level 10).

HB.mixin Record IsLModule (M : Monoid.type) (A : Type) :=
  {act : M -> A -> A;
   actI : forall a, act ϵ a = a;
   actA : forall u v a, act (u ⊕ v) a = act u (act v a)}.

HB.structure Definition LModule (M : Monoid.type) := {A of IsLModule M A}.

Definition is_lmod_hom {M : Monoid.type} {A B : LModule.type M} (f : A -> B) : Prop :=
  forall u a, f (act u a) = act u (f a).


Section Free.
  Context (M : Monoid.type) (A : Type).
  Definition F := M × A.

  Definition F_act : M -> F -> F.
  Proof.
    move=> u m.
    split.
    - exact: (u ⊕ (pi1 m)).
    - exact: (pi2 m).
  Defined.

  Lemma F_actI : forall a, F_act ϵ a = a.
  Proof. by move=> [? ?]; rewrite /F_act addL. Qed.

  Lemma F_actA : forall u v a, F_act (u ⊕ v) a = F_act u (F_act v a).
  Proof. by move=> ? ? [? ?]; rewrite /F_act addA. Qed.

  HB.instance Definition F_LModule := IsLModule.Build M F F_act F_actI F_actA.

  Definition η : A -> F.
  Proof.
    move=> a; split.
    - exact: ϵ.
    - exact: a.
  Defined.

  Context (Z : LModule.type M) (f : A -> Z).

  Definition extends (h : F -> Z) := forall x, h (η x) = f x.

  Definition ext : F -> Z.
  Proof.
    move=> m.
    apply: act.
    - exact: (pi1 m).
    - apply: f.
      exact: (pi2 m).
  Defined.

  Lemma ext_hom : is_lmod_hom ext.
  Proof. by move=> ? /= [? ?]; rewrite /ext /= actA. Qed.

  Lemma ext_extends : extends ext.
  Proof. by move=> ?; rewrite /η /ext actI. Qed.

  Lemma yank_action : forall h : F -> Z, is_lmod_hom h -> extends h -> forall u a, h (Sig u a) = act u (h (η a)).
  Proof. by move=> h hhom hext u a; rewrite /η -hhom /act /= /F_act addR. Qed.

  Lemma extends_uniq : forall (h0 h1 : F -> Z), is_lmod_hom h0 -> is_lmod_hom h1 -> extends h0 -> extends h1 -> h0 = h1.
  Proof.
    move=> h0 h1 hom0 hom1 ext0 ext1.
    apply: funE; case=> u a.
    by rewrite (yank_action h0) // (yank_action h1) // ext0 ext1.
  Qed.

  Lemma ext_universal : forall (h : F -> Z), is_lmod_hom h -> (forall x, h (η x) = f x) -> h = ext.
  Proof. by move=> h hom hf; apply/extends_uniq/ext_extends/hf/ext_hom/hom. Qed.
End Free.
