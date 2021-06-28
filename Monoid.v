From SGDT Require Import Prelude.
From HB Require Import structures.

HB.mixin Record IsMonoid A :=
  {emp : A;
   add : A → A → A;
   addA : associative add;
   addL : left_id emp add;
   addR : right_id emp add}.

HB.structure Definition Monoid := {A & IsMonoid A}.

Notation ϵ := emp.
Infix "⊕" := add (at level 10).

HB.mixin Record IsLModule (M : Monoid.type) (A : Type) :=
  {act : M → A → A;
   actI : ∀ a, act ϵ a = a;
   actA : ∀ u v a, act (u ⊕ v) a = act u (act v a)}.

HB.structure Definition LModule (M : Monoid.type) := {A of IsLModule M A}.

Definition is_lmod_hom {M : Monoid.type} {A B : LModule.type M} (f : A → B) : Prop :=
  ∀ u a, f (act u a) = act u (f a).


Section Free.
  Context (M : Monoid.type) (A : Type).
  Definition F := M × A.

  Definition F_act : M → F → F.
  Proof.
    move=> u m.
    split.
    - exact: (u ⊕ m.1).
    - exact: m.2.
  Defined.

  Lemma F_actI : ∀ a, F_act ϵ a = a.
  Proof. by move=> [? ?]; rewrite /F_act addL. Qed.

  Lemma F_actA : ∀ u v a, F_act (u ⊕ v) a = F_act u (F_act v a).
  Proof. by move=> ? ? [? ?]; rewrite /F_act addA. Qed.

  HB.instance Definition F_LModule := IsLModule.Build M F F_act F_actI F_actA.

  Context (Z : LModule.type M).

  Definition ext (f : A → Z) : F → Z.
  Proof.
    move=> m.
    apply: act.
    - exact: m.1.
    - apply: f.
      exact: m.2.
  Defined.

  Definition η : A → F.
  Proof.
    move=> a; split.
    - exact: ϵ.
    - exact: a.
  Defined.

  Lemma extends_uniq : ∀ f (h0 h1 : F → Z), is_lmod_hom h0 → is_lmod_hom h1 → (∀ x, h0 (η x) = f x) → (∀ x, h1 (η x) = f x) → h0 = h1.
  Proof.
    move=> f h0 h1 hom0 hom1 ext0 ext1.
    apply: funext; case=> u a.

    rewrite (_ : (h0 (u, a)) = act u (h0 (η a))).
    - have Q0 := hom0 u (η a).
      by rewrite /η {1}/act /= /F_act /= addR in Q0.
    - rewrite (_ : (h1 (u, a)) = act u (h1 (η a))).
      + have Q1 := hom1 u (η a).
        by rewrite /η {1}/act /= /F_act /= addR in Q1.
      + by rewrite ext0 ext1.
  Qed.


  Lemma ext_extends : ∀ f x, ext f (η x) = f x.
  Proof. by move=> f x; rewrite /η /ext actI. Qed.

  Lemma ext_hom : ∀ f, is_lmod_hom (ext f).
  Proof. by move=> f u /= [v a]; rewrite /ext /= actA. Qed.

  Lemma ext_universal : ∀ f (h : F → Z), is_lmod_hom h → (∀ x, h (η x) = f x) → h = ext f.
  Proof. by move=> f h hom hf; apply/extends_uniq/ext_extends/hf/ext_hom/hom. Qed.
End Free.
