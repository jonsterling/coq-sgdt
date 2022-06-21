Require Import ssrbool.
From extructures Require Import ord fmap fset.
From sgdt Require Import preamble impredicative guarded category functor.
From sgdt Require itree.

Set Bullet Behavior "Strict Subproofs".
Set Universe Polymorphism.

Module World.
  Definition world (T : Type) : Type := {fmap nat -> T}.

  Section World.
    Context (T : Type).

    Definition world_leq (U V : world T) :=
      forall i, i \in domm U -> U i = V i.

    Fact world_leqR (U : world T) : world_leq U U.
    Proof. by []. Qed.

    Fact world_leqT (U V W : world T) : world_leq U V -> world_leq V W -> world_leq U W.
    Proof.
      move=> UV VW i hi.
      rewrite UV//= VW//=.
      apply/dommP.
      case eqn: (U i) => [x|].
      - by exists x; rewrite -eqn -UV//=.
      - case/dommP: hi=> x eqn'.
        rewrite eqn' in eqn.
        by discriminate eqn.
    Qed.

    Definition hom_mixin : Hom.mixin_of (world T).
    Proof. constructor; exact world_leq. Defined.

    Canonical hom : Hom.type.
    Proof. by esplit; apply: hom_mixin. Defined.

    Definition precat_mixin : Precategory.mixin_of hom.
    Proof. by build; apply: world_leqT. Qed.

    Definition precat : Precategory.type.
    Proof. by esplit; apply: precat_mixin. Defined.

    Definition cat_mixin : Category.mixin_of precat.
    Proof. by build; move=>*; cbn. Qed.

    Definition cat : Category.type.
    Proof. by esplit; apply: cat_mixin. Defined.
  End World.
End World.

Local Open Scope category_scope.

Definition ℱ (T : Type) : Type :=
  World.cat T ~> SET.cat.

Definition 𝒯 : Type.
Proof. by apply: Later.loeb=> /dlater; apply: ℱ. Defined.

Local Lemma 𝒯_unfold : 𝒯 = ℱ (▷ 𝒯).
Proof. by rewrite dlater_next_eq /𝒯 {1} Later.loeb_unfold. Qed.

Global Instance 𝒯_conn : Connective 𝒯 (ℱ (▷ 𝒯)).
Proof. by build; rewrite -𝒯_unfold; apply: iso_id. Qed.

Opaque 𝒯_conn.


Notation 𝒲 := (World.cat (▷ 𝒯)).
Notation "𝒞+" := Cat[𝒲, SET.cat].
Notation "𝒞-" := Cat[𝒲^op, SET.cat].


Module Ref.
  Section Ref.
    Context (A : 𝒞+).

    Definition ob (w : 𝒲) : Set :=
      {i : nat | w i = Some (next: intro A)}.

    Definition rst (w1 w2 : 𝒲) (w12 : w1 ~> w2) : ob w1 -> ob w2.
    Proof.
      move=> [i hi]; exists i.
      abstract by rewrite -(w12 i) //=; apply/dommP; eauto.
    Defined.

    Definition prefunctor_mixin : Prefunctor.mixin_of 𝒲 SET.cat ob.
    Proof. by build; apply: rst. Defined.

    Canonical prefunctor : Prefunctor.type 𝒲 SET.cat.
    Proof. by esplit; apply: prefunctor_mixin. Defined.

    Lemma functor_mixin : Functor.mixin_of _ _ prefunctor.
    Proof. by build; move=> *; apply: funE=> //=; case=> *; apply: subE. Qed.

    Canonical functor : Functor.type 𝒲 SET.cat.
    Proof. by esplit; apply: functor_mixin. Defined.

    Definition T : 𝒞+ := functor.
  End Ref.
End Ref.


Definition heaplet (w w' : 𝒲) : Set :=
  forall i : nat,
    match w i with
    | None => True
    | Some A =>
        dlater (Later.map (fun X => (elim X : ℱ (▷ 𝒯)) w') A)
    end.

Definition heap (w : 𝒲) := heaplet w w.

Module LeftAdjunctive.
  Section LeftAdjunctive.
    Context (A : 𝒞+) (E : itree.Thy).

    Definition ob (w : 𝒲) : Set :=
      ⋁ w' : 𝒲, @hom 𝒲 w w' × (heap w' × itree.ITree E (A w')).

    Definition rst (w1 w2 : 𝒲) (w12 : @hom 𝒲 w1 w2) : ob w2 -> ob w1.
    Proof.
      apply: Reflection.map; case=> w2' [w2w2' [h u]].
      exists w2'; do ? split.
      - exact: (w12 >> w2w2').
      - exact: h.
      - exact: u.
    Defined.

    Definition prefunctor_mixin : Prefunctor.mixin_of (𝒲^op) SET.cat ob.
    Proof. by build=> x y; apply: rst. Defined.

    Canonical prefunctor : Prefunctor.type (𝒲^op) SET.cat.
    Proof. by esplit; apply: prefunctor_mixin. Defined.

    Lemma functor_mixin : Functor.mixin_of _ _ prefunctor.
    Proof.
      build.
      - move=> w; cbn.
        rewrite -Reflection.map_id.
        congr Reflection.map.
        apply: funE=> p.
        apply: sigE=> //=.
        apply: prodE=> //=.
        apply: (@seqR (𝒲^op)).
      - move=> w1 w2 w3 w12 w23; cbn.
        rewrite -Reflection.map_cmp.
        congr Reflection.map.
        apply: funE=> p.
        apply: sigE=> //=.
        apply: prodE=> //=.
        apply: (@seqA (𝒲^op)).
    Qed.

    Canonical functor : Functor.type (𝒲^op) SET.cat.
    Proof. esplit; apply: functor_mixin. Defined.

    Definition T : 𝒞- := functor.
  End LeftAdjunctive.
End LeftAdjunctive.

Module RightAdjunctive.
  Section RightAdjunctive.
    Context (X : 𝒞-) (E : itree.Thy).

    Definition ob (w : 𝒲^op) : Set :=
      ⋀ w' : 𝒲, @hom 𝒲 w w' -> heap w' -> itree.ITree E (X w').

    Definition rst (w1 w2 : 𝒲^op) (w12 : @hom (𝒲^op) w1 w2) : ob w2 -> ob w1.
    Proof.
      move=> p w2' w2w2' h.
      apply: p.
      - by exact: (@seq 𝒲 _ _ _ w12 w2w2').
      - by exact: h.
    Defined.

    Definition prefunctor_mixin : Prefunctor.mixin_of 𝒲 SET.cat ob.
    Proof. by build=> w1 w2 w12; apply: rst. Defined.

    Canonical prefunctor : Prefunctor.type 𝒲 SET.cat.
    Proof. by esplit; apply: prefunctor_mixin. Defined.

    Definition functor_mixin : Functor.mixin_of _ _ prefunctor.
    Proof.
      build.
      - move=> w.
        apply: funE=> //= p; cbn.
        apply: dfunE=> w'.
        apply: funE=> ww'.
        apply: funE=> h.
        by rewrite /rst seqL.
      - move=> w1 w2 w3 w12 w23.
        apply: funE=> //= p; cbn.
        apply: dfunE=> w3'.
        apply: funE=> w3w3'.
        apply: funE=> h.
        by rewrite /rst (@seqA 𝒲 _ _ _ _ w12 w23 w3w3').
    Qed.

    Canonical functor : Functor.type 𝒲 SET.cat.
    Proof. esplit; apply: functor_mixin. Defined.

    Definition T : 𝒞+ := functor.
  End RightAdjunctive.
End RightAdjunctive.



Module LeftAdjoint.
  Section LeftAdjoint.
    Context (E : itree.Thy).

    Definition ob (A : 𝒞+) : 𝒞- :=
      LeftAdjunctive.T A E.

    Definition map_el (A B: 𝒞+) (f : A ~> B) : forall w, ob A w -> ob B w.
    Proof.
      move=> w.
      apply: Reflection.map.
      case=> w' [ww' [h u]].
      exists w', ww', h; move: u.
      by apply/itree.map/f.
    Defined.

    Definition map (A B : 𝒞+) (f : A ~> B) : ob A ~> ob B.
    Proof.
      build.
      - by apply: map_el.
      - abstract by
          build=> w w' ww';
          cbn; rewrite -?Reflection.map_cmp;
          congr Reflection.map.
    Defined.

    Definition prefunctor_mixin : Prefunctor.mixin_of 𝒞+ 𝒞- ob.
    Proof. by build; apply: map. Defined.

    Canonical prefunctor : Prefunctor.type 𝒞+ 𝒞-.
    Proof. by esplit; apply: prefunctor_mixin. Defined.

    Definition functor_mixin : Functor.mixin_of _ _ prefunctor.
    Proof.
      build.
      - move=> A.
        apply: NatTrans.ext.
        apply: dfunE=> w.
        cbn; rewrite -Reflection.map_id.
        congr Reflection.map.
        apply: funE=> //= ?.
        by rewrite itree.map_id.
      - move=> A B C f g.
        apply: NatTrans.ext.
        apply: dfunE=> w.
        cbn; rewrite -Reflection.map_cmp.
        congr Reflection.map.
        apply: funE=> //= ?.
        by rewrite itree.map_cmp.
    Qed.

    Canonical functor : Functor.type 𝒞+ 𝒞-.
    Proof. by esplit; apply: functor_mixin. Defined.
  End LeftAdjoint.
End LeftAdjoint.
