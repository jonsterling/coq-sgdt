Require Import ssrbool.
From extructures Require Import ord fmap fset.
From sgdt Require Import preamble impredicative guarded category functor adjunction.
From sgdt Require itree.

Set Bullet Behavior "Strict Subproofs".
Set Universe Polymorphism.

Module World.
  Definition world (T : Type) : Type := {fmap nat -> T}.

  Section World.
    Universe u.
    Context (T : Type@{u}).

    Definition world_leq (U V : world T) : Prop :=
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
  World.cat T ~> TYPE.cat@{_ Set}.

Definition 𝒯 : Type.
Proof. by apply: Later.loeb=> /dlater; apply: ℱ. Defined.

Local Lemma 𝒯_unfold : 𝒯 = ℱ (▷ 𝒯).
Proof. by rewrite dlater_next_eq /𝒯 {1} Later.loeb_unfold. Qed.

Global Instance 𝒯_conn : Connective 𝒯 (ℱ (▷ 𝒯)).
Proof. by build; rewrite -𝒯_unfold; apply: iso_id. Qed.

Opaque 𝒯_conn.


Notation 𝒲 := (World.cat (▷ 𝒯)).
Notation "𝒞+" := Cat[𝒲, TYPE.cat@{_ Set}].
Notation "𝒞-[ E ]" := Cat[𝒲^op, itree.ALG.cat E].


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

    Definition prefunctor_mixin : Prefunctor.mixin_of 𝒲 (TYPE.cat@{_ Set}) ob.
    Proof. by build; apply: rst. Defined.

    Canonical prefunctor : Prefunctor.type 𝒲 (TYPE.cat@{_ Set}).
    Proof. by esplit; apply: prefunctor_mixin. Defined.

    Lemma functor_mixin : Functor.mixin_of _ _ prefunctor.
    Proof. by build; move=> *; apply: funE=> //=; case=> *; apply: subE. Qed.

    Canonical functor : Functor.type 𝒲 (TYPE.cat@{_ Set}).
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

Module HEAP.
  Definition cat := Discrete.cat {w : 𝒲 & heap w}.
End HEAP.

Notation ℋ := HEAP.cat.

Module PointwiseAlgAdjunction.
  Section Defs.
    Context (E : itree.Thy).
    Definition adj := PointwiseLiftingAdjunction.adj (𝒲 ^op) _ _ (itree.EilenbergMoore.adj E).
  End Defs.
End PointwiseAlgAdjunction.

Module Δ.
  Module Psh.
    Section Defs.
      Context (A : Cat[𝒲, SET.cat]).

      Definition ob : ℋ -> SET.cat.
      Proof. by move/pi1; apply: A. Defined.

      Definition prefunctor_mixin : Prefunctor.mixin_of _ _ ob.
      Proof.
        build=> h1 h2 h12 x.
        by rewrite -h12.
      Defined.

      Canonical prefunctor : Prefunctor.type ℋ SET.cat.
      Proof. by esplit; apply: prefunctor_mixin. Defined.

      Definition functor_mixin : Functor.mixin_of _ _ prefunctor.
      Proof.
        build=> h1 h2 h3 h12.
        move: h2 h12.
        apply: eq_ind.
        by move: h3; apply: eq_ind.
      Qed.

      Canonical functor : ℋ ~~> SET.cat.
      Proof. by esplit; apply: functor_mixin. Defined.
    End Defs.
  End Psh.

  Definition prefunctor_mixin : Prefunctor.mixin_of _ _ Psh.functor.
  Proof.
    build=> A B.
    cbn.
    build.
    - case=> w h; apply: f.
    - abstract by build=> h1; apply: eq_ind.
  Defined.

  Canonical prefunctor : Prefunctor.type Cat[𝒲,SET.cat] Cat[ℋ, SET.cat].
  Proof. by esplit; apply: prefunctor_mixin. Defined.

  Definition functor_mixin : Functor.mixin_of _ _ prefunctor.
  Proof.
    build.
    - by move=> ?; apply: NatTrans.ext.
    - by move=> ? ? ? ? ?; apply: NatTrans.ext.
  Qed.

  Canonical functor : Cat[𝒲, SET.cat] ~~> Cat[ℋ, SET.cat].
  Proof. by esplit; apply: functor_mixin. Defined.
End Δ.

Module Σ.
  Module Psh.
    Section Defs.
      Context (A : Cat[ℋ, TYPE.cat]).

      Definition ob : 𝒲^op -> TYPE.cat.
      Proof.
        move=> w.
        by refine {h : ℋ & @hom 𝒲 w (pi1 h) × A h}.
      Defined.

      Definition prefunctor_mixin : Prefunctor.mixin_of (𝒲^op) TYPE.cat ob.
      Proof.
        build=> w1 w2 w21 [h [ρ a]].
        exists h; split.
        - by exact: (@seq 𝒲 _ _ _ w21 ρ).
        - by exact: a.
      Defined.

      Canonical prefunctor : Prefunctor.type (𝒲^op) TYPE.cat.
      Proof. esplit; apply: prefunctor_mixin. Defined.

      Definition functor_mixin : Functor.mixin_of _ _ prefunctor.
      Proof.
        build.
        - move=> w.
          apply: funE.
          case=> h [ρ a].
          by cbn; rewrite (@seqL 𝒲).
        - move=> w1 w2 w3 w12 w23.
          apply: funE; case=> h [ρ a].
          by cbn; rewrite (@seqA 𝒲).
      Qed.

      Canonical functor : 𝒲^op ~~> TYPE.cat.
      Proof. by esplit; apply: functor_mixin. Defined.
    End Defs.
  End Psh.

  Definition prefunctor_mixin : Prefunctor.mixin_of _ _ Psh.functor.
  Proof.
    build=> A B f.
    build.
    - move=> w; case=> h [ρ a].
      exists h, ρ.
      by apply: f.
    - by build.
  Defined.

  Canonical prefunctor : Prefunctor.type Cat[ℋ, TYPE.cat] Cat[𝒲^op, TYPE.cat].
  Proof. by esplit; apply: prefunctor_mixin. Defined.

  Definition functor_mixin : Functor.mixin_of _ _ prefunctor.
  Proof.
    build.
    - by move=> ?; apply: NatTrans.ext.
    - by move=> ?????; apply: NatTrans.ext.
  Qed.

  Canonical functor : Cat[ℋ, TYPE.cat] ~~> Cat[𝒲^op, TYPE.cat].
  Proof. by esplit; apply: functor_mixin. Defined.
End Σ.


Module Σ_Set.
  Definition functor : Cat[ℋ, SET.cat] ~~> Cat[𝒲^op, SET.cat].
  Proof.
    apply: Compose.functor.
    - by apply/PointwiseLifting.functor/SetToType.functor.
    - apply: Compose.functor.
      + by apply: Σ.functor.
      + by apply/PointwiseLifting.functor/TypeToSet.functor.
  Defined.
End Σ_Set.
