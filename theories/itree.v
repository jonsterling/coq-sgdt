From sgdt Require Import preamble guarded category functor adjunction.
From HB Require Import structures.

(** Guarded Interaction Trees. *)

Local Open Scope category_scope.
Set Primitive Projections.
Set Universe Polymorphism.

Record Thy :=
  {op :> Set;
   bdry : op -> Set}.

Arguments bdry [_] _.

Section ITree.
  Context (E : Thy) (R : Set).

  Inductive ITree_F (T : Set) : Set :=
  | Ret (r : R)
  | Do (e : E) (k : bdry e -> T).

  Definition ITree_F_map {S T : Set} : (S -> T) -> (ITree_F S -> ITree_F T).
  Proof.
    move=> α; case.
    - apply: Ret.
    - move=> e f.
      apply: Do.
      by move/f/α.
  Defined.

  Definition ITree_F_iso {S T : Set} : (S ≅ T) -> (ITree_F S ≅ ITree_F T).
  Proof.
    move=> α.
    unshelve esplit.
    - apply/ITree_F_map/(fwd α).
    - apply/ITree_F_map/(bwd α).
    - case=>//=.
      by move=> ??; congr Do; apply: funE=>?; rewrite fwd_bwd.
    - case=>//=.
      by move=> ??; congr Do; apply: funE=>?; rewrite bwd_fwd.
  Defined.

  Definition ITree : Set := Later.loeb (fun T => ITree_F (dlater T)).

  Global Instance ITree_conn : Connective ITree (ITree_F (▷ ITree)).
  Proof. by split; apply/iso_trans/Later.loeb_iso/ITree_F_iso/dlater_next_iso. Defined.

  Definition η : R -> ITree.
  Proof. by move=> x; apply/intro/Ret/x. Defined.
End ITree.

Arguments Ret [E] [R] [T].
Arguments Do [E] [R] [T].
Arguments η [E] [R].


Module Action.
  Record type (E : Thy) (A : Set) :=
    {eff : E; kont : bdry eff -> ▷ A}.

  Arguments eff [_] [_].
  Arguments kont [_] [_].

  Definition map {E} {A B : Set} (f : A -> B) : type E A -> type E B.
  Proof.
    move=> α.
    unshelve esplit.
    - exact: eff α.
    - move=> /(kont α).
      apply/Later.map/f.
  Defined.

  Lemma map_cmp {E : Thy} {A B C : Set} {f : A -> B} {g : B -> C} (x : type E A) : map (g \o f) x = map g (map f x).
  Proof.
    rewrite /map.
    congr Build_type.
    apply: funE => ?.
    by rewrite Later.map_assoc.
  Qed.

  Lemma map_id {E : Thy} {A : Set} {x : type E A} : map id x = x.
  Proof.
    case: x => ? ?.
    rewrite /map; congr Build_type.
    apply: funE => ?.
    by rewrite Later.map_id.
  Qed.
End Action.


Module Alg.
  Record mixin_of (E : Thy) (A : Set) : Set :=
    {do_action : Action.type E A -> A}.

  Structure type E : Type := Pack {sort; class : mixin_of E sort}.

  Module Exports.
    Coercion sort : type >-> Sortclass.
  End Exports.
End Alg.

Export Alg.Exports.

Definition do_action {E : Thy} {X : Alg.type E} :=
  Alg.do_action _ _ (Alg.class E X).

Module AlgHom.
  Record mixin_of {E : Thy} (A B : Alg.type E) (f : A -> B) : Prop :=
    {pres_do_action : forall α, f (do_action α) = do_action (Action.map f α) }.

  Structure type {E} (A B : Alg.type E) := Pack {map; class : mixin_of A B map}.

  Module Exports.
    Coercion map : type >-> Funclass.
  End Exports.

  Lemma ext {E} {A B : Alg.type E} : forall f g : type A B, map _ _ f = map _ _ g -> f = g.
  Proof.
    case=> f hf; case=> g hg //= fg.
    move: g fg hg.
    apply: eq_ind=> ?.
    by congr Pack.
  Qed.
End AlgHom.

Export AlgHom.Exports.

Definition pres_do_action {E : Thy} {X Y : Alg.type E} (f : AlgHom.type X Y) :
  forall α, f (do_action α) = do_action (Action.map f α).
Proof.
  apply: AlgHom.pres_do_action.
  apply: AlgHom.class.
Defined.

Definition do {E : Thy} {A : Alg.type E} (e : E) (k : bdry e -> ▷ A) : A.
Proof. apply: do_action; esplit; apply: k. Defined.


Module ALG.
  Section ALG.
    Context (E : Thy).

    Definition hom_mixin : Hom.mixin_of (Alg.type E).
    Proof. build; apply AlgHom.type. Defined.

    Canonical hom : Hom.type.
    Proof. esplit; apply: hom_mixin. Defined.

    Definition precat_mixin : Precategory.mixin_of hom.
    Proof.
      build.
      - move=> X Y Z f g.
        build.
        + by exact: (g \o f).
        + abstract by build=> α; case: f=> f hf; case: g=> g hg; rewrite Action.map_cmp -?pres_do_action.
      - move=> X.
        build.
        + by exact: id.
        + abstract by build=> α; rewrite Action.map_id.
    Defined.

    Canonical precat : Precategory.type.
    Proof. esplit; apply: precat_mixin. Defined.

    Definition cat_mixin : Category.mixin_of precat.
    Proof. by build; move=>*; apply: AlgHom.ext. Qed.

    Canonical cat : StrictCat.cat.
    Proof. esplit; apply: cat_mixin. Defined.
  End ALG.
End ALG.

Lemma pres_do {E} {A B : Alg.type E} {f : AlgHom.type A  B} :
  forall e (k : bdry e -> ▷ A), f (do e k) = do e (Later.map f \o k).
Proof.
  move=> e k.
  rewrite /do.
  apply: pres_do_action.
Qed.

Module Forgetful.
  Section Defs.
    Context (E : Thy).

    Definition ob (X : ALG.cat E) : Set := X.

    Definition prefunctor_mixin : Prefunctor.mixin_of (ALG.cat E) SET.cat ob.
    Proof.
      build.
      move=> X Y f.
      by apply: f.
    Defined.

    Canonical prefunctor : Prefunctor.type (ALG.cat E) SET.cat.
    Proof. by esplit; apply: prefunctor_mixin. Defined.

    Definition functor_mixin : Functor.mixin_of (ALG.cat E) SET.cat prefunctor.
    Proof. by build. Qed.

    Canonical functor : (ALG.cat E) ~~> SET.cat.
    Proof. by esplit; apply: functor_mixin. Defined.
  End Defs.
End Forgetful.

Module Free.
  Section Defs.
    Context (E : Thy).

    Definition ob_do_action {R : Set} : Action.type E (ITree E R) -> ITree E R.
    Proof. by move=> α; apply/intro/Do/Action.kont/α. Defined.

    Definition ob_alg_mixin {R : Set} : Alg.mixin_of E (ITree E R).
    Proof. by build; apply: ob_do_action. Defined.

    Canonical ob (R : Set) : ALG.cat E.
    Proof. by esplit; apply: ob_alg_mixin. Defined.

    Section Ext.
      Context {A : Set} {B : ALG.cat E}.

      Definition extends (f : A -> B) (h : ITree E A -> B) : Prop :=
        forall x, h (η x) = f x.

      Lemma extends_unique (f : A -> B) (h h' : AlgHom.type (ob A) B) : extends f h -> extends f h' -> h = h'.
      Proof.
        move=> hext h'ext.
        apply: AlgHom.ext.
        apply: funE.
        apply: push_conn.
        apply: Later.loeb=>ih.
        case.
        - by move=>?; rewrite hext h'ext.
        - move=> e k.
          have -> : (intro (Do e k) = do e k) by [].
          rewrite ? pres_do. congr do.
          apply: funE=>/=i.
          congr Later.ap.
          apply: Later.from_eq.
          move: ih.
          apply: Later.map => H'.
          apply: funE.
          by apply: push_conn.
      Qed.

      Definition ext (f : A -> B) : ITree E A -> B.
      Proof.
        apply: Later.loeb=>f'.
        case/elim.
        - exact: f.
        - move=> e k.
          apply: (do e); move/k.
          move: f'.
          apply: Later.ap.
      Defined.


      Section ExtLaws.
        Lemma ext_extends : forall f : A -> B, extends f (ext f).
        Proof. by move=>??; rewrite /ext Later.loeb_unfold /η beta. Qed.

        Definition ext_hom_mixin (f : A -> B) : AlgHom.mixin_of _ _ (ext f).
        Proof. by build; case=> ??; rewrite {1}/ext Later.loeb_unfold beta. Qed.

        Canonical ext_hom (f : A -> B) : AlgHom.type (ob A) B.
        Proof. by esplit; apply: ext_hom_mixin. Defined.
      End ExtLaws.
    End Ext.

    Section Map.
      Context {A B : Set}.

      Definition map (f : A -> B) : ob A ~> ob B.
      Proof.
        apply: ext_hom=> x.
        apply/η/f/x.
      Defined.

    End Map.

    Definition prefunctor_mixin : Prefunctor.mixin_of SET.cat (ALG.cat E) ob.
    Proof. by build=> ? ?; apply: map. Defined.

    Canonical prefunctor : Prefunctor.type SET.cat (ALG.cat E).
    Proof. by esplit; apply: prefunctor_mixin. Defined.

    Definition functor_mixin : Functor.mixin_of _ _ prefunctor.
    Proof.
      build.
      - move=> x.
        apply: AlgHom.ext; apply: funE => u.
        congr AlgHom.map.
        apply: extends_unique.
        + by move=> ?; apply: ext_extends.
        + by [].
      - move=> x y z f g.
        apply: AlgHom.ext; apply: funE => u.
        congr AlgHom.map.
        by apply: extends_unique=> ?; rewrite //= ?ext_extends.
    Qed.

    Definition functor : Functor.type SET.cat (ALG.cat E).
    Proof. esplit; apply: functor_mixin. Defined.
  End Defs.
End Free.

Module TranspFwd.
  Section Defs.
    Context (E : Thy).

    Definition transf_fam : forall U, LeftNerve.functor (Free.functor E) U ~> RightNerve.functor (Forgetful.functor E) U.
    Proof.
      move=> [A X] f a.
      by apply/f/η/a.
    Defined.

    Lemma transf_mixin : NatTrans.mixin_of _ _ transf_fam.
    Proof.
      build; case=> A X; case=> B Y; case=> f g.
      apply: funE; cbn.
      move=> h.
      apply: funE=> b //=.
      congr (g _).
      congr (h _).
      by rewrite Free.ext_extends.
    Qed.

    Canonical transf : LeftNerve.functor (Free.functor E) ~> RightNerve.functor (Forgetful.functor E).
    Proof. by esplit; apply: transf_mixin. Defined.
  End Defs.
End TranspFwd.

Module TranspBwd.
  Section Defs.
    Context (E : Thy).

    Definition transf_fam : forall U, RightNerve.functor (Forgetful.functor E) U ~> LeftNerve.functor (Free.functor E) U.
    Proof.
      move=> [A X]; cbn; move=> f.
      by apply/Free.ext_hom/f.
    Defined.

    Lemma transf_mixin : NatTrans.mixin_of _ _ transf_fam.
    Proof.
      build; case=> A X; case=> B Y; case=> f g.
      apply: funE=> h.
      rewrite /transf_fam.
      apply: Free.extends_unique.
      - by move=> ?; apply: Free.ext_extends.
      - move=> b //=.
        by rewrite ?Free.ext_extends.
    Qed.

    Canonical transf : RightNerve.functor (Forgetful.functor E) ~> LeftNerve.functor (Free.functor E).
    Proof. by esplit; apply: transf_mixin. Defined.
  End Defs.
End TranspBwd.

Module EilenbergMoore.
  Section Defs.
    Context (E : Thy).

    Definition preadjunction : Preadjunction.type (Free.functor E) (Forgetful.functor E).
    Proof.
      build.
      - by apply: TranspFwd.transf.
      - by apply: TranspBwd.transf.
    Defined.

    Definition adjunction_mixin : Adjunction.mixin_of (Free.functor E) (Forgetful.functor E) preadjunction.
    Proof.
      build.
      - apply: NatTrans.ext.
        apply: dfunE; case=> A X //=.
        apply: funE=> f.
        apply: Free.extends_unique.
        + by move=> ?; apply: Free.ext_extends.
        + by [].
      - apply: NatTrans.ext.
        apply: dfunE; case=> A X //=.
        apply: funE=> f.
        apply: funE=> a.
        by apply: Free.ext_extends.
    Qed.

    Canonical adjunction : Adjunction.type (Free.functor E) (Forgetful.functor E).
    Proof. by esplit; apply: adjunction_mixin. Defined.
  End Defs.
End EilenbergMoore.

Notation "f ♯" := (Free.ext f) (at level 0).
