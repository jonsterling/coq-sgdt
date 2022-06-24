(** Based on https://github.com/xuanruiqi/categories/blob/master/functor.v and natural.v *)

From sgdt Require Import preamble category.

Local Open Scope category_scope.
Set Universe Polymorphism.

Module Prefunctor.
  Structure mixin_of(C D : Category.type) (F : C -> D) : Type :=
    Mixin {fhom : forall {x y : C} (f : x ~> y), F x ~> F y}.

  Structure type (C D : Category.type) := Pack {func : C -> D; class : mixin_of C D func}.

  Arguments func [C] [D].
  Arguments class [C] [D].

  Lemma ext {C D}: forall F G : type C D, forall h : func F = func G, rew h in class F = class G -> F = G.
  Proof.
    move=> [F homF] [G homG] //= FG.
    move: G FG homG.
    by apply: eq_ind=> homG//= ->.
  Qed.

  Module Exports.
    Coercion func : type >-> Funclass.

    Section fhom.
      Context {C D : Category.type}.
      Definition fhom (F : type C D) {x y : C} : x ~> y -> F x ~> F y.
        move=> xy.
        apply: fhom.
        - apply: class.
        - apply: xy.
      Defined.
    End fhom.

    Notation "F @@ f" := (fhom F f) (at level 50) : category_scope.
  End Exports.
End Prefunctor.

Export Prefunctor.Exports.

Module Functor.
  Section Laws.
    Context {C D : Category.type} (F : Prefunctor.type C D).
    Definition law_fidn := forall x : C, F @@ (idn x) = idn (F x).
    Definition law_fseq := forall (u v w : C) (uv : u ~> v) (vw : v ~> w), F @@ (uv >> vw) = F @@ uv >> F @@ vw.
  End Laws.

  Section ClassDef.
    Context (C D : Category.type).
    Structure mixin_of (F : Prefunctor.type C D) := Mixin {fidn : law_fidn F; fseq : law_fseq F}.
    Structure type := Pack {func : Prefunctor.type C D; class : mixin_of func}.
  End ClassDef.
  Arguments func [C] [D].

  Lemma ext {C D} : forall F G : type C D, func F = func G -> F = G.
  Proof.
    move=> [F hF] [G hG] //= FG.
    move: G FG hG.
    apply: eq_ind=> hG.
    by congr Pack.
  Qed.

  Module Exports.
    Coercion func : type >-> Prefunctor.type.
    Global Hint Unfold law_fidn law_fseq : core.
  End Exports.
End Functor.

Export Functor.Exports.

Infix "~~>" := Functor.type (at level 100) : category_scope.

Section Facts.
  Variables (C D : Category.type) (F : C ~~> D).

  Lemma fidn : Functor.law_fidn F.
  Proof. by case: (Functor.class _ _ F). Qed.

  Lemma fseq : Functor.law_fseq F.
  Proof. by case: (Functor.class _ _ F). Qed.
End Facts.

Module StrictCat.
  Definition hom_mixin : Hom.mixin_of Category.type.
  Proof. by build=> C D; exact (C ~~> D). Defined.

  Canonical hom : Hom.type.
  Proof. by esplit; apply: hom_mixin. Defined.

  Definition precat_mixin : Precategory.mixin_of hom.
  Proof.
    build.
    - move=> C D E CD DE.
      build.
      + build.
        * by move=> c; apply/DE/CD/c.
        * build=> x y xy.
          by do 2 apply: fhom.
      + build.
        * move=> x; cbn.
          by rewrite ?fidn.
        * move=> u v w uv vw; cbn.
          by rewrite ?fseq.
    - by move=> X; build; build.
  Defined.

  Canonical precat : Precategory.type.
  Proof. esplit; apply: precat_mixin. Defined.

  Definition cat_mixin : Category.mixin_of precat.
  Proof.
    build.
    - move=> C D E F CD DE EF.
      by apply: Functor.ext.
    - move=> C D CD.
      apply: Functor.ext; cbn.
      by case: CD; case=>+ []//=.
    - move=> C D CD.
      apply: Functor.ext.
      by case: CD; case=>+ []//=.
  Qed.

  Canonical cat : Category.type.
  Proof. esplit; apply: cat_mixin. Defined.
End StrictCat.

Canonical StrictCat.hom.
Canonical StrictCat.precat.
Canonical StrictCat.cat.

Module Compose.
  Section Defs.
    Context {C D E : Category.type} (F : C ~~> D) (G : D ~~> E).

    Definition ob : C -> E.
    Proof. by move/F/G. Defined.

    Definition prefunctor_mixin : Prefunctor.mixin_of C E ob.
    Proof.
      build=> x y f.
      by exact: (G @@ (F @@ f)).
    Defined.

    Canonical prefunctor : Prefunctor.type C E.
    Proof. by esplit; apply: prefunctor_mixin. Defined.

    Definition functor_mixin : Functor.mixin_of C E prefunctor.
    Proof.
      build.
      - move=> x; cbn.
        by rewrite ?fidn.
      - move=> x y z f g; cbn.
        by rewrite ?fseq.
    Qed.

    Canonical functor : C ~~> E.
    Proof. by esplit; apply: functor_mixin. Defined.
  End Defs.
End Compose.


Module NatTrans.
  Section ClassDef.
    Context {C : Category.type} {D : Category.type} (F G : C ~~> D).

    Definition natural (η : forall x, F x ~> G x) :=
      forall (x y : C) (f : x ~> y), F @@ f >> η y = η x >> G @@ f.

    Structure mixin_of (η : forall x, F x ~> G x) :=
      Mixin {_ : natural η}.

    Structure type := Pack {transf; class : mixin_of transf}.
  End ClassDef.

  Arguments class [C] [D] [F] [G] η : rename.
  Arguments transf [C] [D] [F] [G].

  Definition ext {C D} {F G : C ~~> D} : forall (f g : type F G), transf f = transf g -> f = g.
  Proof.
    move=> [f hf] [g hg] //= fg.
    move: g fg hg.
    apply: eq_ind=> hg.
    by congr Pack.
  Qed.

  Module Exports.
    Coercion transf : type >-> Funclass.
  End Exports.
End NatTrans.

Infix "~~~>" := NatTrans.type (at level 55) : category_scope.
Export NatTrans.Exports.

Section naturality.
  Context {C D} {F G : C ~~> D} (η : F ~~~> G).

  Lemma naturality : NatTrans.natural _ _ η.
  Proof. by case/NatTrans.class: η. Qed.
End naturality.


Module NatCompose.
  Section Defs.
    Context {C : Category.type} {D : Category.type} {F G H : C ~~> D} (f : F ~~~> G) (g : G ~~~> H).

    Definition fam : forall x, F x ~> H x.
    Proof.
      move=> x.
      by exact: (f x >> g x).
    Defined.

    Definition mixin : NatTrans.mixin_of _ _ fam.
    Proof.
      build=> x y xy.
      rewrite /fam.
      rewrite seqA.
      rewrite naturality.
      rewrite -seqA.
      rewrite naturality.
      by rewrite seqA.
    Qed.

    Canonical transf : F ~~~> H.
    Proof. by esplit; apply: mixin. Defined.
  End Defs.
End NatCompose.

Module NatIdn.
  Section Defs.
    Context {C D : Category.type} (F : C ~~> D).

    Definition fam : forall x, F x ~> F x.
    Proof.
      move=> x.
      apply: idn.
    Defined.

    Definition mixin : NatTrans.mixin_of _ _ fam.
    Proof.
      build=> x y xy.
      by rewrite /fam seqR seqL.
    Defined.

    Canonical transf : F ~~~> F.
    Proof. by esplit; apply: mixin. Defined.
  End Defs.
End NatIdn.

Module FunctorCategory.
  Section FunctorCategory.
    Context (C : Category.type) (D : Category.type).

    Definition hom_mixin : Hom.mixin_of (C ~~> D).
    Proof. by build=> f g; exact (f ~~~> g). Defined.

    Canonical hom : Hom.type.
    Proof. esplit; apply: hom_mixin. Defined.

    Definition functor_seq : Precategory.op_seq hom.
    Proof.
      move=> F G H FG GH.
      build.
      - move=> x; exact: (FG x >> GH x).
      - abstract by build=> x y xy; rewrite seqA naturality -seqA naturality seqA.
    Defined.

    Definition functor_idn : Precategory.op_idn hom.
    Proof.
      move=> F.
      build.
      - by move=> ?; apply: idn.
      - abstract by build=> x y f; rewrite seqL seqR.
    Defined.

    Definition precat_mixin : Precategory.mixin_of hom.
    Proof.
      build.
      - apply: functor_seq.
      - apply: functor_idn.
    Defined.

    Canonical precat : Precategory.type.
    Proof. esplit; apply: precat_mixin. Defined.

    Definition cat_mixin : Category.mixin_of precat.
    Proof.
      build.
      - move=> F G H I FG GH HI.
        apply/NatTrans.ext/dfunE=> x//=.
        by rewrite seqA.
      - move=> F G FG.
        apply/NatTrans.ext/dfunE=> x//=.
        by rewrite seqL.
      - move=> F G FG.
        apply/NatTrans.ext/dfunE=> x//=.
        by rewrite seqR.
    Qed.

    Canonical cat : Category.type.
    Proof. esplit; apply: cat_mixin. Defined.
  End FunctorCategory.
End FunctorCategory.

Canonical FunctorCategory.hom.
Canonical FunctorCategory.precat.
Canonical FunctorCategory.cat.

Notation "Cat[ C , D ]" := (FunctorCategory.cat C D).


Module ConstantFunctor.
  Section ConstantFunctor.
    Context {C D : Category.type} (d : D).

    Definition const : Functor.type C D.
    Proof.
      build.
      - build.
        + by move=> _; exact: d.
        + by build=> _ _ _; apply: idn.
      - by build=> x y z xy yz; rewrite seqL.
    Defined.
  End ConstantFunctor.
End ConstantFunctor.

Notation "{{ x }}" := (ConstantFunctor.const x) : category_scope.
Canonical ConstantFunctor.const.
