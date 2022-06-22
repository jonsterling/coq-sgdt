(* Based on https://github.com/xuanruiqi/categories/blob/master/category.v by Xuanruiqi. *)

From sgdt Require Import preamble.
Declare Scope category_scope.
Delimit Scope category_scope with cat.

Set Universe Polymorphism.
Set Primitive Projections.

Reserved Infix "~>" (at level 90, right associativity).
Reserved Infix "\\o" (at level 40, left associativity).
Reserved Notation "C '^op'" (at level 20, left associativity).

Module Hom.
  Structure mixin_of (obj : Type) :=
    Mixin {hom : obj -> obj -> Type}.

  Structure type : Type := Pack {sort; class : mixin_of sort}.

  Module Exports.
    Coercion sort : type >-> Sortclass.
    Global Bind Scope category_scope with sort.
  End Exports.
End Hom.

Export Hom.Exports.

Definition hom {C} := Hom.hom _ (Hom.class C).
Notation "U ~> V" := (hom U V) : category_scope.

Module Precategory.
  Local Open Scope category_scope.

  Section Ops.
    Context (C : Hom.type).
    Definition op_seq := forall (X Y Z : C), X ~> Y -> Y ~> Z -> X ~> Z.
    Definition op_idn := forall X : C, X ~> X.
  End Ops.

  Structure mixin_of (C : Hom.type) :=
    Mixin
      {seq : op_seq C;
       idn : op_idn C}.

  Structure type : Type := Pack {sort; class : mixin_of sort}.

  Module Exports.
    Coercion sort : type >-> Hom.type.
    Global Hint Unfold op_idn op_seq : core.
  End Exports.
End Precategory.

Export Precategory.Exports.

Definition seq {C} {x y z} := @Precategory.seq _ (Precategory.class C) x y z.
Definition idn {C} := Precategory.idn _ (Precategory.class C).

Infix ">>" := seq (at level 60) : category_scope.

Module Category.
  Local Open Scope category_scope.

  Section Laws.
    Context (C : Precategory.type).

    Definition law_seqA := forall (X Y Z W : C) (f : X ~> Y) (g : Y ~> Z) (h : Z ~> W), seq f (seq g h) = seq (seq f g) h.
    Definition law_seqL := forall (X Y : C) (f : X ~> Y), seq (idn X) f = f.
    Definition law_seqR := forall (X Y : C) (f : X ~> Y), seq f (idn Y) = f.

  End Laws.

  Structure mixin_of (C : Precategory.type) : Prop :=
    Mixin
      {seqA : law_seqA C;
       seqL : law_seqL C;
       seqR : law_seqR C}.

  Structure type : Type := Pack {sort; class : mixin_of sort}.

  Module Exports.
    Coercion sort : type >-> Precategory.type.

    Global Hint Unfold law_seqA law_seqL law_seqR : core.
  End Exports.
End Category.

Export Category.Exports.

Section Facts.
  Context {C : Category.type}.

  Fact seqA : Category.law_seqA C.
  Proof. by case: (Category.class C). Qed.

  Fact seqL : Category.law_seqL C.
  Proof. by case: (Category.class C). Qed.

  Fact seqR : Category.law_seqR C.
  Proof. by case: (Category.class C). Qed.
End Facts.


Local Open Scope category_scope.

Module Opposite.

  Section Opposite.
    Context (C : Category.type).


    Definition hom_mixin : Hom.mixin_of C.
    Proof. build=> x y; exact: (y ~> x). Defined.

    Canonical hom : Hom.type.
    Proof. esplit; apply: hom_mixin. Defined.

    Definition precat_mixin : Precategory.mixin_of hom.
    Proof.
      build.
      - move=> x y z xy yz.
        exact: (yz >> xy).
      - move=> x; apply: idn.
    Defined.

    Canonical precat : Precategory.type.
    Proof. esplit; apply: precat_mixin. Defined.

    Definition cat_mixin : Category.mixin_of precat.
    Proof.
      build.
      - move=> u v w x uv vw wx.
        by rewrite /seq//=seqA.
      - move=> u v uv.
        by rewrite /seq//=seqR.
      - move=> u v uv.
        by rewrite/seq//=seqL.
    Qed.

    Canonical cat : Category.type.
    Proof. esplit; apply: cat_mixin. Defined.
  End Opposite.
End Opposite.

Canonical Opposite.hom.
Canonical Opposite.precat.
Canonical Opposite.cat.

Notation "C '^op' " := (Opposite.cat C) : category_scope.

Module FullSubcategory.
  Section Defs.
    Context (C : Category.type) (P : C -> Prop).

    Definition hom_mixin : Hom.mixin_of {x : C | P x}.
    Proof. by build=> x y; exact: (pi1 x ~> pi1 y). Defined.

    Canonical hom : Hom.type.
    Proof. by esplit; apply: hom_mixin. Defined.

    Definition precat_mixin : Precategory.mixin_of hom.
    Proof.
      build.
      - by move=> x y z; apply: seq.
      - by move=> x; apply: idn.
    Defined.

    Canonical precat : Precategory.type.
    Proof. by esplit; apply: precat_mixin. Defined.

    Definition cat_mixin : Category.mixin_of precat.
    Proof.
      build.
      - by move=>*; apply: seqA.
      - by move=>*; apply: seqL.
      - by move=>*; apply: seqR.
    Defined.

    Canonical cat : Category.type.
    Proof. by esplit; apply: cat_mixin. Defined.
  End Defs.
End FullSubcategory.

Canonical FullSubcategory.hom.
Canonical FullSubcategory.precat.
Canonical FullSubcategory.cat.

Set Printing Universes.

Module TYPE.
  Definition hom_mixin : Hom.mixin_of Type.
  Proof. constructor=> A B; exact: (A -> B). Defined.

  Canonical hom : Hom.type.
  Proof. by esplit; apply: hom_mixin. Defined.

  Definition precat_mixin : Precategory.mixin_of hom.
  Proof.
    build.
    - by move=> A B C f g; exact: (g \o f).
    - by move=> A; exact: id.
  Defined.

  Canonical precat : Precategory.type.
  Proof. by esplit; apply: precat_mixin. Defined.

  Definition cat_mixin : Category.mixin_of precat.
  Proof. by []. Defined.


  Canonical cat : Category.type.
  Proof. by esplit; apply: cat_mixin. Defined.
End TYPE.

Module SET.
  Definition hom_mixin : Hom.mixin_of Set.
  Proof. constructor=> A B; exact: (A -> B). Defined.

  Canonical hom : Hom.type.
  Proof. by esplit; apply: hom_mixin. Defined.

  Definition precat_mixin : Precategory.mixin_of hom.
  Proof.
    build.
    - by move=> A B C f g; exact: (g \o f).
    - by move=> A; exact: id.
  Defined.

  Canonical precat : Precategory.type.
  Proof. by esplit; apply: precat_mixin. Defined.

  Definition cat_mixin : Category.mixin_of precat.
  Proof. by []. Defined.


  Canonical cat : Category.type.
  Proof. by esplit; apply: cat_mixin. Defined.
End SET.
