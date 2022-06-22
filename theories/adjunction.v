From sgdt Require Import preamble category functor.

Local Open Scope category_scope.
Set Universe Polymorphism.

Module LeftNerve.
  Section Defs.
    Context {𝒞 𝒟 : Category.type} (F : 𝒞 ~~> 𝒟).

    Definition ob : Product.cat (𝒞^op) 𝒟 -> TYPE.cat.
    Proof.
      move=> [c d].
      by exact: (F c ~> d).
    Defined.

    Definition prefunctor_mixin : Prefunctor.mixin_of (Product.cat (𝒞^op) 𝒟) TYPE.cat ob.
    Proof.
      build=> u v [f1 f2]; rewrite /ob //=; move=> h.
      by exact: (F @@ f1 >> h >> f2).
    Defined.

    Canonical prefunctor : Prefunctor.type (Product.cat (𝒞^op) 𝒟) TYPE.cat.
    Proof. by esplit; apply: prefunctor_mixin. Defined.

    Definition functor_mixin : Functor.mixin_of _ _ prefunctor.
    Proof.
      build.
      - move=> u.
        apply: funE=> //= ?.
        by cbn; rewrite fidn seqR seqL.
      - move=> u v w f g.
        apply: funE=> //= ?.
        by cbn; rewrite ? fseq ?seqA.
    Qed.

    Canonical functor : Functor.type (Product.cat (𝒞^op) 𝒟) TYPE.cat.
    Proof. by esplit; apply: functor_mixin. Defined.
  End Defs.
End LeftNerve.

Module RightNerve.
  Section Defs.
    Context {𝒞 𝒟 : Category.type} (G : 𝒟 ~~> 𝒞).

    Definition ob : Product.cat (𝒞^op) 𝒟 -> TYPE.cat.
    Proof.
      move=> [c d].
      by exact: (@hom 𝒞 c (G d)).
    Defined.

    Definition prefunctor_mixin : Prefunctor.mixin_of (Product.cat (𝒞^op) 𝒟) TYPE.cat ob.
    Proof.
      build=> u v //=; cbn; move=> [f1 f2] h.
      refine (f1 >> h >> G @@ f2).
    Defined.

    Canonical prefunctor : Prefunctor.type (Product.cat (𝒞^op) 𝒟) TYPE.cat.
    Proof. by esplit; apply: prefunctor_mixin. Defined.

    Definition functor_mixin : Functor.mixin_of _ _ prefunctor.
    Proof.
      build.
      - move=> u.
        apply: funE=> //= ?.
        by cbn; rewrite fidn seqR seqL.
      - move=> u v w f g.
        apply: funE=> //= ?.
        by cbn; rewrite ? fseq ?seqA.
    Qed.

    Canonical functor : Functor.type (Product.cat (𝒞^op) 𝒟) TYPE.cat.
    Proof. by esplit; apply: functor_mixin. Defined.
  End Defs.
End RightNerve.

Module Preadjunction.
  Section Defs.
    Context {𝒞 𝒟 : Category.type} (F : 𝒞 ~~> 𝒟) (U : 𝒟 ~~> 𝒞).

    Record type :=
      { fwd : LeftNerve.functor F ~> RightNerve.functor U;
        bwd : RightNerve.functor U ~> LeftNerve.functor F }.
  End Defs.

  Arguments fwd [𝒞] [𝒟] [F] [U].
  Arguments bwd [𝒞] [𝒟] [F] [U].
End Preadjunction.

Module Adjunction.
  Section Defs.
    Context {𝒞 𝒟 : Category.type} (F : 𝒞 ~~> 𝒟) (U : 𝒟 ~~> 𝒞).

    Record mixin_of (T : Preadjunction.type F U) :=
      { bwd_fwd : Preadjunction.fwd T >> Preadjunction.bwd T = idn _;
        fwd_bwd : Preadjunction.bwd T >> Preadjunction.fwd T = idn _ }.

    Record type := {transp; class: mixin_of transp}.
  End Defs.

  Arguments bwd_fwd [𝒞] [𝒟] [F] [U].
  Arguments fwd_bwd [𝒞] [𝒟] [F] [U].
End Adjunction.

Section Facts.

  Context {𝒞 𝒟 : Category.type} {F : 𝒞 ~~> 𝒟} {U : 𝒟 ~~> 𝒞} (T : Adjunction.type F U).

  Definition transpose : LeftNerve.functor F ~> RightNerve.functor U :=
    Preadjunction.fwd (Adjunction.transp _ _ T).

  Definition untranspose : RightNerve.functor U ~> LeftNerve.functor F :=
    Preadjunction.bwd (Adjunction.transp _ _ T).

End Facts.
