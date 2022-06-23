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

Notation "F ⊣ U" := (Adjunction.type F U) (at level 100).

Section Facts.

  Context {𝒞 𝒟 : Category.type} {F : 𝒞 ~~> 𝒟} {U : 𝒟 ~~> 𝒞} (T : F ⊣ U).

  Definition transpose : LeftNerve.functor F ~> RightNerve.functor U :=
    Preadjunction.fwd (Adjunction.transp _ _ T).

  Definition untranspose : RightNerve.functor U ~> LeftNerve.functor F :=
    Preadjunction.bwd (Adjunction.transp _ _ T).

  Definition untranspose_transpose : transpose >> untranspose = idn _ :=
    Adjunction.bwd_fwd _ (Adjunction.class _ _ T).

  Definition transpose_untranspose : untranspose >> transpose = idn _ :=
    Adjunction.fwd_bwd _ (Adjunction.class _ _ T).
End Facts.

Module HorizontalComposition.

  Section Defs.
    Context
      {𝒞 𝒟 ℰ : Category.type}
        {F1 : 𝒞 ~> 𝒟}
        {G1 : 𝒟 ~> 𝒞}
        {F2 : 𝒟 ~> ℰ}
        {G2 : ℰ ~> 𝒟}
        (T1 : F1 ⊣ G1)
        (T2 : F2 ⊣ G2).


    Definition transp_fwd_fam : forall U, LeftNerve.functor (F1 >> F2) U ~> RightNerve.functor (G2 >> G1) U.
    Proof.
      case=> c e //= f.
      apply: (transpose T1 (Sig c (G2 e))).
      apply: (transpose T2 (Sig (F1 c) e)).
      apply: f.
    Defined.

    Definition transp_bwd_fam : forall U, RightNerve.functor (G2 >> G1) U ~> LeftNerve.functor (F1 >> F2) U.
    Proof.
      case=> c e //= f.
      apply: (untranspose T2 (Sig (F1 c) e)).
      apply: (untranspose T1 (Sig c (G2 e))).
      apply: f.
    Defined.

    Definition transp_fwd_mixin : NatTrans.mixin_of _ _ transp_fwd_fam.
    Proof.
      build; case=> c1 e1; case=> c2 e2; case=> f1 f2.
      apply: funE=> x.
      have Q1 := unfunE _ _ (naturality (transpose T1) (Sig c1 (G2 e1)) (Sig c2 (G2 e2)) (Sig f1 (G2 @@ f2))).
      have Q2 := unfunE _ _ (naturality (transpose T2) (Sig (F1 c1) e1) (Sig (F1 c2) e2) (Sig (F1 @@ f1) f2)).
      cbn in Q2, Q1.
      by cbn; rewrite /transp_fwd_fam Q2 Q1.
    Qed.

    Definition transp_bwd_mixin : NatTrans.mixin_of _ _ transp_bwd_fam.
    Proof.
      build; case=> c1 e1; case=> c2 e2; case=> f1 f2.
      apply: funE=> x.
      have Q2 := unfunE _ _ (naturality (untranspose T2) (Sig (F1 c1) e1) (Sig (F1 c2) e2) (Sig (F1 @@ f1) f2)).
      have Q1 := unfunE _ _ (naturality (untranspose T1) (Sig c1 (G2 e1)) (Sig c2 (G2 e2)) (Sig f1 (G2 @@ f2))).
      cbn in Q1, Q2.
      by cbn; rewrite /transp_bwd_fam Q1 Q2.
    Qed.

    Canonical transp_fwd : LeftNerve.functor (F1 >> F2) ~> RightNerve.functor (G2 >> G1).
    Proof. by esplit; apply: transp_fwd_mixin. Defined.

    Canonical transp_bwd : RightNerve.functor (G2 >> G1) ~> LeftNerve.functor (F1 >> F2).
    Proof. by esplit; apply: transp_bwd_mixin. Defined.

    Canonical preadj : Preadjunction.type (F1 >> F2) (G2 >> G1).
    Proof.
      build.
      - apply: transp_fwd.
      - apply: transp_bwd.
    Defined.

    Lemma eta_cmp {A B C : Type} (f : A -> B) (g : B -> C) : (fun x => g (f x)) = g \o f.
    Proof. by []. Qed.

    Lemma cmp_assoc {A B C D : Type} (f : A -> B) (g : B -> C) (h : C -> D) : h \o (g \o f) = (h \o g) \o f.
    Proof. by []. Qed.

    (* Yuck *)
    Definition adj_mixin : Adjunction.mixin_of _ _ preadj.
    Proof.
      build.
      - apply: NatTrans.ext.
        apply: dfunE; case=> c e; cbn.
        rewrite /transp_fwd_fam /transp_bwd_fam.
        rewrite [fun f => untranspose T2 _ _]eta_cmp.
        rewrite [fun f => transpose T1 _ _]eta_cmp.
        rewrite -cmp_assoc.
        rewrite [untranspose T1 _ \o _]cmp_assoc.
        rewrite (_ :  untranspose T1 _ \o transpose T1 _ = (transpose T1 >> untranspose T1) _); first by [].
        rewrite untranspose_transpose.
        rewrite (_ : (idn (LeftNerve.functor F1) {| pi1 := c; pi2 := G2 e |} \o transpose T2 {| pi1 := F1 c; pi2 := e|}) = transpose T2 _); first by [].
        rewrite (_ : untranspose T2 _ \o transpose T2 {| pi1 := F1 c; pi2 := e |} = (transpose T2 >> untranspose T2) _); first by [].
        by rewrite untranspose_transpose.

      - apply: NatTrans.ext.
        apply: dfunE; case=> c e; cbn.
        rewrite /transp_fwd_fam /transp_bwd_fam.
        rewrite [fun f => untranspose T2 _ _]eta_cmp.
        rewrite [fun f => transpose T1 _ _]eta_cmp.
        rewrite -cmp_assoc.
        rewrite [transpose T2 _ \o _]cmp_assoc.
        rewrite (_ : transpose T2 {| pi1 := F1 c; pi2 := e |} \o untranspose T2 {| pi1 := F1 c; pi2 := e |} = (untranspose T2 >> transpose T2) _); first by [].
        rewrite transpose_untranspose.
        rewrite (_ : idn (RightNerve.functor G2) {| pi1 := F1 c; pi2 := e |} \o untranspose T1 {| pi1 := c; pi2 := G2 e |} = untranspose T1 _); first by [].
        rewrite (_ : transpose T1 {| pi1 := c; pi2 := G2 e |} \o untranspose T1 {| pi1 := c; pi2 := G2 e |} = (untranspose T1 >> transpose T1) _); first by [].
        by rewrite transpose_untranspose.
    Qed.

    Canonical adj : (F1 >> F2) ⊣ (G2 >> G1).
    Proof. esplit; apply: adj_mixin. Defined.
  End Defs.

End HorizontalComposition.
