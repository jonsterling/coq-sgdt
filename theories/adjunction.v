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


    Definition transp_fwd_fam U : LeftNerve.functor (F1 >> F2) U ~> RightNerve.functor (G2 >> G1) U.
    Proof.
      case: U=> c e //= f.
      apply: (transpose T1 (c, G2 e)).
      apply: (transpose T2 (F1 c, e)).
      apply: f.
    Defined.

    Definition transp_bwd_fam U : RightNerve.functor (G2 >> G1) U ~> LeftNerve.functor (F1 >> F2) U.
    Proof.
      case: U => c e //= f.
      apply: (untranspose T2 (F1 c, e)).
      apply: (untranspose T1 (c, G2 e)).
      apply: f.
    Defined.

    Definition transp_fwd_mixin : NatTrans.mixin_of _ _ transp_fwd_fam.
    Proof.
      build; case=> c1 e1; case=> c2 e2; case=> f1 f2.
      apply: funE=> x.
      have Q1 := unfunE _ _ (naturality (transpose T1) (c1, G2 e1) (c2, G2 e2) (f1, G2 @@ f2)).
      have Q2 := unfunE _ _ (naturality (transpose T2) (F1 c1, e1) (F1 c2, e2) (F1 @@ f1, f2)).
      cbn in Q2, Q1.
      by cbn; rewrite /transp_fwd_fam Q2 Q1.
    Qed.

    Definition transp_bwd_mixin : NatTrans.mixin_of _ _ transp_bwd_fam.
    Proof.
      build; case=> c1 e1; case=> c2 e2; case=> f1 f2.
      apply: funE=> x.
      have Q2 := unfunE _ _ (naturality (untranspose T2) (F1 c1, e1) (F1 c2, e2) (F1 @@ f1, f2)).
      have Q1 := unfunE _ _ (naturality (untranspose T1) (c1, G2 e1) (c2, G2 e2) (f1, G2 @@ f2)).
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
        rewrite (_ : (idn (LeftNerve.functor F1) (c, G2 e) \o transpose T2 (F1 c, e)) = transpose T2 _); first by [].
        rewrite (_ : untranspose T2 _ \o transpose T2 (F1 c, e) = (transpose T2 >> untranspose T2) _); first by [].
        by rewrite untranspose_transpose.

      - apply: NatTrans.ext.
        apply: dfunE; case=> c e; cbn.
        rewrite /transp_fwd_fam /transp_bwd_fam.
        rewrite [fun f => untranspose T2 _ _]eta_cmp.
        rewrite [fun f => transpose T1 _ _]eta_cmp.
        rewrite -cmp_assoc.
        rewrite [transpose T2 _ \o _]cmp_assoc.
        rewrite (_ : transpose T2 (F1 c, e) \o untranspose T2 (F1 c, e) = (untranspose T2 >> transpose T2) _); first by [].
        rewrite transpose_untranspose.
        rewrite (_ : idn (RightNerve.functor G2) (F1 c, e) \o untranspose T1 (c, G2 e) = untranspose T1 _); first by [].
        rewrite (_ : transpose T1 (c, G2 e) \o untranspose T1 (c, G2 e) = (untranspose T1 >> transpose T1) _); first by [].
        by rewrite transpose_untranspose.
    Qed.

    Canonical adj : (F1 >> F2) ⊣ (G2 >> G1).
    Proof. esplit; apply: adj_mixin. Defined.
  End Defs.

End HorizontalComposition.

Module PointwiseLifting.
  Section Defs.
    Context (ℐ : Category.type) {𝒞 𝒟 : Category.type} (F : 𝒞 ~~> 𝒟).

    Definition ob : Cat[ℐ,𝒞] -> Cat[ℐ,𝒟].
    Proof.
      move=> A.
      by exact: ((A : ℐ ~> 𝒞) >> F).
    Defined.

    Definition prefunctor_mixin : Prefunctor.mixin_of _ _ ob.
    Proof.
      build=> A B f.
      build.
      - move=> i.
        by exact: (F @@ f _).
      - build=> i j ij.
        abstract by cbn; rewrite -?fseq naturality.
    Defined.

    Canonical prefunctor : Prefunctor.type Cat[ℐ,𝒞] Cat[ℐ,𝒟].
    Proof. by esplit; apply: prefunctor_mixin. Defined.

    Definition functor_mixin : Functor.mixin_of _ _ prefunctor.
    Proof.
      build.
      - move=> A.
        apply: NatTrans.ext.
        apply: dfunE=> i //=.
        by rewrite fidn.
      - move=> A B C f g.
        apply: NatTrans.ext.
        apply: dfunE=> i //=.
        by rewrite fseq.
    Qed.

    Canonical functor : Cat[ℐ,𝒞] ~~> Cat[ℐ,𝒟].
    Proof. by esplit; apply: functor_mixin. Defined.
  End Defs.
End PointwiseLifting.

Module PointwiseLiftingAdjunction.
  Section Defs.
    Context (ℐ : Category.type) {𝒞 𝒟 : Category.type} (F : 𝒞 ~~> 𝒟) (U : _) (T : F ⊣ U).
    Local Notation F' := (PointwiseLifting.functor ℐ F).
    Local Notation U' := (PointwiseLifting.functor ℐ U).

    Definition transp_fwd_fam_fam : forall P, LeftNerve.functor F' P ->  forall i : ℐ, pi1 P i ~> U' (pi2 P) i.
    Proof.
      case=> A X f i.
      rewrite /U'; cbn.
      apply: (transpose T (A i, X i)).
      by apply: f.
    Defined.

    Lemma transp_fwd_fam_mixin : forall P f, NatTrans.mixin_of _ _ (transp_fwd_fam_fam P f).
    Proof.
      case=> A X.
      build=> i j ij.
      rewrite /PointwiseLifting.ob.
      have Qi := unfunE _ _ (naturality (transpose T) (A i, X i) (A i, X j) (idn _, X @@ ij)) (f i).
      have Qj := unfunE _ _ (naturality (transpose T) (A j, X j) (A i, X j) (A @@ ij, idn _)) (f j).
      rewrite /LeftNerve.ob /LeftNerve.functor /LeftNerve.prefunctor //= in Qi Qj.
      cbn in Qi, Qj.
      rewrite ?fidn ?seqL ?seqR in Qi Qj.
      by rewrite -Qi -Qj (naturality f).
    Qed.

    Canonical transp_fwd_fam : forall x, LeftNerve.functor F' x ~> RightNerve.functor U' x.
    Proof. by esplit; apply: transp_fwd_fam_mixin. Defined.

    Lemma transp_fwd_mixin : NatTrans.mixin_of _ _ transp_fwd_fam.
    Proof.
      build; case=> A1 X1; case=> A2 X2; case=> f g.
      apply: dfunE=> h.
      apply: NatTrans.ext.
      rewrite /transp_fwd_fam /transp_fwd_fam_fam //=.
      apply: dfunE=> i.
      have Q := unfunE _ _ (naturality (transpose T) (A1 i, X1 i) (A2 i, X2 i) (f i, g i)) (h i).
      cbn in Q.
      by rewrite Q.
    Qed.

    Canonical transp_fwd : LeftNerve.functor F' ~> RightNerve.functor U'.
    Proof. by esplit; apply: transp_fwd_mixin. Defined.

    Definition transp_bwd_fam_fam : forall P, RightNerve.functor U' P ->  forall i : ℐ, F' (pi1 P) i ~> (pi2 P) i.
    Proof.
      case=> A X f i.
      rewrite /F'; cbn.
      apply: (untranspose T (A i, X i)).
      by apply: f.
    Defined.

    Lemma transp_bwd_fam_mixin : forall P f, NatTrans.mixin_of _ _ (transp_bwd_fam_fam P f).
    Proof.
      case=> A X.
      build=> i j ij.
      rewrite /PointwiseLifting.ob.
      have Qi := unfunE _ _ (naturality (untranspose T) (A i, X i) (A i, X j) (idn _, X @@ ij)) (f i).
      have Qj := unfunE _ _ (naturality (untranspose T) (A j, X j) (A i, X j) (A @@ ij, idn _)) (f j).
      rewrite /RightNerve.ob /RightNerve.functor /RightNerve.prefunctor //= in Qi Qj.
      cbn in Qi, Qj.
      rewrite ?fidn ?seqL ?seqR in Qi, Qj.
      by rewrite -Qi -Qj (naturality f).
    Qed.

    Canonical transp_bwd_fam : forall x, RightNerve.functor U' x ~> LeftNerve.functor F' x.
    Proof. by esplit; apply: transp_bwd_fam_mixin. Defined.

    Lemma transp_bwd_mixin : NatTrans.mixin_of _ _ transp_bwd_fam.
    Proof.
      build; case=> A1 X1; case=> A2 X2; case=> f g.
      apply: dfunE=> h.
      apply: NatTrans.ext.
      rewrite /transp_bwd_fam /transp_bwd_fam_fam //=.
      apply: dfunE=> i.
      have Q := unfunE _ _ (naturality (untranspose T) (A1 i, X1 i) (A2 i, X2 i) (f i, g i)) (h i).
      cbn in Q.
      by rewrite Q.
    Qed.

    Canonical transp_bwd : RightNerve.functor U' ~> LeftNerve.functor F'.
    Proof. by esplit; apply: transp_bwd_mixin. Defined.

    Definition preadj : Preadjunction.type F' U'.
    Proof.
      build.
      - apply: transp_fwd.
      - apply: transp_bwd.
    Defined.

    Definition adj_mixin : Adjunction.mixin_of F' U' preadj.
    Proof.
      build; apply: NatTrans.ext; apply: dfunE; case=> A X;
      apply: funE=> f; apply: NatTrans.ext; apply: dfunE=> i;
      rewrite /transp_fwd /transp_bwd /transp_fwd_fam /transp_bwd_fam /transp_fwd_fam_fam /transp_bwd_fam_fam //=.
      - suff: ((transpose T >> untranspose T) (A i, X i) (f i) = f i); first by [].
        by rewrite untranspose_transpose.
      - suff: ((untranspose T >> transpose T) (A i, X i) (f i) = f i); first by [].
        by rewrite transpose_untranspose.
    Qed.

    Canonical adj : F' ⊣ U'.
    Proof. by esplit; apply: adj_mixin. Defined.
  End Defs.
End PointwiseLiftingAdjunction.