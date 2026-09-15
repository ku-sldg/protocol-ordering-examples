Require Import Coq.Lists.List.

Require Import AttestationProtocolOrdering.attackgraph.
Require Import AttestationProtocolOrdering.adversary_ordering.
Require Import AttestationProtocolOrdering.set_relationship.

Require Import ProtocolOrderingExamples.components.
Require Import ProtocolOrderingExamples.trianglelefteq.

Definition advOrder : list (tauTaggedLabel components * tauTaggedLabel components) := nil.



Lemma trianglelefteq_charac : forall t1 t2,
    @trianglelefteq _ advOrder t1 t2 <->
    t1 = t2 \/ (exists l, t1 = blankTag _ l /\ t2 = tauTag _ l).
Proof.
    intros t1 t2; split; intro H.
    - induction H; eauto.
    -- inversion H.
    -- destruct IHtrianglelefteq1 as [|[l1 []]], IHtrianglelefteq2 as [|[l2 []]]; subst; eauto.
       inversion H3.
    - destruct H as [|[l []]]; subst; constructor.
Qed.

Lemma trianglelefteq_antisymmetric : forall t1 t2,
    @trianglelefteq _ advOrder t1 t2 -> 
    @trianglelefteq _ advOrder t2 t1 -> 
    t1 = t2.
Proof.
    intros t1 t2 H12 H21; apply trianglelefteq_charac in H12, H21.
    destruct H12 as [|[l1 []]]; auto.
    destruct H21 as [|[l2 []]]; auto.
    subst. inversion H2.
Qed.

Lemma eqDec_advLabel : forall (l1 l2 : advLabel components),
    {l1 = l2} + {l1 <> l2}.
Proof.
    repeat decide equality.
Defined.

Lemma eqDec_ttl : forall (t1 t2 : tauTaggedLabel components),
    {t1 = t2} + {t1 <> t2}.
Proof.
    repeat decide equality.
Defined.

Lemma trianglelefteqDec : forall t1 t2,
  {@trianglelefteq _ advOrder t1 t2} + {~ @trianglelefteq _ advOrder t1 t2}.
Proof.
    intros t1 t2. destruct (eqDec_ttl t1 t2) as [|HNeq]; subst; [left; constructor|].
    destruct t1 as [l1|l1], t2 as [l2|l2].
    - right. intros H; apply trianglelefteq_charac in H;
      destruct H as [H|[a [H1 H2]]]; [contradiction|]. 
      inversion H1.
    - right. intros H; apply trianglelefteq_charac in H;
      destruct H as [H|[a [H1 H2]]]; [contradiction|]. 
      inversion H1.
    - destruct (eqDec_advLabel l1 l2) as [|HNeq']; subst; [left; constructor|].
      right. intros H; apply trianglelefteq_charac in H;
      destruct H as [H|[a [H1 H2]]]; [contradiction|]. 
      inversion H1; inversion H2; subst; contradiction.
    - right. intros H; apply trianglelefteq_charac in H;
      destruct H as [H|[a [H1 H2]]]; [contradiction|]. 
      inversion H2.
Defined.



Definition myOrder_fix := @order_fix components (@trianglelefteq _ advOrder) trianglelefteqDec.