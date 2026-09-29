Require Import Coq.Lists.List.
Require Import Lia.

Require Import AttestationProtocolOrdering.attackgraph.
Require Import AttestationProtocolOrdering.adversary_ordering.
Require Import AttestationProtocolOrdering.set_relationship.

Require Import ProtocolOrderingExamples.components.
Require Import ProtocolOrderingExamples.trianglelefteq.

Definition advOrder : list (tauTaggedLabel components * tauTaggedLabel components) := 
    (blankTag _ (cor _ nwk), blankTag _ (cor _ swk)) ::
    (blankTag _ (cor _ rtlib), blankTag _ (cor _ appm)) ::
    (tauTag _ (cor _ nwk), tauTag _ (cor _ swk)) ::
    (tauTag _ (cor _ rtlib), tauTag _ (cor _ appm)) ::
    nil.

Definition level (comp : components) : nat :=
    match comp with
    | nwk => 0
    | app => 0
    | rtlib => 1
    | pxy => 2
    | swk => 3
    | appm => 4
    | rtm => 5
    end.

Definition levelAdv (a : advLabel components) : nat :=
    match a with
    | cor _ comp => level comp
    | rep _ comp => level comp
    end.

Definition rank (t : tauTaggedLabel components) : nat :=
    match t with
    | blankTag _ a => 2 * levelAdv a
    | tauTag _ a => 2 * levelAdv a + 1
    end.

Lemma trianglelefteq_charac : forall t1 t2,
    @trianglelefteq _ advOrder t1 t2 -> 
    t1 = t2 \/ rank t1 < rank t2.
Proof.
    intros t1 t2 H; induction H; auto.
    - simpl; lia.
    - right. simpl in H; repeat destruct H as [H|H];
      inversion H; subst;
      simpl; lia.
    - destruct IHtrianglelefteq1 as [|IH1], IHtrianglelefteq2 as [|IH2]; subst; auto.
      simpl; lia.
Qed.

Lemma trianglelefteq_antisymmetric : forall t1 t2,
    @trianglelefteq _ advOrder t1 t2 -> 
    @trianglelefteq _ advOrder t2 t1 -> 
    t1 = t2.
Proof.
    intros t1 t2 H12 H21.
    apply trianglelefteq_charac in H12; apply trianglelefteq_charac in H21.
    destruct H12; auto. destruct H21; auto.
    lia.
Qed.

Definition myOrder_fix := @order_fix components (@trianglelefteq _ advOrder) (@trianglelefteqDec _ eqDec_components advOrder).
