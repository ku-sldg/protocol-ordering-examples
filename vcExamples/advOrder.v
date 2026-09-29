Require Import Coq.Lists.List.
Require Import Lia.

Require Import AttestationProtocolOrdering.attackgraph.
Require Import AttestationProtocolOrdering.adversary_ordering.
Require Import AttestationProtocolOrdering.set_relationship.

Require Import ProtocolOrderingExamples.components.
Require Import ProtocolOrderingExamples.trianglelefteq.

Definition advOrder_base : list (tauTaggedLabel components * tauTaggedLabel components) := 
    (blankTag _ (cor _ vc), blankTag _ (cor _ ker)) ::
    (blankTag _ (cor _ vc), blankTag _ (cor _ vcm)) ::
    (blankTag _ (cor _ vcm), blankTag _ (cor _ lkim)) ::    
    (tauTag _ (cor _ vc), tauTag _ (cor _ ker)) ::
    (tauTag _ (cor _ vc), tauTag _ (cor _ vcm)) ::
    (tauTag _ (cor _ vcm), tauTag _ (cor _ lkim)) ::
    nil.

Definition level_base (comp : components) : nat :=
    match comp with
    | vc => 0
    | ker => 1
    | vcm => 1
    | lkim => 2
    | _ => 0
    end.

Definition levelAdv_base (a : advLabel components) : nat :=
    match a with
    | cor _ comp => level_base comp
    | rep _ comp => level_base comp
    end.

Definition rank_base (t : tauTaggedLabel components) : nat :=
    match t with
    | blankTag _ a => 2 * levelAdv_base a
    | tauTag _ a => 2 * levelAdv_base a + 1
    end.

Lemma trianglelefteq_base_charac : forall t1 t2,
    @trianglelefteq _ advOrder_base t1 t2 -> 
    t1 = t2 \/ rank_base t1 < rank_base t2.
Proof.
    intros t1 t2 H; induction H; auto.
    - simpl; lia.
    - right. simpl in H; destruct H as [H|[H|[H|[H|[H|[H|[]]]]]]]; 
      inversion H; subst;
      simpl; lia.
    - destruct IHtrianglelefteq1 as [|IH1], IHtrianglelefteq2 as [|IH2]; subst; auto.
      simpl; lia.
Qed.

Lemma trianglelefteq_base_antisymmetric : forall t1 t2,
    @trianglelefteq _ advOrder_base t1 t2 -> 
    @trianglelefteq _ advOrder_base t2 t1 -> 
    t1 = t2.
Proof.
    intros t1 t2 H12 H21.
    apply trianglelefteq_base_charac in H12; apply trianglelefteq_base_charac in H21.
    destruct H12; auto. destruct H21; auto.
    lia.
Qed.

Definition myOrder_base_fix := @order_fix components (@trianglelefteq _ advOrder_base) (@trianglelefteqDec _ eqDec_components advOrder_base).




(* Add judgment corrupting virus checker under time-constraints is easier than corrupting the meta-measurer *)
Definition advOrder_vc : list (tauTaggedLabel components * tauTaggedLabel components) := 
    (tauTag _ (cor _ vc), blankTag _ (cor _ mm)) ::
    advOrder_base.


Definition level_vc (comp : components) : nat :=
    match comp with
    | vc => 0
    | ker => 1
    | vcm => 1
    | lkim => 2
    | mm => 4
    | _ => 0
    end.

Definition levelAdv_vc (a : advLabel components) : nat :=
    match a with
    | cor _ comp => level_vc comp
    | rep _ comp => level_vc comp
    end.

Definition rank_vc (t : tauTaggedLabel components) : nat :=
    match t with
    | blankTag _ a => 2 * levelAdv_vc a
    | tauTag _ a => 2 * levelAdv_vc a + 1
    end.

Lemma trianglelefteq_vc_charac : forall t1 t2,
    @trianglelefteq _ advOrder_vc t1 t2 -> 
    t1 = t2 \/ rank_vc t1 < rank_vc t2.
Proof.
    intros t1 t2 H; induction H; auto.
    - simpl; lia.
    - right. simpl in H; destruct H as [H|[H|[H|[H|[H|[H|[H|[]]]]]]]];
      try (inversion H; subst;
      simpl; lia).
    - destruct IHtrianglelefteq1 as [|IH1], IHtrianglelefteq2 as [|IH2]; subst; auto.
      simpl; lia.
Qed.

Lemma trianglelefteq_vc_antisymmetric : forall t1 t2,
    @trianglelefteq _ advOrder_vc t1 t2 -> 
    @trianglelefteq _ advOrder_vc t2 t1 -> 
    t1 = t2.
Proof.
    intros t1 t2 H12 H21.
    apply trianglelefteq_vc_charac in H12; apply trianglelefteq_vc_charac in H21.
    destruct H12; auto. destruct H21; auto.
    lia.
Qed.

Definition myOrder_vc_fix := @order_fix components (@trianglelefteq _ advOrder_vc) (@trianglelefteqDec _ eqDec_components advOrder_vc).