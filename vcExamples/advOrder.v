Require Import Coq.Lists.List.

Require Import AttestationProtocolOrdering.attackgraph.
Require Import AttestationProtocolOrdering.adversary_ordering.
Require Import AttestationProtocolOrdering.make_adversary_ordering.

Require Import ProtocolOrderingExamples.components.

Definition advOrder_base : list (tauTaggedLabel components * tauTaggedLabel components) := 
    (blankTag _ (cor _ vc), blankTag _ (cor _ ker)) ::
    (blankTag _ (cor _ vc), blankTag _ (cor _ vcm)) ::
    (blankTag _ (cor _ vcm), blankTag _ (cor _ lkim)) ::    
    (tauTag _ (cor _ vc), tauTag _ (cor _ ker)) ::
    (tauTag _ (cor _ vc), tauTag _ (cor _ vcm)) ::
    (tauTag _ (cor _ vcm), tauTag _ (cor _ lkim)) ::
    nil.

Lemma trianglelefteq_base_antisymmetric : forall t1 t2,
    makeTrianglelefteq advOrder_base t1 t2 -> 
    makeTrianglelefteq advOrder_base t2 t1 -> 
    t1 = t2.
Proof.
    rewrite <- (makeTrianglelefteq_antisymmetric_same eqDec_components advOrder_base);
    vm_compute; auto.
Qed.




(* Add judgment corrupting virus checker under time-constraints is easier than corrupting the meta-measurer *)
Definition advOrder_vc : list (tauTaggedLabel components * tauTaggedLabel components) := 
    (tauTag _ (cor _ vc), blankTag _ (cor _ mm)) ::
    advOrder_base.

Lemma trianglelefteq_vc_antisymmetric : forall t1 t2,
    makeTrianglelefteq advOrder_vc t1 t2 -> 
    makeTrianglelefteq advOrder_vc t2 t1 -> 
    t1 = t2.
Proof.
    rewrite <- (makeTrianglelefteq_antisymmetric_same eqDec_components advOrder_vc);
    vm_compute; auto.
Qed.