Require Import AttestationProtocolOrdering.set_relationship.

Require Import ProtocolOrderingExamples.components.
Require Import ProtocolOrderingExamples.advOrder.

Require Import ProtocolOrderingExamples.P2.
Require Import ProtocolOrderingExamples.P3.


Lemma P2_P3_base : myOrder_base_fix P2 P3 = leq.
Proof. auto. Qed.

Lemma P2_P3_vc : myOrder_vc_fix P2 P3 = equiv.
Proof. auto. Qed.
