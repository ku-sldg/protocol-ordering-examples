Require Import AttestationProtocolOrdering.set_relationship.

Require Import ProtocolOrderingExamples.components.
Require Import ProtocolOrderingExamples.advOrder.

Require Import ProtocolOrderingExamples.P1.
Require Import ProtocolOrderingExamples.P2.
Require Import ProtocolOrderingExamples.P3.
Require Import ProtocolOrderingExamples.P4.
Require Import ProtocolOrderingExamples.P5.


Lemma P1_P2_base : myOrder_base_fix P1 P2 = equiv.
Proof. auto. Qed.
Lemma P1_P2_stm : myOrder_stm_fix P1 P2 = equiv.
Proof. auto. Qed.


Lemma P1_P3_base : myOrder_base_fix P1 P3 = leq.
Proof. auto. Qed.
Lemma P1_P3_stm : myOrder_stm_fix P1 P3 = leq.
Proof. auto. Qed.

Lemma P2_P3_base : myOrder_base_fix P2 P3 = leq.
Proof. auto. Qed.
Lemma P2_P3_stm : myOrder_stm_fix P2 P3 = leq.
Proof. auto. Qed.


Lemma P1_P4_base : myOrder_base_fix P1 P4 = leq.
Proof. auto. Qed.
Lemma P1_P4_stm : myOrder_stm_fix P1 P4 = leq.
Proof. auto. Qed.

Lemma P2_P4_base : myOrder_base_fix P2 P4 = leq.
Proof. auto. Qed.
Lemma P2_P4_stm : myOrder_stm_fix P2 P4 = leq.
Proof. auto. Qed.

Lemma P3_P4_base : myOrder_base_fix P3 P4 = equiv.
Proof. auto. Qed.
Lemma P3_P4_stm : myOrder_stm_fix P3 P4 = equiv.
Proof. auto. Qed.

Lemma P1_P5_base : myOrder_base_fix P1 P5 = incomparable.
Proof. auto. Qed.

Lemma P1_P5_stm : myOrder_stm_fix P3 P5 = leq.
Proof. auto. Qed.


Lemma P2_P5_base : myOrder_base_fix P2 P5 = incomparable.
Proof. auto. Qed.

Lemma P2_P5_stm : myOrder_stm_fix P2 P5 = leq.
Proof. auto. Qed.


Lemma P3_P5_base : myOrder_base_fix P3 P5 = incomparable.
Proof. auto. Qed.

Lemma P3_P5_stm : myOrder_stm_fix P3 P5 = leq.
Proof. auto. Qed.


Lemma P4_P5_base : myOrder_base_fix P4 P5 = incomparable.
Proof. auto. Qed.

Lemma P4_P5_stm : myOrder_stm_fix P4 P5 = leq.
Proof. auto. Qed.




