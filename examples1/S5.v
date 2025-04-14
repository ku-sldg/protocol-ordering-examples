Require Import AttestationProtocolOrdering.attackgraph.
Require Import ProtocolOrderingExamples.components.

Definition A0 : attackgraph components := 
{|
	event := 
		nat ;
	edges :=
		(2,0) :: (7,0) :: (4,2) :: (4,1) :: (1,7) :: (6,0) :: (3,2) :: (3,1) :: (5,2) :: (5,1) :: nil ;
	label := fun ev =>
		match ev with
		| 2 => inl (msp _ a2 ker)
		| 0 => inl (msp _ vc sys)
		| 7 => inr (cor _ vc)
		| 4 => inl (msp _ rtm a2)
		| 1 => inl (msp _ a1 vc)
		| 6 => inr (cor _ sys)
		| 3 => inl (msp _ rtm a1)
		| 5 => inl (msp _ rtm vm)
		| _ => inl (ms _)
		end ;
	eqDec_event := 
		ltac:(decide equality) ;
	eqDec_component := 
		eqDec_components
|}.

Definition A1 : attackgraph components := 
{|
	event := 
		nat ;
	edges :=
		(2,7) :: (7,0) :: (4,2) :: (4,1) :: (1,0) :: (3,2) :: (3,1) :: (6,0) :: (5,2) :: (5,1) :: nil ;
	label := fun ev =>
		match ev with
		| 2 => inl (msp _ a2 ker)
		| 7 => inr (cor _ ker)
		| 0 => inl (msp _ vc sys)
		| 4 => inl (msp _ rtm a2)
		| 1 => inl (msp _ a1 vc)
		| 3 => inl (msp _ rtm a1)
		| 6 => inr (cor _ sys)
		| 5 => inl (msp _ rtm vm)
		| _ => inl (ms _)
		end ;
	eqDec_event := 
		ltac:(decide equality) ;
	eqDec_component := 
		eqDec_components
|}.

Definition A2 : attackgraph components := 
{|
	event := 
		nat ;
	edges :=
		(2,0) :: (7,1) :: (1,0) :: (4,2) :: (4,1) :: (6,0) :: (3,2) :: (3,8) :: (8,1) :: (5,2) :: (5,1) :: nil ;
	label := fun ev =>
		match ev with
		| 2 => inl (msp _ a2 ker)
		| 0 => inl (msp _ vc sys)
		| 7 => inr (cor _ vc)
		| 1 => inl (msp _ a1 vc)
		| 4 => inl (msp _ rtm a2)
		| 6 => inr (cor _ sys)
		| 3 => inl (msp _ rtm a1)
		| 8 => inr (cor _ a1)
		| 5 => inl (msp _ rtm vm)
		| _ => inl (ms _)
		end ;
	eqDec_event := 
		ltac:(decide equality) ;
	eqDec_component := 
		eqDec_components
|}.

Definition A3 : attackgraph components := 
{|
	event := 
		nat ;
	edges :=
		(2,0) :: (7,2) :: (4,1) :: (4,8) :: (1,0) :: (8,2) :: (3,2) :: (3,1) :: (6,0) :: (5,2) :: (5,1) :: nil ;
	label := fun ev =>
		match ev with
		| 2 => inl (msp _ a2 ker)
		| 0 => inl (msp _ vc sys)
		| 7 => inr (cor _ ker)
		| 4 => inl (msp _ rtm a2)
		| 1 => inl (msp _ a1 vc)
		| 8 => inr (cor _ a2)
		| 3 => inl (msp _ rtm a1)
		| 6 => inr (cor _ sys)
		| 5 => inl (msp _ rtm vm)
		| _ => inl (ms _)
		end ;
	eqDec_event := 
		ltac:(decide equality) ;
	eqDec_component := 
		eqDec_components
|}.

Definition S5 : list (attackgraph components) := 
	A0 :: A1 :: A2 :: A3 :: nil.
