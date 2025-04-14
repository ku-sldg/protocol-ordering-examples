Require Import AttestationProtocolOrdering.attackgraph.
Require Import ProtocolOrderingExamples.components.

Definition A0 : attackgraph components := 
{|
	event := 
		nat ;
	edges :=
		(6,0) :: (5,0) :: (4,1) :: (4,2) :: (1,6) :: (2,0) :: (3,1) :: (3,2) :: nil ;
	label := fun ev =>
		match ev with
		| 6 => inr (cor _ vc)
		| 0 => inl (msp _ vc sys)
		| 5 => inr (cor _ sys)
		| 4 => inl (msp _ rtm a2)
		| 1 => inl (msp _ a1 vc)
		| 2 => inl (msp _ a2 ker)
		| 3 => inl (msp _ rtm a1)
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
		(6,0) :: (4,1) :: (4,2) :: (2,6) :: (3,1) :: (3,2) :: (5,0) :: nil ;
	label := fun ev =>
		match ev with
		| 6 => inr (cor _ ker)
		| 0 => inl (msp _ vc sys)
		| 4 => inl (msp _ rtm a2)
		| 1 => inl (msp _ a1 vc)
		| 2 => inl (msp _ a2 ker)
		| 3 => inl (msp _ rtm a1)
		| 5 => inr (cor _ sys)
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
		(6,1) :: (6,0) :: (5,0) :: (4,1) :: (4,2) :: (2,0) :: (7,1) :: (3,2) :: (3,7) :: nil ;
	label := fun ev =>
		match ev with
		| 6 => inr (cor _ vc)
		| 1 => inl (msp _ a1 vc)
		| 0 => inl (msp _ vc sys)
		| 5 => inr (cor _ sys)
		| 4 => inl (msp _ rtm a2)
		| 2 => inl (msp _ a2 ker)
		| 7 => inr (cor _ a1)
		| 3 => inl (msp _ rtm a1)
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
		(6,2) :: (2,0) :: (4,1) :: (4,7) :: (7,2) :: (3,2) :: (3,1) :: (5,0) :: nil ;
	label := fun ev =>
		match ev with
		| 6 => inr (cor _ ker)
		| 2 => inl (msp _ a2 ker)
		| 0 => inl (msp _ vc sys)
		| 4 => inl (msp _ rtm a2)
		| 1 => inl (msp _ a1 vc)
		| 7 => inr (cor _ a2)
		| 3 => inl (msp _ rtm a1)
		| 5 => inr (cor _ sys)
		| _ => inl (ms _)
		end ;
	eqDec_event := 
		ltac:(decide equality) ;
	eqDec_component := 
		eqDec_components
|}.

Definition A4 : attackgraph components := 
{|
	event := 
		nat ;
	edges :=
		(6,0) :: (0,7) :: (5,0) :: (4,2) :: (2,0) :: (3,2) :: (7,1) :: nil ;
	label := fun ev =>
		match ev with
		| 6 => inr (cor _ vc)
		| 0 => inl (msp _ vc sys)
		| 7 => inr (rep _ vc)
		| 5 => inr (cor _ sys)
		| 4 => inl (msp _ rtm a2)
		| 2 => inl (msp _ a2 ker)
		| 1 => inl (msp _ a1 vc)
		| 3 => inl (msp _ rtm a1)
		| _ => inl (ms _)
		end ;
	eqDec_event := 
		ltac:(decide equality) ;
	eqDec_component := 
		eqDec_components
|}.

Definition S2 : list (attackgraph components) := 
	A0 :: A1 :: A2 :: A3 :: A4 :: nil.
