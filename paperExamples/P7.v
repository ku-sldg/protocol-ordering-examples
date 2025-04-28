Require Import AttestationProtocolOrdering.attackgraph.
Require Import ProtocolOrderingExamples.components.

Definition A0 : attackgraph components := 
{|
	event := 
		nat ;
	edges :=
		(1,7) :: (7,0) :: (3,5) :: (5,2) :: (6,0) :: (4,3) :: (2,1) :: nil ;
	label := fun ev =>
		match ev with
		| 1 => inl (msp _ vcm vc)
		| 7 => inr (cor _ vc)
		| 0 => inl (msp _ vc sys)
		| 3 => inl (msp _ rtm vcm)
		| 5 => inl (msp _ rtm c)
		| 2 => inl (msp _ lkim ker)
		| 6 => inr (cor _ sys)
		| 4 => inl (msp _ rtm lkim)
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
		(1,0) :: (7,0) :: (3,5) :: (5,2) :: (4,3) :: (2,1) :: (2,7) :: (6,0) :: nil ;
	label := fun ev =>
		match ev with
		| 1 => inl (msp _ vcm vc)
		| 0 => inl (msp _ vc sys)
		| 7 => inr (cor _ ker)
		| 3 => inl (msp _ rtm vcm)
		| 5 => inl (msp _ rtm c)
		| 2 => inl (msp _ lkim ker)
		| 4 => inl (msp _ rtm lkim)
		| 6 => inr (cor _ sys)
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
		(1,0) :: (7,1) :: (3,8) :: (3,5) :: (8,1) :: (5,2) :: (6,0) :: (4,3) :: (2,1) :: nil ;
	label := fun ev =>
		match ev with
		| 1 => inl (msp _ vcm vc)
		| 0 => inl (msp _ vc sys)
		| 7 => inr (cor _ vc)
		| 3 => inl (msp _ rtm vcm)
		| 8 => inr (cor _ vcm)
		| 5 => inl (msp _ rtm c)
		| 2 => inl (msp _ lkim ker)
		| 6 => inr (cor _ sys)
		| 4 => inl (msp _ rtm lkim)
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
		(1,0) :: (7,2) :: (2,1) :: (3,5) :: (5,2) :: (4,3) :: (4,8) :: (8,2) :: (6,0) :: nil ;
	label := fun ev =>
		match ev with
		| 1 => inl (msp _ vcm vc)
		| 0 => inl (msp _ vc sys)
		| 7 => inr (cor _ ker)
		| 2 => inl (msp _ lkim ker)
		| 3 => inl (msp _ rtm vcm)
		| 5 => inl (msp _ rtm c)
		| 4 => inl (msp _ rtm lkim)
		| 8 => inr (cor _ lkim)
		| 6 => inr (cor _ sys)
		| _ => inl (ms _)
		end ;
	eqDec_event := 
		ltac:(decide equality) ;
	eqDec_component := 
		eqDec_components
|}.

Definition P7 : list (attackgraph components) := 
	A0 :: A1 :: A2 :: A3 :: nil.
