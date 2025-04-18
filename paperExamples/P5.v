Require Import AttestationProtocolOrdering.attackgraph.
Require Import ProtocolOrderingExamples.components.

Definition A0 : attackgraph components := 
{|
	event := 
		nat ;
	edges :=
		(6,0) :: (5,0) :: (3,2) :: (3,1) :: (2,0) :: (1,6) :: (4,2) :: (4,1) :: nil ;
	label := fun ev =>
		match ev with
		| 6 => inr (cor _ vc)
		| 0 => inl (msp _ vc sys)
		| 5 => inr (cor _ sys)
		| 3 => inl (msp _ rtm abc)
		| 2 => inl (msp _ lkim ker)
		| 1 => inl (msp _ abc vc)
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
		(6,0) :: (3,2) :: (3,1) :: (2,6) :: (4,2) :: (4,1) :: (5,0) :: nil ;
	label := fun ev =>
		match ev with
		| 6 => inr (cor _ ker)
		| 0 => inl (msp _ vc sys)
		| 3 => inl (msp _ rtm abc)
		| 2 => inl (msp _ lkim ker)
		| 1 => inl (msp _ abc vc)
		| 4 => inl (msp _ rtm lkim)
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
		(6,0) :: (6,1) :: (5,0) :: (3,7) :: (3,2) :: (7,1) :: (2,0) :: (4,1) :: (4,2) :: nil ;
	label := fun ev =>
		match ev with
		| 6 => inr (cor _ vc)
		| 0 => inl (msp _ vc sys)
		| 1 => inl (msp _ abc vc)
		| 5 => inr (cor _ sys)
		| 3 => inl (msp _ rtm abc)
		| 7 => inr (cor _ abc)
		| 2 => inl (msp _ lkim ker)
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
		(6,2) :: (2,0) :: (3,2) :: (3,1) :: (4,1) :: (4,7) :: (7,2) :: (5,0) :: nil ;
	label := fun ev =>
		match ev with
		| 6 => inr (cor _ ker)
		| 2 => inl (msp _ lkim ker)
		| 0 => inl (msp _ vc sys)
		| 3 => inl (msp _ rtm abc)
		| 1 => inl (msp _ abc vc)
		| 4 => inl (msp _ rtm lkim)
		| 7 => inr (cor _ lkim)
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
		(6,0) :: (0,7) :: (5,0) :: (3,2) :: (2,0) :: (4,2) :: (7,1) :: nil ;
	label := fun ev =>
		match ev with
		| 6 => inr (cor _ vc)
		| 0 => inl (msp _ vc sys)
		| 7 => inr (rep _ vc)
		| 5 => inr (cor _ sys)
		| 3 => inl (msp _ rtm abc)
		| 2 => inl (msp _ lkim ker)
		| 4 => inl (msp _ rtm lkim)
		| 1 => inl (msp _ abc vc)
		| _ => inl (ms _)
		end ;
	eqDec_event := 
		ltac:(decide equality) ;
	eqDec_component := 
		eqDec_components
|}.

Definition P5 : list (attackgraph components) := 
	A0 :: A1 :: A2 :: A3 :: A4 :: nil.
