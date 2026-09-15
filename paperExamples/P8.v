Require Import AttestationProtocolOrdering.attackgraph.
Require Import ProtocolOrderingExamples.components.

Definition A0 : attackgraph components := 
{|
	event := 
		nat ;
	edges :=
		(1,7) :: (7,0) :: (4,3) :: (3,2) :: (6,0) :: (5,4) :: (2,1) :: nil ;
	label := fun ev =>
		match ev with
		| 1 => inl (msp _ vcm vc)
		| 7 => inr (cor _ vc)
		| 0 => inl (msp _ vc sys)
		| 4 => inl (msp _ mm lkim)
		| 3 => inl (msp _ mm vcm)
		| 2 => inl (msp _ lkim ker)
		| 6 => inr (cor _ sys)
		| 5 => inl (msp _ rtm mm)
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
		(1,0) :: (4,3) :: (3,2) :: (7,0) :: (5,4) :: (2,1) :: (2,7) :: (6,0) :: nil ;
	label := fun ev =>
		match ev with
		| 1 => inl (msp _ vcm vc)
		| 0 => inl (msp _ vc sys)
		| 4 => inl (msp _ mm lkim)
		| 3 => inl (msp _ mm vcm)
		| 2 => inl (msp _ lkim ker)
		| 7 => inr (cor _ ker)
		| 5 => inl (msp _ rtm mm)
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
		(1,0) :: (4,3) :: (3,8) :: (3,2) :: (7,1) :: (6,0) :: (5,4) :: (8,1) :: (2,1) :: nil ;
	label := fun ev =>
		match ev with
		| 1 => inl (msp _ vcm vc)
		| 0 => inl (msp _ vc sys)
		| 4 => inl (msp _ mm lkim)
		| 3 => inl (msp _ mm vcm)
		| 8 => inr (cor _ vcm)
		| 2 => inl (msp _ lkim ker)
		| 7 => inr (cor _ vc)
		| 6 => inr (cor _ sys)
		| 5 => inl (msp _ rtm mm)
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
		(1,0) :: (4,3) :: (4,8) :: (3,2) :: (8,2) :: (7,2) :: (2,1) :: (5,4) :: (6,0) :: nil ;
	label := fun ev =>
		match ev with
		| 1 => inl (msp _ vcm vc)
		| 0 => inl (msp _ vc sys)
		| 4 => inl (msp _ mm lkim)
		| 3 => inl (msp _ mm vcm)
		| 8 => inr (cor _ lkim)
		| 2 => inl (msp _ lkim ker)
		| 7 => inr (cor _ ker)
		| 5 => inl (msp _ rtm mm)
		| 6 => inr (cor _ sys)
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
		(1,0) :: (4,9) :: (9,3) :: (7,1) :: (6,0) :: (5,4) :: (8,3) :: (3,2) :: (2,1) :: nil ;
	label := fun ev =>
		match ev with
		| 1 => inl (msp _ vcm vc)
		| 0 => inl (msp _ vc sys)
		| 4 => inl (msp _ mm lkim)
		| 9 => inr (cor _ mm)
		| 3 => inl (msp _ mm vcm)
		| 7 => inr (cor _ vc)
		| 6 => inr (cor _ sys)
		| 5 => inl (msp _ rtm mm)
		| 8 => inr (cor _ vcm)
		| 2 => inl (msp _ lkim ker)
		| _ => inl (ms _)
		end ;
	eqDec_event := 
		ltac:(decide equality) ;
	eqDec_component := 
		eqDec_components
|}.

Definition A5 : attackgraph components := 
{|
	event := 
		nat ;
	edges :=
		(1,0) :: (4,3) :: (3,2) :: (7,1) :: (6,0) :: (5,9) :: (9,4) :: (8,3) :: (2,1) :: nil ;
	label := fun ev =>
		match ev with
		| 1 => inl (msp _ vcm vc)
		| 0 => inl (msp _ vc sys)
		| 4 => inl (msp _ mm lkim)
		| 3 => inl (msp _ mm vcm)
		| 2 => inl (msp _ lkim ker)
		| 7 => inr (cor _ vc)
		| 6 => inr (cor _ sys)
		| 5 => inl (msp _ rtm mm)
		| 9 => inr (cor _ mm)
		| 8 => inr (cor _ vcm)
		| _ => inl (ms _)
		end ;
	eqDec_event := 
		ltac:(decide equality) ;
	eqDec_component := 
		eqDec_components
|}.

Definition A6 : attackgraph components := 
{|
	event := 
		nat ;
	edges :=
		(1,0) :: (9,4) :: (4,3) :: (3,2) :: (7,2) :: (2,1) :: (5,9) :: (6,0) :: (8,4) :: nil ;
	label := fun ev =>
		match ev with
		| 1 => inl (msp _ vcm vc)
		| 0 => inl (msp _ vc sys)
		| 9 => inr (cor _ mm)
		| 4 => inl (msp _ mm lkim)
		| 3 => inl (msp _ mm vcm)
		| 2 => inl (msp _ lkim ker)
		| 7 => inr (cor _ ker)
		| 5 => inl (msp _ rtm mm)
		| 6 => inr (cor _ sys)
		| 8 => inr (cor _ lkim)
		| _ => inl (ms _)
		end ;
	eqDec_event := 
		ltac:(decide equality) ;
	eqDec_component := 
		eqDec_components
|}.

Definition A7 : attackgraph components := 
{|
	event := 
		nat ;
	edges :=
		(1,0) :: (9,4) :: (4,10) :: (10,3) :: (7,2) :: (2,1) :: (5,9) :: (3,2) :: (6,0) :: (8,4) :: nil ;
	label := fun ev =>
		match ev with
		| 1 => inl (msp _ vcm vc)
		| 0 => inl (msp _ vc sys)
		| 9 => inr (cor _ mm)
		| 4 => inl (msp _ mm lkim)
		| 10 => inr (rep _ mm)
		| 3 => inl (msp _ mm vcm)
		| 7 => inr (cor _ ker)
		| 2 => inl (msp _ lkim ker)
		| 5 => inl (msp _ rtm mm)
		| 6 => inr (cor _ sys)
		| 8 => inr (cor _ lkim)
		| _ => inl (ms _)
		end ;
	eqDec_event := 
		ltac:(decide equality) ;
	eqDec_component := 
		eqDec_components
|}.

Definition P8 : list (attackgraph components) := 
	A0 :: A1 :: A2 :: A3 :: A4 :: A5 :: A6 :: A7 :: nil.
