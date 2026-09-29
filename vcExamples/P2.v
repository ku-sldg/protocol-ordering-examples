Require Import AttestationProtocolOrdering.attackgraph.
Require Import ProtocolOrderingExamples.components.

Definition A0 : attackgraph components := 
{|
	event := 
		nat ;
	edges :=
		(6,0) :: (5,0) :: (4,1) :: (1,2) :: (3,4) :: (2,6) :: nil ;
	label := fun ev =>
		match ev with
		| 0 => inl (msp _ vc sys)
		| 6 => inr (cor _ vc)
		| 5 => inr (cor _ sys)
		| 4 => inl (msp _ mm vcm)
		| 1 => inl (msp _ lkim ker)
		| 2 => inl (msp _ vcm vc)
		| 3 => inl (msp _ mm lkim)
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
		(6,0) :: (4,1) :: (1,6) :: (1,2) :: (3,4) :: (2,0) :: (5,0) :: nil ;
	label := fun ev =>
		match ev with
		| 0 => inl (msp _ vc sys)
		| 6 => inr (cor _ ker)
		| 4 => inl (msp _ mm vcm)
		| 1 => inl (msp _ lkim ker)
		| 2 => inl (msp _ vcm vc)
		| 3 => inl (msp _ mm lkim)
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
		(6,2) :: (2,0) :: (5,0) :: (4,7) :: (4,1) :: (7,2) :: (1,2) :: (3,4) :: nil ;
	label := fun ev =>
		match ev with
		| 0 => inl (msp _ vc sys)
		| 6 => inr (cor _ vc)
		| 2 => inl (msp _ vcm vc)
		| 5 => inr (cor _ sys)
		| 4 => inl (msp _ mm vcm)
		| 7 => inr (cor _ vcm)
		| 1 => inl (msp _ lkim ker)
		| 3 => inl (msp _ mm lkim)
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
		(6,1) :: (1,2) :: (4,1) :: (3,4) :: (3,7) :: (7,1) :: (2,0) :: (5,0) :: nil ;
	label := fun ev =>
		match ev with
		| 0 => inl (msp _ vc sys)
		| 6 => inr (cor _ ker)
		| 1 => inl (msp _ lkim ker)
		| 2 => inl (msp _ vcm vc)
		| 4 => inl (msp _ mm vcm)
		| 3 => inl (msp _ mm lkim)
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
		(6,2) :: (2,0) :: (5,0) :: (4,1) :: (1,2) :: (7,4) :: (3,8) :: (8,4) :: nil ;
	label := fun ev =>
		match ev with
		| 0 => inl (msp _ vc sys)
		| 6 => inr (cor _ vc)
		| 2 => inl (msp _ vcm vc)
		| 5 => inr (cor _ sys)
		| 4 => inl (msp _ mm vcm)
		| 1 => inl (msp _ lkim ker)
		| 7 => inr (cor _ vcm)
		| 3 => inl (msp _ mm lkim)
		| 8 => inr (cor _ mm)
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
		(6,2) :: (2,0) :: (5,0) :: (4,1) :: (1,2) :: (7,4) :: (3,4) :: (8,3) :: nil ;
	label := fun ev =>
		match ev with
		| 0 => inl (msp _ vc sys)
		| 6 => inr (cor _ vc)
		| 2 => inl (msp _ vcm vc)
		| 5 => inr (cor _ sys)
		| 4 => inl (msp _ mm vcm)
		| 1 => inl (msp _ lkim ker)
		| 7 => inr (cor _ vcm)
		| 3 => inl (msp _ mm lkim)
		| 8 => inr (cor _ mm)
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
		(8,3) :: (3,4) :: (6,1) :: (1,2) :: (4,1) :: (2,0) :: (5,0) :: (7,3) :: nil ;
	label := fun ev =>
		match ev with
		| 0 => inl (msp _ vc sys)
		| 8 => inr (cor _ mm)
		| 3 => inl (msp _ mm lkim)
		| 4 => inl (msp _ mm vcm)
		| 6 => inr (cor _ ker)
		| 1 => inl (msp _ lkim ker)
		| 2 => inl (msp _ vcm vc)
		| 5 => inr (cor _ sys)
		| 7 => inr (cor _ lkim)
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
		(8,3) :: (3,9) :: (6,1) :: (1,2) :: (4,1) :: (9,4) :: (2,0) :: (5,0) :: (7,3) :: nil ;
	label := fun ev =>
		match ev with
		| 0 => inl (msp _ vc sys)
		| 8 => inr (cor _ mm)
		| 3 => inl (msp _ mm lkim)
		| 9 => inr (rep _ mm)
		| 6 => inr (cor _ ker)
		| 1 => inl (msp _ lkim ker)
		| 2 => inl (msp _ vcm vc)
		| 4 => inl (msp _ mm vcm)
		| 5 => inr (cor _ sys)
		| 7 => inr (cor _ lkim)
		| _ => inl (ms _)
		end ;
	eqDec_event := 
		ltac:(decide equality) ;
	eqDec_component := 
		eqDec_components
|}.

Definition P2 : list (attackgraph components) := 
	A0 :: A1 :: A2 :: A3 :: A4 :: A5 :: A6 :: A7 :: nil.
