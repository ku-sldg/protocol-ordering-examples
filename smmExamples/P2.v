Require Import AttestationProtocolOrdering.attackgraph.
Require Import ProtocolOrderingExamples.components.

Definition A0 : attackgraph components := 
{|
	event := 
		nat ;
	edges :=
		(4,0) :: (2,1) :: (1,0) :: (5,0) :: (3,2) :: nil ;
	label := fun ev =>
		match ev with
		| 4 => inr (cor _ app)
		| 0 => inl (msp _ ker app)
		| 2 => inl (msp _ bios boot)
		| 1 => inl (msp _ boot ker)
		| 5 => inr (cor _ smm)
		| 3 => inl (msp _ crtm bios)
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
		(5,0) :: (2,1) :: (1,5) :: (3,2) :: (4,0) :: nil ;
	label := fun ev =>
		match ev with
		| 5 => inr (cor _ ker)
		| 0 => inl (msp _ ker app)
		| 2 => inl (msp _ bios boot)
		| 1 => inl (msp _ boot ker)
		| 3 => inl (msp _ crtm bios)
		| 4 => inr (cor _ app)
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
		(5,1) :: (1,0) :: (2,6) :: (6,1) :: (3,2) :: (4,0) :: nil ;
	label := fun ev =>
		match ev with
		| 5 => inr (cor _ ker)
		| 1 => inl (msp _ boot ker)
		| 0 => inl (msp _ ker app)
		| 2 => inl (msp _ bios boot)
		| 6 => inr (cor _ boot)
		| 3 => inl (msp _ crtm bios)
		| 4 => inr (cor _ app)
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
		(5,1) :: (1,0) :: (2,1) :: (3,7) :: (7,2) :: (6,2) :: (4,0) :: nil ;
	label := fun ev =>
		match ev with
		| 5 => inr (cor _ ker)
		| 1 => inl (msp _ boot ker)
		| 0 => inl (msp _ ker app)
		| 2 => inl (msp _ bios boot)
		| 3 => inl (msp _ crtm bios)
		| 7 => inr (cor _ bios)
		| 6 => inr (cor _ boot)
		| 4 => inr (cor _ app)
		| _ => inl (ms _)
		end ;
	eqDec_event := 
		ltac:(decide equality) ;
	eqDec_component := 
		eqDec_components
|}.

Definition P2 : list (attackgraph components) := 
	A0 :: A1 :: A2 :: A3 :: nil.
