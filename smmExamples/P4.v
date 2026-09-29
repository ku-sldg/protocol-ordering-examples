Require Import AttestationProtocolOrdering.attackgraph.
Require Import ProtocolOrderingExamples.components.

Definition A0 : attackgraph components := 
{|
	event := 
		nat ;
	edges :=
		(2,3) :: (3,1) :: (6,0) :: (5,0) :: (4,2) :: (1,6) :: nil ;
	label := fun ev =>
		match ev with
		| 2 => inl (msp _ bios boot)
		| 3 => inl (msp _ bios smm)
		| 1 => inl (msp _ boot ker)
		| 6 => inr (cor _ ker)
		| 0 => inl (msp _ ker app)
		| 5 => inr (cor _ app)
		| 4 => inl (msp _ crtm bios)
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
		(2,3) :: (3,6) :: (3,1) :: (6,0) :: (4,2) :: (5,0) :: (1,0) :: nil ;
	label := fun ev =>
		match ev with
		| 2 => inl (msp _ bios boot)
		| 3 => inl (msp _ bios smm)
		| 6 => inr (cor _ smm)
		| 1 => inl (msp _ boot ker)
		| 0 => inl (msp _ ker app)
		| 4 => inl (msp _ crtm bios)
		| 5 => inr (cor _ app)
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
		(2,7) :: (2,3) :: (7,1) :: (3,1) :: (6,1) :: (1,0) :: (5,0) :: (4,2) :: nil ;
	label := fun ev =>
		match ev with
		| 2 => inl (msp _ bios boot)
		| 7 => inr (cor _ boot)
		| 3 => inl (msp _ bios smm)
		| 1 => inl (msp _ boot ker)
		| 6 => inr (cor _ ker)
		| 0 => inl (msp _ ker app)
		| 5 => inr (cor _ app)
		| 4 => inl (msp _ crtm bios)
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
		(2,7) :: (7,3) :: (6,3) :: (3,1) :: (4,2) :: (5,0) :: (1,0) :: nil ;
	label := fun ev =>
		match ev with
		| 2 => inl (msp _ bios boot)
		| 7 => inr (cor _ bios)
		| 3 => inl (msp _ bios smm)
		| 6 => inr (cor _ smm)
		| 1 => inl (msp _ boot ker)
		| 4 => inl (msp _ crtm bios)
		| 0 => inl (msp _ ker app)
		| 5 => inr (cor _ app)
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
		(2,3) :: (3,1) :: (6,3) :: (4,7) :: (7,2) :: (5,0) :: (1,0) :: nil ;
	label := fun ev =>
		match ev with
		| 2 => inl (msp _ bios boot)
		| 3 => inl (msp _ bios smm)
		| 1 => inl (msp _ boot ker)
		| 6 => inr (cor _ smm)
		| 4 => inl (msp _ crtm bios)
		| 7 => inr (cor _ bios)
		| 0 => inl (msp _ ker app)
		| 5 => inr (cor _ app)
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
		(2,3) :: (3,1) :: (6,1) :: (1,0) :: (5,0) :: (4,8) :: (8,2) :: (7,2) :: nil ;
	label := fun ev =>
		match ev with
		| 2 => inl (msp _ bios boot)
		| 3 => inl (msp _ bios smm)
		| 1 => inl (msp _ boot ker)
		| 6 => inr (cor _ ker)
		| 0 => inl (msp _ ker app)
		| 5 => inr (cor _ app)
		| 4 => inl (msp _ crtm bios)
		| 8 => inr (cor _ bios)
		| 7 => inr (cor _ boot)
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
		(2,9) :: (9,3) :: (6,1) :: (1,0) :: (5,0) :: (4,8) :: (8,2) :: (7,2) :: (3,1) :: nil ;
	label := fun ev =>
		match ev with
		| 2 => inl (msp _ bios boot)
		| 9 => inr (rep _ bios)
		| 3 => inl (msp _ bios smm)
		| 6 => inr (cor _ ker)
		| 1 => inl (msp _ boot ker)
		| 0 => inl (msp _ ker app)
		| 5 => inr (cor _ app)
		| 4 => inl (msp _ crtm bios)
		| 8 => inr (cor _ bios)
		| 7 => inr (cor _ boot)
		| _ => inl (ms _)
		end ;
	eqDec_event := 
		ltac:(decide equality) ;
	eqDec_component := 
		eqDec_components
|}.

Definition P4 : list (attackgraph components) := 
	A0 :: A1 :: A2 :: A3 :: A4 :: A5 :: A6 :: nil.
