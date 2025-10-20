Require Import Lia.
Require Import FOL.ModelTheory.Core.
Require Import FOL.ModelTheory.gDLS_defs.

Section BDP_and_BEP.

	Definition extend_sigP: preds_signature -> preds_signature :=
			fun s => Build_preds_signature (fun P => match P with 
					| Some R => @ar_preds s R
					| None => 1
					end).

	Context {s_f: funcs_signature}.
	Context {s_P:  preds_signature}.
	Context {smaller: Type -> Type -> Prop} {smaller_lt: lessthanT smaller} {surj_of_smaller: SoS smaller}.
	Notation "X ≤ Y" := (smaller X Y) (at level 80) : type_scope.

	Definition xs_P := extend_sigP s_P.

	Notation xform := (form s_f xs_P).

	Theorem BDP_of_DLS:
	forall M: Type, M -> 
	(forall xM: @model s_f xs_P, gDLS_on s_f xs_P xM smaller) ->
	gBDP_on (term + xform) M.
	Proof.
			intros M m0 dls P.
			pose (xI := @B_I
				s_f
				xs_P
				M
				(fun _ _ => m0)
				(fun Q v => match Q with
					| Some _ => True
					| None => match v with 
						| cons _ m 0 (nil _) => P m 
						| _ => False
						end
				end)).
			pose (xM := @Build_model s_f xs_P M xI).
			destruct (dls xM) as [N [[n0] [hsizeN [h hh]]]].
			destruct (surj_of_smaller hsizeN) as [g hg].
			exists (g >> h).
			intros Htf. 

			(* phi0 :=  `∀ p(x0)` *)
			pose (phi0 := quant s_f xs_P _ _ All (@atom s_f xs_P _ _ (None) (cons term $0 0 (nil term)))).
			assert (H3 := hh phi0 (fun _ => g (inl $0))); simpl in H3.
			rewrite <-H3.
			
			intros n'.
			assert (H5 := hh (@atom s_f xs_P _ _ None (cons term $0 0 (nil term))) (fun _ => n')); simpl in H5.
			rewrite H5.
			destruct (hg n') as [x hx]. unfold ">>". rewrite <-hx.
			apply (Htf x).
	Qed.

	Theorem BEP_of_DLS:
	forall M: Type, M -> 
	(forall xM: @model s_f xs_P, gDLS_on s_f xs_P xM smaller) ->
	gBEP_on (term + xform) M.
	Proof.
		intros M m0 dls P.
		pose (xI := @B_I
				s_f
				xs_P
				M
				(fun _ _ => m0)
				(fun Q v => match Q with
					| Some _ => True
					| None => match v with 
						| cons _ m 0 (nil _) => P m 
						| _ => False
						end
				end)).
			pose (xM := @Build_model s_f xs_P M xI).
			destruct (dls xM) as [N [[n0] [hsizeN [h hh]]]].
			destruct (surj_of_smaller hsizeN) as [g hg].
			exists (g >> h).

			pose (phi0 := quant s_f xs_P _ _ Ex (@atom s_f xs_P _ _ (None) (cons term $0 0 (nil term)))).
			assert (H3 := hh phi0 (fun _ => g (inl $0))); simpl in H3.
			rewrite <-H3.
			
			intros [n hn].
			assert (H5 := hh (@atom s_f xs_P _ _ None (cons term $0 0 (nil term))) (fun _ => n)); simpl in H5.
			destruct (hg n) as [x hx].
			exists x. unfold ">>". rewrite hx.
			rewrite <-H5. apply hn.
	Qed.

	Section BDP'.

		Definition gBDP'_on (B A: Type):=
		forall P, exists B', B' ≤ B /\ (exists f: B' -> A, (forall b', P (f b')) -> (forall a, P a)).

		Definition gBDP' B := forall A, gBDP'_on B A.

		Lemma gBDP'_mono :
		forall B B', B ≤ B' -> gBDP' B -> gBDP' B'.
		Proof.
			intros B B' hBB' bdp A P.
			destruct (bdp A P) as [B'' [hBB'' H]]. exists B''. split.
			+ transitivity B. apply hBB''. apply hBB'.
			+ apply H.
		Qed. 

		Theorem BDP'_of_DLS:
		forall M: Type, M -> 
		(forall xM: @model s_f xs_P, gDLS_on s_f xs_P xM smaller) ->
		gBDP'_on (term + xform) M.
		Proof.
				intros M m0 dls P.
				pose (xI := @B_I
					s_f
					xs_P
					M
					(fun _ _ => m0)
					(fun Q v => match Q with
						| Some _ => True
						| None => match v with 
							| cons _ m 0 (nil _) => P m 
							| _ => False
							end
					end)).
				pose (xM := @Build_model s_f xs_P M xI).
				destruct (dls xM) as [N [[n0] [hsizeN [h hh]]]].
				exists N. split.
				apply hsizeN.
				exists h.

				(* phi0 :=  `∀ P(x0)` *)
				pose (phi0 := quant s_f xs_P _ _ All (@atom s_f xs_P _ _ (None) (cons term $0 0 (nil term)))).
				assert (H3 := hh phi0 (fun _ => n0)); simpl in H3.
				rewrite <-H3.
				intros H  n'.
				assert (H5 := hh (@atom s_f xs_P _ _ None (cons term $0 0 (nil term))) (fun _ => n'));
				simpl in H5.
				rewrite H5. apply H.
		Qed.


		(* Unusual notation *)
		Notation "X ≤s Y" := (exists f: Y -> X, surjective f) (at level 80) : type_scope.
		
		Lemma BDP_mono_of_surj:
		forall B B', B ≤s B' -> (gBDP B -> gBDP B').
		Proof.
			intros B B' [g hg] bdp A P.
			destruct (bdp A P) as [f hf].
			exists (g >> f).
			intros H. apply hf. intros b.
			destruct (hg b) as [b' hb'].
			rewrite <-hb'. apply H.
		Qed.

		Lemma BDP'_of_BDP: forall B A, gBDP_on B A <-> gBDP'_on B A.
		Proof.
			intros B A. split.
			all: intros bdp P.
			+ destruct (bdp P) as [f hf].
				exists B. split. reflexivity. exists f. apply hf.	
			+ destruct (bdp P) as [B' [hBB' [f hf]]].
				destruct (surj_of_smaller hBB') as [g hg].	
				exists (g >> f).
				intros H. apply hf. intros b'. destruct (hg b') as [b hb]. rewrite <-hb. apply H.
		Qed.

	End BDP'.

End BDP_and_BEP.

Section DDC_and_BAC.

	Definition extend2_sigP: preds_signature -> preds_signature :=
			fun s => Build_preds_signature (fun P => match P with 
					| Some R => @ar_preds s R
					| None => 2
					end).

	Context {s_f: funcs_signature}.
	Context {s_P:  preds_signature}.
	Context {smaller: Type -> Type -> Prop} {smaller_lt: lessthanT smaller} {surj_of_smaller: @SoS smaller}.
	Notation "X ≤ Y" := (smaller X Y) (at level 80) : type_scope.

	Definition x2s_P := extend2_sigP s_P.

	Notation x2form := (form s_f x2s_P).

	Theorem DDC_of_DLS:
	forall M, M ->
	(forall xM: @model s_f x2s_P, gDLS_on s_f x2s_P xM smaller) ->
	gDDC_on (term + x2form) M.
	Proof.
		intros M m0 dls R hR.
		pose (xI := @B_I
				s_f
				x2s_P
				M
				(fun _ _ => m0)
				(fun Q v => match Q with
					| Some _ => True
					| None => match v with 
						| cons _ v1 _ (cons _ v2 _ (nil _)) => R v1 v2 
						| _ => False
						end
				end)).
			pose (xM := @Build_model s_f x2s_P M xI).
				destruct (dls xM) as [N [[n0] [hsizeN [h hh]]]].
			destruct (surj_of_smaller hsizeN) as [g hg].
			exists (g >> h).

			pose (phi0 :=
				quant s_f x2s_P _ _ All
					(quant s_f x2s_P _ _ All
						(quant s_f x2s_P _ _ Ex
							(bin s_f x2s_P _ _ Conj
								(atom s_f x2s_P _ _ (None) (cons term $2 1 (cons term $0 0 (nil term))))
								(atom s_f x2s_P _ _ (None) (cons term $1 1 (cons term $0 0 (nil term))))
							)
						)
					)
				).
			

			assert (H1 := hh phi0 (fun _ => g (inl $0))). simpl in H1.
			intros x x'.
			unfold directedR in hR.
			rewrite <-H1 in hR.
			destruct (hR (g x) (g x')) as [n' hn'].
			destruct (hg n') as [y hy].
			exists y.
			unfold ">>".
			rewrite hy.
			simpl in hn'.
			assert (H2 :=
				hh
					(@atom s_f x2s_P _ _ None (cons term $1 1 (cons term $0 0 (nil term))))
					( n' .: (fun _ => (g x)))
				).
			assert (H2' :=
				hh
					(@atom s_f x2s_P _ _ None (cons term $2 1 (cons term $0 0 (nil term))))
					( n' .: (fun _ => (g x')))
				).
			simpl in H2, H2'. rewrite <-H2, <-H2'. apply hn'.
	Qed.

End DDC_and_BAC.