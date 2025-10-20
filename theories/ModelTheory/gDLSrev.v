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
	Context {smaller: Type -> Type -> Prop} {smaller_lt: lessthanT smaller}.
	Notation "X ≤ Y" := (smaller X Y) (at level 80) : type_scope.

	Definition surjective {A B: Type} (f: A -> B) :=
		forall b: B, exists a: A, f a  = b.

	Axiom (surj_of_smaller: forall A B: Type, A ≤ B -> (exists f: B -> A, surjective f)).

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
			destruct (dls xM) as [N [hsizeN [h hh]]].
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
			destruct (dls xM) as [N [hsizeN [h hh]]].
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

	(* Unusual notation *)
	Notation "X ≤ Y" := (exists f: Y -> X, surjective f) (at level 80) : type_scope.

		Definition gBDP'_on (B A: Type):=
		forall P, exists B', B' ≤ B /\ (exists f: B' -> A, (forall b', P (f b')) -> (forall a, P a)).
		
		Lemma BDP_mono_of_surj:
		forall B B', B ≤ B' -> (gBDP B -> gBDP B').
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
			+ exists B. split. exists id. intros x. exists x. reflexivity.
				apply (bdp P).
			+ destruct (bdp P) as [B' [[g hg] [f hf]]].
				exists (g >> f).
				intros H. apply hf. intros b'. destruct (hg b') as [b hb]. rewrite <-hb. apply H.
		Qed.

	End BDP'.

End BDP_and_BEP.

Section DDC_and_BAC.
End DDC_and_BAC. 

Print Assumptions BDP_of_DLS.

