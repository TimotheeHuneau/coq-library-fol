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
				pose (phi0 := quant s_f xs_P _ _ All (atom s_f xs_P _ _ (None) (cons term $0 0 (nil term)))).
				assert (Hphi0 := hh phi0 (fun _ => n0)); simpl in Hphi0.
				rewrite <-Hphi0.
				intros H n'.
				assert (Hs := hh (@atom s_f xs_P _ _ None (cons term $0 0 (nil term))) (fun _ => n'));
				simpl in Hs.
				rewrite Hs. apply H.
		Qed.

	End BDP'.

	Section BEP'.

		Definition gBEP'_on (B A: Type):=
		forall P, exists B', B' ≤ B /\ (exists f: B' -> A, (exists x, P x) -> (exists b, P (f b))).

		Definition gBEP' B := forall A, gBEP'_on B A.

		Lemma gBEP'_mono :
		forall B B', B ≤ B' -> gBEP' B -> gBEP' B'.
		Proof.
			intros B B' hBB' bep A P.
			destruct (bep A P) as [B'' [hBB'' H]]. exists B''. split.
			+ transitivity B. apply hBB''. apply hBB'.
			+ apply H.
		Qed. 

		Theorem BEP'_of_DLS:
		forall M: Type, M -> 
		(forall xM: @model s_f xs_P, gDLS_on s_f xs_P xM smaller) ->
		gBEP'_on (term + xform) M.
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
				pose (phi0 := quant s_f xs_P _ _ Ex (@atom s_f xs_P _ _ (None) (cons term $0 0 (nil term)))).
				assert (Hphi0 := hh phi0 (fun _ => n0)); simpl in Hphi0.
				rewrite <-Hphi0.
				intros [n Hn].
				assert (Hs := hh (@atom s_f xs_P _ _ None (cons term $0 0 (nil term))) (fun _ => n));
				simpl in Hs.
				exists n.
				rewrite <-Hs. apply Hn.
		Qed.

	End BEP'.

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

	Lemma lt_dir: directedR lt.
	Proof. 
		intros n n'. exists (S (n + n')). lia.
	Qed.

	Lemma not_DDC_unit: ~ gDDC unit.
	Proof.
		intros H.
		destruct (H nat lt lt_dir) as [f H'].
		destruct (H' tt tt) as [[] [H'' _]]. lia.
	Qed.

	Lemma lt_tot: totalR lt.
	Proof.
		intros n. exists (S n). lia.
	Qed.

	Lemma not_BDC_unit:
	~ (
		forall X, forall R: X -> X -> Prop, totalR R ->
		exists f: unit -> X, totalR (fun x x' => R (f x) (f x'))
	).
	Proof.
		intros H.
		destruct (H nat lt lt_tot) as [f H'].
		destruct (H' tt) as [[] H'']. lia.
	Qed.

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

	Definition es_f: funcs_signature :=
			Build_funcs_signature (fun f: False => match f return nat with end).

	Definition totaldR {X Y} (R: (forall x: X, Y x -> Prop)) :=
  forall x, exists y, R x y.

	Definition gAC_on B X :=
    forall R: B -> X -> Prop, totalR R ->
		exists B', B' ≤ B /\ exists f: B' -> X, forall b b', R b (f b').

	Theorem AC_of_DLS:
	forall M, M ->
	(forall xM: @model es_f s_P, gDLS_on es_f s_P xM smaller) ->
	gAC_on (s_P) (sigT (fun n => vec M n)).
	Proof.
		intros M m0 dls R hR.
		pose (xI := @B_I
				es_f
				s_P
				M
				(fun _ _ => m0)
				(fun Q v => R Q (existT _ (ar_preds Q) v))).
		pose (xM := @Build_model es_f s_P M xI).
		destruct (dls xM) as [N [[n0] [hsizeN [h hh]]]].
	Admitted.

	Section DDC'.

		Definition gDDC'_on (B A: Type):=
		forall R, directedR R ->
		exists B', B' ≤ B /\ (exists f: B' -> A, directedR (fun b b' => R (f b) (f b'))).

		Definition gDDC' B := forall A, gDDC'_on B A.
	
		Theorem DDC'_of_DLS:
		forall M, M ->
		(forall xM: @model s_f x2s_P, gDLS_on s_f x2s_P xM smaller) ->
		gDDC'_on (term + x2form) M.
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
			exists N. split. apply hsizeN.
			exists h.

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
			
			assert (Hphi0 := hh phi0 (fun _ => n0)). simpl in Hphi0.
			intros n n'.
			unfold directedR in hR.
			rewrite <-Hphi0 in hR.
			destruct (hR n n') as [y hy].
			exists y.
			unfold ">>".
			assert (Hs :=
				hh
					(@atom s_f x2s_P _ _ None (cons term $1 1 (cons term $0 0 (nil term))))
					( y .: (fun _ => n))
				).
			assert (Hs' :=
				hh
					(@atom s_f x2s_P _ _ None (cons term $2 1 (cons term $0 0 (nil term))))
					( y .: (fun _ => n'))
				).
			simpl in Hs, Hs'. rewrite <-Hs, <-Hs'. apply hy.
		Qed.

	End DDC'.

End DDC_and_BAC.

Notation "A ≤s B" := (exists f: B -> A, surjective f) (at level 90).

Lemma BDP_mono_s: forall B B', B ≤s B' -> (gBDP B -> gBDP B').
Proof.
	intros B B' [g hg] bdp A P.
	destruct (bdp A P) as [f hf].
	exists (g >> f).
	intros H a.
	apply hf. intros b.
	destruct (hg b) as [b' h'].
	rewrite <-h'. apply H.
Qed.
	
Lemma BEP_mono_s: forall B B', B ≤s B' -> (gBEP B -> gBEP B'). 
Proof.
	intros B B' [g hg] bep A P.
	destruct (bep A P) as [f hf].
	exists (g >> f).
	intros [a H].
	destruct (hf (ex_intro _ a H)) as [b hb].
	destruct (hg b) as [b' hb'].
	exists b'. unfold ">>". rewrite hb'. apply hb.
Qed.

Lemma DDC_mono_s: forall B B', B ≤s B' -> (gDDC B -> gDDC B').
Proof.
	intros B B' [g hg] ddc A R hdr.
	destruct (ddc A R hdr) as [f hf].
	exists (g >> f).
	intros b1' b2'.
	destruct (hf (g b1') (g b2')) as [b0 h0].
	destruct (hg b0) as [b0' e].
	exists b0'. unfold ">>". rewrite e. apply h0.
Qed.
