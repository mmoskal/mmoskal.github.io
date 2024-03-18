Section Bg.

Require Import Classical.

Require Import Omega.

Open Scope Z_scope.

Lemma s_id : forall T : Type,
	forall A : T -> Prop,
	forall t : T,
	A t -> A t.
intros. trivial. Qed.

Lemma s_pos_implies_def : forall T : Type,
	forall A B : T -> Prop,
	forall t : T,
	(A t -> B t) -> (~A t \/ B t).
intros. apply NNPP. tauto. Qed.

Lemma s_neg_implies_def : forall T : Type,
	forall A B : T -> Prop,
	forall t : T,
	~(A t -> B t) -> ~(~A t \/ B t).
intros. apply NNPP. tauto. Qed.

Lemma s_pos_iff_def : forall T : Type,
	forall A B : T -> Prop,
	forall t : T,
	(A t <-> B t) -> ((~A t \/ B t) /\ (~B t \/ A t)).
intros. apply NNPP. tauto. Qed.

Lemma s_neg_iff_def : forall T : Type,
	forall A B : T -> Prop,
	forall t : T,
	~(A t <-> B t) -> ~((~A t \/ B t) /\ (~B t \/ A t)).
intros. apply NNPP. tauto. Qed.

Lemma s_and_or_distr : forall T : Type,
	forall T0 : Type, forall P0 : T -> T0 -> Prop,
	forall T1 : Type, forall P1 : T -> T1 -> Prop,
	forall A B C : T -> Prop,
	(exists f1 : T1, forall t : T, (B t \/ C t) -> P1 t f1) ->
	(exists f0 : T0, forall t : T, (A t \/ C t) -> P0 t f0) ->
	exists f0 : T0, exists f1 : T1, forall t : T,
	((A t /\ B t) \/ C t) -> (P0 t f0 /\ P1 t f1).
intros. elim H. elim H0. intros. exists x. exists x0. intro.
pose proof (H1 t) as H3. pose proof (H2 t) as H4. tauto. Qed.

Lemma s_or_and_distr : forall T : Type,
	forall T0 : Type, forall P0 : T -> T0 -> Prop,
	forall T1 : Type, forall P1 : T -> T1 -> Prop,
	forall A B C : T -> Prop,
	(exists f1 : T1, forall t : T, (A t \/ C t) -> P1 t f1) ->
	(exists f0 : T0, forall t : T, (A t \/ B t) -> P0 t f0) ->
	exists f0 : T0, exists f1 : T1, forall t : T,
	(A t \/ (B t /\ C t)) -> (P0 t f0 /\ P1 t f1).
intros. elim H. elim H0. intros. exists x. exists x0. intro.
pose proof (H1 t) as H3. pose proof (H2 t) as H4. tauto. Qed.

Lemma s_and_get : forall T : Type,
	forall A B : T -> Prop,
	forall t : T,
	(A t /\ B t) -> A t.
intros. apply NNPP. tauto. Qed.

Lemma s_and_skip : forall T : Type,
	forall A B : T -> Prop,
	forall t : T,
	(A t /\ B t) -> B t.
intros. apply NNPP. tauto. Qed.

Lemma s_pos_and_comp : forall T : Type,
	forall T0 : Type, forall P0 : T -> T0 -> Prop,
	forall T1 : Type, forall P1 : T -> T1 -> Prop,
	forall A B : T -> Prop,
	(exists f1 : T1, forall t : T, B t -> P1 t f1) ->
	(exists f0 : T0, forall t : T, A t -> P0 t f0) ->
	exists f0 : T0, exists f1 : T1, forall t : T,
	(A t /\ B t) -> (P0 t f0 /\ P1 t f1).
intros. elim H. elim H0. intros. exists x. exists x0. intros.
pose proof (H1 t) as H4. pose proof (H2 t) as H5. tauto. Qed.

Lemma s_neg_and_comp : forall T : Type,
	forall T0 : Type, forall P0 : T -> T0 -> Prop,
	forall T1 : Type, forall P1 : T -> T1 -> Prop,
	forall A B : T -> Prop,
	(exists f1 : T1, forall t : T, ~B t -> P1 t f1) ->
	(exists f0 : T0, forall t : T, ~A t -> P0 t f0) ->
	exists f0 : T0, exists f1 : T1, forall t : T,
	~(A t /\ B t) -> (P0 t f0 \/ P1 t f1).
intros. elim H. elim H0. intros. exists x. exists x0. intros.
pose proof (H1 t) as H4. pose proof (H2 t) as H5. apply NNPP. tauto. Qed.

Lemma s_pos_or_comp : forall T : Type,
	forall T0 : Type, forall P0 : T -> T0 -> Prop,
	forall T1 : Type, forall P1 : T -> T1 -> Prop,
	forall A B : T -> Prop,
	(exists f1 : T1, forall t : T, B t -> P1 t f1) ->
	(exists f0 : T0, forall t : T, A t -> P0 t f0) ->
	exists f0 : T0, exists f1 : T1, forall t : T,
	(A t \/ B t) -> (P0 t f0 \/ P1 t f1).
intros. elim H. elim H0. intros. exists x. exists x0. intros.
pose proof (H1 t) as H4. pose proof (H2 t) as H5. tauto. Qed.

Lemma s_neg_or_comp : forall T : Type,
	forall T0 : Type, forall P0 : T -> T0 -> Prop,
	forall T1 : Type, forall P1 : T -> T1 -> Prop,
	forall A B : T -> Prop,
	(exists f1 : T1, forall t : T, ~B t -> P1 t f1) ->
	(exists f0 : T0, forall t : T, ~A t -> P0 t f0) ->
	exists f0 : T0, exists f1 : T1, forall t : T,
	~(A t \/ B t) -> (P0 t f0 /\ P1 t f1).
intros. elim H. elim H0. intros. exists x. exists x0. intros.
pose proof (H1 t) as H4. pose proof (H2 t) as H5. tauto. Qed.

Lemma s_or_comm : forall T : Type,
	forall T0 : Type, forall P0 : T -> T0 -> Prop,
	forall A B C : T -> Prop,
	(exists f0 : T0, forall t : T, (B t \/ C t) -> P0 t f0) ->
	exists f0 : T0, forall t : T,
	((A t \/ B t) \/ C t) -> (A t \/ P0 t f0).
intros. elim H. intros. exists x. intros. pose proof (H0 t) as H2. tauto. Qed.

Lemma s_and_comm : forall T : Type,
	forall T0 : Type, forall P0 : T -> T0 -> Prop,
	forall A B C : T -> Prop,
	(exists f0 : T0, forall t : T, (B t /\ C t) -> P0 t f0) ->
	exists f0 : T0, forall t : T,
	((A t /\ B t) /\ C t) -> (A t /\ P0 t f0).
intros. elim H. intros. exists x. intros. pose proof (H0 t) as H2. tauto. Qed.

Lemma s_nnpp : forall T : Type,
	forall A : T -> Prop,
	forall t : T,
	~~A t -> A t.
intros. apply NNPP. tauto. Qed.

Lemma s_duplicate : forall T : Type,
	forall T0 : Type, forall P0 : T -> T0 -> Prop,
	forall P : T -> Prop,
	(exists f0 : T0, forall t : T, P t -> P0 t f0) ->
	exists f0 : T0, forall t : T,
	P t -> (P0 t f0 /\ P0 t f0).
intros. elim H. intros. exists x. intros. pose proof (H0 t) as H2. tauto. Qed.


Lemma s_compose : forall T T0 T1 : Type,
        forall P0 : T -> T0 -> T1 -> Prop,
        forall P1 : T -> T1 -> Prop,
        forall A : T -> Prop,
        (exists f1 : T1, forall t : T, A t -> P1 t f1) ->
        (forall f1 : T1, exists f0 : T0, forall t : T, P1 t f1 -> P0 t f0 f1) ->
        exists f1 : T1, exists f0 : T0, forall t : T,
        A t -> P0 t f0 f1.
intros.  elim H.  intros.
pose proof (H0 x) as H2.
elim H2.  intros. 
exists x. exists x0.
 intros.
pose proof (H3 t) as H5.
pose proof (H1 t) as H6.
tauto.  Qed.

Require Import ClassicalChoice.
Lemma s_skolemize : forall T T2 : Type,
	T2 -> (* T2 is non empty *)
	forall P : T -> T2 -> Prop,
	exists f : T -> T2, forall t : T,
	((exists x : T2, P t x) -> P t (f t)).

intros. apply choice with (R := fun t ft => (exists x : T2, P t x) -> P t ft).
intros. assert ((exists x0 : T2, P x x0) -> exists y : T2, P x y).
intros.  elim H.  intros.  exists x0.  trivial.
assert (~(exists x0 : T2, P x x0) \/ (exists x0 : T2, P x x0)).
apply NNPP.  tauto.
intuition.  exists X.  tauto.  elim H1.  intros.  exists x0.  tauto.  Qed.

Lemma s_skip_forall : 
forall T1 T2 T3 : Type,
forall P1 : T2 -> T3 -> Prop,
forall P2 : T1 -> T2 -> T3 -> Prop,
  (exists f : T1, forall x : T2, forall y : T3, (P1 x y -> P2 f x y)) ->
  (exists f : T1, forall x : T2, (forall y : T3, P1 x y) -> (forall y : T3, P2 f x y)).
intros. elim H. intros.
exists x. intros.
pose proof (H0 x0 y) as H2.
pose proof (H1 y) as H3.
auto. Qed.

Lemma s_norm_forall : forall T T2 : Type,
	forall P : T -> T2 -> Prop,
	forall t : T,
	(~(forall x : T2, P t x) -> exists x : T2, ~ P t x).
intros.  pose proof (not_all_ex_not T2 (P t) H). trivial. Qed.

Lemma s_norm_exists : forall T T2 : Type,
        forall P : T -> T2 -> Prop,
        forall t : T,
        (~(exists x : T2, P t x) -> forall x : T2, ~ P t x).
intros.  pose proof (not_ex_all_not T2 (P t) H x) . trivial. Qed.

Lemma remove_unused : forall T T2 : Type, forall P : T -> T2 -> Prop,
  T2 -> exists bogus : T2,
  (forall t : T, (forall x : T2, P t x) -> P t bogus).
intros. exists X. intros. apply H. Qed.

Lemma k_to_clause_1 : forall B A : Prop, (A -> B) -> (A -> (~B -> False)).
intros. apply NNPP. tauto. Qed.

Lemma k_to_clause_2 : forall B A : Prop, (A -> B) -> (~B -> (A -> False)).
intros. apply NNPP. tauto. Qed.

Lemma k_to_clause_1_sn : forall B A : Prop, (A -> ~B) -> (A -> (B -> False)).
intros. apply NNPP. tauto. Qed.

Lemma k_to_clause_2_sn : forall B A : Prop, (A -> ~B) -> (B -> (A -> False)).
intros. apply NNPP. tauto. Qed.

Lemma k_absurd_n : forall X : Prop, (~X -> False) -> X.
intros. apply NNPP. tauto. Qed.

Lemma k_absurd_p : forall X : Prop, (X -> False) -> ~X.
intros. apply NNPP. tauto. Qed.

Lemma k_absurd_x : forall X : Prop, X -> (~X -> False).
intros. apply NNPP. tauto. Qed.

Lemma k_absurd_x2 : forall X : Prop, ~X -> (X -> False).
intros. apply NNPP. tauto. Qed.

Lemma k_and_get : forall B A : Prop, (A /\ B) -> A.
intros. apply NNPP. tauto. Qed.

Lemma k_and_skip : forall B A : Prop, (A /\ B) -> B.
intros. apply NNPP. tauto. Qed.

Lemma k_nor_get : forall B A : Prop, ~(A \/ B) -> ~A.
intros. apply NNPP. tauto. Qed.

Lemma k_nor_skip : forall B A : Prop, ~(A \/ B) -> ~B.
intros. apply NNPP. tauto. Qed.

Lemma k_neg_unit_res : forall B A : Prop, A -> ~(A /\ B) -> ~B.
intros. apply NNPP. tauto. Qed.

Lemma k_excl_mid_pn : forall A : Prop, A -> ~A -> False.
intros. apply NNPP. tauto. Qed.

Lemma k_excl_mid_np : forall A : Prop, ~A -> A -> False.
intros. apply NNPP. tauto. Qed.

Lemma k_excl_mid_pn__2 : forall X : Prop, False -> False.
intros. apply NNPP. tauto. Qed.

Lemma k_unit_res_pn : forall B A : Prop, A -> (~A \/ B) -> B.
intros. apply NNPP. tauto. Qed.

Lemma k_unit_res_pn__2 : forall B : Prop, True -> (False \/ B) -> B.
intros. apply NNPP. tauto. Qed.

Lemma k_unit_res_np : forall B A : Prop, ~A -> (A \/ B) -> B.
intros. apply NNPP. tauto. Qed.

Lemma k_simple_res_1_1 : forall L : Prop, (L -> False) -> ~L.
intros. apply NNPP. tauto. Qed.

Lemma k_simple_res_2_1 : forall A L : Prop, (L -> (A -> False)) -> A -> ~L.
intros. apply NNPP. tauto. Qed.

Lemma k_simple_res_2_2 : forall L A : Prop, (A -> (L -> False)) -> A -> ~L.
intros. apply NNPP. tauto. Qed.

Lemma k_simple_res_3_1 : forall B A L : Prop, (L -> (A -> (B -> False))) -> A -> B -> ~L.
intros. apply NNPP. tauto. Qed.

Lemma k_simple_res_3_2 : forall B L A : Prop, (A -> (L -> (B -> False))) -> A -> B -> ~L.
intros. apply NNPP. tauto. Qed.

Lemma k_simple_res_3_3 : forall L B A : Prop, (A -> (B -> (L -> False))) -> A -> B -> ~L.
intros. apply NNPP. tauto. Qed.

Lemma k_nnpp : forall L : Prop, ~~L -> L.
intros. apply NNPP. tauto. Qed.

Lemma k_id : forall X : Prop, (X -> X).
intros. apply NNPP. tauto. Qed.

Lemma k_mp : forall X L : Prop, (L -> X) -> L -> X.
intros. apply NNPP. tauto. Qed.

Lemma k_eq_refl : forall T : Type, forall  T : T, (T = T).
congruence. Qed.

Lemma k_eq_trans : forall T : Type, forall  C B A : T, (A = B) -> (B = C) -> (A = C).
congruence. Qed.

Lemma k_eq_symm : forall T : Type, forall  B A : T, (A = B) -> (B = A).
congruence. Qed.

Lemma k_neq_symm : forall T : Type, forall  B A : T, ~(A = B) -> ~(B = A).
congruence. Qed.


Lemma k_eq_mon : forall T1 T2 : Type, forall P : T1 -> T2,
  forall a b : T1, a = b -> P a = P b.
congruence. Qed.

Lemma k_eq_mon2 : forall T1 : Type, forall P : T1 -> Prop,
  forall a b : T1, a = b -> (P a -> P b).
congruence. Qed.
Lemma k_arith_neg_lt : forall B A : Z, ~(A < B) -> (B <= A).
intros. omega. Qed.

Lemma k_arith_neg_gt : forall B A : Z, ~(A > B) -> (A <= B).
intros. omega. Qed.

Lemma k_arith_lt : forall B A : Z, (A < B) -> ((A + 1) <= B).
intros. omega. Qed.

Lemma k_arith_gt : forall B A : Z, (A > B) -> ((B + 1) <= A).
intros. omega. Qed.

Lemma k_arith_ge : forall B A : Z, (A >= B) -> (B <= A).
intros. omega. Qed.

Lemma k_arith_neg_ge : forall B A : Z, ~(A >= B) -> ((A + 1) <= B).
intros. omega. Qed.

Lemma k_arith_neg_le : forall B A : Z, ~(A <= B) -> ((B + 1) <= A).
intros. omega. Qed.

Lemma k_arith_eq : forall B A : Z, (A = B) -> (A <= B).
intros. omega. Qed.

Lemma k_arith_le_to_left : forall B A : Z, (A <= B) -> ((A - B) <= 0).
intros. omega. Qed.

Lemma k_arith_move_1 : forall C B A : Z, (A <= (B + C)) -> ((A + -B) <= C).
intros. omega. Qed.

Lemma k_arith_move_2 : forall C B A : Z, ((A + B) <= C) -> (A <= (C - B)).
intros. omega. Qed.

Lemma k_utvpi_swap : forall C B A : Z, ((A + B) <= C) -> ((B + A) <= C).
intros. omega. Qed.

Lemma k_utvpi_trans : forall C2 C C1 B A : Z, ((A + B) <= C1) -> ((-A + C) <= C2) -> ((B + C) <= (C1 + C2)).
intros. omega. Qed.


Lemma k_utvpi_tight : forall C2 C1 B A : Z, ((A + B) <= C1) -> ((-A + B) <= C2) -> (B + B <= ((C1 + C2) )).
intros. omega. Qed.  
Lemma k_utvpi_contr1 : forall C2 C1 B A : Z, ((A + B) <= C1) -> ((-A + -B) <= C2) -> (0 <= (C1 + C2)).
intros. omega. Qed.

Lemma k_utvpi_contr2 : forall C2 C1 B A : Z, ((A + -B) <= C1) -> ((-A + B) <= C2) -> (0 <= (C1 + C2)).
intros. omega. Qed.


Lemma k_utvpi_tight2 : forall C A : Z, ((A + A) <= C) -> ((A + 0) + (A + 0) <= (C )).
intros. omega. Qed.  
Lemma k_utvpi_contr_const : forall C : Z, ((0 + 0) <= C) -> (0 <= C).
intros. omega. Qed.

Lemma k_plus_comm : forall W Y X : Z, (((X + Y) + W) = (X + (Y + W))).
intros. omega. Qed.

Lemma k_plus_symm : forall Y X : Z, ((X + Y) = (Y + X)).
intros. omega. Qed.

Lemma k_constant_fold : forall X : Z, (X = X).
intros. omega. Qed.

Lemma k_arith_plus_norm : forall C2 B2 A2 T2 C1 B1 A1 T1 : Z, (T1 = ((A1 + B1) + C1)) -> (T2 = ((A2 + B2) + C2)) -> ((T1 + T2) = (((A1 + A2) + (B1 + B2)) + (C1 + C2))).
intros. omega. Qed.

Lemma k_arith_plus_norm2 : forall C2 A2 T2 C1 A1 T1 : Z, (T1 = ((A1 + 0) + C1)) -> (T2 = ((A2 + 0) + C2)) -> ((T1 + T2) = ((A1 + A2) + (C1 + C2))).
intros. omega. Qed.

Lemma k_arith_minus_norm : forall C2 B2 A2 T2 C1 B1 A1 T1 : Z, (T1 = ((A1 + B1) + C1)) -> (T2 = ((A2 + B2) + C2)) -> ((T1 - T2) = (((A1 - A2) + (B1 - B2)) + (C1 - C2))).
intros. omega. Qed.

Lemma k_arith_minus_norm2 : forall C2 A2 T2 C1 A1 T1 : Z, (T1 = ((A1 + 0) + C1)) -> (T2 = ((A2 + 0) + C2)) -> ((T1 - T2) = ((A1 + -A2) + (C1 - C2))).
intros. omega. Qed.

Lemma k_arith_minus_norm3 : forall C2 A2 T2 C1 A1 T1 : Z, (T1 = ((A1 + 0) + C1)) -> (T2 = ((-A2 + 0) + C2)) -> ((T1 - T2) = ((A1 + A2) + (C1 - C2))).
intros. omega. Qed.

Lemma k_arith_neg_norm : forall C1 B1 A1 T1 : Z, (T1 = ((A1 + B1) + C1)) -> (-T1 = (((0 - A1) + (0 - B1)) + (0 - C1))).
intros. omega. Qed.

Lemma k_arith_neg_norm2 : forall C1 B1 A1 T1 : Z, (T1 = ((A1 + B1) + C1)) -> (-T1 = (((0 - A1) + (0 - B1)) + (0 - C1))).
intros. omega. Qed.

Lemma k_arith_leq_norm : forall C1 B1 A1 T2 T1 : Z, ((T1 - T2) = ((A1 + B1) + C1)) -> (T1 <= T2) -> ((A1 + B1) <= (0 - C1)).
intros. omega. Qed.

Lemma k_minus_eq_def1 : forall C B A : Z, ((A + -B) = C) -> (A = (B + C)).
intros. omega. Qed.

Lemma k_minus_eq_def2 : forall C B A : Z, ((A + -B) = C) -> (B = (A + -C)).
intros. omega. Qed.

Lemma k_minus_eq_def1p : forall C B A : Z, ((A + B) = C) -> (A = (-B + C)).
intros. omega. Qed.

Lemma k_minus_eq_def2p : forall C B A : Z, ((A + -B) = C) -> (B = (A + -C)).
intros. omega. Qed.

Lemma k_utvpi_rev2 : forall C B A : Z, ((-A + B) <= C) -> (-C <= (A + -B)).
intros. omega. Qed.

Lemma k_utvpi_rev2p : forall C B A : Z, ((-A + -B) <= C) -> (-C <= (A + B)).
intros. omega. Qed.

Lemma k_utvpi_rev : forall C A : Z, ((-A + 0) <= C) -> (-C <= A).
intros. omega. Qed.

Lemma k_utvpi_drop_zero : forall C A : Z, ((A + 0) <= C) -> (A <= C).
intros. omega. Qed.

Lemma k_leq_antysymm : forall A C : Z, (C <= A) -> (A <= C) -> (A = C).
intros. omega. Qed.

Lemma k_arith_var_norm : forall V : Z, (V = ((V + 0) + 0)).
intros. omega. Qed.

Lemma k_arith_const_norm : forall C : Z, (C = ((0 + 0) + C)).
intros. omega. Qed.

Lemma k_arith_mul2l : forall T : Z, ((2 * T) = (T + T)).
intros. omega. Qed.

Lemma k_arith_mul2r : forall T : Z, ((T * 2) = (T + T)).
intros. omega. Qed.


Lemma inst : forall T T2 : Type, forall P1 : T -> T2 -> Prop,
  forall P2 : T -> Prop, T2 -> exists inst_t : T2,
    forall t : T, (P2 t -> forall x : T2, P1 t x) -> (P2 t -> P1 t inst_t).
intros. exists X. intros. apply H. trivial. Qed.

End Bg.

