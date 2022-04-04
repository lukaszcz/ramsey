(* A proof of the finite Ramsey's theorem: for every s, t there exists
   n such that any finite graph of size at least n contains a clique
   of size s or a completely disconnect subgraph of size t. *)

Require Import Arith Lia ssrfun.
Require Import Program.

Import EqNotations.

From Hammer Require Import Tactics.

Require Import fin.

(* A finite graph on n vertices. The vertices are natural numbers less than n. *)
Structure Graph (n : nat) := {
  E :> Fin n -> Fin n -> Prop;
  E_decidable : forall x y, {E x y} + {~ E x y};
  E_irreflexive : forall x, ~ E x x;
  E_symmetric : forall x y, E x y -> E y x
}.

Definition Empty (n : nat) : Graph n.
Proof.
  refine {| E := (fun x y => False) |}; auto.
Defined.

Definition Clique (n : nat) : Graph n.
Proof.
  refine {| E := (fun x y => x <> y) |}.
  - intros x y.
    destruct (Nat.eq_dec x y); auto with shints.
  - sauto.
  - sauto.
Defined.

Definition SubgraphBy {n m} (f : Fin n -> Fin m) (g1 : Graph n) (g2 : Graph m) :=
    injective f /\ forall i j : Fin n, g1 i j <-> g2 (f i) (f j).

Definition Subgraph {n m} (g1 : Graph n) (g2 : Graph m) :=
  exists f : Fin n -> Fin m, SubgraphBy f g1 g2.

Definition preimage {n m} (g : Graph m) (f : Fin n -> Fin m) : Graph n.
  refine {| E := (fun x y => g (f x) (f y)) |}; sauto.
Defined.

Lemma lem_subgraph_preimage {n m} : forall (g : Graph m) (f : Fin n -> Fin m),
    injective f -> Subgraph (preimage g f) g.
Proof.
  sauto.
Qed.

Lemma lem_subgraph_trans {n m k} (g1 : Graph n) (g2 : Graph m) (g3 : Graph k) :
  Subgraph g1 g2 -> Subgraph g2 g3 -> Subgraph g1 g3.
Proof.
  unfold Subgraph, SubgraphBy; intros [f1 H1] [f2 H2].
  exists (f2 ∘ f1).
  hauto l: on use: inj_comp.
Qed.

Lemma lem_clique_extend {n m} (g : Graph m) (v : Fin m) (f : Fin n -> Fin m) (s : nat) :
  injective f ->
  Subgraph (Clique s) (preimage g f) ->
  (forall v' : Fin n, g v (f v')) ->
  Subgraph (Clique (S s)) g.
Proof.
  intros Hf H Hv.
  unfold Subgraph, SubgraphBy, preimage in H.
  simpl in H.
  destruct H as [h [Hh H]].
  unfold Subgraph, SubgraphBy.
  simpl.
  destruct s as [|s].
  - exists (fun=> v).
    unfold injective.
    sauto lq: on dep: on use: E_irreflexive.
  - exists (fun x : Fin (S (S s)) =>
              match fin_conv (m := s) x with
              | inleft x' => f (h x')
              | inright _ => v
              end).
    split.
    + unfold injective in *; simpl.
      intros x1 x2.
      destruct (fin_conv x1) as [x1'|?] eqn: Heq1.
      * assert (Hx1s: x1 <= s) by eauto using lem_fin_conv_le.
        destruct (fin_conv x2) as [x2'|?] eqn: Heq2.
        ** assert (Hx2s: x2 <= s) by eauto using lem_fin_conv_le.
           destruct (lem_fin_conv x1 s Hx1s) as [x1'' ?].
           destruct (lem_fin_conv x2 s Hx2s) as [x2'' ?].
           assert (x1'' = x1') by hauto l: on.
           assert (x2'' = x2') by hauto l: on.
           hauto l: on use: lem_fin_eq.
        ** intro.
           sfirstorder use: E_irreflexive.
      * destruct (fin_conv x2) as [x2'|?] eqn: Heq2.
        ** assert (Hx2s: x2 <= s) by eauto using lem_fin_conv_le.
           intro.
           sfirstorder use: E_irreflexive.
        ** assert (x1 <= S s) by sauto use: lem_fin_le.
           assert (x1 = ∇ (S s)).
           { apply lem_fin_nabla; lia. }
           assert (x2 <= S s) by sauto use: lem_fin_le.
           assert (x2 = ∇ (S s)).
           { apply lem_fin_nabla; lia. }
           strivial.
    + intros x1 x2.
      destruct (fin_conv x1) as [x1'|?] eqn: Heq1.
      * assert (Hx1s: x1 <= s) by eauto using lem_fin_conv_le.
        destruct (fin_conv x2) as [x2'|?] eqn: Heq2.
        ** assert (Hx2s: x2 <= s) by eauto using lem_fin_conv_le.
           destruct (lem_fin_conv x1 s Hx1s) as [x1'' ?].
           destruct (lem_fin_conv x2 s Hx2s) as [x2'' ?].
           assert (x1'' = x1') by hauto l: on.
           assert (x2'' = x2') by hauto l: on.
           sfirstorder.
        ** sauto use: E_irreflexive.
      * destruct (fin_conv x2) as [x2'|?] eqn: Heq2.
        ** assert (Hx2s: x2 <= s) by eauto using lem_fin_conv_le.
           sauto use: E_irreflexive.
        ** assert (x1 <= S s) by sauto use: lem_fin_le.
           assert (x1 = ∇ (S s)).
           { apply lem_fin_nabla; lia. }
           assert (x2 <= S s) by sauto use: lem_fin_le.
           assert (x2 = ∇ (S s)).
           { apply lem_fin_nabla; lia. }
           strivial use: E_irreflexive.
Qed.

Lemma lem_empty_extend {n m} (g : Graph m) (v : Fin m) (f : Fin n -> Fin m) (s : nat) :
  injective f ->
  Subgraph (Empty s) (preimage g f) ->
  (forall v' : Fin n, f v' <> v /\ ~ g v (f v')) ->
  Subgraph (Empty (S s)) g.
Proof.
  intros Hf H Hv.
  unfold Subgraph, SubgraphBy, preimage in H.
  simpl in H.
  destruct H as [h [Hh H]].
  unfold Subgraph, SubgraphBy.
  simpl.
  destruct s as [|s].
  - exists (fun=> v).
    unfold injective.
    sauto lq: on dep: on use: E_irreflexive.
  - exists (fun x : Fin (S (S s)) =>
              match fin_conv (m := s) x with
              | inleft x' => f (h x')
              | inright _ => v
              end).
    split.
    + unfold injective in *; simpl.
      intros x1 x2.
      destruct (fin_conv x1) as [x1'|?] eqn: Heq1.
      * assert (Hx1s: x1 <= s) by eauto using lem_fin_conv_le.
        destruct (fin_conv x2) as [x2'|?] eqn: Heq2.
        ** assert (Hx2s: x2 <= s) by eauto using lem_fin_conv_le.
           destruct (lem_fin_conv x1 s Hx1s) as [x1'' ?].
           destruct (lem_fin_conv x2 s Hx2s) as [x2'' ?].
           assert (x1'' = x1') by hauto l: on.
           assert (x2'' = x2') by hauto l: on.
           hauto l: on use: lem_fin_eq.
        ** sfirstorder.
      * destruct (fin_conv x2) as [x2'|?] eqn: Heq2.
        ** assert (Hx2s: x2 <= s) by eauto using lem_fin_conv_le.
           sauto lq: on rew: off.
        ** assert (x1 <= S s) by sauto use: lem_fin_le.
           assert (x1 = ∇ (S s)).
           { apply lem_fin_nabla; lia. }
           assert (x2 <= S s) by sauto use: lem_fin_le.
           assert (x2 = ∇ (S s)).
           { apply lem_fin_nabla; lia. }
           strivial.
    + intros x1 x2.
      destruct (fin_conv x1) as [x1'|?] eqn: Heq1.
      * assert (Hx1s: x1 <= s) by eauto using lem_fin_conv_le.
        destruct (fin_conv x2) as [x2'|?] eqn: Heq2.
        ** assert (Hx2s: x2 <= s) by eauto using lem_fin_conv_le.
           destruct (lem_fin_conv x1 s Hx1s) as [x1'' ?].
           destruct (lem_fin_conv x2 s Hx2s) as [x2'' ?].
           assert (x1'' = x1') by hauto l: on.
           assert (x2'' = x2') by hauto l: on.
           sfirstorder.
        ** sauto.
      * destruct (fin_conv x2) as [x2'|?] eqn: Heq2.
        ** assert (Hx2s: x2 <= s) by eauto using lem_fin_conv_le.
           sauto.
        ** assert (x1 <= S s) by sauto use: lem_fin_le.
           assert (x1 = ∇ (S s)).
           { apply lem_fin_nabla; lia. }
           assert (x2 <= S s) by sauto use: lem_fin_le.
           assert (x2 = ∇ (S s)).
           { apply lem_fin_nabla; lia. }
           strivial use: E_irreflexive.
Qed.

Definition dec_add : forall n1 n2 m1 m2,
    n1 + n2 = m1 + m2 -> {n1 >= m1} + {n2 >= S m2}.
  induction n1 as [|n1 IH]; [sauto|].
  destruct n2 as [|n2]; [sauto|].
  destruct m1 as [|m1]; [sauto|].
  destruct m2 as [|m2]; [sauto|].
  sauto.
Defined.

Definition connected_or_disconnected n m (g : Graph (n + m)) :
  forall v : Fin (n + m),
    { exists f : Fin n -> Fin (n + m), injective f /\
                                       forall v' : Fin n, g v (f v')}
    +
    { exists f : Fin m -> Fin (n + m), injective f /\
                                       forall v' : Fin m, f v' <> v /\
                                                          ~ g v (f v') }.
Proof.
  intro v.
  destruct (fin_extract (fun x => g v x) (E_decidable (n + m) g v)) as
      [[k1 k2] [Heq H]].
  destruct (dec_add k1 k2 n m Heq).
  - left.
    destruct H as [f1 [f2 [HIf1 [HIf2 [Hf1 Hf2]]]]].
    destruct k1 as [|k1]; [sauto|].
    exists (fun x : Fin n => f1 (fin_conv2 k1 x)).
    split.
    + unfold injective in *.
      intros.
      destruct n as [|n]; [sauto q: on rew: off|].
      apply (lem_fin_conv2_injective (m := k1)); sauto use: lem_fin_le.
    + sauto.
  - right.
    destruct H as [f1 [f2 [HIf1 [HIf2 [Hf1 Hf2]]]]].
    destruct k2 as [|k2]; [sauto|].
    pose (f := (fun x : Fin m => if fin_eq_dec (f2 (fin_conv2 k2 x)) v then
                                   f2 (∇ k2)
                                 else
                                   f2 (fin_conv2 k2 x))).
    exists f.
    split.
    + unfold injective, f in *.
      intros x1 x2 H.
      destruct m as [|m]; [depelim x1|].
      destruct (fin_eq_dec (f2 (fin_conv2 k2 x1)) v) as [H1|H1];
        destruct (fin_eq_dec (f2 (fin_conv2 k2 x2)) v) as [H2|H2].
      * apply (lem_fin_conv2_injective (m := k2)); sauto use: lem_fin_le.
      * assert (x2 < S m) by sauto use: lem_fin_lt.
        assert (fin_conv2 k2 x2 <> k2 :> nat) by
            (rewrite lem_fin_conv2_to_nat; lia).
        hauto l: on use: lem_nat_to_nat.
      * assert (x1 < S m) by sauto use: lem_fin_lt.
        assert (fin_conv2 k2 x1 <> k2 :> nat) by
            (rewrite lem_fin_conv2_to_nat; lia).
        hauto l: on use: lem_nat_to_nat.
      * apply (lem_fin_conv2_injective (m := k2)); sauto use: lem_fin_le.
    + split.
      * unfold f.
        destruct (fin_eq_dec (f2 (fin_conv2 k2 v')) v) as [Hv'|Hv']; [|assumption].
        destruct m as [|m]; [sauto lq: on rew: off|].
        assert (v' < S m) by sauto use: lem_fin_lt.
        assert (fin_conv2 k2 v' <> k2 :> nat) by
            (rewrite lem_fin_conv2_to_nat; lia).
        hauto l: on use: lem_nat_to_nat unfold: injective.
      * sauto.
Defined.

Definition Ramsey (s t n : nat) :=
  forall g : Graph n, Subgraph (Clique s) g \/ Subgraph (Empty t) g.

Lemma lem_ramsey_zero_l : forall n, Ramsey 0 n 0.
Proof.
  intro n.
  unfold Ramsey.
  intro g.
  left.
  unfold Subgraph.
  refine (ex_intro _ (fun _ => _) _).
  unfold SubgraphBy.
  split.
  - sauto unfold: injective.
  - depelim i; lia.
Qed.

Lemma lem_ramsey_zero_r : forall n, Ramsey n 0 0.
Proof.
  intro n.
  unfold Ramsey.
  intro g.
  right.
  unfold Subgraph.
  refine (ex_intro _ (fun _ => _) _).
  unfold SubgraphBy.
  split.
  - sauto unfold: injective.
  - depelim i; lia.
Qed.

Lemma lem_ramsey_zero : forall s t, Ramsey s t 0 -> s = 0 \/ t = 0.
Proof.
  intros s t.
  unfold Ramsey.
  intro H.
  specialize (H (Empty 0)).
  destruct H as [H|H].
  - left; destruct s; sauto.
  - right; destruct t; sauto.
Qed.

Theorem thm_ramsey : forall s t, exists n, Ramsey s t n.
Proof.
  enough (forall m s t, s + t <= m -> exists n, Ramsey s t n) by sauto.
  induction m as [| m IH ].
  - intros s t ?.
    assert (s = 0) by lia.
    subst.
    exists 0.
    auto using lem_ramsey_zero_l.
  - intros s t Heq.
    destruct (le_lt_eq_dec (s + t) (S m)) as [ | H]; [ trivial.. | ].
    + assert (s + t <= m) by lia.
      auto.
    + clear Heq.
      destruct (Nat.eq_dec s 0) as [Hs|Hs];
        [ exists 0; sauto use: lem_ramsey_zero_l | ].
      destruct (Nat.eq_dec t 0) as [Ht|Ht];
        [ exists 0; sauto use: lem_ramsey_zero_r | ].
      assert (H1: (s - 1) + t <= m) by lia.
      assert (H2: s + (t - 1) <= m) by lia.
      destruct (IH (s - 1) t H1) as [ s' Hs' ].
      destruct (IH s (t - 1) H2) as [ t' Ht' ].
      remember (s' + t') as n eqn:Heqn.
      destruct n as [|n].
      * assert (s' = 0) by lia; subst.
        assert (t' = 0) by lia; subst.
        assert (HH: s = 1 \/ t = 1) by hauto rew: off use: lem_ramsey_zero.
        exists 1.
        destruct HH; subst.
        ** unfold Ramsey.
           intro g.
           left.
           unfold Subgraph.
           exists id.
           unfold SubgraphBy, injective.
           split; [ sauto | ].
           depelim i; [ depelim j; [| depelim j] | depelim i ].
           sauto use: E_irreflexive.
        ** unfold Ramsey.
           intro g.
           right.
           unfold Subgraph.
           exists id.
           unfold SubgraphBy, injective.
           split; [ sauto | ].
           depelim i; [ depelim j; [| depelim j] | depelim i ].
           sauto use: E_irreflexive.
      * exists (s' + t').
        unfold Ramsey in *.
        intro g.
        pose (v := FinO (n := n)).
        destruct (connected_or_disconnected s' t' g (rew Heqn in v)) as
            [[f [Hi Hc]]|[f [Hi Hc]]].
        ** specialize (Hs' (preimage g f)).
           destruct Hs' as [HH|HH].
           *** left.
               clear -HH Hi Hc.
               destruct s as [|s].
               { unfold Subgraph, SubgraphBy, injective.
                 sauto dep: on. }
               simpl in HH.
               rewrite <- minus_n_O in HH.
               eapply lem_clique_extend; sauto.
           *** right.
               clear -HH Hi.
               assert (Subgraph (preimage g f) g) by auto using lem_subgraph_preimage.
               sauto use: lem_subgraph_trans.
        ** specialize (Ht' (preimage g f)).
           destruct Ht' as [HH|HH].
           *** left.
               clear -HH Hi.
               assert (Subgraph (preimage g f) g) by auto using lem_subgraph_preimage.
               sauto use: lem_subgraph_trans.
           *** right.
               clear -HH Hi Hc.
               destruct t.
               { unfold Subgraph, SubgraphBy, injective.
                 sauto dep: on. }
               simpl in HH.
               rewrite <- minus_n_O in HH.
               eapply lem_empty_extend; sauto.
Qed.
