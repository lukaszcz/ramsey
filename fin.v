Require Import Arith Lia ssrfun.
Require Import Program.

From Hammer Require Import Tactics.

(* Fin n is a type of natural numbers < n *)
Inductive Fin : nat -> Set :=
| FinO {n} : Fin (S n)
| FinS {n} : Fin n -> Fin (S n).

Fixpoint fin_to_nat {n} (x : Fin n) : nat :=
  match x with
  | FinO => 0
  | FinS y => S (fin_to_nat y)
  end.

Coercion fin_to_nat : Fin >-> nat.

Lemma lem_fin_le {n} : forall x : Fin (S n), x <= n.
Proof.
  depind x; sauto dep: on.
Qed.

Lemma lem_fin_lt {n} : forall x : Fin n, x < n.
Proof.
  depind x; sauto dep: on.
Qed.

Fixpoint nat_to_fin (k : nat) : Fin (S k) :=
  match k with
  | 0 => FinO
  | S m => FinS (nat_to_fin m)
  end.

Lemma lem_nat_to_nat : forall k, fin_to_nat (nat_to_fin k) = k.
Proof.
  induction k; sauto.
Qed.

Lemma lem_fin_eq {n} : forall x y : Fin n, Nat.eq x y -> x = y.
Proof.
  induction x; depelim y; sauto.
Qed.

Global Hint Resolve lem_fin_eq : shints.

Lemma lem_fin_neq {n} : forall x y : Fin n, ~ Nat.eq x y -> x <> y.
Proof.
  hauto l: on.
Qed.

Global Hint Resolve lem_fin_neq : shints.

Definition fin_eq_dec {n} (x y : Fin n) : {x = y} + {x <> y}.
  depind x.
  - sauto lq: on dep: on.
  - depelim y; [ sauto | ].
    destruct (IHx y); [ sauto | ].
    right.
    intro H.
    depelim H.
    sdone.
Defined.

Fixpoint fin_conv {n m} (x : Fin n) : (Fin (S m))+{m < x}.
  refine(
      match x with
      | FinO => inleft FinO
      | @FinS n' x' =>
        match m with
        | 0 => inright _
        | S m' =>
          match fin_conv n' m' x' with
          | inleft y => inleft (FinS y)
          | inright _ => inright _
          end
        end
      end).
  - sauto.
  - sauto.
Defined.

Notation "∇ X" := (nat_to_fin X) (at level 40).
Notation "∇ [ M ] X" := (fin_conv (m := M) (nat_to_fin X)) (at level 40).
Notation "∇ [ ? ] X" := (fin_conv (nat_to_fin X)) (at level 40).

Lemma lem_fin_conv_0_eq {n m} :
  fin_conv (n := S n) (m := m) FinO = inleft FinO.
Proof.
  sauto.
Qed.

Lemma lem_fin_conv_S_eq {n m} (x : Fin n) (y : Fin (S m)) :
  fin_conv x = inleft y ->
  fin_conv (n := S n) (m := S m) (FinS x) = inleft (FinS y).
Proof.
  sauto.
Qed.

Lemma lem_fin_conv {n} :
  forall (x : Fin (S n)) m, x <= m ->
                            exists y, fin_conv (m := m) x = inleft y /\
                                      fin_conv y = inleft x /\
                                      x = y :> nat.
Proof.
  depind x; intros m H.
  - exists FinO.
    sauto lq: on use: lem_fin_conv_0_eq.
  - destruct n; [depelim x|].
    destruct m; [simpl in H; lia|].
    assert (Hnm: x <= m) by sauto.
    destruct (IHx n x ltac:(reflexivity) ltac:(reflexivity) m Hnm) as [y ?].
    exists (FinS y).
    sauto use: lem_fin_conv_S_eq.
Qed.

Lemma lem_fin_conv_le {n} :
  forall (x : Fin (S n)) m,
    (exists y, fin_conv (m := m) x = inleft y) -> x <= m.
Proof.
  depind x; intro m.
  - sauto.
  - intros [y H].
    destruct n; [depelim x|].
    destruct m; [sauto|].
    simpl in H.
    destruct (fin_conv x) as [y'|] eqn:Heq; [|sauto].
    destruct (IHx n x ltac:(reflexivity) ltac:(reflexivity) m (ex_intro _ y' Heq));
      sauto.
Qed.

Definition fin_conv' {n m} (x : Fin n) : (Fin (S m))+{S m < n}.
  destruct (fin_conv (m := m) x).
  - left; assumption.
  - right.
    assert (x < n) by sauto use: lem_fin_lt.
    lia.
Defined.

Lemma lem_fin_conv_injective {n m} :
  forall x y : Fin (S n), x <= m -> y <= m ->
                          fin_conv' (m := m) x = fin_conv' (m := m) y -> x = y.
Proof.
  intros x y Hx Hy.
  destruct (lem_fin_conv x m Hx) as [x' [Hx' [Hx'1 _]]].
  destruct (lem_fin_conv y m Hy) as [y' [Hy' [Hy'1 _]]].
  unfold fin_conv'.
  rewrite Hx'.
  rewrite Hy'.
  intro H.
  injection H.
  intro.
  subst.
  rewrite Hx'1 in Hy'1.
  depelim Hy'1.
  reflexivity.
Qed.

Definition fin_conv2 {n} m (x : Fin n) : Fin (S m) :=
  match fin_conv (m := m) x with inleft y => y | inright _ => FinO end.

Lemma lem_fin_conv2 {n} :
  forall (x : Fin (S n)) m, x <= m -> fin_conv2 n (fin_conv2 m x) = x.
Proof.
  intros x m H.
  destruct (lem_fin_conv x m H) as [y [H1 [H2 _]]].
  unfold fin_conv2.
  rewrite H1.
  rewrite H2.
  reflexivity.
Qed.

Lemma lem_fin_conv2_to_nat {n} :
  forall (x : Fin (S n)) m, x <= m -> fin_to_nat (fin_conv2 m x) = x.
Proof.
  intros x m H.
  destruct (lem_fin_conv x m H).
  unfold fin_conv2.
  sauto.
Qed.

Lemma lem_fin_conv2_injective {n m} :
  forall x y : Fin (S n), x <= m -> y <= m -> fin_conv2 m x = fin_conv2 m y -> x = y.
Proof.
  unfold fin_conv2.
  intros x y Hx Hy H.
  eapply lem_fin_conv_injective; [eassumption..|].
  destruct (lem_fin_conv x m Hx) as [x' [Hx' [Hx'1 _]]].
  destruct (lem_fin_conv y m Hy) as [y' [Hy' [Hy'1 _]]].
  unfold fin_conv'.
  qauto l: on dep: on.
Qed.

Lemma lem_fin_nabla {n} (x : Fin (S n)) : x = n :> nat -> x = ∇ n.
Proof.
  depind x; sauto q: on.
Qed.

Lemma lem_fin_neq_nabla {n} (x : Fin (S n)) : x <> ∇ n -> x < n.
Proof.
  intro H.
  assert (x <> n :> nat) by auto using lem_fin_nabla.
  assert (x <= n) by sauto use: lem_fin_le.
  assert (x < n) by lia.
  strivial.
Qed.

Lemma lem_fin_S_either {n m} (f : Fin (S n) -> Fin (S m)) :
  (exists x : Fin (S n), f x = ∇ m) \/ forall x : Fin (S n), f x < m.
Proof.
  induction n as [|n IH].
  - destruct (fin_eq_dec (f FinO) (∇ m));
      sauto lq: on dep: on use: lem_fin_neq_nabla.
  - pose (g := fun x : Fin (S n) => f (fin_conv2 (S n) x)).
    specialize (IH g).
    destruct IH as [[x H]|H].
    + left.
      exists (fin_conv2 (S n) x).
      assumption.
    + destruct (fin_eq_dec (f (∇ S n)) (∇ m)); [ strivial | ].
      right.
      intro x.
      destruct (fin_eq_dec x (∇ S n)).
      * qauto l: on use: lem_fin_neq_nabla.
      * assert (x < S n) by qauto l: on use: lem_fin_neq_nabla.
        specialize (H (fin_conv2 n x)).
        unfold g in H.
        rewrite lem_fin_conv2 in H by lia.
        assumption.
Qed.

Lemma lem_fin_injective_le {n m} (f : Fin n -> Fin m) : injective f -> n <= m.
Proof.
  revert f.
  revert m n.
  unfold injective.
  induction m as [| m IH ].
  - intros.
    destruct n; subst.
    + reflexivity.
    + remember (∇[n] 0) as x0.
      destruct x0 as [x0|]; [| strivial ].
      remember (f x0) as y.
      depelim y.
  - intros n f H.
    destruct n; [lia|].
    destruct m.
    { destruct n; [reflexivity|].
      remember (∇[S n] 0) as x0.
      remember (∇[S n] 1) as x1.
      destruct x0 as [x0|]; [| strivial ].
      destruct x1 as [x1|]; [| strivial ].
      remember (f x0) as y0.
      remember (f x1) as y1.
      depelim y0.
      depelim y1.
      2: depelim y1.
      2: depelim y0.
      assert (x0 = x1) by sauto.
      sauto. }
    destruct (lem_fin_S_either f) as [[y HH]|HH].
    + assert (H0: forall x : Fin (S n), x <> y -> f x <= m).
      { intros x Hx.
        assert (f x <> ∇ S m) by sauto.
        assert (f x <= S m) by auto using lem_fin_le.
        assert (f x < S m) by auto using lem_fin_neq_nabla.
        lia. }
      pose (g := fun x : Fin n =>
                   fin_conv2 m (f (if lt_dec x y then fin_conv2 n x else FinS x))).
      assert (Hg: forall x1 x2 : Fin n, g x1 = g x2 -> x1 = x2).
      { clear -H0 H.
        intros x1 x2 Hg.
        unfold g in Hg.
        destruct n; [depelim x1|].
        destruct (lt_dec x1 y) as [H1|H1];
          destruct (lt_dec x2 y) as [H2|H2].
        * apply (lem_fin_conv2_injective (m := S n)); auto using lem_fin_le.
          apply H.
          apply (lem_fin_conv2_injective (m := m)).
          ** apply H0.
             intro HH.
             rewrite <- HH in H1.
             rewrite lem_fin_conv2_to_nat in H1 by sauto use: lem_fin_le.
             lia.
          ** apply H0.
             intro HH.
             rewrite <- HH in H2.
             rewrite lem_fin_conv2_to_nat in H2 by sauto use: lem_fin_le.
             lia.
          ** assumption.
        * exfalso.
          apply lem_fin_conv2_injective in Hg.
          ** apply H in Hg.
             assert (x1 = S x2 :> nat).
             { erewrite <- lem_fin_conv2_to_nat; hauto l: on use: lem_fin_le. }
             lia.
          ** apply H0.
             intro HH.
             rewrite <- HH in H1.
             rewrite lem_fin_conv2_to_nat in H1; [lia|hauto l: on use: lem_fin_le].
          ** apply H0.
             intro HH.
             rewrite <- HH in H2.
             simpl in H2.
             lia.
        * exfalso.
          apply lem_fin_conv2_injective in Hg.
          ** apply H in Hg.
             assert (S x1 = x2 :> nat).
             { replace (fin_to_nat x2) with (fin_to_nat (fin_conv2 (S n) x2)).
               *** rewrite <- Hg.
                   reflexivity.
               *** rewrite lem_fin_conv2_to_nat;
                     [ reflexivity |  hauto l: on use : lem_fin_le ]. }
             lia.
          ** apply H0.
             intro HH.
             rewrite <- HH in H1.
             simpl in H1.
             lia.
          ** apply H0.
             intro HH.
             rewrite <- HH in H2.
             rewrite lem_fin_conv2_to_nat in H2; [lia|hauto l: on use: lem_fin_le].
        * apply lem_fin_conv2_injective in Hg.
          ** apply H in Hg.
             depelim Hg.
             reflexivity.
          ** apply H0.
             intro HH.
             rewrite <- HH in H1.
             simpl in H1.
             lia.
          ** apply H0.
             intro HH.
             rewrite <- HH in H2.
             simpl in H2.
             lia. }
      specialize (IH n g Hg).
      lia.
    + pose (g := fun x : Fin (S n) => fin_conv2 m (f x)).
      assert (Hg: forall x1 x2, g x1 = g x2 -> x1 = x2).
      { unfold g.
        intros x1 x2 Hg.
        apply H.
        assert (f x1 <= m) by (clear -HH; sauto).
        assert (f x2 <= m) by (clear -HH; sauto).
        eapply lem_fin_conv2_injective; [eassumption..|].
        assumption. }
      specialize (IH (S n) g Hg).
      lia.
Qed.

Import EqNotations.

Program Fixpoint do_fin_extract m n (p : m <= n) (P : Fin n -> Prop)
        (P_dec : forall x, {P x}+{~P x}) {struct m} :
  { (k1,k2) : nat * nat | k1 + k2 = m /\
      exists (f1 : Fin k1 -> Fin n) (f2 : Fin k2 -> Fin n),
      injective f1 /\ injective f2 /\
      (forall x : Fin k1, f1 x < m) /\
      (forall x : Fin k2, f2 x < m) /\
      (forall x : Fin k1, P (f1 x)) /\
      (forall x : Fin k2, ~ P (f2 x)) } :=
  match m with
  | 0 => (0,0)
  | S m' =>
    match n with
    | 0 => (0,0)
    | S n' =>
      match ∇[n'] m' with
      | inleft k =>
        if P_dec k then
          match do_fin_extract m' n _ P P_dec with
          | (k1, k2) => (S k1, k2)
          end
        else
          match do_fin_extract m' n _ P P_dec with
          | (k1, k2) => (k1, S k2)
          end
      | inright _ => _
      end
    end
  end.
Next Obligation.
  qsimpl.
  unshelve (eexists; eexists; qsimpl); intro x; depelim x.
Defined.
Next Obligation.
  lia.
Defined.
Next Obligation.
  lia.
Defined.
Next Obligation.
  qsimpl.
  rename H into f2.
  rename e0 into f0.
  rename y into HP.
  match goal with
  | [ H: P ?Y |- _ ] => remember Y as y
  end.
  pose (f1 :=
          (fun x : Fin (S n0) =>
             match x in Fin n return n = S n0 -> Fin (S n') with
             | FinO => fun _ => y
             | FinS x' => fun p => f0 (rew (eq_add_S _ _ p) in x')
             end eq_refl)).
  exists f1, f2.
  unfold injective.
  qsimpl dep: on.
  - assert (f0 X = n0 + n1 :> nat).
    { assert (HH: ∇ (n0 + n1) <= n') by (rewrite lem_nat_to_nat; lia).
      destruct (lem_fin_conv (∇ (n0 + n1)) n' HH).
      sauto use: lem_nat_to_nat. }
    generalize (l X).
    lia.
  - assert (f0 X = n0 + n1 :> nat).
    { assert (HH: ∇ (n0 + n1) <= n') by (rewrite lem_nat_to_nat; lia).
      destruct (lem_fin_conv (∇ (n0 + n1)) n' HH).
      sauto use: lem_nat_to_nat. }
    generalize (l X).
    lia.
  - sauto unfold: injective.
  - assert (k = n0 + n1 :> nat).
    { assert (HH: ∇ (n0 + n1) <= n') by (rewrite lem_nat_to_nat; lia).
      destruct (lem_fin_conv (∇ (n0 + n1)) n' HH).
      sauto use: lem_nat_to_nat. }
    lia.
  - sauto.
  - sauto.
Defined.
Next Obligation.
  lia.
Defined.
Next Obligation.
  qsimpl.
  rename H into f2'.
  rename e0 into f1.
  rename n0 into HP.
  match goal with
  | [ H: P ?Y -> False |- _ ] => remember Y as y
  end.
  pose (f2 :=
          (fun x : Fin (S n2) =>
             match x in Fin n return n = S n2 -> Fin (S n') with
             | FinO => fun _ => y
             | FinS x' => fun p => f2' (rew (eq_add_S _ _ p) in x')
             end eq_refl)).
  exists f1, f2.
  unfold injective.
  qsimpl dep: on.
  - assert (f2' X = n1 + n2 :> nat).
    { assert (HH: ∇ (n1 + n2) <= n') by (rewrite lem_nat_to_nat; lia).
      destruct (lem_fin_conv (∇ (n1 + n2)) n' HH).
      sauto use: lem_nat_to_nat. }
    generalize (l0 X).
    lia.
  - assert (f2' X = n1 + n2 :> nat).
    { assert (HH: ∇ (n1 + n2) <= n') by (rewrite lem_nat_to_nat; lia).
      destruct (lem_fin_conv (∇ (n1 + n2)) n' HH).
      sauto use: lem_nat_to_nat. }
    generalize (l0 X).
    lia.
  - sauto unfold: injective.
  - sauto.
  - assert (k = n1 + n2 :> nat).
    { assert (HH: ∇ (n1 + n2) <= n') by (rewrite lem_nat_to_nat; lia).
      destruct (lem_fin_conv (∇ (n1 + n2)) n' HH).
      sauto use: lem_nat_to_nat. }
    lia.
  - sauto.
Defined.
Next Obligation.
  clear Heq_anonymous.
  rewrite lem_nat_to_nat in wildcard'.
  lia.
Defined.

Definition fin_extract {n} (P : Fin n -> Prop) (P_dec : forall x, {P x}+{~P x}) :
  { (k1,k2) : nat * nat | k1 + k2 = n /\
      exists (f1 : Fin k1 -> Fin n) (f2 : Fin k2 -> Fin n),
      injective f1 /\ injective f2 /\
      (forall x : Fin k1, P (f1 x)) /\ (forall x : Fin k2, ~ P (f2 x)) }.
  destruct (do_fin_extract n n (Nat.le_refl n) P P_dec) as [[k1 k2] [Heq H]].
  exists (k1, k2).
  sauto.
Defined.
