Structure SubgraphOf {m} (g : Graph m) := {
  SG_size : nat;
  SG_graph : Graph SG_size;
  SG_embedding : Fin SG_size -> Fin m;
  SG_subgraph_by : SubgraphBy SG_embedding SG_graph g;
}.

Arguments SG_graph {m g}.
Arguments SG_embedding {m g}.

Lemma lem_subgraph_of {m} (g : Graph m) :
  forall sg : SubgraphOf g, SubgraphBy (SG_embedding sg) (SG_graph sg) g.
Proof.
  sauto lq: on.
Qed.


Program Fixpoint do_fin_fold {n A} m (p : m <= n) (f : Fin n -> A -> A) (acc : A) {struct m} : A :=
  match m with
  | 0 => acc
  | S m' =>
    match n with
    | 0 => _
    | S n' =>
      match ∇[n'] m' with
      | inleft k => do_fin_fold m' _ f (f k acc)
      | inright _ => _
      end
    end
  end.
Next Obligation.
  lia.
Defined.

Definition fin_fold {n A} (f : Fin n -> A -> A) (acc : A) : A.
  refine (do_fin_fold n _ f acc).
  reflexivity.
Defined.

Definition fin_count {n} (P : Fin n -> bool) : nat :=
  fin_fold (fun x acc => if P x then S acc else acc) 0.

Lemma lem_fin_count {n} (P : Fin n -> bool) :
  fin_count P + fin_count (negb ∘ P) = n.
Proof.
Qed.

Program Fixpoint do_fin_extract m n (p : m <= n) (P : Fin n -> Prop)
        (P_dec : forall x, {P x}+{~P x}) {struct m} :
  { (p,f) : { p : nat * nat & ((Fin (fst p) -> Fin n) *
                               (Fin (snd p) -> Fin n))%type} |
      fst p + snd p = m /\
      injective (fst f) /\ injective (snd f) /\
      (forall x : Fin (fst p), fst f x < m) /\
      (forall x : Fin (snd p), snd f x < m) /\
      (forall x : Fin (fst p), P (fst f x)) /\
      (forall x : Fin (snd p), ~ P (snd f x)) } :=
  match m with
  | 0 => existT _ (0,0) _
  | S m' =>
    match n with
    | 0 => existT _ (0,0) _
    | S n' =>
      match ∇[n'] m' with
      | inleft y =>
        if P_dec y then
          match do_fin_extract m' n _ P P_dec with
          | existT _ (k1, k2) (f1, f2) =>
            exist _
                  (existT _ (S k1, k2)
                          ((fun x : Fin (S k1) =>
                              match x in Fin n0 return n0 = S k1 -> Fin n with
                              | FinO => fun _ => _
                              | FinS x' => fun p => f1 (rew (eq_add_S _ _ p) in x')
                              end eq_refl),
                           f2)) _
          end
        else
          match do_fin_extract m' n _ P P_dec with
          | existT _ (k1, k2) (f1, f2) =>
            exist _
                  (existT _ (k1, S k2)
                          (f1,
                           (fun x : Fin (S k2) =>
                              match x in Fin n0 return n0 = S k2 -> Fin n with
                              | FinO => fun _ => _
                              | FinS x' => fun p => f2 (rew (eq_add_S _ _ p) in x')
                              end eq_refl))) _
          end
      | inright _ => _
      end
    end
  end.
Next Obligation.
  qsimpl.
Defined.
Next Obligation.
  qsimpl.
Defined.
Next Obligation.
  qsimpl.
Defined.
Next Obligation.
  lia.
Defined.
Next Obligation.
  lia.
Defined.
Next Obligation.
  unfold injective.
  qsimpl dep: on.
  - unfold do_fin_extract_obligation_7 in *.
    qsimpl.
    assert (f1 X = k1 + k2 :> nat).
    { assert (HH: ∇ (k1 + k2) <= n') by (rewrite lem_nat_to_nat; lia).
      destruct (lem_fin_conv (∇ (k1 + k2)) n' HH).
      hauto use: lem_nat_to_nat. }
    generalize (l X).
    lia.
  - unfold do_fin_extract_obligation_7 in *.
    qsimpl.
    assert (f1 X = k1 + k2 :> nat).
    { assert (HH: ∇ (k1 + k2) <= n') by (rewrite lem_nat_to_nat; lia).
      destruct (lem_fin_conv (∇ (k1 + k2)) n' HH).
      hauto use: lem_nat_to_nat. }
    generalize (l X).
    lia.
  - sauto unfold: injective.
  - unfold do_fin_extract_obligation_7.
    qsimpl.
    assert (k = n0 + n1 :> nat).
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
  lia.
Defined.
