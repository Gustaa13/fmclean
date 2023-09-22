
section propositional

variables P Q R : Prop


------------------------------------------------
-- Proposições de dupla negaço:
------------------------------------------------

theorem doubleneg_intro :
  P → ¬¬P  :=
begin
  intro p,
  intro fp,
  exact fp(p),
end

theorem doubleneg_elim :
  ¬¬P → P  :=
begin
  intro ffp,
  by_cases p_ou_fp : P,
  {
    exact p_ou_fp,
  },
  {
    have f : false := ffp(p_ou_fp),
    contradiction,
  },
end

theorem doubleneg_law :
  ¬¬P ↔ P  :=
begin
  split,
  {
    intro ffp,
    exact doubleneg_elim P (ffp),
  },
  {
    intros p fp,
    exact fp(p),
  },
end

------------------------------------------------
-- Comutatividade dos ∨,∧:
------------------------------------------------

theorem disj_comm :
  (P ∨ Q) → (Q ∨ P)  :=
begin
  intro p_ou_q,
  cases p_ou_q with p q,
  {
    right,
    exact p,
  }, 
  {
    left,
    exact q,
  },
end

theorem conj_comm :
  (P ∧ Q) → (Q ∧ P)  :=
begin
  intro p_e_q,
  cases p_e_q with p q,
  split,
  {
    exact q,
  },
  {
    exact p,
  },
end


------------------------------------------------
-- Proposições de interdefinabilidade dos →,∨:
------------------------------------------------

theorem impl_as_disj_converse :
  (¬P ∨ Q) → (P → Q)  :=
begin
  intros fp_ou_q p,
  cases fp_ou_q with fp q,
  {
    have f : false := fp(p),
    contradiction,
  },
  {
    exact q,
  },
end

theorem disj_as_impl :
  (P ∨ Q) → (¬P → Q)  :=
begin
  intros p_ou_q fp,
  cases p_ou_q with p q,
  {
    have f : false := fp(p),
    contradiction,
  },
  {
    exact q,
  },
end


------------------------------------------------
-- Proposições de contraposição:
------------------------------------------------

theorem impl_as_contrapositive :
  (P → Q) → (¬Q → ¬P)  :=
begin
  intros p_imp_q fq p,
  have q : Q := p_imp_q(p),
  exact fq(q),
end

theorem impl_as_contrapositive_converse :
  (¬Q → ¬P) → (P → Q)  :=
begin
  intros fq_imp_fp p,
  by_cases q_ou_fq : Q,
  {
    exact q_ou_fq,
  },
  {
    have fp : ¬P := fq_imp_fp(q_ou_fq),
    have f : false := fp(p),
    contradiction,
  },
end

theorem contrapositive_law :
  (P → Q) ↔ (¬Q → ¬P)  :=
begin
  split,
  {
    intros p_imp_q fq p,
    have q : Q := p_imp_q(p),
    exact fq(q),
  },
  {
    intros fq_imp_fp p,
    have p_imp_q : P → Q := impl_as_contrapositive_converse P Q (fq_imp_fp),
    exact p_imp_q(p),
  },
end


------------------------------------------------
-- A irrefutabilidade do LEM:
------------------------------------------------

theorem lem_irrefutable :
  ¬¬(P∨¬P)  :=
begin
  intro f_p_ou_fp,
  apply f_p_ou_fp,
  right,
  intro p,
  have p_ou_fq : P ∨ ¬P,
  {
    left,
    exact p,
  },
  exact f_p_ou_fp(p_ou_fq),
end


------------------------------------------------
-- A lei de Peirce
------------------------------------------------

theorem peirce_law_weak :
  ((P → Q) → P) → ¬¬P  :=
begin
  intros p_imp_q__imp_p fp, 
  have p_imp_q : P → Q,
  {
    intro p,
    have f : false := fp(p),
    contradiction,
  },
  have p : P := p_imp_q__imp_p(p_imp_q),
  have f : false := fp(p),
  contradiction,
end


------------------------------------------------
-- Proposições de interdefinabilidade dos ∨,∧:
------------------------------------------------

theorem disj_as_negconj :
  P∨Q → ¬(¬P∧¬Q)  :=
begin
  intros p_ou_q fp_e_fq,
  cases fp_e_fq with fp fq,
  cases p_ou_q with p q,
  {
    exact fp(p),
  },
  {
    exact fq(q),
  },
end

theorem conj_as_negdisj :
  P∧Q → ¬(¬P∨¬Q)  :=
begin
  intros p_e_q fp_ou_fq,
  cases p_e_q with p q,
  cases fp_ou_fq with fp fq,
  {
    exact fp(p),
  },
  {
    exact fq(q),
  },
end


------------------------------------------------
-- As leis de De Morgan para ∨,∧:
------------------------------------------------

theorem demorgan_disj :
  ¬(P∨Q) → (¬P ∧ ¬Q)  :=
begin
  intro f_p_ou_q,
  split,
  {
    intro p,
    have p_ou_q : P∨Q,
    {
      left,
      exact p,
    },
    exact f_p_ou_q(p_ou_q),
  },
  {
    intro q,
    have p_ou_q : P∨Q,
    {
      right,
      exact q,
    },
    exact f_p_ou_q(p_ou_q),
  },
end

theorem demorgan_disj_converse :
  (¬P ∧ ¬Q) → ¬(P∨Q)  :=
begin
  intros fp_e_fq p_ou_q,
  cases fp_e_fq with fp fq,
  cases p_ou_q with p q,
  {
    exact fp(p),
  },
  {
    exact fq(q),
  },
end

theorem demorgan_conj :
  ¬(P∧Q) → (¬Q ∨ ¬P)  :=
begin
  intro f_p_e_q,
  by_cases p_ou_fp : P,
  {
    left,
    intro q,
    have p_e_q : P∧Q,
    {
      split,
      {
        exact p_ou_fp,
      },
      {
        exact q,
      },
    },
    exact f_p_e_q(p_e_q),
  },
  {
    right,
    exact p_ou_fp,
  },
end

theorem demorgan_conj_converse :
  (¬Q ∨ ¬P) → ¬(P∧Q)  :=
begin
  intros fq_ou_fp p_e_q,
  cases p_e_q with p q,
  cases fq_ou_fp with fq fp,
  {
    exact fq(q),
  },
  {
    exact fp(p),
  },
end

theorem demorgan_conj_law :
  ¬(P∧Q) ↔ (¬Q ∨ ¬P)  :=
begin
  split,
  {
    intro f_p_e_q,
    exact demorgan_conj P Q (f_p_e_q),
  },
  {
    intro fq_ou_fp,
    exact demorgan_conj_converse P Q (fq_ou_fp),
  },
end

theorem demorgan_disj_law :
  ¬(P∨Q) ↔ (¬P ∧ ¬Q)  :=
begin
  split,
  {
    intro f_p_ou_q,
    exact demorgan_disj P Q (f_p_ou_q),
  },
  {
    intro fp_e_fq,
    exact demorgan_disj_converse P Q (fp_e_fq),
  },
end

------------------------------------------------
-- Proposições de distributividade dos ∨,∧:
------------------------------------------------

theorem distr_conj_disj :
  P∧(Q∨R) → (P∧Q)∨(P∧R)  :=
begin
  intro p_e__q_ou_r,
  cases p_e__q_ou_r with p q_ou_r,
  cases q_ou_r with q r,
  {
    left,
    split,
    {
      exact p,
    },
    {
      exact q,
    },
  },
  {
    right,
    split,
    {
      exact p,
    },
    {
      exact r,
    },
  },
end

theorem distr_conj_disj_converse :
  (P∧Q)∨(P∧R) → P∧(Q∨R)  :=
begin
  intro p_e_q__ou__p_e_r,
  split,
  {
    cases p_e_q__ou__p_e_r with p_e_q p_e_r,
    {
      cases p_e_q with p q,
      exact p,
    },
    {
      cases p_e_r with p r,
      exact p,
    },
  },
  {
    cases p_e_q__ou__p_e_r with p_e_q p_e_r,
    {
      cases p_e_q with p q,
      left,
      exact q,
    },
    {
      cases p_e_r with p r,
      right,
      exact r,
    },
  },
end

theorem distr_disj_conj :
  P∨(Q∧R) → (P∨Q)∧(P∨R)  :=
begin
  intro p_ou__q_e_r,
  split,
  {
    cases p_ou__q_e_r with p q_e_r,
    {
      left,
      exact p,
    },
    {
      cases q_e_r with q r,
      right,
      exact q,
    },
  },
  {
    cases p_ou__q_e_r with p q_e_r,
    {
      left,
      exact p,
    },
    {
      cases q_e_r with q r,
      right,
      exact r, 
    },
  },
end

theorem distr_disj_conj_converse :
  (P∨Q)∧(P∨R) → P∨(Q∧R)  :=
begin
  intro p_ou_q__e__p_ou_r,
  cases p_ou_q__e__p_ou_r with p_ou_q p_ou_r,
  cases p_ou_r with p r,
  {
    left,
    exact p,
  },
  {
    cases p_ou_q with p q,
    {
      left,
      exact p,
    },
    {
      right,
      split,
      {
        exact q,
      },
      {
        exact r,
      },
    },
  },
end


------------------------------------------------
-- Currificação
------------------------------------------------

theorem curry_prop :
  ((P∧Q)→R) → (P→(Q→R))  :=
begin
  intros p_e_q_imp_r p q,
  have p_e_q : P∧Q,
  {
    split,
    {
      exact p,
    },
    {
      exact q,
    },
  },
  {
    exact p_e_q_imp_r(p_e_q),
  },
end

theorem uncurry_prop :
  (P→(Q→R)) → ((P∧Q)→R)  :=
begin
  intros p_imp_q_imp_r p_e_q,
  cases p_e_q with p q,
  have q_imp_r : Q→R := p_imp_q_imp_r(p),
  exact q_imp_r(q),
end


------------------------------------------------
-- Reflexividade da →:
------------------------------------------------

theorem impl_refl :
  P → P  :=
begin
  intro p,
  exact p,
end

------------------------------------------------
-- Weakening and contraction:
------------------------------------------------

theorem weaken_disj_right :
  P → (P∨Q)  :=
begin
  intro p,
  left,
  exact p,
end

theorem weaken_disj_left :
  Q → (P∨Q)  :=
begin
  intro q,
  right,
  exact q,
end

theorem weaken_conj_right :
  (P∧Q) → P  :=
begin
  intro p_e_q,
  cases p_e_q with p q,
  exact p,
end

theorem weaken_conj_left :
  (P∧Q) → Q  :=
begin
  intro p_e_q,
  cases p_e_q with p q,
  exact q,
end

theorem conj_idempot :
  (P∧P) ↔ P :=
begin
  split,
  {
    intro p_e_p,
    cases p_e_p with p p,
    exact p,
  },
  {
    intro p,
    split,
    {
      exact p,
    },
    {
      exact p,
    },
  },
end

theorem disj_idempot :
  (P∨P) ↔ P  :=
begin
  split,
  {
    intro p_ou_p,
    cases p_ou_p with p p,
    {
      exact p,
    },
    {
      exact p,
    },
  },
  {
    intro p,
    left,
    exact p,
  },
end

end propositional


----------------------------------------------------------------


section predicate

variable U : Type
variables P Q : U -> Prop


------------------------------------------------
-- As leis de De Morgan para ∃,∀:
------------------------------------------------

theorem demorgan_exists :
  ¬(∃x, P x) → (∀x, ¬P x)  :=
begin
  intro fE_px,
  intro u,
  intro pu,
  have px : ∃ (x : U), P x,
  {
    existsi u,
    exact pu,
  },
  exact fE_px(px),
end

theorem demorgan_exists_converse :
  (∀x, ¬P x) → ¬(∃x, P x)  :=
begin
  intro P_fpx,
  intro E_px,
  cases E_px with u pu,
  have fpu : ¬P u := P_fpx(u),
  exact fpu(pu),
end

theorem demorgan_forall :
  ¬(∀x, P x) → (∃x, ¬P x)  :=
begin
  intro fP_px,
  by_contra fE_px,
  apply fP_px,
  intro u,
  by_contra fpu,
  apply fE_px,
  existsi u,
  exact fpu,
end

theorem demorgan_forall_converse :
  (∃x, ¬P x) → ¬(∀x, P x)  :=
begin
  intro E_px,
  intro P_px,
  cases E_px with u fpu,
  have pu : P u := P_px(u),
  exact fpu(pu),
end

theorem demorgan_forall_law :
  ¬(∀x, P x) ↔ (∃x, ¬P x)  :=
begin
  split,
  {
    intro fP_px,
    exact demorgan_forall U P (fP_px),
  },
  {
    intro E_fpx,
    exact demorgan_forall_converse U P (E_fpx),
  },
end

theorem demorgan_exists_law :
  ¬(∃x, P x) ↔ (∀x, ¬P x)  :=
begin
  split,
  {
    intro fE_px,
    exact demorgan_exists U P (fE_px),
  },
  {
    intro P_fpx,
    exact demorgan_exists_converse U P (P_fpx),
  },
end


------------------------------------------------
-- Proposições de interdefinabilidade dos ∃,∀:
------------------------------------------------

theorem exists_as_neg_forall :
  (∃x, P x) → ¬(∀x, ¬P x)  :=
begin
  intros E_px P_fpx,
  cases E_px with u pu,
  have fpu : ¬P u := P_fpx(u),
  exact fpu(pu),
end

theorem forall_as_neg_exists :
  (∀x, P x) → ¬(∃x, ¬P x)  :=
begin
  intros P_px E_fpx,
  cases E_fpx with u fpu,
  have pu : P u := P_px(u),
  exact fpu(pu),
end

theorem forall_as_neg_exists_converse :
  ¬(∃x, ¬P x) → (∀x, P x)  :=
begin
  intros fE_fpx u,
  by_contra fpu,
  have E_fpx : ∃x, ¬P x,
  {
    existsi u,
    exact fpu,
  },
  {
    apply fE_fpx,
    exact E_fpx,
  },
end

theorem exists_as_neg_forall_converse :
  ¬(∀x, ¬P x) → (∃x, P x)  :=
begin
  intro fP_fpx,
  by_contra fE_px,
  apply fP_fpx,
  intro u,
  intro pu,
  apply fE_px,
  existsi u,
  exact pu,
end

theorem forall_as_neg_exists_law :
  (∀x, P x) ↔ ¬(∃x, ¬P x)  :=
begin
  split,
  {
    intro P_px,
    exact forall_as_neg_exists U P (P_px),
  },
  {
    intro fE_fpx,
    exact forall_as_neg_exists_converse U P (fE_fpx),
  },
end

theorem exists_as_neg_forall_law :
  (∃x, P x) ↔ ¬(∀x, ¬P x)  :=
begin
  split,
  {
    intro E_px,
    exact exists_as_neg_forall U P (E_px),
  },
  {
    intro fP_fpx,
    exact exists_as_neg_forall_converse U P (fP_fpx),
  },
end


------------------------------------------------
--  Proposições de distributividade de quantificadores:
------------------------------------------------

theorem exists_conj_as_conj_exists :
  (∃x, P x ∧ Q x) → (∃x, P x) ∧ (∃x, Q x)  :=
begin
  intro E_px_e_qx,
  split,
  {
    cases E_px_e_qx with u pu_e_qu,
    cases pu_e_qu with pu qu,
    existsi u,
    exact pu,
  },
  {
    cases E_px_e_qx with u pu_e_qu,
    cases pu_e_qu with pu qu,
    existsi u,
    exact qu,
  },
end

theorem exists_disj_as_disj_exists :
  (∃x, P x ∨ Q x) → (∃x, P x) ∨ (∃x, Q x)  :=
begin
  intro E_px_ou_qx,
  cases E_px_ou_qx with u pu_ou_qu,
  cases pu_ou_qu with pu qu,
  {
    left,
    existsi u,
    exact pu,
  },
  {
    right,
    existsi u,
    exact qu,
  },
end

theorem exists_disj_as_disj_exists_converse :
  (∃x, P x) ∨ (∃x, Q x) → (∃x, P x ∨ Q x)  :=
begin
  intro E_px__ou__E_qx,
  cases E_px__ou__E_qx with E_px E_qx,
  {
    cases E_px with u pu,
    existsi u,
    left,
    exact pu,
  },
  {
    cases E_qx with u qu,
    existsi u,
    right,
    exact qu,
  },
end

theorem forall_conj_as_conj_forall :
  (∀x, P x ∧ Q x) → (∀x, P x) ∧ (∀x, Q x)  :=
begin
  intro P_px_e_qx,
  split,
  {
    intro u,
    have pu_e_qu : P u ∧ Q u := P_px_e_qx(u),
    cases pu_e_qu with pu qu,
    exact pu,
  },
  {
    intro u,
    have pu_e_qu : P u ∧ Q u := P_px_e_qx(u),
    cases pu_e_qu with pu qu,
    exact qu,
  },
end

theorem forall_conj_as_conj_forall_converse :
  (∀x, P x) ∧ (∀x, Q x) → (∀x, P x ∧ Q x)  :=
begin
  intros P_px__e__P_qx u,
  cases P_px__e__P_qx with P_px P_qx,
  split,
  {
    exact P_px(u),
  },
  {
    exact P_qx(u),
  },
end


theorem forall_disj_as_disj_forall_converse :
  (∀x, P x) ∨ (∀x, Q x) → (∀x, P x ∨ Q x)  :=
begin
  intro P_px__ou__P_qx,
  intro u,
  cases P_px__ou__P_qx with P_px P_qx,
  {
    left,
    exact P_px(u),
  },
  {
    right,
    exact P_qx(u),
  },
end


/- NOT THEOREMS --------------------------------

theorem forall_disj_as_disj_forall :
  (∀x, P x ∨ Q x) → (∀x, P x) ∨ (∀x, Q x)  :=
begin
end

theorem exists_conj_as_conj_exists_converse :
  (∃x, P x) ∧ (∃x, Q x) → (∃x, P x ∧ Q x)  :=
begin
end

---------------------------------------------- -/

end predicate
