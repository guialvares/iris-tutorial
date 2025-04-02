From iris.heap_lang Require Import lang proofmode notation.

Section double_list.
Context `{!heapGS Σ}.

Fixpoint dlist (a prev : val) (xs : list val) (e next : val) : iProp Σ :=
  match xs with
  | [] => ⌜a = next /\ prev = e⌝
  | x :: xs => ∃ (b : val) (ha : loc) , 
    ha ↦ (x, b, prev) ∗ dlist b a xs e next ∗ ⌜a = SOMEV (#ha) ⌝
  end.

Print val.

Compute ([SOMEV #1] : list val).

Example list_ex : list val := SOMEV #1 :: [] .
Example list_ex2 : list val := SOMEV #2 :: SOMEV #1 :: [] .

(* Example prog : expr :=
    let: "l1" := ref (#0) in
    #1. *)

Lemma wp_ex (prev next x : val) (a : loc) :
    {{{ a ↦ #0 }}}
    #a <- (InjRV #1, next, prev)
    {{{ v, RET v; dlist (SOMEV #a) prev list_ex (SOMEV #a) next }}}.
Proof.
    iIntros (h) "WA Phi".
    wp_pures.
    wp_store.
    iModIntro.
    iApply "Phi".
    unfold list_ex.
    unfold dlist.
    iExists next.
    iExists a.
    by iFrame.
Qed.
