From iris.heap_lang Require Import lang proofmode notation.

Section double_list.
Context `{!heapGS Σ}.

Fixpoint dlist (a prev : val) (xs : list val) (e next : val) : iProp Σ :=
  match xs with
  | [] => ⌜a = next /\ prev = e⌝
  | x :: xs => ∃ (b : val) (ha : loc) , 
    ha ↦ (x, b, prev) ∗ dlist b a xs e next ∗ ⌜a = SOMEV #ha ⌝
  end.

Print val.

Compute ([SOMEV #1] : list val).

Example list_ex : list val := SOMEV #1 :: [] .
Example list_ex2 : list val := SOMEV #1 :: SOMEV #2 :: [] .

Lemma wp_ex (prev next : val) (a : loc) :
    {{{ a ↦ #0 }}}
    #a <- (InjRV #1, next, prev)
    {{{ RET #(); dlist #a prev list_ex #a next }}}.
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
Abort.
    (* by iFrame.
Qed. *)

Lemma wp_ex2 :
    {{{ True }}}
    let: "prev" := ref #0 in 
    let: "next" := ref #1 in 
    let: "a" := ref ((InjRV #1, "next", "prev"))  in
    #()
    {{{ RET #(); ∃ a prev next, dlist a prev list_ex a next }}}.
Proof.
    iIntros (h) "WA Phi".
    wp_alloc prev as "HPrev".
    wp_let.
    wp_alloc next as "HNext".
    wp_alloc a as "Ha".
    wp_pures.
    iModIntro.
    iApply "Phi".
    iExists (SOMEV #a).
    iExists #prev.
    iExists #next.
    unfold list_ex.
    unfold dlist.
    iExists #next.
    iExists a.
    by iFrame.
Qed.

Lemma wp_ex3 :
  {{{ True }}}
  let: "a0" := ref #1 in 
  let: "a" := SOME "a0" in 
  let: "e0" := ref #4 in 
  let: "e" := SOME "e0" in 
  "a0" <- (InjRV #1, "e", #0);;
  "e0" <- (InjRV #2, #0, "a")
  {{{ RET #(); ∃ a e prev next, dlist a prev list_ex2 e next }}}.
Proof.
  iIntros (h) "WA Phi".
  wp_alloc a0 as "Ha".
  wp_let.
  wp_alloc prev as "HPrev".
  wp_let.
  wp_pures.
  wp_store.
  wp_store.
  iModIntro.
  iApply "Phi".
  unfold list_ex2.
  unfold dlist.
  iFrame.
  iExists (SOMEV #prev).
  iExists #0.
  iPureIntro.
  auto.
Qed.