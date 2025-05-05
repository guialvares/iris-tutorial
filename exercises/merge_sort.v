From stdpp Require Export sorting.
From iris.heap_lang Require Import array lang proofmode notation par.

(* ################################################################# *)
(** * Case Study: Merge Sort *)

(* ================================================================= *)
(** ** Implementation *)

(**
  Let us implement a simple multithreaded merge sort on arrays. Merge
  sort consists of splitting the array in half until we are left with
  pieces of size [0] or [1]. Then, each pair of pieces is merged into a
  new sorted array.
*)

(**
  We begin by implementing a function which merges two arrays [a1] and
  [a2] of lengths [n1] and [n2] into an array [b] of length [n1 + n2].
*)
Definition merge : val :=
  rec: "merge" "a1" "n1" "a2" "n2" "b" :=
  (** If [a1] is empty, we simply copy the second [a2] into [b]. *)
  if: "n1" = #0 then
    array_copy_to "b" "a2" "n2"
  (** Likewise if [a2] is empty instead. *)
  else if: "n2" = #0 then
    array_copy_to "b" "a1" "n1"
  else
  (**
    Otherwise, we compare the first elements of [a1] and [a2]. The
    smallest is removed and written to [b]. Rinse and repeat.
  *)
    let: "x1" := !"a1" in
    let: "x2" := !"a2" in
    if: "x1" ≤ "x2" then
      "b" <- "x1";;
      "merge" ("a1" +ₗ #1) ("n1" - #1) "a2" "n2" ("b" +ₗ #1)
    else
      "b" <- "x2";;
      "merge" "a1" "n1" ("a2" +ₗ #1) ("n2" - #1) ("b" +ₗ #1).

(**
  To sort an array [a], we split the array in half, sort each sub-array
  recursively on separate threads, and merge the sorted sub-arrays using
  [merge], writing the elements back into the array.
*)
Definition merge_sort_inner : val :=
  rec: "merge_sort_inner" "a" "b" "n" :=
  if: "n" ≤ #1 then #()
  else
    let: "n1" := "n" `quot` #2 in
    let: "n2" := "n" - "n1" in
    ("merge_sort_inner" "b" "a" "n1" ||| "merge_sort_inner" ("b" +ₗ "n1") ("a" +ₗ "n1") "n2");;
    merge "b" "n1" ("b" +ₗ "n1") "n2" "a".

(**
  HeapLang requires array allocations to contain at least one element.
  As such, we need to treat this case separately.
*)
Definition merge_sort : val :=
  λ: "a" "n",
  if: "n" = #0 then #()
  else
    let: "b" := AllocN "n" #() in
    array_copy_to "b" "a" "n";;
    merge_sort_inner "a" "b" "n".

(**
  Our desired specification will be that [merge_sort] produces a new
  sorted array which, importantly, is a permutation of the input.
*)

(* ================================================================= *)
(** ** Specifications *)

Section proofs.
Context `{!heapGS Σ, !spawnG Σ}.

(**
  We begin by giving a specification for the [merge] function. To merge
  two arrays [a1] and [a2], we require that they are both already
  sorted. Furthermore, we need the result array [b] to have enough
  space, though we don't care what it contains.
*)
Lemma merge_spec (a1 a2 b : loc) (l1 l2 : list Z) (l : list val) :
  {{{
    a1 ↦∗ ((λ x : Z, #x) <$> l1) ∗
    a2 ↦∗ ((λ x : Z, #x) <$> l2) ∗ b ↦∗ l ∗
    ⌜StronglySorted Z.le l1⌝ ∗
    ⌜StronglySorted Z.le l2⌝ ∗
    ⌜length l = (length l1 + length l2)%nat⌝
  }}}
    merge #a1 #(length l1) #a2 #(length l2) #b
  {{{(l : list Z), RET #();
    a1 ↦∗ ((λ x : Z, #x) <$> l1) ∗
    a2 ↦∗ ((λ x : Z, #x) <$> l2) ∗
    b ↦∗ ((λ x : Z, #x) <$> l) ∗
    ⌜StronglySorted Z.le l⌝ ∗
    ⌜l1 ++ l2 ≡ₚ l⌝
  }}}.
Proof.
  iIntros (Φ) "(A1 & A2 & Bl & %SL1 & %SL2 & %LEq) H2".
  iLöb as "IH" forall (a1 a2 b l1 l2 l SL1 SL2 LEq).
  destruct l1 as [|x1 l1].
  - simpl.
    wp_rec.
    wp_pures.
    rewrite length_nil Nat.add_0_l in LEq.
    iApply (wp_array_copy_to with "[$Bl $A2]"); auto.
    * by rewrite length_fmap.
    * iIntros "!> [BL A2L]".
      iApply "H2".
      by iFrame.
  - wp_rec.
    wp_pures.
    destruct l2 as [|x2 l2].
    * wp_pures.
      iApply (wp_array_copy_to with "[$Bl $A1]").
      -- rewrite LEq. auto.
      -- simpl. by rewrite length_fmap.
      -- iIntros "!> [Hb Ha1]".
         iApply "H2".
         iFrame.
         by rewrite app_nil_r.
    * wp_pures.
      rewrite !fmap_cons.
      setoid_rewrite array_cons.
      iDestruct "A1" as "[HA1 HA1c]".
      iDestruct "A2" as "[HA2 HA2c]".
      wp_load.
      wp_load.
      wp_pures.
      destruct l as [|y l].
      { inversion LEq. }
      setoid_rewrite array_cons.
      iDestruct "Bl" as "(HBx & HB1)".
      apply StronglySorted_inv in SL1 as [H1 Hl1].
      (* apply StronglySorted_inv in SL2 as [H2 Hl2]. *)
      rewrite !length_cons Nat.add_succ_l Nat.add_succ_r in LEq.
      injection LEq as LEq.
      destruct (bool_decide_reflect (x1 ≤ x2)%Z) as [Hx|Hx]; wp_pures; wp_store; wp_pures.
      + rewrite Nat2Z.inj_succ Z.sub_1_r Z.pred_succ.
        iApply ("IH" $! (a1 +ₗ 1) a2 (b +ₗ 1) l1 (x2 :: l2) l with "[] [] [] [HA1c] [HA2 HA2c] [HB1]"); try done.
        { by rewrite !length_cons Nat.add_succ_r LEq. }
        { rewrite !fmap_cons. setoid_rewrite array_cons.  iFrame. }
        iIntros "!> %l0 (HAa1 & HA2 & B1 & %Sl0 & %EqP)".
        iApply ("H2" $! (x1 :: l0)).
        rewrite !fmap_cons.
        setoid_rewrite array_cons.
        iFrame.
        iPureIntro.
        split.
        ++ apply SSorted_cons; auto.
           rewrite -EqP Forall_app Forall_cons.
           split; try split; try auto.
           apply StronglySorted_inv in SL2 as [H2 Hl2].
           eapply Forall_impl; first done.
           intros. by etrans.
        ++ by apply Permutation_skip.
      + apply Z.nle_gt, Z.lt_le_incl in Hx.
        rewrite (Nat2Z.inj_succ (length l2)) Z.sub_1_r Z.pred_succ.
        apply StronglySorted_inv in SL2 as [H2 Hl2].
        iApply ("IH" $! a1 (a2 +ₗ 1) (b +ₗ 1) (x1 :: l1) l2 l with "[] [] [] [HA1 HA1c] [HA2c] [HB1]"); try done.
        { iPureIntro. by apply SSorted_cons. }
        { rewrite fmap_cons array_cons. iFrame. }
        iClear "IH".
        iIntros "!> %l0 (HAa1 & HAa2 & B1 & %Sl0 & %EqP)".
        iApply ("H2" $! (x2 :: l0)).
        rewrite fmap_cons array_cons.
        iFrame.
        iPureIntro.
        split.
        ++ apply SSorted_cons; first done.
           rewrite -EqP.
           rewrite Forall_app Forall_cons.
           split_and!; try done.
           eapply Forall_impl; try done.
           intros. 
           etrans; try done.
        ++ by eapply (Permutation_elt _ l2 [] _ x2).
Qed.  

(**
  With this, we can prove that sort actually sorts the output.
*)
Lemma merge_sort_inner_spec (a b : loc) (l : list Z) :
  {{{
    a ↦∗ ((λ x : Z, #x) <$> l) ∗
    b ↦∗ ((λ x : Z, #x) <$> l)
  }}}
    merge_sort_inner #a #b #(length l)
  {{{(l' : list Z) vs, RET #();
    a ↦∗ ((λ x : Z, #x) <$> l') ∗
    b ↦∗ vs ∗ ⌜StronglySorted Z.le l'⌝ ∗
    ⌜l ≡ₚ l'⌝ ∗
    ⌜length vs = length l'⌝
  }}}.
Proof.
  (* exercise *)
Admitted.

(**
  Finally, we lift this result to the outer [merge_sort] function.
*)
Lemma merge_sort_spec (a : loc) (l : list Z) :
  {{{a ↦∗ ((λ x : Z, #x) <$> l)}}}
    merge_sort #a #(length l)
  {{{(l' : list Z), RET #();
    a ↦∗ ((λ x : Z, #x) <$> l') ∗
    ⌜StronglySorted Z.le l'⌝ ∗
    ⌜l ≡ₚ l'⌝
  }}}.
Proof.
  (* exercise *)
Admitted.

End proofs.
