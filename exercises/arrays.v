From iris.heap_lang Require Import lang proofmode notation.

(* ################################################################# *)
(** * Arrays *)

(**
  In the Linked List chapter, we saw that we could use references to
  implement a list data structure. However, HeapLang also supports
  arrays that we can use for this purpose. The expression [AllocN n v]
  allocates [n] contiguous copies of [v] and returns the location of the
  first element. We then access a specific value by calculating its
  offset [l +ₗ i] from the first element. This results in a location
  which we can load from or write to.
*)

(* ================================================================= *)
(** ** Copy *)

Section proofs.
Context `{heapGS Σ}.

(**
  To see arrays in action, let's implement a function, [copy], that
  copies an array while keeping the original intact. We define it in
  terms of a more general function, [copy_to].
*)

Definition copy_to : val :=
  rec: "copy_to" "src" "dst" "len" :=
  if: "len" = #0 then #()
  else
    "dst" <- !"src";;
    "copy_to" ("src" +ₗ #1) ("dst" +ₗ #1) ("len" - #1).

Definition copy : val :=
  λ: "src" "len",
  let: "dst" := AllocN "len" #() in
  copy_to "src" "dst" "len";;
  "dst".

(**
  Just as with [isList], arrays have a predicate we can use, written
  [l ↦∗ vs]. Here, [l] is the location of the first element in the array,
  and [vs] is the list of values currently stored at each location of
  the array.
*)

Lemma copy_to_spec a1 a2 l1 l2 :
  {{{a1 ↦∗ l1 ∗ a2 ↦∗ l2 ∗ ⌜length l1 = length l2⌝}}}
    copy_to #a1 #a2 #(length l1)
  {{{RET #(); a1 ↦∗ l1 ∗ a2 ↦∗ l1}}}.
Proof.
  iIntros "%Φ (H1 & H2 & %H) HΦ".
  (**
    We proceed by Löb induction and case distinction on the contents of
    [l1].
  *)
  iLöb as "IH" forall (a1 a2 l1 l2 H).
  destruct l1 as [|v1 l1], l2 as [|v2 l2]; try done.
  - wp_rec; wp_pures.
    (**
      The empty array predicate is trivial, as it says nothing about the
      values on the heap. So we can use [array_nil] to rewrite them into
      [emp], which in Iris is just a synonym for [True].
    *)
    rewrite !array_nil.
    iModIntro.
    by iApply "HΦ".
  - wp_rec; wp_pures.
    (**
      For the cons case, we can use [array_cons] to split the array into
      a mapsto on the first location, with the remaining array starting
      at the next location.
    *)
    rewrite !array_cons.
    iDestruct "H1" as "[H1 Hl1]".
    iDestruct "H2" as "[H2 Hl2]".
    wp_load.
    wp_store.
    wp_pures.
    rewrite Nat2Z.inj_succ Z.sub_1_r Z.pred_succ.
    wp_apply ("IH" with "[] Hl1 Hl2").
    { by injection H. }
    iIntros "[Hl1 Hl2]".
    iApply "HΦ".
    iFrame.
Qed.

(**
  When allocating arrays, HeapLang requires the size to be greater than
  zero. So we add this to our precondition.
*)
Lemma copy_spec a l :
  {{{a ↦∗ l ∗ ⌜0 < length l⌝}}}
    copy #a #(length l)
  {{{(a' : loc), RET #a'; a ↦∗ l ∗ a' ↦∗ l}}}.
Proof.
  iIntros "%Φ [Ha %H] HΦ".
  wp_lam; wp_pures.
  wp_alloc a' as "Ha'".
  { apply (Nat2Z.inj_lt 0), H. }
  rewrite Nat2Z.id.
  wp_pures.
  wp_apply (copy_to_spec with "[$Ha $Ha']").
  {
    iPureIntro.
    symmetry.
    Search length replicate.
    apply length_replicate.
  }
  iIntros "[Ha Ha']".
  wp_pures.
  iApply "HΦ".
  by iFrame.
Qed.

(* ================================================================= *)
(** ** Increment *)

(**
  As arrays can be thought of as a type of list, we can re-implement
  some of the functions we wrote for linked lists. For instance, the
  increment function.
*)
Definition inc : val :=
  rec: "inc" "arr" "len" :=
  if: "len" = #0 then #()
  else
    "arr" <- !"arr" + #1;;
    "inc" ("arr" +ₗ #1) ("len" - #1).

Lemma inc_spec a l :
  {{{a ↦∗ ((λ i : Z, #i) <$> l)}}}
    inc #a #(length l)
  {{{RET #(); a ↦∗ ((λ i : Z, #(i + 1)) <$> l)}}}.
Proof.
  iIntros "%Φ H1 HΦ".
  iInduction l as [| i l] "IH" forall (a).
  - wp_rec.
    wp_pures.
    iApply "HΦ".
    iApply "H1".
  - wp_rec.
    wp_pures.
    rewrite !fmap_cons !array_cons.
    iDestruct "H1" as "[H11 H12]".
    wp_load.
    wp_store.
    wp_pures.
    rewrite Nat2Z.inj_succ Z.sub_1_r Z.pred_succ.
    wp_apply ("IH" with "H12").
    iIntros "H2".
    iApply "HΦ".
    by iFrame.
Qed.

(* ================================================================= *)
(** ** Reverse *)

(**
  Another common list operation is reversing the list. One way of
  reversing an array is by swapping the first and last elements of the
  array, and recursively repeating this process on the remaining array.
*)
Definition reverse : val :=
  rec: "reverse" "arr" "len" :=
  if: "len" ≤ #1 then #()
  else
    let: "last" := "arr" +ₗ ("len" - #1) in
    let: "tmp" := !"arr" in
    "arr" <- !"last";;
    "last" <- "tmp";;
    "reverse" ("arr" +ₗ #1) ("len" - #2).

(**
  Notice we are not following structural induction on the list of values
  as we remove elements from both the front and the back. As such, you
  need to use either löb induction or strong induction on the size of
  the list.
*)
Lemma reverse_spec a l :
  {{{a ↦∗ l}}}
    reverse #a #(length l)
  {{{RET #(); a ↦∗ rev l}}}.
Proof.
  iIntros "%Φ H1 HΦ".
  iLöb as "IH" forall (a l).
  wp_rec.
  wp_let.
  wp_pures.
  (* Search bool_decide. *)
  destruct (bool_decide_reflect (length l ≤ 1)%Z); wp_pures.
  - iApply "HΦ".
    destruct l as [|v1 [| v2 l]]; try done.
    (* Search length cons. *)
    rewrite !length_cons in l0.
    (* About Nat2Z.inj_le. *)
    apply (Nat2Z.inj_le _ 1) in l0.
    (* Search (S _ ≤ S _). *)
    apply le_S_n in l0.
    inversion l0.
  - apply Z.nle_gt in n.
    destruct l as [|v1 l]; try done.
    rewrite array_cons. iDestruct "H1" as "[H1 H2]".
    wp_load.
    wp_pures.
    rewrite Nat2Z.inj_succ Z.sub_1_r Z.pred_succ.
    destruct l as [| vn l _] using rev_ind; try done.
    rewrite array_app.
    iDestruct "H2" as "[H21 H22]".
    (* Search "array" "singleton". *)
    rewrite array_singleton.
    (* Search length cons. *)
    rewrite last_length.
    (* Search "add" "1". *)
    rewrite <- Nat.add_1_l.
    (* Search (Z.of_nat (_ + _)). *)
    rewrite Nat2Z.inj_add.
    Search (_  +ₗ _ +ₗ _).
    rewrite <- Loc.add_assoc.
    wp_load.
    wp_store.
    wp_store.
    wp_pures.
    rewrite Z.add_1_l -!Z.add_1_r.
    rewrite -Z.add_assoc.
    (* Search (_ + ?m - ?m)%Z. *)
    rewrite Z.add_simpl_r.
    wp_apply ("IH" with "H21").
    iIntros "Hl".
    iApply "HΦ".
    (* Search "rev" "app". *)
    simpl. rewrite rev_unit.
    simpl. rewrite array_cons.
    rewrite array_app array_singleton.
    iFrame.
    (* Search "length" "rev". *)
    rewrite length_rev.
    iApply "H22".
Qed.

End proofs.
