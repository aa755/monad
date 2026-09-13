From iris.proofmode Require Import proofmode.
Require Import skylabs.auto.cpp.proof.

Ltac use_go_instead tac :=
  fail 100 tac
    "is disabled here. Use `go.` or `go using hint1, hint2.` instead."
    "If automation is missing a structural step, add a local rewrite/fwd/bwd hint."
    "Read fmdeps/fmai/skills/rocqcpp/references/proof/sepproofs.v and cpp.v.".

Ltac use_fwd_hint_instead tac :=
  fail 100 tac
    "is disabled here. Define a local FWD hint instead, then use `go.` or `go using hint1, hint2.`."
    "Do not introduce named facts manually with this tactic."
    "Read fmdeps/fmai/skills/rocqcpp/references/proof/sepproofs.v and cpp.v as usual.".

Ltac explain_go_failure :=
  lazymatch goal with
  | |- _ -|- _ =>
      fail 100
        "`go` ignores `-|-` goals."
        "use iSplit tosplit the equivalence into two `|--` goals first, then use `go` on each direction."
        "Read skills/rocqcpp/references/proof/sepproofs.v and cpp.v."
  | |- _ |-- _ => idtac
  | |- environments.envs_entails _ => idtac
  | _ =>
      fail 100
           "go only works on separation logic entailment goals, of shape _ |-- _ or environments.envs_entails _ _"
  end.

Tactic Notation "upstream_go" sl_modifier_list(ms) := go ${ms}.

Tactic Notation "go" sl_modifier_list(ms) :=
  tryif
    upstream_go ${ms}
  then idtac
  else explain_go_failure.

Tactic Notation "iIntros" := use_go_instead "iIntros".
Tactic Notation "iIntros" constr(pat) := use_go_instead "iIntros".
Tactic Notation "iIntros" "(" ne_simple_intropattern_list(xs) ")" :=
  use_go_instead "iIntros".
Tactic Notation "iIntros" "(" ne_simple_intropattern_list(xs) ")" constr(pat) :=
  use_go_instead "iIntros".
Tactic Notation "iIntros" constr(pat) "(" ne_simple_intropattern_list(xs) ")" :=
  use_go_instead "iIntros".
Tactic Notation "iIntros" constr(pat1) "(" ne_simple_intropattern_list(xs) ")" constr(pat2) :=
  use_go_instead "iIntros".

Tactic Notation "iDestruct" open_constr(lem) "as" constr(pat) :=
  use_go_instead "iDestruct".
Tactic Notation "iDestruct" open_constr(lem) "as"
    "(" ne_simple_intropattern_list(xs) ")" constr(pat) :=
  use_go_instead "iDestruct".
Tactic Notation "iDestruct" open_constr(lem) "as" "%" simple_intropattern(pat) :=
  use_go_instead "iDestruct".
Tactic Notation "iDestruct" "select" open_constr(sel) "as" constr(ipat) :=
  use_go_instead "iDestruct".
Tactic Notation "iDestruct" "select" open_constr(sel) "as"
    "(" ne_simple_intropattern_list(xs) ")" constr(ipat) :=
  use_go_instead "iDestruct".
Tactic Notation "iDestruct" "select" open_constr(sel) "as" "%"
    simple_intropattern(ipat) :=
  use_go_instead "iDestruct".

Tactic Notation "iSplitL" := use_go_instead "iSplitL".
Tactic Notation "iSplitR" := use_go_instead "iSplitR".
Tactic Notation "iSplitL" constr(Hs) := use_go_instead "iSplitL".
Tactic Notation "iSplitR" constr(Hs) := use_go_instead "iSplitR".

Tactic Notation "iApply" open_constr(lem) := use_go_instead "iApply".

Tactic Notation "iAssert" open_constr(P) "as" constr(pat) :=
  use_fwd_hint_instead "iAssert".
Tactic Notation "iAssert" open_constr(P) "as" "%" simple_intropattern(pat) :=
  use_fwd_hint_instead "iAssert".
Tactic Notation "iAssert" open_constr(P) "with" constr(sel) "as" constr(pat) :=
  use_fwd_hint_instead "iAssert".
Tactic Notation "iAssert" open_constr(P) "with" constr(sel) "as" "%"
    simple_intropattern(pat) :=
  use_fwd_hint_instead "iAssert".

Tactic Notation "iPoseProof" open_constr(lem) "as" constr(pat) :=
  use_fwd_hint_instead "iPoseProof".
Tactic Notation "iPoseProof" open_constr(lem) "as" "%"
    simple_intropattern(pat) :=
  use_fwd_hint_instead "iPoseProof".

Goal True.
  Fail iIntros.
  Fail iIntros "H".
  Fail iDestruct "H" as "H'".
  Fail iSplitL.
  Fail iSplitR.
  Fail iSplitL "H".
  Fail iSplitR "H".
  Fail iApply I.
  Fail iAssert True%I as "H".
  Fail iPoseProof I as "H".
Abort.

From Ltac2 Require Import Init Char Constr Control Int Ltac1 Message Option String.

Tactic Notation "upstream_wapply" open_constr(lem) := wapply lem.

Ltac2 rec string_contains_at (needle : string) (haystack : string)
    (i : int) (j : int) : bool :=
  if Int.equal j (String.length needle) then true
  else if Int.le (String.length haystack) (Int.add i j) then false
  else if Char.equal (String.get needle j) (String.get haystack (Int.add i j)) then
    string_contains_at needle haystack i (Int.add j 1)
  else false.

Ltac2 rec string_contains_from (needle : string) (haystack : string)
    (i : int) : bool :=
  if Int.le (String.length haystack) i then String.is_empty needle
  else if string_contains_at needle haystack i 0 then true
  else string_contains_from needle haystack (Int.add i 1).

Ltac2 string_contains (needle : string) (haystack : string) : bool :=
  string_contains_from needle haystack 0.

Ltac2 fold_occurrence_is_unfold (haystack : string) (i : int) : bool :=
  if Int.le 2 i then
    let start := Int.sub i 2 in
    if string_contains_at "unfold" haystack start 0 then true
    else string_contains_at "Unfold" haystack start 0
  else false.

Ltac2 rec string_contains_fold_not_unfold_from (haystack : string)
    (i : int) : bool :=
  if Int.le (String.length haystack) i then false
  else if string_contains_at "fold" haystack i 0 then
    if fold_occurrence_is_unfold haystack i then
      string_contains_fold_not_unfold_from haystack (Int.add i 4)
    else true
  else string_contains_fold_not_unfold_from haystack (Int.add i 1).

Ltac2 string_contains_fold_not_unfold (haystack : string) : bool :=
  string_contains_fold_not_unfold_from haystack 0.

Ltac2 rec constr_head (c : constr) : constr :=
  match Constr.Unsafe.kind c with
  | Constr.Unsafe.App f _ => constr_head f
  | Constr.Unsafe.Cast c _ _ => constr_head c
  | _ => c
  end.

Ltac2 fail_if_wapply_fold_head (lem : constr) : unit :=
  let head := constr_head lem in
  let head_name := Message.to_string (Message.of_constr head) in
  if string_contains_fold_not_unfold head_name then
    Control.throw
      (Tactic_failure
         (Some
            (Message.of_string
               (String.app
                  "wapply is disabled for lemmas whose applied head contains `fold` outside `unfold`/`Unfold`: "
                  head_name))))
  else ().

Tactic Notation "wapply" open_constr(lem) :=
  let run_guard :=
    ltac2:(lem |-
      let lem := Option.get (Ltac1.to_constr lem) in
      fail_if_wapply_fold_head lem) in
  run_guard lem;
  upstream_wapply lem.
