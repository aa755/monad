Set Default Goal Selector "!".

(** The low/high 64-bit scan used by the production storage-page iterator.
    The scalar argument's uint128 bound is supplied by the C++ calling
    convention; no page-specific assumption is needed. *)

Require Import monad.proofs.execproofs.mip8.storage_page_cpp_proofs.common.
Require Import monad.proofs.execproofs.mip8.storage_page_cpp_proofs.compute_nonempty_subtree_root.
Require Import monad.proofs.execproofs.mip8.storage_page_cpp_proofs.storage_page_pair_bitmap.
Require Import monad.proofs.disableIPMtacs_use_go_instead.
Import linearity.
#[local] Hint Resolve UNSAFE_read_prim_cancel : sl_opacity.
Remove Hints _at_pick_cfrac_and_split_C _at_pick_frac_and_split_C
  _at_split_specific_cfrac_C _at_split_specific_frac_C : db_skylabs_syntactic.

Opaque countr_zero64 countr_zero_fuel.
#[local] Hint Opaque lowest_offset_model countr_zero64 countr_zero_fuel
  : sl_opacity typeclass_instances.
#[local] Hint Resolve countr_zero64_int_bound : pure typeclass_instances.

Section with_Sigma.
  Context `{Sigma : cpp_logic} {CU : genv}.
  Context {MODd : storage_page_cpp.source ⊧ CU}.

  Lemma prf_lowest_offset : verify[source] lowest_offset_spec.
  Proof using MODd.
    verify_spec'.
    name_locals.
    go.
    destruct (asbool (trim 64 (Z.of_N bitmap) <> 0)) eqn:Hlo.
    { go.
      Transparent lowest_offset_model.
      unfold lowest_offset_model.
      rewrite N.land_ones.
      rewrite trim64_of_N in Hlo.
      rewrite trim64_of_N N2Z.id.
      rewrite (proj2 (N.eqb_neq (bitmap mod 2 ^ 64) 0) ltac:(lia)).
      pose proof (countr_zero_fuel_le 64 (bitmap mod 2 ^ 64)%N) as Hbound.
      Transparent countr_zero64.
      change (Z.of_N (countr_zero64 (bitmap mod 2 ^ 64)) <= 64 + Z.of_N (N.of_nat 64))%Z in Hbound.
      Opaque countr_zero64 lowest_offset_model.
      go.
    }
    { pose proof (countr_zero_fuel_le 64
          (Z.to_N (trim 64 (Z.shiftr (Z.of_N bitmap) 64)))) as Hbound.
      Transparent countr_zero64.
      change (Z.of_N (countr_zero64
          (Z.to_N (trim 64 (Z.shiftr (Z.of_N bitmap) 64)))) <=
          64 + Z.of_N (N.of_nat 64))%Z in Hbound.
      Opaque countr_zero64.
      (* Normalize the cast before invoking the N-valued bit-scan spec, as
         in [prf_storage_page_pair_bitmap]'s high-half call. *)
      do 15 run1.
      pose proof _x_0 as Hbitmap.
      apply type.has_int_type_RL in Hbitmap.
      rewrite /bitsize.bound /= in Hbitmap.
      assert (HbitmapN : (bitmap < 2 ^ 128)%N) by lia.
      rewrite (trim64_shiftr64_of_N bitmap HbitmapN).
      rewrite (trim64_shiftr64_of_N bitmap HbitmapN) N2Z.id in Hbound.
      go.
      Transparent lowest_offset_model.
      unfold lowest_offset_model.
      rewrite N.land_ones.
      rewrite trim64_of_N in Hlo.
      rewrite (proj2 (N.eqb_eq (bitmap mod 2 ^ 64) 0) ltac:(lia)).
      rewrite N2Z.inj_add.
      go.
    }
  Qed.
  Opaque lowest_offset_model.

End with_Sigma.
