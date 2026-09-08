(** * Extraction of the executable parts to OCaml

    Compiled separately by [make extract]; it is not part of [_CoqProject]
    so that the library build never depends on generated OCaml. The core is
    an ordinary AST and the scopes are plain lists, so the extracted code is
    first-order; the build rejects any [Obj.magic] in the output.

    Numbers stay exact [nat]: no native [int] mapping is introduced without
    range control. Addresses are natural numbers compared for equality. *)

From Stdlib Require Import Extraction ExtrOcamlBasic ExtrOcamlNativeString.
From DILLref Require Import Ty Syntax Mask OPE Infer.
From DILLref Require Import Renaming Substitution NatMap Store Examples.
From DILLref Require Import NamedSyntax Resolve.

Extraction Language OCaml.
Set Extraction Output Directory "ocaml/generated".

Extraction "dillref.ml"
  ty_eqb mask_eqb loc_free select view mask_id mask_comp ope_index mask_compl
  mask_zero mask_single mask_consume mask_meet mask_diff infer check_open check_program
  rename subst subst_l subst_u locations natmap_domain natmap_lookup natmap_replace
  find_name resolve
  source_examples source_infer_expectations
  infer_case_name run_infer_case expected_infer_case infer_edge_cases
  binding_examples store_examples location_examples resolution_examples.

(** TODO: extract [step], [runFuel] and [girard] together with their examples
    once they are defined. *)
