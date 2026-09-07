(* Driver for the extracted DILLref tool.

   Nothing here is verified: it prints terms and reports what the extracted
   functions answer. Every reported fact is also checked in theories/, so the
   two agree by construction.

   TODO: subcommands [check], [run] and [girard] with the [--affine] flag,
   once the corresponding functions are extracted. *)

open Dillref

(* Display-only conversion for the small bundled examples. This non-tail-
   recursive traversal can overflow the stack on large Peano naturals and
   assumes the result fits in an OCaml int.
   TODO: use a tail-recursive conversion with explicit range checking before
   printing arbitrary input. *)
let rec int_of_nat = function
  | O -> 0
  | S n -> 1 + int_of_nat n

let rec pp_ty = function
  | TUnit -> "unit"
  | TNat -> "nat"
  | TBool -> "bool"
  | TLolli (a, b) -> pp_ty_atom a ^ " ⊸ " ^ pp_ty b
  | TTensor (a, b) -> pp_ty_atom a ^ " ⊗ " ^ pp_ty_atom b
  | TWith (a, b) -> pp_ty_atom a ^ " & " ^ pp_ty_atom b
  | TBang a -> "!" ^ pp_ty_atom a
  | TRef a -> "ref " ^ pp_ty_atom a

and pp_ty_atom = function
  | (TUnit | TNat | TBool) as a -> pp_ty a
  | a -> "(" ^ pp_ty a ^ ")"

(* De Bruijn indices are printed as written in the core: [x0] for the
   innermost resource binder, [u0] for the innermost shared binder. *)
let rec pp = function
  | LVar i -> "x" ^ string_of_int (int_of_nat i)
  | UVar i -> "u" ^ string_of_int (int_of_nat i)
  | Loc l -> "ℓ" ^ string_of_int (int_of_nat l)
  | Lam (a, e) -> "λ:" ^ pp_ty_atom a ^ ". " ^ pp e
  | App (f, x) -> pp_fun f ^ " " ^ pp_atom x
  | Unit -> "()"
  | LetUnit (e1, e2) -> "let () = " ^ pp e1 ^ " in " ^ pp e2
  | Pair (e1, e2) -> "(" ^ pp e1 ^ ", " ^ pp e2 ^ ")"
  | LetPair (e1, e2) -> "let (x1, x0) = " ^ pp e1 ^ " in " ^ pp e2
  | With (e1, e2) -> "⟨" ^ pp e1 ^ ", " ^ pp e2 ^ "⟩"
  | Fst e -> "fst " ^ pp_atom e
  | Snd e -> "snd " ^ pp_atom e
  | Bang e -> "!" ^ pp_atom e
  | LetBang (e1, e2) -> "let !u0 = " ^ pp e1 ^ " in " ^ pp e2
  | Nat n -> string_of_int (int_of_nat n)
  | Succ e -> "succ " ^ pp_atom e
  | Iter (count, step, seed) ->
      "iter " ^ pp_atom count ^ " " ^ pp_atom step ^ " " ^ pp_atom seed
  | Bool b -> string_of_bool b
  | If (c, e1, e2) ->
      "if " ^ pp c ^ " then " ^ pp e1 ^ " else " ^ pp e2
  | New e -> "new " ^ pp_atom e
  | Swap (e1, e2) -> "swap " ^ pp_atom e1 ^ " " ^ pp_atom e2
  | Free e -> "free " ^ pp_atom e

and pp_fun = function
  | App _ as t -> pp t
  | t -> pp_atom t

and pp_atom = function
  | (LVar _ | UVar _ | Loc _ | Unit | Pair _ | With _ | Nat _ | Bool _) as t ->
      pp t
  | t -> "(" ^ pp t ^ ")"

let () =
  let failures = ref 0 in
  List.iter
    (fun (name, e) ->
      let ok = loc_free e in
      Printf.printf "%-20s %s\n" name (pp e);
      if not ok then begin
        Printf.eprintf "%s: source term contains a store address\n" name;
        incr failures
      end)
    source_examples;
  List.iter
    (fun (name, (actual, expected)) ->
      if actual <> expected then begin
        Printf.eprintf "%s: got %s, expected %s\n" name (pp actual) (pp expected);
        incr failures
      end)
    binding_examples;
  List.iter
    (fun (name, (actual, expected)) ->
      if actual <> expected then begin
        let describe = function
          | Some e -> pp e
          | None -> "unbound name"
        in
        Printf.eprintf "%s: resolved to %s, expected %s\n"
          name (describe actual) (describe expected);
        incr failures
      end)
    resolution_examples;
  List.iter
    (fun (name, (actual, expected)) ->
      if actual <> expected then begin
        Printf.eprintf "%s: store update differs from the expected store\n" name;
        incr failures
      end)
    store_examples;
  List.iter
    (fun (name, (actual, expected)) ->
      if actual <> expected then begin
        Printf.eprintf "%s: address occurrences differ from the expected list\n" name;
        incr failures
      end)
    location_examples;
  if not (ty_eqb (TLolli (TNat, TNat)) (TLolli (TNat, TNat)))
     || ty_eqb (TTensor (TNat, TNat)) (TWith (TNat, TNat))
  then begin
    prerr_endline "ty_eqb disagrees with syntactic equality";
    incr failures
  end;
  Printf.printf "Source examples: %d checked\n" (List.length source_examples);
  Printf.printf "Binding examples: %d checked\n" (List.length binding_examples);
  Printf.printf "Name resolution: %d checked\n" (List.length resolution_examples);
  Printf.printf "Store updates: %d checked\n" (List.length store_examples);
  Printf.printf "Address traversals: %d checked\n" (List.length location_examples);
  if !failures > 0 then exit 1
