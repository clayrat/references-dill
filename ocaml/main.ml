(* Driver for the extracted DILLref tool.

   Nothing here is verified: it prints terms and reports what the extracted
   functions answer. Every reported fact is also checked in theories/, so the
   two agree by construction.

   Without arguments the driver runs the bundled regression checks. The
   [check] subcommand accepts or rejects bundled closed programs with the
   extracted [check_program] and prints the synthesized type. No expected
   type is given on the command line: binders are annotated, so the type of
   a program is determined by the program alone (see Infer.v). [list] prints
   the catalog.

   TODO: [run] and [girard] once their corresponding functions are
   extracted; a text parser so that [check] accepts programs from files. *)

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

let pp_mask bits =
  "[" ^ String.concat "; " (List.map string_of_bool bits) ^ "]"

let pp_infer_result = function
  | None -> "rejected"
  | Some (a, leftovers) -> pp_ty a ^ " with " ^ pp_mask leftovers

let flag_name = function
  | Linear -> "linear"
  | Affine -> "affine"

let regression () =
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
  if List.length source_examples <> List.length source_infer_expectations then begin
    Printf.eprintf "source inference table has %d entries for %d programs\n"
      (List.length source_infer_expectations) (List.length source_examples);
    incr failures
  end else
    List.iter2
      (fun (name, e) (expected_name, (expected_linear, expected_affine)) ->
        if name <> expected_name then begin
          Printf.eprintf "source inference table has %s where %s was expected\n"
            expected_name name;
          incr failures
        end;
        List.iter
          (fun (mode, expected) ->
            let actual = infer mode [] [] [] e in
            if actual <> expected then begin
              Printf.eprintf "%s (%s): got %s, expected %s\n"
                name (flag_name mode) (pp_infer_result actual)
                (pp_infer_result expected);
              incr failures
            end)
          [ (Linear, expected_linear); (Affine, expected_affine) ])
      source_examples source_infer_expectations;
  List.iter
    (fun case ->
      let name = infer_case_name case in
      let actual = run_infer_case case in
      let expected = expected_infer_case case in
      if actual <> expected then begin
        Printf.eprintf "%s: got %s, expected %s\n"
          name (pp_infer_result actual) (pp_infer_result expected);
        incr failures
      end)
    infer_edge_cases;
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
  Printf.printf "Source type checks: %d checked in both modes\n"
    (List.length source_examples);
  Printf.printf "Checker edge cases: %d checked\n"
    (List.length infer_edge_cases);
  Printf.printf "Binding examples: %d checked\n" (List.length binding_examples);
  Printf.printf "Name resolution: %d checked\n" (List.length resolution_examples);
  Printf.printf "Store updates: %d checked\n" (List.length store_examples);
  Printf.printf "Address traversals: %d checked\n" (List.length location_examples);
  if !failures > 0 then exit 1

let usage () =
  prerr_endline "usage: dillref                          run the bundled regression checks";
  prerr_endline "       dillref list                     list the bundled programs";
  prerr_endline "       dillref check [--affine] NAME... type-check bundled programs";
  exit 2

(* A rejected program is reported on stdout and makes the exit code nonzero,
   like a compiler; an unknown name is an error. *)
let check_command args =
  let mode = if List.mem "--affine" args then Affine else Linear in
  let names = List.filter (fun a -> a <> "--affine") args in
  if names = [] then usage ();
  let failures = ref 0 in
  List.iter
    (fun name ->
      match List.assoc_opt name source_examples with
      | None ->
          Printf.eprintf "%s: unknown program\n" name;
          incr failures
      | Some e ->
          Printf.printf "%s (%s): " name (flag_name mode);
          (match check_program mode e with
           | Some a -> print_endline (pp_ty a)
           | None -> print_endline "rejected"; incr failures))
    names;
  if !failures > 0 then exit 1

let () =
  match Array.to_list Sys.argv with
  | [] | [_] -> regression ()
  | _ :: "list" :: _ ->
      List.iter (fun (name, e) -> Printf.printf "%-20s %s\n" name (pp e))
        source_examples
  | _ :: "check" :: args -> check_command args
  | _ -> usage ()
