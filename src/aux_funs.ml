open Term

let clause_to_string (head, body) =
  (Term.term_to_string head) ^ " :- " ^
  (String.concat " " (List.map Term.term_to_string body))

let list_clauses () = List.map clause_to_string (!Prover.clauses)

let rec get_clause clauses = function
  | 1 -> List.hd clauses
  | n -> get_clause (List.tl clauses) (n-1)

let rip_app t =
  match observe t with
  | App (h, args) -> (h, args)
  | _ -> failwith "Not an App"

let rip_lam t =
  match observe t with
  | Lam (_, bd) -> bd
  | _ -> failwith "Not a Lam"
