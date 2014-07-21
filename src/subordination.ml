(****************************************************************************)
(* Copyright (C) 2007-2009 Gacek                                            *)
(*                                                                          *)
(* This file is part of Abella.                                             *)
(*                                                                          *)
(* Abella is free software: you can redistribute it and/or modify           *)
(* it under the terms of the GNU General Public License as published by     *)
(* the Free Software Foundation, either version 3 of the License, or        *)
(* (at your option) any later version.                                      *)
(*                                                                          *)
(* Abella is distributed in the hope that it will be useful,                *)
(* but WITHOUT ANY WARRANTY; without even the implied warranty of           *)
(* MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the            *)
(* GNU General Public License for more details.                             *)
(*                                                                          *)
(* You should have received a copy of the GNU General Public License        *)
(* along with Abella.  If not, see <http://www.gnu.org/licenses/>.          *)
(****************************************************************************)

open Type
open Term
open Extensions

type sr = Tygraph.t * string list

let empty = (Tygraph.empty, [])

let close (graph, closed) ids = (graph,closed)
  (* let closed = ids @ closed in *)
  (*   List.iter *)
  (*     (fun id -> *)
  (*       try *)
  (*         let preds = (Tygraph.predecessors graph aty) in *)
  (*         let preds = List.map aty_head preds in *)
  (*         match List.minus preds closed with *)
  (*          | [] -> () *)
  (*          | xs -> failwith *)
  (*              (Printf.sprintf "Cannot close %s without closing %s" *)
  (*                 (aty_head aty) (String.concat ", " xs)) *)
  (*       with *)
  (*       | InfinitePredecessors ->  *)
          
  (*     ) *)
  (*     ids ; *)
  (*   (graph, closed) *)

let query (graph, closed) a b =
  Tygraph.is_path graph (ty_head a) (ty_head b)
  (* || not (List.mem (head b) closed) *)

let add (graph, closed) a b =
  if Tygraph.is_path graph a b then
    (graph, closed)
  else
    let vars = (get_tyvars (Ty([],a))) @ (get_tyvars (Ty([],b))) in
    (Tygraph.add_arc graph vars a b, closed)
  (* if List.mem (aty_head b) closed then *)
  (*   if Tygraph.is_path graph a b then *)
  (*     (graph, closed) *)
  (*   else *)
  (*     failwithf "Type %s is closed and cannot be subordinated by %s" b a *)
  (* else *)
  (*   (Tygraph.add_arc graph a b, closed) *)

let update sr ty =
  let rec aux sr (Ty(args, target)) =
    let sr = List.fold_left aux sr args in
      List.fold_left (fun sr ty -> add sr (ty_head ty) target) sr args
  in
    aux sr ty

let ensure (graph, _) ty =
  let rec aux (Ty(args, target)) =
    List.iter aux args;
    try
      let target_preds = Tygraph.predecessors graph target in
      match target_preds with
      | Tygraph.PredAll -> ();
      | Tygraph.PredList preds ->
        List.iter
          (fun aty ->
            if not (List.mem aty preds) then
              failwith
                (Printf.sprintf
                   "Type %s cannot be made subordinate to %s without explicit declaration"
                   (aty_head aty) (aty_head target)))
          (List.map ty_head args)
    with
    | Tygraph.InfinitePredecessors (_,_) -> 
      failwith
        (Printf.sprintf "Error: %s has infinite predecessors" (aty_head target))
  in
    aux ty

let subordinates (graph, closed) a =
  try 
    Tygraph.predecessors graph a
  with
  | Tygraph.InfinitePredecessors (_,_) ->
    failwith
     (Printf.sprintf "Error: %s has infinite predecessors" (aty_head a)) 
