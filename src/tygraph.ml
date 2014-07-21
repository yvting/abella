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

open Extensions
open Type

type t = (string list * aty * aty) list
type preds_ty = PredAll | PredList of aty list
exception InfinitePredecessors of aty * aty

let empty = []

(* an arc is valid if and only if
   1. type variables in tyr are the same as in vars
   2. type variables in tya is a subset of vars
*)
let valid_arc vars tya tyr =
  let rvars = get_tyvars (Ty([],tyr)) in
  let avars = get_tyvars (Ty([],tya)) in
     List.minus avars rvars = [] 
  && List.minus rvars vars = []
  && List.minus vars rvars = []

let add_arc arcs vars tya tyr =
  if not (valid_arc vars tya tyr) then
    failwith "Internal Error: adding an invalid arc to the type graph";
  if List.mem (vars, tya, tyr) arcs then 
    arcs 
  else 
    (vars, tya, tyr) :: arcs

let arc_pred ty (vars, tya, tyr) =
  try
    let eqns = match_aty tyr ty in
    Some (apply_sub_aty eqns tya)
  with
    TypeMismatch(_,_) -> None
    
let direct_predecessors arcs ty =
  match ty with
  | Tyvar(_,_) -> failwith "direct_predecessors: impossible case"
  | Tycon(_,_) -> List.filter_map (arc_pred ty) arcs

let predecessors arcs ty =
  let rec aux pstack accum_preds ty =
    match ty with
    | Tyvar(_,_) -> PredAll
    | Tycon(_,_) ->
    (* Check if ty is a proper instantiation of some type 
       on the DFS stack. If so, the computation of predcessors
       will go into an infinite loop. *)
      List.iter
        (fun pty -> 
          try let eqns = match_aty pty ty in
              List.iter 
                (fun (id,uty) ->
                  match uty with
                  | Ty([], Tyvar(_,_)) -> ()
                  | _ -> raise (InfinitePredecessors(ty,pty)))
                eqns
          with
          | TypeMismatch(_,_) -> ())
        pstack;

      match accum_preds with
      | PredAll -> PredAll
      | PredList acc ->
        if List.mem ty acc then
          accum_preds
        else
          let acc_pred accum_preds pty =
            match accum_preds with
            | PredAll -> PredAll
            | PredList acc -> aux (ty::pstack) accum_preds pty 
          in
          List.fold_left acc_pred (PredList (ty::acc))
            (direct_predecessors arcs ty)
  in
  aux [] (PredList []) ty
  
let is_path arcs a b =
  try
    let preds = predecessors arcs b in
    match preds with
    | PredAll -> true
    | PredList acc -> List.mem a acc
  with
  | InfinitePredecessors (_,_) -> false
