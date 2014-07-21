(****************************************************************************)
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

type id = string
(* Kind *)
type kd = string * int

(* Type *)
type tvmode = Var | Const

type ty = Ty of ty list * aty
and aty =
| Tyvar of string * tvmode
| Tycon of string * ty list

let ty_head = function
  | Ty(_,aty) -> aty

let aty_head = function
  | Tyvar (id,_) -> id
  | Tycon (id,_) -> id

let tyarrow tys ty =
  match ty with
    | Ty(tys', bty) -> Ty(tys @ tys', bty)

let tybase bty =
  Ty([], Tycon(bty, []))

let oty = tybase "o"
let olistty = Ty([], Tycon("list", [oty]))
let propty = tybase "prop"

let is_tyvar str =
  str.[0] = '?'

let tyvar str mode =
  Ty([], Tyvar(str, mode))

let fresh_tyvar =
  let count = ref 0 in
    fun () ->
      incr count ;
      tyvar ("?" ^ string_of_int !count) Var

type tyctx = (id * ty) list

let rec ty_to_list = function
  | Ty(tys,aty) ->
    let lst =
      match aty with
      | Tyvar(_,_) -> [aty]
      | Tycon(name,tys') -> aty::(List.flatten_map ty_to_list tys') in
    (List.flatten_map ty_to_list tys) @ lst

let is_abbrev_ty id tys =
  id = "olist" && tys = []

let expand_abbrev_ty id tys =
  if id = "olist" && tys = [] then
    olistty
  else
    failwith ("Not a abbreviated type: " ^ id)


exception TypeMismatch of ty * ty

let match_ty tyb ty =
  let rec aux eqns tyb ty =
    match tyb, ty with
    | Ty([], Tyvar(idb,_)), _ ->
      (try
         let tyv = List.assoc idb eqns in
         if tyv = ty then
           eqns
         else
           raise (TypeMismatch (ty,tyv))
       with
       | Not_found -> (idb, ty)::eqns)
    | Ty([], Tycon(idb,tysb)), Ty([], Tycon(id,tys)) ->
      if idb <> id || List.length tysb <> List.length tys then
        raise (TypeMismatch(tyb,ty))
      else
        List.fold_left2
          (fun eqns tyb ty -> aux eqns tyb ty)
          eqns tysb tys
    | Ty(tyb::tysb, atyb), Ty(ty::tys, aty) ->
      let eqns = aux eqns tyb ty in
      aux eqns (Ty(tysb,atyb)) (Ty(tys,aty))
    | _, _ -> raise (TypeMismatch(tyb,ty))
  in
  aux [] tyb ty

let match_aty atyb aty = 
  match_ty (Ty([],atyb)) (Ty([],aty))

(** Ultility functions *)
let iter_ty f ty =
  List.iter f (ty_to_list ty)
let fold_ty f s ty =
  List.fold_left f s (ty_to_list ty)

let get_tyvars ty =
  fold_ty 
    (fun ids aty ->
      match aty with
      | Tyvar(name,_) -> 
        if List.mem name ids then ids else name::ids
      | Tycon(name,tys) ->
        ids)
    [] ty

(** Type substitutions *)
exception InstantiateConstTyvar of string

type tysub = (string * ty) list

let rec apply_bind_ty v ty = function
  | Ty(tys, aty) ->
    let ty' = 
      match aty with
      | Tyvar(name,Var) ->
        if v = name then ty else Ty([],aty)
      | Tyvar(name,Const) ->
        if v = name then 
          raise (InstantiateConstTyvar(name))
        else
          Ty([],aty)
      | Tycon(name, tys) ->
        Ty([], Tycon(name, List.map (apply_bind_ty v ty) tys)) in
    tyarrow (List.map (apply_bind_ty v ty) tys) ty'

let apply_sub_ty s ty =
  List.fold_left (fun ty (v,vty) -> apply_bind_ty v vty ty) ty s

let apply_sub_aty s aty =
  match (apply_sub_ty s (Ty([],aty))) with
  | Ty([],aty') -> aty'
  | _ -> failwith "Impossible case in: apply_sub_aty"

let apply_sub_tyctx s tyctx =
  List.map (fun (id, ty) -> (id, apply_sub_ty s ty)) tyctx

(* let ty_eq ty1 ty2 = *)
(*   try *)
(*     let eqns = match_ty ty1 ty2 in *)
(*     let vars =  *)
(*       List.map  *)
(*         (fun (id,ty) ->  *)
(*           match ty with *)
(*           | Ty([], Tyvar(id',_)) -> id' *)
(*           | _ -> raise Not_found) *)
(*         eqns in *)
(*     let uniq_var var vars =  *)
(*       List.length (List.filter (fun x -> (=) x var) vars) = 1 in *)
(*     List.for_all *)
(*       (fun v -> uniq_var v vars) *)
(*       vars *)
(*   with *)
(*   | Not_found -> false *)
(*   | TypeMismatch(_,_) -> false *)
        
      
      
