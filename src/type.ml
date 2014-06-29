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
