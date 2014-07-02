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

type id = string

(* Kinds *)
type kd = id * int

(* Types *)
type tvmode = Var | Const

type ty = Ty of ty list * aty
and aty = 
| Tyvar of string * tvmode
| Tycon of string * ty list

val aty_head : aty -> string

val tyarrow : ty list -> ty -> ty
val tybase : string -> ty
val oty : ty
val olistty : ty
val propty : ty

val tyvar : string -> tvmode -> ty
val is_tyvar : string -> bool
val fresh_tyvar : unit -> ty

type tyctx = (id * ty) list

val ty_to_list : ty -> aty list

(* Expanding abbreviated types *)
val is_abbrev_ty : id -> ty list -> bool
val expand_abbrev_ty : id -> ty list -> ty

(* Match types *)
exception TypeMismatch of ty * ty
val match_ty : ty -> ty -> (id * ty) list
val match_aty : aty -> aty -> (id * ty) list

(** Type substitutions *)
exception InstantiateConstTyvar of string
type tysub = (string * ty) list

(* Utility functions *)
val iter_ty : (aty -> unit) -> ty -> unit
val fold_ty : ('a -> aty -> 'a) -> 'a -> ty -> 'a

val get_tyvars : ty -> string list
val apply_bind_ty : id -> ty -> ty -> ty
val apply_sub_ty : (id * ty) list -> ty -> ty
val apply_sub_aty : (id * ty) list -> aty -> aty
val apply_sub_tyctx : (id * ty) list -> (id * ty) list -> (id * ty) list
