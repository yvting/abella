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

type aty =
  | Tyvar of string
  | Tycon of string

val arep : aty -> string

type ty = Ty of ty list * aty

val tyarrow : ty list -> ty -> ty
val tyvar   : string -> ty
val tybase  : string -> ty

val oty     : ty
val olistty : ty

val is_tyvar : aty -> bool

val fresh_tyvar : unit -> ty

val to_string : ty -> string