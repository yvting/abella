(****************************************************************************)
(* An implemention of Higher-Order Pattern Unification                      *)
(* Copyright (C) 2006-2009 Nadathur, Linnell, Baelde, Ziegler, Gacek        *)
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

(* Types *)

type id = Namespace.id
type ty = Ty of ty list * id

val tyarrow : ty list -> ty -> ty
val tybase : id -> ty
val oty : ty
val olistty : ty

(* Variables *)

type tag = Eigen | Constant | Logic | Nominal
type var = private {
  name : id ;
  tag  : tag ;
  ts   : int ;
  ty   : ty ;
}

(* Terms. The use of references allow in-place normalization,
 * but is completely hidden by the interface. *)

type term
type ptr
type envitem = Dum of int | Binding of term * int
type env = envitem list

type rawterm =
  | Var of var
  | DB of int
  | Lam of ty list * term
  | App of term * term list
  | Susp of term * int * int * env
  | Ptr of ptr (* Sorry about this one, hiding it is costly.. *)

(* [observe t] is the way to analyze the structure of a term. *)
val observe : term -> rawterm

(** Creation of terms.
  * There is probably more to come here. *)

val var : tag -> id -> int -> ty -> term

val app : term -> term list -> term
val susp : term -> int -> int -> env -> term
val db : int -> term

module Notations :
sig
  val (//) : ty list -> term -> term
  val (^^) : term -> term list -> term
end


val eq : term -> term -> bool

(* Binding a variable to a term. The *contents* of the cell representing the
 * variable is a reference which must be updated. Also the variable must
 * not be made a reference to itself. *)

val bind : term -> term -> unit

type bind_state
val get_bind_state : unit -> bind_state
val set_bind_state : bind_state -> unit

(* Scoped bind state is more efficient than regular bind state, but it
   must always be used in a lexically scoped fashion. The unwind_state
   wraps a function with a scoped get and set. *)

type scoped_bind_state
val get_scoped_bind_state : unit -> scoped_bind_state
val set_scoped_bind_state : scoped_bind_state -> unit

val unwind_state : ('a -> 'b) -> ('a -> 'b)

(* Raise the substitution *)
val add_dummies : env -> int -> int -> env

(* Add abstractions. *)
val lambda : ty list -> term -> term

(** Abstract [t] over constant or variable named [id]. *)
val abstract : id -> ty -> term -> term

(** Abella specific additions and changes *)
val const : ?ts:int -> id -> ty -> term
val fresh : ?tag:tag -> int -> ty -> term
val fresh_wrt : ts:int -> tag -> id -> ty ->
                  (id * term) list -> term * (id * term) list

val nominal_var : id -> ty -> term

val find_vars : tag -> term list -> var list
val find_var_refs : tag -> term list -> term list
val map_vars : (var -> 'a) -> term list -> 'a list

val term_to_var : term -> var
val term_to_name : term -> id
val term_to_pair : term -> id * term

val has_logic_head : term -> bool
val has_eigen_head : term -> bool

val hnorm : term -> term

val ty_to_string : ty -> string
val term_to_string : term -> string
val prefix : tag -> string

val get_used : term list -> (id * term) list
val is_free : term -> bool

val is_nominal_name : id -> bool
val is_nominal : term -> bool
val fresh_name : id -> (id * 'a) list -> id
val term_head_var : term -> term option
val is_head_name : id -> term -> bool
val term_head_name : term -> id

val is_capital_name : id -> bool
val capital_tids : term list -> (id * ty) list
val question_tids : term list -> (id * ty) list
val nominal_tids : term list -> (id * ty) list
val all_tids : term list -> (id * ty) list

val tc : ty list -> term -> ty

val tyvar : id -> ty
val is_tyvar : id -> bool
val fresh_tyvar : unit -> ty
