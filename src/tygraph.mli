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

(* Functional implementation of infinite directed graphs on atomic
   types with reflexive and transitivie closure *)

(* A type graph consists of a list of arcs.  *)
(* An arc is triple of  *)
(*   1) a list of names of type variables *)
(*   2) an atomic type as the start *)
(*   3) an atomic type as the end *)
type t = (string list * aty * aty) list

(* Result of computing predecessors *)
type preds_ty = PredAll | PredList of aty list

(* An exception for when the search of predecessors *)
(* gets into an infinite loop *)
exception InfinitePredecessors of aty * aty

val empty : t
val add_arc : t -> string list -> aty -> aty -> t
val is_path : t -> aty -> aty -> bool
val predecessors : t -> aty -> preds_ty
