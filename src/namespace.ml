type namespace = 
  | IrrevNs
  | TopNs
  | Namespace of string * namespace
type id = Id of string * namespace

type parse_ns =
  | PsSpecNs
  | PsReasNs
  | PsInvNs



let id_to_str (Id (id,_)) = id
let id_to_ns (Id (_,ns)) = ns
let ids_to_str ids = String.concat "," (List.map id_to_str ids)

let spec_ty_ns = Namespace ("specty", TopNs)
let reas_ty_ns = Namespace ("reasty", spec_ty_ns)
let spec_cn_ns = Namespace ("speccn", TopNs)
let reas_cn_ns = Namespace ("reascn", spec_cn_ns)

let irrev_id str = Id(str, IrrevNs)
let spec_ty_id str = Id (str, spec_ty_ns)
let reas_ty_id str = Id (str, reas_ty_ns)
let spec_cn_id str = Id (str, spec_cn_ns)
let reas_cn_id str = Id (str, reas_cn_ns)

let o_id = spec_ty_id "o"
let imp_id = spec_cn_id "=>"
let pi_id = spec_cn_id "pi"
let sigma_id = spec_cn_id "sigma"

let olist_id = reas_ty_id "olist"
let cons_id = reas_cn_id "::"
let nil_id = reas_cn_id "nil"
let prop_id = reas_ty_id "prop"
let member_id = reas_cn_id "member"
let placeholder_id = reas_cn_id "placeholder"

let get_start_ns = function
  | PsReasNs, true -> reas_ty_ns
  | PsReasNs, false -> reas_cn_ns
  | PsSpecNs, true -> spec_ty_ns
  | PsSpecNs, false -> spec_cn_ns
  | _ -> assert false

(* lookup constant *)
let lookup_const (Id (name,_)) pns ids =
  let cands = List.filter (fun (Id (str,_)) -> str = name) ids in
  let ns = get_start_ns (pns,false) in 
  let rec find_cn = function 
    | IrrevNs -> raise Not_found
    | TopNs -> raise Not_found
    | Namespace (_,par_ns) as ns ->
        try
          List.find (fun (Id (_,cns)) -> cns = ns) cands
        with Not_found ->
          find_cn par_ns
  in
  find_cn ns
