type namespace = 
  | IrrevNs
  | TopNs
  | Namespace of string * namespace
type id = Id of string * namespace

let id_eq (Id (n1,ns1)) (Id (n2,ns2)) = (n1 = n2) && (ns1 = ns2)

let id_to_str (Id (id,_)) = id
let id_to_ns (Id (_,ns)) = ns

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
