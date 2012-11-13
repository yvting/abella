type namespace = 
  | TopNs
  | Namespace of string * namespace
type id = Id of string * namespace

let id_eq (Id (n1,ns1)) (Id (n2,ns2)) = (n1 = n2) && (ns1 = ns2)

let id_to_str (Id (id,_)) = id
let id_to_ns (Id (_,ns)) = ns

let spec_ns = Namespace ("spec", TopNs)
let reas_ns = Namespace ("reas", spec_ns)

let spec_id str = Id (str, spec_ns)
let reas_id str = Id (str, reas_ns)

let o_id = spec_id "o"
let olist_id = spec_id "olist"
let imp_id = spec_id "=>"
let pi_id = spec_id "pi"
let sigma_id = spec_id "sigma"

let cons_id = reas_id "::"
let nil_id = reas_id "nil"
let prop_id = reas_id "prop"
let member_id = reas_id "member"
let placeholder_id = reas_id "placeholder"
