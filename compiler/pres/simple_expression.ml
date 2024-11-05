open Zelus

let node_names = (Hashtbl.create 42 : (string , int) Hashtbl.t)


let simple_op op = 
	match op with
	| Eifthenelse -> !Zmisc.do_viz_text_if
	| _ -> true


let rec simple_exp e =
	match e.e_desc with
	| Elocal _ | Eglobal _ | Econst _ | Econstr0 _ -> true
	| Econstr1 (_, el) -> List.for_all simple_exp el
	| Elast _ -> true
	| Etuple el -> List.for_all simple_exp el
	| Erecord_access (e,_) -> simple_exp e
	| Erecord lel -> let _,el = List.split lel in List.for_all simple_exp el
	| Erecord_with (e , lel) -> 
		simple_exp e && (let _,el = List.split lel in List.for_all simple_exp el)
	| Etypeconstraint (e,_) -> simple_exp e
	| Epresent _ -> false
	| Ematch  _ -> false
	| Elet _ -> false 
  	| Eop (op , el) -> (simple_op op) && List.for_all simple_exp el
	| Eperiod pe -> simple_exp pe.p_period && (match pe.p_phase with | None -> true | Some e -> simple_exp e)
  	| Eblock _ -> false
	| Eseq _ -> false (*done recursively after *)
	| Eapp (_,fct,el) ->
		let fct_simple = match fct.e_desc with
		| Eglobal lid -> 
			not (Hashtbl.mem node_names (begin match lid.lname with	
			| Name n -> n
			| Modname l -> l.id
			end))
		| _ -> simple_exp fct 
		in
		List.for_all simple_exp el && fct_simple 

let rec too_simple e = match e.e_desc with 
	| Elocal _ -> true
	| Eglobal _ | Econst _ | Econstr0 _ -> true
	| Etuple el -> List.for_all too_simple el
	| _ -> false

let rec still_const e = match e.e_desc with
	| Eglobal _ | Econst _ | Econstr0 _ -> true
	| Etuple el -> List.for_all still_const el
	| Eapp (_,fct,el) ->
		let is_basic = match fct.e_desc with
		| Eglobal lid -> begin match lid.lname with
			| Name n -> (List.mem n Special_printer.basic_operations)
			| Modname l -> (List.mem l.id Special_printer.basic_operations)
			end
		| _ -> false
		in
		List.for_all still_const el && is_basic
	| Eperiod ep -> (still_const ep.p_period) && (match ep.p_phase with | None -> true | Some e -> still_const e)
	| Eop (_,el) ->
		List.for_all still_const el
	| _ -> false
