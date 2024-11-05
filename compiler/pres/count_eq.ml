open Zelus
open Viz2_utils

(** counts the number of equation-blocks present in a given block for viz2 *)

(** [count_exp e] count the number of equations for a given expression *)
let rec count_exp e = 
	match e.e_desc with
  	| Elocal _ | Eglobal _ | Econst _ | Econstr0 _ -> 0
	| Econstr1 (_,el) | Eop (_,el) | Etuple el ->
		count_exp_list el
	| Elast _ -> 0
	| Eapp _ -> 0
  	| Erecord_access (e,_) -> count_exp e
	| Erecord (lel) ->
		let _,el = List.split lel in
		count_exp_list el
	| Erecord_with (e,lel) ->
		let _,el = List.split lel in
		count_exp e + (count_exp_list el)
  	| Etypeconstraint (e,_) -> count_exp e
	| Epresent _ | Ematch _ -> assert false
  	| Elet (local , e) ->
		count_local local + count_exp e
  	| Eseq (e1,e2) ->
		(count_exp e1) + (count_exp e2)
  	| Eperiod ep ->
		count_exp ep.p_period + (count_exp_opt ep.p_phase)
  	| Eblock (eqlb, e) ->
		count_block eqlb + count_exp e

and count_exp_list el = 
	List.fold_left (fun acc e ->
		acc + (count_exp e)) 0 el

and count_exp_opt e_opt = 
	match e_opt with
	| None -> 0
	| Some e -> count_exp e

and count_eq (eq : eq) = 
	match eq.eq_desc with
	| EQeq (pat,e) -> 
		let num_pat = if exp_is_function e then 1 else max 1  (List.length (split_pat pat)) in
		(count_exp e) + num_pat(*one block for a function, else number of pats *) 
	| EQder (_,e,e_opt,e_handlers) -> 
		(match e_opt with
		| None -> 0
		| Some e_init -> if !Zmisc.do_viz2_show_init then (count_exp e_init) + 1 else 0) + (count_exp e) + 1
	| EQinit (_,e) ->
		if !Zmisc.do_viz2_show_init then
			1 + (count_exp e)
		else 0
	| EQnext (_,e,_) | EQpluseq (_,e) ->
		(count_exp e) + 1
  	| EQautomaton _ -> 1
  	| EQpresent (bl,b_opt) ->
		begin match b_opt with
		| None -> List.length bl
		| Some _ -> List.length bl + 1
		end
	| EQmatch (_,e,bl) ->
		(count_exp e) + List.length bl
  	| EQreset _ -> 1
	| EQemit (_,e_opt) ->
		let add_one = 
			match e_opt with
			| None -> 0
			| Some e ->
				if Viz2_utils.exp_is_function e && Viz2_utils.is_unit_type e.e_typ then 1 else 0
		in
		add_one + 1 + count_exp_opt e_opt
  	| EQblock eqlb ->
		count_block eqlb
	| EQand eql | EQbefore eql ->
		count_eq_list eql
  	| EQforall _ ->
		1

and count_eq_list eql = 
	List.fold_left (fun acc eq ->
		acc + (count_eq eq))
	0 eql

and count_local	local = 
	count_eq_list local.l_eq

and count_list f l = 
	List.fold_left (fun acc e ->
		acc + (f e)
	) 0 l

and count_block eqlb = 
	(count_list count_local eqlb.b_locals) + count_eq_list eqlb.b_body	
