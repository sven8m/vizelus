open Zelus
open Viz2_utils

let find_list fct el = 
	List.fold_right (fun e acc ->
		Zident.S.union (fct e) acc) el Zident.S.empty

let find_union_list el =	
	List.fold_right (fun e acc -> 
		Zident.S.union e acc) el Zident.S.empty

let find_opt fct e_opt = 
	match e_opt with
	| None -> Zident.S.empty
	| Some e -> fct e

and find_vars_statepat sp = 
	match sp.desc with
	| Estate0pat _ -> Zident.S.empty
	| Estate1pat (_,idl) -> 
		Zident.S.of_list idl

let rec find_vars_pattern pat = match pat.p_desc with
	| Ewildpat -> Zident.S.empty
	| Econstpat _ -> Zident.S.empty
	| Econstr0pat _ -> Zident.S.empty
	| Etuplepat l | Econstr1pat (_ , l) -> List.fold_right (fun p s -> Zident.S.union (find_vars_pattern p) s) l Zident.S.empty
	| Evarpat id -> Zident.S.singleton id
	| Ealiaspat (_,id) -> Zident.S.singleton id
	| Eorpat (p1,p2) -> Zident.S.union (find_vars_pattern p1) (find_vars_pattern p2)
	| Erecordpat lpl ->
		let _ , pl = List.split lpl in
		List.fold_right (fun p s -> Zident.S.union (find_vars_pattern p) s) pl Zident.S.empty
	| Etypeconstraintpat (p,_) -> find_vars_pattern p

let rec find_vars_pattern_order ?(mult=false) pat = 
	let num_mult = if mult then numOutputs pat.p_typ else 1 in
	match pat.p_desc with
	| Ewildpat -> List.init (num_mult) (fun _ -> Zident.fresh "")
	| Econstpat _ -> []
	| Econstr0pat _ -> []
	| Etuplepat l | Econstr1pat (_ , l) -> List.fold_left (fun acc p  -> acc @ (find_vars_pattern_order ~mult:mult p)) [] l 
	| Evarpat id ->
		List.init (num_mult) (fun _ -> id )
	| Ealiaspat (_,id) -> [id]
	| Eorpat (p1,p2) -> (find_vars_pattern_order ~mult:mult p1) @ (find_vars_pattern_order ~mult:mult p2) (* potential bug *)
	| Erecordpat lpl ->
		let _ , pl = List.split lpl in
		List.fold_left (fun acc p  -> acc @ (find_vars_pattern_order ~mult:mult p)) [] pl
	| Etypeconstraintpat (p,_) -> find_vars_pattern_order p



let rec findCondPatIds scond =
	match scond.desc with
	| Econdor (s1,s2) | Econdand (s1,s2) -> Zident.S.union (findCondPatIds s1) (findCondPatIds s2)
	| Econdexp _ -> Zident.S.empty
	| Econdon (s,_) -> findCondPatIds s
	| Econdpat (_,pat) ->
		find_vars_pattern pat

let rec find_reg_vars_exp in_reg e = 
	match e.e_desc with
	| Elocal id -> if in_reg then Zident.S.singleton id else Zident.S.empty
  	| Eglobal _ | Econst _ -> Zident.S.empty
	| Econstr0 _ -> Zident.S.empty
	| Econstr1 (_ , el) -> 
		find_list (find_reg_vars_exp in_reg) el
	| Elast id -> Zident.S.singleton id
	| Eapp (_ , e, el) -> Zident.S.union (find_reg_vars_exp in_reg e) (find_list (find_reg_vars_exp in_reg) el)
  	| Eop (op , el) -> find_reg_vars_op in_reg (op,el) 
  	| Etuple el -> (find_reg_vars_exp_list in_reg el)
  	| Erecord_access (e , _) -> find_reg_vars_exp in_reg e
	| Erecord l -> let _ , el = List.split l in find_reg_vars_exp_list in_reg el
	| Erecord_with (e , l) -> Zident.S.union (find_reg_vars_exp in_reg e) (let _ ,el = List.split l in find_reg_vars_exp_list in_reg el)
	| Etypeconstraint (e,_) -> find_reg_vars_exp in_reg e
	| Epresent (ph , e_opt) -> assert false (*placeholder*) 
	| Ematch _ -> assert false
	| Elet (l , e) -> 
		Zident.S.union (find_reg_vars_local in_reg l) (find_reg_vars_exp in_reg e)	
  	| Eseq (e1,e2) -> Zident.S.union (find_reg_vars_exp in_reg e1) (find_reg_vars_exp in_reg e2)
	| Eperiod ep -> Zident.S.union (find_reg_vars_exp in_reg ep.p_period) (find_opt (find_reg_vars_exp in_reg) ep.p_phase)
	| Eblock _ -> assert false (*placeholder*)

and find_reg_vars_op in_reg (op,el) = 
	match op with
	| Efby ->
		let e1 = List.hd el in
		let e2 = List.hd (List.tl el) in
		Zident.S.union (find_reg_vars_exp in_reg e1) (find_reg_vars_exp true e2)
	| Eunarypre ->
		let e = List.hd el in
		find_reg_vars_exp true e
  	| _ -> find_reg_vars_exp_list in_reg el

and find_reg_vars_exp_list in_reg el = 
	find_list (find_reg_vars_exp in_reg) el

and find_reg_vars_local in_reg local = 
	find_list (find_reg_vars_eq in_reg) local.l_eq

and find_reg_vars_eq in_reg eq = 
	match eq.eq_desc with
	| EQeq (p,e) -> find_reg_vars_exp in_reg e
	| EQder (_ , e , e_opt , epl) ->
		find_list (fun a -> a) [find_reg_vars_exp in_reg e; find_opt (find_reg_vars_exp in_reg) e_opt; find_reg_vars_exp_phl in_reg epl]
	| EQinit (_ , e) -> find_reg_vars_exp in_reg e 
	| EQnext (_ , e , e_opt) -> 
		Zident.S.union (find_reg_vars_exp in_reg e) (find_opt (find_reg_vars_exp in_reg) e_opt)
	| EQpluseq (_ , e) -> find_reg_vars_exp in_reg e
	| EQautomaton (_ , shl , se_opt) -> 
		Zident.S.union (find_opt (find_reg_vars_state_exp in_reg) se_opt) (find_reg_vars_state_handler_list in_reg shl)
	| EQpresent (phl,b_opt) -> 
		Zident.S.union (find_reg_vars_present_handler_list in_reg phl) (find_opt (find_reg_vars_eq_list_block in_reg) b_opt)
	| EQmatch (_,e,mhs) -> Zident.S.union (find_reg_vars_exp in_reg e) (find_reg_vars_match_handlers in_reg mhs)
	| EQreset (eql,e) -> 
		Zident.S.union (find_list (find_reg_vars_eq in_reg) eql) (find_reg_vars_exp in_reg e)
	| EQemit (id , e_opt)  -> 
		find_opt (find_reg_vars_exp in_reg) e_opt
	| EQblock eqbl -> find_reg_vars_eq_list_block in_reg eqbl
	| EQand eql -> find_list (find_reg_vars_eq in_reg) eql
	| EQbefore eql -> find_list (find_reg_vars_eq in_reg) eql
	| EQforall forall_handler -> find_reg_vars_eq_list_block in_reg forall_handler.for_body

and find_reg_vars_eq_list_block in_reg bl =
	Zident.S.union (find_list (find_reg_vars_eq in_reg) bl.b_body) (find_list (find_reg_vars_local in_reg) bl.b_locals)

and find_reg_vars_exp_ph in_reg ep = 
	find_reg_vars_exp in_reg ep.p_body 

and find_reg_vars_exp_phl in_reg epl = 
	find_list (find_reg_vars_exp_ph in_reg) epl

and find_reg_vars_match_handler in_reg mh = 
	find_reg_vars_eq_list_block in_reg mh.m_body

and find_reg_vars_match_handlers in_reg mhs = 
	find_list (find_reg_vars_match_handler in_reg) mhs

and find_reg_vars_eq_list in_reg eq_list = 
	find_list (find_reg_vars_eq in_reg) eq_list

and find_reg_vars_state_exp in_reg se = 
	match se.desc with
	| Estate0 _ -> Zident.S.empty
	| Estate1 (_,el) -> find_reg_vars_exp_list in_reg el

and find_reg_vars_scondpat in_reg sc = 
	match sc.desc with
	| Econdor (sc1,sc2) | Econdand (sc1,sc2) -> Zident.S.union (find_reg_vars_scondpat in_reg sc1) (find_reg_vars_scondpat in_reg sc2)
	| Econdexp e -> find_reg_vars_exp in_reg e
	| Econdpat (e,_) -> find_reg_vars_exp in_reg e
	| Econdon (sc,e) -> Zident.S.union (find_reg_vars_scondpat in_reg sc) (find_reg_vars_exp in_reg e)

and find_reg_vars_escape in_reg es = 
	find_union_list [find_reg_vars_state_exp in_reg es.e_next_state; find_opt (find_reg_vars_eq_list_block in_reg) es.e_block; find_reg_vars_scondpat in_reg es.e_cond]

and find_reg_vars_escape_list in_reg esl = 
	find_list (find_reg_vars_escape in_reg) esl
and find_reg_vars_state_handler in_reg sh = 
	find_union_list [find_reg_vars_eq_list_block in_reg sh.s_body; find_reg_vars_escape_list in_reg sh.s_trans] 	

and find_reg_vars_state_handler_list in_reg shl = 
	find_list (find_reg_vars_state_handler in_reg) shl	

and find_reg_vars_present_handler in_reg ph = 
	Zident.S.union (find_reg_vars_eq_list_block in_reg ph.p_body) (find_reg_vars_scondpat in_reg ph.p_cond)

and find_reg_vars_present_handler_list in_reg phl =
	find_list (find_reg_vars_present_handler in_reg) phl
