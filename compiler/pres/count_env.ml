open Zelus

type count_env_type = int Zident.Env.t


let count_env_union a b = 
	Zident.Env.union (fun id n1 n2 -> Some (n1 + n2)) a b

let count_env_union_list l = 
	List.fold_right (fun a acc ->
		count_env_union a acc) l Zident.Env.empty

let count_env_singleton id = 
	Zident.Env.singleton id 1

let count_list fct l = 
	List.fold_right (fun e acc ->
		count_env_union (fct e) acc) l Zident.Env.empty

let rec count_exp e = 
	match e.e_desc with
	| Elocal id -> count_env_singleton id
	| Eglobal _ | Econst _ | Econstr0 _ -> Zident.Env.empty
	| Econstr1 (_ , el) -> count_exp_list el
	| Elast id -> count_env_singleton id
	| Eapp (_ , e , el) -> count_env_union (count_exp e) (count_exp_list el)
	| Eop (_ ,el) | Etuple el -> count_exp_list el
	| Erecord_access (e,_) -> count_exp e
	| Erecord lel -> 
		let _,el = List.split lel in
		count_exp_list el
	| Erecord_with (e , lel) ->
		let _,el = List.split lel in
		count_exp_list el
	| Etypeconstraint (e, _ ) -> count_exp e

	| Epresent _ -> assert false (*not existing *) 
	| Ematch _ -> assert false (* not existing *)
	| Elet (local,e) -> count_env_union (count_exp e) (count_local local)
	| Eseq (e1,e2) -> count_env_union (count_exp e1) (count_exp e2)
	| Eperiod ep -> count_env_union (count_exp ep.p_period) (count_exp_opt ep.p_phase)
	| Eblock (eql, e) -> 
		count_env_union (count_exp e) (count_eq_list_block eql)	

and count_exp_list el = 
	List.fold_right (fun e acc ->
		count_env_union (count_exp e) acc) el Zident.Env.empty
	
and count_exp_opt e_opt = 
	match e_opt with
	| None -> Zident.Env.empty
	| Some e -> count_exp e

and count_pat pat = 
	match pat.p_desc with
	| Ewildpat | Econstpat _ | Econstr0pat _ -> Zident.Env.empty
	| Econstr1pat (_ , pl) -> count_pat_list pl
	| Etuplepat pl -> count_pat_list pl
	| Evarpat id -> count_env_singleton id
	| Ealiaspat (pat,id) -> count_env_union (count_pat pat) (count_env_singleton id)
	| Eorpat (pat1,pat2) -> count_env_union (count_pat pat1) (count_pat pat2)
	| Erecordpat lpl -> let _,pl = List.split lpl in count_pat_list pl
	| Etypeconstraintpat (pat,_) -> count_pat pat

and count_pat_list pl = 
	List.fold_right (fun pat acc ->
		count_env_union (count_pat pat) acc)
		pl Zident.Env.empty
		
and count_eq eq = 
	match eq.eq_desc with
	| EQeq (pat , e) -> count_env_union (count_pat pat) (count_exp e)
	| EQder (id,e,e_opt,ephl) ->
		count_env_union_list [count_exp e;count_env_singleton id;count_exp_opt e_opt;count_exp_present_handler_list ephl]
	| EQinit (id,e) -> count_env_union (count_env_singleton id) (count_exp e) 
	| EQnext (id, e, e_opt) -> count_env_union_list [count_exp e; count_exp_opt e_opt; count_env_singleton id]
	| EQpluseq (id,e) -> count_env_union (count_env_singleton id) (count_exp e)
	| EQautomaton (_,shl , se_opt) ->
		count_env_union (count_state_handler_list shl) (count_state_exp_option se_opt) 
	| EQpresent (phl, b_opt) ->
		let ph_env = count_present_handler_list phl in
		begin match b_opt with
		| None -> ph_env
		| Some b -> count_env_union ph_env (count_eq_list_block b)
		end
	| EQmatch (_,e,eqlbmhl) ->
		count_env_union (count_exp e) (count_eq_list_block_match_handler_list eqlbmhl)
	| EQreset (eql,e) -> 
		count_env_union (count_list count_eq eql) (count_exp e)
	| EQemit (id , e_opt) -> count_env_union (count_env_singleton id) (count_exp_opt e_opt)
	| EQblock eqlb -> count_eq_list_block eqlb
	| EQand eql -> count_eq_list eql
	| EQbefore eql -> count_eq_list eql
	| EQforall for_handler -> count_forall_handler for_handler

and count_eq_list eql =
	count_list count_eq eql

and count_scondpat scond = 
	match scond.desc with
    | Econdor (sc1,sc2) | Econdand (sc1,sc2) -> count_env_union (count_scondpat sc1) (count_scondpat sc2)
    | Econdexp e -> count_exp e
    | Econdpat (e,pat) -> count_env_union (count_exp e) (count_pat pat)
    | Econdon (sc,e) -> count_env_union (count_exp e) (count_scondpat sc)

and count_exp_present_handler eph = 
	count_env_union (count_exp eph.p_body) (count_scondpat eph.p_cond)

and count_exp_present_handler_list ephl = 
	List.fold_right (fun eph acc ->
		count_env_union acc (count_exp_present_handler eph) )
		ephl Zident.Env.empty

and count_present_handler ph = 
	count_env_union (count_eq_list_block ph.p_body) (count_scondpat ph.p_cond)

and count_present_handler_list phl = 
	List.fold_right (fun ph acc ->
		count_env_union acc (count_present_handler ph))
		phl Zident.Env.empty

and count_eq_list_block eqbl =
	count_eq_list eqbl.b_body

and count_eq_list_block_opt eqbl_opt = 
	match eqbl_opt with
	| None -> Zident.Env.empty
	| Some eqbl -> count_eq_list_block eqbl

and count_local local = 
	count_eq_list local.l_eq

and count_statepat sp = 
	match sp.desc with
	| Estate0pat _ -> Zident.Env.empty
	| Estate1pat ( _ , id_list) -> 
		List.fold_right (fun id acc ->
			count_env_union (count_env_singleton id) acc)
			id_list Zident.Env.empty	

and count_state_exp se = 
	match se.desc with
	| Estate0 _ -> Zident.Env.empty
	| Estate1 (_ , el) -> count_exp_list el

and count_state_exp_option se_opt = 
	match se_opt with
	| None -> Zident.Env.empty
	| Some se -> count_state_exp se

and count_escape es = 
	count_env_union_list [count_state_exp es.e_next_state; count_eq_list_block_opt es.e_block; count_scondpat es.e_cond]	

and count_escape_list el = 
	List.fold_right (fun e acc ->
		count_env_union (count_escape e) acc)
		el Zident.Env.empty

and count_state_handler sh = 
	count_env_union_list [count_statepat sh.s_state; count_eq_list_block sh.s_body; count_escape_list sh.s_trans]

and count_state_handler_list shl = 
	List.fold_right (fun sh acc ->
		count_env_union acc (count_state_handler sh))
		shl Zident.Env.empty

and count_eq_list_block_match_handler elbmh = 
	count_env_union (count_pat elbmh.m_pat) (count_eq_list_block elbmh.m_body)

and count_eq_list_block_match_handler_list elbmhl = 
	count_list count_eq_list_block_match_handler elbmhl	


and count_index index = 
	match index.desc with
	| Einput (id, e) ->
		count_env_union (count_env_singleton id) (count_exp e)
	| Eoutput (id1,id2) ->
		count_env_union (count_env_singleton id1) (count_env_singleton id2)
	| Eindex (id,e1,e2) ->
		count_env_union_list [count_env_singleton id; count_exp e1; count_exp e2]

and count_index_list inl = 
	count_list count_index inl

and count_forall_handler fah = 
	count_env_union (count_eq_list_block fah.for_body) (count_index_list fah.for_index)

let count_funexp fe = 
	count_env_union (count_list count_pat fe.f_args) (count_exp fe.f_body)

let num_opt env id = 
	match Zident.Env.find_opt id env with
	| None -> 0
	| Some n -> n

let used_outside block_count inner_count id = 
	num_opt block_count id <> num_opt inner_count id


