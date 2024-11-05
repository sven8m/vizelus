open Zelus
open Utils_def

type build_env = {
	inputs : Zident.S.t ;
	outputs : Zident.S.t;
	const_inputs : Zident.S.t;
	const_outputs : Zident.S.t;
}

let print_env ff be = 
	Format.printf "inputs @.";
	Format.printf "%a@." Zident.S.fprint_t be.inputs;
	Format.printf "const_inputs @.%a@." Zident.S.fprint_t be.const_inputs;
	Format.printf "outputs @.%a@." Zident.S.fprint_t be.outputs;
	Format.printf "const_outputs @.%a@." Zident.S.fprint_t be.const_outputs;
	Format.printf "end env@."

let empty_env = {
	inputs = Zident.S.empty; 
	outputs = Zident.S.empty; 
	const_inputs = Zident.S.empty; 
	const_outputs = Zident.S.empty}


let build_env_union a b =
	{inputs = Zident.S.union a.inputs b.inputs;
	outputs = Zident.S.union a.outputs b.outputs;
	const_inputs = Zident.S.union a.const_inputs b.const_inputs;
	const_outputs = Zident.S.union a.const_outputs b.const_outputs;
	}

let build_env_union_list l = 
	List.fold_right (fun a acc ->
		build_env_union a acc)
		l empty_env

let build_opt fct el_opt = 
	match el_opt with
	| None -> empty_env
	| Some el -> fct el

let build_list fct l = 
	List.fold_right (fun e acc ->
		build_env_union (fct e) acc)
		l empty_env

let env_no_connection env = 
	if !Zmisc.do_viz_no_connect then
	{empty_env with const_inputs = Zident.S.union env.inputs env.const_inputs;
		const_outputs = Zident.S.union env.outputs env.const_outputs;
	}
	else env

(*let env_table = Hashtbl.create 42
*)
let rec build_exp (utils : utils) e = 
	
	match e.e_desc with
	| Elocal (id) -> {empty_env with inputs = Zident.S.singleton id}
	| Eglobal _ -> empty_env
	| Econst _ -> empty_env 
	| Econstr0 _ -> empty_env
	| Econstr1 (_, el) ->
		build_exp_list utils el
	| Elast id -> {empty_env with inputs = Zident.S.singleton id}
	| Eapp (_, e , el) -> build_env_union (build_exp utils e) (build_exp_list utils el)
	| Eop (_ , el) -> build_exp_list utils el 
	| Etuple el -> build_exp_list utils el
	| Erecord_access (e , _ ) -> build_exp utils e
	| Erecord lel -> let _ , el = List.split lel in build_exp_list utils el
	| Erecord_with (e , lel) ->
		let _ , el = List.split lel in 
		build_env_union (build_exp utils e) (build_exp_list utils el) 
	| Etypeconstraint (e, _ ) -> build_exp utils e

	| Epresent _ -> assert false (*not existing *)
	| Ematch _ -> assert false (*not existing *)
	| Elet (loc, e_after) -> 
		let loc_env = build_local utils loc in 
		let all_union = build_env_union loc_env (build_exp utils e_after) in
		build_pat_e all_union.outputs utils (Count_env.count_exp e) all_union (Find_vars.find_reg_vars_exp utils.in_reg e)
	| Eseq (e1,e2) -> build_env_union (build_exp utils e1) (build_exp utils e2)
	| Eperiod ep ->
		build_env_union (build_exp utils ep.p_period) (build_exp_opt utils ep.p_phase)
	| Eblock (eq_list_block ,ea) ->
		let eq_env = build_eq_list_block utils (*(Count_env.count_exp e)*) (*or ??*) eq_list_block in
		let e_env = build_exp utils ea in
		let all_union = build_env_union eq_env e_env in
		{all_union with outputs = Zident.S.empty; const_outputs = Zident.S.empty}

and build_exp_list utils el = 
	List.fold_right (fun e acc ->
		build_env_union (build_exp utils e) acc
	) el empty_env

and build_exp_opt utils e_opt = 
	match e_opt with
	| None -> empty_env
	| Some e -> build_exp utils e



and build_pat_e pats (utils :utils) count_inner build_env_e reg_vars = 
	let new_inputs = Zident.S.diff build_env_e.inputs pats in
	let new_inputs = 
	if utils.in_match && not !Zmisc.do_viz_no_connect then
		let reg_inputs = 
		(Zident.S.filter (fun id -> Count_env.used_outside utils.count_block count_inner id) reg_vars) in
		Zident.S.union reg_inputs new_inputs
	else 
		new_inputs
	in

	let new_const_inputs = Zident.S.diff build_env_e.const_inputs pats in
	
	let new_inputs_used = Zident.S.filter (fun id -> Count_env.used_outside utils.count_block count_inner id) new_inputs in
	let new_const_inputs = Zident.S.union new_const_inputs (Zident.S.diff new_inputs new_inputs_used) in
	let new_inputs = new_inputs_used in

	let pat_outputs = Zident.S.filter (fun id -> Count_env.used_outside utils.count_block count_inner id) pats in
	let pat_const_outputs = Zident.S.diff pats (Zident.S.union pat_outputs build_env_e.inputs) in
							(*here union to say that an output needed as input in another part is used somewhere so not realy a sink*)
	let new_outputs = pat_outputs in(*Zident.S.union pat_outputs build_env_e.outputs in*) 
	let new_const_outputs = Zident.S.union pat_const_outputs build_env_e.const_outputs in
	{inputs = new_inputs ; const_inputs = new_const_inputs; outputs = new_outputs; const_outputs = new_const_outputs} 

and clean_const env = 
	{env with const_inputs = Zident.S.empty; const_outputs = Zident.S.empty}

and build_eq utils eq = 
	let count_eq = Count_env.count_eq eq in
	let reg_vars_eq = Find_vars.find_reg_vars_eq utils.in_reg eq in
	let res = match eq.eq_desc with
	| EQeq (pat , e) -> 
		let pat_vars = Find_vars.find_vars_pattern pat in
		let build_env_e = build_exp utils e in
		build_pat_e pat_vars utils count_eq build_env_e reg_vars_eq 
	| EQder (id , e , e_opt , ephl) ->
		let pats = Zident.S.singleton id in
		let env_e = build_env_union (build_exp utils e) (build_exp_opt utils e_opt) in
		let env_e = build_env_union env_e (build_exp_present_handler_list utils ephl) in
		build_pat_e pats utils count_eq env_e reg_vars_eq
	| EQinit (id ,e) ->
  		let pats = Zident.S.singleton id in
		let env_e = build_exp utils e in
		build_pat_e pats utils count_eq env_e reg_vars_eq
	| EQnext (id , e , e_opt) ->
		let pats = Zident.S.singleton id in
		let env_e = build_env_union (build_exp utils e) (build_exp_opt utils e_opt) in
		build_pat_e pats utils count_eq env_e reg_vars_eq
	| EQpluseq (id,e) -> 
  		let pats = Zident.S.singleton id in
		let env_e = build_exp utils e in
		build_pat_e pats utils count_eq env_e reg_vars_eq
  	| EQautomaton (_,shl,se_opt) -> clean_const (build_automaton utils shl se_opt)
  	| EQpresent (phl, else_opt) ->
		clean_const (build_present utils (phl,else_opt ))
	| EQmatch (_,cond,match_handlers) -> 
		clean_const (build_env_union (build_exp utils cond) (build_match_block utils match_handlers))
  	| EQreset (eql,e) -> 
		clean_const (build_reset_block utils (eql,e))
  	| EQemit (id,e_opt) ->
		let pats = Zident.S.singleton id in
		let env_e = build_exp_opt utils e_opt in
		build_pat_e pats utils count_eq env_e reg_vars_eq
  	| EQblock eql -> build_eq_list_block utils eql 
  	| EQand eql -> build_eq_list utils eql
  	| EQbefore eql -> build_eq_list utils eql
  	| EQforall forall_handler -> clean_const (build_forall_handler utils forall_handler)
	in
	res

and build_eq_list_block utils eq_list_block =
	let all_union = List.fold_right (fun loc acc ->
		build_env_union (build_local (utils : utils) loc) acc)
		eq_list_block.b_locals empty_env
	in
	let all_union = List.fold_right (fun eq acc ->
		build_env_union (build_eq (utils : utils) eq) acc)
		eq_list_block.b_body all_union
	in

	build_pat_e all_union.outputs (utils : utils) (Count_env.count_eq_list_block eq_list_block) all_union (Find_vars.find_reg_vars_eq_list_block utils.in_reg eq_list_block)

and build_eq_list utils eq_list = 
	let all_union = build_list (build_eq utils) eq_list in
	let res = build_pat_e all_union.outputs utils (Count_env.count_eq_list eq_list) all_union (Find_vars.find_reg_vars_eq_list utils.in_reg eq_list)
	in
	res

and build_local (utils : utils) local = 
	let all_union = List.fold_right (fun eq acc ->
		build_env_union (build_eq utils eq) acc)
		local.l_eq empty_env
	in
	
	build_pat_e all_union.outputs utils (Count_env.count_local local) all_union (Find_vars.find_reg_vars_local utils.in_reg local)


and build_scond utils scond = 
	let res = match scond.desc with
	| Econdor (sc1,sc2) | Econdand (sc1, sc2) -> clean_const (build_env_union (build_scond utils sc1) (build_scond utils sc2))
	| Econdexp e -> build_exp utils e
	| Econdpat (e , pat) -> build_exp utils e
	| Econdon (sc, e) -> build_env_union (build_exp utils e) (clean_const (build_scond utils sc))
	in
	env_no_connection res

and build_exp_present_handler_body utils eph = 
	let condPat = Find_vars.findCondPatIds eph.p_cond in
	let body_env = build_exp utils eph.p_body in
	let new_const_inputs = Zident.S.union (body_env.const_inputs) (Zident.S.inter condPat body_env.inputs) in
	env_no_connection {body_env with inputs = Zident.S.diff body_env.inputs new_const_inputs; const_inputs = new_const_inputs}

and build_exp_present_handler utils eph = 
	let scond_env = clean_const (build_scond utils eph.p_cond) in
	let body_env = clean_const (build_exp_present_handler_body utils eph) in
	build_env_union scond_env body_env

and build_exp_present_handler_list utils ephl = 
	List.fold_right (fun eph acc ->
		build_env_union (build_exp_present_handler utils eph) acc) ephl empty_env

and build_present_handler_body (utils : utils) ph = 
	let condPat = Find_vars.findCondPatIds ph.p_cond in
	let body_env = build_eq_list_block utils ph.p_body in
	let new_const_inputs = Zident.S.union (body_env.const_inputs) (Zident.S.inter condPat body_env.inputs) in
	let avt = {body_env with inputs = Zident.S.diff body_env.inputs new_const_inputs; const_inputs = new_const_inputs} in
	env_no_connection (build_pat_e avt.outputs utils (Count_env.count_eq_list_block ph.p_body) avt (Find_vars.find_reg_vars_eq_list_block utils.in_reg ph.p_body))

and build_present_handler utils ph = 
	let scond_env = clean_const (build_scond utils ph.p_cond) in
	let body_env = clean_const (build_present_handler_body utils ph) in
	build_env_union scond_env body_env	

and build_present utils (phl , else_opt) =
	let new_env = List.fold_right (fun ph acc ->
		build_env_union (build_present_handler utils ph) acc) phl empty_env in
	match else_opt with
	| None -> new_env
	| Some bl -> build_env_union (clean_const (build_eq_list_block utils bl)) new_env

and build_state_exp utils es = 
	match es.desc with
	| Estate0 _ -> empty_env
	| Estate1 (_,el) -> build_list (build_exp utils) el

and build_escape utils es = 
	build_env_union_list [build_scond utils es.e_cond; build_opt (build_eq_list_block utils) es.e_block; build_state_exp utils es.e_next_state]	

and build_escape_handler_list utils esl = 
	build_list (build_escape utils) esl

and build_state_handler_body (utils : utils) sh =
	let body_env = build_eq_list_block utils sh.s_body in
	let new_const_inputs = Zident.S.union body_env.const_inputs body_env.inputs in
	let new_const_outputs = Zident.S.union body_env.const_outputs body_env.outputs in
	let res = {const_inputs = new_const_inputs ; inputs = Zident.S.empty; outputs = Zident.S.empty; const_outputs = new_const_outputs}
	in
	res

and build_state_handler (utils : utils) sh = 
	let state_vars = Find_vars.find_vars_statepat sh.s_state in	
	let body_env = clean_const (build_eq_list_block utils sh.s_body) in
	let body_env_inputs = Zident.S.diff body_env.inputs state_vars in
	let trans_env = (build_escape_handler_list utils sh.s_trans) in

	{body_env with inputs = Zident.S.union body_env_inputs trans_env.inputs;
	outputs = Zident.S.union body_env.outputs trans_env.outputs}	

and build_automaton utils shl se_opt = 
	begin match se_opt with
	| None -> ()
	| Some _ -> ();
	end;
	let union_env = List.fold_right (fun sh acc ->
		build_env_union (build_state_handler utils sh) acc)
		shl empty_env
	in
	let res = build_pat_e union_env.outputs utils (Count_env.count_state_handler_list shl) union_env (Find_vars.find_reg_vars_state_handler_list utils.in_reg shl) in
	clean_const res

and build_aut_transition (utils : utils) b_opt = 
	match b_opt with
	| None -> empty_env
	| Some b ->
		let b_env = build_eq_list_block utils b in
		let new_const_inputs = Zident.S.union b_env.const_inputs b_env.inputs in
		let new_const_outputs = Zident.S.union b_env.const_outputs b_env.outputs in
		{const_inputs = new_const_inputs;
		inputs = Zident.S.empty;
		outputs = Zident.S.empty;
		const_outputs = new_const_outputs;
		}

and build_match_handler (utils : utils) mh = 
	let pat_vars = Find_vars.find_vars_pattern mh.m_pat in
	let b_env = build_eq_list_block utils mh.m_body in
	let mh_count =  (Count_env.count_eq_list_block_match_handler mh) in 
	let reg_inputs = 
		if !Zmisc.do_viz_no_connect then
			Zident.S.empty
		else
			(Zident.S.filter (fun id -> Count_env.used_outside utils.count_block mh_count id) (Find_vars.find_reg_vars_eq_list_block false mh.m_body)) 
	in
	let ins = Zident.S.union b_env.inputs reg_inputs in 

	let c_ins = Zident.S.union b_env.const_inputs (Zident.S.inter pat_vars ins) in
	env_no_connection {b_env with inputs = Zident.S.diff ins c_ins; const_inputs = c_ins} 

and build_match_block utils match_handlers =
	let b_env = build_list (build_match_handler utils) match_handlers in
	let b_env = clean_const b_env in
	let exits = Zident.S.filter (fun id ->
		(Count_env.used_outside utils.count_block (Count_env.count_eq_list_block_match_handler_list match_handlers) id) ||
		(Zident.S.mem id b_env.inputs)
		) b_env.outputs 
	in
	env_no_connection {b_env with outputs = exits; const_outputs = Zident.S.diff b_env.outputs exits}

and build_reset_block utils (eql ,e) =
	let block_env = build_eq_list utils eql in
	(build_env_union (build_exp utils e) (env_no_connection block_env ))


and build_input_index utils index = 
	match index.desc with
	| Einput (id, e) ->
		Zident.S.singleton id, build_exp utils e
	| Eindex (id,e1,e2) ->
		Zident.S.singleton id, build_env_union (build_exp utils e1) (build_exp utils e2)
	| _ -> Zident.S.empty, empty_env

and build_input_list_index utils index_list = 
	List.fold_left (fun (ids,env) index ->
		let id_i, env_i = build_input_index utils index in
		Zident.S.union ids id_i, build_env_union env env_i
	) (Zident.S.empty, empty_env) index_list

and build_output_list_index index_list = 
	List.fold_right (fun index (ins, outs)  ->
		match index.desc with
		| Eoutput (id_in, id_out) ->
			Zident.S.add id_in ins, Zident.S.add id_out outs
		| _ -> ins, outs
	) index_list (Zident.S.empty, Zident.S.empty)

and build_forall_handler utils forall_handler = 
	let block_env = clean_const (build_eq_list_block utils forall_handler.for_body) in		
	let input_index, input_index_env = build_input_list_index utils forall_handler.for_index in
	let env = build_env_union block_env input_index_env in
	let output_ins, output_outs = build_output_list_index forall_handler.for_index in
	let env = {
		inputs = Zident.S.diff env.inputs input_index;
		const_inputs = Zident.S.diff env.const_inputs input_index;
		outputs = Zident.S.diff env.outputs output_ins;
		const_outputs = Zident.S.diff env.const_outputs output_outs}
	in
	env
