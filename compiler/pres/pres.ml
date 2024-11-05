open Zelus
open Knode
open Mk_intermediate
open Intermediate_graph
open Utils_def
open Pres_help

let function_code = Hashtbl.create 42
let function_parameters = Hashtbl.create 42

let filename = ref ""


(** cbf : constr_before*)
let connect_ident ?(l=true) env endPoint lab id = 
	match Zident.Env.find_opt id env.output_env with
	| None -> if l then endPoint#addLabel lab
	| Some vP ->
		new_edge Simple endPoint vP

let rec pres_pattern ?(cbf=false) utils env source pat =
	match pat.p_desc with
	| Ewildpat -> 
		let node = mkOpNode (Sink ("_" ,false)) utils.function_node utils.layer in
		let unres = try_edge [] Simple source (Endpoint (outerToEndPoint (List.hd node#getInputs))) in
		[] , unres
	| Etuplepat pl ->
		let node = mkOpNode (UnTuple (List.length pl)) utils.function_node utils.layer in
		let unres = try_edge [] Simple (*Mult*) source (Endpoint (outerToEndPoint (List.hd node#getInputs))) in
		List.fold_right2 (fun pat outer_port (endList , unres) ->
			let acc_list , acc_unres = pres_pattern ~cbf:true (*fix for now*) utils env (Endpoint (outerToEndPoint outer_port)) pat in
			acc_list @ endList , acc_unres @ unres) pl node#getOutputs ([] , unres)
	| Evarpat id ->
		if (!Zmisc.do_viz_true_no_connect) then
			let node = mkOpNode (Sink (Format.asprintf "%a" Special_printer.name id , false)) utils.function_node utils.layer in
			let unres = try_edge [] Simple source (Endpoint (outerToEndPoint (List.hd node#getInputs))) in
			[], unres
		else begin
			let lab = edgeLabel ~forced:(if cbf then Center else Undef) (Format.asprintf "%a" Special_printer.name id) in 
			let endP, unres = begin match source with
			| Ident id_source ->
				let	node = mkOpNode Buffer utils.function_node utils.layer in
				let unres = try_edge [] Simple source (Endpoint (outerToEndPoint (List.hd node#getInputs))) in
				let exit = outerToEndPoint (List.hd node#getOutputs) in
				exit, unres
			| Endpoint endP ->
				endP, []
			end in
			connect_ident env endP lab id;
			[(endP, id)], unres
		end
	| Econstr0pat lid ->
		let node = mkOpNode (Sink (Format.asprintf "%a" Special_printer.longname lid , false)) utils.function_node utils.layer in
		let unres = try_edge [] Simple (*Mult*) source (Endpoint (outerToEndPoint (List.hd node#getInputs))) in
		[] , unres
	| Econstpat imm ->
		let node = mkOpNode (Sink (Format.asprintf "%a" Special_printer.immediate imm , false)) utils.function_node utils.layer in
		let unres = try_edge [] Simple source (Endpoint (outerToEndPoint (List.hd node#getInputs))) in
		[] , unres
	| Econstr1pat (lid , pl) ->
		let node = mkOpNode (Deconstr ((Format.asprintf "%a" Special_printer.longname lid) , List.length pl)) utils.function_node utils.layer in
		let unres = try_edge [] Simple (*Mult*) source (Endpoint (outerToEndPoint (List.hd node#getInputs))) in
		List.fold_right2 (fun pat outer_port (endList,unres) ->
			let acc_list, acc_unres = pres_pattern ~cbf:true utils env (Endpoint (outerToEndPoint outer_port)) pat in
			acc_list @endList , acc_unres @ unres
		) pl node#getOutputs ([] , unres)
	| Etypeconstraintpat (pat , _) -> pres_pattern utils env source pat
	| Eorpat _ -> assert false 
	| Erecordpat lpl -> 
		let isLast = ref true in
		let names = List.fold_right (fun (name,_) acc -> 
			let res = ((Format.asprintf "%a" Special_printer.longname name) ^ (if !isLast then "}" else " ;")):: acc in
			isLast := false;
			res
			) lpl []
		in
		let names = match names with
		| [] -> []
		| x :: q -> ("{ "^x)::q
		in
		let node = mkRecordNode RecordPat (fun id -> InnerRecordPat id) names utils.function_node utils.layer in
		let unres = try_edge [] Simple source (Endpoint (outerToEndPoint (List.hd node#getInputs))) in
		List.fold_right2 (fun (_,pat) outer_port (endList, unres) ->
			let acc_list, acc_unres = pres_pattern ~cbf:true utils env (Endpoint (outerToEndPoint outer_port)) pat in
			acc_list @ endList, acc_unres @ unres
		) lpl node#getOutputs ([] , unres)
	| Ealiaspat _ -> assert false

(** [map_exp_port utils env unres e_list outerPort_list] creates the visualization for each expression of [e_list]
	and then creates an edge from the endPoint of the expression to the corresponding outer Port from the endPoint of [outerPort_list] *)
let rec map_exp_port utils env unres e_list outerPort_list = 
	List.fold_left2 (fun (unres,env) e outerPort -> 
		let source, source_unres,env = pres_exp utils env e in
		let source,t_unres = List.hd source, [] in (*no no no *) (*expect_one utils source e.e_ty in *)
		let target = Endpoint (outerToEndPoint outerPort) in
		try_edge (t_unres @ source_unres @ unres) Simple  (*(do_mult e.e_ty)*) source target, env
	) (unres,env) e_list outerPort_list

(** [map_outputs node] maps the outer outputs of the [node] to return_type endpoints *)
and map_outputs node = 
	List.map (fun outer_output ->
		let endP = outerToEndPoint outer_output in
		Endpoint endP) 
	node#getOutputs

and pres_text_exp utils env e = 
	let text = Format.asprintf "%a" Special_printer.expression e in
	let inputs = (Env_build.build_exp utils e).inputs in
	
	let textNode = 
		if (Simple_expression.still_const e) && (Zident.S.cardinal inputs = 0) then
			mkOpNode (Const (text,false)) utils.function_node utils.layer 
		else
			mkOpNode (Text (text,Zident.S.cardinal inputs)) utils.function_node utils.layer 
	in

	let unres = List.fold_right2 (fun id outer_target unres ->
		let source = match Zident.Env.find_opt id env.input_env with
		| None -> Ident id
		| Some p -> Endpoint p
		in
		let unres = try_edge unres Simple source (Endpoint (outerToEndPoint outer_target)) in
		unres
	) (Zident.S.to_list inputs) textNode#getInputs []
	in

	map_outputs textNode, unres, env

and pres_exp ?(first=false) utils env e =
	if !Zmisc.do_viz_text &&  (Simple_expression.simple_exp e) && not (Simple_expression.too_simple e) then begin
		pres_text_exp utils env e
	end else 
	match e.e_desc with
	| Elocal id ->
		if (!Zmisc.do_viz_true_no_connect) then
			let opNode = mkOpNode (Const (Format.asprintf "%a" Special_printer.name id, true)) utils.function_node utils.layer in
			map_outputs opNode, [], env
		else begin
			let source = match utils.in_reg with
			| true -> 
				begin match Zident.Env.find_opt id env.reg_env with
				| None -> Ident id
				| Some p -> Endpoint p
				end
			| false ->
				Ident id
			in
			let source,need_buffer = match source with
			| Endpoint p -> Endpoint p, (List.length p#getLabels) <> 0
			| Ident id ->
				begin match Zident.Env.find_opt id env.input_env with
				| None -> (*Format.printf "ident@.";*) Ident id,true
				| Some p -> Endpoint p, (List.length p#getLabels) <> 0
				end
			in
			if first then begin 
				let opNode = mkOpNode Buffer utils.function_node utils.layer in
				let target = Endpoint (outerToEndPoint (List.hd opNode#getInputs)) in
				let unres = try_edge [] Simple source target in
				map_outputs opNode , unres, env
			end else
				[source] , [], env
		end
	| Eglobal lid ->
		let name = Format.asprintf "%a" Special_printer.longname lid.lname in
		let opNode = mkOpNode (Const (name, true)) utils.function_node utils.layer in
		map_outputs opNode , [], env
	| Econst imm -> (*done *)
		let opNode = mkOpNode (Const (Format.asprintf "%a" Special_printer.immediate imm, false)) utils.function_node utils.layer in
		map_outputs opNode , [], env
	| Econstr0 lid -> 
		let opNode = mkOpNode (Const (Format.asprintf "%a" Special_printer.longname lid, false)) utils.function_node utils.layer in
		map_outputs opNode , [], env
	| Econstr1 (lid,el) -> 
		let opNode = mkOpNode (Constr (Format.asprintf "%a" Special_printer.longname lid, List.length el)) utils.function_node utils.layer in
		let unres,env = map_exp_port utils env [] el opNode#getInputs in
		map_outputs opNode, unres, env
	| Elast id -> (*to be tested *)
		let opNode = mkOpNode Last utils.function_node utils.layer in
		let lastInput = outerToEndPoint (List.hd opNode#getInputs) in
		let unres = if Zident.Env.mem id env.reg_env  then try_edge [] Simple (**) (Endpoint (Zident.Env.find id env.reg_env)) (Endpoint lastInput) 
			else try_edge [] Simple (Ident id) (Endpoint lastInput) 
		in
		map_outputs opNode , unres, env
	| Eapp (_ , fct, el) ->
		let name_basic,high = match fct.e_desc with
		| Eglobal lid -> begin match lid.lname with
			| Name n -> n,false
			| Modname l -> l.id,false 
			end
		| _ -> Format.asprintf "%a" Special_printer.expression fct , true
		in

		let rec num_parameters (ty : Deftypes.typ_desc Deftypes.loc)= 
			match ty.t_desc with
			| Deftypes.Tvar | Tproduct _ | Tconstr _ | Tvec _  -> 0
			| Deftypes.Tlink ty -> num_parameters ty
			| Tfun (_,_,_,ty) -> 1 + (num_parameters ty)
		in
		
		let high = high || (List.length el) <> (num_parameters fct.e_typ) in
		(*
			if not high then 
				match Hashtbl.find_opt function_parameters name_basic with
				| None -> false
				| Some n -> (List.length el) <> n
			else
				true
		in *)
		if not high then begin
			let node_type = match name_basic with
			| "or" -> Or 2 
			| "and" -> And 2
			| "+" | "+." -> Add 2 
			| "*" | "*." -> Mult 2
			| "-" | "-." | "~-." -> Minus (List.length el) 
			| "/" | "/." -> Div
			| "mod" -> Mod
			| x when List.mem x basic_operations -> Text (Special_printer.xml_characters x,List.length el)
			| _-> Fct name_basic
			in
		
			let is_extern = (not high) && match fct.e_desc with
			| Eglobal lid -> begin match lid.lname with
				| Name _ -> false
				| Modname l -> l.qual <> !filename
				end
			| _ -> assert false
			in
			let appNode = 
				match node_type with
				| Fct name_basic ->
					(*begin match fct.e_desc with
					| Eglobal lid -> Format.printf "%a %b@." Lident.fprint_t lid.lname is_extern;
					| _ -> assert false
					end;*)
					if (not high) && Hashtbl.mem function_code name_basic && (not is_extern) then
						begin match implementation (Node utils.function_node) (Hashtbl.find function_code name_basic) (utils.layer + 1)
						with Some n -> n
						| _ -> assert false
						end
					else
						let name_basic = Special_printer.xml_characters name_basic in
						let inputs = List.init (List.length el) (fun _ -> "") in
						mkFunctionNode ~order:true (Fct name_basic) inputs [""] (Node utils.function_node) (utils.layer + 1)		
				| _ -> 
					mkOpNode node_type utils.function_node utils.layer 
			in
			if node_type <> Mod then begin
				let unres,env = map_exp_port utils env [] el appNode#getInputs in
				map_outputs appNode, unres, env
			end else begin
				let unres,env = map_exp_port utils env [] [(List.hd el)] appNode#getInputs in
				let unres,env = map_exp_port utils env unres (List.tl el) appNode#getControl in
				map_outputs appNode, unres, env
			end
		end else begin
			let opNode = mkOpNode (PartApp (Format.asprintf "%a" Special_printer.expression fct, num_parameters fct.e_typ, List.length el)) utils.function_node utils.layer in
			let inputs,fct_input = 
				let rec f l = 
					match l with
					| [] -> assert false
					| [x] -> [] , [x]
					| x :: q -> let res,res2 = f q in x ::res,res2
				in f opNode#getInputs 
			in
			let unres,env = map_exp_port utils env [] [fct] fct_input in 
			let unres,env = map_exp_port utils env unres el inputs in
			map_outputs opNode, unres,env
		end
	| Eop (op, exp_l) -> pres_op utils env (op, exp_l)
	| Etuple el -> (* to test *)
		let opNode = mkOpNode (Tuple (List.length el)) utils.function_node utils.layer in
		let unres, env = map_exp_port utils env [] el opNode#getInputs in
		map_outputs opNode, unres, env
	| Erecord_access (e , lid) -> 
		let opNode = mkOpNode (Text (Format.asprintf ".%a" Special_printer.longname lid,1)) utils.function_node utils.layer in
		let unres, env = map_exp_port utils env [] [e] opNode#getInputs in
		map_outputs opNode, unres, env
	| Erecord lel ->
		let names = List.map (fun (lid,_) -> Format.asprintf "%a = " Special_printer.longname lid) lel in
		let opNode = mkRecordNode Record (fun id -> InnerRecord id) names utils.function_node utils.layer in
		let _,el = List.split lel in
		let unres, env = map_exp_port utils env [] el opNode#getInputs in
		map_outputs opNode, unres, env
	| Erecord_with (e, lel) ->
		
		let names = List.map (fun (lid,_) -> Format.asprintf "%a = " Special_printer.longname lid) lel in
		let names = match names with
		| [] -> []
		| x :: q -> ((Format.asprintf "%a with " Special_printer.expression e) ^ x):: q
		in
		let opNode = mkRecordNode Record (fun id -> InnerRecord id) names utils.function_node utils.layer in
		let _,el = List.split lel in
		let unres, env = map_exp_port utils env [] el opNode#getInputs in
		map_outputs opNode, unres, env

	| Etypeconstraint (e , _ ) -> pres_exp utils env e
	| Epresent _ -> assert false (* not existing *)
	| Ematch _ -> assert false (* not existing *)
	| Elet (local , e) -> 
		let new_env , unres = pres_local utils env local in
		let ends , new_unres,new_env_after = pres_exp utils new_env e in
		let env = union_init_env env new_env_after in
		let unres = resolve_after_block new_env env utils (unres @ new_unres) in
		ends , unres, env
	| Eseq (e1,e2) ->
		let outs1, unres1, env1 = pres_exp utils env e1 in
		let outs2, unres2, env2 = pres_exp utils env e2 in
		let env = union_init_env env (union_init_env env1 env2) in
		(* what with outs1 ?*)
		outs2 , unres1 @ unres2, env
	| Eperiod ep -> 
		let is_phase = match ep.p_phase with
		| None -> false
		| _ -> true 
		in
		let opNode = mkOpNode (Period is_phase) utils.function_node utils.layer in
		let unres, env = map_exp_port utils env [] [ep.p_period] opNode#getInputs in
		let unres, env = match ep.p_phase with
		| None -> unres, env
		| Some e -> map_exp_port utils env unres [e] opNode#getControl in
		map_outputs opNode, unres, env
	| Eblock (eqlb , e) ->	
		let new_env, unres = pres_equation_list_block utils env eqlb in
		let outs , unres_e, env_e = pres_exp ~first:true utils new_env e in
		let env = union_init_env env env_e in	
		let unres = resolve_after_block new_env env utils (unres @ unres_e) in
		outs , unres, env

and pres_op utils env (op , exp_list) = 
	match op with
	| Efby -> (*e1 fby e2 *)
		assert (List.length exp_list = 2);
		let e1 = List.hd exp_list in
		let e2 = List.hd (List.tl exp_list) in
		let opNode = mkOpNode Fby utils.function_node utils.layer in
		let unres,env = map_exp_port utils env [] [e1] opNode#getControl in
		let unres,env = map_exp_port {utils with in_reg=true} env unres [e2] opNode#getInputs in
		map_outputs opNode, unres, env
	| Eunarypre -> 	(* pre e *)
		assert (List.length exp_list = 1);
		let e = List.hd exp_list in
		let opNode = mkOpNode Reg utils.function_node utils.layer in
		let unres, env = map_exp_port {utils with in_reg=true} env [] [e] opNode#getInputs in
		map_outputs opNode, unres, env
	| Eifthenelse -> (* if e1 then e2 else e3 *)
		assert (List.length exp_list = 3);
		let e1 = List.hd exp_list in
		let el = List.tl exp_list |> List.rev in
		let opNode = mkOpNode Mux utils.function_node utils.layer in
		let unres, env = map_exp_port utils env [] el opNode#getInputs in
		let unres, env = map_exp_port utils env unres [e1] opNode#getControl in
		map_outputs opNode, unres, env
	| Eminusgreater -> (* e1 -> e2 *)
		assert (List.length exp_list = 2);
		let e1 = List.hd exp_list in
		let e2 = List.hd (List.tl exp_list) in
		let opNode = mkOpNode Mg utils.function_node utils.layer in
		let unres, env = map_exp_port utils env [] [e1] opNode#getControl in
		let unres, env = map_exp_port utils env unres [e2] opNode#getInputs in
		map_outputs opNode, unres, env
	| Eup ->
		assert (List.length exp_list = 1);
		let e = List.hd exp_list in
		let opNode = mkOpNode Up utils.function_node utils.layer in
		let unres, env = map_exp_port utils env [] [e] opNode#getInputs in
		map_outputs opNode, unres, env
	| Einitial -> 
		assert (List.length exp_list = 0);
		let opNode = mkOpNode (Init "") utils.function_node utils.layer in
		map_outputs opNode, [], env
	| Edisc -> 
		assert (List.length exp_list = 1);
		let e = List.hd exp_list in
		let opNode = mkOpNode Disc utils.function_node utils.layer in
		let unres, env = map_exp_port utils env [] [e] opNode#getInputs in
		map_outputs opNode, unres, env
	| Ehorizon -> assert false (*seems to not exist *)
	| Etest -> 
		assert (List.length exp_list = 1);
		let e = List.hd exp_list in
		let opNode = mkOpNode Test utils.function_node utils.layer in
		let unres, env = map_exp_port utils env [] [e] opNode#getInputs in
		map_outputs opNode, unres, env
	| Eaccess -> 
		assert (List.length exp_list = 2);
		(* e.(id) *)
		let e = List.hd exp_list in
		let id = Format.asprintf "%a" Special_printer.expression (List.hd (List.tl exp_list)) in
		let opNode = mkOpNode (Select id) utils.function_node utils.layer in
		let unres,env = map_exp_port utils env [] [e] opNode#getInputs in
		map_outputs opNode, unres, env
	| Eupdate -> 
		assert (List.length exp_list = 3);
		(* [| e with id = e|] *)
		assert false
	| Eslice (s1,s2) -> 
		assert (List.length exp_list  = 1);
		(* e {s1..s2} *)
	assert false
	| Econcat -> 
		assert (List.length exp_list = 2);
		(* [| e1 | e2|] *)

		assert false
	| Eatomic -> 
		assert (List.length exp_list = 1);
		pres_exp utils env (List.hd exp_list)

and pres_equ utils env equ = 
	match equ.eq_desc with
	| EQeq (pat , e) ->
		let is_liquely_imperative = match pat.p_desc with
		| Ewildpat -> (*Format.printf "pat wild@.";*) false (*maybe better *)
		| Econstpat Evoid -> (*Format.printf "pat const@.";*) true
		| Econstpat _ -> (*Format.printf "pat const@.";*) false
		| Econstr0pat _ -> (*Format.printf "pat constr0@.";*) false
		| Econstr1pat _ -> (*Format.printf "pat constr1@.";*) false
		| Etuplepat _ -> (*Format.printf "pat tuple@.";*) false
		| Evarpat _ -> (*Format.printf "var pat@.";*) false
		| Ealiaspat _ -> (*Format.printf "pat alias @.";*) false
		| Eorpat _ -> (*Format.printf "pat or @.";*) false
		| Erecordpat _ -> (*Format.printf "pat record @.";*) false
		| Etypeconstraintpat _ -> (*Format.printf "pat type@.";*) false
		in
		let endPoints , unres, env = pres_exp ~first:true utils env e in
		let endPoint, new_unres = expect_one utils endPoints in
		if (not (is_liquely_imperative)) then begin
			let point_id_list , pat_unres = pres_pattern utils env endPoint pat in
			let env = List.fold_right (fun (endPoint , id) env ->
				{env with input_env = Zident.Env.add id endPoint env.input_env}) point_id_list env
			in
			env, (new_unres @ unres)
		end else
			env,(new_unres @ unres)
	| EQder (id, der, init_opt, resets_list) -> 
		let init_text = match init_opt with
		| None -> ""
		| Some e -> Format.asprintf "%a" Special_printer.expression e
		in
		let opNode = mkOpNode (Der (init_text, if resets_list <> [] then 1 else 0(*List.length resets_list*))) utils.function_node utils.layer in
		let unres, env = map_exp_port utils env [] [der] opNode#getInputs in
	
		let new_reset_env, reset_unres = match resets_list with
		| [] -> env, []
		| _ -> 
			let new_reset_env, reset_unres, resetEnd = pres_reset_der utils env resets_list in
			new_edge ~prio:1 Simple resetEnd (outerToEndPoint (List.hd opNode#getControl));
			new_reset_env, reset_unres
		in

		let endPoint = outerToEndPoint (List.hd opNode#getOutputs) in
		connect_ident env endPoint (labelFromId id) id; 
		let input_env = Zident.Env.add id endPoint new_reset_env.input_env in
		{new_reset_env with input_env = input_env} , (unres @ reset_unres)
	| EQinit (id , e) ->
		if not !Zmisc.viz_no_init then begin
			let opNode = mkOpNode (Init (Format.asprintf "%a" Special_printer.name id)) utils.function_node utils.layer in
			let unres, env = map_exp_port utils env [] [e] opNode#getInputs in
			let endPoint = outerToEndPoint (List.hd opNode#getOutputs) in
			connect_ident ~l:false env endPoint (labelFromId id) id;
			let init_env = Zident.Env.add id endPoint env.init_env in
			{env with init_env = init_env} , unres
		end else
			env, []
	| EQnext (id , e , e_opt) -> 
		begin match e_opt with
		| None -> () | _ -> assert false
		end;
		let nextNode = mkOpNode (Next (Format.asprintf "%a" Special_printer.name id)) utils.function_node utils.layer in
		let outs , unres, env = pres_exp ~first:true utils env e in
		assert (List.length outs = 1);
		let unres = try_edge unres Simple (List.hd outs) (Endpoint (outerToEndPoint (List.hd nextNode#getInputs))) in
		connect_ident env (outerToEndPoint (List.hd nextNode#getOutputs)) (labelFromId id) id; 
		let new_input_env = Zident.Env.add id (outerToEndPoint (List.hd nextNode#getOutputs)) env.input_env in
		{env with input_env = new_input_env} , unres

	| EQpluseq (id , e) -> 
		(*placeholder *)	
		let outs, unres,env = pres_exp ~first:true utils env e in
		assert (List.length outs = 1);
		let pNode = mkOpNode (Text ("+=",2)) utils.function_node utils.layer in
		let unres = try_edge unres Simple (List.hd outs) (Endpoint (outerToEndPoint (List.hd pNode#getInputs))) in
		connect_ident env (outerToEndPoint (List.hd pNode#getOutputs)) (labelFromId id) id;
		let new_input_env = Zident.Env.add id (outerToEndPoint (List.hd pNode#getOutputs)) env.input_env in
		
		let sec = List.hd (List.tl pNode#getInputs) in
		new_edge Simple (outerToEndPoint (List.hd pNode#getOutputs)) (outerToEndPoint sec);
		{env with input_env = new_input_env}, unres	
	| EQautomaton (is_weak,state_handlers,init_opt) -> 
		pres_automaton utils env (is_weak,state_handlers,init_opt) equ
	| EQpresent (phl , else_opt) ->
		pres_present utils env phl else_opt
	| EQmatch (_,cond,match_handlers) -> pres_match utils env (cond,match_handlers) 
	
	| EQreset (eql,e_reset) -> 
		pres_reset_block utils env (eql,e_reset)

	| EQemit (id , e_opt) -> 
		let emitNode = mkOpNode (Emit (Format.asprintf "%a" Special_printer.name id)) utils.function_node utils.layer in
		let unres = match e_opt with
		| None -> []
		| Some e ->
			let outs , unres, env = pres_exp ~first:true utils env e in
			assert (List.length outs = 1);
			try_edge unres Simple (List.hd outs) (Endpoint (outerToEndPoint (List.hd emitNode#getInputs)))
		in
		connect_ident env (outerToEndPoint (List.hd emitNode#getOutputs)) (labelFromId id) id; 
		let new_input_env = Zident.Env.add id (outerToEndPoint (List.hd emitNode#getOutputs)) env.input_env in
		{env with input_env = new_input_env} , unres

	| EQblock eqlb -> 
		(*for now *)
		pres_equation_list_block utils env eqlb
	| EQand eql -> pres_equation_list utils env eql
	| EQbefore eql -> pres_equation_list utils env eql
	| EQforall forall_handler -> pres_forall utils env forall_handler

and pres_local utils env local =
	List.fold_left (fun (env,unres) eq ->
		let new_env, eq_unres =  pres_equ utils env eq 	in
		new_env , unres @ eq_unres) (env , []) local.l_eq 

and pres_equation_list utils env eql = 
	List.fold_left (fun (env,unres) eq ->
		let new_env, eq_unres = pres_equ utils env eq in
		new_env, unres @ eq_unres) (env,[]) eql

and pres_equation_list_block utils env eqlb = 
	let new_env, unres = 
		List.fold_left (fun (env,unres) local ->
			let new_env, new_unres = pres_local utils env local in
			new_env, unres @ new_unres) (env,[]) eqlb.b_locals
	in
	List.fold_left (fun (env,unres) eq ->
		let new_env, eq_unres = pres_equ utils env eq in
		new_env, unres @ eq_unres) (new_env,unres) eqlb.b_body


and init_block ?(is_aut_state=false) ?(is_match=false) ?(addI=[]) ?(addO=[]) ?(control=false) utils (build_env : Env_build.build_env) env node_type = 

	let build_env = 
		if !Zmisc.do_viz_true_no_connect then
			{Env_build.empty_env with const_inputs = build_env.const_inputs; const_outputs = build_env.const_outputs}
		else
			build_env
	in
	let inputs = List.map (fun id -> Format.asprintf "%a" Special_printer.name id)
		(Zident.S.to_list build_env.inputs)
	in
	let outputs = List.map (fun id -> Format.asprintf "%a" Special_printer.name id)
		(Zident.S.to_list build_env.outputs)
	in


	let opNode = mkFunctionNode ~control:control ~addI:addI ~addO:addO node_type inputs outputs (Node utils.function_node) utils.layer in
	

	let rec ignore_n n l = 
		match n, l with
		| 0 , _ -> l
		| _ , x :: q -> ignore_n (n-1) q
		| _ -> assert false
	in

	let inputPorts = ignore_n (List.length addI) opNode#getInputs in
	(*match addI with
	| None -> opNode#getInputs
	| Some _ -> List.tl (opNode#getInputs)
	in*)

	let outputPorts = ignore_n (List.length addO) opNode#getOutputs in
	(*match addO with
	| None -> opNode#getOutputs
	| Some _ -> List.tl (opNode#getOutputs)
	in*)

	let input_env, input_unres = List.fold_right2 (fun id outer_target (input_env,unres) ->
		let source = match Zident.Env.find_opt id env.input_env with
		| None -> Ident id
		| Some p -> Endpoint p
		in
		let unres = try_edge unres Simple source (Endpoint (outerToEndPoint outer_target)) in
		let inner_target = List.hd (outer_target#getInnerPorts) in
		Zident.Env.add id inner_target input_env, unres
	) (Zident.S.to_list build_env.inputs) inputPorts (Zident.Env.empty, [])
	in

	let input_env = 
		Zident.S.fold (fun id new_input_env ->
			let constNode = mkOpNode (Const (Format.asprintf "%a" Special_printer.name id , false)) opNode (utils.layer + 1) in
			let source = outerToEndPoint (List.hd constNode#getOutputs) in
			Zident.Env.add id source new_input_env) build_env.const_inputs input_env
	in

	let output_env, output_unres = List.fold_right2 (fun id outer_source (output_env,unres) ->
		let target = match Zident.Env.find_opt id env.output_env with
		| None -> Ident id
		| Some p -> Endpoint p
		in
		let unres = try_edge unres Simple (Endpoint (outerToEndPoint outer_source)) target in
		let inner_source = List.hd (outer_source#getInnerPorts) in
		Zident.Env.add id inner_source output_env, unres
	) (Zident.S.to_list build_env.outputs) outputPorts (Zident.Env.empty , [])
	in
	
	let outer_output_env = output_env in

	let output_env = 
		Zident.S.fold (fun id new_output_env ->
		let sinkNode = mkOpNode (Sink (Format.asprintf "%a" Special_printer.name id , is_aut_state)) opNode (utils.layer + 1) in
		let target = outerToEndPoint (List.hd sinkNode#getInputs) in
		Zident.Env.add id target new_output_env) build_env.const_outputs output_env
	in

	let reg_env = 
		if is_match then input_env
		else output_env
	in

	let op_env = {input_env = input_env ; output_env = output_env; reg_env = reg_env; init_env = Zident.Env.empty} in
	let op_utils = {utils with function_node = opNode; layer = utils.layer + 1} in
	opNode, op_env , input_unres @ output_unres, op_utils, outer_output_env


and pres_scondpat ?(prio=None) ?(vert=false) utils env scond = 

	let addOSide = match vert with
	| false -> East
	| true -> South
	in
	let prio = if !Zmisc.do_viz_text_scond then
		match prio with
		| None -> Some (Format.asprintf "%a" Special_printer.scondpat scond)
		| Some p -> Some (Format.asprintf "%s : %a" p Special_printer.scondpat scond)
		else prio
	in
	let opNode, cond_env, op_unres, utils, outer_cond_output = init_block ~addI:[mk_addPort Input] ~addO:[mk_addPort addOSide] utils (Env_build.build_scond utils scond) env (Scond prio) in

	let utils = {utils with layer = utils.layer - 1} in
	let exitPoint = outerToEndPoint (List.hd opNode#getOutputs) in
	let inputPoint = outerToEndPoint (List.hd opNode#getInputs) in
	if not !Zmisc.do_viz_text_scond then begin 
		match scond.desc with
	| Econdand (scond1, scond2) -> 
		let inputCond1, exitCond1, unres1 = pres_scondpat utils cond_env scond1 in
		let inputCond2, exitCond2, unres2 = pres_scondpat utils cond_env scond2 in
		inputCond1#delSelf;
		new_edge Big exitCond1 inputCond2;
		new_edge Big exitCond2 exitPoint;
		assert (unres1 @ unres2 = [])
	| Econdor (scond1, scond2) -> 
		let inputCond1, exitCond1,unres1 = pres_scondpat utils cond_env scond1 in
		let inputCond2, exitCond2,unres2 = pres_scondpat utils cond_env scond2 in
		inputCond1#delSelf;
		inputCond2#delSelf;
		let orNode = mkOpNode (Or 2) utils.function_node utils.layer in
		let or1 = List.hd orNode#getInputs in
		let or2 = List.hd (List.tl orNode#getInputs) in
		new_edge Big exitCond1 (outerToEndPoint or1);
		new_edge Big exitCond2 (outerToEndPoint or2);
		new_edge Big (outerToEndPoint (List.hd orNode#getOutputs)) exitPoint;
		assert(unres1 @ unres2 = [])
	| Econdexp e ->
		let outs , unres, _ (*the inits are local*) = pres_exp ~first:true utils cond_env e in
		assert (List.length outs = 1);
		let endPoint = List.hd outs in
		let unres = try_edge unres Big endPoint (Endpoint exitPoint) in
		resolve_unres utils cond_env unres 
	| Econdpat (e, pat) -> 
		(*placeholder *)
		let text = Special_printer.xml_characters (Format.asprintf "%a" Special_printer.scondpat scond) in
		let vars_ins = Find_vars.find_reg_vars_exp true e in
		let textNode = mkFunctionNode ~vis:false (Const (text,false)) (List.init (Zident.S.cardinal vars_ins) (fun _ -> "")) [""] (Node utils.function_node) utils.layer in
		new_edge Big (outerToEndPoint (List.hd textNode#getOutputs)) exitPoint;
		List.iter2 (fun id outer_target->
			let source = Zident.Env.find id cond_env.input_env in
			new_edge Simple source (outerToEndPoint outer_target))
		(Zident.S.to_list vars_ins) (textNode#getInputs)
	| Econdon (scond2, e) -> 
		let inputCond1, exitCond1, unres1 = pres_scondpat utils cond_env {scond with desc = Econdexp e} in
		let inputCond2, exitCond2, unres2 = pres_scondpat utils cond_env scond2 in
		inputCond1#delSelf;
		new_edge Big exitCond1 inputCond2;
		new_edge Big exitCond2 exitPoint;
		assert (unres1 @ unres2 = [])
	end;
	inputPoint, exitPoint, op_unres

and pres_exp_present_handler ?(prio) utils env (ph : exp present_handler) = 
	let inputCond , exitCond, unresCond = pres_scondpat ~prio:prio utils env ph.p_cond in
	inputCond#delSelf;

	let bodyNode , body_env, body_unres, body_utils, outer_body_output = init_block ~addI:[mk_addPort Input] ~addO:[mk_addPort Output] utils (Env_build.build_exp_present_handler_body utils ph) env (BlanckFct SIDE) in 
	
	let bodyCondEndPoint = outerToEndPoint (List.hd bodyNode#getInputs) in
	new_edge Big exitCond bodyCondEndPoint;

	let outs , exp_unres, env = pres_exp ~first:true body_utils body_env ph.p_body in
	resolve_unres body_utils body_env exp_unres;
	assert (List.length outs = 1);
	let exp_endPoint = List.hd outs in
	let unres = try_edge [] Simple exp_endPoint (Endpoint (outerToEndPoint (List.hd bodyNode#getOutputs))) in
	assert (unres = []);
	outerToEndPoint (List.hd bodyNode#getOutputs), unresCond @ body_unres

and pres_reset_der utils env resets_list = 	
	
	let resetNode, reset_env, reset_unres, reset_utils, outer_reset_output = 
		init_block ~addO:[mk_addPort Output] utils (Env_build.build_exp_present_handler_list utils resets_list) env ResetDer in
	
	let priorities = List.init (List.length resets_list) (fun id -> string_of_int (id + 1)) in

	let resetOutput = (outerToEndPoint (List.hd resetNode#getOutputs)) in	
	let unres = List.fold_left2 (fun unres ph prio ->
		let ph_endPoint , ph_unres = pres_exp_present_handler ~prio:prio reset_utils reset_env ph in
		new_edge Simple ph_endPoint resetOutput;
		ph_unres @ unres) 
		[] resets_list priorities 
	in
	resolve_unres reset_utils reset_env unres;

	let new_env = {env with input_env = Zident.Env.union (fun id a1 a2 -> Some a1) env.input_env outer_reset_output} in
	new_env , reset_unres, resetOutput



and pres_present_handler ?(prio) utils env ph = 
	let inputCond, exitCond, unresCond = pres_scondpat ~prio:prio utils env ph.p_cond in
	inputCond#delSelf;
	assert (unresCond = []);

	let blockNode, block_env, ino_unres, block_utils, _ = 
		init_block ~addI:[mk_addPort Input] utils (Env_build.build_present_handler_body utils ph) env (BlanckFct SIDE) in 
	assert (ino_unres = []);
	let blockCondEndPoint = outerToEndPoint (List.hd blockNode#getInputs) in
	new_edge Big exitCond blockCondEndPoint;

	let new_block_env, block_unres =  pres_equation_list_block block_utils block_env ph.p_body in
	resolve_unres block_utils new_block_env block_unres

and pres_else_handler utils env else_block = 
	let condNode, _, _, _,_ = 
		init_block ~addO:[mk_addPort Output] utils (Env_build.empty_env) env (Scond (Some "else")) in
	let exitCond = outerToEndPoint (List.hd condNode#getOutputs) in

	let blockNode, block_env, ino_unres, block_utils,_ = 
		init_block ~addI:[mk_addPort Input] utils (Env_build.build_eq_list_block utils else_block) env (BlanckFct SIDE) in
	assert (ino_unres = []);
	let blockCondEndPoint = outerToEndPoint (List.hd blockNode#getInputs) in
	new_edge Big exitCond blockCondEndPoint;

	let new_block_env, block_unres = pres_equation_list_block block_utils block_env else_block in
	resolve_unres block_utils new_block_env block_unres

and pres_present utils env phl else_opt =
	
	let presentNode, present_env, present_unres, present_utils, outer_present_output = init_block utils (Env_build.build_present utils (phl,else_opt)) env Present in

	let priorities = List.init (List.length phl) (fun id -> string_of_int (id + 1)) in
	List.iter2 (fun ph prio -> 
		pres_present_handler ~prio:prio present_utils present_env ph 
	) phl priorities;
	begin match else_opt with
	| None -> ()
	| Some b -> pres_else_handler present_utils present_env b
	end;
	let new_env = {env with input_env = Zident.Env.union (fun id a1 a2 -> Some a1) env.input_env outer_present_output} in
	new_env , present_unres

and pres_automaton utils env (is_weak, state_handlers, init_opt) eq =
	let autOpNode, aut_env, aut_unres, inner_utils, outer_automaton_output = init_block utils (Env_build.build_eq utils eq) env Aut in

	let state_name statepat = 
		match statepat.desc with
		| Estate0pat n -> n
		| Estate1pat (n,_) -> n
	in


	let first_state = state_name (List.hd state_handlers).s_state in
	let init_state =
		match init_opt with
		| None -> first_state
		| Some se ->
			begin match se.desc with
			| Estate0 id -> id
			| Estate1 (id,_ ) -> id
			end
	in

	let pres_state utils state_handler =
		
		let name = Format.asprintf "%a" Special_printer.statepat state_handler.s_state in	
		
		let init = (state_name state_handler.s_state) = init_state in
		let stateNode, state_env, state_unres, state_utils, _ = init_block ~is_aut_state:true inner_utils (Env_build.build_state_handler_body utils state_handler) aut_env (Aut_state (name, init)) in
		assert (state_unres = []);
		let new_state_env, unres = pres_equation_list_block state_utils state_env state_handler.s_body in
		resolve_unres state_utils new_state_env unres;
		if init then begin
			let invNode = mkOpNode InvState	inner_utils.function_node inner_utils.layer in
			let cont = match init_opt with
			| None -> Format.asprintf "%a" Special_printer.statepat state_handler.s_state
			| Some se -> Format.asprintf "%a" Special_printer.state se
			in
			automaton_edge ~inline:(!Zmisc.do_viz_inline_aut) ~half:true invNode stateNode cont true true
		end;
		stateNode
	in
	let state_env = List.fold_left (fun state_env s ->
		Zident.Env.add (state_name s.s_state) (pres_state inner_utils s) state_env) Zident.Env.empty state_handlers
	in

	List.iteri (fun num s ->
		let do_transition escape = 
			
			let source = state_name s.s_state in
			let target = match escape.e_next_state.desc with
			| Estate0 n -> n
			| Estate1 (n,_) -> n
			in
			let transition_cond = (string_of_int (num+1))^" : "^(Format.asprintf "%a" Special_printer.scondpat escape.e_cond) in
			let transition_target = Format.asprintf "%a" Special_printer.state escape.e_next_state in
			let transition_op = match 
				escape.e_block with
				| None -> ""
				| Some b -> Format.asprintf "%a" (Special_printer.block_equation_list "" "") b 
			in
			if !Zmisc.do_aut_transition && transition_op <> "" then begin
				let transNode, trans_env, transUnres, trans_utils,_ = init_block inner_utils (Env_build.build_aut_transition utils escape.e_block) aut_env (BlanckFct NONE) in
				assert (transUnres = []);
				automaton_edge ~inline:(!Zmisc.do_viz_inline_aut) ~half:true ~first:true (Zident.Env.find source state_env) transNode (transition_cond) false (not is_weak);
				automaton_edge ~inline:(!Zmisc.do_viz_inline_aut) ~half:true transNode (Zident.Env.find target state_env) (transition_target) escape.e_reset (not is_weak);
				match escape.e_block with
				| None -> assert false
				| Some b -> 
					let new_env, unres = pres_equation_list_block trans_utils trans_env b in
					resolve_unres trans_utils new_env unres
			end else begin
				let transition_content = 
					transition_cond^" / \n "^transition_target^" / \n "^transition_op	
				in
				let transition_content = Special_printer.endl_characters transition_content in
				automaton_edge ~inline:(!Zmisc.do_viz_inline_aut) (Zident.Env.find source state_env) (Zident.Env.find target state_env) transition_content escape.e_reset (not is_weak)
			end
		in
		List.iter do_transition s.s_trans)
	state_handlers;
	(*Format.printf "%d %d@." (Zident.Env.cardinal output_env) (Zident.Env.cardinal input_env);
	Format.printf "%d @." (Zident.Env.cardinal env.input_env);*)
	let new_input_env = Zident.Env.union (fun id v1 v2 -> Some v1) env.input_env outer_automaton_output in
	(*Format.printf "new %d @." (Zident.Env.cardinal new_input_env); *)
	{env with input_env = new_input_env} , aut_unres

and pres_match_handler id utils env match_handler = 
	let name = Format.asprintf "%d : %a" id Special_printer.pattern match_handler.m_pat in
	
	let matchNode, match_env, match_unres, match_utils,_ = init_block ~is_match:true utils (Env_build.build_match_handler utils match_handler) env (Match_state name) in
	assert (match_unres = []);
	let new_match_env, unres = pres_equation_list_block match_utils match_env match_handler.m_body in
	resolve_unres match_utils new_match_env unres


and pres_match utils env (cond, match_handlers) = 
	let matchOpNode, match_env, match_unres, match_utils, outer_match_output = init_block ~control:true utils (Env_build.build_match_block utils match_handlers) env Match_node in
	let match_utils = {match_utils with in_match=true} in
	List.iteri (fun i mh ->
		pres_match_handler (i+1) match_utils match_env mh) match_handlers;

	let condOut, cond_unres, env = pres_exp utils env cond in
	assert (List.length condOut = 1);
	let cond_unres = try_edge cond_unres Simple (List.hd condOut) (Endpoint (outerToEndPoint (List.hd matchOpNode#getControl))) in

	let new_input_env = Zident.Env.union (fun id v1 v2 -> Some v1) env.input_env outer_match_output in
	{env with input_env = new_input_env}, (match_unres @ cond_unres)


and pres_reset_block utils env (eql, reset_e) = 
	let resetOpNode, reset_env, reset_unres , reset_utils, outer_reset_output = 
		init_block ~addI:[mk_addPort North] ~addO:[mk_addPort North] utils (Env_build.build_reset_block utils (eql,reset_e)) env Reset in 	
	let resetSource = outerToEndPoint (List.hd resetOpNode#getOutputs) in
	let resetTarget = outerToEndPoint (List.hd resetOpNode#getInputs) in
	let label = new iEdgeLabel (Format.asprintf "%a" Special_printer.expression reset_e) in
	new_edge ~lab:(Some label) Aut_port  resetSource resetTarget;
	
	let new_reset_env, unres = List.fold_left (fun (env,unres) eq ->
		let new_env, new_unres = pres_equ reset_utils env eq in
		new_env, unres @ new_unres) (reset_env,[]) eql
	in
	resolve_unres reset_utils new_reset_env unres;
	let new_input_env = Zident.Env.union (fun id v1 v2 -> Some v1) env.input_env outer_reset_output in
	let new_env = {env with input_env = new_input_env} in
	new_env, reset_unres

and pres_forall utils env forall_handler =
	
	let pres_inputs_index index (env,unres,endL) = 
		match index.desc with
		| Einput (id, e) ->
			let endPoints, e_unres, new_env = pres_exp utils env e in
			assert (List.length endPoints = 1);
			let endPoint = List.hd endPoints in
			(new_env, e_unres @ unres, (id, endPoint) :: endL)
		| Eoutput _ ->
			(env,unres,endL)
		| Eindex (id,e1,e2) ->
			let dotNode = mkOpNode (Text ("..",2)) utils.function_node utils.layer in
			let (unres,env) = map_exp_port utils env [] [e1;e2] (dotNode#getInputs) in
			let out = List.hd (dotNode#getOutputs) in
			(env, unres, (id,Endpoint (outerToEndPoint out))::endL)
	in

	let env, unres, inList = List.fold_right pres_inputs_index forall_handler.for_index (env,[],[]) in
	let in_input_vars, _ = List.split inList in
	let in_input_vars_set = Zident.S.of_list in_input_vars in

	let pres_outputs_index index (env,unres,endL) = 
		match index.desc with
		| Eoutput (id_in, id_out) ->
			(env, unres, (id_in, id_out) :: endL)
		| _ ->
			(env,unres,endL)
	in
	
	let env, unres, outList = List.fold_right pres_outputs_index forall_handler.for_index (env,unres,[]) in
	
	let in_output_vars, _ = List.split outList in
	let in_output_vars_set = Zident.S.of_list in_output_vars in

	let block_build_env = Env_build.build_eq_list_block utils forall_handler.for_body in
	
	let block_build_env = 
		{Env_build.inputs = Zident.S.diff block_build_env.inputs in_input_vars_set;
		const_inputs = Zident.S.diff block_build_env.const_inputs in_input_vars_set;
		outputs = Zident.S.diff block_build_env.outputs in_output_vars_set;
		const_outputs = Zident.S.diff block_build_env.const_outputs in_output_vars_set
	} in
	
	let addI = List.map (fun id -> mk_addPort ~name:(Format.asprintf "%a" Special_printer.name id) Input) in_input_vars in
	let addO = List.map (fun id -> mk_addPort ~name:(Format.asprintf "%a" Special_printer.name id) Output) in_output_vars in

	let forOpNode, for_env, for_unres, for_utils, for_output = 
		init_block ~addI:addI ~addO:addO utils block_build_env env Forall in

	let rec first_n n l = 
		match n, l with
		| 0 , _ -> []
		| _ , x :: q -> x :: (first_n (n-1) q)
		| _ -> assert false
	in

	let for_input_env, for_unres = 
		List.fold_right2 (fun (id, endP) outer (input_env,unres) ->
			let unres = try_edge unres Simple endP (Endpoint (outerToEndPoint outer)) in
			Zident.Env.add id (outerToEndPoint outer) input_env, unres
		) inList (first_n (List.length inList) forOpNode#getInputs) (for_env.input_env, for_unres)
	in
	
	let for_output_env, for_output,for_unres = 
		List.fold_right2 (fun (id_in, id_out) outer (output_env, for_output,unres) ->
			let unres = try_edge ~nec:false unres Simple (Endpoint (outerToEndPoint outer)) (Ident id_out) in

			let outEndPoint = outerToEndPoint outer in
			addLabelEndPoint outEndPoint id_out; (* add label outside for defined variable in forall *) 
			Zident.Env.add id_in (outerToEndPoint outer) output_env, 
			Zident.Env.add id_out outEndPoint for_output,
			unres
		) outList (first_n (List.length outList) forOpNode#getOutputs) (for_env.output_env, for_output,for_unres)
	in	
	let for_env = {input_env = for_input_env;
		output_env = for_output_env;
		reg_env = for_output_env;
		init_env = for_env.init_env}
	in

	let block_env, block_unres = pres_equation_list_block for_utils for_env forall_handler.for_body in
	resolve_unres for_utils block_env block_unres;
	
	let new_input_env = 
		Zident.Env.union (fun id a1 a2 -> Some a1) env.input_env for_output in
	{env with input_env = new_input_env}, for_unres @ unres

and implementation parent impl layer = 
	match impl.desc with
	| Efundecl (f,body) ->
		let input_names = List.map (fun pat -> Format.asprintf "%a" Special_printer.pattern pat) body.f_args in
		let output_names = [""] in (*Array.to_list (Array.make (typ_to_number body.f_body.e_typ) "") in  *)
		(*let input_namesPorts = List.map (fun id -> mk_portRequest id) input_names in
		let output_namesPorts = List.map (fun id -> mk_portRequest id) output_names in*)
		let fctNode = mkFunctionNode ~order:true (Fct f) input_names output_names parent layer in	
		let utils = {
			function_name = f;
			in_present=false;
			layer = layer  + 1; 
			function_node = fctNode;
			in_reg=false;
			count_block = Count_env.count_funexp body;
			in_match=false;
		} in
		let ends = List.map2 (fun pat outer ->
			let endPoint = outerToEndPoint outer in
			if pat.p_desc = Econstpat (Evoid) then
				[]
			else begin
				let res , _ (*no unres here*) = pres_pattern utils empty_env (Endpoint endPoint) pat in
				let inner_endPoints , _ = List.split res in
				List.iter (fun en -> outer#addInnerPort en) inner_endPoints;
				res
			end
		) body.f_args fctNode#getInputs in
	
		let box_inputs = List.fold_right (fun l acc ->
			let _ , ids = List.split l in
			let ids = List.map (fun id -> Format.asprintf "%a" Special_printer.name id) ids in
			ids @ acc
		) ends [] in
	
		(*let box_inputsPorts = List.map (fun id -> mk_portRequest id) box_inputs in *)
		let box_outputs = [""] in
		(*let box_outputsPorts = List.map (fun id -> mk_portRequest id) box_outputs in *)
		let boxNode = mkFunctionNode ~vis:false Inv box_inputs box_outputs (Node fctNode) utils.layer in

	
		let (input_env , _) = List.fold_left (fun (env , outer_inputs) pl ->
			List.fold_left (fun (env,outer_inputs) (endP , id) ->
				let outer_input = List.hd outer_inputs in
				let outer_inputs = List.tl outer_inputs in

				let _ = endP#eatLabels in
				new_edge Simple endP (outerToEndPoint (outer_input));	
				let env = Zident.Env.add id (outerToEndPoint outer_input) env in
				(env,outer_inputs)
			) (env , outer_inputs) pl)
			(Zident.Env.empty , boxNode#getInputs) ends
		in
	
		List.iter2 (fun boxOuter fctOuter ->
			new_edge Simple (outerToEndPoint boxOuter) (outerToEndPoint fctOuter))
			boxNode#getOutputs fctNode#getOutputs;

		let utils = {
			function_name = f;
			in_present=false;
			layer = utils.layer + 1; 
			function_node = boxNode; 
			in_reg = false; 
			count_block = utils.count_block;
			in_match=false;
		} in
		let env = {input_env = input_env ; output_env = Zident.Env.empty ;reg_env = Zident.Env.empty; init_env = Zident.Env.empty} in
		let outs, unres, env  = pres_exp ~first:true utils env body.f_body in
		let unres = List.fold_right2 (fun endPoint outer unres ->
			let target = outerToEndPoint outer in
			try_edge unres Simple endPoint (Endpoint target) 
		) outs boxNode#getOutputs unres in
		resolve_unres utils env unres;
		List.iter2 (fun name outer ->
			let port = outer#getPort in
			if List.length port#getEdges = 0 then(*input point is not connected to anything*) begin
				let sinkNode = mkOpNode (Sink (name,false)) utils.function_node utils.layer in
				new_edge Simple (outerToEndPoint outer) (outerToEndPoint (List.hd sinkNode#getInputs))
			end
		) box_inputs boxNode#getInputs;
		Some fctNode
	| _ -> None

let implementation_list impl_list file =
	let file = String.capitalize_ascii file in
	filename := file;
	Special_printer.filename := file;
	let ig = new iGraph in 
	List.iter (fun impl ->
		match impl.desc with
		| Efundecl (f,body) ->
			Hashtbl.add function_code f impl;
			Hashtbl.add Simple_expression.node_names f 42;
			Hashtbl.add function_parameters f (List.length body.f_args) 
		| _ -> ()) impl_list;
	List.iter (fun impl ->
		match impl.desc with
		| Efundecl (f,_) ->
			if !Zmisc.do_viz_only_fun = "" || f = !Zmisc.do_viz_only_fun then
				ignore (implementation (Graph ig) impl 0)
		| _ -> ()
	) impl_list;

	ig
