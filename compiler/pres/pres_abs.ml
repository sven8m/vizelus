open Zelus
open Knode
open Mk_intermediate
open Intermediate_graph
open Utils_def
open Viz2_utils

module StringEnv = Map.Make (struct type t = string let compare = compare end)
			
let empty_exp = {
	e_desc = Econst (Evoid);
	e_loc = Zlocation.no_location;
	e_typ = Deftypes.no_typ;
	e_caus = Defcaus.no_typ;
	e_init = Definit.no_typ;
}

let function_code = Hashtbl.create 42
let function_parameters = Hashtbl.create 42

let filename = ref ""

type myAddPort = {
	look : Intermediate_graph.portLook option;
	side : Intermediate_graph.portSide;
	name : string;
	id : Zident.t option;
}

let mk_myAddPort ?(corId) ?(name="") ?(look) side =
	{side=side;name=name;id = corId;look=look}


type endPoint_type = 
	| Ident of Zident.t
	| Endpoint of iEndPoint

type return_type = 
	{endPoint : endPoint_type; edge_type : edge_type}

let mk_rt ?(et=Simple) endP = 
	{endPoint = endP; edge_type = et}

(* edges to be added afterwards *)
type unresolved = {
	edge_type : edge_type;
	insideSelf : bool;
	source : Zident.t;
	target : iEndPoint
}

let mk_unres ?(iS=false) ?(et=Simple) source target = 
	{edge_type = et; source = source; target = target; insideSelf=iS}

type env = {
	input_env : (Intermediate_graph.iEndPoint list) Zident.Env.t;
	output_env : (Intermediate_graph.iEndPoint list) Zident.Env.t;
}

let fct_union = fun id a1 a2 -> Some (a1@ a2)


type acc = {
	exitNode : Intermediate_graph.iNode;
	unres : unresolved list;
	env : env;
}


(** [try_edge unres rt_source target] creates an edge from source to target if [rt_source] is an endPoint, else creates an unresolved element *)
let try_edge ?(edge_type) ?(insideSelf=false) unres (rt_source : return_type) target = 
	let edge_type = match edge_type with
	| None -> rt_source.edge_type
	| Some et -> et
	in
	match rt_source.endPoint with
	| Ident id ->
		(mk_unres ~iS:insideSelf ~et:edge_type id target) :: unres
	| Endpoint source ->
		new_edge ~insideSelf:insideSelf edge_type source target; unres

(** [resolve_unres utils env unres] creates the unresolved edges and defined nodes in the environment that have no out connection are given a sink node.
It is called when finishing working on a block. *)
let resolve_unres utils env unres = 
	List.iter (fun unres ->
		let inputs = match Zident.Env.find_opt unres.source env.input_env with
		| None ->
			let constNode = mkOpNode (Const (Format.asprintf "%a" Special_printer.name unres.source , false)) utils.function_node utils.layer in
			[outerToEndPoint (List.hd constNode#getOutputs)]
		| Some l -> l
		in

		List.iter (fun source ->
			new_edge ~insideSelf:unres.insideSelf unres.edge_type source unres.target) inputs
	) (List.sort_uniq compare unres);

	let _ = Zident.Env.fold (fun id endPoints env ->
		List.fold_left (fun env endPoint ->
			let isAlone = List.length (endPoint#getPort#getEdges) = 0 in
			if isAlone then begin
				let targets,env = match Zident.Env.find_opt id env.output_env with
				| None ->
					let sinkNode = mkOpNode (Sink (Format.asprintf "%a" Special_printer.name id, false)) utils.function_node utils.layer in
					let new_env = Zident.Env.singleton id [outerToEndPoint (List.hd sinkNode#getInputs)] in 
					[outerToEndPoint (List.hd sinkNode#getInputs)], {env with output_env = Zident.Env.union fct_union env.output_env new_env}
				| Some ptl -> ptl,env
				in
					
				List.iter (fun target ->
					new_edge Simple endPoint target) targets;
				env
			end else env
		) env endPoints
	) env.input_env env 
	in
	()

(** [map_outputs node] returns a list consisting of the output endPoints of [node] *)
let map_outputs node = 
	List.map (fun outer_output ->
		let endP = outerToEndPoint outer_output in
			mk_rt (Endpoint endP))
 		node#getOutputs

(** [decompose_exp e] returns a list of expressions by flattening the sub-expressions of a given mathematical expression *)
let rec decompose_exp ?(no_void=false) e = 
	match e.e_desc with
	| _ when Simple_expression.still_const e ->
		[e]
	| Elet _ ->
		[e]
	| Eapp _ when (exp_is_function e) -> 
		[e]
	| Eblock _ ->
		[e]
	| Eapp (_,_,el) ->
		List.fold_right (fun e acc ->
			(decompose_exp ~no_void:no_void e) @ acc) el []
	| Etuple el ->
		[e]
	| Eop (op,el) when op <> Eifthenelse ->
		List.fold_left (fun acc e ->
			acc @ (decompose_exp ~no_void:no_void e)) [] el
	| Eseq (e1,e2) ->
		[e]	
	| _ -> [e]

(** [pres_exp_decomposed utils acc e] calculates the intermediate graph corresponding to the expression [e].

	Returned is [endsL,acc] where [endsL] a list which length corresponds to the number of expected returning values the expression [e] has.

	Each element consists itself of a list of endPoints which are the dependencies the returned value has.

	[acc] is the new accumulator with updated unresolved edges, environment and the exitNode being the last node defining an equation *)
let rec pres_exp_decomposed ?(no_void=false) ?(patEq=None) utils (acc : acc) e = 
	let fct_name = get_exp_fct_name e in
	match e.e_desc with
	| _ when (is_void e) && no_void ->
		(* when the expression is the void and we don't want the void we do nothing *)
		[], acc
	| Etuple el -> (* tuples at first *)
		(* we visualize each expression of the tuple separately *)
		let (endsE, acc) = List.fold_left (fun (endsEList, acc) e ->
			let endsE, acc = pres_exp utils acc e in
			(* here we have more expected output values, so we add them to the list of list *)
			(endsEList @ endsE, acc)) ([],acc) el
		in
		endsE, acc

	| _ when Simple_expression.still_const e ->
		(* a constant expression is visualized with a Const node and it outgoing edge is dashed.
		It is here supposed that [e] returns only one value. *)
		if !Zmisc.do_viz2_no_const then
			[], acc
		else
			let constNode = mkOpNode (Const (Format.asprintf "%a" Special_printer.expression e, false)) utils.function_node utils.layer in
			[[mk_rt ~et:Dash (Endpoint (outerToEndPoint (List.hd constNode#getOutputs)))]] , {acc with exitNode = constNode}	
	| Elet (local,e_out) ->
		(* we first calculate the visualization for the local definitions and then the visualization of the expression [e_out] *)
		let new_acc = pres_local utils acc local in
		pres_exp ~no_void:no_void utils new_acc e_out
	| Eapp (_,fct,args) when (exp_is_function e) && (exp_is_true_function_call e) && 
		(Hashtbl.mem function_code fct_name) && (num_parameters fct.e_typ = (List.length (get_fct_args e))) &&
		(fct_name <> utils.function_name) ->
		(* case for the true function calls *)
		(* it is supposed that the function name is the name of a zelus node in the source code, that we have the expected number of parameters 
		and that this is not a recursive endless call *)

		(* we first visualize the function that is called *)
		let fct_name = get_exp_fct_name e in
		let opNode= match implementation ~patEq:patEq (utils.function_node) (Hashtbl.find function_code fct_name) (utils.layer + 1) with
		| None -> assert false;
		| Some a -> a
		in
		
		let pat_function_list = 
			match (Hashtbl.find function_code fct_name).desc with
			|  Efundecl (_,fct) -> fct.f_args
			| _ -> assert false
		in
	
		(* we get the expressions for each input of the call, by flattening the tuples *)
		let input_expressions = 
		List.fold_left2 (fun acc p1 e1 -> acc @ (split_and_flatten_e p1 e1)) [] pat_function_list (get_fct_args e)
		in
		(* we visualize each argument and connect it to the input of the function *)
		let new_acc = List.fold_left2 (fun acc exp outerTarget ->
			let target = (outerToEndPoint outerTarget) in
			let ends_e , new_acc = pres_exp utils acc exp in
			let ends_e = List.flatten ends_e in 
			(* we have flattened the input expressions, so we expect only one value to be returned *) 
			let new_unres = List.fold_left (fun unres rt ->
				try_edge unres rt target
			) new_acc.unres ends_e
			in
			{new_acc with unres = new_unres})
		acc input_expressions opNode#getInputs
		in
		
		let new_acc = {new_acc with (*unres = control_unres @ new_acc.unres ;*) exitNode = opNode} in
		List.map (fun el -> [el]) (map_outputs opNode), new_acc

	| Eapp (_,fct,_) when (exp_is_function e)  && (num_parameters fct.e_typ <> List.length (get_fct_args e)) (*&& (Hashtbl.mem function_code fct_name) *) ->
		(* The case of a partial application where we don't have enough arguments. We only do a textual visualization of the content *)

		let inputs = (Env_build.build_exp utils e).inputs in
		
		let textNode = mkOpNode (Text (Format.asprintf "%a" Special_printer.expression e, Zident.S.cardinal inputs)) utils.function_node utils.layer in
		let unres = List.fold_left2 (fun unres id target ->
			let rt = mk_rt (Ident id) in
			try_edge unres rt (outerToEndPoint target)
		) [] (Zident.S.to_list inputs) (textNode#getInputs)
		in
		List.map (fun el -> [el]) (map_outputs textNode), {acc with unres = acc.unres @ unres ; exitNode = textNode}
	
	| Eapp (_,fct,el) when (exp_is_function e) ->
		(*extern function coming from stl for example, or when [fct] was itself a partial application *) 
		let node_type = (Fct fct_name) in

		let addI = List.init (List.length el) (fun _ -> mk_myAddPort Input) in	
		let addO = List.init (numOutputs e.e_typ) (fun _ -> mk_myAddPort Output) in
			
		(* we create a node for the application, but no intern visualization as it is not possible to know what there should be inside *)
		(* we also suppose that there are no inputs or outputs to flatten *)
		let opNode, _, _ , _ , _ = init_block ~order:true ~addI:addI ~addO:addO utils Env_build.empty_env acc.env node_type in
		opNode#setEnoughSize true;	

		(* we connect the different argument expression to the input of the function *)
		let acc = List.fold_left2 (fun acc exp outer_target ->
			let target = (outerToEndPoint outer_target) in
			let endsE, acc = pres_exp utils acc exp in
			let endsE = List.flatten endsE in
			(* we here suppose that there is only on returned value *)
			let new_unres = List.fold_left (fun unres rt ->
				try_edge unres rt target
			) acc.unres endsE
			in 
			{acc with unres = new_unres}
		) acc el opNode#getInputs
		in
		let new_acc = {acc with exitNode = opNode} in
		List.map (fun el -> [el]) (map_outputs opNode), new_acc

	| Eblock (eqlb , e_after) ->
		(* we first visualize the block then the expression *)
		let new_acc = pres_block utils acc eqlb in
		pres_exp ~no_void:no_void utils new_acc e_after
	| Eseq (e1,e2) ->
		let _, acc = pres_exp utils acc e1 in (*return type should be unit *)
		pres_exp utils acc e2
	| Eop (Eifthenelse, el) ->
		(* special case for the ifthenelse, to duplicate the conditin on each output *)
		let cond = List.hd el in
		let exps = List.tl el in
		let e1 = List.hd exps in
		let e2 = List.hd (List.tl exps) in
		let endsCond, acc=  pres_exp ~no_void:no_void utils acc cond in
		let endsE1, acc = pres_exp ~no_void:no_void utils acc e1 in
		let endsE2, acc = pres_exp ~no_void:no_void utils acc e2 in

		let endsCond = List.flatten endsCond in (*type should be one output *)
		let endsCond = List.init (List.length endsE1) (fun _ -> endsCond) in
	
		let endsE = List.fold_left (fun l ends ->
			List.map2 (fun e1 e2 -> e1 @ e2) l ends) endsCond [endsE1;endsE2]
		in
		endsE, acc
	| _ ->
		(* in other cases we on only gather the variables on which the expression depends *)
		let inputs = (Env_build.build_exp utils e).inputs in
		let rts = Zident.S.fold (fun id l ->
			(mk_rt (Ident id)) :: l)
			inputs []
		in
		let numOuts = numOutputs e.e_typ in
		(* we duplicate the endPoints to have the right numbers of expected returned values *)
		List.init numOuts (fun _ -> rts) , acc


(* [pres_exp utils acc e] creates the visualization of [e] as in [pres_exp_decomposed] but the expression can 
still consist of mathematical operators *)
and pres_exp ?(no_void=false) ?(patEq=None) utils (acc : acc) e =
	let inner_exps = decompose_exp ~no_void:no_void e in
	if List.length inner_exps = 1 then begin
		(* there was no leading mathematical operator *)
		pres_exp_decomposed ~no_void:no_void ~patEq:patEq utils acc (List.hd inner_exps)
	end else begin
		(* the expression cannot be a constant and therefore should depend on some variables, thus we don't show the constant values *)
		let no_consts = List.filter (fun e -> not (Simple_expression.still_const e)) inner_exps in
		if List.length no_consts = 1 then begin
			pres_exp_decomposed ~no_void:no_void utils acc (List.hd no_consts)
		end else begin
			(* each decomposed expression is supposed to have the same number of expected return values, so we add each of them *) 
			let endsList, acc = List.fold_left (fun (endsList, acc) e ->
				let ends,acc = pres_exp_decomposed ~no_void:no_void utils acc e in
				if endsList = [] then
					(ends , acc)
				else begin
					assert (List.length endsList  = List.length ends);
					let endsList = List.map2 (fun el1 el2 -> el1 @ el2) endsList ends in
					endsList , acc
				end
			) ([],acc) no_consts
			in
			endsList, acc
		end
	end

(** [pres_equ_with_node utils acc pats e node_type] creates the visualization of an equation with a node of the given [node_type], 
where outputs are linked in the environment to the variables in [pats] and inputs are the different dependencies that occures in the expression.
We create one box for each different variable in the pattern. *)
and pres_equ_with_node ?(init_eq=false) ?(control=false) utils acc pat_list exp node_type = 
	let endsE, acc = pres_exp ~no_void:true utils acc exp in

	let acc,_ = List.fold_left (fun (acc, (endsList : return_type list list)) pat ->
		(*print_tys pat.p_typ;*)
		let numValues = numOutputs pat.p_typ in
		let endsE, endsList = eatN numValues endsList in
		let endsE = List.flatten endsE |> (List.sort_uniq compare) in
		let outputs = Find_vars.find_vars_pattern pat in
		
		let addI = List.init (List.length endsE) (fun _ -> mk_myAddPort Input) in
		(* creation of the node *)
		let opNode,_,_,to_add,_ = init_block ~addI:addI ~control:control utils {Env_build.empty_env with outputs = outputs} acc.env node_type in
		opNode#setEnoughSize true;

		(* we connect each endPoint dependency to the inputs of the node *)
		let unres_to_add = List.fold_left2 (fun unres rt outer_target ->
			if init_eq then
				try_edge ~edge_type:Dash unres rt (outerToEndPoint outer_target)
			else
				try_edge unres rt (outerToEndPoint outer_target)
		) [] endsE opNode#getInputs
		in
		let env = {acc.env with input_env = Zident.Env.union fct_union acc.env.input_env to_add.output_env} in
		({exitNode = opNode; env = env ; unres = unres_to_add @ acc.unres} , endsList)
	) (acc,endsE) pat_list
	in
	acc

(** [pres_equ utils acc equ] creates the visualization of an equation *)
and pres_equ utils (acc : acc) equ = 
	match equ.eq_desc with
	| EQeq (pat , e) ->
		if (not (exp_is_function e)) then begin
			(* basic equation that isn't a function call *)
			(* we suppose that the pattern consists of only one variable (else it is not very pretty *)
			let node_type = (Text ("=",1(*number irrelevant*))) in
			
			pres_equ_with_node utils acc (split_pat pat) e node_type 
	
		end else begin
			(* in the case of a function call, we want to link the function outputs to the pattern variables in the environment *)
			let endsE , acc = pres_exp ~patEq:(Some pat) utils acc e in	
			let output_names = Find_vars.find_vars_pattern_order (*~mult:true*) pat in
			
			if (List.length endsE = 0 &&  isVoidType (e.e_typ)) then
				acc 
			else begin
				assert (List.length endsE = List.length output_names);
				let new_input_env = List.fold_left2 (fun input_env id rt ->
					let rt = List.hd rt in
					if Zident.source id <> "" then begin
						let lab = edgeLabel (Format.asprintf "%a" Special_printer.name id) in
						match rt.endPoint with
						| Ident _ -> assert false
						| Endpoint endP ->
							endP#addLabel lab;
							let env1 = Zident.Env.singleton id [endP] in
							Zident.Env.union fct_union input_env env1
					end else input_env
				) Zident.Env.empty output_names endsE
				in
				let new_env = {acc.env with input_env = Zident.Env.union fct_union new_input_env acc.env.input_env} in
				{acc with env = new_env}
			end
		end
		
	| EQder (id, der, init_opt, resets_list) ->
		let acc = if !Zmisc.do_viz2_show_init then
			match init_opt with
			| None -> acc
			| Some e ->
				let node_type = Text ("init",1) in
				pres_equ_with_node ~init_eq:true utils acc [create_var_pat id e] e node_type
			else
				acc
		in
		let node_type = (Der ("", if resets_list <> [] then 1 else 0)) in
		
		let resetEndL, acc = List.fold_left (fun (endL,acc) reset ->
			let ends, acc = pres_scondpat utils acc reset.p_cond in
			endL @ (List.flatten ends) , acc )
			([], acc) resets_list
		in

		let acc = pres_equ_with_node utils acc [create_var_pat id der] der node_type in
		(* we connect the variables on which a reset has a condition *)
		
		if resets_list <> [] then begin
			addResetBegin ~look:HalfCircle ~side:Control acc.exitNode;
			let target = (outerToEndPoint (List.hd acc.exitNode#getControl)) in
			let unres = List.fold_left (fun unres source_endP ->
				try_edge unres source_endP target)
				acc.unres resetEndL
			in
			{acc with unres = unres}
		end else
			acc
	| EQemit (id, e_opt) ->
		let node_type = (Emit "") in
		let exp = match e_opt with
		| None ->
			empty_exp
		| Some exp -> exp
		in
		pres_equ_with_node utils acc [create_var_pat id exp] exp node_type
	| EQnext (id,e,init_opt) ->
		let node_type = (Next "") in
		pres_equ_with_node utils acc [create_var_pat id e] e node_type
	| EQpluseq (id,e) ->
		let node_type = Text ("+=", 1) in
		pres_equ_with_node utils acc [create_var_pat id e] e node_type
	| EQpresent (phl,b_opt) -> pres_present utils acc (phl,b_opt)
	| EQblock eqlb -> pres_block ~no_node:true utils acc eqlb 
	| EQand eql | EQbefore eql ->
		List.fold_left (pres_equ utils) acc eql
	| EQautomaton (is_weak,shl,init_state_opt) ->
		pres_automaton utils acc (is_weak,shl,init_state_opt) equ
	| EQinit (id, e) ->
		if !Zmisc.do_viz2_show_init then
			let node_type = Text ("init",1) in
			pres_equ_with_node ~init_eq:true utils acc [create_var_pat id e] e node_type
		else
			acc
	| EQforall forall_handler ->
		pres_forall utils acc forall_handler 
	| EQmatch (_,cond , match_handlers) ->
		pres_match utils acc (cond, match_handlers)
	| EQreset (eql,res_e) -> 
		pres_reset_block utils acc (eql, res_e)

(** [pres_local utils acc local] creates the visualization for [local] 

We only do the visualization of each equation separately. *)
and pres_local utils acc local = 
	List.fold_left (pres_equ utils) acc local.l_eq

(** [pres_block utils acc block] creates the visualization for a block [block] 
Depending on the options, we create a physical block in which we visualize each equation of the block, or we forget about the block. *)
and pres_block ?(no_node=false) ?(has_control=false) ?(forced_const=Zident.S.empty) utils (acc : acc) block = 
	let build_env = Env_build.build_eq_list_block utils block in
	let no_node = no_node || (!Zmisc.do_viz2_less && Count_eq.count_block block <= 1) || (!Zmisc.do_viz2_less && (not has_control)) in
	(* no_node says if there should be a box englobing the entire block *)
	let build_env_inputs = Zident.S.diff build_env.inputs forced_const in
	let build_env_const_inputs = forced_const in
	let build_env = {Env_build.empty_env with inputs = build_env_inputs; const_inputs = build_env_const_inputs; outputs = build_env.outputs} in	
	let fctNode, fct_unres, unres, fct_env, fct_utils = 
		if no_node then
			utils.function_node, [], [],acc.env, utils
		else begin
			init_block utils build_env acc.env (BlanckFct SIDE)
		end
	in

	(* visualize the inside of the block *)
	let inner_acc =  
		List.fold_left (
			pres_local fct_utils
		) {env = fct_env; unres = unres;exitNode=fctNode} block.b_locals 
	in
	let inner_acc = 
		List.fold_left (
			pres_equ fct_utils
		) inner_acc block.b_body in

	if not no_node then
		resolve_unres fct_utils inner_acc.env inner_acc.unres;
	
	let exitNode = if no_node then inner_acc.exitNode else fctNode in

	let new_env = 
		if no_node then inner_acc.env
		else {acc.env with input_env = Zident.Env.union fct_union fct_env.output_env acc.env.input_env} in
	
	let inner_unres = if no_node then inner_acc.unres else [] in
	{exitNode=exitNode; unres = acc.unres @ fct_unres @ inner_unres; env = new_env}

(** [pres_controls controlEnds node unres] visualize the control outputs of a given node.
Depending on the option there is only one control port on the node or one for each return value of [controlEnds]. *)
and pres_controls controlEnds node unres = 
	if !Zmisc.do_viz2_true_no_hyper_present then
		let controlEnds = List.flatten controlEnds in
		List.fold_left2 (
			fun unres endP outer_target ->
				let target = outerToEndPoint outer_target in
				try_edge unres endP target
			) unres controlEnds (first_n (List.length controlEnds) node#getControl)
	else if !Zmisc.do_viz2_no_hyper_present then
		List.fold_left2 (
			fun unres endsList outer_target ->
				let target = outerToEndPoint outer_target in
				List.fold_left (fun unres endP ->
					try_edge unres endP target)
					unres endsList
			) unres controlEnds (first_n (List.length controlEnds) node#getControl)
	else
		let controlEnds = List.flatten controlEnds in
		let target = (outerToEndPoint (List.hd node#getControl)) in
		List.fold_left (fun unres endP ->
			try_edge unres endP target) unres controlEnds	

(** [pres_scondpat utils acc scond] creates the visualization for a condition_pattern *)
and pres_scondpat utils acc scond = 
	match scond.desc with
	| Econdor (sc1,sc2) | Econdand (sc1,sc2) ->
		let ends1, acc = pres_scondpat utils acc sc1 in
		let ends2, acc = pres_scondpat utils acc sc2 in
		ends1 @ ends2, acc
	| Econdexp e ->
		let endsE, acc = pres_exp utils acc e in
		[List.flatten endsE], acc
	| Econdpat (e,_) ->
		let endsE, acc = pres_exp utils acc e in
		[List.flatten endsE], acc
	| Econdon (sc,e) ->
		let endsS, acc = pres_scondpat utils acc sc in
		let endsE, acc = pres_exp utils acc e in
		[(List.flatten endsS) @ (List.flatten endsE)] , acc

(** [pres_present utils acc (phl,b_opt)] creates the visualization for a present equation 
It is composed of a block for each present handler, which for each we have a control port with the dependencies of the condition.

The different present handlers are connected using a line. *)
and pres_present utils acc (phl,b_opt) =
	let exitNodes, acc = 
		List.fold_left (fun (exitNodes, acc) ph ->
			let endsControl,acc = pres_scondpat utils acc ph.p_cond in
		
			let patVars = Find_vars.findCondPatIds ph.p_cond in
			let acc = pres_block ~has_control:true ~forced_const:patVars utils acc ph.p_body in
			(* calculates the number of controls *)	

			let nbControls =
				if !Zmisc.do_viz2_true_no_hyper_present then
					max 1 (List.length (List.flatten endsControl))
				else if !Zmisc.do_viz2_no_hyper_present then max 1 (List.length endsControl) 
				else 1
			in
			for i = 1 to nbControls do
				addResetBegin ~look:HalfCircle ~side:Control acc.exitNode;
			done;

			let new_unres = pres_controls endsControl acc.exitNode acc.unres in 
			let new_acc = {acc with unres = new_unres} in
			(acc.exitNode :: exitNodes , new_acc)
		) ([] , acc) phl
	in
	(* connected the different present handlers *)
	let exitNodes, acc = match b_opt with
	| None -> exitNodes, acc
	| Some b -> 
		let acc = pres_block utils acc b in
		addResetBegin ~look:HalfCircle ~side:Control acc.exitNode;
		(acc.exitNode :: exitNodes , acc)
	in
	let exitNodes = List.rev exitNodes in
	
	let rec addLinks = function 
	| [] | [_] -> ()
	| firstNode :: secondNode :: q ->
		(* do something *)
		addResetBegin ~look:Visible ~side:South firstNode;
		addResetBegin ~look:Visible ~side:North secondNode;
		new_edge Dot (outerToEndPoint (List.hd firstNode#getControl)) (outerToEndPoint (List.hd secondNode#getControl)); 
		addLinks (secondNode :: q)
	in
	addLinks exitNodes;
	acc

(** [pres_automaton utils acc ... ] creates the visualization of an automaton equation. 
We only visualize the states and on the transitions between them only show the variables defined by the transition,
and visualize each state recursively inside. *)
and pres_automaton utils acc (is_weak, state_handlers,init_opt) eq = 
	
	let autOpNode, aut_unres, _ (*inner unres not used *),  aut_env, aut_utils = init_block utils (Env_build.build_eq utils eq) acc.env Aut in

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
		(* we visualize the content of the state recursively *)
		let name = Format.asprintf "%a" Special_printer.statepat state_handler.s_state in	
		
		let init = (state_name state_handler.s_state) = init_state in
		let stateNode, state_unres, inner_state_unres, state_env, state_utils = 
			init_block ~is_aut_state:true utils (Env_build.build_state_handler_body utils state_handler) aut_env (Aut_state (name, init)) in
		assert (state_unres = []);

		let state_acc = pres_block ~no_node:true state_utils {env = state_env; unres = inner_state_unres; exitNode = stateNode} state_handler.s_body in
		resolve_unres state_utils state_acc.env state_acc.unres;
		stateNode
	in
	let state_env = List.fold_left (fun state_env s ->
		Zident.Env.add (state_name s.s_state) (pres_state aut_utils s) state_env) Zident.Env.empty state_handlers
	in

	List.iteri (fun num s ->
		let do_transition escape = 
			(* we only show the condition and the variables defined during the transition *)	
			let source = state_name s.s_state in
			let target = match escape.e_next_state.desc with
			| Estate0 n -> n
			| Estate1 (n,_) -> n
			in
			let names_block = match escape.e_block with
			| None -> " "
			| Some b -> 
				Format.asprintf "%a" (Pp_tools.print_list_r Special_printer.name "" ", " "") ((Env_build.build_eq_list_block aut_utils b).outputs |> Zident.S.to_list)
			in
			
			let names_cond = Format.asprintf "%a" Special_printer.scondpat escape.e_cond in
			let trans_name = 
				names_cond^" / \n "^names_block
			in
			let trans_name = Special_printer.endl_characters trans_name in
			
			automaton_edge ~inline:(true) (Zident.Env.find source state_env) (Zident.Env.find target state_env) trans_name escape.e_reset (not is_weak)
		in
		List.iter do_transition s.s_trans)
	state_handlers;

	let new_input_env = Zident.Env.union fct_union acc.env.input_env aut_env.output_env in
	let env = {acc.env with input_env = new_input_env} in
	{exitNode = autOpNode; env = env; unres = acc.unres @ aut_unres}

(** [pres_forall utils acc forall_handler] *)
and pres_forall utils acc forall_handler =
		
	let pres_inputs_index (acc,endL) index = 
		match index.desc with
		| Einput (id, e) ->
			let endPoints, new_acc = pres_exp utils acc e in
			let endPoints = List.flatten endPoints in
			(new_acc, (id , endPoints) :: endL)
		| Eoutput _ ->
			(acc,endL)
		| Eindex (id,e1,e2) ->
			let endPoints1, new_acc = pres_exp utils acc e1 in
			let endPoints2, new_acc = pres_exp utils new_acc e2 in
			(new_acc, (id,(List.flatten endPoints1) @ (List.flatten endPoints2))::endL)
	in

	let acc, inList = List.fold_left pres_inputs_index (acc,[]) forall_handler.for_index in
	let in_input_vars, _ = List.split inList in
	let in_input_vars_set = Zident.S.of_list in_input_vars in

	let pres_outputs_index endL index = 
		match index.desc with
		| Eoutput (id_in, id_out) ->
			(id_in, id_out) :: endL
		| _ ->
			endL
	in
	
	let outList = List.fold_left pres_outputs_index [] forall_handler.for_index in
	
	let in_output_vars, _ = List.split outList in
	let in_output_vars_set = Zident.S.of_list in_output_vars in

	let block_build_env = Env_build.build_eq_list_block utils forall_handler.for_body in
	
	let block_build_env = 
		{Env_build.inputs = Zident.S.diff block_build_env.inputs in_input_vars_set;
		const_inputs = Zident.S.empty;
		outputs = Zident.S.diff block_build_env.outputs in_output_vars_set;
		const_outputs = Zident.S.empty ;
	} in
	
	let addI = List.map (fun id -> mk_myAddPort ~name:(Format.asprintf "%a" Special_printer.name id) Input) in_input_vars in
	let addO = List.map (fun id -> mk_myAddPort ~name:(Format.asprintf "%a" Special_printer.name id) Output) in_output_vars in

	let forOpNode, for_unres, inner_unres, for_env, for_utils = 
		init_block ~addI:addI ~addO:addO utils block_build_env acc.env Forall in

	let for_input_env, for_unres = 
		List.fold_right2 (fun (id, endPoints) outer (input_env,unres) ->
			let unres = List.fold_left (fun unres endPoint ->
				try_edge unres endPoint (outerToEndPoint outer)) unres endPoints
			in
			let sing_e = Zident.Env.singleton id [outerToEndPoint outer] in
			Zident.Env.union fct_union sing_e input_env, unres
		) inList (first_n (List.length inList) forOpNode#getInputs) (for_env.input_env, for_unres)
	in
	
	let for_output_env, for_output,inner_unres = 
		List.fold_right2 (fun (id_in, id_out) outer (output_env, for_output,unres) ->
			let unres = try_edge ~insideSelf:true unres (mk_rt (Ident id_in)) (outerToEndPoint outer) in
			let sing_in = Zident.Env.singleton id_in [outerToEndPoint outer] in
			let sing_out = Zident.Env.singleton id_out [outerToEndPoint outer] in
			Zident.Env.union fct_union sing_in output_env,
			Zident.Env.union fct_union sing_out for_output,
			unres
		) outList (first_n (List.length outList) forOpNode#getOutputs) (for_env.output_env, for_env.output_env,inner_unres)
	in

	let for_env = {
		input_env = for_input_env;
		output_env = for_output_env
	} in

	let for_acc = {exitNode = forOpNode; env = for_env; unres = inner_unres} in
	let block_acc = pres_block for_utils for_acc forall_handler.for_body in
	resolve_unres for_utils block_acc.env block_acc.unres;
	
	let new_input_env = 
		Zident.Env.union fct_union acc.env.input_env for_output in
	{exitNode = forOpNode; env = {acc.env with input_env = new_input_env}; unres = for_unres @ acc.unres}

(** [pres_match utils acc (cond,match_handlers)] functions like for a present node. We create a block for eatch handler with a half circle Control Port with the dependenciez from the condition.

We also link the handlers from first to last. *)
and pres_match utils acc (cond, match_handlers) = 

	let condEndPoints, acc = pres_exp utils acc cond in
	let condEndPoints = List.flatten condEndPoints in

	let exitNodes, acc = List.fold_left (fun (exitNodes,acc) mh ->
		let patVars = Find_vars.find_vars_pattern mh.m_pat in
		let acc = pres_block ~has_control:true ~forced_const:patVars utils acc mh.m_body in
		let handlerNode = acc.exitNode in
		addResetBegin ~look:(HalfCircle) handlerNode;
		let new_unres = List.fold_left (fun unres rt ->
		 	try_edge unres rt (outerToEndPoint (List.hd handlerNode#getControl)) 
		) [] condEndPoints in
		(handlerNode::exitNodes,{acc with unres = new_unres @ acc.unres})
	) ([],acc) match_handlers
	in

	let exitNodes = List.rev exitNodes in
	
	let rec addLinks = function 
	| [] | [_] -> ()
	| firstNode :: secondNode :: q ->
		(* do something *)
		addResetBegin ~look:Visible ~side:South firstNode;
		addResetBegin ~look:Visible ~side:North secondNode;
		new_edge Dot (outerToEndPoint (List.hd firstNode#getControl)) (outerToEndPoint (List.hd secondNode#getControl)); 
		addLinks (secondNode :: q)
	in
	addLinks exitNodes;

	acc

(** [pres_reset_block utils acc (eql, reset_e)] is visualized as a block, where we add a control port of look Loop which inputs are the dependencies from [reset_e] *)
and pres_reset_block utils acc (eql, reset_e) = 
	let build_env = Env_build.build_eq_list utils eql in
	let no_node = (!Zmisc.do_viz2_less && Count_eq.count_eq_list eql <= 1) in	
	let build_env_inputs = build_env.inputs in
	let build_env = {Env_build.empty_env with inputs = build_env_inputs; outputs = build_env.outputs} in	

	let fctNode, fct_unres, unres, fct_env, fct_utils = 
		if no_node then
			utils.function_node, [], [],acc.env, utils
		else begin
			let addC = [mk_myAddPort ~look:Loop North] in
			init_block utils build_env acc.env (BlanckFct SIDE) ~addC:addC 
		end
	in

	let inner_acc =  
		List.fold_left (
			pres_equ fct_utils) {env = fct_env; unres = unres; exitNode = fctNode} eql 
	in

	if not no_node then
		resolve_unres fct_utils inner_acc.env inner_acc.unres;
	
	let exitNode = if no_node then inner_acc.exitNode else fctNode in

	let resetEnds, acc = pres_exp utils acc reset_e in

	let resetEnds = List.flatten resetEnds in
	let target = (outerToEndPoint (List.hd exitNode#getControl)) in
	
	let fct_unres = List.fold_left (fun unres endP ->
		try_edge unres endP target) fct_unres resetEnds	
	in	

	let new_env = 
		if no_node then inner_acc.env
		else {acc.env with input_env = Zident.Env.union fct_union fct_env.output_env acc.env.input_env} in
	
	let inner_unres = if no_node then inner_acc.unres else [] in
	{exitNode=exitNode; unres = acc.unres @ fct_unres @ inner_unres; env = new_env}

(** [init_block utils build_env env node_type creates a node of type [node_type], with ports corresponding to the build_env.

Options [addI], [addO], [addC] are here to specify a list of custom ports to put first. 

After creation of the ports, we try to connect the input ports to their given variable outside of the block, and the output ports to the given variable inside of the block.

Return of the function : 
[opNode, input_unres, output_unres, block_env, block_utils].
The opNode is the created node, [input_unres] the unresolved edges outside of the block to be connected to inputs of the block, [output_unres] are unresolved edges for the inside of the block,
block_env is the environment corresponding to the inputs and outputs of the created block, and block_utils the corresponding utils for the created node.*)

and init_block ?(isFun=false) ?(order=false) ?(is_aut_state=false) ?(is_match=false) ?(insideSelf=false) ?(addI=[]) ?(addO=[]) ?(addC=[]) ?(control=false) utils (build_env : Env_build.build_env) env node_type = 

	let build_env = 
		if is_aut_state then
			{Env_build.empty_env with inputs = build_env.const_inputs; outputs = build_env.const_outputs}
		else
			build_env
	in

	let inputs = List.map (fun id -> Format.asprintf "%a" Special_printer.name id)
		(Zident.S.to_list build_env.inputs)
	in
	let outputs = List.map (fun id -> Format.asprintf "%a" Special_printer.name id)
		(Zident.S.to_list build_env.outputs)
	in
	
	let inputs = if is_aut_state then [] else inputs in
	let outputs = if is_aut_state then [] else outputs in

	let new_addI = List.map (fun a -> mk_addPort ~look:a.look ~name:a.name a.side) addI in
	let new_addO = List.map (fun a -> mk_addPort ~look:a.look ~name:a.name a.side) addO in
	let new_addC = List.map (fun a -> mk_addPort ~look:a.look ~name:a.name a.side) addC in
	let opNode = mkFunctionNode ~order:order ~insideSelf:insideSelf ~control:control ~addI:new_addI ~addO:new_addO ~addC:new_addC node_type inputs outputs (Node utils.function_node) utils.layer in
	
	let utils = {utils with layer = utils.layer + 1; function_node = opNode} in
	
	let rec ignore_n n l = 
		match n, l with
		| 0 , _ -> l
		| _ , x :: q -> ignore_n (n-1) q
		| _ -> assert false
	in

	let inputPorts = ignore_n (List.length addI) opNode#getInputs in

	let outputPorts = ignore_n (List.length addO) opNode#getOutputs in

	(* connect the inputs to the given variable, and produce the environment *)
	let input_env, input_unres = 
		if not is_aut_state then
			List.fold_right2 (fun id outer_target (input_env,unres) ->
				let new_unres = (mk_unres id (outerToEndPoint outer_target))::unres in
				let new_e = Zident.Env.singleton id [outerToEndPoint outer_target] in
				Zident.Env.union fct_union new_e input_env, new_unres
			) (Zident.S.to_list build_env.inputs) inputPorts (Zident.Env.empty,[])
		else
			(Zident.Env.empty, [])
	in
	
	(* in the case of an automaton_state the inputs are translated into const nodes *)
	let input_env, input_unres = 
		if is_aut_state then
			List.fold_right (fun id (input_env,unres) ->
				let constNode = mkOpNode (Const (Format.asprintf "%a" Special_printer.name id, false)) opNode utils.layer in
				let new_e = Zident.Env.singleton id [outerToEndPoint (List.hd constNode#getOutputs)] in
				Zident.Env.union fct_union new_e input_env , unres
			) (Zident.S.to_list build_env.inputs) (input_env , input_unres)
		else
			input_env, input_unres
	in

	(* add the constant inputs to the input_env. This only happen when we have a present or pattern block *)

	let input_env = 
		List.fold_right (fun id input_env ->
			let constNode = mkOpNode (Const (Format.asprintf "%a" Special_printer.name id, false)) opNode utils.layer in
			let new_e = Zident.Env.singleton id [outerToEndPoint (List.hd constNode#getOutputs)] in
			Zident.Env.union fct_union new_e input_env
		) (Zident.S.to_list build_env.const_inputs) input_env
	in

	(* connect the outputs to the given variable, and produce the output environment *)
	let output_env, output_unres = 
		if not is_aut_state then
			List.fold_right2 (fun id outer_source (output_env,unres) ->
				let new_unres = (mk_unres ~iS:true id (outerToEndPoint outer_source))::unres in
				let new_env = Zident.Env.singleton id [outerToEndPoint outer_source] in
				Zident.Env.union fct_union output_env new_env, new_unres
		) (Zident.S.to_list build_env.outputs) outputPorts (Zident.Env.empty,[])
		else
			(Zident.Env.empty,[])
	in
	
	(* in the case of an automaton_state the outputs are translated into sink nodes *)
	let output_env, output_unres = 
		if is_aut_state then
			List.fold_right (fun id (output_env, unres) ->
				let sinkNode = mkOpNode (Sink (Format.asprintf "%a" Special_printer.name id, true)) opNode utils.layer in
				let new_unres = (mk_unres ~iS:true id (outerToEndPoint (List.hd sinkNode#getInputs)))::unres in
				let new_e = Zident.Env.singleton id [outerToEndPoint (List.hd sinkNode#getInputs)] in
				Zident.Env.union fct_union output_env new_e, new_unres
			) (Zident.S.to_list build_env.outputs) (output_env,output_unres)
		else
			(output_env,output_unres)
	in

	(* we do the same for the additional inputs *)
	let input_env, input_unres = List.fold_right2 (fun addEl outer_target (input_env, unres) ->
		match addEl.id with
		| None -> (input_env, unres)
		| Some id ->
			if is_aut_state then begin
				let constNode = mkOpNode (Const (Format.asprintf "%a" Special_printer.name id, false)) opNode utils.layer in
				let new_e = Zident.Env.singleton id [outerToEndPoint (List.hd constNode#getOutputs)] in
				Zident.Env.union fct_union new_e input_env , unres
			end else begin
				let new_unres = (mk_unres id (outerToEndPoint outer_target))::unres in
				let new_e = Zident.Env.singleton id [outerToEndPoint outer_target] in
				Zident.Env.union fct_union new_e input_env, new_unres
			end
	) addI (first_n (List.length addI) opNode#getInputs) (input_env,input_unres)
	in
	
	(* we do the same for the additional outputs *)
	let output_env, output_unres = List.fold_right2 (fun addEl outer_source (output_env,unres) ->
		match addEl.id with
		| None -> (output_env, unres)
		| Some id ->
			if is_aut_state then begin
				let sinkNode = mkOpNode (Sink (Format.asprintf "%a" Special_printer.name id, true)) opNode utils.layer in
				let new_unres = (mk_unres ~iS:true id (outerToEndPoint (List.hd sinkNode#getInputs)))::unres in
				let new_e = Zident.Env.singleton id [outerToEndPoint (List.hd sinkNode#getInputs)] in
				Zident.Env.union fct_union new_e input_env , new_unres
			end else begin
				let target = if isFun then
					addEmptyNode utils (outerToEndPoint outer_source)
					else (outerToEndPoint outer_source)
				in
				let new_unres = (mk_unres id target)::unres in
				let new_env = Zident.Env.singleton id [outerToEndPoint outer_source] in
				Zident.Env.union fct_union output_env new_env, new_unres
			end	
	) addO (first_n (List.length addO) opNode#getOutputs) (output_env,output_unres) 
	in
	
	opNode,input_unres , output_unres, {input_env = input_env; output_env = output_env}, utils

and addEmptyNode ?(dash=false) utils target = 
	let emptyNode = mkOpNode Empty utils.function_node utils.layer in
	let edgeType = if dash then Dash else Simple in
	new_edge edgeType (outerToEndPoint (List.hd emptyNode#getOutputs)) target;
	outerToEndPoint (List.hd (emptyNode#getInputs))

(** [implementation parent impl layer] creates the visualization for a zelus node *)
and implementation ?(patEq=None) ?(extern=false) parent impl layer = 
	match impl.desc with
	| Efundecl (f,body) ->

		let input_names = List.fold_left (fun acc pat -> 
			let vars = Find_vars.find_vars_pattern_order pat in
			acc @ vars)
		[] body.f_args
		in
		let output_names = [] (*(get_function_output body.f_body)*) in
	
		let outputs = List.map (fun id -> mk_myAddPort ~corId:id ~name:(Format.asprintf "%a" Special_printer.name id) Output) output_names in
		let inputs = List.map (fun id -> mk_myAddPort ~corId:id ~name:(Format.asprintf "%a" Special_printer.name id) Input) input_names in
		let utils = {
			function_name = f;
			layer = layer  + 1; 
			function_node = parent;
			in_reg=false;
			in_present=false;
			count_block = Count_env.count_funexp body;
			in_match=false;
		} in

		let rec addN n = 
			match n with
			| 0 -> []
			| _ -> (mk_myAddPort Output) :: (addN (n-1))
		in

		let finalEList = split_and_flatten_e_no_pat (getExitExp body.f_body) in
		let finalEList = 
			if extern then
				List.filter (fun e -> not (isVoidType e.e_typ)) finalEList 
			else finalEList
		in

		(* if we know the pattern on which the function will be applied we know the number of outputs, else we flatten the outputs *)
		let nbOuts = match patEq with
		| None ->
			if extern then List.length finalEList
			else
				numOutputs body.f_body.e_typ 
		| Some pat ->
			List.length (Find_vars.find_vars_pattern_order pat)
		in

		let has_to_AddOuts = List.length outputs < nbOuts in
		let outputs = if has_to_AddOuts then (addN (nbOuts - (List.length outputs))) @ outputs
		else outputs
		in

		let opNode,_,inner_unres,env,utils = init_block ~order:true ~isFun:true ~insideSelf:true utils ~addI:inputs ~addO:outputs Env_build.empty_env {input_env = Zident.Env.empty; output_env = Zident.Env.empty} (Fct f) in

		let flattened_body = split_and_flatten_e_no_pat body.f_body in
		let endsEList, acc = 
			List.fold_left (fun (endsL, acc) e ->
				let endsE, acc = pres_exp ~no_void:true utils {exitNode = parent; env = acc.env; unres = acc.unres} e in
				endsL @ endsE, acc) ([], {exitNode = parent; env = env; unres = []}) flattened_body
		in
	
		(* we connect the return endPoints to the outputs of the function *)
		let unres_to_add =
			if extern then begin
				(* true visualization of a zelus node, we connect each output to the return endPoints corresponding to him. *)
				List.iter2 (fun e target ->
					target#getPort#setName (findVar e)) finalEList opNode#getOutputs;	

				let new_unres,_ = List.fold_left2 (fun (unres, (endsEList : return_type list list)) finalE outer_output ->
					(* an output can correspond to a tuple and thus having various return endPoints list *)
					let numValues = numOutputs finalE.e_typ in
					let endsE, endsEList = eatN numValues endsEList in
					let endsE = List.flatten endsE in
					let isConst = (List.length endsE = 1) && (List.hd endsE).edge_type = Dash in
					
					let target = if isConst then (outerToEndPoint outer_output) else
						addEmptyNode ~dash:isConst utils (outerToEndPoint outer_output)
					in

					let unres = List.fold_left (fun unres rt ->
						try_edge ~insideSelf:true unres rt target ) unres endsE
					in
					(unres , endsEList)
				) ([] , endsEList) finalEList opNode#getOutputs
				in
				new_unres
			end
			else if patEq = None && has_to_AddOuts && (List.length opNode#getOutputs = List.length endsEList) then begin
				(* case where we don't know the pattern to be applied, we flatten all the tuple outputs *)	
				let finalEList = List.fold_left (fun eL e ->
					eL @ (List.init (numOutputs e.e_typ) (fun _ -> e))) [] finalEList
				in
				
				List.iter2 (fun e target ->
					target#getPort#setName (findVar e)) finalEList opNode#getOutputs;	

				List.fold_left2 (fun unres (rtList : return_type list) target ->
					(* here we have one return endPoints list for one output *)
					let isConst = (List.length rtList = 1) && (List.hd rtList).edge_type = Dash in
					let target = if isConst then (outerToEndPoint target) else
						addEmptyNode ~dash:isConst utils (outerToEndPoint target) 
					in
					List.fold_left (fun unres rt ->
						try_edge ~insideSelf:true unres rt target ) unres rtList

			) [] endsEList (opNode#getOutputs)
			end else if patEq <> None && has_to_AddOuts then begin
				(* we know the pattern on which the function is applied *)
				let finalEList = List.fold_left (fun eL e ->
					eL @ (List.init (numOutputs e.e_typ) (fun _ -> e))) [] finalEList 
				in
				
				let patEq = match patEq with
				| None -> assert false
				| Some patEq -> patEq
				in
				let splitPatEq = split_pat patEq in
			
			(* add names to outputs *)
				let outEnv, _ = List.fold_left2 (fun (outEnv, finalEList) pat outer_output ->
					let numValues = numOutputs pat.p_typ in
					
					let rec eatFinals num finalEList = match num,finalEList with
					| 0 , _ -> [], finalEList
					| _ , [] -> assert false
					| n , x :: q ->
						let taken, leave = eatFinals (num - 1) q in
						x :: taken , leave
					in
					
					let forPat, finalEList = eatFinals numValues finalEList in
					let outEnv = match forPat with
					| [x] -> 
						let var = findVar x in
						if var <> "" then begin
							outer_output#getPort#setName var;
							StringEnv.add var (findVarId x) outEnv
						end else
							outEnv
					| _ -> outEnv
					in
					outEnv, finalEList
				) (StringEnv.empty,finalEList) splitPatEq opNode#getOutputs
				in

				let new_unres,_ = List.fold_left2 (fun (unres, (endsEList : return_type list list)) pat outer_output ->
					let numValues = numOutputs pat.p_typ in
					(* the endsEList is the list of return endPoints list which correspond to each one output. We here take the correct amount of output the pattern want *)	
					let endsE, endsEList = eatN numValues endsEList in
					let endsE = List.flatten endsE in
					let isConst = (List.length endsE = 1) && (List.hd endsE).edge_type = Dash in
					
					let target = if isConst then (outerToEndPoint outer_output) else
						addEmptyNode ~dash:isConst utils (outerToEndPoint outer_output)
					in
	
					let unres = List.fold_left (fun unres rt ->
						try_edge ~insideSelf:true unres rt target ) unres endsE
					in
					let unres = if numValues = 0 && outer_output#getPort#getName <> "" then (*void type *) 
						try_edge unres (mk_rt (Ident (StringEnv.find (outer_output#getPort#getName) outEnv))) target
					else unres
					in
					(unres , endsEList)
				) ([] , endsEList) splitPatEq opNode#getOutputs
				in
				new_unres

			end
			else
				[]
		in

		resolve_unres utils acc.env (unres_to_add @ inner_unres @ acc.unres); (*hack*)
		Some opNode
	| _ -> None

let implementation_list impl_list file =
	let file = String.capitalize_ascii file in
	filename := file;
	Special_printer.filename := file;
	let ig = new iGraph in 

	let globalNode = mkFunctionNode Inv [] [] (Graph ig) 0 in
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
				ignore (implementation ~extern:true globalNode impl 0)
		| _ -> ()
	) impl_list;
	ig
