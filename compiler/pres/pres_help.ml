open Intermediate_graph
open Utils_def
open Mk_intermediate

type return_type = 
	| Ident of Zident.t
	| Endpoint of iEndPoint

type unresolved = {
	source : return_type;
	target : return_type;
	mult : edge_type;
	nec : bool;
	prio : int;
}

let fct_union id a1 a2 = Some a1

let union_init_env env1 env2 = 
	{env1 with init_env = Zident.Env.union fct_union env1.init_env env2.init_env}

let mk_unresolved ?(nec=true) ?(prio=0) source target mult = 
	{source = source ; target = target ; mult = mult; nec = nec; prio=prio}

let self_loop (source : iEndPoint) (target : iEndPoint) = 
	(source#getNode#getId = target#getNode#getId) && (source#getPort#getId = target#getPort#getId)

let try_edge ?(nec=true) ?(prio=0) unres e_type source target =
	match source, target with
	| Ident _ , _ | _ , Ident _ ->
		(mk_unresolved ~nec:nec ~prio:prio source target e_type) :: unres
	| Endpoint source, Endpoint target ->
		if not (self_loop source target) then
			new_edge ~prio:prio e_type source target;
		unres

(** [expect_one utils endL ty] expects an endPoint list [endL] of length 1. If not the case, a tuple node is created and the single output endpoint is returned *)
let expect_one utils (endpoint_list : return_type list) (*ty*) = 
	if List.length endpoint_list > 1 then begin
		let opNode = mkOpNode (Tuple (List.length endpoint_list)) utils.function_node utils.layer in
		(*let ty = match ty with
		| TProd t -> t
		| _ -> assert false
		in*)
	(*	let s_t = List.combine endpoint_list ty in
	*)	let unres = List.fold_right2 (fun (source) outer_input unres ->
			let target = Endpoint (outerToEndPoint outer_input) in
			try_edge unres (*(do_mult ty)*) Simple source target
		) endpoint_list opNode#getInputs []
		in
		Endpoint (outerToEndPoint (List.hd opNode#getOutputs)) , unres
	end else
		List.hd endpoint_list , []

(** [resolve_unres env unres] takes a list of unresolved edges to be created, and an environment [env], and creates in the best way the edges.
It is assumed that all variables that are unresolved are now part of the environment *)
let resolve_unres utils env unres=
	ignore (List.fold_right (fun unres env ->	
		let source = match unres.source with
		| Ident v ->
			begin match Zident.Env.find_opt v env.input_env with
			| Some p -> Some p
			| None -> 
				begin match Zident.Env.find_opt v env.output_env with
				| Some p -> Some p
				| None -> 
					if not !Zmisc.do_viz_no_connect then Zident.Env.find_opt v env.init_env else None
				end
			end
		| Endpoint p -> Some p
		in
		let target = match unres.target with
		| Ident v ->
			begin match Zident.Env.find_opt v env.output_env with
			| Some p -> Some p
			| None ->
				begin match Zident.Env.find_opt v env.input_env with
				| Some p -> Some p
				| None -> if not !Zmisc.do_viz_no_connect then Zident.Env.find_opt v env.init_env else None
				end
			end
		| Endpoint p -> Some p
		in
		let source,env = if !Zmisc.do_viz_no_connect || !Zmisc.viz_no_init then
			match source with
			| Some p -> Some p, env
			| None ->
				let id = match unres.source with
				| Ident v -> v
				| _ -> assert false
				in
				let id_string = Format.asprintf "%a" Special_printer.name id in
				let constNode = mkOpNode (Const (id_string,false)) utils.function_node utils.layer in
				let endPoint = outerToEndPoint (List.hd constNode#getOutputs) in
				Some (endPoint), {env with input_env = Zident.Env.add id endPoint env.input_env}
			else source, env
		in
		let target,env = if !Zmisc.do_viz_no_connect || !Zmisc.viz_no_init then
			match target with
			| Some p -> Some p, env
			| None ->
				let id = match unres.target with
				| Ident v -> v
				| _ -> assert false
				in
				let id_string = Format.asprintf "%a" Special_printer.name id in
				let sinkNode = mkOpNode (Sink (id_string,false)) utils.function_node utils.layer in
				let endPoint = outerToEndPoint (List.hd sinkNode#getInputs) in
				Some (endPoint) , {env with output_env = Zident.Env.add id endPoint env.output_env}
			else target, env
		in

		begin match source, target with
		| Some source, Some target ->
			if (not (self_loop source target)) then ignore (new_edge unres.mult source target)
		| _ -> if unres.nec then assert false
		end;
		env
	) unres env)

let resolve_unres_opt env unres = 
	List.fold_right (fun unres new_unres ->
		let source = match unres.source with
		| Ident v ->
			begin match Zident.Env.find_opt v env.input_env with
			| Some p -> Endpoint p
			| None -> begin match Zident.Env.find_opt v env.output_env with
				| Some p -> Endpoint p
				| None -> 
					if not !Zmisc.do_viz_no_connect then 
						begin match Zident.Env.find_opt v env.init_env with
						| Some p -> Endpoint p
						| None -> Ident v
						end
					else 
						Ident v
				end
			end
		| Endpoint p -> Endpoint p
		in
		let target = match unres.target with
		| Ident v ->
			begin match Zident.Env.find_opt v env.output_env with
			| Some p -> Endpoint p
			| None -> begin match Zident.Env.find_opt v env.input_env with
				| Some p -> Endpoint p
				| None -> 
					if not !Zmisc.do_viz_no_connect then 
						begin match Zident.Env.find_opt v env.init_env with
						| Some p -> Endpoint p
						| None -> Ident v
						end
					else
						Ident v
				end
			end
		| Endpoint p -> Endpoint p
		in
		begin match source , target with
		| Endpoint source , Endpoint target ->	
			if not (self_loop source target) then
				ignore (new_edge unres.mult source target);
			new_unres
		| _ -> (mk_unresolved ~nec:unres.nec source target unres.mult) :: new_unres
		end
	) unres []

let labelFromId id = 
	let t = Format.asprintf "%a" Special_printer.name id in
	edgeLabel t

let addLabelEndPoint e id = 
	let t = Format.asprintf "%a" Special_printer.name id in
	if List.exists (fun lab -> lab#getName = t) e#getLabels then ()
	else begin
		let lab = edgeLabel t in
		e#addLabel lab
	end

let resolve_after_block new_env env utils unres = 
	let unres = resolve_unres_opt new_env unres in
	let unused = Zident.Env.fold (fun id endPoint unused ->
		if not (Zident.Env.mem id (env.input_env)) && (List.length endPoint#getLabels > 0) then begin
			ignore (endPoint#eatLabels);
			id :: unused;
		end else unused) new_env.input_env []
	in
	List.iter (fun id ->
		let endPoint = Zident.Env.find id new_env.input_env in
		let opNode = mkOpNode (Sink (Format.asprintf "%a" Special_printer.name id,false)) utils.function_node utils.layer in
		new_edge Simple endPoint (outerToEndPoint (List.hd opNode#getInputs))
	) unused;
	unres
