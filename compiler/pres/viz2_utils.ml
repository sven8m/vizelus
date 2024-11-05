open Zelus


(** [first_n n l] returns the first [n] elements of [l]*) 
let rec first_n n l =
	match n,l with
	| 0 , _ -> []
	| _ , x :: q -> x :: (first_n (n-1) q)
	| _ -> assert false

(** [exp_is_function e] returns true if the expression [e] if a function, that is
an application that isn't a mathematical operator *)
let exp_is_function e =
	match e.e_desc with
	| Eapp ( _, fct, _) ->
		let name = match fct.e_desc with
		| Eglobal lid -> begin match lid.lname with
			| Name n -> n
			| Modname l -> l.id
 			end
		| _ -> Format.asprintf "%a" Special_printer.expression fct
		in
		if List.mem name Special_printer.basic_operations then
			false
		else true
	| _ -> false

(** [exp_is_true_function_call e] return [true] if the expression [e] calls a function that isn't a variable defined in the code*)
let exp_is_true_function_call e = 
	match e.e_desc with
	| Eapp (_,fct,_ ) ->
		begin match fct.e_desc with
		| Eglobal _ ->true 
		| _ -> false
		end
	| _ -> false

(** [get_exp_fct_name e] returns the name of the function if [e] is an application, else the empty string *)
let get_exp_fct_name e = 
	match e.e_desc with
	| Eapp ( _, fct, _) ->
		let name = match fct.e_desc with
		| Eglobal lid -> begin match lid.lname with
			| Name n -> n 
			| Modname l -> l.id
			end
		| _ -> Format.asprintf "%a" Special_printer.expression fct 
		in
		name
	| _ -> ""

let is_unit_type (ty : Deftypes.typ) = 
	match ty.t_desc with
	| Tconstr (id,[],_) when id.qual="Stdlib" && id.id ="unit" -> true
	| _ -> false

let print_tys (ty : Deftypes.typ) = 
	let text = match ty.t_desc with
	| Deftypes.Tvar -> "var"
	| Tproduct _ -> "prod"
	| Tlink _ -> "link"
	| Tvec _ -> "vec"
	| Tfun _ -> "fun"
	| Tconstr _ -> "constr"
	in
	Format.printf "%s@." text

(** [numOutputs ty] returns the expected number of different outputs a type should have, given that we flatten product types *)
let rec numOutputs (ty : Deftypes.typ) = 
	match ty.t_desc with
	| Deftypes.Tvar -> 1
	| Tproduct tyl -> List.fold_left (fun acc ty -> acc + (numOutputs ty)) 0 tyl
	| Tlink ty -> numOutputs ty
	| Tvec _ -> 1 (* TODO *)
	| Tfun _ -> 1 (* TODO *)
	| Tconstr (id,[],_) when id.qual="Stdlib" && id.id="unit" -> 0
	| Tconstr (id,[],_) -> 1
	| Tconstr (id,[ty],_) when id.qual="Stdlib" && id.id ="signal" && (is_unit_type ty) -> 0
	| Tconstr (id,el,_) when id.qual="Stdlib" && id.id="signal" -> 
		(*List.iter (fun t -> print_tys t) el;*) 1
	| Tconstr (id,_,_) -> 1 (* TODO *) 



(** [split_pat pat] splits the tuple patterns *)
let rec split_pat pat =
	match pat.p_desc with
	| Ewildpat -> [pat] 
	| Econstpat _ -> []
	| Econstr0pat _ -> []
	| Etuplepat l -> List.fold_left (fun acc p  -> acc @ (split_pat p)) [] l
	| Evarpat id -> [pat]
	| Ealiaspat _ -> [pat]
	| Eorpat _ -> [pat]
	| Erecordpat _ -> [pat]
	| Econstr1pat _ -> [pat]
	| Etypeconstraintpat (p,_) -> split_pat p

(** [isVoidType ty] returns true if [ty] is of type unit *)
let rec isVoidType (ty : Deftypes.typ)= 
	match ty.t_desc with
	| Tlink ty -> isVoidType ty
	| Tconstr (id,[],_) when id.qual="Stdlib" && id.id="unit" -> true
	| _ -> false

(** [num_parameters ty] returns the number of expected parameters a function should have, given its type [ty]*)
let rec num_parameters (ty : Deftypes.typ_desc Deftypes.loc)= 
	match ty.t_desc with
	| Deftypes.Tvar | Tproduct _ | Tconstr _ | Tvec _  -> 0
	| Deftypes.Tlink ty -> num_parameters ty
	| Tfun (_,_,_,ty) -> 1 + (num_parameters ty)

(** [split_and_flatten_e pat_e e] takes an expression [e] and a pattern [pat_e] and flatten the tuple expressions and patterns,
returning the list of flattened expressions *)
let rec split_and_flatten_e pat_e e = 
	match pat_e.p_desc, e.e_desc with
	| Ewildpat , _ -> []
	| Etuplepat pl , Etuple el -> 
		List.fold_left2 (fun acc p1 e1 ->
			acc @ (split_and_flatten_e p1 e1)) [] pl el
	| Evarpat _ , _ -> [e]
	| Econstpat (Evoid) , Econst (Evoid) -> []
	| Etuplepat pl, _ -> List.init (List.length pl) (fun _ -> e) (* hack ?*) 
	| _ -> assert false

let create_var_pat id exp = 
	{p_desc = Evarpat id;
	p_loc = Zlocation.no_location;
	p_typ = exp.e_typ;
	p_caus = Defcaus.no_typ;
	p_init = Definit.no_typ; 
	}	

(** [eatN n l] returns [l1,l2] where [l1] are the first [n] elements of [l] and [l2] the rest. *)
let rec eatN num l = match num, l with
	| 0 , _ -> [], l
	| n , [] -> assert false
	| n, x :: q -> let first,last = eatN (n-1) q in
		x :: first, last

(** [is_void e] returns true if the expression [e] is () *)
let is_void e = 
	match e.e_desc with
	| Econst (Evoid) -> true
	| _ -> false

let get_fct_args e = 
	match e.e_desc with
	| Eapp (_,_,el) -> el
	| _ -> assert false

let rec find_vars_as_list e = 
	match e.e_desc with
	| Elocal id -> [id]
	| Etuple el -> 
		List.fold_left (fun acc e -> acc @ (find_vars_as_list e)) [] el
	| _ -> []

let rec get_function_output e = 
	match e.e_desc with
	| Elet (_,e_after) -> get_function_output e_after
	| _ -> find_vars_as_list e (*a simple discrete function*)

let simpleDiscrete e = 
	match e.e_desc with
	| Elet _ -> false
	| _ -> true

let rec split_and_flatten_e_no_pat e = 
	match e.e_desc with
	| Etuple el -> 
		List.fold_left (fun acc e1 ->
			acc @ (split_and_flatten_e_no_pat e1)) [] el
	| _ -> [e]

let rec getExitExp e = 
	match e.e_desc with
	| Elet (_,e_after) -> getExitExp e_after
	| Eblock (_,e_after) -> getExitExp e_after
	| _ -> e

let findVar e = 
	match e.e_desc with
	| Elocal id -> Format.asprintf "%a" Special_printer.name id
	| _ -> ""

let findVarId e = 
	match e.e_desc with
	| Elocal id -> id
	| _ -> assert false
