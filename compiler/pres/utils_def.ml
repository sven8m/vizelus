type utils = {
	function_name : string;
	layer : int;
	function_node : Intermediate_graph.iNode;
	in_reg : bool;
	in_present : bool;
	count_block : Count_env.count_env_type;
	in_match : bool;
}

type env = {
	input_env : Intermediate_graph.iEndPoint Zident.Env.t;
	output_env : Intermediate_graph.iEndPoint Zident.Env.t;
	reg_env : Intermediate_graph.iEndPoint Zident.Env.t;
	init_env : Intermediate_graph.iEndPoint Zident.Env.t;
}

let empty_env = {
	input_env = Zident.Env.empty; 
	output_env = Zident.Env.empty; 
	reg_env = Zident.Env.empty;
	init_env = Zident.Env.empty;
}

let basic_operations = Special_printer.basic_operations


let print_utils_env_content ff env = 
	Zident.Env.iter (fun id _ ->
		Format.fprintf ff "%a, " Special_printer.name id) env

let print_utils_env ff env = 
	Format.fprintf ff "input_env : %a@." print_utils_env_content env.input_env;
	Format.fprintf ff "output_env : %a@." print_utils_env_content env.output_env;
	Format.fprintf ff "reg_env : %a@." print_utils_env_content env.reg_env;
	Format.fprintf ff "init_env : %a@." print_utils_env_content env.init_env

