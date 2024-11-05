(***********************************************************************)
(*                                                                     *)
(*                                                                     *)
(*          Zelus, a synchronous language for hybrid systems           *)
(*                                                                     *)
(*  (c) 2020 Inria Paris (see the AUTHORS file)                        *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique. All rights reserved. This file is distributed under   *)
(*  the terms of the INRIA Non-Commercial License Agreement (see the   *)
(*  LICENSE file).                                                     *)
(*                                                                     *)
(* *********************************************************************)

(* the main *)
open Zmisc
open Initial
open Compiler

let compile file =
  Modules.clear();
  if !no_stdlib then set_no_stdlib();
  if Filename.check_suffix file ".zls" || Filename.check_suffix file ".zlus"
  then
    let filename = Filename.chop_extension file in
    let modname = String.capitalize_ascii (Filename.basename filename) in
    compile modname filename
  else if Filename.check_suffix file ".zli"
  then
    let filename = Filename.chop_suffix file ".zli" in
    let modname = String.capitalize_ascii (Filename.basename filename) in
    interface modname filename
  else if Filename.check_suffix file ".mli"
  then
    let filename = Filename.chop_suffix file ".mli" in
    let modname = String.capitalize_ascii (Filename.basename filename) in
    scalar_interface modname filename
  else
    raise (Arg.Bad ("don't know what to do with " ^ file))

module SS = Zdepend.StringSet
let build file = 
  Deps_tools.add_to_load_path Filename.current_dir_name;
  let rec _build acc file = 
    let deps = 
      match (Filename.extension file) with
      | ".zls" -> Deps_tools.zls_dependencies file
      | ".zli" -> Deps_tools.zli_dependencies file
      | _ -> raise (Arg.Bad ("don't know what to do with " ^ file))
    in
    let acc = List.fold_left _build acc deps in
    let basename = Filename.chop_extension file in
    if not (SS.mem basename acc) then begin
      compile file; 
      SS.add basename acc
    end else
      acc
  in
  ignore (_build (SS.empty) file)
  
let doc_verbose = "\t Set verbose mode"
let doc_vverbose = "\t Set even more verbose mode"
and doc_version = "\t The version of the compiler"
and doc_outname = "<name> \t Simulation file name <name>"
and doc_print_types = "\t Print types"
and doc_print_causality_types = "\t Print causality types"
and doc_print_initialization_types = "\t  Print initialization types"
and doc_include = "<dir> \t Add <dir> to the list of include directories"
and doc_stdlib = "<dir> \t Directory for the standard library"
and doc_locate_stdlib = "\t  Locate standard libray"
and doc_no_stdlib = "\t  Do not load the stdlib module"
and doc_no_zlstdlib = "\t  Do not load the zlstdlib module"
and doc_typeonly = "\t  Stop after typing"
and doc_hybrid = "\t  Select hybrid translation"
and doc_simulation =
  "<node> \t Simulates the node <node> and generates a file <out>.ml\n\
   \t\t   where <out> is equal to the argument of -o if the flag\n\
   \t\t   has been set, or <node> otherwise"
and doc_sampling = "<p> \t Sets the sampling period to p (float <= 1.0)"
and doc_check = "<n> \t Check that the simulated node returns true for n steps"
and doc_use_gtk =
  "\t Use lablgtk2 interface."
and doc_inlining_level = "<n> \t Level of inlining"
and doc_inline_all = "\t Inline all function calls"
and doc_dzero = "\t Turn on discrete zero-crossing detection"
and doc_nocausality = "\t (undocumented)"
and doc_no_opt = "\t (undocumented)"
and doc_no_deadcode = "\t (undocumented)"
and doc_noinitialisation = "\t (undocumented)"
and doc_nosimplify = "\t (undocumented)"
and doc_noreduce = "\t (undocumented)"
and doc_lmm = "<n>\t Translate the node into Lustre--"
and doc_red_name = "\t Static reduction for"
and doc_zsign = "\t Use the sign function for the zero-crossing argument"
and doc_with_copy = "\t Add of a copy method for the state"
and doc_rif = "\t Use RIF format over stdin and stdout to communicate I/O to the node being simulated"
and doc_deps = "\t Recursively compile dependencies"

and doc_viz = "\t visualization"
and doc_viz_fun = "\t visualization only for the given function"
and doc_aut_trans = "\t block representation for automata transitions"
and doc_text = "\t textual when simple expressions"
and doc_text_if = "\t textual when simple expressions, also for if then else"
and doc_text_scond = "\t textual representation for conditions"
and doc_no_connect = "\t don't connect variables from other blocks"
and doc_inline_aut = "\t inline automata transitions"
and doc_true_no_connect = "\t don't connect variables at all"
and doc_viz_no_init = "\t don't show init statements"

and doc_viz2 = "\t visualization with abstraction"
and doc_viz2_less = "\t try not to show block nodes"
and doc_viz2_no_hyper_present = "\t no hyper edge for present port"
and doc_viz2_true_no_hyper_present = "\t strong no hyper edge for present port"
and doc_viz2_show_init = "\t show the init equations"
and doc_viz2_no_const = "\t do not show constant dependencies"

let errmsg = "Options are:"

let set_verbose () =
  verbose := true;
  Printexc.record_backtrace true

let set_vverbose () =
  vverbose := true;
  set_verbose ()

let add_include d =
  Deps_tools.add_to_load_path d;
  load_path := d :: !load_path

let set_gtk () =
    use_gtk := true;
    match !load_path with
    | [stdlib] -> add_include (stdlib ^ "-gtk")
    | _ -> ()

let main () =
  try
    Arg.parse
      (Arg.align [
          "-v", Arg.Unit set_verbose, doc_verbose;
          "-vv", Arg.Unit set_vverbose, doc_vverbose;
          "-version", Arg.Unit show_version, doc_version;
          "-o", Arg.String set_outname, doc_outname;
          "-I", Arg.String add_include, doc_include;
          "-i", Arg.Set print_types, doc_print_types;
          "-ic", Arg.Set print_causality_types, doc_print_causality_types;
          "-ii", Arg.Set print_initialization_types, doc_print_initialization_types;
          "-where", Arg.Unit locate_stdlib, doc_locate_stdlib;
          "-stdlib", Arg.String set_stdlib, doc_stdlib;
          "-nostdlib", Arg.Set no_stdlib, doc_no_stdlib;
          "-typeonly", Arg.Set typeonly, doc_typeonly;
          "-s", Arg.String set_simulation_node, doc_simulation;
          "-sampling", Arg.Float set_sampling_period, doc_sampling;
          "-check", Arg.Int set_check, doc_check;
          "-gtk2", Arg.Unit set_gtk, doc_use_gtk;
          "-dzero", Arg.Set dzero, doc_dzero;
          "-nocausality", Arg.Set no_causality, doc_nocausality;
          "-nopt", Arg.Set no_opt, doc_no_opt;
          "-nodeadcode", Arg.Set no_deadcode, doc_no_deadcode;
          "-noinit", Arg.Set no_initialisation, doc_noinitialisation;
          "-inline", Arg.Int set_inlining_level, doc_inlining_level;
          "-inlineall", Arg.Set inline_all, doc_inline_all;
          "-nosimplify", Arg.Set no_simplify_causality_type, doc_nosimplify;
          "-noreduce", Arg.Set no_reduce, doc_noreduce;
          "-zsign", Arg.Set zsign, doc_zsign;
          "-copy", Arg.Set with_copy, doc_with_copy;
          "-lmm", Arg.String set_lmm_nodes, doc_lmm;
          "-rif", Arg.Set use_rif, doc_rif;
          "-deps", Arg.Set build_deps, doc_deps;

          "-viz", Arg.Set do_visualization, doc_viz;
		  "-viz-fun", Arg.String set_viz_only_fun, doc_viz_fun;

		  "-aut-trans", Arg.Set do_aut_transition, doc_aut_trans;
		  "-viz-text", Arg.Set do_viz_text, doc_text;
		  "-viz-text-if", Arg.Set do_viz_text_if, doc_text_if;
		  "-viz-text-scond", Arg.Set do_viz_text_scond, doc_text_scond;
		  "-viz-noc", Arg.Set do_viz_no_connect, doc_no_connect;
		  "-viz-inline-aut", Arg.Set do_viz_inline_aut, doc_inline_aut;
		  "-viz-tnoc", Arg.Set do_viz_true_no_connect, doc_true_no_connect;
		  "-viz-no-init", Arg.Set viz_no_init, doc_viz_no_init;

		  "-viz2", Arg.Set do_viz2, doc_viz2;
		  "-viz2-less", Arg.Set do_viz2_less, doc_viz2_less;
		  "-viz2-nhp", Arg.Set do_viz2_no_hyper_present, doc_viz2_no_hyper_present;
		  "-viz2-tnhp", Arg.Set do_viz2_true_no_hyper_present, doc_viz2_true_no_hyper_present;
		  "-viz2-show-init", Arg.Set do_viz2_show_init, doc_viz2_show_init;
		  "-viz2-no-const", Arg.Set do_viz2_no_const, doc_viz2_no_const;
		])
      (fun filename -> if !build_deps then build filename else compile filename)
      errmsg;
    begin
      match !simulation_node with
      | Some(name) ->
          Simulator.main !outname name !sampling_period !number_of_checks !use_gtk
      | _ -> ()
    end
  with
  | Zmisc.Error -> exit 2;;

main ();;
exit 0;;
