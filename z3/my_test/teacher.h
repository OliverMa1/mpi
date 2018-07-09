#include <iostream>
#include <vector>
#include <tuple>
#include <typeinfo>
#include "z3++.h"

void check(const z3::expr & e, z3::context & ctx)
{
	auto solver = z3::solver(ctx);
	solver.add(e);
	if (solver.check() == z3::sat){
		std::cout << e << " is satisfiable" << "\n" << "a model is: " << solver.get_model() << std::endl;  
	}
	else {
		std::cout << e << " is unsatisfiable" << std::endl;
	}
}

std::vector<int> check_initial_condition(const z3::expr & hypothesis, const z3::expr & initial_vertices, z3::context & context,const z3::expr_vector & variables)
{

	// initial_vertices subset hypothesis
	std::vector<int> result;
	auto solver = z3::solver(context);
	z3::expr check = implies(initial_vertices,hypothesis);
	solver.add(!check);
	if (solver.check() == z3::unsat) {
		std::cout << "Hypothesis holds for initial condition!" << std::endl;
	}
	else {
		auto m = solver.get_model();
		z3::expr_vector sol(context);
		for (unsigned i = 0; i < m.size(); i++){
			z3::func_decl v = m[i];	
			sol.push_back(m.get_const_interp(v));
			//std::cout<< "m[i]: " << m[i] << "v.arity()" << v.arity() << v.name() << " = " << m.get_const_interp(v) << std::endl;
		}
		for(int i = 0; (unsigned)i < variables.size(); i++){
			int j;
			Z3_get_numeral_int(context, m.eval(variables[i]), &j);
			result.push_back(j);
		}
		std::cout << "counterexample for initial condition!:\n" << solver.get_model() << "\n";
	}
	return result;
}
std::vector<int> check_safe_condition(const z3::expr & hypothesis, const z3::expr & safe_vertices, z3::context & context, const z3::expr_vector & variables)
{	

	// wenn hypothesis subset safe_vertices 
	std::vector<int> result;
	auto solver = z3::solver(context);
	z3::expr check = implies(hypothesis, safe_vertices);
	solver.add(!check);
	if (solver.check() == z3::unsat) {
		std::cout << "Hypothesis holds for safe condition!!" << std::endl;
	}
	else {
		auto m = solver.get_model();
		z3::expr_vector sol(context);
		for (unsigned i = 0; i < m.size(); i++){
			z3::func_decl v = m[i];	
			sol.push_back(m.get_const_interp(v));
			
		}
		for(int i = 0; (unsigned)i < variables.size(); i++){
			int j;
			Z3_get_numeral_int(context, m.eval(variables[i]), &j);
			std::cout << "test: " << j << std::endl;
			result.push_back(j);
		}

		std::cout << "counterexample for safe condition!:\n" << solver.get_model() << "\n";
	}
	std::cout << "test2: " << result.size() << " " << variables.size() << std::endl;
	return result;
}

std::vector<std::vector<int>> build_counterexample(const z3::expr & counterexample,const std::vector<int> & right, const z3::expr & edges, z3::context & context, const z3::expr_vector & variables, const z3::expr_vector & variables_dash, const z3::expr_vector & all_variables, const int n)
{
	std::cout << "build ce " << std::endl;
	for (int i = 0; (unsigned)i < variables.size(); i++)
	{
		std::cout << "variables[" << i << "] :" << variables[i] << " variables_dash[" << i << "] :" << variables_dash[i] << std::endl;
	}
	// pushe alle vektoren in result, bis n erreicht, dann den mitgegeben zusätzlich
	std::vector<std::vector<int>> result;
	auto solver = z3::solver(context);
	solver.add(counterexample);
	result.push_back(right);
	for(int i = 0; i < n; i++){
		if (solver.check() == z3::sat){
			auto m = solver.get_model();
			z3::expr_vector sol(context);
			for (unsigned l = 0; (unsigned)l < m.size(); l++){
				z3::func_decl v = m[l];	
				sol.push_back(m.get_const_interp(v));			
			}
			z3::expr test = context.bool_val(true);
			for(int j = 0; (unsigned)j < variables_dash.size(); j++){
				test =  (test) && (variables_dash[j] == m.eval(variables_dash[j]));
			}
			std::vector<int> tmp;
			for(int k = 0; (unsigned)k < variables_dash.size(); k++){
				int j;
				Z3_get_numeral_int(context, m.eval(variables_dash[k]), &j);
				tmp.push_back(j);
			}
			result.push_back(tmp);
			solver.add(!test);
			// add counterexample mit successor
		}
		else {
			//std::cout << "all successors found" << std::endl;
			break;
		}
	}
	return result;
}

std::vector<std::vector<int>> existential_check(const z3::expr & hypothesis, z3::expr & hypothesis_edge_nodes, 
const z3::expr & vertices, const z3::expr & vertices_dash, const z3::expr & vertices_player0, 
const z3::expr & edges, z3::context & context,const z3::expr_vector & all_variables,
 const z3::expr_vector & variables, const z3::expr_vector & variables_dash, const int & n)
{
	std::vector<std::vector<int>> result;
	auto solver = z3::solver(context);
	
	z3::expr nodes_in_V0_and_W_without_successor_in_W = hypothesis && vertices_player0 && !exists(variables_dash,vertices && edges && hypothesis_edge_nodes);

	solver.add(nodes_in_V0_and_W_without_successor_in_W);
	if (solver.check()== z3::sat){
			std::cout << "counterexample for existential condition!:\n" << solver.get_model() << "\n";
			auto m = solver.get_model();
			z3::expr_vector sol(context);
			for (unsigned i = 0; i < m.size(); i++){
				z3::func_decl v = m[i];	
				sol.push_back(m.get_const_interp(v));
			}
			std::vector<int> tmp;
			z3::expr test = context.bool_val(true);
			for(int i = 0; (unsigned)i < variables.size(); i++){
				test =  (test) && (all_variables[i] == m.eval(all_variables[i]));
				int j;
				Z3_get_numeral_int(context, m.eval(variables[i]), &j);
				tmp.push_back(j);
			}
			return build_counterexample(test && edges, tmp, edges, context, variables,variables_dash, all_variables, n);
			//solver.add(!test);
	}	
	else {
		std::cout << "Hypothesis holds for the existential condition" << std::endl;
		return result;
	}
}
/*std::vector<std::tuple<std::vector<int>,std::vector<int>>> build_counterexample_universal(const z3::expr & counterexample, const std::vector<int> & right, const z3::expr & edges, z3::context & context, const z3::expr_vector variables, const z3::expr_vector variables_dash, const z3::expr_vector all_variables, const int n)
{
	// TODO : male dir den graphen auf und guck ob das stimmt was da raus kommt. danach existential
	auto solver = z3::solver(context);
	solver.add(counterexample);
	std::vector<std::tuple<std::vector<int>,std::vector<int>>> result;
	for(int j = 0; j < n; j++){
		if (solver.check() == z3::sat){
			auto m = solver.get_model();
			z3::expr_vector sol(context);
			for (unsigned i = 0; i < m.size(); i++){
				z3::func_decl v = m[i];	
				sol.push_back(m.get_const_interp(v));			
			}
			std::cout << "Model:\n" << m << "\n";
			z3::expr test = context.bool_val(true);
			std::vector<int> left;
			for(int i = 0; i < variables_dash.size(); i++){
				std::cout << variables_dash[i] << std::endl;
				test =  (test) && (variables_dash[i] == m.eval(variables_dash[i]));
				int j;
				Z3_get_numeral_int(context, m.eval(variables_dash[i]), &j);
				std::cout << " teste hier was du machst BUILD " << j <<std::endl;
				left.push_back(j);
			}
			std::tuple<std::vector<int>,std::vector<int>> counterexample(left,right);
			result.push_back(counterexample);		
			for(int i = 0; i < left.size(); i++){
				std::cout << " teste hier was du machst LINKS COUNTEREXAMPLE" << std::get<0>(counterexample)[i] <<std::endl;
				std::cout << " teste hier was du machst RECHTS COUNTEREXAMPLE" << std::get<1>(counterexample)[i] <<std::endl;

			}
			solver.add(!test);
			std::cout << "test:\n" << test << std::endl;
			// add counterexample mit successor
		}
		else {
			std::cout << "all successors found" << std::endl;
			break;
		}
	}
	return result;
}*/
std::vector<std::vector<int>> universal_check(const z3::expr & hypothesis, z3::expr & hypothesis_edge_nodes, 
const z3::expr & vertices, const z3::expr & vertices_dash, const z3::expr & vertices_player1, 
const z3::expr & edges, z3::context & context, const z3::expr_vector & all_variables,
 const z3::expr_vector & variables,const z3::expr_vector & variables_dash, const int n){
	
	std::vector<std::vector<int>> result;
	auto solver = z3::solver(context);

	z3::expr nodes_in_V1_and_W_without_successor_in_W =  vertices_player1 && hypothesis && exists(variables_dash,vertices && edges && !hypothesis_edge_nodes);
	
	solver.add(nodes_in_V1_and_W_without_successor_in_W);
	if (solver.check()== z3::sat){
			auto m = solver.get_model();
			z3::expr_vector sol(context);
			for (unsigned i = 0; i < m.size(); i++){
				z3::func_decl v = m[i];	
				sol.push_back(m.get_const_interp(v));			
				}
			std::cout << "counterexample for universal condition!:\n" << solver.get_model() << "\n";
			z3::expr test = context.bool_val(true);
			std::vector<int> tmp;
			for(int i = 0; (unsigned)i < sol.size(); i++){
				test =  (test) && (variables[i] == m.eval(variables[i]));
				int j;
				Z3_get_numeral_int(context, m.eval(variables[i]), &j);
				tmp.push_back(j);
			}

			return build_counterexample(test && edges, tmp, edges, context, variables,variables_dash, all_variables, n);
			//solver.add(!test);
	}	
	else {
		std::cout << "Hypothesis holds for the universal condition" << std::endl;
		return result;
	}
}

void prove(z3::expr conjecture) {
    z3::context & c = conjecture.ctx();
    auto s = z3::solver(c);
    s.add(!conjecture);
    std::cout << "conjecture:\n" << conjecture << "\n";
    if (s.check() == z3::unsat) {
        std::cout << "proved" << "\n";
    }
    else {
        std::cout << "failed to prove" << "\n";
        std::cout << "counterexample for safe condition!:\n" << s.get_model() << "\n";
    }
}

void test(){
		std::cout << "testing... the compiling" << std::endl;
}


