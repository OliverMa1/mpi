#include <iostream>
#include <vector>
#include <tuple>
#include <typeinfo>
#include "z3++.h"
#include "test1.h"
struct counterexample_struct
{
	bool found;
};
struct initial_counterexample_struct : counterexample_struct
{
	std::vector<int> initial_ce;	
};

struct safe_counterexample_struct : counterexample_struct
{
	std::vector<int> safe_ce;
};


struct existential_counterexample_struct : counterexample_struct
{
	std::vector<std::vector<int>> existential_ce;
};

struct universal_counterexample_struct : counterexample_struct
{
	std::vector<std::tuple<std::vector<int>,std::vector<int>>> universal_ce;
};
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

initial_counterexample_struct check_initial_condition(const z3::expr & hypothesis, const z3::expr & initial_vertices, z3::context & context, z3::expr_vector variables)
{
	initial_counterexample_struct a;
	a.found = false;
	// initial_vertices subset hypothesis
	std::vector<int> result;
	auto solver = z3::solver(context);
	z3::expr check = implies(initial_vertices,hypothesis);
	solver.add(!check);
	if (solver.check() == z3::unsat) {
		std::cout << "Hypothesis holds for initial condition!" << std::endl;
		return a;
	}
	else {
		auto m = solver.get_model();
		z3::expr_vector sol(context);
		for (unsigned i = 0; i < m.size(); i++){
			z3::func_decl v = m[i];	
			sol.push_back(m.get_const_interp(v));
			//std::cout<< "m[i]: " << m[i] << "v.arity()" << v.arity() << v.name() << " = " << m.get_const_interp(v) << std::endl;
		}
		for(int i = 0; i < sol.size(); i++){
			std::cout << i << ": " << sol[i] << variables[i]<< ": " << m.eval(variables[i]) << "\n";
			int j;
			Z3_get_numeral_int(context, m.eval(variables[i]), &j);
			result.push_back(j);
		}
		for (int i = 0; i < result.size(); i++)
		{
			std::cout << i << ": " << result[i] << std::endl;
		}
		std::cout << "SOL: " << sol << "\n";
		std::cout << "counterexample for initial condition!:\n" << solver.get_model() << "\n";
		a.found = true;
		a.initial_ce = result;
	}
}
safe_counterexample_struct check_safe_condition(const z3::expr & hypothesis, const z3::expr & safe_vertices, z3::context & context, z3::expr_vector variables)
{	
	safe_counterexample_struct a;
	a.found = false;
	// wenn hypothesis subset safe_vertices 
	std::vector<int> result;
	auto solver = z3::solver(context);
	z3::expr check = implies(hypothesis, safe_vertices);
	solver.add(!check);
	if (solver.check() == z3::unsat) {
		std::cout << "Hypothesis holds for safe condition!!" << std::endl;
		return a;
	}
	else {
		auto m = solver.get_model();
		z3::expr_vector sol(context);
		for (unsigned i = 0; i < m.size(); i++){
			z3::func_decl v = m[i];	
			sol.push_back(m.get_const_interp(v));
			std::cout<< "m[i]: " << m[i] << "v.arity() " << v.arity() << v.name() << " = " << m.get_const_interp(v) << std::endl;
		}
		std::cout << "SOL: " << sol << sol[1]<<"\n";
		for(int i = 0; i < sol.size(); i++){
			std::cout << i << ": " << sol[i] << variables[i]<< ": " << m.eval(variables[i]) << "\n";
			int j;
			Z3_get_numeral_int(context, m.eval(variables[i]), &j);
			result.push_back(j);
		}
		for (int i = 0; i < result.size(); i++)
		{
			std::cout << i << "LÖSUNG: " << result[i] << std::endl;
		}
		a.found = true;
		a.safe_ce = result;
		std::cout << "counterexample for safe condition!:\n" << solver.get_model() << "result: " << result[0] << "\n";
		return a;
	}
}

std::vector<std::vector<int>> build_counterexample_existential(const z3::expr & counterexample,const std::vector<int> right, const z3::expr & edges, z3::context & context, const z3::expr_vector variables, const z3::expr_vector variables_dash, const z3::expr_vector all_variables, const int n)
{
	// pushe alle vektoren in result, bis n erreicht, dann den mitgegeben zusätzlich
	std::vector<std::vector<int>> result;
	auto solver = z3::solver(context);
	solver.add(counterexample);
	for(int i = 0; i < n; i++){
		if (solver.check() == z3::sat){
			auto m = solver.get_model();
			z3::expr_vector sol(context);
			for (unsigned l = 0; l < m.size(); l++){
				z3::func_decl v = m[l];	
				sol.push_back(m.get_const_interp(v));			
			}
			std::cout << "Model BUILD EXISTENTIAL:\n" << m << "\n";
			z3::expr test = context.bool_val(true);
			for(int j = 0; j < variables_dash.size(); j++){
				std::cout << variables_dash[i] << std::endl;
				test =  (test) && (variables_dash[i] == m.eval(variables_dash[i]));
			}
			std::vector<int> tmp;
			for(int k = 0; k < variables_dash.size(); k++){
				std::cout << "heeeeelo" << std::endl;
				int j;
				Z3_get_numeral_int(context, m.eval(variables_dash[k]), &j);
				tmp.push_back(j);
			}
			for (int k = 0; k < tmp.size(); k++)
			{
				std::cout << k << " : " << tmp[k] << std::endl;
			}
			result.push_back(tmp);
			solver.add(!test);
			std::cout << "test:\n" << test << std::endl;
			// add counterexample mit successor
		}
		else {
			std::cout << "all successors found" << std::endl;
			break;
		}
	}
	result.push_back(right);
	return result;
}

existential_counterexample_struct existential_check(const z3::expr & hypothesis, z3::expr & hypothesis_edge_nodes, 
const z3::expr & vertices, const z3::expr & vertices_dash, const z3::expr & vertices_player0, 
const z3::expr & edges, z3::context & context, z3::expr_vector all_variables,
 z3::expr_vector variables, z3::expr_vector variables_dash, const int & n)
{
	existential_counterexample_struct a;
	a.found = false;
	auto solver = z3::solver(context);
	
	z3::expr nodes_in_V0_and_W_without_successor_in_W = hypothesis && vertices_player0 && !exists(variables_dash,vertices && edges && hypothesis_edge_nodes);

	solver.add(nodes_in_V0_and_W_without_successor_in_W);
	if (solver.check()== z3::sat){
			auto m = solver.get_model();
			z3::expr_vector sol(context);
			for (unsigned i = 0; i < m.size(); i++){
				z3::func_decl v = m[i];	
				sol.push_back(m.get_const_interp(v));
			}
			std::cout << "counterexample for existential condition!:\n" << solver.get_model() << "\n";
			std::vector<int> tmp;
			z3::expr test = context.bool_val(true);
			for(int i = 0; i < sol.size(); i++){
				test =  (test) && (all_variables[i] == m.eval(all_variables[i]));
				// baue den ersten int vektor für das rechteste element
				int j;
				Z3_get_numeral_int(context, m.eval(variables[i]), &j);
				std::cout << " teste hier was du machst EXISTENTIAL" << j <<std::endl;
				tmp.push_back(j);
			}
			a.found = true;
			a.existential_ce = build_counterexample_existential(test && edges, tmp, edges, context, variables,variables_dash, all_variables, n);
			//solver.add(!test);
	}	
	if (solver.check() == z3::unsat) {
		std::cout << "Hypothesis holds for the existential condition" << std::endl;
		return a;
	}
}
std::vector<std::tuple<std::vector<int>,std::vector<int>>> build_counterexample_universal(const z3::expr & counterexample, const std::vector<int> & right, const z3::expr & edges, z3::context & context, const z3::expr_vector variables, const z3::expr_vector variables_dash, const z3::expr_vector all_variables, const int n)
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
}
universal_counterexample_struct universal_check(const z3::expr & hypothesis, z3::expr & hypothesis_edge_nodes, 
const z3::expr & vertices, const z3::expr & vertices_dash, const z3::expr & vertices_player1, 
const z3::expr & edges, z3::context & context, z3::expr_vector all_variables,
 z3::expr_vector variables, z3::expr_vector variables_dash, const int n){
	 universal_counterexample_struct a;
	 a.found = false;
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
			for(int i = 0; i < sol.size(); i++){
				test =  (test) && (variables[i] == m.eval(variables[i]));
				int j;
				Z3_get_numeral_int(context, m.eval(variables[i]), &j);
				std::cout << " teste hier was du machst " << j <<std::endl;
				tmp.push_back(j);
			}
			a.found = true;
			a.universal_ce = build_counterexample_universal(test && edges, tmp, edges, context, variables,variables_dash, all_variables, n);
			//solver.add(!test);
	}	
	if (solver.check() == z3::unsat) {
		std::cout << "Hypothesis holds for the universal condition" << std::endl;
		return a;
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
counterexample_struct learn(const z3::expr & hypothesis, z3::expr & hypothesis_edge_nodes, 
const z3::expr & vertices, const z3::expr & vertices_dash, 
const z3::expr & initial_vertices, const z3::expr & safe_vertices,
 const z3::expr & vertices_player0, const z3::expr & vertices_player1, 
const z3::expr & edges, z3::context & context, z3::expr_vector all_variables,
 z3::expr_vector variables, z3::expr_vector variables_dash, const int n){
	// implement finding a counterexample and returning it!
	counterexample_struct result;
	check_initial_condition(hypothesis, initial_vertices,context, variables);
	check_safe_condition(hypothesis, safe_vertices, context, variables);
	existential_check(hypothesis, hypothesis_edge_nodes, vertices, vertices_dash,vertices_player0, edges, context, all_variables, variables, variables_dash, n);
	universal_check(hypothesis, hypothesis_edge_nodes, vertices, vertices_dash,vertices_player1, edges, context, all_variables, variables, variables_dash, n);

}
void test(){
		std::cout << "testing..." << std::endl;
}
int main()
{

	z3::context ctx;

	auto four = ctx.int_val(4);
	z3::expr x = ctx.int_const("x");
	auto y = ctx.int_const("y");
	z3::expr x_dash = ctx.int_const("x'");
	auto y_dash = ctx.int_const("y'");
	z3::expr_vector variables(ctx);
	z3::expr_vector all_variables(ctx);
	variables.push_back(x);
	variables.push_back(y);
	z3::expr_vector variables_dash(ctx);
	variables_dash.push_back(x_dash);
	variables_dash.push_back(y_dash);
	all_variables.push_back(x);
	all_variables.push_back(y);
	all_variables.push_back(x_dash);
	all_variables.push_back(y_dash);


	z3::expr hypothesis_edges = (x_dash < 10 && y_dash == 2);
	auto node_0 = ((x == 2) && (y == 2));
	auto node_1 = ((x == 3) && (y == 3));
	auto node_2 = ((x == 2) && (y == 3));
	auto node_3 = ((x == 3) && (y == 2));
	auto node_4 = ((x == 4) && (y == 2));
	auto node_5 = ((x == 4) && (y == 4));
	auto node_0_dash = ((x_dash == 2) && (y_dash == 2));
	auto node_1_dash = ((x_dash == 3) && (y_dash == 3));
	auto node_2_dash = ((x_dash == 2) && (y_dash == 3));
	auto node_3_dash = ((x_dash == 3) && (y_dash == 2));
	auto node_4_dash = ((x_dash == 4) && (y_dash == 2));
	auto node_5_dash = ((x_dash == 4) && (y_dash == 4));
	
	z3::expr initial_vertices = node_0;
	z3::expr safe_vertices = node_0 || node_4 || node_3;
	auto vertices_player0 = node_0 || node_1 || node_5;
	auto vertices_player1 = node_2 || node_3 || node_4;
	auto vertices = node_0 || node_1 || node_2 || node_3 || node_4;//vertices_player0 || vertices_player1;
	auto vertices_dash = vertices.substitute(variables,variables_dash);
	auto edges = (node_0 && node_1_dash)|| (node_0 && node_2_dash) || (node_0 && node_3_dash) 
	|| (node_0 && node_1_dash) || (node_3 && node_4_dash) || (node_4 && node_0_dash) || node_1 && node_3_dash || node_2 && node_3_dash || node_2 && node_0_dash || node_2 && node_1_dash || node_1 && node_5_dash || node_0 && node_5_dash;
	//z3::expr hypothesis = vertices;
	z3::expr hypothesis = node_0 || node_1 || node_4 || node_2;
	z3:: expr hypothesis_edges_test = hypothesis.substitute(variables,variables_dash);
	const int n = 10;
	std::vector<int> test;
	check_initial_condition(hypothesis, initial_vertices, ctx, variables);
	test = check_safe_condition(hypothesis,safe_vertices,ctx,variables).safe_ce;
	auto r = check_safe_condition(hypothesis,safe_vertices,ctx,variables).found;
	for (int i = 0; i < test.size(); i++){
		std::cout << "TEST für CE: " << test[i] << " " <<  r << std::endl;
	}
	existential_check(hypothesis, hypothesis_edges_test, vertices, vertices_dash,vertices_player0, edges, ctx, all_variables, variables, variables_dash, n);
	universal_check(hypothesis, hypothesis_edges_test, vertices, vertices_dash,vertices_player1, edges, ctx, all_variables, variables, variables_dash, n);
}

