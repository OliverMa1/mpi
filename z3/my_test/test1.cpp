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

void check_initial_condition(const z3::expr & hypothesis, const z3::expr & initial_vertices, z3::context & context, z3::expr_vector variables)
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
	}
}
void check_safe_condition(const z3::expr & hypothesis, const z3::expr & safe_vertices, z3::context & context, z3::expr_vector variables)
{
	// wenn hypothesis subset safe_vertices 
	std::vector<int> result;
	auto solver = z3::solver(context);
	z3::expr check = implies(hypothesis, safe_vertices);
	solver.add(!check);
	if (solver.check() == z3::unsat) {
		std::cout << "Hypothesis holds for safe condition!" << std::endl;
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
			std::cout << i << ": " << result[i] << std::endl;
		}
		std::cout << "counterexample for safe condition!:\n" << solver.get_model() << "result: " << result[0] << "\n";
	}
}

void build_counterexample_existential(const z3::expr & counterexample, const z3::expr & edges, z3::context & context, const z3::expr_vector variables, const z3::expr_vector variables_dash, const z3::expr_vector all_variables, const int n)
{
	std::vector<std::vector<int>> result;
	auto solver = z3::solver(context);
	solver.add(counterexample);
	// vector um alle successor zu speichern.
	z3::expr_vector solutions(context);
	for(int i = 0; i < n; i++){
		if (solver.check() == z3::sat){
			auto m = solver.get_model();
			z3::expr_vector sol(context);
			for (unsigned l = 0; l < m.size(); l++){
				z3::func_decl v = m[l];	
				sol.push_back(m.get_const_interp(v));			
			}
			std::cout << "Model:\n" << m << "\n";
			z3::expr test = context.bool_val(true);
			for(int j = 0; j < variables_dash.size(); j++){
				std::cout << variables_dash[i] << std::endl;
				test =  (test) && (variables_dash[i] == m.eval(variables_dash[i]));
			}
			std::vector<int> tmp;
			for(int k = 0; k < variables.size(); k++){
				std::cout << "heeeeelo" << std::endl;
				int j;
				Z3_get_numeral_int(context, m.eval(variables[i]), &j);
				tmp.push_back(j);
			}
			for (int k = 0; k < tmp.size(); k++)
			{
				std::cout << k << " : " << tmp[k] << std::endl;
			}
			solver.add(!test);
			std::cout << "test:\n" << test << std::endl;
			// add counterexample mit successor
			solutions.push_back(test);
		}
		else {
			std::cout << "all successors found" << std::endl;
			break;
		}
	}
	solutions.push_back(counterexample);
}

void existential_check(const z3::expr & hypothesis, z3::expr & hypothesis_edge_nodes, 
const z3::expr & vertices, const z3::expr & vertices_dash, const z3::expr & vertices_player0, 
const z3::expr & edges, z3::context & context, z3::expr_vector all_variables,
 z3::expr_vector variables, z3::expr_vector variables_dash)
{
	auto solver = z3::solver(context);
	
	z3::expr nodes_in_V0_and_W_without_successor_in_W = hypothesis && vertices_player0 && !exists(variables_dash,vertices && edges && hypothesis_edge_nodes);

	solver.add(nodes_in_V0_and_W_without_successor_in_W);
	for (int i = 0; i < 5; i++){
		if (solver.check()== z3::sat){
			auto m = solver.get_model();
			z3::expr_vector sol(context);
			for (unsigned i = 0; i < m.size(); i++){
				z3::func_decl v = m[i];	
				sol.push_back(m.get_const_interp(v));
			}
			std::cout << "counterexample for existential condition!:\n" << solver.get_model() << "\n";

			z3::expr test = context.bool_val(true);
			for(int i = 0; i < sol.size(); i++){
				test =  (test) && (all_variables[i] == m.eval(all_variables[i]));
			}
			solver.add(!test);
		}
	}
	if (solver.check() == z3::unsat) {
		std::cout << "Hypothesis holds for the existential condition" << std::endl;
	}
}
void build_counterexample_universal(const z3::expr & counterexample, const z3::expr & edges, z3::context & context, const z3::expr_vector variables, const z3::expr_vector variables_dash, const z3::expr_vector all_variables, const int n)
{
	
	auto solver = z3::solver(context);
	solver.add(counterexample);
	std::vector<std::tuple<std::vector<int>,std::vector<int>>> result;
	// erstelle int vector für initial counterexample
	std::vector<int> start_node;
	for(int j = 0; i < n; j++){
		if (solver.check() == z3::sat){
			auto m = solver.get_model();
			z3::expr_vector sol(context);
			for (unsigned i = 0; i < m.size(); i++){
				z3::func_decl v = m[i];	
				sol.push_back(m.get_const_interp(v));			
			}
			std::cout << "Model:\n" << m << "\n";
			z3::expr test = context.bool_val(true);
			for(int i = 0; i < variables_dash.size(); i++){
				std::cout << variables_dash[i] << std::endl;
				test =  (test) && (variables_dash[i] == m.eval(variables_dash[i]));
			}
			// erstelle int vector für die nachfolger  
			// erstelle ein tupel aus beiden vektoren 
			// füge result dem tupel hinzu			
			
			solver.add(!test);
			std::cout << "test:\n" << test << std::endl;
			// add counterexample mit successor
		}
		else {
			std::cout << "all successors found" << std::endl;
		}
	}
}
void universal_check(const z3::expr & hypothesis, z3::expr & hypothesis_edge_nodes, 
const z3::expr & vertices, const z3::expr & vertices_dash, const z3::expr & vertices_player1, 
const z3::expr & edges, z3::context & context, z3::expr_vector all_variables,
 z3::expr_vector variables, z3::expr_vector variables_dash, const int n){
	auto solver = z3::solver(context);

	z3::expr nodes_in_V1_and_W_without_successor_in_W =  vertices_player1 && hypothesis && exists(variables_dash,vertices && edges && !hypothesis_edge_nodes);
	
	solver.add(nodes_in_V1_and_W_without_successor_in_W);
	for (int i = 0; i < 5; i++){
		if (solver.check()== z3::sat){
			auto m = solver.get_model();
			z3::expr_vector sol(context);
			for (unsigned i = 0; i < m.size(); i++){
				z3::func_decl v = m[i];	
				sol.push_back(m.get_const_interp(v));			
				}
			std::cout << "counterexample for universal condition!:\n" << solver.get_model() << "\n";
			z3::expr test = context.bool_val(true);
			for(int i = 0; i < sol.size(); i++){
				test =  (test) && (variables[i] == m.eval(variables[i]));
			}

			build_counterexample_universal(test && edges, edges, context, variables,variables_dash, all_variables, n);
			solver.add(!test);
		}
	}
	if (solver.check() == z3::unsat) {
		std::cout << "Hypothesis holds for the universal condition" << std::endl;
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
	
	/*z3::expr hypothesis = (x < 10 && y == 2);
	z3:: expr hypothesis_edges_test = hypothesis.substitute(variables,variables_dash);
	z3::expr hypothesis_edges = (x_dash < 10 && y_dash == 2);
	auto node_0 = ((x == 2) && (y == 2));
	auto node_1 = ((x == 3) && (y == 3));
	auto node_2 = ((x == 2) && (y == 3));
	auto node_3 = ((x == 3) && (y == 2));
	auto node_4 = ((x == 4) && (y == 2));
	auto node_0_dash = ((x_dash == 2) && (y_dash == 2));
	auto node_1_dash = ((x_dash == 3) && (y_dash == 3));
	auto node_2_dash = ((x_dash == 2) && (y_dash == 3));
	auto node_3_dash = ((x_dash == 3) && (y_dash == 2));
	auto node_4_dash = ((x_dash == 4) && (y_dash == 2));
	z3::expr initial_vertices = node_0;
	z3::expr safe_vertices = node_0 || node_4 || node_3;
	auto vertices_player0 = node_0 || node_1;
	auto vertices_player1 = node_2 || node_3 || node_4;
	auto vertices = node_0 || node_1 || node_2 || node_3 || node_4;//vertices_player0 || vertices_player1;
	auto vertices_dash = vertices.substitute(variables,variables_dash);
	auto edges = (node_0 && node_1_dash) || (node_1 && node_0_dash) || (node_0 && node_2_dash) || (node_0 && node_3_dash) 
	|| (node_0 && node_1_dash) || (node_3 && node_4_dash) || (node_4 && node_0_dash);*/

	z3::expr hypothesis_edges = (x_dash < 10 && y_dash == 2);
	auto node_0 = ((x == 2) && (y == 2));
	auto node_1 = ((x == 3) && (y == 3));
	auto node_2 = ((x == 2) && (y == 3));
	auto node_3 = ((x == 3) && (y == 2));
	auto node_4 = ((x == 4) && (y == 2));
	auto node_0_dash = ((x_dash == 2) && (y_dash == 2));
	auto node_1_dash = ((x_dash == 3) && (y_dash == 3));
	auto node_2_dash = ((x_dash == 2) && (y_dash == 3));
	auto node_3_dash = ((x_dash == 3) && (y_dash == 2));
	auto node_4_dash = ((x_dash == 4) && (y_dash == 2));
	
	z3::expr initial_vertices = node_0;
	z3::expr safe_vertices = node_0 || node_4 || node_3;
	auto vertices_player0 = node_0 || node_1;
	auto vertices_player1 = node_2 || node_3 || node_4;
	auto vertices = node_0 || node_1 || node_2 || node_3 || node_4;//vertices_player0 || vertices_player1;
	auto vertices_dash = vertices.substitute(variables,variables_dash);
	auto edges = (node_0 && node_1_dash)|| (node_0 && node_2_dash) || (node_0 && node_3_dash) 
	|| (node_0 && node_1_dash) || (node_3 && node_4_dash) || (node_4 && node_0_dash) || node_1 && node_3_dash || node_2 && node_3_dash || node_2 && node_0_dash || node_2 && node_1_dash;
	//z3::expr hypothesis = vertices;
	z3::expr hypothesis = vertices_player0 || node_4 || node_2;
	z3:: expr hypothesis_edges_test = hypothesis.substitute(variables,variables_dash);
	const int n = 10;
	check_initial_condition(hypothesis, initial_vertices, ctx, variables);
	check_safe_condition(hypothesis,safe_vertices,ctx,variables);
	existential_check(hypothesis, hypothesis_edges_test, vertices, vertices_dash,vertices_player0, edges, ctx, all_variables, variables, variables_dash);
	universal_check(hypothesis, hypothesis_edges_test, vertices, vertices_dash,vertices_player1, edges, ctx, all_variables, variables, variables_dash, n);

	/*auto e1 = x < y +3;

	auto e = exists(y,x < four);


	auto s = z3::solver(ctx);
	s.add(e);
	prove (x + 3 < y == x  < y -3 );

	auto result = s.check();
	std::cout << result << std::endl;


	auto model = s.get_model();
	std::cout << model << std::endl;

	auto idn = model.eval(x + 14, true);
	std::cout << idn << std::endl;	

	std::cout << idn.is_numeral() << std::endl;
	check(e,ctx);

	
	std::cout << "Type of solver: " << typeid(s).name() << std::endl;		std::cout << "Type of solver: " << typeid(s).name() << std::endl;
	std::cout << "Type of context: " << typeid(ctx).name() << std::endl;
	std::cout << "Type of expr: " << typeid(e).name() << std::endl;
	std::cout << "Type of x: " << typeid(x).name() << std::endl;
	std::cout << "Type of result: " << typeid(result).name() << std::endl;
	std::cout << "Type of idn: " << typeid(idn).name() << std::endl;
	z3::expr a = ctx.int_const("a");
	std::cout << "test: " << (typeid(idn).name() == typeid(a).name()) << std::endl;
	std::cout << "test2: " << four.is_int() << std::endl;*/

}

