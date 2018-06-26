#include <iostream>
#include <fstream>
#include <vector>
#include <set>
#include <tuple>
#include <typeinfo>
#include "z3++.h"
#include "teacher.h"
struct Counterexample
{
	std::vector<int> datapoints;
	// 0 = false; 1 = true; 2 = ?
	int classification;
	
	bool operator==(const Counterexample& c)
	{
		std::cout << " = vergleichen! " << std::endl;
	}
	bool operator<(const Counterexample& c)
	{
		std::cout << " < vergleichen! " << std::endl;
	}
};
void prep(int  i)
{
	std::ofstream myfile;
	myfile.open("dillig12.bpl.attributes");
	myfile << "cat,$func,1\n";
	for (int j = 0; j < i; j++){
		myfile << "int,$a" << j << "\n";

	}
	myfile.close();
}
void store(const Counterexample  ce)
{
	
}

Counterexample create_initial_counterexample(const std::vector<int>  ce)
{
	Counterexample(a);
	return a;
}

Counterexample create_safe_counterexample(const std::vector<int>  ce)
{
	Counterexample(a);
	return a;
}

Counterexample create_existential_counterexample(const std::vector<std::vector<int>>  ce)
{
	Counterexample(a);
	return a;	
}
Counterexample create_universal_counterexample(const std::vector<std::vector<int>>  ce)
{
	Counterexample(a);
	return a;	
}
int main()
{
	prep(2);
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
	std::vector<int> test1;
	std::vector<int> test2;
	test1 = check_initial_condition(hypothesis, initial_vertices, ctx, variables);
	if (test1.size() == 0){
		std::cout << "Initial CE leer" << std::endl;
	}
	else {
		for (int i = 0; i < test1.size(); i++){
			std::cout << "Initial: " << i << ": " << test1[i] << std::endl;
		} 
		Counterexample ce = create_initial_counterexample(test1);
		store(ce);
	}
	test2 = check_safe_condition(hypothesis,safe_vertices,ctx,variables);
	if (test2.size() == 0){
		std::cout << "Safe CE leer" << std::endl;
	}
	else {
		for (int i = 0; i < test2.size(); i++){
			std::cout << "Safe: " << i << ": " << test2[i] << std::endl;
		}
		Counterexample ce = create_safe_counterexample(test2); 
		store(ce);
	}
	std::vector<std::vector<int>> new_test1;
	std::vector<std::vector<int>> new_test2;
	new_test2 = existential_check(hypothesis, hypothesis_edges_test, vertices, vertices_dash,vertices_player0, edges, ctx, all_variables, variables, variables_dash, n);
	
	if (new_test1.size() == 0){
		std::cout << "Existential CE leer" << std::endl;
	}
	else {
		for (int i = 0; i < new_test1.size(); i++){
			//std::vector<int> a = (test[0]);
			for (int j = 0; j < new_test1[i].size(); j++){
				std::cout << "Ex: " << j << ": " << new_test1[i][j] << std::endl;	
			}
		} 
		Counterexample ce = create_existential_counterexample(new_test1);
		store(ce);
	}
	new_test2 = universal_check(hypothesis, hypothesis_edges_test, vertices, vertices_dash,vertices_player1, edges, ctx, all_variables, variables, variables_dash, n);
	if (new_test2.size() == 0){
		std::cout << "Uni CE leer" << std::endl;
	}
	else {
		for (int i = 0; i < new_test2.size(); i++){
			//std::vector<int> a = (test[0]);
			for (int j = 0; j < new_test2[i].size(); j++){
				std::cout << "Uni: " << j << ": " << new_test2[i][j] << std::endl;	
			}
		}
		Counterexample ce = create_universal_counterexample(new_test2);
		store(ce);
	}
	std::ofstream myfile;
	myfile.open("example.txt");
	myfile << "Writing this to a file. \n";
	myfile.close();
	Counterexample(a);
	Counterexample(b);
	a==b;
	a<b;
}
