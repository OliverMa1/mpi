#include <iostream>
#include <fstream>
#include <vector>
#include <string>
#include <set>
#include <map>
#include <iterator>
#include <typeinfo>
#include "z3++.h"
#include "teacher.h"
#include <nlohmann/json.hpp>
using json = nlohmann::json;

namespace ns
{
	struct json_node
	{
		std::string attribute;
		int cut;
		bool classification;
		std::vector<int> children;
	};
}
//fange func ab

struct Counterexample
{
	std::vector<int> datapoints;
	// -1 = ?; 0 = false; 1 = true
	int classification;
	Counterexample(const std::vector<int>  & dp, int c): datapoints(dp), classification(c){}
	friend bool operator==(const Counterexample& c1, const Counterexample& c2)
	{
		bool res;
		res = c1.datapoints == c2.datapoints;
		return res;
	}
	friend bool operator<(const Counterexample& c1, const Counterexample& c2)
	{
		return c1.datapoints < c2.datapoints;
	}
	friend std::ostream& operator<<(std::ostream & stream, const Counterexample & c)
	{
		for (int i = 0; (unsigned)i < c.datapoints.size()-1; i++)
		{
			stream << c.datapoints[i] << ", ";
		}
		stream << c.datapoints[c.datapoints.size()-1];
		if (c.classification == -1)
		{
			stream << ",?";
		}
		else if (c.classification == 0)
		{
			stream << ",false";
		}
		else
		{
			stream << ",true";
		}

		return stream;
	} 
};
	std::map<Counterexample,int> counterexample_map;
	//wrapper objekt für pointer reference wrapper
	std::map<int,Counterexample> position_map;
	std::vector<Counterexample> counterexample_vector;
	std::vector<std::vector<int>> horn_clauses;
	std::map<std::string, z3::expr> variables;
	z3::context ctx;
	z3::expr_vector variables_vector(ctx);
	z3::expr_vector all_variables_vector(ctx);
	z3::expr_vector variables_dash_vector(ctx);
	
z3::expr read_json(json j)
{

	if(j["attribute"] == "$func")
	{
		return read_json(j["children"][0]);
	}
	else if (j["children"].is_null())
	{
		int i = j["classification"];
		if (i == 0)
		{
			return ctx.bool_val(true);
		}
		else
		{
			return ctx.bool_val(false);
		}
	}
	else
	{

		std::string varname = j["attribute"].get<std::string>();
		std::map<std::string, z3::expr>::iterator it;
		it = variables.find(varname);
		if (it == variables.end())
		{
			std::cout << varname << " nicht gefunden" << std::endl;
			return ctx.bool_val(false);
		}
		else
		{
			z3::expr x = (it->second);	
			z3::expr left = read_json(j["children"][0]);
			z3::expr right = read_json(j["children"][1]);
			z3::expr c = x <= ctx.int_val(j["cut"].get<int>());
			z3::expr b = ite(c,left,right);
			return b;
		}
		
	}
	
}
void prep(int  i)
{
	std::ofstream myfile;
	myfile.open("data/dillig12.bpl.attributes");
	myfile << "cat,$func,1\n";
	for (int j = 0; j < i; j++){
		std::string s = "$a" + std::to_string(j);
		char const *pchar = s.c_str();
		myfile << "int," << pchar << "\n";
		z3::expr x = ctx.int_const(pchar);
		z3::expr x_dash = ctx.int_const((s + "'").c_str());
		variables_vector.push_back(x);
		variables_dash_vector.push_back(x_dash);
		all_variables_vector.push_back(x);
		variables.insert(std::make_pair(s,x));
		std::cout << "eingefügt in variables: " << s << " " << x << std::endl;
		std::cout << variables.find(s)->second << std::endl;
	}
	for (int j = 0; (unsigned)j < variables_dash_vector.size(); j++)
	{
		all_variables_vector.push_back(variables_dash_vector[j]);
	}
	myfile.close();
}

void write()
{
	std::ofstream myfile;
	myfile.open("data/dillig12.bpl.data");
	for (int i = 0; (unsigned)i < counterexample_vector.size()-1;i++)
	{
		myfile << 0 << "," << counterexample_vector[i] << "\n";
	}
	myfile << 0 << "," << counterexample_vector[counterexample_vector.size()-1];
	myfile.close();	
	myfile.open("data/dillig12.bpl.horn");
	for (int i = 0; (unsigned)i < horn_clauses.size(); i ++)
	{
		myfile << horn_clauses[i][0];
		for (int j = 1; (unsigned)j < horn_clauses[i].size(); j++)
		{
			myfile << ", " << horn_clauses[i][j];
		}
		myfile << "\n";
	}
}

void store_horn(std::vector<int> horn)
{
	std::cout << "entered HORN" << std::endl;
		for (int i = 0; (unsigned)i < horn.size(); i++)
		{
			std::cout << i << ": " << horn[i] << std::endl;
		}
		horn_clauses.push_back(horn);
}
int store(Counterexample  ce)
{
	int position = -1;
	std::map<Counterexample, int>::iterator it = counterexample_map.find(ce);
	if (it != counterexample_map.end())
	{
		//check ob jetztiges > gefundenes, ersetze dann (true, oder false ersetzen ?)
		position = it -> second;
		std::cout << "Element vorhanden: " << it->first << " at position: " << position << std::endl;
		std::map<int,Counterexample>::iterator it_pos = position_map.find(position);
		std::cout << (position_map.find(position)-> second) << std::endl;
		Counterexample ce_found = it_pos -> second;
		std::cout << "Test: " << "Found: " << ce_found << " Input: " << ce << " erg: " << (ce_found < ce) << std::endl;
		if (ce_found.classification == -1 && ce_found.classification < ce.classification)
		{
			position_map.at(position) = ce;
			counterexample_map.erase(ce);
			counterexample_map.insert(std::make_pair(ce,position));
			counterexample_vector[position] = ce;
			std::cout << "Änderung von position map: " << (position_map.find(position)-> second) << std::endl;
			std::cout << "Bedingung verstärkt von: " << ce_found.classification << " -> " << ce.classification << std::endl; 
		}
		else if (ce.classification == -1)
		{
		}
		else {
			//throw runtime error
			std::cout << "ERROR" << "cefound: " << ce_found << " ce: " << ce << std::endl;
		}		
	}
	else 
	{
		std::cout << "element nicht vorhanden" << std::endl;
		position = counterexample_map.size();
		counterexample_map.insert(std::make_pair(ce, position));
		position_map.insert(std::make_pair(position_map.size(), ce));
		counterexample_vector.push_back(ce);
		std::cout << "Stored: " << ce << " at Position: " << counterexample_map.size()-1 << std::endl;
	}
	std::cout << "Position RETURN: " << position << std::endl;
	return position;
}

int create_and_store_initial_counterexample(const std::vector<int> & ce)
{	
	return store(Counterexample(ce,0));
}

int create_and_store_safe_counterexample(const std::vector<int> & ce)
{
	return store(Counterexample(ce,1));
}
int create_and_store_unclassified_counterexample(const std::vector<int> & ce)
{
	return store(Counterexample(ce,-1));
}
bool create_and_store_existential_counterexample(const std::vector<std::vector<int>> & ce)
{
	std::vector<int> a;
	std::vector<int> positions;
	bool success = true;
	for (int i = ce.size()-1; i >= 0; i--)
	{
		int position = create_and_store_unclassified_counterexample(ce[i]);
		if (position == -1){
			success = false;
		}
		positions.push_back(position);
	}
	std::cout << "Posi size: " << positions.size() << std::endl;
	if (positions.size() > 1){
		store_horn(positions);
	}
	else{
		store(Counterexample(ce[0],1));
	}
	return success;	
}
bool create_and_store_universal_counterexample(const std::vector<std::vector<int>>  & ce)
{
	bool success = true;
	int a = create_and_store_unclassified_counterexample(ce[0]);
	std::cout << ce.size() << std::endl;
	for (int i = 1; (unsigned)i < ce.size(); i++)
	{
		std::vector<int> positions;
		int position = create_and_store_unclassified_counterexample(ce[i]);
		if (position == -1){
			success = false;
		}
		positions.push_back(position);
		positions.push_back(a);
		store_horn(positions);
	}
	return success;		
}
bool initial_check(const z3::expr & hypothesis, const z3::expr & initial_vertices, z3::context & context, const z3::expr_vector & variables)
{
	std::vector<int> test1;
	bool flag = false;
	test1 = check_initial_condition(hypothesis, initial_vertices, context, variables);
		if (test1.size() == 0){
			std::cout << "Initial CE leer" << std::endl;
		}
		else {
			flag = true;
			for (int i = 0; (unsigned)i < test1.size(); i++){
				std::cout << "Initial: " << i << ": " << test1[i] << std::endl;
			} 
			create_and_store_initial_counterexample(test1);
		}
		return flag;
}

bool safe_check(const z3::expr & hypothesis, const z3::expr & safe_vertices, z3::context & context,const z3::expr_vector & variables)

{
	bool flag = false;
	std::vector<int> test2;
	test2 = check_safe_condition(hypothesis,safe_vertices,context,variables);
		
		if (test2.size() == 0){
			std::cout << "Safe CE leer" << std::endl;
		}
		else {
			flag = true;
			for (int i = 0; (unsigned)i < test2.size(); i++){
				std::cout << "Safe: " << i << ": " << test2[i] << std::endl;
			}
			create_and_store_safe_counterexample(test2); 
		}
		return flag;
}

bool ex_check(const z3::expr & hypothesis, z3::expr & hypothesis_edge_nodes, 
const z3::expr & vertices, const z3::expr & vertices_dash, const z3::expr & vertices_player0, 
const z3::expr & edges, z3::context & context,const z3::expr_vector & all_variables,
 const z3::expr_vector & variables, const z3::expr_vector & variables_dash, const int & n)
 {
		bool flag = false;
	 	std::vector<std::vector<int>> new_test1;
		new_test1 = existential_check(hypothesis, hypothesis_edge_nodes, vertices, vertices_dash,vertices_player0, edges, context, all_variables, variables, variables_dash, n);
	
		if (new_test1.size() == 0){
			std::cout << "Existential CE leer" << std::endl;
		}
		else {
			flag = true;
			for (int i = 0; (unsigned)i < new_test1.size(); i++){
				for (int j = 0; (unsigned)j < new_test1[i].size(); j++){
					std::cout << "Ex: " << j << ": " << new_test1[i][j] << std::endl;	
				}
			} 
			create_and_store_existential_counterexample(new_test1);
		}
		return flag;
}
bool uni_check(const z3::expr & hypothesis, z3::expr & hypothesis_edge_nodes, 
const z3::expr & vertices, const z3::expr & vertices_dash, const z3::expr & vertices_player1, 
const z3::expr & edges, z3::context & context, const z3::expr_vector & all_variables,
 const z3::expr_vector & variables, const z3::expr_vector & variables_dash, const int n)
{
	bool flag = false;
	 std::vector<std::vector<int>> new_test2;
	 new_test2 = universal_check(hypothesis, hypothesis_edge_nodes, vertices, vertices_dash,vertices_player1, edges, context, all_variables, variables, variables_dash, n);
		if (new_test2.size() == 0){
			std::cout << "Uni CE leer" << std::endl;
		}
		else {
			flag = true;
			for (int i = 0; (unsigned)i < new_test2.size(); i++){
				for (int j = 0; (unsigned)j < new_test2[i].size(); j++){
					std::cout << "Uni: " << j << ": " << new_test2[i][j] << std::endl;	
				}
			}
			create_and_store_universal_counterexample(new_test2);
		
		}
		return flag;
}

void example_1(z3::expr & initial_vertices, z3::expr & safe_vertices, z3::expr & vertices_player0, z3::expr & vertices_player1, z3::expr & edges,int & n)
{
	prep(2);
	z3::expr x = variables_vector[0];
	auto y = variables_vector[1];
	z3::expr x_dash = variables_dash_vector[0];
	auto y_dash = variables_dash_vector[1];
	initial_vertices = (x == 1) && (y == 0);
	safe_vertices = (x >= 0);
	vertices_player0 = (y == 0);
	vertices_player1 = (y == 1);
	edges = (x == x_dash +1 && y_dash == 1-y) || (x == x_dash -1 && y_dash == 1-y);
	n = 10;
		auto solver = z3::solver(ctx);
		solver.add(edges);
		if (solver.check()== z3::sat){
			std::cout << solver.get_model() << std::endl;
		}
		else
		{
			std::cout << "test fehlgeschlagn" << std::endl;
		}
}

int main()
{


	/*auto four = ctx.int_val(4);
	z3::expr x = variables_vector[0];
	auto y = variables_vector[1];
	z3::expr x_dash = variables_dash_vector[0];
	auto y_dash = variables_dash_vector[1];
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
	auto vertices_dash = vertices.substitute(variables_vector,variables_dash_vector);
	auto edges = (node_0 && node_1_dash)|| (node_0 && node_2_dash) || (node_0 && node_3_dash) 
	|| (node_0 && node_1_dash) || (node_3 && node_4_dash) || (node_4 && node_0_dash) || node_1 && node_3_dash || node_2 && node_3_dash || node_2 && node_0_dash || node_2 && node_1_dash || node_1 && node_5_dash || node_0 && node_5_dash;
	const int n = 10;
	z3::expr hypothesis =  node_1 || node_4 || node_2;
	* */
	
	/* 
	 * 1. Initial Vertices
	 * 2. Safe Vertices
	 * 3. Player 0 und Player 1
	 * 4. Edges
	 * */
	z3::expr initial_vertices = ctx.int_val(4);
	z3::expr safe_vertices = ctx.int_val(4);
	z3::expr vertices_player0 = ctx.int_val(4);
	z3::expr vertices_player1 = ctx.int_val(4);
	z3::expr edges = ctx.int_val(4);
	int n;
	example_1(initial_vertices, safe_vertices, vertices_player0, vertices_player1, edges, n);
	auto vertices = vertices_player0 || vertices_player1;
	auto vertices_dash = vertices.substitute(variables_vector,variables_dash_vector);
	auto hypothesis = ctx.bool_val(true);
	z3::expr hypothesis_edges_test = hypothesis.substitute(variables_vector,variables_dash_vector);
	bool flag = true;
	int safety_counter = 0;
	while (flag)
	{
		flag = false;

		flag = initial_check(hypothesis, initial_vertices, ctx, variables_vector);
		if (flag == false){
			flag = safe_check(hypothesis,safe_vertices,ctx,variables_vector);
		}
		if (flag == false){
			flag = ex_check(hypothesis, hypothesis_edges_test, vertices, vertices_dash,vertices_player0, edges, ctx, all_variables_vector, variables_vector, variables_dash_vector, n);
		}
		if (flag == false){
			flag = uni_check(hypothesis, hypothesis_edges_test, vertices, vertices_dash,vertices_player1, edges, ctx, all_variables_vector, variables_vector, variables_dash_vector, n);
		}
		write();
		system("learner/main data/dillig12.bpl");
		std::ifstream ifs("data/dillig12.bpl.json");
		json j = json::parse(ifs);
		hypothesis = read_json(j);
		std::cout << "\n HYPOTHESIS: " << hypothesis << std::endl;
		hypothesis_edges_test  = hypothesis.substitute(variables_vector,variables_dash_vector);
		safety_counter++;
		if (safety_counter >= 10)
		{
			flag = false;
			std::cout << "Safety counter reached" << std::endl;
		}
	}
}
