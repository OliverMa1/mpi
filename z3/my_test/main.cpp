#include <iostream>
#include <fstream>
#include <vector>
#include <set>
#include <map>
#include <iterator>
#include <typeinfo>
#include "z3++.h"
#include "teacher.h"

struct Counterexample
{
	std::vector<int> datapoints;
	// -1 = ?; 0 = false; 1 = true
	int classification;
	Counterexample(std::vector<int> dp, int c): datapoints(dp), classification(c){}
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
		for (int i = 0; i < c.datapoints.size()-1; i++)
		{
			stream << c.datapoints[i] << ", ";
		}
		stream << c.datapoints[c.datapoints.size()-1];
		if (c.classification == -1)
		{
			stream << ", ?";
		}
		else if (c.classification == 0)
		{
			stream << ", 0";
		}
		else
		{
			stream << ", 1";
		}

		return stream;
	} 
};
	std::map<Counterexample,int> counterexample_map;
	std::map<int,Counterexample> position_map;
	std::vector<Counterexample> counterexample_vector;
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

bool write()
{
	std::ofstream myfile;
	myfile.open("dillig12.bpl.data");
	for (int i = 0; i < counterexample_vector.size()-1;i++)
	{
		myfile << counterexample_vector[i] << "\n";
	}
	myfile << counterexample_vector[counterexample_vector.size()-1];
	myfile.close();	
}
bool store(Counterexample  ce)
{
	std::map<Counterexample, int>::iterator it = counterexample_map.find(ce);
	if (it != counterexample_map.end())
	{
		//check ob jetztiges > gefundenes, ersetze dann (true, oder false ersetzen ?)
		int position = it -> second;
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
			std::cout << "ERROR" << std::endl;
		}
		
	}
	else 
	{
		std::cout << "element nicht vorhanden" << std::endl;
		counterexample_map.insert(std::make_pair(ce, counterexample_map.size()));
		position_map.insert(std::make_pair(position_map.size(), ce));
		counterexample_vector.push_back(ce);
		std::cout << "Stored: " << ce << " at Position: " << counterexample_map.size()-1 << std::endl;
	}
}

bool create_and_store_initial_counterexample(const std::vector<int>  ce)
{	
	return store(Counterexample(ce,0));
}

int create_and_store_safe_counterexample(const std::vector<int>  ce)
{
	return store(Counterexample(ce,1));
}
bool create_and_store_unclassified_counterexample(const std::vector<int> ce)
{
	return store(Counterexample(ce,-1));
}
bool create_and_store_existential_counterexample(const std::vector<std::vector<int>>  ce)
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
	// create horn_clausel(positions);
	return success;	
}
bool create_and_store_universal_counterexample(const std::vector<std::vector<int>>  ce)
{
	std::vector<int> a;
	bool success = true;
	int position = create_and_store_unclassified_counterexample(ce[ce.size()-1]);
	for (int i = ce.size()-2; i >= 0; i--)
	{
		std::vector<int> positions;
		positions.push_back(position);
		position = create_and_store_unclassified_counterexample(ce[i]);
		if (position == -1){
			success = false;
		}
		positions.push_back(position);
		// create horn_clausel
	}
	return success;		
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
	z3::expr hypothesis =  node_1 || node_4 || node_2;
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
		bool ce = create_and_store_initial_counterexample(test1);
	}
	test2 = check_safe_condition(hypothesis,safe_vertices,ctx,variables);
	if (test2.size() == 0){
		std::cout << "Safe CE leer" << std::endl;
	}
	else {
		for (int i = 0; i < test2.size(); i++){
			std::cout << "Safe: " << i << ": " << test2[i] << std::endl;
		}
		create_and_store_safe_counterexample(test2); 
		create_and_store_safe_counterexample(test2); 
	}
	std::vector<std::vector<int>> new_test1;
	std::vector<std::vector<int>> new_test2;
	new_test1 = existential_check(hypothesis, hypothesis_edges_test, vertices, vertices_dash,vertices_player0, edges, ctx, all_variables, variables, variables_dash, n);
	
	if (new_test1.size() == 0){
		std::cout << "Existential CE leer" << std::endl;
	}
	else {
		for (int i = 0; i < new_test1.size(); i++){
			for (int j = 0; j < new_test1[i].size(); j++){
				std::cout << "Ex: " << j << ": " << new_test1[i][j] << std::endl;	
			}
		} 
		create_and_store_existential_counterexample(new_test1);
		;
	}
	new_test2 = universal_check(hypothesis, hypothesis_edges_test, vertices, vertices_dash,vertices_player1, edges, ctx, all_variables, variables, variables_dash, n);
	if (new_test2.size() == 0){
		std::cout << "Uni CE leer" << std::endl;
	}
	else {
		for (int i = 0; i < new_test2.size(); i++){
			for (int j = 0; j < new_test2[i].size(); j++){
				std::cout << "Uni: " << j << ": " << new_test2[i][j] << std::endl;	
			}
		}
		create_and_store_universal_counterexample(new_test2);
		
	}
	std::ofstream myfile;
	myfile.open("example.txt");
	myfile << "Writing this to a file. \n";
	myfile.close();
	std::vector<int> c;
	c.push_back(3);
	c.push_back(3);
	Counterexample *a = new Counterexample(c,0);
	std::cout << "Inserting: " << *a << " as Counterexample" << std::endl;
	store(*a);
	write();
	//counterexample_map.insert(std::make_pair(&a,1));
}
