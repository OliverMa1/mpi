#include <iostream>
#include <vector>
#include <tuple>
#include <string>
#include <typeinfo>
#include "z3++.h"
#include "game.h"
#include <nlohmann/json.hpp>
using json = nlohmann::json;
	
class ParserObject {
	/* was brauchen wir?
	 * 1. expr_vector für alle eingaben, init, safe,player0, player1 edges, successors
	 * 2. variables, variables_dash, all_variables, exprs, exprs_var
	 * vermutlich auch context, return game object????
	 * */
	public :ParserObject(json& js)//, z3::expr_vector & variables, z3::expr_vector & exprs, int successors)
	{
		
		game = parse_json(js);
		game->print(1);
	}
	Game* parse_json(json j)
	{
		std::cout << j << std::endl;
		std::vector<std::string> variables_vector;
		std::vector<std::string> variables_dash_vector;
		std::vector<std::string> exprs_var;	
		auto smt2lib = j["smt2"].get<std::string>();
		std::cout << "test inside json parser " << smt2lib << std::endl;
		int i = j["successors"];	
		std::cout << "Parsing json..." << std::endl;
		for (int i = 0; (unsigned)i < j["variables"].size(); i ++)
		{
			std::cout << j["variables"][i].get<std::string>() << std::endl;
			variables_vector.push_back(j["variables"][i].get<std::string>());
		}
				for (int i = 0; i < variables_vector.size(); i++)
		
		{
			std::cout<< "TEST " << variables_vector[i] << std::endl;
		}
		for (int i = 0; (unsigned)i < j["variables_dash"].size(); i ++)
		{
			std::cout << j["variables_dash"][i].get<std::string>() << std::endl;
			variables_dash_vector.push_back(j["variables_dash"][i].get<std::string>());
		}
		for (int i = 0; (unsigned)i < j["exprs"].size(); i ++)
		{
			std::cout << "added to expr_var: " << j["exprs"][i].get<std::string>() << std::endl;
			exprs_var.push_back(j["exprs"][i].get<std::string>());
		}
		for (int i = 0; i < variables_vector.size(); i++)
		
		{
			std::cout<< "TEST " << variables_vector[i] << std::endl;
		}
		return new Game(variables_vector, variables_dash_vector, exprs_var, smt2lib, i);
	}
	
	private :
		Game* game;
	
};
