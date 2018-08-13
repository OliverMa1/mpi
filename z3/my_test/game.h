#ifndef HEADERFILE_H
#define HEADERFILE_H
#include <iostream>
#include <vector>
#include <tuple>
#include <typeinfo>
#include "z3++.h"

class Game {
	// reicht struct ??? vermutlich ja
	/* 1. bekommt init, safe, player0, player1, edges, successors speichere sämtliche attribute hier
	 * 2. bekommt alle art von variablen
	 * 3. Erstelle game mithilfe von parserObject
	 * 4. nutze parameter vom game object für teacher learner interaktion
	 * 5. zusätzliche exprs bei main???, speichere diese aber hier i guess
	 * 
	 * */
	 public:
	 Game(std::vector<std::string> var_char, std::vector<std::string> var_dash_char, std::vector<std::string> exprs_var_char, std::string smt2lib, int n): ctx(), successors(n)
	 {
		std::cout << "Printing Game... Konstruktor" << smt2lib << " wutface " << std::endl;
		print(0);
		auto func_decl_v = z3::func_decl_vector(ctx);
		for (int i = 0; (unsigned)i < var_char.size(); i ++)
		{
			std::cout << "var: " << i << var_char[i] << std::endl;
			z3::expr x = ctx.int_const(var_char[i].c_str());
			variables_vector.push_back(x);
			all_variables_vector.push_back(x);
			variables.insert(std::make_pair(var_char[i],x));
			auto a_decl = ctx.function(ctx.str_symbol(var_char[i].c_str()), z3::sort_vector(ctx), ctx.int_sort());
			func_decl_v.push_back(a_decl);
		}
		for (int i = 0; (unsigned)i < var_dash_char.size(); i ++)
		{
			std::cout << "var_dash: " << i << var_dash_char[i] << std::endl;
			z3::expr x = ctx.int_const(var_dash_char[i].c_str());
			variables_dash_vector.push_back(x);
			all_variables_vector.push_back(x);
			auto a_decl = ctx.function(ctx.str_symbol(var_dash_char[i].c_str()), z3::sort_vector(ctx), ctx.int_sort());
			func_decl_v.push_back(a_decl);
		}
		for (int i = 0; (unsigned)i < exprs_var_char.size(); i ++)
		{
			std::cout << "added to expr_var: " << exprs_var_char[i] << std::endl;
			z3::expr x = ctx.int_const(exprs_var_char[i].c_str());
			exprs_var.push_back(x);
			//expr_var_map.insert(std::make_pair(j["exprs"][i].get<std::string>(),x));
		}
		base = ctx.parse_string(smt2lib.c_str(), z3::sort_vector(ctx), func_decl_v);		
		for (int i = 5; (unsigned) i < base.size(); i++)
		{
			exprs.push_back(base[i]);
			std::cout << "base test: " << i << " " << base[i] << std::endl;
		}
	 }
	 void print(int i)
	 {
		 z3::solver s(ctx);
		 std::cout << "Printing Game..."  << std::endl;
	 }
	 z3::expr get_initial_vertices()
	 {
		 return base[0];
	 }
	 z3::expr get_safe_vertices()
	 {
		 return base[1];
	 }
	 z3::expr get_player0_vertices()
	 {
		 return base[2];
	 }
	 z3::expr get_player1_vertices()
	 {
		 return base[3];
	 }	 
	 z3::expr get_edges()
	 {
		 return base[4];
	 }	 
	 z3::expr_vector get_variables_vector()
	 {
		 return variables_vector;
	 }	 
	 z3::expr_vector get_variables_dash_vector()
	 {
		 return variables_dash_vector;
	 }	 
	 z3::expr_vector get_all_variables_vector()
	 {
		 return all_variables_vector;
	 }
	 z3::expr_vector get_exprs_var()
	 {
		 return exprs_var;
	 }
	 z3::expr_vector get_exprs()
	 {
		 return exprs;
	 }
	 std::map<std::string, z3::expr> get_variables()
	 {
		 return variables;
	 }
	 private:
		z3::context ctx;
		z3::expr_vector base = *(new z3::expr_vector(ctx));
		z3::expr_vector variables_vector = *(new z3::expr_vector(ctx));
		z3::expr_vector variables_dash_vector = *(new z3::expr_vector(ctx));
		z3::expr_vector all_variables_vector = *(new z3::expr_vector(ctx));
		z3::expr_vector exprs_var = *(new z3::expr_vector(ctx));
		z3::expr_vector exprs = *(new z3::expr_vector(ctx));
		std::map<std::string, z3::expr> variables;
		int successors;
};

#endif
