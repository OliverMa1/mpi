#include <iostream>
#include <sstream>


#include "z3++.h"



int main()
{

	try
	{

	z3::context ctx;
	
	std::stringstream smt;
	//smt << "(declare-const a Int)" << std::endl;
	smt << "(assert (> a 42))" << std::endl;;
	smt << "(assert (<= a 43))" << std::endl;;
	std::cout << smt.str() << std::endl;
	
	
	// Manually define function declarations
	auto a_decl = ctx.function(ctx.str_symbol("a"), z3::sort_vector(ctx), ctx.int_sort());
	auto func_decl_v = z3::func_decl_vector(ctx);
	func_decl_v.push_back(a_decl);
	
	auto v = ctx.parse_string(smt.str().c_str(), z3::sort_vector(ctx), func_decl_v);
	std::cout << v.size() << std::endl;


	z3::solver s(ctx);
		
	for (unsigned i=0; i<v.size(); ++i)
	{
		std::cout << v[i] << std::endl;
		s.add(v[i]);
	}
	
	
	std::cout << std::endl << s << std::endl;
	
	if (s.check())
	{
		
		auto m = s.get_model();
		std::cout << "SAT!" << std::endl << m << std::endl;
		
	}
	else
	{
		std::cout << "UNSAT" << std::endl;
	}
	
	
	}
	catch (const z3::exception & e)
	{
		std::cout << e.msg() << std::endl;
		//throw;
	}
	
	
}