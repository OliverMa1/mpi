

counterexample_struct learn(const z3::expr & hypothesis, z3::expr & hypothesis_edge_nodes, 
const z3::expr & vertices, const z3::expr & vertices_dash, 
const z3::expr & initial_vertices, const z3::expr & safe_vertices,
 const z3::expr & vertices_player0, const z3::expr & vertices_player1, 
const z3::expr & edges, z3::context & context, z3::expr_vector all_variables,
 z3::expr_vector variables, z3::expr_vector variables_dash, const int n);
void test();
