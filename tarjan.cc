#include <vector>
#include <stack>
#include <algorithm>
#include <optional>
#include <cassert>
#include <cmath>
#include <utility>
#include <iostream>

using namespace std;

class TarjanSCC {
private:
    int n; // Number of vertices
    vector<vector<int>> adj; // Adjacency list
    vector<int> disc; // Discovery times
    vector<int> low;  // Lowest reachable ancestor time
    vector<bool> onStack; // To check if a node is on the recursion stack
    stack<int> st;    // Stack for nodes in the current SCC candidate
    int timer;            // Time counter for discovery times
    
    vector<int> component;    // component[i] = ID of the SCC containing node i
    int scc_count;            // Total number of SCCs found
    
    void tarjan_dfs(int u) {
        disc[u] = low[u] = timer++;
        st.push(u);
        onStack[u] = true;

        for (int v : adj[u]) {
            if (disc[v] == -1) {
                tarjan_dfs(v);
                low[u] = min(low[u], low[v]);
            } else if (onStack[v]) {
                low[u] = min(low[u], disc[v]);
            }
        }

        if (low[u] == disc[u]) {
            while (true) {
                int w = st.top();
                st.pop();
                onStack[w] = false;
                component[w] = scc_count;
                if (u == w) break;
            }
            scc_count++;
        }
    }

public:
    TarjanSCC(int num_vertices) : n(num_vertices) {
        adj.resize(n);
    }

    // Add a directed edge from u to v
    void add_edge(int u, int v) {
        if (u >= 0 && u < n && v >= 0 && v < n) {
             adj[u].push_back(v);
        }
    }

    /**
     * @brief Finds the strongly connected components (SCCs) in the graph.
     * 
     * A strongly connected component (SCC) in a directed graph is a subgraph where
     * for every pair of vertices u and v in the subgraph, there is a path from u to v
     * and a path from v to u. In other words, every vertex in the SCC is reachable
     * from every other vertex within the SCC.
     * 
     * @return A pair containing:
     *         - A vector<int> where component[i] is the ID of the SCC containing node i.
     *         - An integer representing the total number of SCCs found.
     * 
     * @note Time Complexity: O(V + E), where V is the number of vertices and E is the number of edges.
     * @note Space Complexity: O(V), where V is the number of vertices.
     */
    pair<vector<int>,int> find_sccs() {
        disc.assign(n, -1);
        low.assign(n, -1);
        onStack.assign(n, false);
        component.assign(n, -1);
        while (!st.empty()) st.pop();
        timer = 0;
        scc_count = 0;

        for (int i = 0; i < n; ++i) {
            if (disc[i] == -1) {
                tarjan_dfs(i);
            }
        }
        return {component, scc_count};
    }
};

/**
 * @brief Solves the 2-satisfiability (2-SAT) problem using Tarjan's algorithm for strongly connected components (SCCs).
 * 
 * Given a set of Boolean variables and a set of clauses, where each clause is a disjunction (OR) of exactly two literals,
 * this function determines whether there exists a truth assignment to the variables that satisfies all the clauses.
 * 
 * @note From a clause (a V b) we add edges (¬a => b) and (¬b => a).
 * 
 * @param num_vars The number of Boolean variables. Variables are implicitly numbered from 1 to num_vars.
 * @param clauses A vector of pairs, where each pair represents a clause. Each integer in a pair represents a literal:
 *                - A positive integer 'x' represents the variable x being true (x).
 *                - A negative integer '-x' represents the variable x being false (¬x).
 * @return An optional<vector<bool>>. If the formula is satisfiable, it returns a vector of booleans where:
 *         - assignment[i] == true means variable (i+1) is assigned true.
 *         - assignment[i] == false means variable (i+1) is assigned false.
 *         If the formula is unsatisfiable, it returns std::nullopt.
 */
optional<vector<bool>> solve_2sat(int num_vars, const vector<pair<int, int>>& clauses) {
    // The implication graph will have 2*num_vars nodes.
    // Node 2*i represents variable x_{i+1} being true.
    // Node 2*i + 1 represents variable x_{i+1} being false (¬x_{i+1}).
    int n_nodes = 2 * num_vars;
    TarjanSCC scc_solver(n_nodes);

    // Helper function to map a literal (1-based, signed) to its graph node index (0-based)
    auto map_literal_to_node = [&](int literal) -> int {
        int var_index = abs(literal) - 1;
        if (literal > 0) {
            return 2 * var_index;
        } else {
            return 2 * var_index + 1;
        }
    };

    // Helper function to get the node index of the negation of a given node index
    auto neg_node = [](int node_index) -> int {
        return node_index ^ 1;
    };

    for (const auto& clause : clauses) {
        int lit1 = clause.first;
        int lit2 = clause.second;

        int node_a = map_literal_to_node(lit1);
        int node_b = map_literal_to_node(lit2);

        int node_not_a = neg_node(node_a);
        int node_not_b = neg_node(node_b);

        scc_solver.add_edge(node_not_a, node_b);
        scc_solver.add_edge(node_not_b, node_a);
    }

    auto [component, scc_count] = scc_solver.find_sccs();

    for (int i = 0; i < num_vars; ++i) {
        int node_true = 2 * i;
        int node_false = 2 * i + 1;
        if (component[node_true] == component[node_false]) {
            return nullopt; // Indicate unsatisfiable
        }
    }

    vector<bool> assignment(num_vars);
    for (int i = 0; i < num_vars; ++i) {
        int node_true = 2 * i;
        int node_false = 2 * i + 1;

        assignment[i] = (component[node_true] < component[node_false]);
    }

    return assignment;
}

void test_find_sccs() {
    cout << "--- Testing find_sccs ---" << endl;

    // Test Case 1: Simple Cycle (3 nodes)
    cout << "Test Case 1: Simple Cycle (3 nodes)" << endl;
    {
        TarjanSCC scc_solver(3);
        scc_solver.add_edge(0, 1);
        scc_solver.add_edge(1, 2);
        scc_solver.add_edge(2, 0);
        auto [component, scc_count] = scc_solver.find_sccs();
        assert(scc_count == 1);
        assert(component.size() == 3);
        assert(component[0] != -1);
        assert(component[0] == component[1]);
        assert(component[1] == component[2]);
        cout << "  Passed." << endl;
    }

    // Test Case 2: Two Disjoint Cycles (4 nodes)
    cout << "Test Case 2: Two Disjoint Cycles (4 nodes)" << endl;
    {
        TarjanSCC scc_solver(4);
        scc_solver.add_edge(0, 1);
        scc_solver.add_edge(1, 0);
        scc_solver.add_edge(2, 3);
        scc_solver.add_edge(3, 2);
        auto [component, scc_count] = scc_solver.find_sccs();
        assert(scc_count == 2);
        assert(component.size() == 4);
        assert(component[0] != -1 && component[2] != -1);
        assert(component[0] == component[1]);
        assert(component[2] == component[3]);
        assert(component[0] != component[2]);
        cout << "  Passed." << endl;
    }

    // Test Case 3: Line Graph / DAG (3 nodes)
    cout << "Test Case 3: Line Graph / DAG (3 nodes)" << endl;
    {
        TarjanSCC scc_solver(3);
        scc_solver.add_edge(0, 1);
        scc_solver.add_edge(1, 2);
        auto [component, scc_count] = scc_solver.find_sccs();
        assert(scc_count == 3);
         assert(component.size() == 3);
        assert(component[0] != -1);
        assert(component[0] != component[1]);
        assert(component[1] != component[2]);
        assert(component[0] != component[2]);
        cout << "  Passed." << endl;
    }

    // Test Case 4: More Complex Graph (Wikipedia Example slightly adapted)
    cout << "Test Case 4: Complex Graph (8 nodes, 3 SCCs)" << endl;
    {
        TarjanSCC scc_solver(8);
        scc_solver.add_edge(0, 1);
        scc_solver.add_edge(1, 2);
        scc_solver.add_edge(2, 0);
        scc_solver.add_edge(1, 3);
        scc_solver.add_edge(3, 4);
        scc_solver.add_edge(4, 5);
        scc_solver.add_edge(5, 3);
        scc_solver.add_edge(2, 6);
        scc_solver.add_edge(4, 6);
        scc_solver.add_edge(6, 7);
        scc_solver.add_edge(7, 6);
        scc_solver.add_edge(5,4);

        auto [component, scc_count] = scc_solver.find_sccs();
        assert(scc_count == 3);
        assert(component.size() == 8);

        assert(component[0] != -1);
        assert(component[0] == component[1] && component[1] == component[2]);
        assert(component[3] == component[4] && component[4] == component[5]);
        assert(component[6] == component[7]);

        assert(component[0] != component[3]);
        assert(component[0] != component[6]);
        assert(component[3] != component[6]);
        cout << "  Passed." << endl;
    }

     // Test Case 5: Single Node
    cout << "Test Case 5: Single Node" << endl;
    {
        TarjanSCC scc_solver(1);
        auto [component, scc_count] = scc_solver.find_sccs();
        assert(scc_count == 1);
        assert(component.size() == 1);
        assert(component[0] != -1);
        cout << "  Passed." << endl;
    }

     // Test Case 6: No Edges (4 nodes)
    cout << "Test Case 6: No Edges (4 nodes)" << endl;
    {
        TarjanSCC scc_solver(4);
        auto [component, scc_count] = scc_solver.find_sccs();
        assert(scc_count == 4);
         assert(component.size() == 4);
        assert(component[0] != -1);
        assert(component[0] != component[1]);
        assert(component[0] != component[2]);
        assert(component[0] != component[3]);
        assert(component[1] != component[2]);
        assert(component[1] != component[3]);
        assert(component[2] != component[3]);
        cout << "  Passed." << endl;
    }

    cout << "--- find_sccs tests finished ---" << endl << endl;
}

void test_solve_2sat() {
    cout << "--- Testing solve_2sat ---" << endl;

    // Test Case 1: Simple Satisfiable (x1 V x2)
    cout << "Test Case 1: Simple Satisfiable (x1 V x2)" << endl;
    {
        int num_vars = 2;
        vector<pair<int, int>> clauses = {{1, 2}};
        optional<vector<bool>> result = solve_2sat(num_vars, clauses);
        assert(result.has_value());
        assert(result.value().size() == num_vars);
        assert(result.value()[0] || result.value()[1]);
        cout << "  Passed." << endl;
    }

    // Test Case 2: Simple Unsatisfiable (x1 AND !x1)
    cout << "Test Case 2: Simple Unsatisfiable (x1 AND !x1)" << endl;
    {
        int num_vars = 1;
        vector<pair<int, int>> clauses = {{1, 1}, {-1, -1}};
        optional<vector<bool>> result = solve_2sat(num_vars, clauses);
        assert(!result.has_value());
        cout << "  Passed." << endl;
    }

    // Test Case 3: More Complex Satisfiable (x1 <=> x2, x2 <=> x3)
    cout << "Test Case 3: Complex Satisfiable (x1<=>x2, x2<=>x3)" << endl;
    {
        int num_vars = 3;
        vector<pair<int, int>> clauses = {{1, -2}, {-1, 2}, {2, -3}, {-2, 3}};
        optional<vector<bool>> result = solve_2sat(num_vars, clauses);
        assert(result.has_value());
        assert(result.value().size() == num_vars);
        bool x1 = result.value()[0];
        bool x2 = result.value()[1];
        bool x3 = result.value()[2];
        assert(x1 == x2 && x2 == x3);
        cout << "  Passed." << endl;
    }

    // Test Case 4: Known Unsatisfiable example
    cout << "Test Case 4: Complex Unsatisfiable" << endl;
    {
        int num_vars = 2;
        vector<pair<int, int>> clauses = {{1, 2}, {1, -2}, {-1, 2}, {-1, -2}};
        optional<vector<bool>> result = solve_2sat(num_vars, clauses);
        assert(!result.has_value());
        cout << "  Passed." << endl;
    }

    // Test Case 5: No Clauses (Trivially Satisfiable)
    cout << "Test Case 5: No Clauses" << endl;
    {
        int num_vars = 3;
        vector<pair<int, int>> clauses = {};
        optional<vector<bool>> result = solve_2sat(num_vars, clauses);
        assert(result.has_value());
        assert(result.value().size() == num_vars);
        cout << "  Passed." << endl;
    }

     // Test Case 6: One Variable, Tautology (x1 V !x1)
    cout << "Test Case 6: One Variable, Tautology (x1 V !x1)" << endl;
    {
        int num_vars = 1;
        vector<pair<int, int>> clauses = {{1, -1}};
        optional<vector<bool>> result = solve_2sat(num_vars, clauses);
        assert(result.has_value());
        assert(result.value().size() == num_vars);
        cout << "  Passed." << endl;
    }

    // Test Case 7: Chain of implications (Satisfiable)
    cout << "Test Case 7: Chain Implication (Satisfiable)" << endl;
    {
        int num_vars = 4;
        vector<pair<int, int>> clauses = {{1, 2}, {2, 3}, {3, 4}};
        optional<vector<bool>> result = solve_2sat(num_vars, clauses);
        assert(result.has_value());
        assert(result.value().size() == num_vars);
        assert(result.value()[0] || result.value()[1]);
        assert(result.value()[1] || result.value()[2]);
        assert(result.value()[2] || result.value()[3]);
        cout << "  Passed." << endl;
    }

    cout << "--- solve_2sat tests finished ---" << endl << endl;
}

void example_find_sccs() {
    cout << "--- Example usage of find_sccs ---" << endl;
    TarjanSCC scc_solver(5);
    scc_solver.add_edge(0, 1);
    scc_solver.add_edge(1, 2);
    scc_solver.add_edge(2, 0);
    scc_solver.add_edge(1, 3);
    scc_solver.add_edge(3, 4);

    auto [component, scc_count] = scc_solver.find_sccs();
    cout << "Number of SCCs: " << scc_count << endl;
    for (int i = 0; i < component.size(); ++i) {
        cout << "Node " << i << " is in SCC " << component[i] << endl;
    }
    cout << "--- End of example ---" << endl << endl;
}

void example_solve_2sat() {
    cout << "--- Example usage of solve_2sat ---" << endl;
    int num_vars = 3;
    vector<pair<int, int>> clauses = {{1, 2}, {-1, 3}, {-2, -3}};

    optional<vector<bool>> result = solve_2sat(num_vars, clauses);
    if (result.has_value()) {
        cout << "Formula is satisfiable. Assignment:" << endl;
        for (int i = 0; i < num_vars; ++i) {
            cout << "Variable " << (i + 1) << ": " << (result.value()[i] ? "true" : "false") << endl;
        }
    } else {
        cout << "Formula is unsatisfiable." << endl;
    }
    cout << "--- End of example ---" << endl << endl;
}

int main() {
    test_find_sccs();
    test_solve_2sat();
    example_find_sccs();
    example_solve_2sat();
    return 0;
}
