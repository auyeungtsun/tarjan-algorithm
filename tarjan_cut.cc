#include <vector>
#include <utility>
#include <algorithm>
#include <set>
#include <iostream>
#include <cassert>

using namespace std;

class TarjanCut {
private:
    int n; // Number of vertices
    vector<vector<int>> adj; // Adjacency list
    vector<int> disc; // Discovery times
    vector<int> low;  // Lowest reachable ancestor time
    vector<int> parent; // The parent node of each vertex in the DFS tree
    vector<bool> visited; // Bool array to track if a vertex has been visited
    int timer;            // Time counter for discovery times
    vector<pair<int, int>> bridges; // Stores {u, v} where u < v
    set<int> articulation_points_set; // Use set to handle duplicates automatically

    /**
     * @brief Performs DFS to find cut edges and cut vertices.
     * @param u The current vertex being visited.
     */
    void dfs(int u) {
        visited[u] = true;
        disc[u] = low[u] = timer++;
        int children = 0; // Count children in DFS tree for articulation point check

        for (int v : adj[u]) {
            if (v == parent[u]) {
                continue;
            }

            if (visited[v]) {
                low[u] = min(low[u], disc[v]);
            } else {
                children++;
                parent[v] = u;
                dfs(v);

                low[u] = min(low[u], low[v]);

                // --- Check for Cut Edge (Bridge) ---
                // If the lowest time reachable from v is strictly greater than
                // the discovery time of u, then edge (u, v) is a bridge.
                if (low[v] > disc[u]) {
                    bridges.push_back({min(u, v), max(u, v)});
                }

                // --- Check for Cut Vertex (Articulation Point) ---
                // Condition 1: u is not root, and v's subtree has no back edge
                //              to an ancestor of u (i.e., low[v] >= disc[u]).
                if (parent[u] != -1 && low[v] >= disc[u]) {
                    articulation_points_set.insert(u);
                }
            }
        }

        // --- Check for Cut Vertex (Articulation Point) ---
        // Condition 2: u is the root (parent is -1) and has more than one child in DFS tree.
        if (parent[u] == -1 && children > 1) {
            articulation_points_set.insert(u);
        }
    }

public:
    TarjanCut(int num_vertices) : n(num_vertices) {
        adj.resize(n);
    }

    /**
     * @brief Adds an undirected edge between vertices u and v.
     * @param u The first vertex.
     * @param v The second vertex.
     */
    void add_edge(int u, int v) {
        if (u >= 0 && u < n && v >= 0 && v < n) {
            adj[u].push_back(v);
            adj[v].push_back(u);
        }
    }

    /**
     * @brief Finds all cut edges (bridges) and cut vertices (articulation points)
     *        in an undirected connected graph.
     * @brief In an undirected graph, a cut edge, also known as a bridge, is an edge
     *        whose removal increases the number of connected components in the graph.
     *        A cut vertex, also known as an articulation point, is a vertex whose removal
     *        increases the number of connected components in the graph.
     * @return A pair containing:
     *         first: A vector of pairs {u, v} representing the cut edges (bridges).
     *         second: A vector of integers representing the cut vertices (articulation points).
     * @note Time Complexity: O(V + E), where V is the number of vertices and E is the number of edges.
     *       This is because the algorithm performs a depth-first search (DFS) that visits each vertex and edge once.
     * @note Space Complexity: O(V), where V is the number of vertices. This space is used for storing the adjacency list,
     *       discovery times, lowest reachable ancestor times, parent array, visited array, and the set/vector of articulation points.
     */
    pair<vector<pair<int, int>>, vector<int>> find_cut_edges_and_cut_vertices() {
        disc.assign(n, -1);
        low.assign(n, -1);
        parent.assign(n, -1);
        visited.assign(n, false);
        bridges.clear();
        articulation_points_set.clear();
        timer = 0;

        for (int i = 0; i < n; ++i) {
            if (!visited[i]) {
                dfs(i);
            }
        }

        vector<int> articulation_points_vec(articulation_points_set.begin(), articulation_points_set.end());

        return {bridges, articulation_points_vec};
    }
};

void test_tarjan_cut() {
    // Test case 1: Graph with one bridge and one articulation point
    TarjanCut tarjan_cut1(7);
    tarjan_cut1.add_edge(0, 1);
    tarjan_cut1.add_edge(0, 2);
    tarjan_cut1.add_edge(1, 2);
    tarjan_cut1.add_edge(1, 3);
    tarjan_cut1.add_edge(1, 4);
    tarjan_cut1.add_edge(1, 6);
    tarjan_cut1.add_edge(3, 5);
    tarjan_cut1.add_edge(4, 5);
    auto results1 = tarjan_cut1.find_cut_edges_and_cut_vertices();
    assert(results1.first.size() == 1);
    assert(find(results1.first.begin(), results1.first.end(), make_pair(1, 6)) != results1.first.end());
    assert(results1.second.size() == 1);
    assert(find(results1.second.begin(), results1.second.end(), 1) != results1.second.end());

    // Test case 2: Graph with no bridges and no articulation points (cycle)
    TarjanCut tarjan_cut2(4);
    tarjan_cut2.add_edge(0, 1);
    tarjan_cut2.add_edge(1, 2);
    tarjan_cut2.add_edge(2, 3);
    tarjan_cut2.add_edge(3, 0);
    auto results2 = tarjan_cut2.find_cut_edges_and_cut_vertices();
    assert(results2.first.empty());
    assert(results2.second.empty());

    // Test case 3: Graph with multiple bridges and articulation points
    TarjanCut tarjan_cut3(5);
    tarjan_cut3.add_edge(0, 1);
    tarjan_cut3.add_edge(1, 2);
    tarjan_cut3.add_edge(2, 3);
    tarjan_cut3.add_edge(3, 4);
    auto results3 = tarjan_cut3.find_cut_edges_and_cut_vertices();
    assert(results3.first.size() == 4);
    assert(find(results3.first.begin(), results3.first.end(), make_pair(0, 1)) != results3.first.end());
    assert(find(results3.first.begin(), results3.first.end(), make_pair(1, 2)) != results3.first.end());
    assert(find(results3.first.begin(), results3.first.end(), make_pair(2, 3)) != results3.first.end());
    assert(find(results3.first.begin(), results3.first.end(), make_pair(3, 4)) != results3.first.end());
    assert(results3.second.size() == 3);
    assert(find(results3.second.begin(), results3.second.end(), 1) != results3.second.end() && find(results3.second.begin(), results3.second.end(), 2) != results3.second.end() && find(results3.second.begin(), results3.second.end(), 3) != results3.second.end());

    //Test Case 4: empty graph
    TarjanCut tarjan_cut4(0);
    auto results4 = tarjan_cut4.find_cut_edges_and_cut_vertices();
    assert(results4.first.empty());
    assert(results4.second.empty());
}

void run_tarjan_cut_sample() {
    int n = 7;
    TarjanCut tarjan_cut(n);
    tarjan_cut.add_edge(0, 1);
    tarjan_cut.add_edge(0, 2);
    tarjan_cut.add_edge(1, 2);
    tarjan_cut.add_edge(1, 3);
    tarjan_cut.add_edge(1, 4);
    tarjan_cut.add_edge(1, 6);
    tarjan_cut.add_edge(3, 5);
    tarjan_cut.add_edge(4, 5);

    auto results = tarjan_cut.find_cut_edges_and_cut_vertices();
    auto bridges = results.first;
    auto articulation_points = results.second;

    cout << "Cut Edges (Bridges):\n";
    if (bridges.empty()) {
        cout << "  None\n";
    } else {
        for (const auto& edge : bridges) {
            cout << "  (" << edge.first << ", " << edge.second << ")\n";
        }
    }

    cout << "Cut Vertices (Articulation Points):\n";
     if (articulation_points.empty()) {
        cout << "  None\n";
    } else {
        cout << "  ";
        for (int i = 0; i < articulation_points.size(); ++i) {
            cout << articulation_points[i] << (i == articulation_points.size() - 1 ? "" : ", ");
        }
        cout << "\n";
    }
}

int main() {
    test_tarjan_cut();
    run_tarjan_cut_sample();
    return 0;
}