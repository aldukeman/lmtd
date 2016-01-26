#ifndef PC_GRAPH_H
#define PC_GRAPH_H

#include <vector>
#include <set>
#include <map>
#include <ext/hash_map>
#include <list>
#include <ext/hash_set>
#include <cassert>

#include "landmarks_types.h"
#include "landmarks_graph.h"
#include "landmarks_graph_rpg_sasp.h"

using namespace __gnu_cxx;

class PCNode {
public:
	PCNode(int _var, int _val) : 
    	var(_var), val(_val), ancestors_collected(false) {}
    
    bool operator<(const PCNode& other) {
		if(var < other.var)
			return true;
		else if(var == other.var && val < other.val)
			return true;
		return false;
	}
		
	class compare_nodes {
	public:
		bool operator()(PCNode* n2, PCNode* n3) {
			return (*n2) < (*n3);
		}
	};
		
    int var;
    int val;
	map<PCNode*, edge_type, compare_nodes> parents;
    map<PCNode*, edge_type, compare_nodes> children;
    
    
    hash_set<PCNode*, hash_pointer> ancestors;    
    bool ancestors_collected;    
    set<PCNode*> ancs_in_cond;
    //dynamic member.
    //for pcn_p, pcn_q is in ancs_in_cond(pcn_p) iff. 
    //pcn_q <PC* pcn_p holds and pcn_q is in the same precondition
    //as pcn_p in. This is the info for determining context(pcn_p): best_anc;
     
    PCNode* best_anc; 
    //dynamic member: in a give precond, 
    //this node's nearest ancestor that with the lowest var "index"
};

class PCGraph {
public:
	PCGraph();
	~PCGraph() { }
	void build_pcgraph(bool use_reasonable);
	void build_nodes();
	PCNode& add_node(const pair<int, int>& fact);
	bool node_exists(const pair<int, int>& fact) const; // do we need this function?
    void dump_node(const PCNode* node_pc) const;
    void dump() const;
    inline int number_of_nodes() const {
        return nodes_count;
    }
    inline PCNode& get_pc_node(const pair<int, int>& a) const {
        assert(node_exists(a));
        return *(facts_to_nodes.find(a)->second);
    }
    inline const set<PCNode*, PCNode::compare_nodes>& get_nodes() const {
    	return nodes;
    }
    
    void edge_add(PCNode& from, PCNode& to, edge_type type);
    int number_of_edges() const;    
 
    
	void generate(); 
    void compute_LAdown_order();
    void compute_LAup_order();
    void compute_LR_order();
    void compute_Ldown_order();
    void compute_Lup_order();
    void compute_Adown_order();
    void compute_Aup_order();
    void compute_Rand_order();    
    
    void mk_acyclic();
    int loop_acyclic_graph(PCNode& pcn,
                           hash_set<PCNode*, hash_pointer>& acyclic_node_set);
    bool remove_reasonable_cycle_edge(PCNode* cur,
                                      list<pair<PCNode*, edge_type> >& path,
                                      list<pair<PCNode*, edge_type> >::iterator it);
    bool interferes(const PCNode* node_a, const PCNode* node_b) const;
     
                          
    void collect_pc_ancestors(hash_set<PCNode*, hash_pointer>& result, PCNode& node);
    void set_best_anc(vector<PCNode*>& nodes_in_precond);
	//set the best ancestor of a fact in a given precond
	
	
private:
	set<PCNode*, PCNode::compare_nodes> nodes;
	int nodes_count;
    hash_map<pair<int, int>, PCNode*, hash_int_pair> facts_to_nodes;
    LandmarksGraph *lgraph; // The landmarks-graph built by Silvia's procedure
};

#endif
