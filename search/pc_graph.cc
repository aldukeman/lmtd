#include <algorithm>
#include "landmarks_graph.h"
#include "landmarks_graph_rpg_sasp.h"
#include "pc_graph.h"

// Construtor
PCGraph::PCGraph() : nodes_count(0){
}

void PCGraph::build_pcgraph(bool use_reasonable) {
        /*
	bool order_all_facts = true;
	if (g_pcv == Ldown || g_pcv == Lup)
		order_all_facts = false;
	// (1) build the landmarksgraph
	lgraph = new LandmarksGraphNew(order_all_facts);*/
        lgraph = new LandmarksGraphNew();//by huym
	lgraph->read_external_inconsistencies();
	// compute reasonable order for versions that "order only landmarks"
	if(use_reasonable) 
		(lgraph->use_reasonable_orders)();
	lgraph->generate();
        /*
	cout << "Generated " << lgraph->number_of_landmarks() << " facts, of which "
    << lgraph->number_of_disj_landmarks() << " are disjunctive" << endl
    << "          " << lgraph->number_of_edges() << " edges\n";
    //lgraph->dump();
    */
    //--------------------------------------------------------------
	
	// (2) build the PC graph
	build_nodes(); // build nodes of the PC graph
	generate();	// build edges of the PC graph wrt. a specified PCversion
	mk_acyclic(); // remove cycles;
	//dump(); // dump the pc_graph

}

void PCGraph::build_nodes() {
	int num_variables = g_variable_domain.size();
	for(int var_no = 0; var_no < num_variables; var_no++) {
		int num_values = g_variable_domain[var_no];        
		for(int value = 0; value < num_values; value++) {          	
        	add_node(make_pair(var_no, value));
		}
	}
}

PCNode& PCGraph::add_node(const pair<int, int>& fact) {
	assert(!node_exists(fact));
    PCNode* new_node_p = new PCNode(fact.first, fact.second);
    nodes.insert(new_node_p);
    facts_to_nodes.insert(make_pair(fact, new_node_p));
    nodes_count++;
    return *new_node_p;
}

bool PCGraph::node_exists(const pair<int, int>& fact) const {
	return (facts_to_nodes.count(fact));
}

void PCGraph::dump_node(const PCNode* node_pc) const {
	pair<int, int> node_prop = make_pair(node_pc->var, node_pc->val);
	hash_map<pair<int, int>, LandmarksGraph::Pddl_proposition, hash_int_pair>::const_iterator 
							it = lgraph->pddl_propositions.find(node_prop);
	
	if(it != lgraph->pddl_propositions.end()) {
    	cout << it->second.to_string() << " ("
		<< g_variable_name[node_prop.first] << "(" << node_prop.first << ")"
        << "->" << node_prop.second << ")";
	} else {
		cout << g_variable_name[node_prop.first]
		<< "(" << node_prop.first << ") "
		<< "->" << node_prop.second;
	}
	cout << endl;
}

void PCGraph::dump() const {
	set<PCNode*, PCNode::compare_nodes>::const_iterator it = nodes.begin();
	for(; it != nodes.end(); it++) {
        PCNode* node_p = *it;
        dump_node(node_p);
        
		map<PCNode*, edge_type, PCNode::compare_nodes>::const_iterator parent_it;
        for(parent_it = node_p->parents.begin();
                parent_it != node_p->parents.end();
                parent_it++) {
            const edge_type& edge = parent_it->second;
            const PCNode* parent_p = parent_it->first;
            cout << "\t\t<-_";
            switch(edge) {
            case n:
                cout << "n   ";
                break;
            case r:
                cout << "r   ";
                break;
            case gn:
                cout << "gn  ";
                break;
            case ln:
                cout << "ln  ";
                break;
            case o_r:
                cout << "o_r ";
                break;
            }
            dump_node(parent_p);
        }
		
		map<PCNode*, edge_type, PCNode::compare_nodes>::const_iterator child_it;
        for(child_it = node_p->children.begin();
                child_it != node_p->children.end();
                child_it++) {
            const edge_type& edge = child_it->second;
            const PCNode* child_p = child_it->first;
            cout << "\t\t->_";
            switch(edge) {
            case n:
                cout << "n   ";
                break;
            case r:
                cout << "r   ";
                break;
            case gn:
                cout << "gn  ";
                break;
            case ln:
                cout << "ln  ";
                break;
            case o_r:
                cout << "o_r ";
                break;
            }
            dump_node(child_p);
        }
    }
}

// adding edge. 
// There may be that the arc "q BEFORE_r p" was inserted before "q BEFORE_n p".
// Also there may be that an arc already exists.
void PCGraph::edge_add(PCNode& from, PCNode& to, edge_type type) {
    assert(&from != &to);
    // If edge already exists, remove if weaker
    if(from.children.find(&to) != from.children.end() &&
            from.children.find(&to)->second < type) {
        // cout << "weaker edges exist with type " << from.children.find(&to)->second << endl << endl;
        from.children.erase(&to);
        assert(to.parents.find(&from) != to.parents.end());
        to.parents.erase(&from);
        assert(to.parents.find(&from) == to.parents.end());
        assert(from.children.find(&to) == from.children.end());
    }
    
    // If edge does not exist (or has just been removed), insert
    if(from.children.find(&to) == from.children.end()) {
        assert(to.parents.find(&from) == to.parents.end());
        from.children.insert(make_pair(&to, type));
        to.parents.insert(make_pair(&from, type));
    }
    
    assert(from.children.find(&to) != from.children.end());
    assert(to.parents.find(&from) != to.parents.end());
}

int PCGraph::number_of_edges() const {
	int total = 0;
	set<PCNode*, PCNode::compare_nodes>::const_iterator it = nodes.begin();
    for(; it != nodes.end(); it++) {
        total += (*it)->children.size();
    }
    return total;
}

void PCGraph::generate() {
	//cout << "Generating the Precedence Constraints (PC) Graph." << endl;
	
	if(g_before_order_option == 1) {
		compute_LAdown_order();	
	} else if(g_before_order_option == 2) {
		compute_LAup_order();
	} else if(g_before_order_option == 3) {
		compute_LR_order();
	} else if(g_before_order_option == 4) {
		compute_Ldown_order();
	} else if(g_before_order_option == 5) {
		compute_Lup_order();
	} else if(g_before_order_option == 6) {
		compute_Adown_order();	
	} else if(g_before_order_option == 7) {
		compute_Aup_order();
	} else if(g_before_order_option == 8) {
		cout << " h^add (no order)" << endl;
	} else if(g_before_order_option == 9) {
		cout << " h^cea (pivot condition first, other conditions second)" << endl;	
	}  else {
		cerr << "no option to build Precedence Constraints specified!" << endl; 
	}
	// Note: Versions Add and Cea are embeded in the oc_heuristic.cc
	
}

// Notations:
// anc(q) = {p | ex. a path of <_n, <_gn, <_ln orders from p to q}
// direct-anc(q) = {p | p <_n q, p <_gn q}


// Version LADown. Order all facts.
// Rule: if p in anc(q) in the LandmarksGraph => set q before p and cause(q, p) = n
// in the PCGraph.
// The equavilent rule: if p <_ q is of edge type {n,gn,ln} in the landmarks 
// graph, then set q before p and cause(q, p) = {n} in the PCGraph.
void PCGraph::compute_LAdown_order() {
	//cout << "The version is LADown." << endl;
	set<PCNode*, PCNode::compare_nodes>::iterator it = nodes.begin();
	for(; it != nodes.end(); it++) {
		PCNode& cur_pcn = **it; // fact q
		// get the node corresponding to q in the PCGraph
		if(!lgraph->simple_landmark_exists(make_pair(cur_pcn.var, cur_pcn.val)))
			continue;
		LandmarkNode& cur_lmn = 
			(lgraph->get_simple_lm_node)(make_pair(cur_pcn.var,cur_pcn.val)); 
			
		hash_map<LandmarkNode*, edge_type, hash_pointer>::iterator 
										it2 = cur_lmn.parents.begin();
		for(; it2 != cur_lmn.parents.end(); it2++) {
			LandmarkNode& par_lmn = *(it2->first); // fact p is a parent of q
			if(par_lmn.disjunctive) continue;
			edge_type edge = it2->second;
			if(edge == r || edge == o_r) continue;
			PCNode& par_pcn = get_pc_node(make_pair(par_lmn.vars[0], par_lmn.vals[0]));
			edge_add(cur_pcn, par_pcn, n);
		}
	}
}

// Version LAUp. Order all facts.
// Rule: if p in anc(q) => set p before q and cause(p, q) = b_n.
// The equivalent Rule: if p <_ q is of edge type {n,gn,ln} in the landmarks 
// graph, then set p before q and cause(p, q) = {n} in the PCGraph.
void PCGraph::compute_LAup_order() {
	cout << "The version is LAup." << endl;
	set<PCNode*, PCNode::compare_nodes>::iterator it = nodes.begin();
	for(; it != nodes.end(); it++) {
		PCNode& cur_pcn = **it; // fact q
		// get the node corresponding to q in the PCGraph
		if(!lgraph->simple_landmark_exists(make_pair(cur_pcn.var, cur_pcn.val)))
			continue;
		LandmarkNode& cur_lmn = 
			(lgraph->get_simple_lm_node)(make_pair(cur_pcn.var,cur_pcn.val)); 
			
		hash_map<LandmarkNode*, edge_type, hash_pointer>::iterator 
										it2 = cur_lmn.parents.begin();
		for(; it2 != cur_lmn.parents.end(); it2++) {
			LandmarkNode& par_lmn = *(it2->first); // fact p is a parent of q
			if(par_lmn.disjunctive) continue;
			edge_type edge = it2->second;
			if(edge == r || edge == o_r) continue;
			PCNode& other_pcn = get_pc_node(make_pair(par_lmn.vars[0], par_lmn.vals[0]));
			edge_add(other_pcn, cur_pcn, n);
		}
	}
}

// Version LR. Order all facts.
// Rule: if m in direct-anc(p) and m mutex with q => set p BEFORE q; set
// cause(p,q) := cause(p,q) union {r}
void PCGraph::compute_LR_order() {
	//cout << "The version is LR." << endl;
	set<PCNode*, PCNode::compare_nodes>::iterator it = nodes.begin();
	for(; it != nodes.end(); it++) {
		PCNode& cur_pcn = **it; // fact p
		if(!lgraph->simple_landmark_exists(make_pair(cur_pcn.var, cur_pcn.val)))
			continue;
		LandmarkNode& cur_lmn = 
			(lgraph->get_simple_lm_node)(make_pair(cur_pcn.var,cur_pcn.val));
		bool parent_mutex = false;
		set<PCNode*, PCNode::compare_nodes>::iterator it2 = nodes.begin();
		for(; it2 != nodes.end(); it2++) {
			PCNode& other_pcn = **it2; // fact q
			if(&other_pcn == &cur_pcn) continue;
			if(!lgraph->simple_landmark_exists(make_pair(other_pcn.var, other_pcn.val)))
				continue;
			LandmarkNode& other_lmn = 
				(lgraph->get_simple_lm_node)(make_pair(other_pcn.var,other_pcn.val));
			// consider each n or gn direct ancestor (parent) m of p; check if m is mutex with q
			parent_mutex = false;
			hash_map<LandmarkNode*, edge_type, hash_pointer>::const_iterator 
										it_cur_parent = cur_lmn.parents.begin();			
			for(; it_cur_parent != cur_lmn.parents.end(); it_cur_parent++) {
				edge_type edge = it_cur_parent->second;
				if(edge == n || edge == gn ) {
					LandmarkNode& cur_parent = *(it_cur_parent->first);
					if(cur_parent.disjunctive) continue;
					if(&cur_parent == &other_lmn) continue;
					PCNode& par_pcn = get_pc_node(make_pair(cur_parent.vars[0], cur_parent.vals[0]));
					if(interferes(&par_pcn, &other_pcn)) {
						parent_mutex = true;
						break;
					}
				}				
			}
			
			if(parent_mutex) {
				edge_add(cur_pcn, other_pcn, r);
			}			
		} 
	}
}

// Version LDown. Order only landmarks.
// Rule 1: if p in anc(q) => set q BEFORE p; 
// set cause(p,q) := cause(p,q) union {n}
// Rule 2: if p <_r q => set p BEFORE q; 
// set cause(p,q) := cause(p,q) union {r}

// The equivilant of Rule 1: if p <_ q is of edge type {n,gn,ln} in the landmarks 
// graph, then set q before p and cause(q, p) = {n} in the PCGraph.
void PCGraph::compute_Ldown_order() {
	cout << "The version is LDown." << endl;
	set<PCNode*, PCNode::compare_nodes>::iterator it = nodes.begin();
	for(; it != nodes.end(); it++) {
		PCNode& cur_pcn = **it; // fact q
		// get the node corresponding to q in the PCGraph
		if(!lgraph->simple_landmark_exists(make_pair(cur_pcn.var, cur_pcn.val)))
			continue;
		LandmarkNode& cur_lmn = 
			(lgraph->get_simple_lm_node)(make_pair(cur_pcn.var,cur_pcn.val));
			 
		// apply Rule 1.	
		hash_map<LandmarkNode*, edge_type, hash_pointer>::iterator 
										it2 = cur_lmn.parents.begin();
		for(; it2 != cur_lmn.parents.end(); it2++) {
			LandmarkNode& par_lmn = *(it2->first); // fact p is a parent of q
			if(par_lmn.disjunctive) continue;
			edge_type edge = it2->second;
			if(edge == r || edge == o_r) continue;
			PCNode& par_pcn = get_pc_node(make_pair(par_lmn.vars[0], par_lmn.vals[0]));
			edge_add(cur_pcn, par_pcn, n);
		}
		
		// apply Rule 2
		hash_map<LandmarkNode*, edge_type, hash_pointer>::iterator
								it5 = cur_lmn.children.begin();
		for(; it5 != cur_lmn.children.end(); it5++) {
			if(it5->second == r) {
           		LandmarkNode& child_lmn = *(it5->first);
           		if(child_lmn.disjunctive) continue;
           		PCNode& child_pcn = get_pc_node(make_pair(child_lmn.vars[0], child_lmn.vals[0]));
           		edge_add(cur_pcn, child_pcn, r);
           	}   
        }
	}
}

// Version LUp. Order only landmarks.
// Rule 1: if p in anc(q) => set p BEFORE q; 
// set cause(p,q) := cause(p,q) union {n}
// Rule 2: if p <_r q => set p BEFORE q; 
// set cause(p,q) := cause(p,q) union {r}
// The equivilant of Rule 1: if p <_ q is of edge type {n,gn,ln} in the landmarks 
// graph, then set p before q and cause(p, q) = {n} in the PCGraph.

void PCGraph::compute_Lup_order() {
	cout << "The version is Lup." << endl;
	set<PCNode*, PCNode::compare_nodes>::iterator it = nodes.begin();
	for(; it != nodes.end(); it++) {
		PCNode& cur_pcn = **it;
		// get the node corresponding to q in the PCGraph
		if(!lgraph->simple_landmark_exists(make_pair(cur_pcn.var, cur_pcn.val)))
			continue;
		// apply Rule 1.
		LandmarkNode& cur_lmn = 
			(lgraph->get_simple_lm_node)(make_pair(cur_pcn.var,cur_pcn.val)); 
			
		hash_map<LandmarkNode*, edge_type, hash_pointer>::iterator 
										it2 = cur_lmn.parents.begin();
		for(; it2 != cur_lmn.parents.end(); it2++) {
			LandmarkNode& par_lmn = *(it2->first);
			if(par_lmn.disjunctive) continue;
			edge_type edge = it2->second;
			if(edge == r || edge == o_r) continue;
			
			PCNode& par_pcn = get_pc_node(make_pair(par_lmn.vars[0], par_lmn.vals[0]));
			edge_add(par_pcn, cur_pcn, n);
		}
		
		// apply Rule 2
		hash_map<LandmarkNode*, edge_type, hash_pointer>::iterator
								it5 = cur_lmn.children.begin();
		for(; it5 != cur_lmn.children.end(); it5++) {
			if(it5->second == r) {
           		LandmarkNode& child_lmn = *(it5->first);
           		if(child_lmn.disjunctive) continue;
           		PCNode& child_pcn = get_pc_node(make_pair(child_lmn.vars[0], child_lmn.vals[0]));
           		edge_add(cur_pcn, child_pcn, r);
           	}   
        }
	}
}

// Version ADown. Order all facts.
// Rule 1: if p in anc(q) => set q BEFORE p; 
// set cause(p,q) := cause(p,q) union {n}
// Rule 2: if m in direct-anc(p) and m mutex with q => set p BEFORE q; 
// set cause(p,q) := cause(p,q) union {r}

// The equivilant of Rule 1: if p <_ q is of edge type {n,gn,ln} in the landmarks 
// graph, then set q before p and cause(q, p) = {n} in the PCGraph.
void PCGraph::compute_Adown_order() {
	cout << "The version is Adown." << endl;
	set<PCNode*, PCNode::compare_nodes>::iterator it = nodes.begin();
	for(; it != nodes.end(); it++) {
		PCNode& cur_pcn = **it; // fact q
		if(!lgraph->simple_landmark_exists(make_pair(cur_pcn.var, cur_pcn.val)))
			continue;
		
		LandmarkNode& cur_lmn = 
			(lgraph->get_simple_lm_node)(make_pair(cur_pcn.var,cur_pcn.val)); 
			
		hash_map<LandmarkNode*, edge_type, hash_pointer>::iterator 
										it2 = cur_lmn.parents.begin();
		for(; it2 != cur_lmn.parents.end(); it2++) {
			LandmarkNode& par_lmn = *(it2->first); // fact p is a parent of q
			if(par_lmn.disjunctive) continue;
			edge_type edge = it2->second;
			if(edge == r || edge == o_r) continue;
			PCNode& par_pcn = get_pc_node(make_pair(par_lmn.vars[0], par_lmn.vals[0]));
			edge_add(cur_pcn, par_pcn, n);
		}
		
		// Rule 2:
		bool parent_mutex = false;
		set<PCNode*, PCNode::compare_nodes>::iterator it3 = nodes.begin();
		for(; it3 != nodes.end(); it3++) {
			PCNode& other_pcn = **it3; // fact p, a candidate
			if(&other_pcn == &cur_pcn) continue;
			if(!lgraph->simple_landmark_exists(make_pair(other_pcn.var, other_pcn.val)))
				continue;
			LandmarkNode& other_lmn = 
				(lgraph->get_simple_lm_node)(make_pair(other_pcn.var,other_pcn.val));
			
			// check if there is a parent m of fact q, such that m mutex with p 
			parent_mutex = false;
			hash_map<LandmarkNode*, edge_type, hash_pointer>::const_iterator 
										it_cur_parent = cur_lmn.parents.begin();			
			for(; it_cur_parent != cur_lmn.parents.end(); it_cur_parent++) {
				edge_type edge = it_cur_parent->second;
				if(edge == n || edge == gn) {
					LandmarkNode& cur_parent = *(it_cur_parent->first); // a parent m of fact q
					if(cur_parent.disjunctive) continue;
					if(&cur_parent == &other_lmn) continue;
					PCNode& par_pcn = get_pc_node(make_pair(cur_parent.vars[0], cur_parent.vals[0]));
					if(interferes(&par_pcn, &other_pcn)) { // m mutex with p
						parent_mutex = true;
						break;
					}
				}				
			}
			
			if(parent_mutex) {
				edge_add(cur_pcn, other_pcn, r);
			}			
		}
	}
}

// Version AUp. Order all facts.
// Rule 1: if p in anc(q) => set p BEFORE q; 
// set cause(p,q) := cause(p,q) union {n}
// Rule 2: if m in direct-anc(p) and m mutex with q => set p BEFORE q; 
// set cause(p,q) := cause(p,q) union {r}

// The equivilant of Rule 1: if p <_ q is of edge type {n,gn,ln} in the landmarks 
// graph, then set p before q and cause(p, q) = {n} in the PCGraph.
void PCGraph::compute_Aup_order() {
	cout << "The version is Aup." << endl;
	set<PCNode*, PCNode::compare_nodes>::iterator it = nodes.begin();
	for(; it != nodes.end(); it++) {
		PCNode& cur_pcn = **it; // fact q
		if(!lgraph->simple_landmark_exists(make_pair(cur_pcn.var, cur_pcn.val)))
			continue;	
		LandmarkNode& cur_lmn = 
			(lgraph->get_simple_lm_node)(make_pair(cur_pcn.var,cur_pcn.val)); 
			
		hash_map<LandmarkNode*, edge_type, hash_pointer>::iterator 
										it2 = cur_lmn.parents.begin();
		for(; it2 != cur_lmn.parents.end(); it2++) {
			LandmarkNode& par_lmn = *(it2->first); // fact p is a parent of q
			if(par_lmn.disjunctive) continue;
			edge_type edge = it2->second;
			if(edge == r || edge == o_r) continue;
			PCNode& par_pcn = get_pc_node(make_pair(par_lmn.vars[0], par_lmn.vals[0]));
			edge_add(par_pcn, cur_pcn, n);
		}
		
		// Rule 2:
		bool parent_mutex = false;
		set<PCNode*, PCNode::compare_nodes>::iterator it3 = nodes.begin();
		for(; it3 != nodes.end(); it3++) {
			PCNode& other_pcn = **it3; // fact p, a candidate
			if(&other_pcn == &cur_pcn) continue;
			if(!lgraph->simple_landmark_exists(make_pair(other_pcn.var, other_pcn.val)))
				continue;
			LandmarkNode& other_lmn = 
				(lgraph->get_simple_lm_node)(make_pair(other_pcn.var,other_pcn.val));
			// check if there is a parent m of fact q, such that m mutex with p 
			parent_mutex = false;
			hash_map<LandmarkNode*, edge_type, hash_pointer>::const_iterator 
										it_cur_parent = cur_lmn.parents.begin();
			for(; it_cur_parent != cur_lmn.parents.end(); it_cur_parent++) {
				edge_type edge = it_cur_parent->second;
				if(edge == n || edge == gn) {
					LandmarkNode& cur_parent = *(it_cur_parent->first); // a parent m of q
					if(cur_parent.disjunctive) continue;
					if(&cur_parent == &other_lmn) continue;
					PCNode& par_pcn = get_pc_node(make_pair(cur_parent.vars[0], cur_parent.vals[0]));
					if(interferes(&par_pcn, &other_pcn)) { // m is mutex with p
						parent_mutex = true;
						break;
					}
				}				
			}
			
			if(parent_mutex) {
				edge_add(cur_pcn, other_pcn, r);
			}
		}
	}
}

// If there is a set of facts F, and |F| = m, then how many different partial 
// orders could be defined on F? The answer: there are m*(m-1) arcs between these
// facts. In a partial order, each arc may exist or not. So, there are 2^(m*(m-1))
// different orders. Hence, the number of partial orders are very large. eg,
// if we have 100 facts, then the number of partial orders on these facts are
// 2^(100*99)=2^990.
void PCGraph::compute_Rand_order() {
	cerr << "The version is Rand, but currently Not impelmented!" << endl;
	exit(1);
}

void PCGraph::mk_acyclic() {
	hash_set<PCNode*, hash_pointer> acyclic_node_set;
    int removed_edges = 0;
    set<PCNode*, PCNode::compare_nodes>::iterator it = nodes.begin();
    for(; it != nodes.end(); it++) {
        PCNode& pcn = **it;
        if(acyclic_node_set.find(&pcn) == acyclic_node_set.end())
            removed_edges += loop_acyclic_graph(pcn, acyclic_node_set);
    }
    assert(acyclic_node_set.size() == number_of_nodes());    
    //cout << "Cycle-break: removed " << removed_edges << " *PC order* edges\n";
}

// If a cycle exists, then there are at least one "r" edge in it. So, we 
// could remove an "r" edge to break the cycle.
bool PCGraph::remove_reasonable_cycle_edge(PCNode* cur,
                                 list<pair<PCNode*, edge_type> >& path,
                                 list<pair<PCNode*, edge_type> >::iterator it) {
	PCNode* parent_p = 0;
    PCNode* child_p = 0;
    list<pair<PCNode*, edge_type> >::iterator it2 = it;
    for(; it2 != path.end() ; it2++) {
        edge_type edge = it2->second;
        if(edge == r) {
            parent_p = it2->first;
            if(*it2 == path.back()) {
                child_p = cur;
            } else {
                list<pair<PCNode*, edge_type> >::iterator child_it = it2;
                child_it++;
                child_p = child_it->first;
            }                        
           	break;
        }
    }
    
    assert(parent_p != 0 && child_p != 0);
    assert(parent_p->children.find(child_p) != parent_p->children.end());
    assert(child_p->parents.find(parent_p) != child_p->parents.end());
    parent_p->children.erase(child_p);
    child_p->parents.erase(parent_p);
    return true;                                     
}

int PCGraph::loop_acyclic_graph(PCNode& pcn, hash_set<PCNode*, hash_pointer>& acyclic_node_set) {
	assert(acyclic_node_set.find(&pcn) == acyclic_node_set.end());
    int nr_removed = 0;
    list<pair<PCNode*, edge_type> > path;
    hash_set<PCNode*, hash_pointer> visited;
    PCNode* cur = &pcn;
    while(true) {
        assert(acyclic_node_set.find(cur) == acyclic_node_set.end());
        if(visited.find(cur) != visited.end()) { // cycle
            // find other occurence of cur node in path
            list<pair<PCNode*, edge_type> >::iterator it;
            for(it = path.begin(); it != path.end(); it++) {
                if(it->first == cur)
                    break;
            }
            assert(it->first == cur);
            // remove edge from graph
            bool removed = remove_reasonable_cycle_edge(cur, path, it);
            assert(removed);
            nr_removed++;

            path.clear();
            cur = &pcn;
            visited.clear();
            continue;
        }
        
        // 
        visited.insert(cur);
        bool empty = true;
        for(map<PCNode*, edge_type, PCNode::compare_nodes>::const_iterator it
                = cur->children.begin();
                it != cur->children.end();
                it++) {
            edge_type edge = it->second;
            PCNode* child_p = it->first;
            if(acyclic_node_set.find(child_p) == acyclic_node_set.end()) {
                path.push_back(make_pair(cur, edge));
                cur = child_p;
                empty = false;
                break;
            }
        }
        if(!empty)
            continue;

        // backtrack
        visited.erase(cur);
        acyclic_node_set.insert(cur);
        if(!path.empty()) {
            cur = path.back().first;
            path.pop_back();
            visited.erase(cur);
        } else
            break;
    }
    assert(acyclic_node_set.find(&pcn) != acyclic_node_set.end());
    return nr_removed;
}

// The "interfers" function here is different from that in the LandmarksGraph
// Facts a and b interfere if a and b are inconsistent
bool PCGraph::interferes(const PCNode* node_a, const PCNode* node_b) const { 
    pair<int, int> a = make_pair(node_a->var, node_a->val);
    pair<int, int> b = make_pair(node_b->var, node_b->val);
    assert(a.first != b.first || a.second != b.second);

    // a, b are inconsistent
    if((lgraph->inconsistent)(a,b))
        return true;
        
    return false;
}

void PCGraph::collect_pc_ancestors(hash_set<PCNode*, hash_pointer>& result, PCNode& node) {
	list<PCNode*> open_nodes;
    hash_set<PCNode*, hash_pointer> closed_nodes;
		
    for(map<PCNode*, edge_type, PCNode::compare_nodes>::iterator it
            = node.parents.begin(); it != node.parents.end(); it++) {
        
        edge_type& edge = it->second;
        PCNode& parent = *(it->first);
        assert(edge == n || edge == r);
        
        if(closed_nodes.find(&parent) == closed_nodes.end()) {
        	open_nodes.push_back(&parent);
        	closed_nodes.insert(&parent);
                
       		result.insert(&parent);
        }
    }

    while(!open_nodes.empty()) {
        PCNode& node2 = *(open_nodes.front());
        for(map<PCNode*, edge_type, PCNode::compare_nodes>::iterator 
        	it = node2.parents.begin(); it != node2.parents.end(); it++) {
            edge_type& edge = it->second;
            PCNode& parent = *(it->first);
            assert(edge == n || edge == r);
            
            if(closed_nodes.find(&parent) == closed_nodes.end()) {
            	open_nodes.push_back(&parent);
                closed_nodes.insert(&parent);
                    
            	result.insert(&parent);
            }
        }
        open_nodes.pop_front();
    }
}

// Determine the best ancestor of each fact f in a precond: 
// require each ancestor be in the precond.
// 1. Let q be a fact in the condition.
// 2. Let P be the following set of facts: P = {p in condition | p BEFORE*
// q and (not exists p' in condition: (p' BEFORE* q and p BEFORE* p'))}.
// 3. Let p be the member of P with minimal index(p).
// 4. Set context(q) := p.
void PCGraph::set_best_anc(vector<PCNode*>& pcns_in_precond) {
	// collect the ancestors of each fact in the precond, 
	// and the ancestors of each fact must belong to the precond.
	vector<PCNode*>::iterator it = pcns_in_precond.begin();
        //cout<<"before"<<endl;
	for(; it != pcns_in_precond.end(); it++) {
		PCNode& cur_pcn = **it;
		if(!cur_pcn.ancestors_collected) {
			//cout<<"before collect_pc"<<endl;
			collect_pc_ancestors(cur_pcn.ancestors, cur_pcn);
			cur_pcn.ancestors_collected = true;
			//cout<<"after collect_pc"<<endl;
		}
		//if(g_variable_types[cur_pcn.var] == comparison) cout<<"it's comparison"<<endl;
		//cur_pcn.ancs_in_cond.clear(); // clear previous data
		//cout<<"get anceste"<<endl;
		const hash_set<PCNode*, hash_pointer>& ancestors = cur_pcn.ancestors;
		//cout<<ancestors.size()<<"getton anceste"<<endl;
		vector<PCNode*>::iterator it2 = pcns_in_precond.begin();
		for(; it2 != pcns_in_precond.end(); ++it2) {
			PCNode& pcn = **it2;
			//cout<<"count    "<<ancestors.size()<<endl;
			if(ancestors.count(&pcn) > 0){
				//cout<<"where is rong"<<endl;
				cur_pcn.ancs_in_cond.insert(&pcn);
				//cout<<"is here"<<endl;
			}
				
			//cout<<"done"<<endl;
		}
		assert(!cur_pcn.ancs_in_cond.count(&cur_pcn));
	}
	//cout<<"end"<<endl;
	// determine ctx() for each pcn (fact) in the precond
	for(it = pcns_in_precond.begin(); it != pcns_in_precond.end(); it++) {
		PCNode& cur_pcn = **it;
		cur_pcn.best_anc = NULL;
				
		if(cur_pcn.ancs_in_cond.empty())
			continue;
		
		set<PCNode*>::const_iterator it_anc = cur_pcn.ancs_in_cond.begin();		
		// consider each ancestor of cur_pcn
		for(; it_anc != cur_pcn.ancs_in_cond.end(); it_anc++) {
			PCNode& anc_pcn = **it_anc; // a candidate ancestor
			assert(&anc_pcn != &cur_pcn);
			
			bool nearest_anc = true;		
			// is anc_pcn is an nearest ancestor of cur_pcn?
			// ie., whether anc_pcn is not the ancestor of any ancestor of cur_pcn
			set<PCNode*>::const_iterator it2 = cur_pcn.ancs_in_cond.begin();
			for(; it2 != cur_pcn.ancs_in_cond.end(); it2++) {				
				if((*it2)->ancs_in_cond.find(&anc_pcn) 
						!= (*it2)->ancs_in_cond.end()) {
					assert(&(**it2) != &anc_pcn);
					nearest_anc = false;
					break;	
				}
			}
			
			// a nearest ancestor found?
			// if true, update context(lmn) if it has lower index
			if(nearest_anc) {
				if(!cur_pcn.best_anc) {
					cur_pcn.best_anc = &anc_pcn;
				} else {
					if(anc_pcn.var < cur_pcn.best_anc->var ||
						(anc_pcn.var == cur_pcn.best_anc->var)
						&& (anc_pcn.val < cur_pcn.best_anc->val)) {
							/*
							cout << "a nearer anc with lower index found: " << endl;
							cout << "the current best_anc: ";
							dump_node(cur_pcn.best_anc);
							cout << "the new best_anc: ";
							dump_node(&anc_pcn);
							*/
							
							cur_pcn.best_anc = &anc_pcn;
					}
				}
			}
		}			
		assert(cur_pcn.best_anc);
	}	
}

