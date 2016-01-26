
#include "pc_heuristic.h"
#include <algorithm>
#include <cassert>
#include <vector>
#include <set>

#include "domain_transition_graph.h"
#include "globals.h"
#include "operator.h"
#include "state.h"

#include "landmarks_graph.h"
#include "pc_graph.h"

class CausalGraph;
using namespace std;

PCHeuristic *g_HACK = 0;

LocalProblem::LocalProblem(int the_var_no, int the_start_value) :
    base_priority(-1.0), var_no(the_var_no), causal_graph_parents(NULL), start_value(the_start_value) {
}

double LocalTransition::get_direct_cost() {
    double ret = 0.0;
    assert(label);
    if(label->duration_variable != -1) {
        if(label->duration_variable == -2) {
            assert(false);
            ScheduledOperator *s_op = dynamic_cast<ScheduledOperator*>(label->op);
            assert(s_op);
            g_HACK->set_waiting_time(max(g_HACK->get_waiting_time(),s_op->time_increment));
//            cout << "wait for " << s_op->get_name() << "....waiting_time: " << g_HACK->get_waiting_time() << endl;
        } else {
            LocalProblemNode *source = get_source();
	    int global_duration_var = (*(source->owner->causal_graph_parents))[duration_var_local];
	    if(source->changed_facts.count(global_duration_var) > 0) ret = source->changed_facts[global_duration_var];
            else ret = (*(g_HACK->state))[global_duration_var];
        }
    }
    //TODO: HACK for modeltrain, where it appears, that the duration of a transition is negative...WHY???
    if(ret < 0.0)
        ret = 0.0;
    return ret;
}

//////////////////////////////////////////////////////
// Given facts in the precond; derive precedence constraints outgoing_transitions.clear();
// waiting_list.clear();er them from the
// before graph. 
// Firstly, for "precond", compute its ordered copy "tmp_ordered_precond", 
// and then replace the content of "precond" with that of "tmp_ordered_precond".
void LocalTransition::apply_before_order(vector<LocalAssignment> &precond) {
	assert(!condition_ordered);
	if(precond.size() <= 1)
		return; // no order can apply
	
	// Hack here for special order options: h^add and h^cea
	// for h^add, do nothing and return;
	if(g_before_order_option == 8 || g_before_order_option == 9) {
		return;
	}
	/*
	// for the ctx() function wrt. hcea 
	if(g_before_order_option == 9) {
		int pivot_var = source->owner->var_no;
		int pivot_value = source->value;
		bool found = false;
		// remove pivot conditon from precond
		vector<LocalAssignment>::iterator it = precond.begin();	
		for(; it != precond.end(); it++) {
			if(it->local_var == pivot_var && it->value == pivot_value) {
				found = true;
				precond.erase(it);
				break;
			}		
		}
		assert(found);
              // put pivot condition into the front of precond
	      //??????????the local var of pivot
 		assert(source->owner->global_to_local_parents.count(pivot_var) > 0);
                int local_pivot = global_to_local_parents[pivot];
		precond.insert(precond.begin(), LocalAssignment(g_transition_graphs[pivot_var], pivot_var,local_pivot, pivot_value));
		assert(precond.size() == precede_idx.size());
		for(int i = 1; i < precede_idx.size(); i++) {
			precede_idx[i] = 0;
		}
		
		return;
	}
	*/


       // The follwing procedure is for our Precedence Constrains version
	const int nm_conds = precond.size();
	vector<PCNode*> pcns_in_precond;
	vector<PCNode*> pre_lm;
	pcns_in_precond.reserve(nm_conds);
	// cout << "Ordering precond " << endl;
	// (1) fetch the pcns corresponding to facts in the precond	
        //////////////////////////////////////////////////////////////////////////
        for(int i = 0;i < precond.size();++i){
                int global_var = precond[i].global_var;				
	        pair<int, int> prop = make_pair(global_var, static_cast<int>(precond[i].value));
                if(g_variable_types[global_var] == comparison){
			/*vector<int> vars;
			vars.push_back(global_var);
			vector<int> vals;
			vals.push_back(static_cast<int>(precond[i].value));
                        LandmarkNode cur_lmnc(vars, vals, false);
			pre_lm.push_back(&cur_lmnc);*/
                        PCNode* cur_pcnc = new PCNode(global_var,static_cast<int>(precond[i].value));
			pre_lm.push_back(cur_pcnc);
                             
                }else{
			assert(g_pcgraph->node_exists(prop));
			PCNode& cur_pcn = g_pcgraph->get_pc_node(prop);	//
		        //g_pcgraph->dump_node(&cur_pcn); // debug
		        pre_lm.push_back(&cur_pcn);
		}
		pre_lm[i]->ancs_in_cond.clear();	
	}
	for(int i = 0; i < precond.size(); ++i) {
		//if(!flag[i]){
		pcns_in_precond.push_back(pre_lm[i]);
		//lmn_to_precond_idx.insert(make_pair(pre_lm[i], i));
			//flag[i] = true;
		//} 
		int gl_var = precond[i].global_var;			
		if(g_variable_types[gl_var] == logical){
			for(int j = 0;j < precond.size();++j){
				int gc_var = precond[j].global_var;
				if(g_variable_types[gc_var] == comparison){
					DomainTransitionGraphComp* dtgc =
                                             dynamic_cast<DomainTransitionGraphComp*> (g_transition_graphs[gc_var]);
				 	if(dtgc->global_to_local_ccg_parents.find(gl_var) !=
					  dtgc->global_to_local_ccg_parents.end()){
						pre_lm[i]->ancs_in_cond.insert(pre_lm[j]);
					}
				}
			}
		}
			
				
	}
        ///////////////////////////////////////////////////////////////////////////////
	assert(pcns_in_precond.size() == nm_conds);
	
	// (2) set the ctx() of each pcn (fact) in pcns_in_precond	
	g_pcgraph->set_best_anc(pcns_in_precond); 
	
	// (3) Start a topological sort on the partial order definded by ctx() 
	// over pcns_in_precond. This step is to make the partial order a sequential one
	// that is convinient to be used in computing the costs of transitions.
	vector<pair<PCNode*, int> > orders;
	vector<int> in_orders(nm_conds, 0); // flags indicate if a pcn in pcns_in_precond was put into the orders
	// initialize "orders" with pcns who doesn't have a best_anc; ie, with ctx() undefined
	for(int i = 0; i < nm_conds; i++) {
		PCNode* pcn = pcns_in_precond[i];
		/*
		g_pcgraph->dump_node(pcn); // debug
		if(pcn->best_anc) {
			cout << "best_anc: " ;
			g_pcgraph->dump_node(pcn->best_anc);
		} else cout << "no best_anc " << endl;
		*/ 
		
		if(!(pcn->best_anc)) {
			orders.push_back(make_pair(pcn,i));
			in_orders[i] = 1;
		}
	}	
	// if every fact p in precond is with ctx(p) is undefined, then just return.
	if(orders.size() == nm_conds) return; 
	
	int pos = 0;
	while(pos < orders.size()) {
		pair<PCNode*, int> &e = orders[pos];
		PCNode &cur_pcn = *(e.first);
		// put into "orders" those pcns whose best_anc is cur_pcn 
		for(int i = 0; i < nm_conds; i++) {
			if(in_orders[i] != 1) {
				PCNode *candidate_pcn = pcns_in_precond[i];
				if(&*(candidate_pcn->best_anc) == &cur_pcn) {
					precede_idx[orders.size()] = pos;
					orders.push_back(make_pair(candidate_pcn, i));
					in_orders[i] = 1;					
				}
			}
		}
		pos++;
	}
	assert(orders.size() == nm_conds);
	// (4) reset the precond with sequential result of the partial order
	vector<LocalAssignment> tmp_ordered_precond;
	tmp_ordered_precond.reserve(nm_conds);
	vector<pair<PCNode*, int> >::iterator it = orders.begin();
	for(; it != orders.end(); ++it) {
		tmp_ordered_precond.push_back(precond[it->second]);
	}
  	precond.clear();
  	precond.assign(tmp_ordered_precond.begin(), tmp_ordered_precond.end());
  	assert(precede_idx.size() == nm_conds);
	
	for(int i = 0;i < pcns_in_precond.size();++i){
		if(g_variable_types[pcns_in_precond[i]->var] == comparison) delete pcns_in_precond[i];
	}
	/* debug
	cout << "The ordered precond: ";
	for(int i = 0; i < nm_conds; i++) {
		int global_var = precond[i].local_var;
		cout << g_variable_name[global_var] << "=" << precond[i].value << ";";
	}
	cout << endl;
  	
  	cout << "ctx(): ";
  	for(int i = 0; i < nm_conds; i++) {
  		cout << ctx_idx[i] << " ";
  	}
  	cout << endl;
  	exit(1);
  	*/

}
///////////////////////////////////////////////////////////////////////////////
// fetch the start value for p with var(p)=precond_var from the context state associated 
// with ctx(p)=[conditiont][preced_cond_idx].
// the context state of ctx(p) has 3 possible status:
// (1) when ctx(p) is undef, the context state is the current state;
// (2) when ctx(p) is defined, but the node corresponding to ctx(p) is not determined, 
// due to the start value of ctx(p) is not known;
// (3) when ctx(p) is defined, but the node corresponding to ctx(p) is not expanded; 
// (4) ctx(p) is defined, and the cost of ctx(p) is known, 
// ie, the node corresponding to ctx(p) was expanded.
// In cases (1) and (4) we can "attempt to open a context for p", 
// while for (2) and (3) we wait. Note the special treatment for C.var.
double LocalTransitionDiscrete::get_start_value(const int precond_var, const int preced_cond_idx) {
        if(preced_cond_idx == UNDEF){
                // (1)	
		// if the precond_var is the same as C.var, return C.state(C.var)
		if(precond_var == source->owner->var_no)
			return (source->owner->start_value);
		else // for other variables
			return (*(g_HACK->state))[precond_var];

        }else{// ctx(q) is defined
		assert(preced_cond_idx > -1);
		if(waiting_nodes[preced_cond_idx]) // if the node corresponding to p is known
			return waiting_nodes[preced_cond_idx]->get_context(precond_var); // (3) or (4)
		else if(g_variable_types[ordered_precond[preced_cond_idx].global_var] == comparison){
			if(precond_var == source->owner->var_no)
				return (source->owner->start_value);
		        else // for other variables
				return (*(g_HACK->state))[precond_var];	
		}
		else {return UNDEF * 1.0;} // (2)
        }
}
double LocalTransitionComp::get_start_value(const int precond_var, const int preced_cond_idx) {

	if(preced_cond_idx != UNDEF) { // ctx(q) is defined
		assert(preced_cond_idx > -1);
		if(waiting_nodes[preced_cond_idx]) // if the node corresponding to p is known
			return waiting_nodes[preced_cond_idx]->get_context(precond_var); // (3) or (4)
		else {return UNDEF * 1.0; }// (2)
		
	} else { // (1)	
		// if the precond_var is the same as C.var, return C.state(C.var)
		if(precond_var == source->owner->var_no)
			return (source->owner->start_value);
		else {// for other variables
			//return (*(g_HACK->state))[precond_var];
			if(source->changed_facts.count(precond_var) > 0) 
 				return source->changed_facts[precond_var];
			else return (*(g_HACK->state))[precond_var];
		}
	}
}
//for the order version
void LocalTransitionDiscrete::on_ordered_condition_reached(const LocalProblemNode* reach_cond, 
                                                           const int cond_index) {
	assert(waiting_nodes[cond_index]);
	assert(&*(waiting_nodes[cond_index]) == &*reach_cond);
	
	--unreached_conditions;   
    target_cost += reach_cond->cost;
    //ignore the lower_bound and target_cost, 10_10_12
    if(target->cost <= max<double>(target_cost, lower_bound))
    	return;
   
    //vector<vector<LocalProblem *> > &problem_index = g_HACK->local_problem_index;
   	vector<LocalAssignment>::const_iterator curr_precond = ordered_precond.begin(),
   						last_precond = ordered_precond.end();
    // pose to the next condition to be considered
    for(int i = 0; i <= cond_index; i++)
    	++curr_precond;

    int cur_cond_index = cond_index + 1;    
    for(; curr_precond != last_precond; ++curr_precond, ++cur_cond_index) {
        if(waiting_nodes[cur_cond_index])
        	continue;
        const int var = curr_precond->global_var;
        int precond_value = static_cast<int>(curr_precond->value);
       	assert(precede_idx[cur_cond_index] < cur_cond_index);
        const int start_val = static_cast<int>(get_start_value(var, precede_idx[cur_cond_index]));

        if(start_val == UNDEF) continue;
        contexted_start_values[cur_cond_index] = start_val;
        if(g_variable_types[var]==comparison && start_val == precond_value) continue;
      	LocalProblem *child_problem = g_HACK->get_local_problem(var, start_val);
        if(!child_problem->is_initialized()) {
      		//child_problem = new LocalProblem(var);
      		//g_HACK->local_problems.push_back(child_problem);
            double base_priority = source->priority();
            child_problem->initialize(0, start_val, *(g_HACK->state));
      	}
      	//assert(problem_index[var][start_val]);      	  
      //	if(!child_problem->is_initialized()) {
      //		child_problem->initialize(0, start_val);
      //	}
      	LocalProblemNode *cond_node = child_problem->get_node(precond_value);
        waiting_nodes[cur_cond_index] = cond_node;
	if(!double_equals(cond_node->reached_by_wait_for,-1.0)) {
            	assert(cond_node->cost == 0.0);
            	assert(cond_node->cost <QUITE_A_LOT);
                g_HACK->set_waiting_time(max(g_HACK->get_waiting_time(),cond_node->reached_by_wait_for - EPS_TIME));
                --unreached_conditions;
//                cout << "cond_node: " << g_HACK->get_waiting_time() << endl;
        } else if(cond_node->expanded) {
       		--unreached_conditions;
       		target_cost += cond_node->cost;
		if(target->cost <= max(target_cost, lower_bound))
       			return;       		
        } else {
        	cond_node->add_to_waiting_list(this, cur_cond_index);
        }
     }
     
     try_to_fire();
}


void LocalTransitionDiscrete::on_source_expanded(const TimeStampedState &state) {
    assert(source->cost >= 0);
    assert(source->cost <QUITE_A_LOT);
    assert(source->owner == target->owner);
    double duration = 0.0;
    unreached_conditions = 0;
    if(g_HACK->is_running(this,state)) {
        target_cost = 0.0;
    } else {
        duration = get_direct_cost();
        target_cost = duration;
	lower_bound = source->cost + duration; // initilized to cost(source_value)+1
        if(target->cost <= max<size_t>(target_cost, lower_bound)) 
        return;
    //(1) order the precondition
    //for ordered precondition, it's like this: var, pre, post
    if(!condition_ordered){
          assert(ordered_precond.empty());
    	  const int num_preconds = label->precond.size();
    	  ordered_precond.reserve(num_preconds + 1);
    	  // the following code is to avoid repeated conditions in ADL domains
    	  set<pair<int,double> > facts;
          for(int i = 0; i < num_preconds; i++) {
    		// note: the index of variable in the ordered_precond are 
    		// all converted to their global index here
    		//int global_var = label->precond[i].prev_dtg->var;
		int global_var = (*(get_source()->owner->causal_graph_parents))[label->precond[i].local_var];
    		double value = label->precond[i].value;
    		pair<int,double> fact = make_pair(global_var, value);
    		if(!facts.count(fact)) { // if the fact is not included
    			ordered_precond.push_back(LocalAssignment(label->precond[i].prev_dtg, global_var, label->precond[i].local_var,value));
    			facts.insert(fact);
    		}
    	}
        // initialize data member
    	precede_idx.resize(ordered_precond.size(), -1);
	// apply ordering but not on the dummy top level transition 
        //here ,here, order the precondtion except the goals
    	if(&*source->owner != &*g_HACK->goal_problem){    		
    		// add the "pivot condition" into ordered_precond
    		if(!facts.count(make_pair(source->owner->var_no, source->value))) {
                // the pivot var's local var is itself?
                        int var_source = source->owner->var_no;
                        /*if(source->owner->global_to_local_parents.count(var_source) < 1){
                              int local_source = source->owner->causal_graph_parents.size();
                              source->owner->global_to_local_parents[var_source] = local_source;
                              source->owner->causal_graph_parents.push_back(var_source);
                        }*/
                        assert(source->owner->global_to_local_parents->count(var_source) > 0);
                        int local_var_source = source->owner->global_to_local_parents->find(var_source)->second;
    			ordered_precond.push_back(LocalAssignment(g_transition_graphs[var_source], var_source,            local_var_source, source->value));  
    			precede_idx.push_back(-1);
                        //cout << "local_var_source" << local_var_source << endl;
    		}    		
    		// determine the ctx() info for facts in [condition]
                /*cout << endl << "the order begin" << endl;
		for(int i = 0;i < ordered_precond.size(); ++i){
			cout << ordered_precond[i].global_var<< "  "<<ordered_precond[i].value<<endl;
		}*/
    		apply_before_order(ordered_precond);
		/*cout << "the order done" <<  endl << endl;
		for(int i = 0;i < ordered_precond.size(); ++i){
			cout << ordered_precond[i].global_var<< "  "<<ordered_precond[i].value<<endl;
		}*/
    	}
        else num_lg = ordered_precond.size();
    	condition_ordered = true;

	/*cout << "the precond of this expand" << endl;
    	for(int i = 0;i < ordered_precond.size(); ++i){
			cout << ordered_precond[i].global_var<< "  "<<ordered_precond[i].value<<endl;
	}*/

    	waiting_nodes.resize(precede_idx.size());
    	contexted_start_values.resize(precede_idx.size());
    }
    // reset info
    for(int i = 0; i < waiting_nodes.size(); i++) {
	 waiting_nodes[i] = NULL;
	 contexted_start_values[i] = -1;	
    }

    // (2) compute the cost of each condition	
    const vector<LocalAssignment> &prevail = ordered_precond;
    vector<LocalAssignment>::const_iterator
    						curr_precond = prevail.begin(),
    						last_precond = prevail.end();
    //vector<vector<LocalProblem *> > &problem_index = g_HACK->local_problem_index;
    int cur_cond_idx = 0;
  	assert(precede_idx[cur_cond_idx] == UNDEF);
    for(; curr_precond != last_precond; ++curr_precond, ++cur_cond_idx){
        const int var = curr_precond->global_var;
        int precond_value = static_cast<int>(curr_precond->value);
        assert(precede_idx[cur_cond_idx] < cur_cond_idx);
        assert(g_variable_types[var]==logical ||
                g_variable_types[var]==comparison); 
        const int start_val = static_cast<int>(get_start_value(var, precede_idx[cur_cond_idx]));
        //if(start_val == UNDEF) cout <<"source_expand"<<var << "   " << cur_cond_idx << endl;
	//
       // cout<<(*(g_HACK->state))[var]<<endl;}
      	if(start_val == UNDEF) continue;
	//if(g_variable_types[var]==comparison){ cout<<"i am com "<<start_val<<" preval "<<precond_value<<endl;}
      	contexted_start_values[cur_cond_idx] = start_val;
	if(g_variable_types[var]==comparison && start_val == precond_value) continue;
      	LocalProblem *child_problem = g_HACK->get_local_problem(var, start_val);
        if(!child_problem->is_initialized()) {  
                double base_priority = source->priority();
                child_problem->initialize(0, start_val, state);     		
      	} 
      	LocalProblemNode *cond_node = child_problem->get_node(precond_value);
      	waiting_nodes[cur_cond_idx] = cond_node;
        if(!double_equals(cond_node->reached_by_wait_for,-1.0)) {
            	assert(cond_node->cost == 0.0);
            	assert(cond_node->cost <QUITE_A_LOT);
                g_HACK->set_waiting_time(max(g_HACK->get_waiting_time(),cond_node->reached_by_wait_for - EPS_TIME));
//                cout << "cond_node: " << g_HACK->get_waiting_time() << endl;
        } else if(cond_node->expanded) {
      		target_cost += cond_node->cost;
		if(target->cost <= max<size_t>(target_cost, lower_bound))
        	    return;
      	} else { // the cost of the node according to the current fact is not known
      		cond_node->add_to_waiting_list(this, cur_cond_idx);
		++unreached_conditions;
      	}
    }
    }
    try_to_fire();
}

void LocalTransitionDiscrete::on_condition_reached(int /*cond_no*/, double cost) {
    assert(unreached_conditions);
    --unreached_conditions;
    target_cost = target_cost + cost;
    try_to_fire();
}

void LocalTransitionDiscrete::try_to_fire() {
    //if(!unreached_conditions && target_cost < target->cost) {
//        target->cost = target_cost;
//        target->reached_by = this;
//        target->pred = this;
//        g_HACK->add_to_queue(target);
//    }
    //ignore the estimate_target_cost and target_cost
     double estimate_target_cost = max<double>(lower_bound, target_cost);
    		assert(estimate_target_cost > -1.0); 
    assert(target_cost > -1.0);
    if(!unreached_conditions && target_cost < target->cost) {
    	// 1. to handle two transitions with the same estimation of target->cost,
    	// where the later one has a lower cost. target is not needed to be put
    	// into the heap in this case! 
        
    	if(estimate_target_cost == target->cost && 
    		(target_cost < target->lowest_trans_cost)) {
    		target->lowest_trans_cost = target_cost;
    		//update_target_state();
    		target->reached_by = this;
    		assert(!(target->expanded));
    	}
   		
   		// 2. to handle two transitions, where the later havs a better
   		// estimation of target->cost.
    	if(estimate_target_cost < target->cost) {
    		target->cost = target_cost;
    		target->lowest_trans_cost = target_cost;
    		//update_target_state();
    		target->reached_by = this;
    		assert(!(target->expanded)); 
    		g_HACK->add_to_queue(target);
		//cout << "jia 1:  " << target->owner->var_no << " " << target->value << endl;
    	}
    }            
}

// we have option 1, 2 and 3 here.
void LocalTransitionDiscrete::update_target_state() {
	map<int, double> &changed_facts = target->changed_facts;
	changed_facts.clear();
	// fill in changed_fact wrt y0 acrroding to option 1 and 2, and 3!
	int i = waiting_nodes.size() - 1;
	switch(g_HACK->transtition_option) {
		case 1:
			changed_facts = waiting_nodes[0]->changed_facts;
			break;
		case 2: 
                        while(waiting_nodes[i] == NULL){
				i--;
			}
			assert(i >= 0);
			changed_facts = waiting_nodes[i]->changed_facts;
			break;
		case 3:
			changed_facts = source->changed_facts;
			break;
		default:
			cout << "invalid transition option" << endl;
			exit(1);
	}
	// (1) update context wrt. precondition
    for(int i = 0; i < ordered_precond.size(); i++) 
    	changed_facts[ordered_precond[i].global_var] = ordered_precond[i].value;
    // (2) update context wrt. effect
  	//vector<int>* parent_vars = source->owner->causal_graph_parents;
    const vector<LocalAssignment> &effect = label->effect;
    for(int i = 0; i < effect.size(); i++) {
    	//int global_var = parent_vars[effect[i].local_var];
    	if(g_variable_types[effect[i].prev_dtg->var] == logical){
              changed_facts[effect[i].global_var] = effect[i].value;                                          
        }else{
              assert(g_variable_types[effect[i].prev_dtg->var] == primitive_functional);
              //the state[var] fop= state[var']: var' is the parent of var_no, that's label's source->owner->var_no????
              int *parent_vars = &*source->owner->causal_graph_parents->begin(); 
              const LocalAssignment &la = effect[i];
              target->updatePrimitiveNumericVariable(la.local_var,la.fop, la.global_var, parent_vars[la.var], changed_facts);      
        }
    	
    }
    // (3) update context wrt. the value transition of this var
    if(&*source->owner != &*g_HACK->goal_problem) {
    	changed_facts[source->owner->var_no] = target->value;
    }
}


void LocalTransitionDiscrete::print_description() {
    cout << "TransitionDiscrete" << "<" << source->owner->var_no << "|" << source->value << ","
            << target->value << "> (" << this << "), prevails: ";
    for(int i = 0; i < label->precond.size(); i++) {
        cout
                << (*source->owner->causal_graph_parents)[label->precond[i].local_var]
                << ": " << label->precond[i].value << " ";
    }
    cout << endl;
}

LocalProblemNodeDiscrete::LocalProblemNodeDiscrete(
        LocalProblemDiscrete *owner_, int children_state_size, int the_value) :
    LocalProblemNode(owner_, children_state_size), value(the_value) {
    expanded = false;
    reached_by_wait_for = -1.0;
    reached_by = 0;
    pred = 0;
    lowest_trans_cost =QUITE_A_LOT;
}

void LocalProblemNodeDiscrete::on_expand(const TimeStampedState &state) { 
    assert(!expanded);
    assert(cost > -1); //???
    expanded = true;
    // Set children state unless this was an initial node.
    if(reached_by) {
        LocalProblemNode *parent = reached_by->get_source();
        //map<int, double> &changed_facts = parent->changed_facts;
	//changed_facts.clear();
	// fill in changed_fact wrt y0 acrroding to option 1 and 2, and 3!
	int i = reached_by->waiting_nodes.size() - 1;
	switch(g_HACK->transtition_option) {
		case 1:
			i = 0;
			while(reached_by->waiting_nodes[i] == NULL && i < reached_by->waiting_nodes.size()){
				i++;
			}
			assert(i < reached_by->waiting_nodes.size());
			changed_facts = reached_by->waiting_nodes[i]->changed_facts;
			break;
		case 2: 
                        while(reached_by->waiting_nodes[i] == NULL && i >= 0){
				i--;
			}
			assert(i >= 0);
			changed_facts = reached_by->waiting_nodes[i]->changed_facts;
			break;
		case 3:
			changed_facts = parent->changed_facts;
			break;
		default:
			cout << "invalid transition option" << endl;
			exit(1);
	}
	// (1) update context wrt. precondition
    vector<LocalAssignment> &ordered_precond = reached_by->ordered_precond;
    for(int i = 0; i < ordered_precond.size(); i++) 
    	changed_facts[ordered_precond[i].global_var] = ordered_precond[i].value;
    // (2) update context wrt. effect
  	//vector<int>* parent_vars = source->owner->causal_graph_parents;
    const vector<LocalAssignment> &effect = reached_by->label->effect;
    for(int i = 0; i < effect.size(); i++) {
    	//int global_var = parent_vars[effect[i].local_var];
    	if(g_variable_types[effect[i].prev_dtg->var] == logical){
              changed_facts[effect[i].global_var] = effect[i].value;                                          
        }else{
              assert(g_variable_types[effect[i].prev_dtg->var] == primitive_functional);
              //the state[var] fop= state[var']: var' is the parent of var_no, that's label's source->owner->var_no????
              int *parent_vars = &*parent->owner->causal_graph_parents->begin(); 
              const LocalAssignment &la = effect[i];
              updatePrimitiveNumericVariable(la.local_var,la.fop, la.global_var, parent_vars[la.var], changed_facts);      
        }
    	
    }
    // (3) update context wrt. the value transition of this var
    if(&*parent->owner != &*g_HACK->goal_problem) {
    	changed_facts[parent->owner->var_no] = value;
    }
        //children_state = parent->children_state;
//        const vector<LocalAssignment> &prevail = reached_by->label->precond;
//        for(int i = 0; i < prevail.size(); i++) {
//            children_state[prevail[i].local_var] = prevail[i].value;
//        }
//        const vector<LocalAssignment> &cyclic_effects =
//                reached_by->label->effect;
//        for(int i = 0; i < cyclic_effects.size(); i++) {
//            if(g_variable_types[cyclic_effects[i].prev_dtg->var] == logical) {
//                children_state[cyclic_effects[i].local_var]
//                        = cyclic_effects[i].value;
//            } else {
//                assert(g_variable_types[cyclic_effects[i].prev_dtg->var] == primitive_functional);
//                const LocalAssignment &la = cyclic_effects[i];
//                updatePrimitiveNumericVariable(la.fop, la.local_var, la.var,
//                        children_state);
//            }
//        }
        if(parent->reached_by)
            reached_by = parent->reached_by; //why  here
    }
    for(const_it_waiting_list it = waiting_list.begin(); it
            != waiting_list.end(); ++it) {
        it->first->on_ordered_condition_reached(this, it->second);
    }
    waiting_list.clear();
    //print_name();
    for(int i = 0; i < additional_outgoing_transitions.size(); i++) {
        //additional_outgoing_transitions[i].print_description();
        additional_outgoing_transitions[i].on_source_expanded(state);
    }

//    if(additional_outgoing_transitions.size() == 0) {
        for(int i = 0; i < outgoing_transitions.size(); i++) {
            //outgoing_transitions[i].print_description();
            outgoing_transitions[i].on_source_expanded(state);
            //cout<<"-------------"<<endl;
	    //cout << "expanded the transition done " << endl;
        }
//    }
    return;
}

//for order version
double LocalProblemNode::get_context(const int global_var) {
	//assert(global_var != owner->global_var_no);
	// it is possible that a prcondition involves a variable twice in ADL domain
	
	if(!expanded) {return UNDEF * 1.0;}
	
	assert(cost !=QUITE_A_LOT);
	map<int, double>::iterator it = changed_facts.find(global_var);
	if(it != changed_facts.end())
		return it->second;
	else return (*(g_HACK->state))[global_var];
}

//waiting edges are for free....check if all conditions are satiesfied indeed!
bool LocalProblemNode::all_conds_satiesfied(const ValueTransitionLabel *label, const TimeStampedState &state) {
	for(int i = 0; i < label->precond.size(); ++i) {
		int var = label->precond[i].prev_dtg->var;
		if(!double_equals(label->precond[i].value,state[var])) {
//			cout << "at least the cond " << label->precond[i].prev_dtg->var << ":" << label->precond[i].value << " is not sat." << " for " << label->op->get_name() << endl;
			return false;
		}
	}
	return true;
}

void LocalProblemNode::mark_helpful_transitions(const TimeStampedState &state,int& num_loop) {
    if(!this->owner->is_initialized()) {
        //condition was already satiesfied!
        return;
    }
    if(num_loop > 10) return;
    assert(cost >= 0 && cost <QUITE_A_LOT);
    if(reached_by) {
        double duration = 0.0;
        int duration_variable = reached_by->label->duration_variable;
        if(reached_by->label->duration_variable == -2) {
            ScheduledOperator *s_op =
                    dynamic_cast<ScheduledOperator*> (reached_by->label->op);
            assert(s_op);
            duration = s_op->time_increment;
        } else if(!(duration_variable == -1)) {
	    int duration_var_local = reached_by->duration_var_local;
	    int global_duration_var = (*(reached_by->get_source()->owner->causal_graph_parents))[duration_var_local];
            if(reached_by->get_source()->changed_facts.count(global_duration_var) > 0)
		duration = reached_by->get_source()->changed_facts[global_duration_var];
	    else duration = state[global_duration_var];
        }
	//cout<<"duration  "<<duration<<endl;
        if(double_equals(reached_by->target_cost, duration)) {
            assert(reached_by->label);
            // if reached_by->label->op is NULL this means that the transition corresponds to
            // an axiom. Do not add this axiom (or rather a NULL pointer) to the set of
            // preferred operators.
            if(reached_by->label->op && all_conds_satiesfied(reached_by->label,state)) {
                const Operator *op = reached_by->label->op;
                g_HACK->set_preferred(op);
            }
        } else {
            // Recursively compute helpful transitions for prevailed variables.
	    bool flag = g_HACK->is_running(reached_by, state);
            if(!flag) {
            const vector<LocalAssignment> &prevail = reached_by->ordered_precond;
            for(int i = 0; i < prevail.size(); i++) {
                int prev_var_no = prevail[i].global_var;
                int prev_value = static_cast<int> (prevail[i].value);
                int value = reached_by->contexted_start_values[i];
		//if(g_variable_types[prev_var_no] == comparison) cout<<"comparison"<<endl;
		//cout<<"here  "<<prev_var_no<<" "<<prev_value<<"  "<<value<<endl;
                assert(value != UNDEF);
		if(value == UNDEF) continue;//why is there some reached_by->contexted_start_values[i] == -1???? huym
                if(prev_value == value )
                    continue;

//                cout << "prev_var_no: " << prev_var_no << ", prev_value: " << prev_value << ", value: " << value << endl;

                LocalProblemNode *child_node =
                            g_HACK->get_local_problem(prev_var_no,
                                    value)->get_node(prev_value);
                assert(child_node);
                if(!(child_node->cost <QUITE_A_LOT)) {
//                	child_node->print_name();
//                	assert(false);
                }
                if(child_node->cost <QUITE_A_LOT && double_equals(child_node->reached_by_wait_for,-1.0)) {
//                    child_node->print_name();
//                    cout << "child_node->reached_by_wait_for" << child_node->reached_by_wait_for << endl;
//                    cout << "cost: " << child_node->cost << endl;
//                    cout << "reached_by: ";
//                    if(reached_by->label && reached_by->label->op) {
//                        cout << reached_by->label->op->get_name() << endl;
//                    } else {
//                        cout << "axiom" << endl;
//                    }
		    ++num_loop;
                    child_node->mark_helpful_transitions(state,num_loop);
                }
            }
            }
        }
    }
}

void LocalProblemNodeDiscrete::dump() {
    cout << "---------------" << endl;
    print_name();
    cout << "Waiting list:" << endl;
    for(const_it_waiting_list it = waiting_list.begin(); it
            != waiting_list.end(); ++it) {
        cout << " ";
        it->first->print_description();
        cout << "," << it->second << endl;
    }
    cout << "Context:" << endl;
    if(!expanded)
        cout << " not set yet!" << endl;
    else {
        for(int i = 0; i < owner->causal_graph_parents->size(); i++) {
            cout << (*owner->causal_graph_parents)[i] << ": ";
            cout << children_state[i] << endl;
        }
    }
    cout << "cost: " << cost << endl;
    cout << "priority: " << priority() << endl;
    cout << "reached_by: ";
    if(reached_by && reached_by->label && reached_by->label->op) {
        cout << reached_by->label->op->get_name() << endl;
    } else {
        cout << "axiom" << endl;
    }
    cout << "pred: ";
    if(pred && pred->label && pred->label->op) {
        cout << pred->label->op->get_name() << endl;
    } else {
        cout << "axiom" << endl;
    }
    cout << "---------------" << endl;
}

void LocalProblemNodeDiscrete::print_name() {
    cout << "Local Problem Disctret [" << owner->var_no << ","
            << (dynamic_cast<LocalProblemDiscrete*> (owner))->start_value
            << "], node " << value << " (" << this << ")" << endl;
}

void LocalProblemDiscrete::compile_DTG_arcs_to_LTD_objects(
        DomainTransitionGraphSymb *dtgs) {
    for(int value = 0; value < nodes.size(); value++) {
        LocalProblemNodeDiscrete &node = nodes[value];
        node.outgoing_transitions.clear();
        node.additional_outgoing_transitions.clear();
        ValueNode &dtg_node = dtgs->nodes[value];
        for(int i = 0; i < dtg_node.transitions.size(); i++) {
            ValueTransition &dtg_trans = dtg_node.transitions[i];
            int target_value = dtg_trans.target->value;
            LocalProblemNodeDiscrete &target = nodes[target_value];
            for(int j = 0; j < dtg_trans.ccg_labels.size(); j++) {
                ValueTransitionLabel *label = dtg_trans.ccg_labels[j];
                LocalTransitionDiscrete trans(label, &node, &target);
                trans.duration_var_local = getLocalIndexOfGlobalVariable(
                        label->duration_variable);
                assert(trans.duration_var_local != -1 || label->duration_variable == -1 || label->duration_variable == -2);
                node.outgoing_transitions.push_back(trans);
            }
        }
        for(int i = 0; i < dtg_node.additional_transitions.size(); i++) {
            ValueTransition &dtg_trans = dtg_node.additional_transitions[i];
            int target_value = dtg_trans.target->value;
            LocalProblemNodeDiscrete &target = nodes[target_value];
            for(int j = 0; j < dtg_trans.ccg_labels.size(); j++) {
                ValueTransitionLabel *label = dtg_trans.ccg_labels[j];
                LocalTransitionDiscrete trans(label, &node, &target);
                trans.duration_var_local = getLocalIndexOfGlobalVariable(
                        label->duration_variable);
                assert(trans.duration_var_local != -1 || label->duration_variable == -1 || label->duration_variable == -2);
                node.additional_outgoing_transitions.push_back(trans);
            }
        }
    }
}

void LocalProblemDiscrete::build_nodes_for_variable(int var_no) {
    if(!(g_variable_types[var_no] == logical)) {
        //cout << "variable type: " << g_variable_types[var_no] << endl;
        assert(false);
    }
    DomainTransitionGraph *dtg = g_transition_graphs[var_no];
    DomainTransitionGraphSymb *dtgs =
            dynamic_cast<DomainTransitionGraphSymb *> (dtg);
    assert(dtgs);
    causal_graph_parents = &dtg->ccg_parents;
    global_to_local_parents = &dtg->global_to_local_ccg_parents;
    //add var into its parents
    if(global_to_local_parents->count(var_no) < 1){
            int local_var = causal_graph_parents->size();
	    global_to_local_parents->insert(make_pair(var_no,local_var));
            causal_graph_parents->push_back(var_no);
    }
    int num_parents = causal_graph_parents->size();
    for(int value = 0; value < g_variable_domain[var_no]; value++)
        nodes.push_back(LocalProblemNodeDiscrete(this, num_parents, value));
    compile_DTG_arcs_to_LTD_objects(dtgs);
}

void LocalProblemDiscrete::build_nodes_for_goal() {
    // TODO: We have a small memory leak here. Could be fixed by
    // making two LocalProblem classes with a virtual destructor.
    causal_graph_parents = new vector<int> ;
    for(int i = 0; i < g_goal.size(); i++)
        causal_graph_parents->push_back(g_goal[i].first);

    for(int value = 0; value < 2; value++)
        nodes.push_back(LocalProblemNodeDiscrete(this, g_goal.size(), value));

    vector<LocalAssignment> goals;
    for(int i = 0; i < g_goal.size(); i++) {
        int goal_var = g_goal[i].first;
        double goal_value = g_goal[i].second;
        DomainTransitionGraph *goal_dtg = g_transition_graphs[goal_var];
        goals.push_back(LocalAssignment(goal_dtg, i, goal_value, end_cond));
    }
    ValueTransitionLabel *label = new ValueTransitionLabel(-1, goals, end);
    LocalProblemNodeDiscrete *target = &nodes[1];
    LocalProblemNodeDiscrete *start = &nodes[0];
    assert(label);
    LocalTransitionDiscrete trans(label, start, target);

    nodes[0].outgoing_transitions.push_back(trans);
}

LocalProblemDiscrete::LocalProblemDiscrete(int the_var_no, int the_start_val) :
    LocalProblem(the_var_no, the_start_val) {
    if(var_no == -1)
        build_nodes_for_goal();
    else
        build_nodes_for_variable(var_no);
    int parents_num = causal_graph_parents->size();
    nodes[0].children_state.resize(parents_num, 0.0);
    nodes[1].children_state.resize(parents_num, 0.0);

    if(var_no != -1) {
        depending_vars.resize(parents_num);
        children_in_cg.resize(parents_num);
        buildDependingVars(parents_num);
    }
}

void LocalProblemDiscrete::initialize(double base_priority_, int start_value,
        const TimeStampedState &state) {
    assert(!is_initialized());
    base_priority = base_priority_;

    for(int to_value = 0; to_value < nodes.size(); to_value++) {
        nodes[to_value].expanded = false;
        nodes[to_value].cost = QUITE_A_LOT;
	nodes[to_value].lowest_trans_cost = QUITE_A_LOT;
        nodes[to_value].reached_by = NULL;
        nodes[to_value].pred = NULL;
        nodes[to_value].waiting_list.clear();
	nodes[to_value].changed_facts.clear();
        nodes[to_value].reached_by_wait_for = -1.0;
    }
    LocalProblemNodeDiscrete *start = &nodes[start_value];
    start->cost = 0;
    int parents_num = causal_graph_parents->size();
    for(int i = 0; i < parents_num; i++) {
        int var = (*causal_graph_parents)[i];
	start->changed_facts[var] = state[var];
        //start->children_state[i] = state[var];
    }
    g_HACK->add_to_queue(start);
    for(int i = 0; i < state.scheduled_effects.size(); i++) {
        const ScheduledEffect &seffect = state.scheduled_effects[i];
        if(seffect.var == var_no) {
//        	cout << "Scheduled effect: " << seffect.var << ": " << seffect.post << endl;
        	nodes[static_cast<int>(seffect.post)].cost = 0.0;
//        	g_HACK->add_to_queue(&nodes[static_cast<int>(seffect.post)]);
        	assert(seffect.time_increment > 0);
        	assert(seffect.time_increment <QUITE_A_LOT);
                          nodes[static_cast<int>(seffect.post)].reached_by_wait_for = seffect.time_increment;
//        	cout << "Node:" << endl;
//        	nodes[static_cast<int>(seffect.post)].dump();
//        	cout << "xxxxxxxxxxxxx" << endl;
        	for(int i = 0; i < parents_num; i++) {
        	        int var = (*causal_graph_parents)[i];
        	        nodes[static_cast<int>(seffect.post)].changed_facts[var] = state[var];
        	    }

        	nodes[static_cast<int>(seffect.post)].on_expand(state);
        }
    }
}

void LocalProblem::extract_subplan(LocalProblemNode* goalNode,
        string indent, vector<pair<Operator*, double> >& needed_ops, const TimeStampedState& state) {
    LocalProblemNode* startNode = get_node(start_value);
    vector<LocalTransition*> path;
    LocalProblemNode* helpNode = goalNode;
    while(helpNode != startNode && helpNode->pred) {
        path.push_back(helpNode->pred);
        helpNode = helpNode->pred->get_source();
    }
    indent.append(".");
    for(int i = path.size() - 1; i >= 0; --i) {
        LocalTransition* trans = path[i];
        if(!(g_HACK->is_running(trans,state))) {
        const vector<LocalAssignment> &preconds = trans->label->precond;
        for(int j = 0; j < preconds.size(); ++j) {
            double actual_value = trans->get_source()->children_state[preconds[j].local_var];
            if(!(double_equals(actual_value, preconds[j].value))) {
                int var = preconds[j].prev_dtg->var;
		//                cout << indent << "Set " << var << " from " << actual_value
		//      << " to " << preconds[j].value << " (" << preconds[j].cond_type << ")" << endl;
                LocalProblem* sub_problem =
                            g_HACK->get_local_problem(var, static_cast<int>(actual_value));
                sub_problem->extract_subplan(
                            (sub_problem->get_node(static_cast<int>(preconds[j].value))), indent, needed_ops, state);
            }
        }
        }
        if(trans->label->op) {
            Operator *op = trans->label->op;
            double duration = trans->get_direct_cost();
            needed_ops.push_back(make_pair(op,duration));
	  //              cout << indent << trans->label->op->get_name() << ", direct_cost = "
      //              << trans->get_direct_cost() << " (" << trans->lawaiting_nodes[cur_cond_idx] = cond_node;bel->type << "), overall_cost = " << trans->target_cost << endl;
        } else {
	  //            cout << indent << "axiom, direct_cost = " << trans->target_cost << ", overall_cost = " << trans->target_cost << endl;
        }
    }
}

void LocalTransitionComp::print_description() {
    const FuncTransitionLabel *label_func =
            dynamic_cast<const FuncTransitionLabel*> (label);
    assert(label_func);
    cout << "TransitionComp" << "<" << source->owner->var_no << "|" << source->value << "> ("
            << this << "), prevails: ";
    for(int i = 0; i < label->precond.size(); i++) {
        cout
                << (*source->owner->causal_graph_parents)[label->precond[i].local_var]
                << ": " << label->precond[i].value << " ";
    }
    cout << ";   affecting variable: " << label_func->starting_variable << " " << endl;
}

LocalProblemNodeComp::LocalProblemNodeComp(LocalProblemComp *owner_,
        int children_state_size, int the_value, binary_op the_op) :
    LocalProblemNode(owner_, children_state_size), value(the_value), op(the_op) {
    expanded = false;
    opened = false;
    reached_by_wait_for = -1.0;
    reached_by = NULL;
    pred = NULL;
    bestTransition = NULL;
    lowest_trans_cost =QUITE_A_LOT;
}

void LocalProblemNode::add_to_waiting_list(LocalTransition *transition, int prevail_no) {
    waiting_list.push_front(make_pair(transition, prevail_no));
}

void LocalProblemNodeComp::expand(LocalTransitionComp* trans) {
    LocalProblemComp *prob = dynamic_cast<LocalProblemComp*> (owner);
    LocalProblemNodeComp *target_node = &(prob->nodes[1 - prob->start_value]);
    target_node->reached_by = trans;
    target_node->pred = trans;
    target_node->expanded = true;
    expanded = true;
   
    //////////////////////////////////////////////////////
    //call transitions on the own waiting lists
    for(const_it_waiting_list it = target_node->waiting_list.begin(); it
            != target_node->waiting_list.end(); ++it) {
        it->first->on_ordered_condition_reached(target_node, it->second);
    }
    target_node->waiting_list.clear();
}

void LocalProblemNodeComp::fire(LocalTransitionComp* trans) {
    // we have to add the costs of the transition itself!
    trans->target_cost += trans->get_direct_cost();
    if(trans->target_cost < trans->target->cost) {
        trans->target->cost = trans->target_cost;
        trans->target->bestTransition = trans;
        bestTransition = trans;
        trans->target->opened = true;
    }
    //here     
}
//for order version
void LocalTransitionComp::on_ordered_condition_reached(const LocalProblemNode* reach_cond, const int cond_index) {
    if(!source->opened || source->expanded || conds_satiesfied[cond_index] == true) {
        return;
    }
    target_cost += reach_cond->cost;
    assert(conds_satiesfied[cond_index] == false);
    conds_satiesfied[cond_index] == true;
   // if(target->cost <= target_cost)
   // 	return;
     //try_to_fire(); 
     //source->fire(this); //need to be simple 
     for(int i = 0; i < conds_satiesfied.size(); i++)
        if(conds_satiesfied[i] == false)
            return;
      target_cost += get_direct_cost();
      if(target->cost < target_cost){
	target->cost = target_cost;
        target->bestTransition = this;
        source->bestTransition = this;
        target->opened = true;
        g_HACK->add_to_queue(target);
      }
      //update_target_state();
      //cout<<"target in on_condition_reach"<<endl;
}
void LocalTransitionComp::update_target_state(){
    map<int, double>& changed_facts = target->changed_facts;
	changed_facts.clear();
	// fill in changed_fact wrt y0 acrroding to option 1 and 2, and 3!
	int i = waiting_nodes.size() - 1;
	switch(g_HACK->transtition_option) {
		case 1:
			changed_facts = waiting_nodes[0]->changed_facts;
			break;
		case 2: 
                        while(waiting_nodes[i] == NULL){
				i--;
			}
			assert(i >= 0);
			changed_facts = waiting_nodes[i]->changed_facts;
			break;
		case 3:
			changed_facts = source->changed_facts;
			break;
		default:
			cout << "invalid transition option" << endl;
			exit(1);
	}
	// (1) update context wrt. precondition
    for(int i = 0; i < ordered_precond.size(); i++) 
    	changed_facts[ordered_precond[i].global_var] = ordered_precond[i].value;
    // (2) update context wrt. effect
  	//vector<int>* parent_vars = source->owner->causal_graph_parents;
    const vector<LocalAssignment> &effect = label->effect;
    for(int i = 0; i < effect.size(); i++) {
    	//int global_var = parent_vars[effect[i].local_var];
    	if(g_variable_types[effect[i].prev_dtg->var] == logical){
              changed_facts[effect[i].global_var] = effect[i].value;                                          
        }else{
              assert(g_variable_types[effect[i].prev_dtg->var] == primitive_functional);
              //the state[var] fop= state[var']: var' is the parent of var_no, that's label's source->owner->var_no????
              int *parent_vars = &*source->owner->causal_graph_parents->begin(); 
              const LocalAssignment &la = effect[i];
              target->updatePrimitiveNumericVariable(la.local_var,la.fop, la.global_var, parent_vars[la.var],
                        changed_facts);      
        }
    	
    }
    // (3) update context wrt. the value transition of this var
    if(&*source->owner != &*g_HACK->goal_problem) {
    	changed_facts[source->owner->var_no] = target->value;
    } 
}

void LocalProblemNodeComp::on_expand(const TimeStampedState &state) {
    if(opened) {
        if(bestTransition) {
            LocalProblemNodeComp* parent = bestTransition->source;
            parent->expand(bestTransition);
	     //////////////////////////////////////////////////////
    //map<int, double>& changed_facts = target->changed_facts;
	//changed_facts.clear();
	// fill in changed_fact wrt y0 acrroding to option 1 and 2, and 3!
	int i = bestTransition->waiting_nodes.size() - 1;
	switch(g_HACK->transtition_option) {
		case 1:
			i = 0;
			while(bestTransition->waiting_nodes[i] == NULL && i < bestTransition->waiting_nodes.size()){
				i++;
			}
			assert(i < bestTransition->waiting_nodes.size());
			changed_facts = bestTransition->waiting_nodes[i]->changed_facts;
			break;
		case 2: 
                        while(bestTransition->waiting_nodes[i] == NULL){
				i--;
			}
			assert(i >= 0);
			changed_facts = bestTransition->waiting_nodes[i]->changed_facts;
			break;
		case 3:
			changed_facts = parent->changed_facts;
			break;
		default:
			cout << "invalid transition option" << endl;
			exit(1);
	}
	// (1) update context wrt. precondition
    vector<LocalAssignment> &ordered_precond = bestTransition->ordered_precond;
    for(int i = 0; i < ordered_precond.size(); i++) 
    	changed_facts[ordered_precond[i].global_var] = ordered_precond[i].value;
    // (2) update context wrt. effect
  	//vector<int>* parent_vars = source->owner->causal_graph_parents;
    const vector<LocalAssignment> &effect = bestTransition->label->effect;
    for(int i = 0; i < effect.size(); i++) {
    	//int global_var = parent_vars[effect[i].local_var];
    	if(g_variable_types[effect[i].prev_dtg->var] == logical){
              changed_facts[effect[i].global_var] = effect[i].value;                                          
        }else{
              assert(g_variable_types[effect[i].prev_dtg->var] == primitive_functional);
              //the state[var] fop= state[var']: var' is the parent of var_no, that's label's source->owner->var_no????
              int *parent_vars = &*parent->owner->causal_graph_parents->begin(); 
              const LocalAssignment &la = effect[i];
              updatePrimitiveNumericVariable(la.local_var,la.fop, la.global_var, parent_vars[la.var],
                        changed_facts);      
        }
    	
    }
    // (3) update context wrt. the value transition of this var
    if(&*parent->owner != &*g_HACK->goal_problem) {
    	changed_facts[parent->owner->var_no] = value;
    } 
        }
        return;
    }
    opened = true;
    //print_name();
    vector<LocalTransitionComp*> ready_transitions;
    nodes_where_this_subscribe.resize(outgoing_transitions.size());
    //vector<double> temp_children_state(children_state.size());
    for(int i = 0; i < outgoing_transitions.size(); i++) {
        LocalTransitionComp *trans = &outgoing_transitions[i];
        map<int, double> temp_children_state = changed_facts;
        //temp_children_state = children_state;
        updateNumericVariables((*trans), temp_children_state);
        if(check_progress_of_transition(temp_children_state, trans)) {
            if(is_satiesfied(i, trans, state)) {
                ready_transitions.push_back(trans);
            } else if(g_HACK->is_running(trans, state)) {
//           	cout << "Simply wait for " << trans->label->op->get_name() << endl;
                ready_transitions.push_back(trans);
            }
        }
    }
    if(!ready_transitions.empty()) {
        for(int i = 0; i < ready_transitions.size(); ++i) {
            fire(ready_transitions[i]);
        }
        assert(bestTransition);
        assert(bestTransition->target);
        g_HACK->add_to_queue(bestTransition->target);
	//cout<<"target is in"<<endl;
    }
    //subscribe_to_waiting_lists();
    return;
}

bool LocalProblemNodeComp::check_progress_of_transition(
	 map<int, double> &temp_children_state, LocalTransitionComp *trans) {
    int var = (*(owner->causal_graph_parents))[0];
    double old_value = changed_facts.count(var) > 0 ? changed_facts[var] : (*(g_HACK->state))[var];
    double new_value = temp_children_state.count(var) > 0 ? temp_children_state[var] : (*(g_HACK->state))[var];
    LocalProblemNodeComp *node = dynamic_cast<LocalProblemNodeComp*>(trans->get_source());
    assert(node);
    binary_op comp_op = node->op;
    switch (comp_op) {
    case lt:
    case le:
      return new_value < old_value;
    case gt:
    case ge:
      return new_value > old_value;
    case eq:
      return abs(new_value) < abs(old_value);
    case ue:
      return !(double_equals(new_value,0));
    default:
      return false;
    }
}

void LocalTransitionComp::on_condition_reached(int cond_no, double cost) {
    if(!source->opened || source->expanded || conds_satiesfied[cond_no] == true) {
        return;
    }
    target_cost += cost;
    assert(conds_satiesfied[cond_no] == false);
    conds_satiesfied[cond_no] = true;
    for(int i = 0; i < conds_satiesfied.size(); i++)
        if(conds_satiesfied[i] == false)
            return;
	// we have to add the costs of the transition itself!
    target_cost += get_direct_cost();
   	target->cost = target_cost;
   	target->bestTransition = this;
   	source->bestTransition = this;
   	target->opened = true;
   	g_HACK->add_to_queue(target);
        //cout<<"target is later in"<<endl;
	//update_target_state();
}

bool PCHeuristic::is_running(LocalTransition* trans, const TimeStampedState& state) {
	if(!trans->label || !trans->label->op)
		return false;
	for(int i = 0; i < state.operators.size(); ++i) {
	  //cout<<state.operators[i].get_name()<<"   "<<trans->label->op->get_name()<<endl;
	  if(!(state.operators[i].get_name().compare(trans->label->op->get_name()))) {
//			cout << "Running operator: " << state.operators[i].get_name() << endl;
                    g_HACK->set_waiting_time(max(g_HACK->get_waiting_time(),state.operators[i].time_increment - EPS_TIME));
//                    cout << "wait for " << state.operators[i].get_name() << "....waiting_time: " << g_HACK->get_waiting_time() << endl;
		    return true;
		}
	}
	return false;
}

bool LocalProblemNodeComp::is_satiesfied(int trans_index,
        LocalTransitionComp* trans, const TimeStampedState &state) {
    bool ret = true;
     //for com variable, we need to choose the best transition in all the transition
     //so, it don't need to use order
    const vector<LocalAssignment> &precond = trans->label->precond;
    trans->ordered_precond.clear();
    //vector<LocalAssignment> com_precond;
    //vector<LocalAssignment> lg_precond;
    set<pair<int,double> > facts;
    for(int i = 0; i < precond.size(); i++) {
         // note: the index of variable in the ordered_precond are 
    	 // all converted to their global index here
    	 int global_var = (*(owner->causal_graph_parents))[precond[i].local_var];
    	 double value = precond[i].value;
    	 pair<int,double> fact = make_pair(global_var, value);
    	 //cout<<"precond "<<global_var<<"  "<<value<<endl;	 
    	 if(!facts.count(fact)) { // if the fact is not included
		//if(g_variable_types[global_var] == logical) 
                    trans->ordered_precond.push_back(LocalAssignment(trans->label->precond[i].prev_dtg, global_var, 
                                                         trans->label->precond[i].local_var,value));
		//else com_precond.push_back(LocalAssignment(trans->label->precond[i].prev_dtg, global_var, 
                                                        // trans->label->precond[i].local_var,value));
    		facts.insert(fact);
    	}
    }
    //trans->num_lg = lg_precond.size();
    //lg_precond.insert(lg_precond.end(), com_precond.begin(), com_precond.end());
    //trans->ordered_precond.assign(lg_precond.begin(), lg_precond.end());
    trans->precede_idx.resize(trans->ordered_precond.size(), -1);
    trans->waiting_nodes.resize(trans->precede_idx.size());
    trans->contexted_start_values.resize(trans->precede_idx.size());
    trans->unreached_conditions = 0;
    for(int i = 0; i < trans->waiting_nodes.size(); i++) {
	 trans->waiting_nodes[i] = NULL;
	 trans->contexted_start_values[i] = -1;	
    }
    vector<LocalAssignment>::const_iterator
    						curr_precond = trans->ordered_precond.begin(),
    						last_precond = trans->ordered_precond.end();
    //vector<vector<LocalProblem *> > &problem_index = g_HACK->local_problem_index;
		int cur_cond_idx = 0;
  	assert(trans->precede_idx[cur_cond_idx] == UNDEF);
    for(; curr_precond != last_precond; ++curr_precond, ++cur_cond_idx) {
	
        //const LocalAssignment &pre_cond = trans->ordered_precond[i];
        // check whether the cost of this prevail has already been computed
        int global_var = curr_precond->global_var;
        assert(!is_functional(global_var));
        double current_val = trans->get_start_value(global_var, trans->precede_idx[cur_cond_idx]);
        const int start_val = static_cast<int>(current_val);
        //if(start_val == UNDEF) cout << start_val<<" is_saties "<<trans->precede_idx[cur_cond_idx]<<cur_cond_idx << "  " <<endl;
	if(start_val == UNDEF) {ret = false; continue;}
	int prev_value = static_cast<int>(curr_precond->value);
        trans->contexted_start_values[cur_cond_idx] = start_val;
        if(g_variable_types[global_var] == comparison && double_equals(current_val, curr_precond->value)) {
            // to change nothing costs nothing
            assert(trans->conds_satiesfied[cur_cond_idx] == false);
            trans->conds_satiesfied[cur_cond_idx] = true;
            continue;
        }
        LocalProblem *child_problem = g_HACK->get_local_problem(global_var,
                start_val);
        if(!child_problem->is_initialized()) {
            double base_priority = priority();
            child_problem->initialize(0, start_val, state);
        }
	//cout<<"ordered_precond "<<global_var<<"  "<<prev_value<<endl;
        LocalProblemNode *cond_node = child_problem->get_node(prev_value);
	trans->waiting_nodes[cur_cond_idx] = cond_node;
//        cond_node->print_name();
//        cout << endl;
        if(!double_equals(cond_node->reached_by_wait_for,-1.0)) {
            g_HACK->set_waiting_time(max(g_HACK->get_waiting_time(),cond_node->reached_by_wait_for - EPS_TIME));
//            cout << "cond_node....waiting_time: " << g_HACK->get_waiting_time() << endl;
            assert(trans->target_cost <QUITE_A_LOT);
        	assert(trans->conds_satiesfied[cur_cond_idx] == false);
        	trans->conds_satiesfied[cur_cond_idx] = true;
        } else if(cond_node->expanded) {
            trans->target_cost = trans->target_cost + cond_node->cost;
            assert(trans->conds_satiesfied[cur_cond_idx] == false);
            trans->conds_satiesfied[cur_cond_idx] = true;
        } else {
            //nodes_where_this_subscribe[trans_index].push_back(make_pair(
            //        cond_node, cur_cond_idx));
	    cond_node->add_to_waiting_list(trans, cur_cond_idx);
            ++(trans->unreached_conditions);
            //the cost of this prevail has not been determined so far...
            ret = false;
        }
    }
    return ret;
}

bool LocalProblemNodeComp::is_directly_satiesfied(
        const LocalAssignment &pre_cond) {
    if(double_equals(children_state[pre_cond.local_var], pre_cond.value))
        return true;
    return false;
}

void LocalProblemNodeComp::subscribe_to_waiting_lists() {
    for(int i = 0; i < nodes_where_this_subscribe.size(); i++) {
        for(int j = 0; j < nodes_where_this_subscribe[i].size(); j++) {
	    
            LocalProblemNode *prob =
                    nodes_where_this_subscribe[i][j].first;
            int prevail_no = nodes_where_this_subscribe[i][j].second;
            prob->add_to_waiting_list(&(outgoing_transitions[i]), prevail_no);
        }
    }
}

void LocalProblemNodeComp::updateNumericVariables(LocalTransitionComp &trans,
        map<int, double> &temp_children_state) {
    const FuncTransitionLabel* label_func =
            dynamic_cast<const FuncTransitionLabel*> (trans.label);
    assert(label_func);
    int primitive_var_local = label_func->starting_variable;
    int primitive_var_global = (*owner->causal_graph_parents)[primitive_var_local];
    assert(g_variable_types[primitive_var_global] == primitive_functional);
    //int influencing_var_local = label_func->influencing_variable;
    int influencing_var_global = (*owner->causal_graph_parents)[label_func->influencing_variable];
    assert(is_functional(influencing_var_global));
    assignment_op a_op = label_func->a_op;
    updatePrimitiveNumericVariable(primitive_var_local, a_op, primitive_var_global,
            influencing_var_global, temp_children_state);
}

void LocalProblemNode::updatePrimitiveNumericVariable(const int local_var, const assignment_op a_op,
        const int primitive_var_global, int influencing_var_global,
        map<int, double> &temp_children_state) {
    //double &new_value = temp_children_state[primitive_var_local];
    double new_value = 0.0;
    if(temp_children_state.count(primitive_var_global) > 0){
         new_value = temp_children_state[primitive_var_global];                                                 
    }else{
         new_value = (*(g_HACK->state))[primitive_var_global];    
    }
    //double &influencing_value = temp_children_state[influencing_var_local];
    double influencing_value = 0.0;
    if(temp_children_state.count(influencing_var_global) > 0){
         influencing_value = temp_children_state[influencing_var_global];                                                 
    }else{
         influencing_value = (*(g_HACK->state))[influencing_var_global];      
    }
    switch (a_op) {
    case assign:
        new_value = influencing_value;
        break;
    case scale_up:
        new_value *= influencing_value;
        break;
    case scale_down:
        if(double_equals(influencing_value, 0.0)) {
            if(new_value < 0)
                new_value = REALLYBIG;
            else
                new_value = REALLYSMALL;
        } else
            new_value /= influencing_value;
        break;
    case increase:
        new_value += influencing_value;
        break;
    case decrease:
        new_value -= influencing_value;
        break;
    default:
        assert(false);
        break;
    }
    temp_children_state[primitive_var_global] = new_value;
    updateNumericVariablesRec(local_var, temp_children_state);
}

void LocalProblemNode::updateNumericVariablesRec(const int local_var,
        map<int, double> &temp_children_state) {
    for(int i = 0; i < owner->depending_vars[local_var].size(); i++) {
        int var_to_update = owner->depending_vars[local_var][i];
        if(!(owner->children_in_cg[var_to_update].size() == 3)) {
            //	    cout << "owner->children_in_cg[var_to_update].size(): " << owner->children_in_cg[var_to_update].size() << endl;
            //	    assert(false);
            continue;
        }
        binary_op
                bop =
                        static_cast<binary_op> (owner->children_in_cg[var_to_update][2]);
        int global_var = (*(owner->causal_graph_parents))[var_to_update];
        //int left_var = (g_transition_graphs[global_var]->ccg_parents)[owner->children_in_cg[var_to_update][0]];
        //int right_var =(g_transition_graphs[global_var]->ccg_parents)[owner->children_in_cg[var_to_update][1]];
	int left_var = 0, right_var = 0;
	DomainTransitionGraph *dtg = g_transition_graphs[global_var];
        if(g_variable_types[global_var]== subterm_functional) {
            //here
            DomainTransitionGraphSubterm *dtgs = dynamic_cast<DomainTransitionGraphSubterm*>(dtg);
	    left_var = dtgs->left_var;
	    right_var = dtgs->right_var;
            updateSubtermNumericVariables(var_to_update,global_var , bop, left_var,
                    right_var, temp_children_state);
        } else {
            assert(g_variable_types[global_var] == comparison);
            //here
	    DomainTransitionGraphComp *dtgc = dynamic_cast<DomainTransitionGraphComp*>(dtg);
	    left_var = dtgc->nodes.first.left_var;
            right_var = dtgc->nodes.first.left_var;
            updateComparisonVariables(var_to_update, global_var, bop, left_var, right_var,
                    temp_children_state);
        }
    }
}

int LocalProblem::getLocalIndexOfGlobalVariable(int global_var) {
    hashmap::const_iterator iter;
    iter = global_to_local_parents->find(global_var);
    if(iter == global_to_local_parents->end())
        return -1;
    return (*iter).second;
}

void LocalProblemNode::updateComparisonVariables(int local_var, int var, binary_op op,
        int left_var, int right_var,map<int, double> &temp_children_state) {
    double left = temp_children_state.count(left_var) > 0 ? temp_children_state[left_var] : (*(g_HACK->state))[left_var];
    double right = temp_children_state.count(right_var) > 0 ? temp_children_state[right_var] : (*(g_HACK->state))[right_var];
    double target = 0;
    switch (op) {
    case lt:
        if(left + EPSILON < right) {
            target = 0;
        } else {
            target = 1;
        }
        break;
    case le:
        if(left + EPSILON < right || double_equals(left, right)) {
            target = 0;
        } else {
            target = 1;
        }
        break;
    case eq:
        if(double_equals(left, right)) {
            target = 0;
        } else {
            target = 1;
        }
        break;
    case gt:
        if(left + EPSILON > right) {
            target = 0;
        } else {
            target = 1;
        }
        break;
    case ge:
        if(left + EPSILON > right || !double_equals(left, right)) {
            target = 0;
        } else {
            target = 1;
        }
        break;
    case ue:
        if(!double_equals(left, right)) {
            target = 0;
        } else {
            target = 1;
        }

    default:
        assert(false);
        break;
    }
    temp_children_state[var] = target;
    updateNumericVariablesRec(local_var, temp_children_state);
}

void LocalProblemNode::updateSubtermNumericVariables(int& local_var, int var, binary_op op,
        int left_var, int right_var, map<int, double> &temp_children_state) {
    double left = temp_children_state.count(left_var) > 0 ? temp_children_state[left_var] : (*(g_HACK->state))[left_var];
    double right = temp_children_state.count(right_var) > 0 ? temp_children_state[right_var] : (*(g_HACK->state))[right_var];
    double target = 0;
    switch (op) {
    case add:
        target = left + right;
        break;
    case subtract:
        target = left - right;
        break;
    case mult:
        target = left * right;
        break;
    case divis:
        if(double_equals(right, 0.0)) {
            if(left < 0)
                target = REALLYBIG;
            else
                target = REALLYSMALL;
        } else
            target = left / right;
        break;
    default:
        assert(false);
        break;
    }
    temp_children_state[var] = target;
    updateNumericVariablesRec(local_var, temp_children_state);
}

void LocalProblemNodeComp::dump() {
    cout << "---------------" << endl;
    print_name();
    cout << "Waiting list:" << endl;
    for(const_it_waiting_list it = waiting_list.begin(); it
            != waiting_list.end(); ++it) {
        cout << " ";
        it->first->print_description();
        cout << "," << it->second << endl;
    }
    cout << "Context:" << endl;
    if(!opened)
        cout << " not set yet!" << endl;
    else {
        for(int i = 0; i < owner->causal_graph_parents->size(); i++) {
            cout << (*owner->causal_graph_parents)[i] << ": ";
            cout << children_state[i] << endl;
        }
    }
    cout << "cost: " << cost << endl;
    cout << "priority: " << priority() << endl;
    cout << "---------------" << endl;
}

void LocalProblemNodeComp::print_name() {
    cout << "Local Problem comp [" << owner->var_no << ","
            << (dynamic_cast<LocalProblemComp*> (owner))->start_value
            << "], node " << value << " (" << this << ")" << endl;
}

void LocalProblem::buildDependingVars(int parents_num) {
    for(int i = 0; i < parents_num; i++) {
        int context_variable = (*causal_graph_parents)[i];
        const vector<int>& current_depending_vars =
                g_causal_graph->get_successors(context_variable);
        for(int j = 0; j < current_depending_vars.size(); j++) {
            int current_depending_var = current_depending_vars[j];
            if(g_variable_types[current_depending_var] == comparison
                    || g_variable_types[current_depending_var]
                            == subterm_functional) {
                int idx = getLocalIndexOfGlobalVariable(current_depending_var);
                if(idx != -1)
                    depending_vars[i].push_back(idx);
            }
        }
        if(g_variable_types[context_variable] == subterm_functional) {
            DomainTransitionGraph *dtg = g_transition_graphs[context_variable];
            DomainTransitionGraphSubterm *dtgs =
                    dynamic_cast<DomainTransitionGraphSubterm*> (dtg);
            assert(dtgs);
            int left_var = getLocalIndexOfGlobalVariable(dtgs->left_var);
            int right_var =
                    getLocalIndexOfGlobalVariable(dtgs->right_var);
            if(left_var != -1 && right_var != -1) {
                assert(children_in_cg[i].size() == 0);
                children_in_cg[i].push_back(left_var);
                children_in_cg[i].push_back(right_var);
                children_in_cg[i].push_back(dtgs->op);
            }
        } else if(g_variable_types[context_variable] == comparison) {
            DomainTransitionGraph *dtg = g_transition_graphs[context_variable];
            DomainTransitionGraphComp *dtgc =
                    dynamic_cast<DomainTransitionGraphComp*> (dtg);
            assert(dtgc);
            int left_var = getLocalIndexOfGlobalVariable(
                    dtgc->nodes.first.left_var);
            int right_var = getLocalIndexOfGlobalVariable(
                    dtgc->nodes.first.right_var);
            if(left_var != -1 && right_var != -1) {
                assert(children_in_cg[i].size() == 0);
                children_in_cg[i].push_back(left_var);
                children_in_cg[i].push_back(right_var);
                children_in_cg[i].push_back(dtgc->nodes.first.op);
            }
        }
    }
}

LocalProblemComp::LocalProblemComp(int the_var_no, int the_start_value) :
    LocalProblem(the_var_no, the_start_value) {
    assert(var_no >= 0);
    build_nodes_for_variable(var_no, the_start_value);

    int parents_num = causal_graph_parents->size();
    nodes[start_value].children_state.resize(parents_num, 0.0);

    depending_vars.resize(parents_num);
    children_in_cg.resize(parents_num);
    buildDependingVars(parents_num);
}

void LocalProblemComp::build_nodes_for_variable(int var_no, int the_start_value) {
    if(!(g_variable_types[var_no] == comparison)) {
        assert(false);
    }
    DomainTransitionGraph *dtg = g_transition_graphs[var_no];
    DomainTransitionGraphComp *dtgc =
            dynamic_cast<DomainTransitionGraphComp *> (dtg);
    assert(dtgc);

    causal_graph_parents = &dtgc->ccg_parents;
    global_to_local_parents = &dtgc->global_to_local_ccg_parents;
    //add the var into its parents
    if(global_to_local_parents->count(var_no) < 1){
            int local_var = causal_graph_parents->size();
            global_to_local_parents->insert(make_pair(var_no, local_var));
            causal_graph_parents->push_back(var_no);
    }
    int num_parents = causal_graph_parents->size();

    assert(g_variable_domain[var_no] == 3);
    // There are 3 values for a comp variable: false, true and undefined. In the heuristic we only have
    // to deal with the first both of them.
    nodes.push_back(LocalProblemNodeComp(this, num_parents, 0, dtgc->nodes.second.op));
    nodes.push_back(LocalProblemNodeComp(this, num_parents, 1, dtgc->nodes.first.op));

    // Compile the DTG arcs into LocalTransition objects.
    for(int i = 0; i < dtgc->transitions.size(); i++) {
        LocalTransitionComp trans(&(dtgc->transitions[i]),
                &(nodes[the_start_value]), &(nodes[1-the_start_value]));
        //variables in func_transitions of comp nodes are local!!!!
        trans.duration_var_local = dtgc->transitions[i].duration_variable;
        nodes[the_start_value].outgoing_transitions.push_back(trans);
    }
}

void LocalProblemComp::initialize(double base_priority_, int start_value,
        const TimeStampedState &state) {

    //cout << "--------------------------------------" << endl << endl;
    //cout << "build Comp node" << endl;
    //cout << "--------------------------------------" << endl << endl; 
    assert(start_value == this->start_value);

    int target_value = abs(start_value - 1);

    assert(!is_initialized());
    base_priority = base_priority_;

    assert(nodes.size() == 2);

    for(int to_value = 0; to_value < nodes.size(); to_value++) {
        nodes[to_value].expanded = false;
        nodes[to_value].opened = false;
        nodes[to_value].reached_by = NULL;
        nodes[to_value].pred = NULL;
        nodes[to_value].waiting_list.clear();
        nodes[to_value].nodes_where_this_subscribe.clear();
        nodes[to_value].bestTransition = NULL;
        nodes[to_value].reached_by_wait_for = -1.0;
	nodes[to_value].changed_facts.clear();
        nodes[to_value].lowest_trans_cost = QUITE_A_LOT;
    }

    nodes[start_value].cost = 0;
    nodes[target_value].cost = QUITE_A_LOT;

    for(int i = 0; i < nodes[start_value].outgoing_transitions.size(); i++) {
        LocalTransitionComp &trans = nodes[start_value].outgoing_transitions[i];
        trans.target_cost = 0;
        for(int j = 0; j < trans.label->precond.size(); j++) {
            trans.conds_satiesfied[j] = false;
        }
    }

    int parents_num = causal_graph_parents->size();
    for(int i = 0; i < parents_num; i++) {
        int var = (*causal_graph_parents)[i];
        nodes[start_value].changed_facts[var] = state[var];
    }



 //   for(int i = 0; i < state.scheduled_effects.size(); i++) {
 //       const ScheduledEffect &seffect = state.scheduled_effects[i];
 //       if(seffect.var == var_no) {
 //       	cout << "Scheduled effect: " << seffect.var << ": " << seffect.post << endl;
 //       	nodes[static_cast<int>(seffect.post)].cost = 0.0;
 //       	g_HACK->add_to_queue(&nodes[static_cast<int>(seffect.post)]);
 //       	assert(seffect.time_increment > 0);
 //       	assert(seffect.time_increment <QUITE_A_LOT);
 //       	nodes[static_cast<int>(seffect.post)].reached_by_wait_for = seffect.time_increment;
 //       }
 //   }

    g_HACK->add_to_queue(&nodes[start_value]);
}

PCHeuristic::PCHeuristic(int trans_option):
  transtition_option(trans_option) {
    assert(!g_HACK);
    g_HACK = this;
    goal_problem = 0;
    //transtition_option = trans_option;
    goal_node = 0;
}

PCHeuristic::~PCHeuristic() {
    delete goal_problem;
    for(int i = 0; i < local_problems.size(); i++)
        delete local_problems[i];
    g_HACK->state = NULL;
}

void PCHeuristic::initialize() {
    assert(goal_problem == 0);
   // cout << "Initializing cyclic causal graph heuristic...";

    int num_variables = g_variable_domain.size();

    goal_problem = new LocalProblemDiscrete(-1, 0);
    goal_node = &goal_problem->nodes[1];

    local_problem_index.resize(num_variables);
    for(int var_no = 0; var_no < num_variables; var_no++) {
        int num_values = g_variable_domain[var_no];
        if(num_values == -1) {
            //we don't need local problems for functional variables so far....
            assert(g_variable_types[var_no] == subterm_functional || g_variable_types[var_no] == primitive_functional);
        } else {
            local_problem_index[var_no].resize(num_values, NULL);
        }
    }
   // cout << "done." << endl;
}

void PCHeuristic::build_transitions_for_running_ops(
        const TimeStampedState &state) {
    for(int i = 0; i < state.scheduled_effects.size(); i++) {
        const ScheduledEffect &seffect = state.scheduled_effects[i];
        assert(g_variable_types[seffect.var] == logical || g_variable_types[seffect.var] == primitive_functional);
        DomainTransitionGraph *dtg = g_transition_graphs[seffect.var];
        if(g_variable_types[seffect.var] == logical) {
            DomainTransitionGraphSymb *dtgs =
                    dynamic_cast<DomainTransitionGraphSymb*> (dtg);
            assert(dtgs);
            vector<ValueNode> &nodes = dtgs->nodes;

            vector<int> start_values;

            if(seffect.pre == -1) {
                for(int j = 0; j < g_variable_domain[seffect.var]; ++j) {
                    if(j != seffect.post)
                        start_values.push_back(j);
                }
            } else {
                start_values.push_back(static_cast<int>(seffect.pre));
            }
            int target_value = nodes[static_cast<int>(seffect.post)].value;
            for(int j = 0; j < start_values.size(); ++j) {
                int source_value = start_values[j];
                //TODO: when to delete?
                ScheduledOperator *waiting_op = new ScheduledOperator(
                        seffect.time_increment - EPS_TIME);
                generated_waiting_ops.push_back(waiting_op);
                //TODO: when to delete?
                ValueTransitionLabel *label = new ValueTransitionLabel(-2,
                        vector<LocalAssignment> (), end, vector<LocalAssignment> (),
                        waiting_op);
                //cout << "new label: " << label << endl;
                generated_labels.push_back(label);
                ValueTransition *trans = new ValueTransition(
                        &nodes[target_value]);
                trans->ccg_labels.push_back(label);
                //cout << "Adding trans for " << seffect.var << " from " << source_value << " to " << seffect.post << endl;
                nodes[source_value].additional_transitions.push_back(*trans);
                dtg_nodes_with_an_additional_transition.push_back(
                        &nodes[source_value]);
                //cout << "pushed_back on : " << dtg_nodes_with_an_additional_transition.back() << endl;
                for(int k = 0; k < local_problem_index[seffect.var].size(); ++k) {
                    if(local_problem_index[seffect.var][k]) {
                        LocalProblem *problem =
                                local_problem_index[seffect.var][k];
                        LocalProblemDiscrete *problem_discrete =
                                dynamic_cast<LocalProblemDiscrete*> (problem);
                        assert(problem_discrete);
                        problem_discrete->nodes[source_value].additional_outgoing_transitions.push_back(
                                LocalTransitionDiscrete(label,
                                        &(problem_discrete->nodes[source_value]),
                                        &(problem_discrete->nodes[target_value])));
                        nodes_with_an_additional_transition.push_back(
                                &(problem_discrete->nodes[source_value]));
                        //                        problem_discrete->compile_DTG_arcs_to_LTD_objects(dtgs);

                    }
                }
            }
        }
    }
}

void PCHeuristic::remove_transitions_for_running_ops(
        const TimeStampedState &/*state*/) {
    for(int i = 0; i < dtg_nodes_with_an_additional_transition.size(); ++i) {
        ValueNode* node = dtg_nodes_with_an_additional_transition[i];
//        int effect_var = node->parent_graph->var;
        node->additional_transitions.clear();
//        DomainTransitionGraph *dtg = node->parent_graph;
//        DomainTransitionGraphSymb *dtgs =
//                dynamic_cast<DomainTransitionGraphSymb*> (dtg);
//        assert(dtgs);
//        for(int k = 0; k < local_problem_index[effect_var].size(); ++k) {
//            if(local_problem_index[effect_var][k]) {
//                //since we only created additional transitions for discrete effects,
//                //we are sure that we deal with an LocalProblemDiscrete at this point.
//                LocalProblem *problem = local_problem_index[effect_var][k];
//                LocalProblemDiscrete *problem_discrete =
//                        dynamic_cast<LocalProblemDiscrete*> (problem);
//                problem_discrete->compile_DTG_arcs_to_LTD_objects(dtgs);
//            }
//        }
    }
    for(int i = 0; i < nodes_with_an_additional_transition.size(); ++i) {
        LocalProblemNodeDiscrete* node = nodes_with_an_additional_transition[i];
        node->additional_outgoing_transitions.clear();
    }
    dtg_nodes_with_an_additional_transition.clear();
    nodes_with_an_additional_transition.clear();
}

double PCHeuristic::compute_heuristic(const TimeStampedState &state) {
    if(state.satisfies(g_goal) && state.operators.empty())
        return 0.0;
//    build_transitions_for_running_ops(state);
    initialize_queue();
    set_waiting_time(REALLYSMALL);
    goal_problem->base_priority = -1;
    for(int i = 0; i < local_problems.size(); i++)
        local_problems[i]->base_priority = -1;

    goal_problem->initialize(0.0, 0, state);
    g_HACK->state = &state;

    //cout << "----------------------------------" <<endl;
    //cout << "start the compute of state" <<endl;
    double heuristic = compute_costs(state);
    //cout << "end the compute of state:  " << heuristic << endl;
   // exit(1);
   // cout << "----------------------------------" <<endl;
    double alternative_heuristic = 0.0;

    if(heuristic != DEAD_END && heuristic != 0) {
	int num_loop = 0;
        goal_node->mark_helpful_transitions(state,num_loop);
//        cout << "Extracting subplan..." << endl;
//        vector<pair<Operator*,double> > needed_ops;
//        goal_problem->extract_subplan(goal_node,"", needed_ops, state);
//        cout << "Vanila ops:" << endl;
//        for(int i = 0; i < needed_ops.size(); ++i) {
//            cout << needed_ops[i].first->get_name() << ", duration: " << needed_ops[i].second << endl;
//        }
//        sort(needed_ops.begin(), needed_ops.end());
//        needed_ops.erase(unique(needed_ops.begin(), needed_ops.end()),
//                needed_ops.end());
//        for(int i = 0; i < needed_ops.size(); ++i) {
//            alternative_heuristic += needed_ops[i].second;
//        }
////        cout << "Unique ops:" << endl;
//        for(int i = 0; i < needed_ops.size(); ++i) {
//            cout << needed_ops[i].first->get_name() << ", duration: " << needed_ops[i].second << endl;
//        }
//        cout << "Subplan extracted!" << endl;

    }

    if(!state.operators.empty() && (heuristic == 0.0)) {
        heuristic += 1.0;
        alternative_heuristic += 1.0;
    }

//    remove_transitions_for_running_ops(state);

//    cout << "h: " << heuristic << endl;
//    cout << "waiting_time: " << g_HACK->get_waiting_time() << endl;

    double waiting_time = g_HACK->get_waiting_time();
    if(!(double_equals(heuristic,-1.0)) && (waiting_time - EPSILON > 0.0)) {
        heuristic += waiting_time;
        alternative_heuristic += waiting_time;
    }

//    cout << "Final h: " << heuristic << endl;
//    cout << "alternative h: " << alternative_heuristic << endl;

    if(double_equals(heuristic,-1.0)) {
        alternative_heuristic = -1.0;
    }

//    if(double_equals(heuristic,-1.0)) {
//        state.dump();
//    } else {
//        state.dump();
//    }

    return heuristic;
//    return alternative_heuristic;
}

void PCHeuristic::initialize_queue() {
    open_nodes = node_queue();
}

void PCHeuristic::add_to_queue(LocalProblemNode *node) {
//    cout << "add to queue:" << endl;
//    node->dump();
    open_nodes.push(node);
}

LocalProblemNode* PCHeuristic::remove_from_queue() {
    LocalProblemNode* ret = open_nodes.top();
    open_nodes.pop();
    return ret;
}

double PCHeuristic::compute_costs(const TimeStampedState &state) {
    while(!open_nodes.empty()) {
        LocalProblemNode *node = remove_from_queue();
        if(node == goal_node)
            return node->cost;
        if(!(node->expanded)) {
            //cout << "Next node: ";
            //node->print_name();
	    //cout<<open_nodes.size()<<endl;
            node->on_expand(state);
        }
	//node->print_name();f
    }
		/*for(int i = 0;i < g_goal.size(); ++i){
			int var = g_goal[i].first;
			int g_value = static_cast<int>(g_goal[i].second);
			double s_value = state[var];
			LocalProblem *child_problem = g_HACK->get_local_problem(var, static_cast<int>(s_value));
                        if(!child_problem->is_initialized()){
                           LocalProblemNode *cond_node = child_problem->get_node(g_value);
			   if(cond_node->expanded) cout << "local cost" << cond_node->cost<<endl;
			}else cout << "it's not expand" << endl;
  		}*/
    return DEAD_END;
}
