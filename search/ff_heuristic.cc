/*********************************************************************
 * Author: Malte Helmert (helmert@informatik.uni-freiburg.de)
 * (C) Copyright 2003-2004 Malte Helmert
 * Modified by: Silvia Richter (silvia.richter@nicta.com.au),
 *              Matthias Westphal (westpham@informatik.uni-freiburg.de)             
 * (C) Copyright 2008 NICTA and Matthias Westphal
 *
 * This file is part of LAMA.
 *
 * LAMA is free software; you can redistribute it and/or
 * modify it under the terms of the GNU General Public License
 * as published by the Free Software Foundation; either version 3
 * of the license, or (at your option) any later version.
 *
 * LAMA is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program; if not, see <http://www.gnu.org/licenses/>.
 *
 *********************************************************************/

#include "ff_heuristic.h"
#include "globals.h"
#include "operator.h"
#include "state.h"

#include <cassert>

using namespace std;
using namespace __gnu_cxx;

// Construction and destruction
FFHeuristic::FFHeuristic(bool use_cache)
        : Heuristic(use_cache) {
   // cout << "Initializing HSP/FF heuristic..." << endl;

    // Build propositions.
    for(int var = 0; var < g_variable_domain.size(); var++) {
   	if(g_variable_types[var] == logical){
               // cout << var << "  " << g_variable_domain[var] << endl;;
		propositions.push_back(vector<Proposition>(g_variable_domain[var]));
        	for(int val = 0; val < g_variable_domain[var]; val++) {
           		 propositions[var][val].var = var;
           		 propositions[var][val].val = val;
			 propositions[var][val].precondition_of.resize(0);
        	}	
  	}else propositions.push_back(vector<Proposition>(0));
    }

    // Build goal propositions.
    //cout << "before goal_proposition" << endl;
    for(int i = 0; i < g_goal.size(); i++) {
        int var = g_goal[i].first, val = (int)(g_goal[i].second);
	if(g_variable_types[var] != logical) continue;
        propositions[var][val].is_goal_condition = true;
        propositions[var][val].is_termination_condition = true;
        goal_propositions.push_back(&propositions[var][val]);
        termination_propositions.push_back(&propositions[var][val]);
    }
    //cout << "after goal_proposition" << endl;
    // Build unary operators for operators and axioms.
    for(int i = 0; i < g_simpleoperators.size(); i++)
        build_unary_operators(g_simpleoperators[i]);
    //cout << "after build_unary_operators" << endl;
    // Simplify unary operators.
    simplify();
   // cout << "simplify" << endl;
    // Cross-reference unary operators.
    for(int i = 0; i < unary_operators.size(); i++) {
        UnaryOperator *op = &unary_operators[i];
        for(int j = 0; j < op->precondition.size(); j++)
            op->precondition[j]->precondition_of.push_back(op);
    }
    // Set flag that before heuristic values can be used, computation
    // (relaxed exploration) needs to be done
    heuristic_recomputation_needed = true;
}

FFHeuristic::~FFHeuristic() {}

void FFHeuristic::set_additional_goals(const std::vector<pair<int, int> >& add_goals) {
    //Clear previous additional goals.
    for(int i = 0; i < termination_propositions.size(); i++) {
        int var = termination_propositions[i]->var, val = termination_propositions[i]->val;
        propositions[var][val].is_termination_condition = false;
    }
    termination_propositions.clear();
    for(int i = 0; i < g_goal.size(); i++) {
        int var = g_goal[i].first, val = (int)(g_goal[i].second);
        propositions[var][val].is_termination_condition = true;
        termination_propositions.push_back(&propositions[var][val]);
    }
    // Build new additional goal propositions.
    for(int i = 0; i < add_goals.size(); i++) {
        int var = add_goals[i].first, val = add_goals[i].second;
        if(!propositions[var][val].is_goal_condition) {
            propositions[var][val].is_termination_condition = true;
            termination_propositions.push_back(&propositions[var][val]);
        }
    }
    heuristic_recomputation_needed = true;
}

void FFHeuristic::build_unary_operators(const SimpleOperator &op) {
    // Note: changed from the original to allow sorting of operator conditions
    int base_cost = op.is_axiom() ? 0 : 1;


    if(g_use_metric)
        base_cost = op.get_cost();


    const vector<Prevail> &prevail = op.get_prevail();
    const vector<PrePost> &pre_post = op.get_pre_post();
    vector<Proposition *> precondition;
    vector<pair<int,int> > precondition_var_vals1;

    for(int i = 0; i < prevail.size(); i++) {
        if(double_equals(prevail[i].prev, -1) || g_variable_types[prevail[i].var] != logical) continue;
        assert(prevail[i].var >= 0 && prevail[i].var < g_variable_domain.size());
        assert(prevail[i].prev >= 0 && prevail[i].prev < g_variable_domain[prevail[i].var]);
        // precondition.push_back(&propositions[prevail[i].var][prevail[i].prev]);
        precondition_var_vals1.push_back(make_pair(prevail[i].var, (int)(prevail[i].prev)));
        //cout << "the prevail: " << prevail[i].var << "  " << prevail[i].prev;
        //if(g_variable_types[prevail[i].var] == logical) cout << "logical" << endl;
       // else cout << endl;
    }
    for(int i = 0; i < pre_post.size(); i++)
        if(!double_equals(pre_post[i].pre, -1) && g_variable_types[pre_post[i].var] == logical) {
            assert(pre_post[i].var >= 0 && pre_post[i].var < g_variable_domain.size());
            assert(pre_post[i].pre >= 0.0 && pre_post[i].pre < g_variable_domain[pre_post[i].var]);
            // precondition.push_back(&propositions[pre_post[i].var][pre_post[i].pre]);
            precondition_var_vals1.push_back(make_pair(pre_post[i].var, (int)(pre_post[i].pre)));
           // cout << "the prepost: " << pre_post[i].var << "  " << pre_post[i].pre << endl;
        }
    for(int i = 0; i < pre_post.size(); i++) {
        if(g_variable_types[pre_post[i].var] != logical) continue;
        vector<pair<int,int> > precondition_var_vals2(precondition_var_vals1);
        assert(pre_post[i].var >= 0 && pre_post[i].var < g_variable_domain.size());
        assert(pre_post[i].post >= 0.0 && pre_post[i].post < g_variable_domain[pre_post[i].var]);
        Proposition *effect = &propositions[pre_post[i].var][(int)(pre_post[i].post)];
        //cout << "the post:  "<< pre_post[i].var << pre_post[i].post << endl;
        const vector<Prevail> &eff_cond = pre_post[i].cond;
        for(int j = 0; j < eff_cond.size(); j++) {
            assert(eff_cond[j].var >= 0 && eff_cond[j].var < g_variable_domain.size());
            assert(eff_cond[j].prev >= 0.0 && eff_cond[j].prev < g_variable_domain[eff_cond[j].var]);
            // precondition.push_back(&propositions[eff_cond[j].var][eff_cond[j].prev]);
              if(g_variable_types[eff_cond[j].var] == logical)
              precondition_var_vals2.push_back(make_pair(eff_cond[j].var, (int)(eff_cond[j].prev)));
             // cout << "effect prevail: " << eff_cond[j].var << " " << eff_cond[j].prev << endl;
        }

        sort(precondition_var_vals2.begin(), precondition_var_vals2.end());

        for(int j = 0; j < precondition_var_vals2.size(); j++){
            //cout << "check the index" << precondition_var_vals2[j].first << "  " << precondition_var_vals2[j].second << endl;
            precondition.push_back(&propositions[precondition_var_vals2[j].first]
                                   [precondition_var_vals2[j].second]);
        }
        unary_operators.push_back(UnaryOperator(precondition, effect, &op, base_cost));
        // precondition.erase(precondition.end() - eff_cond.size(), precondition.end());
        precondition.clear();
        precondition_var_vals2.clear();
    }
}

class hash_unary_operator {
public:
    size_t operator()(const pair<vector<Proposition *>, Proposition *> &key) const {
        unsigned long hash_value = reinterpret_cast<unsigned long>(key.second);
        const vector<Proposition *> &vec = key.first;
        for(int i = 0; i < vec.size(); i++)
            hash_value = 17 * hash_value + reinterpret_cast<unsigned long>(vec[i]);
        return size_t(hash_value);
    }
};

void FFHeuristic::simplify() {
    // Remove duplicate or dominated unary operators.

    /*
      Algorithm: Put all unary operators into a hash_map
      (key: condition and effect; value: index in operator vector.
      This gets rid of operators with identical conditions.

      Then go through the hash_map, checking for each element if
      none of the possible dominators are part of the hash_map.
      Put the element into the new operator vector iff this is the case.
    */


   // cout << "Simplifying " << unary_operators.size() << " unary operators..." << flush;

    typedef pair<vector<Proposition *>, Proposition *> HashKey;
    typedef hash_map<HashKey, int, hash_unary_operator> HashMap;
    HashMap unary_operator_index;
    unary_operator_index.resize(unary_operators.size() * 2);
    for(int i = 0; i < unary_operators.size(); i++) {
        UnaryOperator &op = unary_operators[i];
        // sort(op.precondition.begin(), op.precondition.end());
        HashKey key(op.precondition, op.effect);
        unary_operator_index[key] = i;
        /*cout << "uop  " << i << "  is " <<op.precondition.size() << endl;
        for(int j = 0;j < op.precondition.size(); ++j){
                if(g_variable_types[op.precondition[j]->var] != logical)
			cout<<"it's not logical"<<endl;
		cout << op.precondition[j]->var << "  " << op.precondition[j]->val << endl;
        }
	if(g_variable_types[op.effect->var] != logical) 
 		cout<<"it's not logical"<<endl;
		
        cout << "its effect is : " << op.effect->var << "  " << op.effect->val << endl;*/
    }

    vector<UnaryOperator> old_unary_operators;
    old_unary_operators.swap(unary_operators);

    for(HashMap::iterator it = unary_operator_index.begin();
            it != unary_operator_index.end(); ++it) {
        const HashKey &key = it->first;
        int unary_operator_no = it->second;
        int powerset_size = (1 << key.first.size()) - 1; // -1: only consider proper subsets
        bool match = false;
        if(powerset_size <= 31) { // HACK! Don't spend too much time here...
            for(int mask = 0; mask < powerset_size; mask++) {
                HashKey dominating_key = make_pair(vector<Proposition *>(), key.second);
                for(int i = 0; i < key.first.size(); i++)
                    if(mask & (1 << i))
                        dominating_key.first.push_back(key.first[i]);
                if(unary_operator_index.count(dominating_key)) {
                    match = true;
                    break;
                }
            }
        }
        if(!match)
            unary_operators.push_back(old_unary_operators[unary_operator_no]);
    }
    sort(unary_operators.begin(), unary_operators.end());
   // cout << " done! [" << unary_operators.size() << " unary operators]" << endl;
}

// heuristic computation
void FFHeuristic::setup_exploration_queue(const TimeStampedState &state,
        const vector<pair<int, int> >& excluded_props,
        const hash_set<const SimpleOperator *,
        hash_operator_ptr>& excluded_ops,
        bool use_h_max = false) {
    reachable_queue.clear();
    for(int var = 0; var < propositions.size(); var++) {
        for(int value = 0; value < propositions[var].size(); value++) {
            Proposition &prop = propositions[var][value];
            //cout<<"proposition:  "<<var << "   "<< value<<endl;
	   // cout<<"it's refer unary_op size  "<<prop.precondition_of.size()<<endl;
            prop.h_add_cost = -1;
            prop.h_max_cost = -1;
            prop.depth = -1;
        }
    }
    if(excluded_props.size() > 0) {
        for(unsigned i = 0; i < excluded_props.size(); i++) {
	    //cout<<"i   "<<i<<endl;
            Proposition &prop = propositions[excluded_props[i].first][excluded_props[i].second];
            prop.h_add_cost = -2;
        }
    }
    // Deal with current state.
    for(int var = 0; var < propositions.size(); var++) {
	if(g_variable_types[var] != logical) continue;
        Proposition *init_prop = &propositions[var][(int)(state[var])];
        enqueue_if_necessary(init_prop, 0, 0, 0, use_h_max);
    }
    // Initialize operator data, deal with precondition-free operators/axioms.
    for(int i = 0; i < unary_operators.size(); i++) {
        UnaryOperator &op = unary_operators[i];
        op.unsatisfied_preconditions = op.precondition.size();
        if(excluded_ops.size() > 0 && (op.effect->h_add_cost == -2 ||
                                       excluded_ops.find(op.op) != excluded_ops.end())) {
            op.h_add_cost = -2; // operator will not be applied during relaxed exploration
            continue;
        }
        op.h_add_cost = op.base_cost; // will be increased by precondition costs
        op.h_max_cost = op.base_cost;
        op.depth = -1;

        if(op.unsatisfied_preconditions == 0) {
            op.depth = 0;
            int depth = op.op->is_axiom() ? 0 : 1;
            enqueue_if_necessary(op.effect, op.base_cost, depth, &op, use_h_max);
        }
    }
}

void FFHeuristic::relaxed_exploration(bool use_h_max = false, bool level_out = false) {
    int unsolved_goals = termination_propositions.size();
    for(int distance = 0; distance < reachable_queue.size(); distance++) {
        for(;;) {
            Bucket &bucket = reachable_queue[distance];
            // NOTE: Cannot set "bucket" outside the loop because the
            //       reference can change if reachable_queue is
            //       resized.
            if(bucket.empty())
                break;
            Proposition *prop = bucket.back();
            bucket.pop_back();
            int prop_cost;
            if(use_h_max)
                prop_cost = prop->h_max_cost;
            else
                prop_cost = prop->h_add_cost;
            assert(prop_cost <= distance);
            if(prop_cost < distance)
                continue;
            if(!level_out && prop->is_termination_condition && --unsolved_goals == 0)
                return;
            const vector<UnaryOperator *> &triggered_operators = prop->precondition_of;
            //cout<<"bucket prop  "<<prop->var<<"  "<<prop->val<<endl;
	    //cout<<"its op's size() "<<triggered_operators.size()<<endl;
            //if(prop->var ==8 && prop->val == 3) cout<<"---------------------"<<endl;
            for(int i = 0; i < triggered_operators.size(); i++) {
	       // cout<<"just in  "<<i<<endl;
                UnaryOperator *unary_op = triggered_operators[i];
		//why there is some unary_op is wrong indicator, where is it changed??,huym
		if(unary_op < &unary_operators[0] || unary_op > &unary_operators[unary_operators.size()-1]) continue;
		//cout<<"get unary_op ok"<<endl;
                //cout<<unary_op->precondition.size()<<"  it's the size"<<endl;
		//cout<<"unary_op->h_add_cost  "<<unary_op->h_add_cost<<endl;
		/*if(prop->var ==8 && prop->val == 3){
			cout<<"begin"<<unary_op<<endl;
			cout<<unary_op->effect->var<<"  "<<unary_op->effect->val<<endl;
			cout<<"unary_op->h_add_cost"<<unary_op->h_add_cost<<endl;
			cout<<"unary_op->unsatisfied_preconditions "<<unary_op->unsatisfied_preconditions<<endl;
			cout<<"done"<<endl;
                } */
                                         
                if(unary_op->h_add_cost == -2) // operator is not applied
                    continue;
                unary_op->unsatisfied_preconditions--;
		//cout<<"unary_op->unsatisfied "<<unary_op->unsatisfied_preconditions<<endl;
                unary_op->h_add_cost += prop_cost;
		//cout<<"unary_op->h_add_cost "<<unary_op->h_add_cost<<endl;
                unary_op->h_max_cost = max(prop_cost + unary_op->base_cost,
                                           unary_op->h_max_cost);
		//cout<<"unary_op->h_max_cost  "<<unary_op->h_max_cost<<endl;
                unary_op->depth = max(unary_op->depth, prop->depth);
		//cout<<"unary_op->depth   "<<unary_op->depth<<endl;
                assert(unary_op->unsatisfied_preconditions >= 0);
		//cout<<"in a while"<<endl;
                if(unary_op->unsatisfied_preconditions == 0) {
                    int depth = unary_op->op->is_axiom() ? unary_op->depth : unary_op->depth + 1;
                    if(use_h_max)
                        enqueue_if_necessary(unary_op->effect, unary_op->h_max_cost,
                                             depth, unary_op, use_h_max);
                    else
                        enqueue_if_necessary(unary_op->effect, unary_op->h_add_cost,
                                             depth, unary_op, use_h_max);
                }
            }
	    //if(prop->var ==8 && prop->val == 3) cout<<"---------------------"<<endl;
        }
    }
}

void FFHeuristic::enqueue_if_necessary(Proposition *prop, int cost, int depth,
                                       UnaryOperator *op,
                                       bool use_h_max) {
    assert(cost >= 0);
    if(use_h_max && (prop->h_max_cost == -1 || prop->h_max_cost > cost)) {
        prop->h_max_cost = cost;
        prop->depth = depth;
        prop->reached_by = op;
        if(cost >= reachable_queue.size())
            reachable_queue.resize(cost + 1);
        reachable_queue[cost].push_back(prop);
    } else if(!use_h_max && (prop->h_add_cost == -1 || prop->h_add_cost > cost)) {
        prop->h_add_cost = cost;
        prop->depth = depth;
        prop->reached_by = op;
        if(cost >= reachable_queue.size())
            reachable_queue.resize(cost + 1);
        reachable_queue[cost].push_back(prop);
    }
    if(use_h_max)
        assert(prop->h_max_cost != -1 &&
               prop->h_max_cost <= cost);
    else
        assert(prop->h_add_cost != -1 &&
               prop->h_add_cost <= cost);
}


int FFHeuristic::compute_hsp_add_heuristic() {
    int total_cost = 0;
    for(int i = 0; i < goal_propositions.size(); i++) {
        int prop_cost = goal_propositions[i]->h_add_cost;
        if(prop_cost == -1)
            return DEAD_END;
        total_cost += prop_cost;
    }
    return total_cost;
}

int FFHeuristic::compute_hsp_max_heuristic() {
    /* Note: this function is currently not used */
    int maximal_cost = 0;
    for(int i = 0; i < goal_propositions.size(); i++) {
        int prop_cost = goal_propositions[i]->h_max_cost;
        if(prop_cost == -1)
            return DEAD_END;
        maximal_cost = max(maximal_cost, prop_cost);
    }
    return maximal_cost;
}

int FFHeuristic::get_lower_bound(const TimeStampedState &state) {
    /* Note: this function is currently not used */
    prepare_heuristic_computation(state, true);
    int h = compute_hsp_max_heuristic();
    heuristic_recomputation_needed = true;
    return h;
}


int FFHeuristic::compute_ff_heuristic(const TimeStampedState &state) {
    int h_add_heuristic = compute_hsp_add_heuristic();
    if(h_add_heuristic == DEAD_END) {
        return DEAD_END;
    } else {
        RelaxedPlan relaxed_plan;
        relaxed_plan.resize(2 * h_add_heuristic);
        // Collecting the relaxed plan also marks helpful actions as preferred.
        for(int i = 0; i < goal_propositions.size(); i++)
            collect_relaxed_plan(goal_propositions[i], relaxed_plan, state);
        assert(!g_use_metric);
        if(!g_use_metric)
            return relaxed_plan.size();
        else {
            int cost = 0;
            RelaxedPlan::iterator it = relaxed_plan.begin();
            for(; it != relaxed_plan.end(); ++it)
                cost += (*it)->get_cost();
            return cost;
        }
    }
}

void FFHeuristic::collect_relaxed_plan(Proposition *goal,
                                       RelaxedPlan &relaxed_plan, const TimeStampedState &state) {

    UnaryOperator *unary_op = goal->reached_by;
    if(unary_op) { // We have not yet chained back to a start node.
        for(int i = 0; i < unary_op->precondition.size(); i++)
            collect_relaxed_plan(unary_op->precondition[i], relaxed_plan, state);
        
        const SimpleOperator *op = unary_op->op;
        bool added_to_relaxed_plan = false;
        if(!op->is_axiom())
            added_to_relaxed_plan = relaxed_plan.insert(op).second;

        assert(unary_op->depth != -1);
        if(added_to_relaxed_plan
                && unary_op->h_add_cost == unary_op->base_cost
                && unary_op->depth == 0
                && !op->is_axiom()) {
            
            set_ff_preferred(op);
            if(!op->is_applicable(state)) {
            	state.dump();
            	op->dump();
            	cout << unary_op->h_add_cost << endl;
            	cout << "precond depth " << endl;
            	for(int i = 0; i < unary_op->precondition.size(); i++) {
            		cout << unary_op->precondition[i]->depth << endl;
            		int var = unary_op->precondition[i]->var;
            		int val = unary_op->precondition[i]->val;
            		cout << g_variable_name[var] << "," << val << endl;
            	}
            	cout << flush;
            	
            }
            assert(op->is_applicable(state));
        }
    }
}

void FFHeuristic::
compute_reachability_with_excludes(vector<vector<int> >& lvl_var,
                                   vector<map<pair<int, int>, int> >& lvl_op,
                                   bool level_out,
                                   const vector<pair<int, int> >& excluded_props,
                                   const hash_set<const SimpleOperator*, hash_operator_ptr>& excluded_ops,
                                   bool compute_lvl_ops) {

    // Perform exploration using h_max-values
    setup_exploration_queue(*g_initial_state, excluded_props, excluded_ops, true);
    relaxed_exploration(true, level_out);
    // Copy reachability information into lvl_var and lvl_op
    for(int var = 0; var < propositions.size(); var++) {
        for(int value = 0; value < propositions[var].size(); value++) {
            Proposition &prop = propositions[var][value];
            if(prop.h_max_cost >= 0)
                lvl_var[var][value] = prop.h_max_cost;
        }
    }
    if(compute_lvl_ops) {
        hash_map< const SimpleOperator *, int, hash_operator_ptr> operator_index;
        for(int i = 0; i < g_simpleoperators.size(); i++) {
            operator_index.insert(make_pair(&g_simpleoperators[i], i));
        }
        for(int i = 0; i < unary_operators.size(); i++) {
            UnaryOperator &op = unary_operators[i];
            // H_max_cost of operator might be wrongly 0 or 1, if the operator
            // did not get applied during relaxed exploration. Look through
            // preconditions and adjust.
            for(int i = 0; i < op.precondition.size(); i++) {
                Proposition* prop = op.precondition[i];
                if(prop->h_max_cost == -1) {
                    // Operator cannot be applied due to unreached precondition
                    op.h_max_cost = INT_MAX;
                    break;
                } else if(op.h_max_cost < prop->h_max_cost + op.base_cost)
                    op.h_max_cost = prop->h_max_cost + op.base_cost;
            }
            if(op.h_max_cost == INT_MAX)
                break;
            int op_index = operator_index[op.op];
            // We subtract 1 to keep semantics for landmark code:
            // if op can achieve prop at time step i+1,
            // its index (for prop) is i, where the initial state is time step 0.
            pair<int, int> effect = make_pair(op.effect->var, op.effect->val);
            assert(lvl_op[op_index].find(effect) != lvl_op[op_index].end());
            int new_lvl = op.h_max_cost - 1;
            // If we have found a cheaper achieving operator, adjust h_max cost of proposition.
            if(lvl_op[op_index].find(effect)->second > new_lvl)
                lvl_op[op_index].find(effect)->second = new_lvl;
        }
    }
    heuristic_recomputation_needed = true;
}

void FFHeuristic::prepare_heuristic_computation(const TimeStampedState& state, bool h_max = false) {
    setup_exploration_queue(state, h_max);
    relaxed_exploration(h_max);
    heuristic_recomputation_needed = false;
}

double FFHeuristic::compute_heuristic(const TimeStampedState &state) {
	//assert(heuristic_recomputation_needed);
    //if(heuristic_recomputation_needed) {
        prepare_heuristic_computation(state);
    //}
    return (double)compute_ff_heuristic(state);
}


void FFHeuristic::collect_ha(Proposition *goal,
                             RelaxedPlan &relaxed_plan, const TimeStampedState &state) {

    // This is the same as collect_relaxed_plan, except that preferred operators
    // are saved in exported_ops rather than preferred_operators

    UnaryOperator *unary_op = goal->reached_by;
    if(unary_op) { // We have not yet chained back to a start node.
        for(int i = 0; i < unary_op->precondition.size(); i++)
            collect_ha(unary_op->precondition[i], relaxed_plan, state);
        const SimpleOperator *op = unary_op->op;
        bool added_to_relaxed_plan = false;
        if(!op->is_axiom())
            added_to_relaxed_plan = relaxed_plan.insert(op).second;
        if(added_to_relaxed_plan
                && unary_op->h_add_cost == unary_op->base_cost
                && unary_op->depth == 0
                && !op->is_axiom()) {
            exported_ops.push_back(op); // This is a helpful action.
            assert(op->is_applicable(state));
        }
    }
}

bool is_landmark(vector<pair<int, int> >& landmarks, int var, int val) {
    // TODO: change landmarks to set or hash_set
    for(int i = 0; i < landmarks.size(); i++)
        if(landmarks[i].first == var && landmarks[i].second == val)
            return true;
    return false;
}

int FFHeuristic::plan_for_disj(vector<pair<int, int> >& landmarks,
                               const TimeStampedState& state) {
    RelaxedPlan relaxed_plan;
    // generate plan to reach part of disj. goal OR if no landmarks given, plan to real goal
    if(!landmarks.empty()) {
        // search for quickest achievable landmark leaves
        if(heuristic_recomputation_needed) {
            prepare_heuristic_computation(state);
        }
        int min_cost = INT_MAX;
        Proposition *target = NULL;
        for(int i = 0; i < termination_propositions.size(); i++) {
            const int prop_cost = termination_propositions[i]->h_add_cost;
            if(prop_cost == -1 && is_landmark(landmarks, termination_propositions[i]->var,
                                              termination_propositions[i]->val)) { // DEAD_END
                return DEAD_END;
            }
            if(prop_cost < min_cost && is_landmark(landmarks, termination_propositions[i]->var,
                                                   termination_propositions[i]->val)) {
                target = termination_propositions[i];
                min_cost = prop_cost;
            }
        }
        assert(target != NULL);
        relaxed_plan.resize(2 * min_cost);
        assert(exported_ops.size() == 0);
        collect_ha(target, relaxed_plan, state);
    } else {
        // search for original goals of the task
        if(heuristic_recomputation_needed) {
            prepare_heuristic_computation(state);
        }
        for(int i = 0; i < goal_propositions.size(); i++) {
            if(goal_propositions[i]->h_add_cost == -1)
                return DEAD_END;
            collect_ha(goal_propositions[i], relaxed_plan, state);
        }
    }
    return relaxed_plan.size();
}

void FFHeuristic::set_ff_preferred(const SimpleOperator* op){
         if(!op->is_marked()) {
                 op->mark();
                 ff_preferred_operators.push_back(op);
         }
}
