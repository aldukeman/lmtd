#ifndef CYCLIC_CG_HEURISTIC_H
#define CYCLIC_CG_HEURISTIC_H

#include <vector>
#include <queue>
#include <tr1/unordered_map>
#include "heuristic.h"
#include "state.h"
#include "domain_transition_graph.h"
#include <ext/slist>
#include <cmath>

using namespace std;
class FuncTransitionLabel;
class TimeStampedState;

class LocalProblemDiscrete;
class LocalProblemComp;
class LocalProblemNodeDiscrete;
class LocalProblemNodeComp;
class LocalProblemNode;
class PCHeuristic;
class LocalProblem;
class LocalTransitionComp;
class LocalTransitionDiscrete;
class LocalTransition;
class Node_compare;

typedef priority_queue<LocalProblemNode*, std::vector<LocalProblemNode*>,
        Node_compare> node_queue;

typedef __gnu_cxx ::slist<std::pair<LocalTransition*, int> > waiting_list_t;
typedef waiting_list_t::const_iterator const_it_waiting_list;
typedef waiting_list_t::iterator it_waiting_list;

typedef std::tr1::unordered_map<int, int> hashmap;
typedef hashmap::value_type ValuePair;

const int UNDEF = -1;
const double QUITE_A_LOT = 1000000.0;

//*****************************************************
//general classes
//*****************************************************
class LocalTransition {
public:
    double target_cost;
    double lower_bound;
    int duration_var_local;
    const ValueTransitionLabel *label;
    virtual LocalProblemNode* get_source() = 0;
    virtual void on_condition_reached(int, double) = 0;
    virtual void print_description() = 0;

    //for ordered condition, huym 10-08-22
    bool condition_ordered;
    vector<LocalAssignment> ordered_precond;
    int num_lg; // the munber of logical precondition
    vector<int> precede_idx;
    // precede_idx[i] = j means 
    // precond[j] is ordered before precond[i] by our ordering rules 
    vector<LocalProblemNode *>  waiting_nodes;
    // each condition has a corresponding end node.
    // if precede_idx[i] = j, then we can fetch in the context info of precond[j] 
    // a new start value for precond[i] 
    // (j < i should be guarrenteed!).
    int unreached_conditions;
    vector<int> contexted_start_values; // helpfull transition??????
    // NOTE: this is for helpful actions extraction. If ctx(q) = p, then
    // in the state_of_p when p is achieved, state_of_p(var(q)) != state[var(q)]
    // may exist, due to the precedence constraints. We should reflect this
    // when collecting helpuful actions!
    void apply_before_order(vector<LocalAssignment> &precond);
    virtual double get_start_value(const int precond_var, const int preced_cond_idx) = 0;
    //for the order version, its function is similar with on_condition_reached,huym 10-08-24
    //triggered when the cost of condition[index] of this transition is fixed
    virtual void on_ordered_condition_reached(const LocalProblemNode* reach_cond, int index) = 0;
    virtual void update_target_state() = 0;
    
    /////////////////////////////////////////////////

    LocalTransition(ValueTransitionLabel *the_label) :
        label(the_label) , condition_ordered(false){
    }
    virtual ~LocalTransition() {
    }
    double get_direct_cost();

};

class LocalProblemNode {
public:
    // Static attributes
    LocalProblem *owner;

    std::vector<double> children_state;
    
    LocalTransition *reached_by;

    LocalTransition *pred;
    
    double lowest_trans_cost;
    // Dynamic attributes (modified during heuristic computation).
    double cost;
    inline double priority() const;
    bool expanded;
    double reached_by_wait_for;
    virtual void dump() {
    }

    virtual void on_expand(const TimeStampedState &state) = 0;

    waiting_list_t waiting_list;

    void updatePrimitiveNumericVariable(const int local_var, const assignment_op a_op,
         const int primitive_var_global, int influencing_var_global, map<int, double> &temp_children_state);
    void
            updateNumericVariablesRec(const int local_var,
                    map<int, double> &temp_children_state);
                    ///////////////
    void updateSubtermNumericVariables(int& local_var,int var, binary_op op, int left_var,
            int right_var, map<int, double> &temp_children_state);
            /////////////////
    void updateComparisonVariables(int local_var, int var, binary_op op, int left_var,
            int right_var, map<int, double> &temp_children_state);

    bool all_conds_satiesfied(const ValueTransitionLabel *label, const TimeStampedState &state);
    void mark_helpful_transitions(const TimeStampedState &state,int& num_loop);
    virtual ~LocalProblemNode() {
    }
    LocalProblemNode(LocalProblem* owner, int children_state_size) :
        owner(owner) {
        children_state.resize(children_state_size, 0.0);
        cost = -1.0;
        changed_facts.clear();
    }
    void add_to_waiting_list(LocalTransition *transition, int start_val);
    virtual void print_name() = 0;
    //for order version
    map<int, double> changed_facts;
    double get_context(const int global_var);
};

class LocalProblem {
public:
    double base_priority;
    const int var_no;
    vector<int> *causal_graph_parents;
    const int start_value;
    virtual LocalProblemNode* get_node(int var_no) = 0;
    hashmap *global_to_local_parents;
    vector<vector<int> > depending_vars;
    vector<vector<int> > children_in_cg;
    int getLocalIndexOfGlobalVariable(int global_var);
    void buildDependingVars(int parents_num);
    void extract_subplan(LocalProblemNode* goalNode, string indent, vector<pair<Operator*, double> >& needed_ops, const TimeStampedState& state);
    virtual ~LocalProblem() {
    }
    virtual void initialize(double base_priority, int start_value,
            const TimeStampedState &state) = 0;
    inline bool is_initialized() const;
    LocalProblem(int the_var_no, int the_start_value);
};

//*****************************************************
//discrete variables
//*****************************************************
class LocalProblemNodeDiscrete: public LocalProblemNode {
public:

    // Static attributes (fixed upon initialization).
    std::vector<LocalTransitionDiscrete> outgoing_transitions;
    std::vector<LocalTransitionDiscrete> additional_outgoing_transitions;

    int value;

    LocalProblemNodeDiscrete(LocalProblemDiscrete *owner,
            int children_state_size, int value);
    virtual void on_expand(const TimeStampedState &state);
    void dump();
    void print_name();
};

class LocalTransitionDiscrete: public LocalTransition {
public:

    LocalProblemNodeDiscrete *source;
    LocalProblemNodeDiscrete *target;

    LocalProblemNodeDiscrete* get_source() {
        return source;
    }

    

    LocalTransitionDiscrete(ValueTransitionLabel *the_label,
            LocalProblemNodeDiscrete *the_source,
            LocalProblemNodeDiscrete *the_target) :
        LocalTransition(the_label), source(the_source), target(the_target) {
		condition_ordered = false;
    }

    void on_source_expanded(const TimeStampedState &state);
    virtual void on_condition_reached(int cond_no, double cost);
    void try_to_fire();
    virtual void print_description();
    /////////////////////////////////////////////////////////////////////////
    //for order version
    virtual void on_ordered_condition_reached(const LocalProblemNode* reach_cond, int index);
    virtual void update_target_state();
    virtual double get_start_value(const int precond_var, const int preced_cond_idx);
};

class LocalProblemDiscrete: public LocalProblem {
public:

    std::vector<LocalProblemNodeDiscrete> nodes;
    virtual LocalProblemNodeDiscrete* get_node(int var_no) {
        return &(nodes[var_no]);
    }

    void build_nodes_for_variable(int var_no);
    void build_nodes_for_goal();
    void compile_DTG_arcs_to_LTD_objects(DomainTransitionGraphSymb *dtgs);
    LocalProblemDiscrete(int var_no, int start_val);
    virtual ~LocalProblemDiscrete(){
        // if(var_no == -1){
	//	delete causal_graph_parents;
 	// } 
    }
    virtual void initialize(double base_priority, int start_value,
            const TimeStampedState &state);
};

//*****************************************************
//comparison case
//*****************************************************
class LocalProblemNodeComp: public LocalProblemNode {
public:

    std::vector<LocalTransitionComp> outgoing_transitions;

    vector<vector<pair<LocalProblemNode*, int> > >
            nodes_where_this_subscribe;

    int value;

    binary_op op;

    bool opened;
    LocalTransitionComp* bestTransition;

    LocalProblemNodeComp(LocalProblemComp *owner_, int children_state_size,
            int the_value, binary_op the_binary_op);
    void fire(LocalTransitionComp* trans);
    virtual void on_expand(const TimeStampedState &state);
    void expand(LocalTransitionComp* trans);
    bool is_satiesfied(int trans_index, LocalTransitionComp* trans,
            const TimeStampedState &state);
    bool is_directly_satiesfied(const LocalAssignment &pre_cond);
    void subscribe_to_waiting_lists();
    //void updateNumericVariables(LocalTransitionComp &trans,
     //       vector<double> &temp_children_state);
     //for order verssion
     void updateNumericVariables(LocalTransitionComp &trans,
            map<int, double> &temp_children_state);
    bool check_progress_of_transition(map<int, double> &temp_children_state, LocalTransitionComp *trans);
    void dump();
    void print_name();
};

class LocalTransitionComp: public LocalTransition {
public:

    LocalProblemNodeComp* source;

    LocalProblemNodeComp* target;

    LocalProblemNodeComp* get_source() {
        return source;
    }

    vector<bool> conds_satiesfied;

    LocalTransitionComp(FuncTransitionLabel *the_label,
            LocalProblemNodeComp *the_source, LocalProblemNodeComp *the_target) :
        LocalTransition(the_label), source(the_source), target(the_target){
		 condition_ordered = false; 
        target_cost = 0.0;
        //TODO: is this necessary?
        conds_satiesfied.resize(label->precond.size());
    }

    virtual void on_condition_reached(int cond_no, double cost);
    virtual void print_description();
    //for order version
    virtual void on_ordered_condition_reached(const LocalProblemNode* reach_cond, const int cond_index);
    virtual void update_target_state();
    virtual double get_start_value(const int precond_var, const int preced_cond_idx);
};

class LocalProblemComp: public LocalProblem {
public:

    //nodes[0] = false, nodes[1] = true
    std::vector<LocalProblemNodeComp> nodes;
    LocalProblemNodeComp* get_node(int var_no) {
        return &(nodes[var_no]);
    }

    //inherited member variable start_value always has start_value 0 (true) or 1 (false)

//    binary_op comp_op;

    void build_nodes_for_variable(int var_no, int the_start_value);

    LocalProblemComp(int var_no, int start_val);
    virtual void initialize(double base_priority, int start_value,
            const TimeStampedState &state);
};

//*****************************************************
//PCHeuristic
//*****************************************************

class Node_compare {
public:
    bool operator()(const LocalProblemNode* ln, const LocalProblemNode* rn) const {
        return (rn->priority() < ln->priority());
    }
};

class PCHeuristic: public Heuristic {
public:
    int transtition_option;//for order version
     
    std::vector<LocalProblem *> local_problems;
    std::vector<std::vector<LocalProblem *> > local_problem_index;
    LocalProblemDiscrete *goal_problem;
    LocalProblemNodeDiscrete *goal_node;

    node_queue open_nodes;

    int number_of_nodes_in_queue;

    vector<LocalProblemNodeDiscrete*> nodes_with_an_additional_transition;
    vector<ValueNode*> dtg_nodes_with_an_additional_transition;
    vector<Operator*> generated_waiting_ops;
    vector<ValueTransitionLabel*> generated_labels;

    bool is_running(LocalTransition* trans, const TimeStampedState& state);
    double compute_costs(const TimeStampedState &state);
    void initialize_queue();
    void add_to_queue(LocalProblemNode *node);
    LocalProblemNode* remove_from_queue();
    void build_transitions_for_running_ops(const TimeStampedState &state);
    void remove_transitions_for_running_ops(const TimeStampedState &state);

    inline LocalProblem *get_local_problem(int var_no, int value);

    virtual void initialize();
    virtual double compute_heuristic(const TimeStampedState &state);

    PCHeuristic(){

    }
    PCHeuristic(int trans_potion);
    ~PCHeuristic();
    virtual bool dead_ends_are_reliable() {
        return false;
    }
    //for order version
    const TimeStampedState *state;
};

//*****************************************************
//inline functions
//*****************************************************
inline double LocalProblemNode::priority() const {
    return cost + owner->base_priority;
}

inline bool LocalProblem::is_initialized() const {
    return base_priority != -1;
}

inline LocalProblem *PCHeuristic::get_local_problem(int var_no,
        int value) {
    LocalProblem *result = local_problem_index[var_no][value];
    if(!result) {
        if(g_variable_types[var_no] == comparison) {
            result = new LocalProblemComp(var_no, value);
        } else {
            assert(g_variable_types[var_no] == logical);
            result = new LocalProblemDiscrete(var_no, value);
        }
        local_problem_index[var_no][value] = result;
        local_problems.push_back(result);
    }
    return result;
}

#endif
