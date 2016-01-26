#include "best_first_search.h"
//#include "cyclic_cg_heuristic.h"
#include "pc_heuristic.h"
#include "no_heuristic.h"

#include "globals.h"
#include "operator.h"
#include "partial_order_lifter.h"
#include "monitoring.h"

#include <cstdlib>
#include <cstring>
#include <iostream>
#include <fstream>
#include <vector>
#include <sstream>

#include <cstdio>
#include <math.h>

using namespace std;

#include <sys/times.h>

#define ANYTIME_SEARCH 1

pair<double, double> save_plan(const vector<PlanStep> &plan, const PlanTrace &path, pair<double,double> best_makespan, string &plan_best, int& plan_num);
void readPlanFromFile(const string& filename, vector<string>& plan);
bool validatePlan(vector<string>& plan);

int main(int argc, const char **argv) {
    struct tms start, search_start, search_end;
    times(&start);
    bool poly_time_method = false;

    g_greedy = false;
    bool pc_heuristic = false, pc_preferred_operators = false;
    bool no_heuristic = false;
    bool use_reasonable = false;
    string plan_best = "sas_plan";
    if(argc < 3) {
	cerr << "missing argument: output file name" << endl;
	return 1;
    } else {
	plan_best = string(argv[argc - 1]);
	argc--;
    }
    int trans_option = 2; // default transition option, for 4a, 4b, 4c
    bool monitor = false;
    for(int i = 1; i < argc; i++) {
        if(i == 1) {
  		const char *c = argv[i];
               // cout<< *c;
  		if(*c >= '1' && *c <= '9') {
  			g_before_order_option = *c - '0'; 
  		}
  		else {
  			cerr << "Invalid option of before order; choose from [1..7] " << endl;
  			return 1;
  		}
  	} else {
  		if (g_before_order_option == -1) {
  			cerr << "Error, no option of before order!" << endl;
  			return 1;
  		}
	    for(const char *c = argv[i]; *c != 0; c++) {
	    if(*c == 't') {
		g_timeout = atoi(string(argv[++i]).c_str());
	    } else if(*c == 'm') {
	        g_planMonitorFileName = string(argv[++i]);
	        monitor = true;
	    } else if(*c == 'g') {
	        g_greedy = true;
	    } else if(*c == 'p'){
              pc_heuristic = true;   
            }else if(*c == 'P'){
              pc_preferred_operators = true;       
            }else if(*c == 'n') {
		no_heuristic = true;
	    } else if(*c >= '1' && *c <= '3') {
  		trans_option = *c - '0';	
   	    } else {
		    cerr << "Unknown option: " << *c << endl;
		    return 1;
	    }
	    }
        }
    }
    //if(g_timeout > 0) {
    //	cout << "Timeout set to " << g_timeout << " sec." << endl;
    //}

    if(!pc_heuristic && !no_heuristic) {
	cerr << "Error: you must select at least one heuristic!" << endl
		<< "If you are unsure, choose options \"yY\"." << endl;
	return 2;
    }
    cin >> poly_time_method;
    if(poly_time_method) {
	cout << "Poly-time method not implemented in this branch." << endl;
	cout << "Starting normal solver." << endl;
	// cout << "Aborting." << endl;
	// return 1;
    }
    
     // versions Ldown and Lup need to compute reasonable orders over landmarks. 
    if(g_before_order_option == 4 || g_before_order_option == 5) {
	use_reasonable = true;
    }
    
    read_everything(cin, true, use_reasonable);
    //dump_everything();
    
    g_let_time_pass = new Operator(false);
    g_wait_operator = new Operator(true);



    if(monitor) {
        vector<string> plan;
        readPlanFromFile(g_planMonitorFileName, plan);
        bool ret = validatePlan(plan);
        cout << "Plan is valid: " << ret << endl;
        exit(0);
    }

    BestFirstSearchEngine *engine = new BestFirstSearchEngine;
    if(no_heuristic){
	engine->add_heuristic(new NoHeuristic, no_heuristic, false);
    } 

    if(pc_heuristic){
       engine->add_heuristic(new PCHeuristic(trans_option), pc_heuristic, pc_preferred_operators);               
    }

    pair<double,double> best_makespan = make_pair(REALLYBIG,REALLYBIG); // first: original makespan, second: recheduled makespan
    int plan_num = 1;
    times(&search_start);
    while(true) {                 
	engine->initialize();
	engine->search();
	times(&search_end);
   	//double search_tsm = (search_end.tms_utime - search_start.tms_utime) * 10 / 1000.0;
	if(engine->found_solution()) {
	    best_makespan = save_plan(engine->get_plan(),engine->get_path(),best_makespan,plan_best,plan_num);
#ifdef ANYTIME_SEARCH
	    engine->fetch_next_state();         
#else
	    break;
#endif
	}
	else {
	    break;
	}
    }


    //int search_ms = (search_end.tms_utime - search_start.tms_utime) * 10;
    //int total_ms = (search_end.tms_utime - start.tms_utime) * 10;

    return engine->found_at_least_one_solution() ? 0 : 1;
    
}

void readPlanFromFile(const string& filename, vector<string>& plan) {
    ifstream fin(filename.c_str(), ifstream::in);
    string buffer;
    while(fin.good()) {
        getline(fin,buffer,'\n');
        plan.push_back(buffer);
    }
    fin.close();
}

bool validatePlan(vector<string>& plan) {
    cout << "Validate Plan!" << endl;
    MonitorEngine* mon = MonitorEngine::getInstance();
    bool monitor = mon->validatePlan(plan);
    return monitor;
}

pair<double,double> save_plan(const vector<PlanStep> &plan, const PlanTrace &path, pair<double,double> best_makespan, string &plan_best, int& plan_num) {


    PartialOrderLifter partialOrderLifter(plan, path);

    Plan new_plan = partialOrderLifter.lift();
    double makespan = 0;
    for(int i = 0; i < new_plan.size(); i++) {
	double end_time = new_plan[i].start_time + new_plan[i].duration;
	makespan = max(makespan,end_time);
    }

    double original_makespan = 0;
    for(int i = 0; i < plan.size(); i++) {
        double end_time = plan[i].start_time + new_plan[i].duration;
        original_makespan = max(original_makespan,end_time);
    }
    if(makespan >= best_makespan.second) return best_makespan;

    FILE *best_file = 0;
    if(plan_best != "-"){
	 int len = static_cast<int>(plan_best.size() + log10(plan_num) + 10);
	 char *filename = (char*)malloc(len * sizeof(char));
         sprintf(filename, "%s.%d", plan_best.c_str(), plan_num);
	 best_file = fopen(filename,"w");
    }else best_file = stdout;

    plan_num++;
    for(int i = 0; i < new_plan.size(); i++) {
	 const PlanStep& step = new_plan[i];
         fprintf(best_file,"%.8f: (%s) [%.8f]\n", step.start_time, step.op->get_name().c_str(), step.duration);
    }
    fprintf(best_file, "Plan length:  %d  step(s)\n", new_plan.size()); 
    fprintf(best_file, "Makespan  : %0.8f \n", makespan);  
    if(plan_best != "-")  
        fclose(best_file);

    return make_pair(original_makespan,makespan);

}
