#ifndef OPERATOR_H
#define OPERATOR_H

#include <cassert>
#include <iostream>
#include <string>
#include <vector>

#include "axioms.h"
#include "globals.h"
#include "state.h"

class Operator {
    vector<Prevail> prevail_start; // var, val
    vector<Prevail> prevail_overall; // var, val
    vector<Prevail> prevail_end; // var, val
    vector<PrePost> pre_post_start; // var, old-val, new-val
    vector<PrePost> pre_post_end; // var, old-val, new-val
    int duration_var;
    string name;
public:
    Operator(std::istream &in);
    Operator(bool uses_concrete_time_information);
    void dump() const;
    const vector<Prevail> &get_prevail_start() const {
        return prevail_start;
    }
    const vector<Prevail> &get_prevail_overall() const {
        return prevail_overall;
    }
    const vector<Prevail> &get_prevail_end() const {
        return prevail_end;
    }
    const vector<PrePost> &get_pre_post_start() const {
        return pre_post_start;
    }
    const vector<PrePost> &get_pre_post_end() const {
        return pre_post_end;
    }
    const int &get_duration_var() const {
        return duration_var;
    }
    const string &get_name() const {
        return name;
    }

    bool operator<(const Operator &other) const;

    bool is_applicable(const TimeStampedState &state) const;

    virtual ~Operator() {}
};

class ScheduledOperator : public Operator {
public:
    double time_increment;
    ScheduledOperator(double t, const Operator& op) : Operator(op), time_increment(t) {}
    ScheduledOperator(double t) : Operator(true), time_increment(t) {}
};

//added by huym, for landmarks,10-08-09
class SimpleOperator{
    bool is_an_axiom;
    std::vector<Prevail> prevail;      // var, val
    std::vector<PrePost> pre_post;     // var, old-val, new-val, effect conditions
   	std::string name;
    int cost; 

    mutable bool marked; //Used for short-term marking of preferred operators
		
public:
    SimpleOperator();
    SimpleOperator(Operator& op);
    SimpleOperator(LogicAxiom& la);
    SimpleOperator(NumericAxiom& na);
    void dump() const;
    std::string get_name() const {
        return name;
    }

    bool is_axiom() const {
        return is_an_axiom;
    }

    const std::vector<Prevail> &get_prevail() const {
        return prevail;
    }
    const std::vector<PrePost> &get_pre_post() const {
        return pre_post;
    }

    bool is_applicable(const TimeStampedState &state) const {
        for(int i = 0; i < prevail.size(); i++)
            if(!prevail[i].is_applicable(state))
                return false;
        for(int i = 0; i < pre_post.size(); i++)
            if(!pre_post[i].is_applicable(state))
                return false;
        return true;
    }
    int get_cost() const {
        return cost;
    }

    //Malte's
    bool is_marked() const {
        return marked;
    }
    //Malte's
    void mark() const {
        marked = true;
    }
    //Malte's
    void unmark() const {
        marked = false;
    }
};

#endif
