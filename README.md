# lmtd
LMTD planning algorithm from IPC 2011










Copied from original README


LMTD,IPC7 version
Yanmei Hu, Dunbo Cai

Just like TFD, LMTD runs in three separate parts:
translate(pddl->sas), preprocess(knowlege compilation),
and search. Following is the steps to solve a planning
task:
1. translate domain.pddl problem.pddl > output.sas
(output.sas is for the inpput of preprocess)
this step transforms the pddl tasks to sas tasks


2.preprocess < output.sas > output
(do some pretreatments, for the search part)

3.search [1-7] t [1-1800] gpPn[1-3] plan_name < output

This part is for the search.The parameter [1-7] is for
the order version(how to order the preconditions). The
second and third parameters are for the time limit the
running of search.The parameter g is for the gready search
algorithm, p is for our heuristic choice, that is pc_heuristic
P is for the choice of preferred operators and n is for the
choice of no any heuristics.[1-3] here is for context state
choice, every local problem has waiting nodes that store the
unsatisfied preconditions, so we can choose any waiting nodes's
context state as the final sate after the local problem is solved.
plan_name store the plan for the successful running, while if
unsuccessful, plan_name is empty. On the other hand, our planner
is a anytime planner, so the plan for a planning task may be
not just one. if our planner search several plans for a planning
task, for example 3 plans( they are different), there will be 
3 files, named plan_name1, plan_name2, plan_name3, for the output.




Note:for convenient, we simply the excutable of our planner,
here is for how to run our planner combining three parts.
1. tempo-sat-LMTD/build  

   This shell is to make our planner

2. tempo-sat-LMTD/plan domain.pddl problem.pddl plan_name

   This shell is to run our planner and get the plan for
   the input planning task.
