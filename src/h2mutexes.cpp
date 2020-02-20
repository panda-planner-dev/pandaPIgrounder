#define NO_OPERATOR

#include <unordered_set>
#include <unistd.h>

#include "h2mutexes.h"
#include "../h2-fd-preprocessor/src/domain_transition_graph.h"
#include "../h2-fd-preprocessor/src/state.h"
#include "../h2-fd-preprocessor/src/mutex_group.h"
#include "../h2-fd-preprocessor/src/operator.h"
#include "../h2-fd-preprocessor/src/axiom.h"
#include "../h2-fd-preprocessor/src/causal_graph.h"
#include "../h2-fd-preprocessor/src/h2_mutexes.h"


bool h2_mutexes(const Domain & domain, const Problem & problem,
		std::vector<Fact> & reachableFacts,
		std::vector<GroundedTask> & reachableTasks,
		std::vector<bool> & prunedFacts,
		std::vector<bool> & prunedTasks,
		bool quietMode){
    
	int h2_mutex_time = 300; // 5 minutes to compute mutexes by default
    bool disable_bw_h2 = false;

	std::vector<Variable *> variables;
	std::map<Variable *,int> variableIndex;
	std::vector<Variable> internal_variables;
    State initial_state;
	std::vector<std::pair<Variable *, int>> goals;
	std::vector<MutexGroup> mutexes;
	std::vector<Operator> operators;
	std::vector<Axiom> axioms;
	std::vector<DomainTransitionGraph> transition_graphs;

	/////////////////////////// FILL THE MODEL, partially coped from FD
	// determine the number of unpruned facts
	int unprunedFacts = 0;
	for (bool x : prunedFacts) if (!x) unprunedFacts++;
	int numberOfFacts = unprunedFacts + (problem.initialAbstractTask == -1? 0 : 1);
	
	internal_variables.reserve(numberOfFacts);
	
	// contains mapping from output IDs to internal IDS
	std::vector<int> factOutput;
	std::vector<int> factIDtoOutputOutput;
	std::set<Fact> outputFactsSet;
	for(size_t factID = 0; factID < reachableFacts.size(); factID++){
		if (prunedFacts[factID]) {
			factIDtoOutputOutput.push_back(-1);
			continue;
		}
		int factOut = factOutput.size();
		factOutput.push_back(factID);
		factIDtoOutputOutput.push_back(factOut);

		Fact & fact = reachableFacts[factID];
		outputFactsSet.insert(fact);
		std::string factName = domain.predicates[fact.predicateNo].name + "[";
		for (unsigned int i = 0; i < fact.arguments.size(); i++){
			if (i) factName += ",";
			factName += domain.constants[fact.arguments[i]];
		}
		factName += "]";

		// construct variable
	    Variable var(2);
		var.name = "var" + factOut;
		var.layer = -1;
		var.values[0] = "Atom " + factName;
		var.values[1] = "Not Atom " + factName;

		internal_variables.push_back(var);
        variables.push_back(&internal_variables.back());
		variableIndex[&internal_variables.back()] = factID;
	}
	
	if (problem.initialAbstractTask != -1){
		// construct variable
	    Variable var(2);
		var.name = "fakeGoal";
		var.layer = -1;
		var.values[0] = "GOAL";
		var.values[1] = "NOT GOAL";

		internal_variables.push_back(var);
        variables.push_back(&internal_variables.back());
		variableIndex[&internal_variables.back()] = -1;
	}

	// initial state
	std::set<Fact> initFacts (problem.init.begin(), problem.init.end());
	for (int & factID : factOutput){
		Fact & fact = reachableFacts[factID];
		int fdID = factIDtoOutputOutput[factID];

		auto initFactIterator = initFacts.find(fact);
		if (initFactIterator != initFacts.end())
			initial_state.values[variables[fdID]] = 0;
		else
			initial_state.values[variables[fdID]] = 1;
	}
	if (problem.initialAbstractTask != -1)
	   initial_state.values[variables[unprunedFacts]] = 1;


	// goal
	for (const Fact & f : problem.goal){
		auto it = outputFactsSet.find(f);
		if (it == outputFactsSet.end()) continue; // might be unsolvable, but we shall detect this at another place.
		if (prunedFacts[it->groundedNo]) continue; // same as above

		int fdID = factIDtoOutputOutput[it->groundedNo];
		goals.push_back(std::make_pair(variables[fdID],0));
	}
	
	if (problem.initialAbstractTask != -1)
		goals.push_back(std::make_pair(variables[unprunedFacts],0));


	// create operators
	
	// for action costs
	std::map<Fact,int> init_functions_map;
	for (auto & init_function_literal : problem.init_functions){
		init_functions_map[init_function_literal.first] = init_function_literal.second;
	}
	
	int unprunedActions = 0;
	for(size_t taskID = 0; taskID < reachableTasks.size(); taskID++) if (! prunedTasks[taskID] && reachableTasks[taskID].taskNo < domain.nPrimitiveTasks){
		GroundedTask & task = reachableTasks[taskID];
		unprunedActions++;

		std::string actionName = domain.tasks[task.taskNo].name + "[";
		// only output the original variables
		for (unsigned int i = 0; i < domain.tasks[task.taskNo].number_of_original_variables; i++){
			if (i) actionName += ",";
			actionName += domain.constants[task.arguments[i]];
		}
		actionName += "]";

		// determine the prevail  
		std::unordered_set<int> pre,add,del;
		for (int & prec : task.groundedPreconditions)
			if (!prunedFacts[prec])
				pre.insert(factIDtoOutputOutput[prec]);
		
		for (int & addf : task.groundedAddEffects)
			if (!prunedFacts[addf])
				add.insert(factIDtoOutputOutput[addf]);
		
		for (int & delf : task.groundedDelEffects)
			if (!prunedFacts[delf])
				del.insert(factIDtoOutputOutput[delf]);

		std::unordered_set<int> prevail;
		for (const int & p : pre) if (!del.count(p)) prevail.insert(p);


		// create FD operator
		::Operator op;
		op.operatorID = taskID;
		op.name = actionName;
		for (const int & p : prevail) 
			op.prevail.push_back(Operator::Prevail(variables[p],0));

		for (const int & x : add) {
			// TODO consider conditional effects, if we can parse and ground them
			op.pre_post.push_back(Operator::PrePost(variables[x],-1,0));
		}

		for (const int & x : del) {
			// TODO consider conditional effects, if we can parse and ground them
			op.pre_post.push_back(Operator::PrePost(variables[x],(pre.count(x)?0:-1),1));
		}

		if (problem.initialAbstractTask != -1){
			op.pre_post.push_back(Operator::PrePost(variables[unprunedFacts],-1,0));
		}

		op.cost = domain.tasks[task.taskNo].computeGroundCost(task,init_functions_map);
		operators.push_back(op);
	}

	///////////////////////////////////////////////////////// conversion done

	// compute h2 mutexes

	if (!quietMode) std::cout << "Building causal graph..." << std::endl;

	// H2 inference produces output to std, so temporarily disable it if in quiet mode
	if (quietMode)
		std::cout.setstate(std::ios_base::failbit);

    CausalGraph causal_graph(variables, operators, axioms, goals);
    const vector<Variable *> &ordering = causal_graph.get_variable_ordering();
    bool cg_acyclic = causal_graph.is_acyclic();

    // Remove unnecessary effects from operators and axioms, then remove
    // operators and axioms without effects.
    strip_mutexes(mutexes);
    strip_operators(operators);
    strip_axioms(axioms);


    // compute h2 mutexes
    if (axioms.size() > 0) {
        cout << "Disabling h2 analysis because it does not currently support axioms" << endl;
    } else if (h2_mutex_time) {
        bool conditional_effects = false;
        for (const Operator &op : operators) {
            if (op.has_conditional_effects()) {
                conditional_effects = true;
                break;
            }
        }
        if (conditional_effects)
            disable_bw_h2 = true;

        if(!compute_h2_mutexes(ordering, operators, axioms,
                           mutexes, initial_state, goals,
			       h2_mutex_time, disable_bw_h2)){
			std::cerr << "Goal is unreachable [never reachable] ... " << std::endl;
			_exit(0);
		}
        //Update the causal graph and remove unneccessary variables
        strip_mutexes(mutexes);
        strip_operators(operators);
        strip_axioms(axioms);

        cout << "Change id of operators: " << operators.size() << endl;
        // 1) Change id of values in operators and axioms to remove unreachable facts from variables
        for (Operator &op: operators) {
            op.remove_unreachable_facts(ordering);
        }
        // TODO: Activate this if axioms get supported by the h2 heuristic
        // cout << "Change id of axioms: " << axioms.size() << endl;
        // for(int i = 0; i < axioms.size(); ++i){
        //     axioms[i].remove_unreachable_facts();
        // }
        cout << "Change id of mutexes" << endl;
        for (MutexGroup &mutex : mutexes) {
            mutex.remove_unreachable_facts();
        }
        cout << "Change id of goals" << endl;
        vector<pair<Variable *, int>> new_goals;
        for (pair<Variable *, int> &goal : goals) {
            if (goal.first->is_necessary()) {
                goal.second = goal.first->get_new_id(goal.second);
                new_goals.push_back(goal);
            }
        }
        new_goals.swap(goals);
        cout << "Change id of initial state" << endl;
        if (initial_state.remove_unreachable_facts()) {
			std::cerr << "Goal is unreachable [never reachable] ... " << std::endl;
			_exit(0);
        }

        cout << "Remove unreachable facts from variables: " << ordering.size() << endl;
        // 2)Remove unreachable facts from variables
        for (Variable *var : ordering) {
            if (var->is_necessary()) {
                var->remove_unreachable_facts();
            }
        }

        strip_mutexes(mutexes);
        strip_operators(operators);
        strip_axioms(axioms);

        causal_graph.update();
        cg_acyclic = causal_graph.is_acyclic();
        strip_mutexes(mutexes);
        strip_operators(operators);
        strip_axioms(axioms);
    }

	// H2 inference produces output to std, so re-endable cout
	if (quietMode)
		std::cout.clear();

	// find out which operators and facts were pruned
	int afterwardsUnprunedFacts = 0;
	int afterwardsUnprunedActions = 0;

	// set all facts to pruned
	for (size_t factID = 0; factID < prunedFacts.size(); factID++)
		prunedFacts[factID] = true;
	for (Variable* var : causal_graph.get_variable_ordering()){
		int variableID = variableIndex[var];
		if (variableID == -1) continue; // artificial goal fact
		prunedFacts[variableID] = false;
		afterwardsUnprunedFacts++;
	}

	// set all primitives to pruned	
	for(size_t taskID = 0; taskID < reachableTasks.size(); taskID++)
		if (reachableTasks[taskID].taskNo < domain.nPrimitiveTasks)
			prunedTasks[taskID] = true;

	// set all operators that are still reachable to not pruned
	for (Operator & op : operators){
		prunedTasks[op.operatorID] = false;
		afterwardsUnprunedActions++;
	}

	//return (afterwardsUnprunedActions != unprunedActions) || (afterwardsUnprunedFacts != unprunedFacts);
	return afterwardsUnprunedActions != unprunedActions;
}


