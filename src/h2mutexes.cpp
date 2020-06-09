#define NO_OPERATOR

#include <unordered_set>
#include <unistd.h>
#include <cassert>

#include "debug.h"
#include "h2mutexes.h"
#include "../h2-fd-preprocessor/src/domain_transition_graph.h"
#include "../h2-fd-preprocessor/src/state.h"
#include "../h2-fd-preprocessor/src/mutex_group.h"
#include "../h2-fd-preprocessor/src/operator.h"
#include "../h2-fd-preprocessor/src/axiom.h"
#include "../h2-fd-preprocessor/src/causal_graph.h"
#include "../h2-fd-preprocessor/src/h2_mutexes.h"


std::tuple<bool,std::vector<std::unordered_set<int>>, std::vector<std::unordered_set<int>>> compute_h2_mutexes(const Domain & domain, const Problem & problem,
		std::vector<Fact> & reachableFacts,
		std::vector<GroundedTask> & reachableTasks,
		std::vector<bool> & prunedFacts,
		std::vector<bool> & prunedTasks,
		std::vector<std::unordered_set<int>> sas_groups,
		std::vector<bool> & sas_variables_needing_none_of_them,
	grounding_configuration & config){
    
	int h2_mutex_time = 10; // 10 seconds to compute mutexes by default
    bool disable_bw_h2 = false;

	std::vector<Variable *> variables;
	std::map<Variable *,std::map<string,int>> variableIndex;
	std::vector<Variable> internal_variables;
    State initial_state;
	std::vector<std::pair<Variable *, int>> goals;
	std::vector<MutexGroup> mutexes;
	std::vector<Operator> operators;
	std::vector<Axiom> axioms;
	std::vector<DomainTransitionGraph> transition_graphs;

	/////////////////////////// FILL THE MODEL, partially coped from FD
	// determine the number of unpruned facts
	//int unprunedFacts = 0;


	// contains mapping from output IDs to internal IDS
	std::vector<int> factOutput;
	std::vector<std::pair<int,int>> factIDtoVarVal (reachableFacts.size());
	for (size_t i = 0; i < reachableFacts.size(); i++)
		factIDtoVarVal[i] = std::make_pair(-1,-1); // all pruned unless otherwise noted
	std::set<Fact> outputFactsSet;
	
	// build init together with the variables
	std::set<Fact> initFacts (problem.init.begin(), problem.init.end());
	std::set<Fact> goalFacts (problem.goal.begin(), problem.goal.end());

	// first add the variables for true SAS+ groups
	std::unordered_set<int> facts_covered_by_sas_groups;
	internal_variables.reserve(sas_groups.size() + (problem.initialAbstractTask != -1));

	for (size_t sas_g = 0; sas_g < sas_groups.size(); sas_g++){
		int size_of_sas_group = sas_groups[sas_g].size() + sas_variables_needing_none_of_them[sas_g];
		
		// construct variable
	    Variable var(size_of_sas_group);
		var.name = "var" + internal_variables.size();
		var.layer = -1;

		int valPos = 0;
		int initialValue = -1;
		int goalValue = -1;
		for (int elem : sas_groups[sas_g]){
			Fact & f = reachableFacts[elem];
			assert(!prunedFacts[f.groundedNo]);
			// for H2 mutexes it is ok that a member of the mutex group is a guard predicate
			//assert(!domain.predicates[f.predicateNo].guard_for_conditional_effect);
			// assemble the name of this fact
			std::string factName = domain.predicates[f.predicateNo].name + "[";
			for (unsigned int i = 0; i < f.arguments.size(); i++){
				if (i) factName += ",";
				factName += domain.constants[f.arguments[i]];
			}
			factName += "]";

			var.values[valPos] = factName;
	
			factIDtoVarVal[elem].first = variables.size();
			factIDtoVarVal[elem].second = valPos;

			if (initFacts.count(f)) initialValue = valPos;
			if (goalFacts.count(f)) goalValue = valPos;
			valPos++;
		}

		if (sas_variables_needing_none_of_them[sas_g]){
			var.values[valPos] = "none-of-those";
			if (initialValue == -1) initialValue = valPos;
		}


		// add variable to data structures
		internal_variables.push_back(var);
		variables.push_back(&internal_variables.back());

		// set the initial value of this variable
		assert(initialValue != -1);
		initial_state.values[variables.back()] = initialValue;

		// goal
		if (goalValue != -1)
			goals.push_back(std::make_pair(&internal_variables.back(),goalValue));

		// add variable to back translation table		
		valPos = 0;
		for (int elem : sas_groups[sas_g])
			variableIndex[&internal_variables.back()][var.values[valPos++]] = elem;
		if (sas_variables_needing_none_of_them[sas_g])
			variableIndex[&internal_variables.back()][var.values[valPos]] = -sas_g - 3; // none of those
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
		variableIndex[&internal_variables.back()]["GOAL"] = -1;
		variableIndex[&internal_variables.back()]["NOT GOAL"] = -2;
	   
		// set the initial state to unreached
		initial_state.values[&internal_variables.back()] = 1;
		// and that it must be reached in the goal
		goals.push_back(std::make_pair(&internal_variables.back(),0));
	}



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


		// TODO consider conditional effects, if we can parse and ground them
	
		// determine the prevail and changing conditions
		std::map<int,int> pre,add;
		for (int & prec : task.groundedPreconditions)
			if (!prunedFacts[prec])
				pre[factIDtoVarVal[prec].first] = factIDtoVarVal[prec].second;
		
		for (int & addf : task.groundedAddEffects)
			if (!prunedFacts[addf])
				add[factIDtoVarVal[addf].first] = factIDtoVarVal[addf].second;

		for (const int & sas_g : task.noneOfThoseEffect)
			add[sas_g] = variables[sas_g]->values.size() - 1; 

		std::map<int,int> prevail;
		for (const auto & p : pre)
			if (!add.count(p.first))
				prevail[p.first] = p.second;


		// create FD operator
		::Operator op;
		op.operatorID = taskID;
		op.name = actionName;
		for (const auto & p : prevail) 
			op.prevail.push_back(Operator::Prevail(variables[p.first],p.second));

		for (const auto & x : add) {
			int precondition = -1;
			if (pre.count(x.first)) precondition = pre[x.first];
			op.pre_post.push_back(Operator::PrePost(variables[x.first],precondition,x.second));
		}

		if (problem.initialAbstractTask != -1)
			op.pre_post.push_back(Operator::PrePost(&internal_variables.back(),-1,0));


		op.cost = domain.tasks[task.taskNo].computeGroundCost(task,init_functions_map);
		operators.push_back(op);
		DEBUG(std::cout << "Action " << actionName << ": prevail " << op.prevail.size() << " prepost " << op.pre_post.size() << std::endl);
	}

	///////////////////////////////////////////////////////// conversion done

	// compute h2 mutexes


	if (!config.quietMode)
		std::cout << "Entering H2 mutex computation with " << unprunedActions << " actions." << std::endl;
	if (!config.quietMode) std::cout << "Building causal graph..." << std::endl;

	// H2 inference produces output to std, so temporarily disable it if in quiet mode
	if (config.quietMode)
		std::cout.setstate(std::ios_base::failbit);

    CausalGraph causal_graph(variables, operators, axioms, goals);
    const vector<Variable *> &ordering = causal_graph.get_variable_ordering();
    //bool cg_acyclic = causal_graph.is_acyclic();

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
        //cg_acyclic = causal_graph.is_acyclic();
        strip_mutexes(mutexes);
        strip_operators(operators);
        strip_axioms(axioms);
    }

	// H2 inference produces output to std, so re-endable cout
	if (config.quietMode)
		std::cout.clear();
	
	DEBUG(std::cout << "Finished H2 mutex computation" << std::endl);

	// find out which operators and facts were pruned
	int afterwardsUnprunedFacts = 0;
	int afterwardsUnprunedActions = 0;

	// set all facts to pruned
	for (size_t factID = 0; factID < prunedFacts.size(); factID++)
		prunedFacts[factID] = true;
	for (Variable* var : causal_graph.get_variable_ordering()){
		for (int val = 0; val < var->values.size(); val++){
			if (!var->is_reachable(val)) continue;
			int factID = variableIndex[var][var->values[val]]; // identification via string
			if (factID < 0) continue; // artificial goal fact or "non-of-those"
			prunedFacts[factID] = false;
			afterwardsUnprunedFacts++;
		}
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
	

	std::vector<unordered_set<int>> h2_mutexes;	
	std::vector<unordered_set<int>> h2_invariants;	
	

	
	for (const MutexGroup & mutex :  mutexes){
		std::unordered_set<int> facts;
		bool irrelevant = false;
		bool invariant = false;
		DEBUG(std::cout << "H2 Mutex Group:");
		for (auto & f : mutex.getFacts()){
			int factID = variableIndex[const_cast<Variable*>(f.first)][f.first->values[f.second]];
			if (factID == -1 || factID == -2) irrelevant = true; // artificial goal fact
			if (factID < -2) invariant	= true; // none-of-those
			if (factID >= 0 && prunedFacts[factID]) irrelevant = true;
			DEBUG(std::cout << " " << factID);	
			facts.insert(factID);

			DEBUG(
				if (factID == -1 || factID == -2) continue; // goal
				if (factID < 0) {
					for (int elem : sas_groups[-factID - 3]){
						Fact & fact = reachableFacts[elem];
						std::string factName = domain.predicates[fact.predicateNo].name + "[";
						for (unsigned int i = 0; i < fact.arguments.size(); i++){
							if (i) factName += ",";
							factName += domain.constants[fact.arguments[i]];
						}
						factName += "]";
	
						std::cout << " " << factName;
					}
				} else {
					Fact & fact = reachableFacts[factID];
					std::string factName = domain.predicates[fact.predicateNo].name + "[";
					for (unsigned int i = 0; i < fact.arguments.size(); i++){
						if (i) factName += ",";
						factName += domain.constants[fact.arguments[i]];
					}
					factName += "]";

					std::cout << " " << factName;
				}
			);
		}
		DEBUG(std::cout << std::endl);

		if (irrelevant) continue; // don't add it
		
		if (!invariant){
			// true mutex
			DEBUG(std::cout << "Add as mutex" << std::endl);
			h2_mutexes.push_back(facts);
		} else {
			DEBUG(std::cout << "Add as invariant:");
			std::unordered_set<int> inv;
			
			for (const int & elem : facts){
				if (elem >= 0){
					DEBUG(std::cout << " " << (-elem-1));
					inv.insert(-elem-1); // not this one
				} else {
					for (int e : sas_groups[-elem - 3]){
						DEBUG(std::cout << " " << e);
						inv.insert(e);
					}
				}
			}
			h2_invariants.push_back(inv);
			DEBUG(std::cout << std::endl);
		}
	}

	return std::make_tuple(afterwardsUnprunedActions != unprunedActions,
			h2_mutexes,
			h2_invariants);
}


