#include <iomanip>
#include <iostream>
#include <ostream>
#include <map>
#include <algorithm>
#include <unistd.h>

#include "output.h"

void write_grounded_HTN(std::ostream & pout, const Domain & domain, const Problem & problem,
		std::vector<Fact> & reachableFacts,
		std::vector<GroundedTask> & reachableTasks,
		std::vector<GroundedMethod> & reachableMethods,
		std::vector<bool> & prunedTasks,
		std::vector<bool> & prunedFacts,
		std::vector<bool> & prunedMethods,
		int facts,
		int absTask,
		int primTask,
		int methods,
		bool quietMode	
		){
	if (!quietMode) std::cerr << "Writing instance to output." << std::endl;

	std::set<Fact> reachableFactsSet(reachableFacts.begin(), reachableFacts.end());

	// assign fact numbers
	int fn = 0;
	for (Fact & fact : reachableFacts){
		if (prunedFacts[fact.groundedNo]) continue;
		fact.outputNo = fn++; // assign actual index to fact
	}

	pout << ";; #state features" << std::endl;
	pout << facts << std::endl;
	for (Fact & fact : reachableFacts){
		if (prunedFacts[fact.groundedNo]) continue;
		pout << domain.predicates[fact.predicateNo].name << "[";
		for (unsigned int i = 0; i < fact.arguments.size(); i++){
			if (i) pout << ",";
			pout << domain.constants[fact.arguments[i]];
		}
		pout << "]" << std::endl;
	}
	pout << std::endl;


	// as long as we can't output true SAS+, we simply output the fact list again
	pout << ";; Mutex Groups" << std::endl;
	pout << facts << std::endl;
	for (Fact & fact : reachableFacts){
		if (prunedFacts[fact.groundedNo]) continue;
		pout << fact.outputNo << " " << fact.outputNo << " ";
		pout << domain.predicates[fact.predicateNo].name << "[";
		for (unsigned int i = 0; i < fact.arguments.size(); i++){
			if (i) pout << ",";
			pout << domain.constants[fact.arguments[i]];
		}
		pout << "]" << std::endl;
	}
	pout << std::endl;

	
	std::map<Fact,int> init_functions_map;
	for (auto & init_function_literal : problem.init_functions){
		init_functions_map[init_function_literal.first] = init_function_literal.second;
	}



	pout << ";; Actions" << std::endl;
	pout << primTask << std::endl; 
	int ac = 0;
	for (GroundedTask & task : reachableTasks){
		if (task.taskNo >= domain.nPrimitiveTasks || prunedTasks[task.groundedNo]) continue;

		task.outputNo = ac++;
		
		// compute the costs for this ground actions
		std::vector<std::variant<PredicateWithArguments,int>> additive_cost_expressions = domain.tasks[task.taskNo].costs;
		int costs = 0;
		for (std::variant<PredicateWithArguments,int> cost_element : additive_cost_expressions){
			if (std::holds_alternative<int>(cost_element)){
				costs += std::get<int>(cost_element);
			} else {
				PredicateWithArguments function_term = std::get<PredicateWithArguments>(cost_element);
				// build fact representation of this term with respect to the grounding
				Fact cost_fact;
				cost_fact.predicateNo = function_term.predicateNo;
				for (int & argument_variable : function_term.arguments)
					cost_fact.arguments.push_back(task.arguments[argument_variable]);

				costs += init_functions_map[cost_fact];
			}
		}
		pout << costs << std::endl;
		
		for (int & prec : task.groundedPreconditions)
			if (!prunedFacts[prec])
				pout << reachableFacts[prec].outputNo << " ";
		pout << -1 << std::endl;
		
		for (int & add : task.groundedAddEffects)
			if (!prunedFacts[add])
				pout << reachableFacts[add].outputNo << " ";
		pout << -1 << std::endl;
		
		for (int & del : task.groundedDelEffects)
			if (!prunedFacts[del])
				pout << reachableFacts[del].outputNo << " ";
		pout << -1 << std::endl;
	}

	pout << std::endl << ";; initial state" << std::endl;
	std::set<int> initFacts; // needed for efficient goal checking
	std::set<int> initFactsPruned; // needed for efficient checking of pruned facts in the goal

	for (const Fact & f : problem.init){
		int groundNo = reachableFactsSet.find(f)->groundedNo;
		if (prunedFacts[groundNo]){
			initFactsPruned.insert(groundNo);
			continue;
		}
		pout << reachableFacts[groundNo].outputNo << " ";
		initFacts.insert(groundNo);
	}
	
	pout << -1 << std::endl;
	pout << std::endl << ";; goal" << std::endl;
	for (const Fact & f : problem.goal){
		auto it = reachableFactsSet.find(f);
		if (it == reachableFactsSet.end()){
			// TODO detect this earlier and do something intelligent
			std::cerr << "Goal is unreachable [never reachable] ... " << std::endl;
			_exit(0);
		}
		if (prunedFacts[it->groundedNo]){
			// check whether it is true ...
			if (!initFactsPruned.count(it->groundedNo)){
				// TODO detect this earlier and do something intelligent
				std::cerr << "Goal is unreachable [pruned] ..." << std::endl;

				std::cout << "Pruned, non-true fact: " << domain.predicates[f.predicateNo].name << "[";
				for (unsigned int i = 0; i < f.arguments.size(); i++){
					if (i) std::cout << ",";
					std::cout << domain.constants[f.arguments[i]];
				}
				std::cout << "]" << std::endl;

				_exit(0);
			}
			continue;
		}
		pout << reachableFacts[it->groundedNo].outputNo << " ";
	}
	pout << -1 << std::endl;

	
	pout << std::endl << ";; tasks (primitive and abstract)" << std::endl;
	pout << ac + absTask << std::endl;
	// count number of reachable  abstracts
	for (GroundedTask & task : reachableTasks){
		if (prunedTasks[task.groundedNo]) continue;
		if (task.taskNo >= domain.nPrimitiveTasks) continue;
		pout << 0 << " ";
		
		
		pout << domain.tasks[task.taskNo].name << "[";
		// only output the original variables
		for (unsigned int i = 0; i < domain.tasks[task.taskNo].number_of_original_variables; i++){
			if (i) pout << ",";
			pout << domain.constants[task.arguments[i]];
		}
		pout << "]" << std::endl;
	}

	int initialAbstract = -1;
	for (GroundedTask & task : reachableTasks){
		if (prunedTasks[task.groundedNo]) continue;
		if (task.taskNo < domain.nPrimitiveTasks) continue;
		task.outputNo = ac++;
		if (task.taskNo == problem.initialAbstractTask) initialAbstract = task.outputNo; 

		pout << 1 << " ";

		pout << domain.tasks[task.taskNo].name << "[";
		for (unsigned int i = 0; i < task.arguments.size(); i++){
			if (i) pout << ",";
			pout << domain.constants[task.arguments[i]];
		}
		pout << "]" << std::endl;
	}


	pout << std::endl << ";; initial abstract task" << std::endl;
	pout << initialAbstract << std::endl;


	pout << std::endl << ";; methods" << std::endl;
	pout << methods << std::endl;
	int mc = 0;
	for (auto & method : reachableMethods){
		if (prunedMethods[method.groundedNo]) continue;
		mc++;
		// output their name
		pout << domain.decompositionMethods[method.methodNo].name << std::endl;
		/* method names may not contained variables for verification
		 * TODO maybe add a FLAG here (for debugging the planner)
		<< "[";
		for (unsigned int i = 0; i < method.arguments.size(); i++){
			if (i) pout << ",";
			pout << domain.constants[method.arguments[i]];
		}
		pout << "]" << std::endl;*/

		// the abstract tasks
		pout << reachableTasks[method.groundedAddEffects[0]].outputNo << std::endl;
		
		std::map<int,int> subTaskIndexToOutputIndex;
		// output subtasks in their topological ordering
		for (size_t outputIndex = 0; outputIndex < method.preconditionOrdering.size(); outputIndex++){
			int subtaskIndex = method.preconditionOrdering[outputIndex];
			subTaskIndexToOutputIndex[subtaskIndex] = outputIndex;

			pout << reachableTasks[method.groundedPreconditions[subtaskIndex]].outputNo << " ";
		}
		pout << "-1" << std::endl;

		auto orderings = domain.decompositionMethods[method.methodNo].orderingConstraints;
		auto last = std::unique(orderings.begin(), orderings.end());
		orderings.erase(last, orderings.end());


		for (auto & order : orderings)
			pout << subTaskIndexToOutputIndex[order.first] << " " << subTaskIndexToOutputIndex[order.second] << " ";
		pout << "-1" << std::endl;
	}


	// exiting this way is faster as data structures will not be cleared ... who needs this anyway
	if (!quietMode) std::cerr << "Exiting." << std::endl;
	// exiting this way is faster ...
	_exit (0);
}
