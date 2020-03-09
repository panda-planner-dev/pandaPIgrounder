#include <iomanip>
#include <iostream>
#include <ostream>
#include <map>
#include <algorithm>
#include <unistd.h>
#include <cassert>

#include "output.h"
#include "debug.h"

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
		std::vector<std::unordered_set<int>> sas_groups,
		std::vector<std::unordered_set<int>> further_mutex_groups,
		bool quietMode	
		){
	if (!quietMode) std::cerr << "Writing instance to output." << std::endl;

	std::set<Fact> reachableFactsSet(reachableFacts.begin(), reachableFacts.end());


	// assign fact numbers
	int fn = 0;
	for (Fact & fact : reachableFacts) fact.outputNo = -1;

	std::vector<int> orderedFacts;

	int number_of_sas_groups = 0;
	// elements of sas groups have to be handled together
	for (size_t sas_g = 0; sas_g < sas_groups.size(); sas_g++){
		number_of_sas_groups++;
		for (int elem : sas_groups[sas_g]){
			Fact & f = reachableFacts[elem];
			assert(!prunedFacts[f.groundedNo]);
			assert(!domain.predicates[f.predicateNo].guard_for_conditional_effect);
			f.outputNo = fn++; // assign actual index to fact
			orderedFacts.push_back(elem);
		}
	}

	DEBUG(std::cout << fn << " of " << facts << " facts covered by SAS+ groups" << std::endl);

	for (Fact & fact : reachableFacts){
		if (fact.outputNo != -1) continue; // is covered by sas+ 
		if (prunedFacts[fact.groundedNo]) continue;
		if (domain.predicates[fact.predicateNo].guard_for_conditional_effect) continue;
		fact.outputNo = fn++; // assign actual index to fact
		orderedFacts.push_back(fact.groundedNo);
		number_of_sas_groups++; // these variables are groups by themselves
	}


	pout << ";; #state features" << std::endl;
	pout << facts << std::endl;
	for (int factID : orderedFacts){
		Fact & fact = reachableFacts[factID];
		if (prunedFacts[fact.groundedNo]) continue;
		if (domain.predicates[fact.predicateNo].guard_for_conditional_effect) continue;
		pout << domain.predicates[fact.predicateNo].name << "[";
		for (unsigned int i = 0; i < fact.arguments.size(); i++){
			if (i) pout << ",";
			pout << domain.constants[fact.arguments[i]];
		}
		pout << "]" << std::endl;
	}
	pout << std::endl;


	pout << ";; Mutex Groups" << std::endl;
	pout << number_of_sas_groups << std::endl;
	
	int current_fact_position = 0;
	int variable_number = 0;
	for (size_t sas_g = 0; sas_g < sas_groups.size(); sas_g++){
		int group_size = sas_groups[sas_g].size();

		pout << current_fact_position << " " << current_fact_position + group_size - 1 << " var" << std::to_string(++variable_number) << std::endl;
		current_fact_position += group_size;
	}
	
	
	// as long as we can't output true SAS+, we simply output the fact list again
	for (int factID : orderedFacts){
		Fact & fact = reachableFacts[factID];
		if (prunedFacts[fact.groundedNo]) continue;
		if (domain.predicates[fact.predicateNo].guard_for_conditional_effect) continue;
		// is part of mutex group?
		if (fact.outputNo <= current_fact_position) continue;
		
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

	// gather conditional effect actions
	std::map<int,GroundedTask> ce_effects;
	for (GroundedTask & task : reachableTasks){
		if (!domain.tasks[task.taskNo].isCompiledConditionalEffect) continue;
		if (task.taskNo >= domain.nPrimitiveTasks || prunedTasks[task.groundedNo]) continue;

		int guardID = -1;
		for (int & prec : task.groundedPreconditions)
			if (domain.predicates[reachableFacts[prec].predicateNo].guard_for_conditional_effect){
				guardID = prec;
				break;
			}

		if (ce_effects.count(guardID)){
			std::cerr << "Multiple assigned conditional effect groundings. I thought this cannot happen ..." << std::endl;
			exit(-1);
		}

		ce_effects[guardID] = task;
	}

	pout << ";; Actions" << std::endl;
	pout << primTask << std::endl; 
	int ac = 0;
	for (GroundedTask & task : reachableTasks){
		if (domain.tasks[task.taskNo].isCompiledConditionalEffect) continue;
		if (task.taskNo >= domain.nPrimitiveTasks || prunedTasks[task.groundedNo]) continue;
		//pout << domain.tasks[task.taskNo].name << std::endl;

		task.outputNo = ac++;
		
		int costs = domain.tasks[task.taskNo].computeGroundCost(task,init_functions_map);
		pout << costs << std::endl;
		
		for (int & prec : task.groundedPreconditions)
			if (!prunedFacts[prec])
				pout << reachableFacts[prec].outputNo << " ";
		pout << -1 << std::endl;

		std::vector<int> ce_guards;
		for (int & add : task.groundedAddEffects)
			if (domain.predicates[reachableFacts[add].predicateNo].guard_for_conditional_effect)
				ce_guards.push_back(add);
			else {	
				if (!prunedFacts[add])
					pout << 0 << " " << reachableFacts[add].outputNo << "  ";
			}


		// compute conditional effects
		std::vector<std::pair<std::vector<int>,int>> addCEs;
		std::vector<std::pair<std::vector<int>,int>> delCEs;

		for (int guard : ce_guards){
			if (!ce_effects.count(guard)) continue; // CE condition might be unreachable
			GroundedTask ce_task = ce_effects[guard];

			int effectID; bool isAdd;
			if (ce_task.groundedAddEffects.size()){
				assert(ce_task.groundedDelEffects.size() == 0);
				assert(ce_task.groundedAddEffects.size() == 1);
				effectID = ce_task.groundedAddEffects[0];
				isAdd = true;
			} else {
				assert(ce_task.groundedDelEffects.size() == 1);
				assert(ce_task.groundedAddEffects.size() == 0);
				effectID = ce_task.groundedDelEffects[0];
				isAdd = false;
			}

			if (prunedFacts[effectID]) continue; // this effect is not necessary

			std::vector<int> nonPrunedPrecs;
			for (int & prec : ce_task.groundedPreconditions)
				if (!domain.predicates[reachableFacts[prec].predicateNo].guard_for_conditional_effect) // don't output the guard
					if (!prunedFacts[prec])
						nonPrunedPrecs.push_back(reachableFacts[prec].outputNo);

			
			if (isAdd)
				addCEs.push_back(std::make_pair(nonPrunedPrecs, reachableFacts[effectID].outputNo));
			else
				delCEs.push_back(std::make_pair(nonPrunedPrecs, reachableFacts[effectID].outputNo));

		}

		// output conditional adds
		for (auto ce : addCEs){
			pout  << ce.first.size();
			for (int c : ce.first) pout << " " << c;
			pout << " " << ce.second << "  ";
		}

		pout << -1 << std::endl;
		
		for (int & del : task.groundedDelEffects)
			if (!prunedFacts[del])
				pout << 0 << " " << reachableFacts[del].outputNo << "  ";

		// output conditional dels
		for (auto ce : delCEs){
			pout << ce.first.size();
			for (int c : ce.first) pout << " " << c;
			pout << " " << ce.second << "  ";
		}

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
		if (domain.tasks[task.taskNo].isCompiledConditionalEffect) continue;
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
		std::sort(orderings.begin(), orderings.end());
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


std::string toHDDLName(std::string name){
	std::string result = "";
	for (size_t i = 0; i < name.size(); i++){
		char c = name[i];

		if (c == '_' && !i) result += "US";

		if (c == '<') result += "LA_";
		else if (c == '>') result += "RA_";
		else if (c == '[') result += "LB_";
		else if (c == ']') result += "RB_";
		else if (c == ';') result += "SEM_";
		else if (c == ',') result += "COM_";
		else if (c == '+') result += "PLUS_";
		else if (c == '-') result += "MINUS_";
		else result += c;
	}

	return result;
}


void write_grounded_HTN_to_HDDL(std::ostream & dout, std::ostream & pout, const Domain & domain, const Problem & problem,
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

	std::map<Fact,int> init_functions_map;
	for (auto & init_function_literal : problem.init_functions){
		init_functions_map[init_function_literal.first] = init_function_literal.second;
	}

	bool domainHasActionCosts = false;
	for (GroundedTask & task : reachableTasks){
		if (task.taskNo >= domain.nPrimitiveTasks || prunedTasks[task.groundedNo]) continue;
		if (domain.tasks[task.taskNo].isCompiledConditionalEffect) continue;
		
		if (domain.tasks[task.taskNo].computeGroundCost(task,init_functions_map) != 1){
			domainHasActionCosts = true;
			break;
		}
	}


	// gather conditional effect actions
	std::map<int,GroundedTask> ce_effects;
	for (GroundedTask & task : reachableTasks){
		if (!domain.tasks[task.taskNo].isCompiledConditionalEffect) continue;
		if (task.taskNo >= domain.nPrimitiveTasks || prunedTasks[task.groundedNo]) continue;

		int guardID = -1;
		for (int & prec : task.groundedPreconditions)
			if (domain.predicates[reachableFacts[prec].predicateNo].guard_for_conditional_effect){
				guardID = prec;
				break;
			}

		if (ce_effects.count(guardID)){
			std::cerr << "Multiple assigned conditional effect groundings. I thought this cannot happen ..." << std::endl;
			exit(-1);
		}

		ce_effects[guardID] = task;
	}


	dout << "(define (domain d)" << std::endl;
	dout << "  (:requirements :typing)" << std::endl;
	
	dout << std::endl;

	std::map<int,std::string> factname;
	std::map<int,std::string> taskname;
	
	bool somePredicate = false;
	for (Fact & fact : reachableFacts){
		if (prunedFacts[fact.groundedNo]) continue;
		if (domain.predicates[fact.predicateNo].guard_for_conditional_effect) continue;
		somePredicate = true; break;
	}

	dout << "  (:predicates" << std::endl;
	if (!somePredicate){
		dout << "    (DUMMY)" << std::endl; // the Java PANDA cannot parse domains without predicates
	}
	for (Fact & fact : reachableFacts){
		if (prunedFacts[fact.groundedNo]) continue;
		if (domain.predicates[fact.predicateNo].guard_for_conditional_effect) continue;
		
		dout << "    (";

		std::string name = toHDDLName(domain.predicates[fact.predicateNo].name);
		for (unsigned int i = 0; i < fact.arguments.size(); i++){
			name += "_";
			name += toHDDLName(domain.constants[fact.arguments[i]]);
		}

		factname[fact.groundedNo] = name;
		dout << name << ")" << std::endl;
	}
	dout << "  )" << std::endl;

	dout << std::endl;


	if (domainHasActionCosts){
		dout << "  (:functions" << std::endl;
		dout << "    (total-cost) - number" << std::endl;
		dout << "  )" << std::endl;
		dout << std::endl;
	}



	for (GroundedTask & task : reachableTasks){
		if (prunedTasks[task.groundedNo]) continue;

		// construct task name
		std::string name = toHDDLName(domain.tasks[task.taskNo].name);
		// only output the original variables
		for (unsigned int i = 0; i < domain.tasks[task.taskNo].number_of_original_variables; i++){
			name += "_" + toHDDLName(domain.constants[task.arguments[i]]);
		}
		taskname[task.groundedNo] = name;

		// if this one is not abstract, continue
		if (task.taskNo < domain.nPrimitiveTasks) continue;
		
		dout << "  (:task " << taskname[task.groundedNo] << " :parameters ())" << std::endl;
	}

	dout << std::endl;

	// methods

	for (auto & method : reachableMethods){
		if (prunedMethods[method.groundedNo]) continue;
		// output their name
		dout << "  (:method ";
		dout << toHDDLName(domain.decompositionMethods[method.methodNo].name) << std::endl;
		dout << "   :parameters ()" << std::endl;
		
		GroundedTask & at = reachableTasks[method.groundedAddEffects[0]];
		dout << "    :task (" << taskname[at.groundedNo] << ")" << std::endl;
		
		std::map<int,int> subTaskIndexToOutputIndex;
		// output subtasks in their topological ordering
		dout << "    :subtasks (and" << std::endl;
		for (size_t outputIndex = 0; outputIndex < method.preconditionOrdering.size(); outputIndex++){
			int subtaskIndex = method.preconditionOrdering[outputIndex];
			subTaskIndexToOutputIndex[subtaskIndex] = outputIndex;
			
			GroundedTask & task	= reachableTasks[method.groundedPreconditions[subtaskIndex]];
			dout << "      (t" << outputIndex << " (" << taskname[task.groundedNo] << "))" << std::endl;
		}
		dout << "    )" << std::endl;

		auto orderings = domain.decompositionMethods[method.methodNo].orderingConstraints;
		std::sort(orderings.begin(), orderings.end());
		auto last = std::unique(orderings.begin(), orderings.end());
		orderings.erase(last, orderings.end());

		
		if (orderings.size()){
			// ordering of subtasks
			dout << "    :ordering (and" << std::endl;
			for (auto & order : orderings){
				dout << "      (t" << subTaskIndexToOutputIndex[order.first];
		   		dout << " < t" << subTaskIndexToOutputIndex[order.second] << ")" << std::endl;
			}
			dout << "    )" << std::endl;
		}
		dout << "  )" << std::endl << std::endl;
	}


	for (GroundedTask & task : reachableTasks){
		if (task.taskNo >= domain.nPrimitiveTasks || prunedTasks[task.groundedNo]) continue;
		if (domain.tasks[task.taskNo].isCompiledConditionalEffect) continue;
		
		dout << "  (:action " << taskname[task.groundedNo] << std::endl;
		dout << "   :parameters ()" << std::endl;
		

		std::vector<std::string> precs;
		std::vector<std::string> adds;
		std::vector<std::string> dels;
		for (int & prec : task.groundedPreconditions)
			if (!prunedFacts[prec])
				precs.push_back(factname[prec]);

		std::vector<int> ce_guards;
		for (int & add : task.groundedAddEffects)
			if (domain.predicates[reachableFacts[add].predicateNo].guard_for_conditional_effect)
				ce_guards.push_back(add);
			else {	
				if (!prunedFacts[add])
					adds.push_back(factname[add]);
			}

		for (int & del : task.groundedDelEffects)
			if (!prunedFacts[del])
				dels.push_back(factname[del]);



		// compute conditional effects
		std::vector<std::pair<std::vector<std::string>,std::string>> addCEs;
		std::vector<std::pair<std::vector<std::string>,std::string>> delCEs;

		for (int guard : ce_guards){
			if (!ce_effects.count(guard)) continue; // CE condition might be unreachable
			GroundedTask ce_task = ce_effects[guard];

			int effectID; bool isAdd;
			if (ce_task.groundedAddEffects.size()){
				assert(ce_task.groundedDelEffects.size() == 0);
				assert(ce_task.groundedAddEffects.size() == 1);
				effectID = ce_task.groundedAddEffects[0];
				isAdd = true;
			} else {
				assert(ce_task.groundedDelEffects.size() == 1);
				assert(ce_task.groundedAddEffects.size() == 0);
				effectID = ce_task.groundedDelEffects[0];
				isAdd = false;
			}

			if (prunedFacts[effectID]) continue; // this effect is not necessary

			std::vector<std::string> nonPrunedPrecs;
			for (int & prec : ce_task.groundedPreconditions)
				if (!domain.predicates[reachableFacts[prec].predicateNo].guard_for_conditional_effect) // don't output the guard
					if (!prunedFacts[prec])
						nonPrunedPrecs.push_back(factname[prec]);

			if (nonPrunedPrecs.size()){
				if (isAdd)
					addCEs.push_back(std::make_pair(nonPrunedPrecs, factname[effectID]));
				else
					delCEs.push_back(std::make_pair(nonPrunedPrecs, factname[effectID]));
			} else {
				if (isAdd)
					adds.push_back(factname[effectID]);
				else
					dels.push_back(factname[effectID]);
			}
		}



		if (precs.size()){
			dout << "    :precondition (and" << std::endl;
			for (std::string p : precs)
				dout << "      (" << p << ")" << std::endl;
			dout << "    )" << std::endl;
		}

		int costs = domain.tasks[task.taskNo].computeGroundCost(task,init_functions_map);
		if ((adds.size() + dels.size() + addCEs.size() + delCEs.size()) || (domainHasActionCosts && costs)){
			dout << "    :effect (and" << std::endl;

			if (domainHasActionCosts && costs){
				dout << "      (increase (total-cost) " << costs << ")" << std::endl;
			}
		

			// add and conditional add
			for (std::string a : adds)
				dout << "      (" << a << ")" << std::endl;
			for (auto ce : addCEs){
				dout << "      (when (and";
				for (std::string p : ce.first)
					dout << " (" << p << ")";
				dout << ") (" << ce.second << "))" << std::endl;
			}
			
			// delete and conditional delete
			for (std::string d : dels)
				dout << "      (not (" << d << "))" << std::endl;
			for (auto ce : delCEs){
				dout << "      (when (and";
				for (std::string p : ce.first)
					dout << " (" << p << ")";
				dout << ") (not (" << ce.second << ")))" << std::endl;
			}

			dout << "    )" << std::endl;
		}
		
		dout << "  )" << std::endl << std::endl;
	}

	dout << ")" << std::endl;


	// problem
	pout << "(define" << std::endl;
	pout << "  (problem p)" << std::endl;
	pout << "  (:domain d)" << std::endl;

	pout << "  (:htn" << std::endl;
	pout << "    :parameters ()" << std::endl;
	pout << "    :subtasks (and (" << toHDDLName("__top") << "))" << std::endl;
	pout << "  )" << std::endl;

	pout << "  (:init" << std::endl;
	std::set<int> initFacts; // needed for efficient goal checking
	std::set<int> initFactsPruned; // needed for efficient checking of pruned facts in the goal
	std::set<Fact> reachableFactsSet(reachableFacts.begin(), reachableFacts.end());

	for (const Fact & f : problem.init){
		int groundNo = reachableFactsSet.find(f)->groundedNo;
		if (prunedFacts[groundNo]){
			initFactsPruned.insert(groundNo);
			continue;
		}
		pout << "    (" << factname[groundNo] << ")" << std::endl;
		initFacts.insert(groundNo);
	}
	pout << "  )" << std::endl;
	
	
	
	std::vector<std::string> goalFacts;
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
		goalFacts.push_back(factname[it->groundedNo]);
	}

	if (goalFacts.size()){
		pout << "  (:goal (and" << std::endl;
		for (std::string gf : goalFacts)
			pout << "    (" << gf << ")" << std::endl;
		pout << "  ))" << std::endl;
	}
	pout << ")" << std::endl;

}
