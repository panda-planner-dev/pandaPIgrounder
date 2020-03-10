#include <iomanip>
#include <iostream>
#include <ostream>
#include <map>
#include <algorithm>
#include <unistd.h>
#include <cassert>

#include "output.h"
#include "debug.h"


void instantiate_cover_pruned_dfs(std::map<int,int> & cover_pruned_precs, std::map<int,std::vector<int>> & cover_pruned, std::vector<int> & cover_pruned_facts, int curpos, std::vector<int> & current_assignment, std::vector<std::vector<int>> & all_assignments){
	if (curpos == cover_pruned_facts.size()){
		all_assignments.push_back(current_assignment);
		return;
	}

	int cur_f = cover_pruned_facts[curpos];
	for (const int & v : cover_pruned[cur_f]){
		current_assignment[cover_pruned_precs[cur_f]] = v;
		instantiate_cover_pruned_dfs(cover_pruned_precs,cover_pruned,cover_pruned_facts,curpos+1, current_assignment, all_assignments);
	}
}

std::vector<std::vector<int>> instantiate_cover_pruned(std::map<int,int> & cover_pruned_precs, std::map<int,std::vector<int>> & cover_pruned){

	std::vector<int> cover_pruned_facts;
	for (const auto & entry : cover_pruned_precs) cover_pruned_facts.push_back(entry.first);

	std::vector<int> current_assignment (cover_pruned_facts.size());
	std::vector<std::vector<int>> all_assignments;

	instantiate_cover_pruned_dfs(cover_pruned_precs,cover_pruned,cover_pruned_facts,0,current_assignment, all_assignments);

	return all_assignments;
}



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
		std::unordered_set<int> initFacts,
		std::unordered_set<int> initFactsPruned,
		std::unordered_set<Fact> reachableFactsSet,
		std::vector<std::unordered_set<int>> sas_groups,
		std::vector<std::unordered_set<int>> further_mutex_groups,
		std::vector<bool> & sas_variables_needing_none_of_them,
		bool compileNegativeSASVariables,
		sas_delete_output_mode sas_mode,
		bool quietMode	
		){
	if (!quietMode) std::cerr << "Writing instance to output." << std::endl;

	// find candidates for fact elimination by duplication
	std::map<int,std::vector<int>> cover_pruned;
	std::unordered_set<int> pruned_sas_groups;
	if (compileNegativeSASVariables){
		for (const std::unordered_set<int> & m_g : further_mutex_groups){
			if (m_g.size() != 2) continue; // only pairs of facts are eligible
			int fact_in_large_group = -1;
			int og_large = -1;
			int other_fact = -1;
			int og_small = -1;
			bool two_large = false;
			for (const int & elem : m_g){
				bool found = false;
				for (size_t ogID = 0; ogID < sas_groups.size(); ogID++){
					const std::unordered_set<int> & og = sas_groups[ogID];
					if (!og.count(elem)) continue;
					found = true;
					if (og.size() == 1) {
						other_fact = elem;
						og_small = ogID;
						continue; // contains only this fact, i.e. is artificial
					}

					if (fact_in_large_group != -1){
						two_large = true;
						break;
					}

					fact_in_large_group = elem;
					og_large = ogID;
				}
				if (two_large) break;
				if (!found) other_fact = elem;
			}
			if (two_large) continue;
			if (fact_in_large_group == -1) continue;

			std::vector<int> other_values;
			for (const int & val : sas_groups[og_large]) if (val != fact_in_large_group)
				other_values.push_back(val);
			// might need a none-of-those
			if (sas_variables_needing_none_of_them[og_large]) other_values.push_back(-1);
			cover_pruned[other_fact] = other_values;
			pruned_sas_groups.insert(og_small);

			DEBUG(std::cout << "Fact " << other_fact << " is eligible for pruning as opposite of " << fact_in_large_group << std::endl;
				Fact & f1 = reachableFacts[other_fact];
				std::cout << "Pruning: " << domain.predicates[f1.predicateNo].name << "[";
				for (unsigned int i = 0; i < f1.arguments.size(); i++){
					if (i) std::cout << ",";
					std::cout << domain.constants[f1.arguments[i]];
				}
				std::cout << "]" << std::endl;
				Fact & f2 = reachableFacts[fact_in_large_group];
				std::cout << "Negation of " << domain.predicates[f2.predicateNo].name << "[";
				for (unsigned int i = 0; i < f2.arguments.size(); i++){
					if (i) std::cout << ",";
					std::cout << domain.constants[f2.arguments[i]];
				}
				std::cout << "]" << std::endl;
	
				std::cout << "Possible facts are:";
				for (int x : other_values) std::cout << " " << x;
				std::cout << std::endl;
					);
		}
	}

	DEBUG(std::cout << "Cover Pruned size = " << cover_pruned.size() << std::endl);

	// assign fact numbers
	int fn = 0;
	for (Fact & fact : reachableFacts) fact.outputNo = -1;

	std::vector<int> orderedFacts;

	int number_of_sas_groups = 0;
	// elements of sas groups have to be handled together
	for (size_t sas_g = 0; sas_g < sas_groups.size(); sas_g++){
		if (pruned_sas_groups.count(sas_g)) continue; // is obsolete
		
		number_of_sas_groups++;
		for (int elem : sas_groups[sas_g]){
			Fact & f = reachableFacts[elem];
			assert(!prunedFacts[f.groundedNo]);
			assert(!domain.predicates[f.predicateNo].guard_for_conditional_effect);
			f.outputNo = fn++; // assign actual index to fact
			orderedFacts.push_back(elem);
		}
		if (sas_variables_needing_none_of_them[sas_g]){
			fn++;
			orderedFacts.push_back(-1);
		}
	}


	DEBUG(std::cout << fn << " of " << facts << " facts covered by SAS+ groups" << std::endl);

	// to distinguish between SAS+ and STRIPS facts later on
	const int number_of_sas_covered_facts = fn;

	// facts that are not translated into SAS+
	for (Fact & fact : reachableFacts){
		if (fact.outputNo != -1) continue; // is covered by sas+ 
		if (prunedFacts[fact.groundedNo]) continue;
		if (domain.predicates[fact.predicateNo].guard_for_conditional_effect) continue;
		if (cover_pruned.count(fact.groundedNo)) continue; // removed
		fact.outputNo = fn++; // assign actual index to fact
		orderedFacts.push_back(fact.groundedNo);
		number_of_sas_groups++; // these variables are groups by themselves
	}


	pout << ";; #state features" << std::endl;
	pout << fn << std::endl;
	for (int factID : orderedFacts){
		// artificial member for SAS groups
		if (factID == -1){
			pout << "none-of-them" << std::endl;
			continue;
		}
		// real fact
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
	std::vector<int> none_of_them_per_sas_group (sas_groups.size());
	for (size_t sas_g = 0; sas_g < sas_groups.size(); sas_g++){
		if (pruned_sas_groups.count(sas_g)) continue;
		int group_size = sas_groups[sas_g].size() + (sas_variables_needing_none_of_them[sas_g] ? 1 : 0);
		if (sas_variables_needing_none_of_them[sas_g])
			none_of_them_per_sas_group[sas_g] = current_fact_position + group_size - 1;
		else
			none_of_them_per_sas_group[sas_g] = -1;

		pout << current_fact_position << " ";
		pout << current_fact_position + group_size - 1;
	   	pout << " var" << std::to_string(++variable_number) << std::endl;
		current_fact_position += group_size;
	}
	
	
	// these are the facts, that do not belong to a SAS+ group, we have to output them on their own.
	for (int factID : orderedFacts){
		if (factID == -1) continue;
		Fact & fact = reachableFacts[factID];
		if (prunedFacts[fact.groundedNo]) continue;
		if (domain.predicates[fact.predicateNo].guard_for_conditional_effect) continue;
		// is part of mutex group? or pruned? Then it will still have -1
		if (fact.outputNo < current_fact_position) continue;
		
		pout << fact.outputNo << " ";
		pout << fact.outputNo << " ";
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
		
		int costs = domain.tasks[task.taskNo].computeGroundCost(task,init_functions_map);
		
		std::map<int,int> cover_pruned_precs;
		// find facts that were cover pruned
		for (int & prec : task.groundedPreconditions){
			if (cover_pruned.count(prec)){
				int pos = cover_pruned_precs.size();
				cover_pruned_precs[prec] = pos;
			}
		}
		
		// analyse precondition
		std::vector<int> prec_out;
		for (int & prec : task.groundedPreconditions) if (!prunedFacts[prec]){
			if (! cover_pruned_precs.count(prec))
				prec_out.push_back(reachableFacts[prec].outputNo);
			else
				prec_out.push_back(-cover_pruned_precs[prec]-1); // marker
		}

		std::vector<std::pair<std::vector<int>,int>> add_out;
		std::vector<std::pair<std::vector<int>,int>> del_out;

		std::vector<int> ce_guards;
		std::vector<int> _empty;
		for (int & add : task.groundedAddEffects)
			if (domain.predicates[reachableFacts[add].predicateNo].guard_for_conditional_effect)
				ce_guards.push_back(add);
			else {	
				if (!prunedFacts[add]){
					add_out.push_back(std::make_pair(_empty,reachableFacts[add].outputNo));
				}
			}

		for (const int & sas_g : task.noneOfThoseEffect){
			assert(none_of_them_per_sas_group[sas_g] != -1);
			add_out.push_back(std::make_pair(_empty,none_of_them_per_sas_group[sas_g])); 
		}

		for (int & del : task.groundedDelEffects) if (!prunedFacts[del]){
			if (sas_mode == SAS_NONE && reachableFacts[del].outputNo < number_of_sas_covered_facts) continue; // if the user want's it, don't output delete effects on SAS variables
			del_out.push_back(std::make_pair(_empty,reachableFacts[del].outputNo));
		}


		// compute conditional effects
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
			if (sas_mode == SAS_NONE && reachableFacts[effectID].outputNo < number_of_sas_covered_facts) continue; // if the user want's it, don't output delete effects on SAS variables

			std::vector<int> nonPrunedPrecs;
			for (int & prec : ce_task.groundedPreconditions)
				if (!domain.predicates[reachableFacts[prec].predicateNo].guard_for_conditional_effect) // don't output the guard
					if (!prunedFacts[prec]){
						if (!cover_pruned.count(prec))
							nonPrunedPrecs.push_back(reachableFacts[prec].outputNo);
						else {
							int pos;
							if (cover_pruned_precs.count(prec)) // might also be in prec, or coordinated between conditions ...
								pos = cover_pruned_precs[prec];
							else
								pos = cover_pruned_precs.size();

							cover_pruned_precs[prec] = pos;

							nonPrunedPrecs.push_back(-pos-1); // marker
						}
					}

			
			if (isAdd)
				add_out.push_back(std::make_pair(nonPrunedPrecs, reachableFacts[effectID].outputNo));
			else
				del_out.push_back(std::make_pair(nonPrunedPrecs, reachableFacts[effectID].outputNo));

		}
		
		
		
		if (cover_pruned_precs.size() == 0)
			task.outputNo = ac;
		else 
			task.outputNo = -2; // marker for additionally needed task

		for (const std::vector<int> cover_assignment : instantiate_cover_pruned(cover_pruned_precs, cover_pruned)){
			///////////////////////////// ACTUAL OUTPUT
			task.outputNosForCover.push_back(ac++);
			pout << costs << std::endl;
			// preconditions
			for (const int & prec : prec_out)
				if (prec >= 0)
					pout << prec << " ";
				else
					pout << reachableFacts[cover_assignment[-prec-1]].outputNo << " ";

			pout << -1 << std::endl;

			// output add effects
			for (const auto & add : add_out){
				pout << add.first.size();
				for (const int & p : add.first) 
					if (p >= 0)
						pout << p << " ";
					else
						pout << reachableFacts[cover_assignment[-p-1]].outputNo << " ";
				pout << " " << add.second << "  ";
			}
			pout << -1 << std::endl;

			// output del effects
			for (const auto & del : del_out){
				pout << del.first.size();
				for (const int & p : del.first)
					if (p >= 0)
						pout << p << " ";
					else
						pout << reachableFacts[cover_assignment[-p-1]].outputNo << " ";
				pout << " " << del.second << "  ";
			}
			pout << -1 << std::endl;
		}
	}
	
	//exit(-2);


	pout << std::endl << ";; initial state" << std::endl;
	for (size_t sas_g = 0; sas_g < sas_groups.size(); sas_g++){
		bool didOutput = false;
		for (const int & f : sas_groups[sas_g]) if (initFacts.count(f)){
			pout << reachableFacts[f].outputNo << " ";
			didOutput = true;
		}
		if (!didOutput){
			assert(none_of_them_per_sas_group[sas_g] != -1);
			pout << none_of_them_per_sas_group[sas_g] << " ";
		}
	}
	

	for (int fID : initFacts){
		int outputNo = reachableFacts[fID].outputNo;
		if (outputNo < number_of_sas_covered_facts) continue; // is a sas+ fact
		pout << outputNo << " ";
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
