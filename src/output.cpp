#include <iomanip>
#include <iostream>
#include <ostream>
#include <map>
#include <algorithm>
#include <unistd.h>
#include <cassert>

#include "output.h"
#include "debug.h"
#include "util.h"


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


void write_task_name(std::ostream & pout, const Domain & domain, GroundedTask & task){
	pout << domain.tasks[task.taskNo].name << "[";
	// only output the original variables
	for (unsigned int i = 0; i < domain.tasks[task.taskNo].number_of_original_variables; i++){
		if (i) pout << ",";
		pout << domain.constants[task.arguments[i]];
	}
	pout << "]";
}



void write_grounded_HTN(std::ostream & pout, const Domain & domain, const Problem & problem,
		std::vector<Fact> & reachableFacts,
		std::vector<GroundedTask> & reachableTasks,
		std::vector<GroundedMethod> & reachableMethods,
		std::vector<bool> & prunedTasks,
		std::vector<bool> & prunedFacts,
		std::vector<bool> & prunedMethods,
		std::unordered_set<int> initFacts,
		std::unordered_set<int> initFactsPruned,
		std::unordered_set<Fact> reachableFactsSet,
		std::vector<std::unordered_set<int>> sas_groups,
		std::vector<std::unordered_set<int>> further_strict_mutex_groups,
		std::vector<std::unordered_set<int>> further_mutex_groups,
		std::vector<std::unordered_set<int>> invariants,
		std::vector<bool> & sas_variables_needing_none_of_them,
		grounding_configuration & config
		){
	if (!config.quietMode) std::cerr << "Writing instance to output." << std::endl;

	// determine whether we need an additional noop for empty methods
	bool contains_empty_method = false;
	if (config.noopForEmptyMethods) for (auto & method : reachableMethods){
		if (prunedMethods[method.groundedNo]) continue;
		if (method.preconditionOrdering.size() == 0){
			contains_empty_method = true;
			DEBUG(std::cout << "Instance contains empty method. Adding noop." << std::endl);
			break;
		}
	}

	std::unordered_set<int> goal_facts;
	for (const Fact & f : problem.goal){
		auto it = reachableFactsSet.find(f);
		if (it != reachableFactsSet.end())
			goal_facts.insert(it->groundedNo);
	}

	// find candidates for fact elimination by duplication
	std::map<int,std::vector<int>> cover_pruned;
	std::unordered_set<int> pruned_sas_groups;
	for (const std::unordered_set<int> & m_g : further_strict_mutex_groups){
		if (m_g.size() != 2) continue; // only pairs of facts are eligible
		bool is_in_goal = false;
		for (int x : m_g) is_in_goal |= goal_facts.count(x);
		if (is_in_goal) continue; // do not prune facts that occur in the goal
		int fact_in_large_group = -1;
		int og_large = -1;
		int other_fact = -1;
		int second_fact_in_small_group = -1;
		int og_small = -1;
		bool two_large = false;
		for (const int & elem : m_g){
			bool found = false;
			for (size_t ogID = 0; ogID < sas_groups.size(); ogID++){
				const std::unordered_set<int> & og = sas_groups[ogID];
				if (!og.count(elem)) continue;
				found = true;
				if (og.size() + sas_variables_needing_none_of_them[ogID] <= 2) {   // this element if part of the mutex is member of a size <= 2 SAS+ group
					// we can thus remove this element with the other values from the large group
					// and if there is a second value in this sas group, we can replace it with the other element of this mutex (i.e. fact_in_large_group)
					other_fact = elem;
					og_small = ogID;
					if (og.size() == 2)
						for (const int & ogElem : og) if (ogElem != elem) second_fact_in_small_group = ogElem;

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
		if (cover_pruned.count(other_fact)) continue; // if the other fact is already pruned don't
		if (prunedFacts[other_fact]) continue;

		std::vector<int> other_values;
		for (const int & val : sas_groups[og_large]) if (val != fact_in_large_group)
			other_values.push_back(val);
		
		if (sas_variables_needing_none_of_them[og_large]) other_values.push_back(-og_large-1);
	
		// always use implications, where there is just one other option
		if (other_values.size() != 1 && !config.compileNegativeSASVariables) continue;
		
		// might need a none-of-those
		cover_pruned[other_fact] = other_values;
		if (og_small != -1) {
			pruned_sas_groups.insert(og_small);
			if (second_fact_in_small_group != -1){
				std::vector<int> mainValue;
				mainValue.push_back(fact_in_large_group);
				cover_pruned[second_fact_in_small_group] = mainValue;
			}
		}

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
			
			if (og_small != -1)	{
				std::cout << "Removing SAS+ group: " << og_small << std::endl;
				if (second_fact_in_small_group){
					std::cout << "SAS+ group has a second element (" << second_fact_in_small_group << ") which will be identical to " << fact_in_large_group << std::endl;
					Fact & f3 = reachableFacts[second_fact_in_small_group];
					std::cout << "Pruning: " << domain.predicates[f3.predicateNo].name << "[";
					for (unsigned int i = 0; i < f3.arguments.size(); i++){
						if (i) std::cout << ",";
						std::cout << domain.constants[f3.arguments[i]];
					}
				} 
			}

            std::cout << "Possible facts are:";
            for (int x : other_values) {
                    Fact & of = reachableFacts[x];
                    std::cout << " " << domain.predicates[of.predicateNo].name << "[";
                    for (unsigned int i = 0; i < of.arguments.size(); i++){
                            if (i) std::cout << ",";
                            std::cout << domain.constants[of.arguments[i]];
                    }
                    std::cout << "]";
            }
            std::cout << std::endl;
				);
	}
	DEBUG(std::cout << "Cover Pruned size = " << cover_pruned.size() << std::endl);

	// assign fact numbers
	int fn = 0;
	for (Fact & fact : reachableFacts) fact.outputNo = -1;

	std::vector<int> orderedFacts;
	std::vector<std::pair<int,int>> per_sas_fact_from_to;
	std::vector<int> sas_g_per_fact;

	int number_of_sas_groups = 0;
	// elements of sas groups have to be handled together
	for (size_t sas_g = 0; sas_g < sas_groups.size(); sas_g++){
		if (pruned_sas_groups.count(sas_g)) continue; // is obsolete
		
		number_of_sas_groups++;
		int from = fn;
		for (int elem : sas_groups[sas_g]){
			Fact & f = reachableFacts[elem];
			if (prunedFacts[f.groundedNo]) std::cout << "FAIL " << f.groundedNo << std::endl;
			assert(!prunedFacts[f.groundedNo]);
			assert(!domain.predicates[f.predicateNo].guard_for_conditional_effect);
			f.outputNo = fn++; // assign actual index to fact
			orderedFacts.push_back(elem);
			sas_g_per_fact.push_back(sas_g);
		}
		if (sas_variables_needing_none_of_them[sas_g]){
			fn++;
			orderedFacts.push_back(-sas_g-1); // to get the correct fact
			sas_g_per_fact.push_back(sas_g);
		}
		int to = fn-1;
		for (int x = from; x <= to; x++)
			per_sas_fact_from_to.push_back(std::make_pair(from,to));
	}

	
	DEBUG(
			int facts = 0; for (bool b : prunedFacts) if (!b) facts++;
			std::cout << fn << " of " << facts << " facts covered by SAS+ groups" << std::endl
			);

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
		if (factID < 0){
			pout << "none-of-them" << std::endl;
			continue;
		}
		// real fact
		Fact & fact = reachableFacts[factID];
		if (prunedFacts[fact.groundedNo]) continue;
		if (domain.predicates[fact.predicateNo].guard_for_conditional_effect) continue;

		DEBUG(std::cout << fact.outputNo << " ");

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
		if (factID < 0) continue;
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

	// further known mutex groups
	std::vector<std::unordered_set<int>> out_strict_mutexes;
	std::vector<std::unordered_set<int>> out_non_strict_mutexes;
	for (int mutexType = 0; mutexType < 2; mutexType++){
		std::vector<std::unordered_set<int>> & mutex_groups = (mutexType == 0) ? further_strict_mutex_groups : further_mutex_groups;
		std::vector<std::unordered_set<int>> & out_mutexes = (mutexType == 0) ? out_strict_mutexes : out_non_strict_mutexes;
		for (const auto & mgroup : mutex_groups){
			std::unordered_set<int> mutex;
			for (const int & elem : mgroup){
				Fact & fact = reachableFacts[elem];
				if (prunedFacts[elem]) continue;
				if (domain.predicates[fact.predicateNo].guard_for_conditional_effect) continue;
				if (cover_pruned.count(elem))
					for (const int & other : cover_pruned[elem]){
						if (other < 0)
							mutex.insert(none_of_them_per_sas_group[-other-1]);
						else
							mutex.insert(reachableFacts[other].outputNo);
					}
				else
					mutex.insert(reachableFacts[elem].outputNo);
			}

			if (mutex.size() < 2) continue; // mutexes with 0 or 1 element are irrelevant. They may appear due to pruning.

			bool hasSTRIPS = false;
			int sas_g_so_far = -1;
			bool multiple_sas_g = false;
			for (const int & elem : mutex){
				if (elem >= sas_g_per_fact.size()){
					hasSTRIPS = true;
					break;
				}

				int sas_g = sas_g_per_fact[elem];
				if (sas_g_so_far != -1 && sas_g_so_far != sas_g){
					multiple_sas_g = true;
					break;
				}
				sas_g_so_far = sas_g;
			}

			// if this is a subset of a SAS group, then just not output it. It is redundant.
			if (!hasSTRIPS && !multiple_sas_g && mutex.size() == sas_groups[sas_g_so_far].size() + sas_variables_needing_none_of_them[sas_g_so_far]) continue;

			out_mutexes.push_back(mutex);
		}
	}
	
	
	for (int mutexType = 0; mutexType < 2; mutexType++){
		if (mutexType == 0)
			pout << ";; further strict Mutex Groups" << std::endl;
		else
			pout << ";; further non strict Mutex Groups" << std::endl;
		
		std::vector<std::unordered_set<int>> & out_mutexes = (mutexType == 0) ? out_strict_mutexes : out_non_strict_mutexes;

		pout << out_mutexes.size() << std::endl;
		for (const auto & mutex : out_mutexes){
			for (const int & elem : mutex){
				assert(elem >= 0);
				pout << elem << " ";
			}
			pout << -1 << std::endl;
		}
		pout << std::endl;
	}


	// further known mutex groups
	pout << ";; known invariants" << std::endl;

	std::vector<std::unordered_set<int>> out_invariants;
	for (const auto & inv : invariants){
		// we can't handle negation over a cover pruned fact ..
		bool negation_over_cover_pruned = false;
		bool pruned_invariant_member = false;
		std::unordered_set<int> out_inv;

		for (const int & invElem : inv){
			if (invElem < 0 && cover_pruned.count(-invElem-1)){
				negation_over_cover_pruned = true;
				break;
			}

			int elem = invElem;
			if (invElem < 0) elem = -elem -1;
			if (prunedFacts[elem]) { pruned_invariant_member = true; break; }

			if (invElem < 0) {
				assert(!prunedFacts[elem]);
				out_inv.insert(-reachableFacts[elem].outputNo - 2);
			} else {
				if (cover_pruned.count(elem))
					for (const int & other : cover_pruned[elem]){
						if (other < 0) {
							out_inv.insert(none_of_them_per_sas_group[-other-1]);
						} else {
							assert(!prunedFacts[other]);
							out_inv.insert(reachableFacts[other].outputNo);
						}
					}
				else { 
					assert(!prunedFacts[elem]);
					out_inv.insert(reachableFacts[elem].outputNo);
				}
			}
		}

		if (negation_over_cover_pruned) continue;
		if (pruned_invariant_member) continue; // pruning a member may make a disjunctive invariant false ...
		bool isTrivial = false;
		bool hasNegativeOrHasSTRIPS = false;
		for (const int & elem : out_inv)
			if (out_inv.count(-elem-2)){
				isTrivial = true;
				break;
			} else if (elem < 0 || elem >= sas_g_per_fact.size())
				hasNegativeOrHasSTRIPS = true;
		if (isTrivial) continue; // ignore this invariant if it is trivial

		if (!hasNegativeOrHasSTRIPS){
			int sas_g_so_far = -1;
			bool multiple_sas_g = false;
			for (const int & elem : out_inv){
				int sas_g = sas_g_per_fact[elem];
				if (sas_g_so_far != -1 && sas_g_so_far != sas_g){
					multiple_sas_g = true;
					break;
				}
				sas_g_so_far = sas_g;
			}

			assert(sas_g_so_far >= 0);
			assert(sas_g_so_far < sas_groups.size());
			assert(sas_g_so_far < sas_variables_needing_none_of_them.size());
			if (!multiple_sas_g && out_inv.size() == sas_groups[sas_g_so_far].size() + sas_variables_needing_none_of_them[sas_g_so_far]) continue;
		}

		out_invariants.push_back(out_inv);
	}


	pout << out_invariants.size() << std::endl;
	for (const auto & inv : out_invariants){
		for (const int & elem : inv)
			pout << elem << " ";
		pout << -1 << std::endl;
	}
	pout << std::endl;


	////// OUTPUT OF ACTIONS
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
	
	// if we add extra actions for removal of facts, we might have to add more actions ...
	// so first gather them all, and then output
	std::vector<std::tuple<int,int,std::vector<int>,
						   std::vector<std::pair<std::vector<int>,int>>,
						   std::vector<std::pair<std::vector<int>,int>>,
						   std::vector<std::vector<int>>
							   >> output_actions;
	int number_of_actions_in_output = 0;
	for (GroundedTask & task : reachableTasks){
		if (domain.tasks[task.taskNo].isCompiledConditionalEffect) continue;
		if (task.taskNo >= domain.nPrimitiveTasks || prunedTasks[task.groundedNo]) continue;
		
		DEBUG( std::cout << "Processing task " << domain.tasks[task.taskNo].name << " for output" << std::endl);
		
		int costs = domain.tasks[task.taskNo].computeGroundCost(task,init_functions_map);
		
		std::map<int,int> cover_pruned_precs;
		// find facts that were cover pruned
		for (int & prec : task.groundedPreconditions){
			if (cover_pruned.count(prec)){
				int pos = cover_pruned_precs.size();
				cover_pruned_precs[prec] = pos;
			}
		}
	
		DEBUG(std::cout << "Number of cover pruned preconditions: " << cover_pruned_precs.size() << std::endl);

		// analyse precondition
		std::vector<int> prec_out;
		for (int & prec : task.groundedPreconditions) if (!prunedFacts[prec]){
			DEBUG(std::cout << "  PREC(" << prec  << "):" << reachableFacts[prec].predicateNo;
					for (int arg : reachableFacts[prec].arguments) std::cout << " " << arg;
					std::cout << std::endl;
					);

			if (! cover_pruned_precs.count(prec))
				prec_out.push_back(reachableFacts[prec].outputNo);
			else
				prec_out.push_back(-cover_pruned_precs[prec]-1); // marker
		} else {
			DEBUG(std::cout << "  pruned PREC(" << prec  << "):" << reachableFacts[prec].predicateNo;
					for (int arg : reachableFacts[prec].arguments) std::cout << " " << arg;
					std::cout << std::endl;
					);
		}

		std::vector<std::pair<std::vector<int>,int>> add_out;
		std::vector<std::pair<std::vector<int>,int>> del_out;

		std::vector<int> ce_guards;
		std::vector<int> _empty;
		for (int & add : task.groundedAddEffects)
			if (domain.predicates[reachableFacts[add].predicateNo].guard_for_conditional_effect)
				ce_guards.push_back(add);
			else {	
				if (!prunedFacts[add] && !cover_pruned.count(add)){
					int addOut = reachableFacts[add].outputNo;
					add_out.push_back(std::make_pair(_empty,addOut));

					// if this is a member of a SAS group that needs a none-of-those, delete it
					if (addOut < sas_g_per_fact.size()){
						int sas_g = sas_g_per_fact[addOut];
						if (sas_variables_needing_none_of_them[sas_g])
							del_out.push_back(std::make_pair(_empty,none_of_them_per_sas_group[sas_g]));
					}
				}
			}

		for (const int & sas_g : task.noneOfThoseEffect){
			assert(none_of_them_per_sas_group[sas_g] != -1);
			add_out.push_back(std::make_pair(_empty,none_of_them_per_sas_group[sas_g])); 
		}

		for (int & del : task.groundedDelEffects) if (!prunedFacts[del] && !cover_pruned.count(del)){
			if (config.sas_mode != SAS_AS_INPUT && reachableFacts[del].outputNo < number_of_sas_covered_facts) 
				continue; // if the user instructed us to do something else than keeping, we will do it
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

			if (prunedFacts[effectID] || cover_pruned.count(effectID)) continue; // this effect is not necessary
			if (config.sas_mode != SAS_AS_INPUT && reachableFacts[effectID].outputNo < number_of_sas_covered_facts)
				continue; // see above

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

			
			if (isAdd){
				int addOut = reachableFacts[effectID].outputNo;
				
				add_out.push_back(std::make_pair(nonPrunedPrecs, addOut));
				DEBUG(std::cout << "Found conditional add effect on ce-task " << ce_task.groundedNo << " internal ID " << effectID << " output as " << reachableFacts[effectID].outputNo << std::endl);
			
				// if this is a member of a SAS group that needs a none-of-those, delete it
				if (addOut < sas_g_per_fact.size()){
					int sas_g = sas_g_per_fact[addOut];
					if (sas_variables_needing_none_of_them[sas_g])
						del_out.push_back(std::make_pair(nonPrunedPrecs,none_of_them_per_sas_group[sas_g]));
				}
			} else {
				del_out.push_back(std::make_pair(nonPrunedPrecs, reachableFacts[effectID].outputNo));
				DEBUG(std::cout << "Found conditional del effect on ce-task " << ce_task.groundedNo << " internal ID " << effectID << " output as " << reachableFacts[effectID].outputNo << std::endl);
			}
		}
		
		
		if (config.sas_mode == SAS_ALL){
			for (const auto & add : add_out){
				if (add.second >= number_of_sas_covered_facts) continue; // this is not a SAS+ fact
				// add delete effects for everything that is not *this* add
				auto [from,to] = per_sas_fact_from_to[add.second];
				for (int other = from; other <= to; other++) if (other != add.second)
					del_out.push_back(std::make_pair(add.first, other)); 
			}
		}

		
		std::vector<std::vector<int>> instances = instantiate_cover_pruned(cover_pruned_precs, cover_pruned);

		number_of_actions_in_output += instances.size();
		output_actions.push_back(std::make_tuple(task.groundedNo,costs,prec_out,add_out,del_out,instances));
	}
	

	// actual output of actions

	pout << ";; Actions" << std::endl;
	pout << number_of_actions_in_output + (contains_empty_method ? 1 : 0) << std::endl; 
	int ac = 0;
	int number_of_additional_abstracts = 0;
	int number_of_output_primitives = 0;
	int number_of_output_artificial_primitives = 0;

	// if necessary, we add a no-op, s.t. methods are non-empty. This task will always have cost 0
	if (contains_empty_method){
		pout << 0 << std::endl;
		pout << -1 << std::endl;
		pout << -1 << std::endl;
		pout << -1 << std::endl;

		ac++;
		number_of_output_artificial_primitives++;
	}

	for (const auto & [tID, costs, prec_out, add_out, del_out, instances] : output_actions){
		DEBUG(std::cout << "Task " << tID << " gets outputID " << ac << std::endl);
		
		GroundedTask & task = reachableTasks[tID];
		if (instances.size() == 1)
			task.outputNo = ac;
		else {
			number_of_additional_abstracts++;
			task.outputNo = -2; // marker for additionally needed task
		}

		for (const std::vector<int> & cover_assignment : instances){
			///////////////////////////// ACTUAL OUTPUT
			task.outputNosForCover.push_back(ac++);
			if (domain.tasks[task.taskNo].name[0] == '_')
				number_of_output_artificial_primitives++;
			else
				number_of_output_primitives++;
			
			DEBUG(write_task_name(std::cout,domain,task); std::cout << std::endl;
			// output raw for debugging
			for (int p : task.groundedPreconditions) std::cout << p << " "; std::cout << std::endl;
			for (int p : task.groundedAddEffects) std::cout << p << " "; std::cout << std::endl;
			for (int p : task.groundedDelEffects) std::cout << p << " "; std::cout << std::endl);


			// ACTUAL
			pout << costs << std::endl;
			// preconditions
			std::unordered_set<int> p_out;
			for (const int & prec : prec_out)
				if (prec >= 0)
					p_out.insert(prec);
				else {
					int alternate = cover_assignment[-prec-1];
					if (alternate >= 0)
						p_out.insert(reachableFacts[alternate].outputNo);
					else
						p_out.insert(none_of_them_per_sas_group[-alternate-1]);
				}

			for (const int & x : p_out)
				pout << x << " ";
			pout << -1 << std::endl;


			std::unordered_set<std::pair<std::unordered_set<int>,int>> a_out;
			// output add effects
			for (const auto & add : add_out){
				std::pair<std::unordered_set<int>,int> op;
				for (const int & p : add.first) 
					if (p >= 0)
						op.first.insert(p);
					else {
						int alternate = cover_assignment[-p-1];
						if (alternate >= 0)
							op.first.insert(reachableFacts[alternate].outputNo);
						else
							op.first.insert(none_of_them_per_sas_group[-alternate-1]);
					}
				op.second = add.second;
				a_out.insert(op);
			}

			// output add effects
			for (const auto & add : a_out){
				pout << add.first.size() << " ";
				for (const int & p : add.first) 
					pout << p << " ";
				pout << add.second << "  ";
			}
			pout << -1 << std::endl;

			// output del effects
			std::unordered_set<std::pair<std::unordered_set<int>,int>> d_out;
			for (const auto & del : del_out){
				std::pair<std::unordered_set<int>,int> op;
				for (const int & p : del.first)
					if (p >= 0)
						op.first.insert(p);
					else {
						int alternate = cover_assignment[-p-1];
						if (alternate >= 0)
							op.first.insert(reachableFacts[alternate].outputNo);
						else
							op.first.insert(none_of_them_per_sas_group[-alternate-1]);
					}
				op.second = del.second;
				d_out.insert(op);
			}

			for (const auto & del : d_out){
				pout << del.first.size() << " " ;
				for (const int & p : del.first)
					pout << p << " ";
				pout << del.second << "  ";
			}
			pout << -1 << std::endl;
		}
	}

	pout << std::endl << ";; initial state" << std::endl;
	for (size_t sas_g = 0; sas_g < sas_groups.size(); sas_g++){
		if (pruned_sas_groups.count(sas_g)) continue; // has been cover pruned
		
		bool didOutput = false;
		for (const int & f : sas_groups[sas_g]) if (initFacts.count(f)){
			assert(!prunedFacts[f]);
			assert(!cover_pruned.count(f));
			assert(reachableFacts[f].outputNo >= 0);
			pout << reachableFacts[f].outputNo << " ";
			didOutput = true;
		}
		if (!didOutput){
			assert(none_of_them_per_sas_group[sas_g] != -1);
			pout << none_of_them_per_sas_group[sas_g] << " ";
		}
	}
	

	for (int fID : initFacts){
		if (prunedFacts[fID]) continue;
		if (cover_pruned.count(fID)) continue;
		
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

	int abstractTasks = 0;
	for (GroundedTask & task : reachableTasks){
		if (prunedTasks[task.groundedNo]) continue;
		if (task.taskNo < domain.nPrimitiveTasks) continue;
		abstractTasks++;
	}
	
	pout << std::endl << ";; tasks (primitive and abstract)" << std::endl;
	pout << number_of_actions_in_output + abstractTasks + number_of_additional_abstracts + (contains_empty_method ? 1 : 0) << std::endl;
	
	// if necessary additional noop
	if (contains_empty_method){
		pout << 0 << " __noop" << std::endl;
	}
	
	// output names of primitives
	for (const auto & [tID, _1, _2, _3, _4, instances] : output_actions){
		GroundedTask & task = reachableTasks[tID];

		for (const std::vector<int> & _cover_assignment : instances){
			pout << 0 << " ";
			write_task_name(pout,domain,task);
			pout << std::endl;
		}
	}


	int initialAbstract = -1;
	for (GroundedTask & task : reachableTasks){
		if (prunedTasks[task.groundedNo]) continue;
		if (task.taskNo < domain.nPrimitiveTasks) continue;
		task.outputNo = ac++;
		if (task.taskNo == problem.initialAbstractTask) initialAbstract = task.outputNo; 

		pout << 1 << " ";
		write_task_name(pout,domain,task);
		pout << std::endl;
	}
	int number_of_output_abstracts = ac - number_of_output_primitives - number_of_output_artificial_primitives;

	
	// artificial tasks
	int number_of_additional_methods = 0;
	for (GroundedTask & task : reachableTasks) if (task.outputNo == -2){
		pout << 1 << " __sas";
		task.outputNo = -(ac++) - 2;
		write_task_name(pout,domain,task);
		pout << std::endl;
		number_of_additional_methods += task.outputNosForCover.size();
	}

	pout << std::endl << ";; initial abstract task" << std::endl;
	pout << initialAbstract << std::endl;

	int number_of_actual_methods = 0;
	for (bool b : prunedMethods) if (!b) number_of_actual_methods++;
	
	pout << std::endl << ";; methods" << std::endl;
	pout << number_of_actual_methods + number_of_additional_methods << std::endl;
	int number_of_output_methods = 0;
	for (auto & method : reachableMethods){
		if (prunedMethods[method.groundedNo]) continue;
		number_of_output_methods++;
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

		// the abstract task
		int atOutputNo = reachableTasks[method.groundedAddEffects[0]].outputNo;
		assert(atOutputNo >= 0);
		pout << atOutputNo << std::endl;

		
		std::map<int,int> subTaskIndexToOutputIndex;
		// output subtasks in their topological ordering
		for (size_t outputIndex = 0; outputIndex < method.preconditionOrdering.size(); outputIndex++){
			int subtaskIndex = method.preconditionOrdering[outputIndex];
			assert(subtaskIndex >= 0);
			assert(subtaskIndex < method.groundedPreconditions.size());
			subTaskIndexToOutputIndex[subtaskIndex] = outputIndex;

			int groundedSubtask = method.groundedPreconditions[subtaskIndex];
			assert(!prunedTasks[groundedSubtask]);

			int outNo = reachableTasks[groundedSubtask].outputNo;
			if (outNo < 0) outNo = -outNo - 2; // marker task, and keeps -1 invariant ...

			pout << outNo << " ";
			assert(outNo >= 0);
		}
		// no empty methods if desired. If this method would be empty, add a no-op.
		if (contains_empty_method && method.preconditionOrdering.size() == 0)
			pout << "0 ";

		pout << "-1" << std::endl;

		auto orderings = domain.decompositionMethods[method.methodNo].orderingConstraints;
		std::sort(orderings.begin(), orderings.end());
		auto last = std::unique(orderings.begin(), orderings.end());
		orderings.erase(last, orderings.end());


		for (auto & order : orderings)
			pout << subTaskIndexToOutputIndex[order.first] << " " << subTaskIndexToOutputIndex[order.second] << " ";
		pout << "-1" << std::endl;
	}

	for (GroundedTask & task : reachableTasks) if (task.outputNo <= -2){
		int at = -task.outputNo -2;
	
		for (const int & prim : task.outputNosForCover){
			number_of_output_methods++;
			pout << "sas_method_";
			write_task_name(pout,domain,task);
			pout << std::endl;
			pout << at << std::endl;
			pout << prim << " " << -1 << std::endl;
			pout << -1 << std::endl;
		}
	}
	
	if (!config.quietMode) std::cout << "Final Statistics: F " << fn << " S " << sas_groups.size() << 
		" SC " << number_of_sas_covered_facts << 
		" SM " << out_strict_mutexes.size() << " NSM " << out_non_strict_mutexes.size() << " I " << out_invariants.size() <<
		" P " << number_of_output_primitives << " S " << number_of_output_artificial_primitives <<
		" A " << number_of_output_abstracts << " M " << number_of_output_methods << std::endl;

	// exiting this way is faster as data structures will not be cleared ... who needs this anyway
	if (!config.quietMode) std::cerr << "Exiting." << std::endl;
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
		else if (c == '|') result += "BAR_";
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
		grounding_configuration & config
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
		
		if (method.preconditionOrdering.size()){
			dout << "    :subtasks (and" << std::endl;
			for (size_t outputIndex = 0; outputIndex < method.preconditionOrdering.size(); outputIndex++){
				int subtaskIndex = method.preconditionOrdering[outputIndex];
				subTaskIndexToOutputIndex[subtaskIndex] = outputIndex;
				
				GroundedTask & task	= reachableTasks[method.groundedPreconditions[subtaskIndex]];
				dout << "      (t" << outputIndex << " (" << taskname[task.groundedNo] << "))" << std::endl;
			}
			dout << "    )" << std::endl;
		}

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
