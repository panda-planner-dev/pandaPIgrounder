#include <algorithm>
#include <tuple>
#include <iostream>
#include <unordered_set>
#include "sasinvariants.h"
#include "debug.h"

void add_fact_to_FAM_instance(const Domain & domain, std::vector<std::map<std::vector<int>,std::unordered_set<int>>> & factsPerFAMInstance, int factID, const FAMGroup & g, int gID, std::vector<int> & free_variable_assignment){

	for (size_t vIDX = 0; vIDX < free_variable_assignment.size(); vIDX++){
		if (free_variable_assignment[vIDX] != -1) continue;

		// branch over all possible values
		int vSort = g.vars[g.free_vars[vIDX]].sort;
		for (int c : domain.sorts[vSort].members){
			free_variable_assignment[vIDX] = c;
			add_fact_to_FAM_instance(domain,factsPerFAMInstance,factID,g,gID,free_variable_assignment);
		}
		free_variable_assignment[vIDX] = -1;
	}

	// if we got here, we have assigned all free variables.
	factsPerFAMInstance[gID][free_variable_assignment].insert(factID);

}

std::pair<std::vector<std::unordered_set<int>>, std::vector<std::unordered_set<int>>> compute_sas_groups(const Domain & domain, const Problem & problem,
		std::vector<FAMGroup> & groups,
		std::vector<Fact> & reachableFacts,
		std::vector<GroundedTask> & reachableTasks,
		std::vector<GroundedMethod> & reachableMethods,
		std::vector<bool> & prunedTasks,
		std::vector<bool> & prunedFacts,
		std::vector<bool> & prunedMethods,
		bool quietMode){

	DEBUG(std::cout << "Computing SAS+ groups" << std::endl);


	// number of FAM group, values of free variables -> number of facts in this FAM mutex
	std::vector<std::map<std::vector<int>,std::unordered_set<int>>> factsPerFAMInstance (groups.size());


	for (size_t factID = 0; factID < reachableFacts.size(); factID++) if (!prunedFacts[factID]){
		const Fact & f = reachableFacts[factID];

		// go through all FAM groups and look whether we can be part of them
		for (size_t gID = 0; gID < groups.size(); gID++){
			const FAMGroup & g = groups[gID];
			for (const FAMGroupLiteral & l : g.literals){
				if (l.predicateNo != f.predicateNo) continue;


				std::vector<int> free_variable_assignment (g.free_vars.size());
				for (size_t i = 0; i < free_variable_assignment.size(); i++)
					free_variable_assignment[i] = -1;

				// check whether
				bool notMatching = false;
				for (size_t argID = 0; !notMatching && argID < l.args.size(); argID++){
					int factArg = f.arguments[argID];
					if (l.isConstant[argID]){
						if (factArg != l.args[argID])
							notMatching = true;
						// else ok!
					} else {
						const FAMVariable & v = g.vars[l.args[argID]];
						if (!domain.sorts[v.sort].members.count(factArg))
							notMatching = true;
						else if (!v.isCounted){ // a free var, bust be assigned consistently
							int assignment_index = g.vars_to_pos_in_separated_lists[l.args[argID]];
							if (free_variable_assignment[assignment_index] != -1){
								if (free_variable_assignment[assignment_index] != factArg)
									notMatching = true;
							}

							free_variable_assignment[assignment_index] = factArg;
						}
					}
				}


				if (notMatching) continue;

				// this fact matches the literal of the (lifted) FAMGroup, so add it
				add_fact_to_FAM_instance(domain,factsPerFAMInstance,factID,g,gID,free_variable_assignment);
			}
			
		}
	}



	// create SAS+ representation, i.e. the ground mutex groups that we will actually use.
	// We do this greedily, by taking the largest mutex group first

	std::vector<std::tuple<int,int,std::vector<int>>> mutex_groups_by_size;

	for (size_t gID = 0; gID < factsPerFAMInstance.size(); gID++){
		for (auto & keyValue : factsPerFAMInstance[gID]){
			const std::vector<int> & free_variable_assignment = keyValue.first;

			DEBUG(
				std::cout << "Mutex Group " << gID << " Free vars:";
				for (size_t v = 0; v < groups[gID].free_vars.size(); v++){
					std::cout << " var" << groups[gID].free_vars[v] << " = " <<  domain.constants[free_variable_assignment[v]];
				}
				std::cout << " -> " << keyValue.second.size() << std::endl;
				);


			// negative size, to get largest groups first
			mutex_groups_by_size.push_back(std::make_tuple(-keyValue.second.size(), gID, free_variable_assignment));
		}
	}

	// sort groups by size
	std::sort(mutex_groups_by_size.begin(), mutex_groups_by_size.end());

	std::vector<bool> factCovered (reachableFacts.size());
	for (size_t i = 0; i < factCovered.size(); i++) factCovered[i] = false;
	std::vector<std::unordered_set<int>> ground_mutex_groups;
	std::vector<std::unordered_set<int>> orthogonal_mutex_groups;

	for (auto & [_,gID,free_variable_assignment] : mutex_groups_by_size){
		std::unordered_set<int> covered_facts = factsPerFAMInstance[gID][free_variable_assignment];

		// check whether all facts are not-covered
		bool alreadyCovered = false;
		for (int f : covered_facts) if (factCovered[f]) { alreadyCovered = true; break; }
		if (alreadyCovered) {
			orthogonal_mutex_groups.push_back(covered_facts);
			continue;
		}

		ground_mutex_groups.push_back(covered_facts);
		for (int f : covered_facts) factCovered[f] = true;
	}

	return std::make_pair(ground_mutex_groups,orthogonal_mutex_groups);
}
