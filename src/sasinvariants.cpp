#include <algorithm>
#include <tuple>
#include <iostream>
#include <unordered_set>
#include <cassert>
#include "sasinvariants.h"
#include "debug.h"
#include "output.h"



/// hash function s.t. mutex groups can be put into unordered sets
namespace std {
    template<> struct hash<std::unordered_set<int>>
    {
        std::size_t operator()(const std::unordered_set<int> & m) const noexcept
        {
			std::vector<int> v;
			for (const int & a : m) v.push_back(a);
			std::sort(v.begin(),v.end());
			std::size_t h = 0;
			for (const int & a : v) h = h*601 + a;
			return h;
        }
    };
}


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
		return;
	}

	// if we got here, we have assigned all free variables.
	factsPerFAMInstance[gID][free_variable_assignment].insert(factID);

}

std::pair<std::vector<std::unordered_set<int>>, std::vector<std::unordered_set<int>>> compute_sas_groups(const Domain & domain, const Problem & problem,
		std::vector<FAMGroup> & groups,
		std::vector<std::unordered_set<int>> & known_mutex_groups,
		std::vector<Fact> & reachableFacts,
		std::vector<GroundedTask> & reachableTasks,
		std::vector<GroundedMethod> & reachableMethods,
		std::vector<bool> & prunedTasks,
		std::vector<bool> & prunedFacts,
		std::vector<bool> & prunedMethods,
		std::unordered_set<int> initFacts,
		std::unordered_set<Fact> reachableFactsSet,
		grounding_configuration & config){

	DEBUG(std::cout << "Computing SAS+ groups" << std::endl);


	// number of FAM group, values of free variables -> number of facts in this FAM mutex
	std::vector<std::map<std::vector<int>,std::unordered_set<int>>> factsPerFAMInstance (groups.size());

	for (size_t factID = 0; factID < reachableFacts.size(); factID++) if (!prunedFacts[factID]){
		const Fact & f = reachableFacts[factID];

		
		//std::cout << factID << " " << domain.predicates[f.predicateNo].name << "[";
		//for (unsigned int i = 0; i < f.arguments.size(); i++){
		//	if (i) std::cout << ",";
		//	std::cout << domain.constants[f.arguments[i]];
		//}
		//std::cout << "]" << std::endl;


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
						else if (!v.isCounted){ // a free var, must be assigned consistently
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

	std::unordered_set<std::unordered_set<int>> mutex_groups_set;
	for (size_t gID = 0; gID < factsPerFAMInstance.size(); gID++){
		for (auto & keyValue : factsPerFAMInstance[gID]){
			const std::unordered_set<int> & facts = keyValue.second;

			DEBUG(
				const std::vector<int> & free_variable_assignment = keyValue.first;
				std::cout << "Mutex Group " << gID << " Free vars:";
				for (size_t v = 0; v < groups[gID].free_vars.size(); v++){
					std::cout << " v=" << v << " fva[v]=" << free_variable_assignment[v];
					std::cout.flush();
					std::cout << " var" << groups[gID].free_vars[v];
					std::cout << " = " <<  domain.constants[free_variable_assignment[v]];
				}
				std::cout << " -> " << keyValue.second.size() << std::endl;
				);

			if (mutex_groups_set.count(facts)){
				DEBUG(std::cout << "Duplicate FAM mutex:";
						for (int m : facts) std::cout << " " << m;
						std::cout << std::endl);

			} else {
				DEBUG(std::cout << "Insert (FAM):";
						for (int m : facts) std::cout << " " << m;
						std::cout << std::endl);
				mutex_groups_set.insert(facts);
			}
		}
	}



	// add mutex groups from known predicate mutexes
	std::map<int,int> predicate_mutex_partner;
	for (const std::pair<int,int> & predicate_mutex : domain.predicateMutexes)
		predicate_mutex_partner[predicate_mutex.first] = predicate_mutex.second;

	for (size_t factID = 0; factID < reachableFacts.size(); factID++) if (!prunedFacts[factID]){
		const Fact & f = reachableFacts[factID];

		// continue, if this is not a predicate in a mutex
		if (!predicate_mutex_partner.count(f.predicateNo)) continue;
		
		// check if the partner is also still reachable
		Fact partner = f;
		partner.predicateNo = predicate_mutex_partner[f.predicateNo];
		auto partnerIterator = reachableFactsSet.find(partner);
		if (partnerIterator == reachableFactsSet.end()) continue;

		int partnerGroundNo = partnerIterator->groundedNo;
		if (prunedFacts[partnerGroundNo]) continue;


		// I my partner are mutex and unpruned, so we are a mutex
		std::unordered_set<int> mutex;
		mutex.insert(f.groundedNo);
		mutex.insert(partnerGroundNo);
		if (mutex_groups_set.count(mutex))
			DEBUG(std::cout << "Duplicate negation mutex for factID " << factID << std::endl);
		else {
			DEBUG(std::cout << "Insert (PRED):";
					for (int m : mutex) std::cout << " " << m;
					std::cout << std::endl);
			//mutex_groups_set.insert(mutex);
		}
	}

	// add known mutex groups
	for (const auto & mgroup : known_mutex_groups){
		// remove pruned facts
		std::unordered_set<int> unpruned_facts;
		for (int f : mgroup) if (!prunedFacts[f]) unpruned_facts.insert(f);
		
		if (unpruned_facts.size() < 2) continue; // mutex with less than two members is useless

		if (mutex_groups_set.count(unpruned_facts)){
			DEBUG(std::cout << "Duplicate H2-mutex:";
					for (const int &x : unpruned_facts) std::cout << " " << x;
					std::cout << std::endl;	
					);
		} else {
			DEBUG(std::cout << "Insert (H2):";
					for (int m : unpruned_facts) std::cout << " " << m;
					std::cout << std::endl);
			mutex_groups_set.insert(unpruned_facts);
		}
	}


	std::vector<std::unordered_set<int>> mutex_groups_by_size;
	mutex_groups_by_size.assign(mutex_groups_set.begin(), mutex_groups_set.end());

	// sort groups by size
	std::sort(mutex_groups_by_size.begin(), mutex_groups_by_size.end(), [](const auto& one, const auto& two ){return one.size() > two.size();});

	std::vector<bool> factCovered (reachableFacts.size());
	for (size_t i = 0; i < factCovered.size(); i++) factCovered[i] = false;
	std::vector<std::unordered_set<int>> ground_mutex_groups;
	std::vector<std::unordered_set<int>> orthogonal_mutex_groups;

	for (auto & covered_facts : mutex_groups_by_size){
		DEBUG(std::cout << "Consider mutex group of size " << covered_facts.size());

		if (covered_facts.size() < 2) continue; // not a real mutex group

		// check how many of them are in the initial state
		int number_in_init = 0;
		for (int f : covered_facts)
			if (initFacts.count(f)) number_in_init++;
		DEBUG(std::cout << " of which " << number_in_init << " are true in init." << std::endl);
		if (number_in_init > 1) continue; // can't handle this


		// check whether all facts are not-covered
		bool alreadyCovered = false;
		for (int f : covered_facts) {
			assert(!prunedFacts[f]);
			if (factCovered[f]) {
				alreadyCovered = true;
				break; 
			}
		}

		if (alreadyCovered) {
			orthogonal_mutex_groups.push_back(covered_facts);
			continue;
		}

		ground_mutex_groups.push_back(covered_facts);
		for (int f : covered_facts) factCovered[f] = true;

		DEBUG(std::cout << "Generating SAS group containing:"; for (int f : covered_facts) std::cout << " " << f; std::cout << std::endl;);
	}

	for (auto mg : ground_mutex_groups)
		for (int f : mg){
			if (prunedFacts[f]) std::cout << "F " << f << std::endl;
			assert(!prunedFacts[f]);
		}


	// add mutex groups for all uncovered variables, if we want to output everything as SAS+
	if (config.outputSASVariablesOnly){
		for (size_t f = 0; f < reachableFacts.size(); f++) if (!prunedFacts[f] && !factCovered[f]){
			std::unordered_set<int> s;
			s.insert(f);
			ground_mutex_groups.push_back(s);
		}
	}


	for (auto mg : ground_mutex_groups)
		for (int f : mg){
			if (prunedFacts[f]) std::cout << "F " << f << std::endl;
			assert(!prunedFacts[f]);
		}

	return std::make_pair(ground_mutex_groups,orthogonal_mutex_groups);
}



std::pair<std::vector<bool>,std::vector<bool>> ground_invariant_analysis(const Domain & domain, const Problem & problem,
		std::vector<Fact> & reachableFacts,
		std::vector<GroundedTask> & reachableTasks,
		std::vector<GroundedMethod> & reachableMethods,
		std::vector<bool> & prunedTasks,
		std::vector<bool> & prunedFacts,
		std::vector<bool> & prunedMethods,
		std::unordered_set<int> & initFacts,
		std::vector<std::unordered_set<int>> & sas_mutexes,
		std::vector<std::unordered_set<int>> & other_mutexes,
		bool & changedPruned,
		grounding_configuration & config){
	// identify those SAS+ groups, which need the element "none-of-them"
	std::vector<bool> sas_groups_needing_none_of_them (sas_mutexes.size());
	for (size_t i = 0; i < sas_groups_needing_none_of_them.size(); i++)
		sas_groups_needing_none_of_them[i] = false;
	// do the same for the other mutexes
	std::vector<bool> mutex_groups_needing_none_of_them (other_mutexes.size());
	for (size_t i = 0; i < mutex_groups_needing_none_of_them.size(); i++)
		mutex_groups_needing_none_of_them[i] = false;
	
	std::vector<std::vector<int>> mutex_groups_per_fact (reachableFacts.size());
	for (size_t m = 0; m < sas_mutexes.size(); m++){
		bool initContainsOne = false;
		for (const int & f : sas_mutexes[m]){
			mutex_groups_per_fact[f].push_back(m);
			initContainsOne |= initFacts.count(f);
		}
		// if it is not set in init, we definitely one
		if (!initContainsOne) sas_groups_needing_none_of_them[m] = true;
	}

	for (size_t m = 0; m < other_mutexes.size(); m++){
		bool initContainsOne = false;
		for (const int & f : other_mutexes[m]){
			mutex_groups_per_fact[f].push_back(-m-1); // negative numbers are other mutexes
		 	initContainsOne |= initFacts.count(f);
		}
		// if it is not set in init, we definitely one
		if (!initContainsOne) mutex_groups_needing_none_of_them[m] = true;
	}

	for (size_t aID = 0; aID < reachableTasks.size(); aID++) {
		if (prunedTasks[aID]) continue;
		if (domain.nPrimitiveTasks <= reachableTasks[aID].taskNo) continue; // abstract
		reachableTasks[aID].noneOfThoseEffect.clear();

		// check whether the preconditions violate one of the mutexes
		std::map<int,int> mutex_required_count;
		std::unordered_set<int> handledPreconditions;
		for (const int & pre : reachableTasks[aID].groundedPreconditions){
			if (handledPreconditions.count(pre)) continue;
			handledPreconditions.insert(pre);
			for (const int & m : mutex_groups_per_fact[pre]){
				DEBUG(std::cout << "Action " << aID << "[";
					write_task_name(std::cout, domain, reachableTasks[aID]);
					std::cout << "] mutex " << m << " on " << pre << std::endl;
						);
				mutex_required_count[m]++;
			}
		}

		for (const auto & entry : mutex_required_count){
			//DEBUG(std::cout << "Action " << aID << "'s preconditions refer mutex " << entry.first << " " << entry.second << " times " << std::endl);
			if (entry.second == 1) continue; // ok
			DEBUG(std::cout << "Pruning action " << aID << " [";
				write_task_name(std::cout, domain, reachableTasks[aID]);
				std::cout << "] as its preconditions violate a mutex " << entry.first << " @ " << entry.second << std::endl);
			prunedTasks[aID] = true;
			changedPruned = true;
		}

		if (prunedTasks[aID]) continue;

		// action can be executable. Thus its effects won't violate mutexes, else the mutex is not a real mutex


		// determine for the sas_mutexes whether this action can make all elements of the mutex false
		// This is the case, if it does not add, but deletes
		// Here we look at the conditional effect actions on a one-by-one-basis. This is an approximation (i.e. one conditional delete will lead to detection), but I guess this happens rarely?
		std::unordered_set<int> add,del;
		for (const int & a : reachableTasks[aID].groundedAddEffects)
			for (const int & m : mutex_groups_per_fact[a])
				add.insert(m);
		for (const int & d : reachableTasks[aID].groundedDelEffects)
			for (const int & m : mutex_groups_per_fact[d])
				del.insert(m);
		
		for (const int & d : del) if (!add.count(d)){
			if (d >= 0){
				sas_groups_needing_none_of_them[d] = true;
				reachableTasks[aID].noneOfThoseEffect.push_back(d);
			} else {
				mutex_groups_needing_none_of_them[-d-1] = true;
			}
		}
	}

	return std::make_pair(sas_groups_needing_none_of_them,mutex_groups_needing_none_of_them);
}



