#include "grounding.h"
#include "gpg.h"
#include "liftedGPG.h"
#include "groundedGPG.h"
#include "postprocessing.h"
#include "output.h"
#include "sasplus.h"
#include "h2mutexes.h"
#include "FAMmutexes.h"
#include "conditional_effects.h"
#include "duplicate.h"


void run_grounding (const Domain & domain, const Problem & problem, std::ostream & dout, std::ostream & pout, grounding_configuration & config){

  	std::vector<FAMGroup> famGroups;	
	if (config.computeInvariants){
		famGroups = compute_FAM_mutexes(domain,problem,config);
	}

	// if the instance contains conditional effects we have to compile them into additional primitive actions
	// for this, we need to be able to write to the domain
	expand_conditional_effects_into_artificial_tasks(const_cast<Domain &>(domain), const_cast<Problem &>(problem));
	if (!config.quietMode) std::cout << "Conditional Effects expanded" << std::endl;

	// run the lifted GPG to create an initial grounding of the domain
	auto [initiallyReachableFacts,initiallyReachableTasks,initiallyReachableMethods] = run_lifted_HTN_GPG(domain, problem, config);
	// run the grounded GPG until convergence to get the grounding smaller
	std::vector<bool> prunedFacts (initiallyReachableFacts.size());
	std::vector<bool> prunedTasks (initiallyReachableTasks.size());
	std::vector<bool> prunedMethods (initiallyReachableMethods.size());
	
	run_grounded_HTN_GPG(domain, problem, initiallyReachableFacts, initiallyReachableTasks, initiallyReachableMethods, 
			prunedFacts, prunedTasks, prunedMethods,
			config);

////////////////////// H2 mutexes
	std::vector<std::unordered_set<int>> h2_mutexes;
	std::vector<std::unordered_set<int>> h2_invariants;
	if (config.h2Mutexes){
		// remove useless predicates to make the H2 inference easier
		grounding_configuration temp_configuration = config;
		temp_configuration.expandChoicelessAbstractTasks = false;
		temp_configuration.pruneEmptyMethodPreconditions = false;
		temp_configuration.outputSASVariablesOnly = true; // -> force SAS+ here. This makes the implementation easier

		postprocess_grounding(domain, problem, initiallyReachableFacts, initiallyReachableTasks, initiallyReachableMethods, prunedFacts, prunedTasks, prunedMethods, temp_configuration); 

		// H2 mutexes need the maximum amount of information possible, so we have to compute SAS groups at this point

		// prepare data structures that are needed for efficient access
		std::unordered_set<Fact> reachableFactsSet(initiallyReachableFacts.begin(), initiallyReachableFacts.end());
		
		std::unordered_set<int> initFacts; // needed for efficient goal checking
		std::unordered_set<int> initFactsPruned; // needed for efficient checking of pruned facts in the goal

		for (const Fact & f : problem.init){
			int groundNo = reachableFactsSet.find(f)->groundedNo;
			if (prunedFacts[groundNo]){
				initFactsPruned.insert(groundNo);
				continue;
			}
			initFacts.insert(groundNo);
		}



		auto [sas_groups,further_mutex_groups] = compute_sas_groups(domain, problem, 
				famGroups, h2_mutexes,
				initiallyReachableFacts,initiallyReachableTasks, initiallyReachableMethods, prunedTasks, prunedFacts, prunedMethods, 
				initFacts, reachableFactsSet,
				temp_configuration);
		
		
		bool changedPruned = false;
		auto [sas_variables_needing_none_of_them,_] = ground_invariant_analysis(domain, problem, 
				initiallyReachableFacts, initiallyReachableTasks, initiallyReachableMethods,
				prunedTasks, prunedFacts, prunedMethods,
				initFacts,
				sas_groups,further_mutex_groups,
				changedPruned,
				temp_configuration);


		// run H2 mutex analysis
		auto [has_pruned, _h2_mutexes, _h2_invariants] = 
			compute_h2_mutexes(domain,problem,initiallyReachableFacts,initiallyReachableTasks,
					prunedFacts, prunedTasks, 
					sas_groups, sas_variables_needing_none_of_them,
					temp_configuration);
		h2_mutexes = _h2_mutexes;
		h2_invariants = _h2_invariants;

		if (has_pruned || changedPruned){
			// if we have pruned actions, rerun the PGP and HTN stuff
			run_grounded_HTN_GPG(domain, problem, initiallyReachableFacts, initiallyReachableTasks, initiallyReachableMethods, 
				prunedFacts, prunedTasks, prunedMethods,
				temp_configuration);
		}
	}
//////////////////////// end of H2 mutexes

	// run postprocessing
	postprocess_grounding(domain, problem, initiallyReachableFacts, initiallyReachableTasks, initiallyReachableMethods, prunedFacts, prunedTasks, prunedMethods, config);	

	if (config.outputSASPlus){
		write_sasplus(dout, domain,problem,initiallyReachableFacts,initiallyReachableTasks, prunedFacts, prunedTasks, config);
		return;
	}

	if (config.outputForPlanner){
		if (config.outputHDDL)
			write_grounded_HTN_to_HDDL(dout, pout, domain, problem, initiallyReachableFacts,initiallyReachableTasks, initiallyReachableMethods, prunedTasks, prunedFacts, prunedMethods, config);
		else {
			// prepare data structures that are needed for efficient access
			std::unordered_set<Fact> reachableFactsSet(initiallyReachableFacts.begin(), initiallyReachableFacts.end());
			
			std::unordered_set<int> initFacts; // needed for efficient goal checking
			std::unordered_set<int> initFactsPruned; // needed for efficient checking of pruned facts in the goal

			for (const Fact & f : problem.init){
				int groundNo = reachableFactsSet.find(f)->groundedNo;
				if (prunedFacts[groundNo]){
					initFactsPruned.insert(groundNo);
					continue;
				}
				initFacts.insert(groundNo);
			}

			std::vector<bool> sas_variables_needing_none_of_them;
			std::vector<bool> mutex_groups_needing_none_of_them;
			std::vector<std::unordered_set<int>> sas_groups;
			std::vector<std::unordered_set<int>> further_mutex_groups;

			while (true){
				auto [_sas_groups,_further_mutex_groups] = compute_sas_groups(domain, problem, 
						famGroups, h2_mutexes,
						initiallyReachableFacts,initiallyReachableTasks, initiallyReachableMethods, prunedTasks, prunedFacts, prunedMethods, 
						initFacts, reachableFactsSet,
						config);

				bool changedPruned = false;
				auto [_sas_variables_needing_none_of_them,_mutex_groups_needing_none_of_them] = ground_invariant_analysis(domain, problem, 
						initiallyReachableFacts, initiallyReachableTasks, initiallyReachableMethods,
						prunedTasks, prunedFacts, prunedMethods,
						initFacts,
						_sas_groups,_further_mutex_groups,
						changedPruned,
						config);

				if (changedPruned){
					run_grounded_HTN_GPG(domain, problem, initiallyReachableFacts, initiallyReachableTasks, initiallyReachableMethods, 
						prunedFacts, prunedTasks, prunedMethods,
						config);
				} else {
					sas_variables_needing_none_of_them = _sas_variables_needing_none_of_them;
					mutex_groups_needing_none_of_them = _mutex_groups_needing_none_of_them;
					sas_groups = _sas_groups;
					further_mutex_groups = _further_mutex_groups;
					break;
				}
			}

			// duplicate elemination
			if (config.removeDuplicateActions)
				unify_duplicates(domain,problem,initiallyReachableFacts,initiallyReachableTasks, initiallyReachableMethods, prunedTasks, prunedFacts, prunedMethods, config);

			std::vector<std::unordered_set<int>> strict_mutexes;
			std::vector<std::unordered_set<int>> non_strict_mutexes;
			for (size_t m = 0; m < further_mutex_groups.size(); m++){
				if (mutex_groups_needing_none_of_them[m])
					non_strict_mutexes.push_back(further_mutex_groups[m]);
				else
					strict_mutexes.push_back(further_mutex_groups[m]);
			}
			
			if (!config.quietMode)
				std::cout << "Further Mutex Groups: " << strict_mutexes.size() <<  " strict " << non_strict_mutexes.size() << " non strict" << std::endl;

			write_grounded_HTN(dout, domain, problem, initiallyReachableFacts,initiallyReachableTasks, initiallyReachableMethods, prunedTasks, prunedFacts, prunedMethods,
				initFacts, initFactsPruned, reachableFactsSet,
				sas_groups, strict_mutexes, non_strict_mutexes, h2_invariants,
				sas_variables_needing_none_of_them,
				config);
		}
	
	}
}

