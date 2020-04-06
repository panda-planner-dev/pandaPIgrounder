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


void run_grounding (const Domain & domain, const Problem & problem, std::ostream & dout, std::ostream & pout, 
		bool enableHierarchyTyping, 
		bool removeUselessPredicates,
		bool expandChoicelessAbstractTasks,
		bool pruneEmptyMethodPreconditions,
		bool futureCachingByPrecondition,
		bool h2Mutextes,
		bool computeInvariants,
		bool outputSASVariablesOnly,
		sas_delete_output_mode sas_mode,
		bool compileNegativeSASVariables,
		bool removeDuplicateActions,
		bool noopForEmptyMethods,
		bool outputForPlanner, 
		bool outputHDDL, 
		bool outputSASPlus, 
		bool printTimings,
		bool quietMode){

  	std::vector<FAMGroup> famGroups;	
	if (computeInvariants){
		famGroups = compute_FAM_mutexes(domain,problem,quietMode);
	}

	// if the instance contains conditional effects we have to compile them into additional primitive actions
	// for this, we need to be able to write to the domain
	expand_conditional_effects_into_artificial_tasks(const_cast<Domain &>(domain), const_cast<Problem &>(problem));
	if (!quietMode) std::cout << "Conditional Effects expanded" << std::endl;

	// run the lifted GPG to create an initial grounding of the domain
	auto [initiallyReachableFacts,initiallyReachableTasks,initiallyReachableMethods] = run_lifted_HTN_GPG(domain, problem, 
			enableHierarchyTyping, futureCachingByPrecondition, printTimings, quietMode);
	// run the grounded GPG until convergence to get the grounding smaller
	std::vector<bool> prunedFacts (initiallyReachableFacts.size());
	std::vector<bool> prunedTasks (initiallyReachableTasks.size());
	std::vector<bool> prunedMethods (initiallyReachableMethods.size());
	
	run_grounded_HTN_GPG(domain, problem, initiallyReachableFacts, initiallyReachableTasks, initiallyReachableMethods, 
			prunedFacts, prunedTasks, prunedMethods,
			quietMode);

////////////////////// H2 mutexes
	std::vector<std::unordered_set<int>> h2_mutexes;
	std::vector<std::unordered_set<int>> h2_invariants;
	if (h2Mutextes){
		// remove useless predicates to make the H2 inference easier
		postprocess_grounding(domain, problem, initiallyReachableFacts, initiallyReachableTasks, initiallyReachableMethods, prunedFacts, prunedTasks, prunedMethods, 
			removeUselessPredicates, false, false, quietMode);	

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
				true, // outputSASVariablesOnly -> force SAS+ here. This makes the implementation easier
				quietMode);
		
		
		bool changedPruned = false;
		std::vector<bool> sas_variables_needing_none_of_them = ground_invariant_analysis(domain, problem, 
				initiallyReachableFacts, initiallyReachableTasks, initiallyReachableMethods,
				prunedTasks, prunedFacts, prunedMethods,
				initFacts,
				sas_groups,further_mutex_groups,
				changedPruned,
				quietMode);


		// run H2 mutex analysis
		auto [has_pruned, _h2_mutexes, _h2_invariants] = 
			compute_h2_mutexes(domain,problem,initiallyReachableFacts,initiallyReachableTasks,
					prunedFacts, prunedTasks, 
					sas_groups, further_mutex_groups,sas_variables_needing_none_of_them,
					quietMode);
		h2_mutexes = _h2_mutexes;
		h2_invariants = _h2_invariants;

		if (has_pruned || changedPruned){
			// if we have pruned actions, rerun the PGP and HTN stuff
			run_grounded_HTN_GPG(domain, problem, initiallyReachableFacts, initiallyReachableTasks, initiallyReachableMethods, 
				prunedFacts, prunedTasks, prunedMethods,
				quietMode);
		}
	}
//////////////////////// end of H2 mutexes

	// run postprocessing
	postprocess_grounding(domain, problem, initiallyReachableFacts, initiallyReachableTasks, initiallyReachableMethods, prunedFacts, prunedTasks, prunedMethods, 
			removeUselessPredicates, expandChoicelessAbstractTasks, pruneEmptyMethodPreconditions, quietMode);	

	if (outputSASPlus){
		write_sasplus(dout, domain,problem,initiallyReachableFacts,initiallyReachableTasks, prunedFacts, prunedTasks, quietMode);
		return;
	}

	if (outputForPlanner){
		if (outputHDDL)
			write_grounded_HTN_to_HDDL(dout, pout, domain, problem, initiallyReachableFacts,initiallyReachableTasks, initiallyReachableMethods, prunedTasks, prunedFacts, prunedMethods, quietMode);
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
			std::vector<std::unordered_set<int>> sas_groups;
			std::vector<std::unordered_set<int>> further_mutex_groups;

			while (true){
				auto [_sas_groups,_further_mutex_groups] = compute_sas_groups(domain, problem, 
						famGroups, h2_mutexes,
						initiallyReachableFacts,initiallyReachableTasks, initiallyReachableMethods, prunedTasks, prunedFacts, prunedMethods, 
						initFacts, reachableFactsSet,
						outputSASVariablesOnly,
						quietMode);

				bool changedPruned = false;
				std::vector<bool> _sas_variables_needing_none_of_them = ground_invariant_analysis(domain, problem, 
						initiallyReachableFacts, initiallyReachableTasks, initiallyReachableMethods,
						prunedTasks, prunedFacts, prunedMethods,
						initFacts,
						_sas_groups,_further_mutex_groups,
						changedPruned,
						quietMode);

				if (changedPruned){
					run_grounded_HTN_GPG(domain, problem, initiallyReachableFacts, initiallyReachableTasks, initiallyReachableMethods, 
						prunedFacts, prunedTasks, prunedMethods,
						quietMode);
				} else {
					sas_variables_needing_none_of_them = _sas_variables_needing_none_of_them;
					sas_groups = _sas_groups;
					further_mutex_groups = _further_mutex_groups;
					break;
				}
			}

			// duplicate elemination
			if (removeDuplicateActions)
				unify_duplicates(domain,problem,initiallyReachableFacts,initiallyReachableTasks, initiallyReachableMethods, prunedTasks, prunedFacts, prunedMethods, quietMode);

			
			write_grounded_HTN(dout, domain, problem, initiallyReachableFacts,initiallyReachableTasks, initiallyReachableMethods, prunedTasks, prunedFacts, prunedMethods,
				initFacts, initFactsPruned, reachableFactsSet,
				sas_groups, further_mutex_groups, h2_invariants,
				sas_variables_needing_none_of_them,
				compileNegativeSASVariables, sas_mode, noopForEmptyMethods,
				quietMode);
		}
	
	}
}

