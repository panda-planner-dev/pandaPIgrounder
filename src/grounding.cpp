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

void grounding_configuration::print_options(){
	if (quietMode) return;
	
	// program output behaviour	
	std::cout << std::boolalpha;
	std::cout << "General Options" << std::endl;
	std::cout << "  Print timings: " << printTimings << std::endl;
	std::cout << "  Quiet mode: " << quietMode << std::endl;
	
	
	std::cout << "Inference Options" << std::endl;
	// inference of additional information
	std::cout << "  H2 mutexes: " << h2Mutexes << std::endl;
	std::cout << "  FAM groups: " << computeInvariants << std::endl;

	std::cout << "Transformation Options" << std::endl;
	// compilations to apply
	std::cout << "  Add zero-cost no-op to empty methods: " << noopForEmptyMethods << std::endl;
	std::cout << "  Remove duplicate actions: " << removeDuplicateActions << std::endl;
	std::cout << "  Remove useless literals: " << removeUselessPredicates << std::endl;
	std::cout << "  Expand abstract tasks with one method: " << expandChoicelessAbstractTasks << std::endl;
	std::cout << "  Remove empty method preconditions: " << pruneEmptyMethodPreconditions << std::endl;
	std::cout << "  Two regularisation: " << atMostTwoTasksPerMethod << std::endl;
	std::cout << "  Compile negative SAS variables: " << compileNegativeSASVariables << std::endl;
	
	std::cout << "Runtime Optimisations" << std::endl;
	// runtime optimisations
	std::cout << "  Hierarchy Typing: " << enableHierarchyTyping << std::endl;
	std::cout << "  Future Caching: " << futureCachingByPrecondition << std::endl;
	std::cout << "  Static Precondition Checking: " << withStaticPreconditionChecking << std::endl;
	

	std::cout << "Output Options" << std::endl;
	// select output format
	std::cout << "  Panda planner format: " << outputForPlanner << std::endl;
	std::cout << "  HDDL: " << outputHDDL << std::endl;
	std::cout << "  SAS for Fast Downward (without hierarchy): " << outputSASPlus << std::endl; 

	std::cout << "Output Formatting Options" << std::endl;
	// output formatting
	std::cout << "  Output only SAS+ variables: " << outputSASVariablesOnly << std::endl;
	std::cout << "  SAS+ delete mode: ";
	switch (sas_mode){
		case SAS_AS_INPUT: std::cout << "as input"; break;
		case SAS_ALL: std::cout << "delete all facts of SAS+ group"; break;
		case SAS_NONE: std::cout << "no deletes"; break;
	}

	std::cout << std::endl;
}


void run_grounding (const Domain & domain, const Problem & problem, std::ostream & dout, std::ostream & pout, grounding_configuration & config, given_plan_typing_information & given_typing){

  	std::vector<FAMGroup> famGroups;	
	if (config.computeInvariants){
		famGroups = compute_FAM_mutexes(domain,problem,config);
	}

	// if the instance contains conditional effects we have to compile them into additional primitive actions
	// for this, we need to be able to write to the domain
	expand_conditional_effects_into_artificial_tasks(const_cast<Domain &>(domain), const_cast<Problem &>(problem));
	if (!config.quietMode) std::cout << "Conditional Effects expanded" << std::endl;

	// run the lifted GPG to create an initial grounding of the domain
	auto [initiallyReachableFacts,initiallyReachableTasks,initiallyReachableMethods] = run_lifted_HTN_GPG(domain, problem, config, given_typing);
	// run the grounded GPG until convergence to get the grounding smaller
	std::vector<bool> prunedFacts (initiallyReachableFacts.size());
	std::vector<bool> prunedTasks (initiallyReachableTasks.size());
	std::vector<bool> prunedMethods (initiallyReachableMethods.size());
	
	// do this early
	applyEffectPriority(domain, prunedTasks, prunedFacts, initiallyReachableTasks, initiallyReachableFacts);
	
	run_grounded_HTN_GPG(domain, problem, initiallyReachableFacts, initiallyReachableTasks, initiallyReachableMethods, 
			prunedFacts, prunedTasks, prunedMethods,
			config, false);

////////////////////// H2 mutexes
	std::vector<std::unordered_set<int>> h2_mutexes;
	std::vector<std::unordered_set<int>> h2_invariants;
	if (config.h2Mutexes){
		// remove useless predicates to make the H2 inference easier
		grounding_configuration temp_configuration = config;
		temp_configuration.expandChoicelessAbstractTasks = false;
		temp_configuration.pruneEmptyMethodPreconditions = false;
		temp_configuration.atMostTwoTasksPerMethod = false;
		temp_configuration.compactConsecutivePrimitives = false;
		temp_configuration.outputSASVariablesOnly = true; // -> force SAS+ here. This makes the implementation easier

		bool reachabilityNecessary = false;
		postprocess_grounding(domain, problem, initiallyReachableFacts, initiallyReachableTasks, initiallyReachableMethods, prunedFacts, prunedTasks, prunedMethods, reachabilityNecessary, temp_configuration); 

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
				temp_configuration, false);
		}
	}
//////////////////////// end of H2 mutexes

	// run postprocessing
	bool reachabilityNecessary = false;
	postprocess_grounding(domain, problem, initiallyReachableFacts, initiallyReachableTasks, initiallyReachableMethods, prunedFacts, prunedTasks, prunedMethods, reachabilityNecessary, config);

	DEBUG(	
	// check integrity of data structures
	for (int i = 0; i < initiallyReachableMethods.size(); i++){
		if (prunedMethods[i]) continue;
		int at = initiallyReachableMethods[i].groundedAddEffects[0];
		assert(std::count(initiallyReachableTasks[at].groundedDecompositionMethods.begin(),initiallyReachableTasks[at].groundedDecompositionMethods.end(),i));
	}

	for (int i = 0; i < initiallyReachableTasks.size(); i++){
		if (prunedTasks[i]) continue;
		for (int m : initiallyReachableTasks[i].groundedDecompositionMethods)
			assert(initiallyReachableMethods[m].groundedAddEffects[0] == i);
	});



	if (config.outputSASPlus){
		write_sasplus(dout, domain,problem,initiallyReachableFacts,initiallyReachableTasks, prunedFacts, prunedTasks, config);
		return;
	}

	if (config.outputHDDL)
		write_grounded_HTN_to_HDDL(dout, pout, domain, problem, initiallyReachableFacts,initiallyReachableTasks, initiallyReachableMethods, prunedTasks, prunedFacts, prunedMethods, config);
	else if (config.outputForPlanner) {
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

		bool first = reachabilityNecessary;
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

			if (changedPruned || first){
				run_grounded_HTN_GPG(domain, problem, initiallyReachableFacts, initiallyReachableTasks, initiallyReachableMethods, 
					prunedFacts, prunedTasks, prunedMethods,
					config, first);
				first = false;
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
