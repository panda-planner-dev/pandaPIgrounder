#include "grounding.h"
#include "gpg.h"
#include "liftedGPG.h"
#include "groundedGPG.h"
#include "postprocessing.h"
#include "output.h"



void run_grounding (const Domain & domain, const Problem & problem, std::ostream & pout, 
		bool enableHierarchyTyping, 
		bool removeUselessPredicates,
		bool expandChoicelessAbstractTasks,
		bool pruneEmptyMethodPreconditions,
		bool futureCachingByPrecondition,
		bool outputForPlanner, 
		bool printTimings,
		bool quietMode){
	// run the lifted GPG to create an initial grounding of the domain
	auto [initiallyReachableFacts,initiallyReachableTasks,initiallyReachableMethods] = run_lifted_HTN_GPG(domain, problem, 
			enableHierarchyTyping, futureCachingByPrecondition, printTimings, quietMode);
	// run the grounded GPG until convergence to get the grounding smaller
	auto [prunedFacts, prunedTasks, prunedMethods] = run_grounded_HTN_GPG(domain, problem, initiallyReachableFacts, initiallyReachableTasks, initiallyReachableMethods, quietMode);

	// run postprocessing
	postprocess_grounding(domain, problem, initiallyReachableFacts, initiallyReachableTasks, initiallyReachableMethods, prunedFacts, prunedTasks, prunedMethods, 
			removeUselessPredicates, expandChoicelessAbstractTasks, pruneEmptyMethodPreconditions, quietMode);	

	// get statistics
	int facts = 0;
	int abstractTasks = 0;
	int primitiveTasks = 0;
	int methodPreconditionPrimitiveTasks = 0;
	int methods = 0;
	for (Fact & fact : initiallyReachableFacts){
		if (prunedFacts[fact.groundedNo]) continue;
		facts++;
	}
	
	for(int i = 0; i < initiallyReachableTasks.size(); i++)
		if (! prunedTasks[i]){
			if (initiallyReachableTasks[i].taskNo >= domain.nPrimitiveTasks)
				abstractTasks ++;
			else {
				if (domain.tasks[initiallyReachableTasks[i].taskNo].name.rfind("method_precondition_",0) == 0)
					methodPreconditionPrimitiveTasks++;
				else
					primitiveTasks++;
			}
		}

	for (auto & method : initiallyReachableMethods){
		if (prunedMethods[method.groundedNo]) continue;
		methods++;
	}
	

	// output statistics	
	if (!quietMode) std::cerr << "Statistics: " << facts << " " << primitiveTasks << " " << methodPreconditionPrimitiveTasks << " " << abstractTasks << " " << methods << std::endl;

	if (outputForPlanner){
		write_grounded_HTN(pout, domain, problem, initiallyReachableFacts,initiallyReachableTasks, initiallyReachableMethods, prunedTasks, prunedFacts, prunedMethods,
				facts, abstractTasks, primitiveTasks + methodPreconditionPrimitiveTasks, methods, quietMode);
	
	}



}

