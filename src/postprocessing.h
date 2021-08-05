#ifndef POSTPROCESSING_H_INCLUDED
#define POSTPROCESSING_H_INCLUDED

#include <vector>

#include "model.h"
#include "grounding.h"

void applyEffectPriority(const Domain & domain,
		std::vector<bool> & prunedTasks,
		std::vector<bool> & prunedFacts,
		std::vector<GroundedTask> & inputTasksGroundedPg,
		std::vector<Fact> & inputFactsGroundedPg);

	void postprocess_grounding(const Domain & domain, const Problem & problem,
		std::vector<Fact> & reachableFacts,
		std::vector<GroundedTask> & reachableTasks,
		std::vector<GroundedMethod> & reachableMethods,
		std::vector<bool> & prunedFacts,
		std::vector<bool> & prunedTasks,
		std::vector<bool> & prunedMethods,
		bool & reachabilityNecessary,
		grounding_configuration & config);

#endif
