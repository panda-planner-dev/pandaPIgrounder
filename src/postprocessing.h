#ifndef POSTPROCESSING_H_INCLUDED
#define POSTPROCESSING_H_INCLUDED

#include <vector>

#include "model.h"
#include "grounding.h"

void postprocess_grounding(const Domain & domain, const Problem & problem,
		std::vector<Fact> & reachableFacts,
		std::vector<GroundedTask> & reachableTasks,
		std::vector<GroundedMethod> & reachableMethods,
		std::vector<bool> & prunedFacts,
		std::vector<bool> & prunedTasks,
		std::vector<bool> & prunedMethods,
		grounding_configuration & config);

#endif
