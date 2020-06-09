#ifndef DUPLICATE_H_INCLUDED
#define DUPLICATE_H_INCLUDED 

#include "model.h"
#include "grounding.h"

void unify_duplicates(const Domain & domain, const Problem & problem,
		std::vector<Fact> & reachableFacts,
		std::vector<GroundedTask> & reachableTasks,
		std::vector<GroundedMethod> & reachableMethods,
		std::vector<bool> & prunedTasks,
		std::vector<bool> & prunedFacts,
		std::vector<bool> & prunedMethods,
		grounding_configuration & config	
		);
#endif

