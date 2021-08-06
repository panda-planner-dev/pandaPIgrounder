#ifndef GGPG_H_INCLUDED
#define GGPG_H_INCLUDED

#include <vector>

#include "model.h"
#include "grounding.h"

void run_grounded_HTN_GPG(const Domain & domain, const Problem & problem,  
		std::vector<Fact> reachableFacts,
		std::vector<GroundedTask> reachableTasks,
		std::vector<GroundedMethod> reachableMethods,
		std::vector<bool> & prunedFacts,
		std::vector<bool> & prunedTasks,
		std::vector<bool> & prunedMethods,
		grounding_configuration & config,
		bool alwaysRunDFS);


#endif
