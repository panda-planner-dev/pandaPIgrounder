#ifndef H2MUTEXES_H_INCLUDED
#define H2MUTEXES_H_INCLUDED

#include <vector>
#include "model.h"

void h2_mutexes(const Domain & domain, const Problem & problem,
		std::vector<Fact> & reachableFacts,
		std::vector<GroundedTask> & reachableTasks,
		std::vector<bool> & prunedFacts,
		std::vector<bool> & prunedTasks,
		bool quietMode);


#endif
