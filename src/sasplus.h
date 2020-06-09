#ifndef SASPLUS_H_INCLUDED
#define SASPLUS_H_INCLUDED

#include <ostream>
#include <vector>
#include "model.h"
#include "grounding.h"

void write_sasplus(std::ostream & sout, const Domain & domain, const Problem & problem,
		std::vector<Fact> & reachableFacts,
		std::vector<GroundedTask> & reachableTasks,
		std::vector<bool> & prunedFacts,
		std::vector<bool> & prunedTasks,
		grounding_configuration & config);

#endif
