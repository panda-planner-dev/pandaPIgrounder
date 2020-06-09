#ifndef H2MUTEXES_H_INCLUDED
#define H2MUTEXES_H_INCLUDED

#include <vector>
#include "model.h"
#include "grounding.h"

std::tuple<bool,std::vector<std::unordered_set<int>>, std::vector<std::unordered_set<int>>> compute_h2_mutexes(const Domain & domain, const Problem & problem,
		std::vector<Fact> & reachableFacts,
		std::vector<GroundedTask> & reachableTasks,
		std::vector<bool> & prunedFacts,
		std::vector<bool> & prunedTasks,
		std::vector<std::unordered_set<int>> sas_groups,
		std::vector<bool> & sas_variables_needing_none_of_them,
		grounding_configuration & config);


#endif
