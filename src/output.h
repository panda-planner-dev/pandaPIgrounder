#ifndef OUTPUT_H_INCLUDED
#define OUTPUT_H_INCLUDED


#include <unordered_set>
#include "main.h"
#include "model.h"
#include "grounding.h"

void write_grounded_HTN(std::ostream & pout, const Domain & domain, const Problem & problem,
		std::vector<Fact> & reachableFacts,
		std::vector<GroundedTask> & reachableTasks,
		std::vector<GroundedMethod> & reachableMethods,
		std::vector<bool> & prunedTasks,
		std::vector<bool> & prunedFacts,
		std::vector<bool> & prunedMethods,
		std::unordered_set<int> initFacts,
		std::unordered_set<int> initFactsPruned,
		std::unordered_set<Fact> reachableFactsSet,
		std::vector<std::unordered_set<int>> sas_groups,
		std::vector<std::unordered_set<int>> further_strict_mutex_groups,
		std::vector<std::unordered_set<int>> further_mutex_groups,
		std::vector<std::unordered_set<int>> invariants,
		std::vector<bool> & sas_variables_needing_none_of_them,
		grounding_configuration & config);

void write_grounded_HTN_to_HDDL(std::ostream & dout, std::ostream & pout, const Domain & domain, const Problem & problem,
		std::vector<Fact> & reachableFacts,
		std::vector<GroundedTask> & reachableTasks,
		std::vector<GroundedMethod> & reachableMethods,
		std::vector<bool> & prunedTasks,
		std::vector<bool> & prunedFacts,
		std::vector<bool> & prunedMethods,
		grounding_configuration & config
		);

void write_task_name(std::ostream & pout, const Domain & domain, GroundedTask & task);

#endif
