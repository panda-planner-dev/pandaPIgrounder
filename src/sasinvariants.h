#ifndef SAS_INVARIANTS_H_INCLUDED
#define SAS_INVARIANTS_H_INCLUDED

#include <vector>
#include <unordered_set>
#include "model.h"

struct FAMGroupLiteral{
	int predicateNo;
	std::vector<int> args; // the id of the arguments
	std::vector<bool> isConstant; // if true, the id is a constant, else variable
};

struct FAMVariable{
	int sort;
	bool isCounted;
};

struct FAMGroup{
	std::vector<FAMVariable> vars;
	std::vector<FAMGroupLiteral> literals;

	std::vector<int> counted_vars;
	std::vector<int> free_vars;
	std::vector<int> vars_to_pos_in_separated_lists;
};


std::pair<std::vector<std::unordered_set<int>>, std::vector<std::unordered_set<int>>> compute_sas_groups(const Domain & domain, const Problem & problem,
		std::vector<FAMGroup> & groups,
		std::vector<Fact> & reachableFacts,
		std::vector<GroundedTask> & reachableTasks,
		std::vector<GroundedMethod> & reachableMethods,
		std::vector<bool> & prunedTasks,
		std::vector<bool> & prunedFacts,
		std::vector<bool> & prunedMethods,
		bool quietMode);


#endif
