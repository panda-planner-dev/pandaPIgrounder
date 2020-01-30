#ifndef GGPG_H_INCLUDED
#define GGPG_H_INCLUDED

#include <vector>

#include "model.h"

std::tuple<std::vector<bool>,std::vector<bool>,std::vector<bool>> run_grounded_HTN_GPG(const Domain & domain, const Problem & problem,  
		std::vector<Fact> reachableFacts,
		std::vector<GroundedTask> reachableTasks,
		std::vector<GroundedMethod> reachableMethods,
		bool quietMode);


#endif
