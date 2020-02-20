#ifndef GROUNDING_H_INCLUDED
#define GROUNDING_H_INCLUDED

#include <ostream>
#include "model.h"

void run_grounding (const Domain & domain, const Problem & problem, std::ostream & pout,
		bool enableHierarchyTyping, 
		bool removeUselessPredicates,
		bool expandChoicelessAbstractTasks,
		bool pruneEmptyMethodPreconditions,
		bool futureCachingByPrecondition,
		bool h2Mutextes,
		bool outputForPlanner, 
		bool printTimings,
		bool quietMode);

#endif

