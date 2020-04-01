#ifndef GROUNDING_H_INCLUDED
#define GROUNDING_H_INCLUDED

#include <ostream>
#include "main.h"
#include "model.h"

void run_grounding (const Domain & domain, const Problem & problem, std::ostream & dout, std::ostream & pout,
		bool enableHierarchyTyping, 
		bool removeUselessPredicates,
		bool expandChoicelessAbstractTasks,
		bool pruneEmptyMethodPreconditions,
		bool futureCachingByPrecondition,
		bool h2Mutextes,
		bool computeInvariants,
		bool outputSASVariablesOnly,
		sas_delete_output_mode sas_mode,
		bool compileNegativeSASVariables,
		bool removeDuplicateActions,
		bool noopForEmptyMethods,
		bool outputForPlanner, 
		bool outputHDDL, 
		bool outputSASPlus, 
		bool printTimings,
		bool quietMode);

#endif

