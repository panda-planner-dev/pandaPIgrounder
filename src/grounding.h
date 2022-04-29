#ifndef GROUNDING_H_INCLUDED
#define GROUNDING_H_INCLUDED

#include <ostream>
#include "main.h"
#include "model.h"
#include "givenPlan.h"


struct grounding_configuration{
	// runtime optimisations
	bool enableHierarchyTyping = true;
	bool futureCachingByPrecondition = false;
	bool withStaticPreconditionChecking = false;
	
	// inference of additional information
	bool h2Mutexes = false;
	bool computeInvariants = false;

	// select output format
	bool outputForPlanner = true;
	bool outputHDDL = false;
	bool outputSASPlus = false; 

	// output formatting
	bool outputSASVariablesOnly = false;
	sas_delete_output_mode sas_mode = SAS_AS_INPUT;
	bool noopForEmptyMethods = false;
	
	// compilations to apply
	bool compileNegativeSASVariables = false;
	bool removeDuplicateActions = false;
	bool removeUselessPredicates = true;
	bool expandChoicelessAbstractTasks = true;
	bool keepTwoRegularisation = false;
	bool pruneEmptyMethodPreconditions = true;
	bool atMostTwoTasksPerMethod = false;
	bool compactConsecutivePrimitives = false;
	
	// program output behaviour	
	bool printTimings = false;
	bool quietMode = false;

	void print_options();
};


void run_grounding (const Domain & domain, const Problem & problem, std::ostream & dout, std::ostream & pout, grounding_configuration & config, given_plan_typing_information & given_typing);

#endif

