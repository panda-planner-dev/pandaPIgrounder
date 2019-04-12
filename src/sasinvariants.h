#ifndef SAS_INVARIANTS_H_INCLUDED
#define SAS_INVARIANTS_H_INCLUDED

#include <vector>

#include "model.h"

struct invariant{
	// variables in invariant candidate are numbered -1, -2, -3, ... to keep them distinct from variables in tasks!
	std::set<int> fixedVariables; // those set fixed in the mutex group
	std::set<int> freeVariables; // those over which we quantify, also called "counted variables"
	std::vector<PredicateWithArguments> elements;
};

/**
 * computes lifted invariants according to Helmert, JAIR 2009: "Concise finite-domain representations for PDDL planning tasks"
 */
std::vector<invariant> computeSASPlusInvariants (const Domain & domain, const Problem & problem);



#endif
