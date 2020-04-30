#ifndef HIERARCHY_TYPING_H_INCLUDED
#define HIERARCHY_TYPING_H_INCLUDED

/**
 * @defgroup hierarchy-typing Hierarchy Typing
 * @brief Hierarchy type information propagation
 *
 * Hierarchy Typing propagates type information (i.e. variable sorts) down the task hierarchy.
 *
 * It starts with the initial abstract task and then performs a depth-first search (DFS) along the task hierarchy,
 * passing the possible constants for all of the current task's variables in each step.
 *
 * The constants allowed by a variable's sort are intersected with the constants passed by the DFS.
 * Variable equality constraints are applied by intersecting the allowed constants for both variables referenced by the constraint.
 * In some cases, variable inequality constraints can also be applied.
 * This results in a reduction of the number of allowed constants for each variable, which is then propagated down the hierarchy by the DFS.
 *
 * The information gained by the Hierarchy Typing can then be used in the Planning Graph to reduce the number of created ground instances.
 *
 * @{
 */

#include <set>
#include <vector>

#include "model.h"

/// Contains a set of possible constants for each variable of a task/method.
using PossibleConstants = std::vector<std::set<int>>;

struct HierarchyTyping
{
	/**
	 * @brief Reference to domain
	 */
	const Domain * domain;

	/**
	 * @brief Contains a list of PossibleConstants instances for each task in the domain.
	 */
	std::vector<std::vector<PossibleConstants>> possibleConstantsPerTask;


	std::vector<std::vector<std::map<int,std::vector<int>>>> possibleConstantsSplitted;

	/**
	 * @brief Contains a list of PossibleConstants instances for each decomposition method in the domain.
	 */
	std::vector<std::vector<PossibleConstants>> possibleConstantsPerMethod;
	
	std::vector<std::vector<std::map<int,std::vector<int>>>> possibleConstantsPerMethodSplitted;

	/**
	 * @brief Calculates the hierarchy typing.
	 */
	HierarchyTyping (const Domain & domain, const Problem & Problem, bool withStaticPreconditionChecking, bool quietMode);

	/**
	 * @brief Perform the depth-first search.
	 */
	void taskDfs (const Domain & domain, const Problem & problem, bool withStaticPreconditionChecking, const std::vector<bool> & staticPredicates, std::vector<std::vector<std::map<int,std::vector<int>>>> & factsPerPredicate, size_t taskNo, PossibleConstants possibleConstants);

	/**
	 * @brief Returns true if the given VariableAssignment is compatible with the Hierarchy Typing information.
	 *
	 * This templated function is only defined for the Task and DecompositionMethod types.
	 */
	template<typename>
	bool isAssignmentCompatible (int taskNo, const VariableAssignment & assignedVariables) const;
};

/**
 * @}
 */

#endif
